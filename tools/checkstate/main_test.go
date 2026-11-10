// SPDX-License-Identifier: Apache-2.0

package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func auditSource(t *testing.T, src string) []string {
	t.Helper()
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "lib.go"), []byte(src), 0o600); err != nil {
		t.Fatal(err)
	}
	// Test files are outside the audit even when they hold state.
	if err := os.WriteFile(filepath.Join(dir, "lib_test.go"), []byte("package d\nvar Hits int\nfunc init() { Hits++; panic(1) }\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	findings, err := auditDir(dir)
	if err != nil {
		t.Fatal(err)
	}
	return findings
}

// TestStateAuditRejectsEachViolation is the deliberate-failure control for
// the audit: each fixture seeds one violation that must be named, including
// every shape a name-based audit would miss.
func TestStateAuditRejectsEachViolation(t *testing.T) {
	for _, tc := range []struct{ name, src, want string }{
		{"counter", "package d\nvar calls int\nfunc F() { calls++ }\n", "write to package variable calls"},
		{"assign", "package d\nvar mode = 1\nfunc Set(m int) { mode = m }\n", "write to package variable mode"},
		{"table-element", "package d\nvar table = [2]int{1, 2}\nfunc F() { table[1] = 3 }\n", "write to package variable table"},
		{"field", "package d\nvar cfg struct{ p int }\nfunc F() { cfg.p = 3 }\n", "write to package variable cfg"},
		{"address", "package d\nvar table [2]int\nfunc F() *int { return &table[0] }\n", "address of package variable table"},
		{"exported-knob", "package d\nvar DivisionPrecision = 16\nfunc P() int { return DivisionPrecision }\n", "exported package variable DivisionPrecision"},
		{"slice-type", "package d\nvar names = []string{\"a\"}\nfunc N() string { return names[0] }\n", "package variable names has reference type"},
		{"map-type", "package d\nvar seen = map[int]bool{}\nfunc S(i int) bool { return seen[i] }\n", "package variable seen has reference type"},
		{"func-literal-initializer", "package d\nvar calls int\nvar bump = func() { calls++ }\n", "write to package variable calls"},
		{"pointer-receiver-method", "package d\nimport \"sync/atomic\"\nvar hits atomic.Int64\nfunc F() { hits.Add(1) }\n", "pointer-receiver method on package variable hits"},
		{"method-value", "package d\nimport \"sync/atomic\"\nvar hits atomic.Int64\nfunc F() { add := hits.Add; add(1) }\n", "pointer-receiver method on package variable hits"},
		{"alias-slice", "package d\nvar table [4]byte\nfunc F() { s := table[:]; s[0] = 1 }\n", "aliasing slice of package variable table"},
		{"copy-into", "package d\nvar table [4]byte\nfunc F(b []byte) { copy(table[:], b) }\n", "aliasing slice of package variable table"},
		{"range-assign", "package d\nvar last int\nfunc F(xs []int) { for _, last = range xs {} }\n", "write to package variable last"},
		{"inner-shadow", "package d\nvar calls int\nfunc F() { { calls := 1; _ = calls }; calls++ }\n", "write to package variable calls"},
		{"init", "package d\nfunc init() {}\n", "init function"},
		{"panic", "package d\nfunc Parse() { panic(\"x\") }\n", "panic outside a Must function (Parse)"},
		{"panic-mustard", "package d\nfunc Mustard() { panic(\"x\") }\n", "panic outside a Must function (Mustard)"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			findings := auditSource(t, tc.src)
			found := false
			for _, f := range findings {
				found = found || strings.Contains(f, tc.want)
			}
			if !found {
				t.Fatalf("findings %q, want one containing %q", findings, tc.want)
			}
		})
	}
}

func TestStateAuditAcceptsReadOnlyTablesAndMust(t *testing.T) {
	src := `package d

import "strings"

var powers = [3]uint32{1, 10, 100}
var names = [...]string{"a", "b"}
var spaces = strings.Repeat(" ", 8)
var wide = func() (table [3]uint64) {
	for i := range table {
		table[i] = uint64(i)
	}
	return table
}()
var _ = powers

func Pow(i int) uint32   { return powers[i] }
func Name(i int) string  { return names[i] }
func Pad(n int) string   { return spaces[:n] }
func Wide(i int) uint64  { return wide[i] }
func Shadow() int        { powers := 3; powers++; return powers }
func Param(names []string) { names[0] = "x" }
func MustParse(s string) int {
	if s == "" {
		panic("empty")
	}
	return len(s)
}
`
	if findings := auditSource(t, src); len(findings) != 0 {
		t.Fatalf("read-only library flagged: %q", findings)
	}
}

// TestStateAuditCoversEveryBuildConfiguration pins that files selected only by the scalar profile, by 386 or by wasm
// are audited too, not just the host's selection.
func TestStateAuditCoversEveryBuildConfiguration(t *testing.T) {
	for _, tc := range []struct{ name, constraint string }{
		{"scalar-only", "//go:build !goexperiment.simd"},
		{"simd-only", "//go:build goexperiment.simd"},
		{"386-only", "//go:build 386"},
		{"wasm-only", "//go:build wasm"},
		{"arm64-only", "//go:build arm64"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			files := map[string]string{
				"lib.go":   "package d\nfunc F() int { return 1 }\n",
				"state.go": tc.constraint + "\n\npackage d\nvar calls int\nfunc G() { calls++ }\n",
			}
			for name, src := range files {
				if err := os.WriteFile(filepath.Join(dir, name), []byte(src), 0o600); err != nil {
					t.Fatal(err)
				}
			}
			findings, err := auditDir(dir)
			if err != nil {
				t.Fatal(err)
			}
			if len(findings) != 1 || !strings.Contains(findings[0], "write to package variable calls") {
				t.Fatalf("findings %q, want the %s write", findings, tc.name)
			}
		})
	}
}

// TestLibraryHasNoMutablePackageState runs the check on the real library:
// no package variable is ever written, so no package-level setting can
// affect a result.
func TestLibraryHasNoMutablePackageState(t *testing.T) {
	findings, err := auditDir(filepath.Join("..", ".."))
	if err != nil {
		t.Fatal(err)
	}
	if len(findings) != 0 {
		t.Fatalf("library state findings: %q", findings)
	}
}
