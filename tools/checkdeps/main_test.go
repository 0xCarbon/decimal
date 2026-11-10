// SPDX-License-Identifier: Apache-2.0

package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestDependencyPolicy(t *testing.T) {
	for _, tc := range []struct {
		name, graph string
		policy      policy
		valid       bool
	}{
		{"stdlib-root", `{"Path":"github.com/0xCarbon/decimal","Main":true}`, stdlibOnly, true},
		{"root-is-stdlib-only", `{"Path":"golang.org/x/tools"}`, stdlibOnly, false},
		{"official-tool", `{"Path":"golang.org/x/tools"}`, toolPolicy, true},
		{"transitive-tool-violation", `{"Path":"golang.org/x/perf"} {"Path":"github.com/aclements/go-moremath"}`, toolPolicy, false},
		{"lookalike", `{"Path":"golang.org/xevil/tools"}`, toolPolicy, false},
		{"replacement", `{"Path":"golang.org/x/tools","Replace":{"Path":"example.org/tools"}}`, toolPolicy, false},
		{"local-replacement", `{"Path":"golang.org/x/tools","Replace":{"Path":"../tools"}}`, toolPolicy, false},
		{"incumbent", `{"Path":"github.com/shopspring/decimal"}`, comparison, true},
		{"incumbent-transitive", `{"Path":"github.com/lib/pq"}`, comparison, true},
		{"comparison-refuses-other", `{"Path":"github.com/example/bigdecimal"}`, comparison, false},
		{"comparison-local-library", `{"Path":"github.com/0xCarbon/decimal","Replace":{"Path":"../.."}}`, comparison, true},
		{"comparison-refuses-replacement", `{"Path":"github.com/shopspring/decimal","Replace":{"Path":"example.org/fork"}}`, comparison, false},
		{"tool-refuses-incumbent", `{"Path":"github.com/shopspring/decimal"}`, toolPolicy, false},
		{"empty", ``, toolPolicy, false},
		{"malformed", `{`, toolPolicy, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			err := auditGraph([]byte(tc.graph), tc.policy)
			if (err == nil) != tc.valid {
				t.Fatalf("auditGraph = %v, want valid %v", err, tc.valid)
			}
		})
	}
}

func TestGoListFailureIsFatal(t *testing.T) {
	root := t.TempDir()
	if err := os.WriteFile(filepath.Join(root, "go.mod"), []byte("not a module file\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := audit(root); err == nil || !strings.Contains(err.Error(), "go list failed") {
		t.Fatalf("invalid maintained module accepted: %v", err)
	}
}

func TestUnsafeImportPolicy(t *testing.T) {
	root := t.TempDir()
	if err := os.WriteFile(filepath.Join(root, "core.go"), []byte("package decimal\nimport \"unsafe\"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := audit(root); err == nil || !strings.Contains(err.Error(), "unsafe") {
		t.Fatalf("project-authored unsafe import accepted: %v", err)
	}
	if err := os.Remove(filepath.Join(root, "core.go")); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(root, "safe.go"), []byte("package decimal\n// import \"unsafe\" is only a comment\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(filepath.Join(root, ".cache", "download"), 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(root, ".cache", "download", "probe.go"), []byte("package probe\nimport \"unsafe\"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := audit(root); err != nil {
		t.Fatalf("safe core and downloaded material rejected: %v", err)
	}
	// A nested directory named like a root-level scratch directory remains
	// maintained source and must not bypass the import policy.
	nested := filepath.Join(root, "tools", "dist")
	if err := os.MkdirAll(nested, 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(nested, "bad.go"), []byte("package tool\nimport \"unsafe\"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := audit(root); err == nil || !strings.Contains(err.Error(), filepath.Join("tools", "dist", "bad.go")) || !strings.Contains(err.Error(), "unsafe") {
		t.Fatalf("nested maintained unsafe import escaped: %v", err)
	}
}

// TestLibraryModuleRefusesEveryRequire pins that the library go.mod has no
// require line at all, so embedding
// projects with std-only policies can adopt it. A 0xCarbon sibling module is
// refused for the library module too.
func TestLibraryModuleRefusesEveryRequire(t *testing.T) {
	root := t.TempDir()
	sibling := filepath.Join(root, "sibling")
	if err := os.MkdirAll(sibling, 0o700); err != nil {
		t.Fatal(err)
	}
	files := map[string]string{
		filepath.Join(sibling, "go.mod"): "module github.com/0xCarbon/sibling\n\ngo 1.27\n",
		filepath.Join(sibling, "s.go"):   "package sibling\n",
		filepath.Join(root, "go.mod"): "module github.com/0xCarbon/decimal\n\ngo 1.27\n\n" +
			"require github.com/0xCarbon/sibling v0.0.0\n\nreplace github.com/0xCarbon/sibling => ./sibling\n",
		filepath.Join(root, "d.go"): "package decimal\n",
	}
	for path, content := range files {
		if err := os.WriteFile(path, []byte(content), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	err := audit(root)
	if err == nil || !strings.Contains(err.Error(), "prohibited dependency github.com/0xCarbon/sibling") {
		t.Fatalf("library module require accepted: %v", err)
	}
}

// TestCorePurityPolicy pins core purity: repository code
// has no assembly or object files and never imports simd/archsimd directly;
// the portable simd package keeps ISA selection with the compiler.
func TestCorePurityPolicy(t *testing.T) {
	for _, tc := range []struct{ file, content, want string }{
		{"add_amd64.s", "TEXT ·add(SB),4,$0\n", "assembly"},
		{"blob.syso", "x", "assembly"},
		{"k.go", "package decimal\nimport \"simd/archsimd\"\n", "simd/archsimd"},
	} {
		t.Run(tc.file, func(t *testing.T) {
			root := t.TempDir()
			if err := os.WriteFile(filepath.Join(root, tc.file), []byte(tc.content), 0o600); err != nil {
				t.Fatal(err)
			}
			if err := audit(root); err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("%s accepted: %v", tc.file, err)
			}
		})
	}
	root := t.TempDir()
	if err := os.WriteFile(filepath.Join(root, "k.go"), []byte("package decimal\nimport \"simd\"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := audit(root); err != nil {
		t.Fatalf("portable simd import refused: %v", err)
	}
}

// TestLibraryPackageImportsStdlibOnly pins that the root package's full dependency closure may contain only
// standard-library packages and itself, so an in-module package (which a
// module-graph audit cannot see) cannot carry state or a non-std import.
func TestLibraryPackageImportsStdlibOnly(t *testing.T) {
	root := t.TempDir()
	knob := filepath.Join(root, "internal", "knob")
	if err := os.MkdirAll(knob, 0o700); err != nil {
		t.Fatal(err)
	}
	files := map[string]string{
		filepath.Join(root, "go.mod"): "module github.com/0xCarbon/decimal\n\ngo 1.27\n",
		filepath.Join(root, "d.go"):   "package decimal\nimport (\n\t\"strings\"\n\t\"github.com/0xCarbon/decimal/internal/knob\"\n)\nvar _ = strings.Repeat\nvar _ = knob.Precision\n",
		filepath.Join(knob, "k.go"):   "package knob\nvar Precision = 16\n",
	}
	for path, content := range files {
		if err := os.WriteFile(path, []byte(content), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	err := audit(root)
	if err == nil || !strings.Contains(err.Error(), "non-standard dependency github.com/0xCarbon/decimal/internal/knob") {
		t.Fatalf("in-module dependency of the library package accepted: %v", err)
	}
	if err := os.WriteFile(filepath.Join(root, "d.go"), []byte("package decimal\nimport \"strings\"\nvar _ = strings.Repeat\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := audit(root); err != nil {
		t.Fatalf("stdlib-only library package refused: %v", err)
	}
}

// TestLibraryDependencyAuditCoversEveryConfiguration pins that an import hidden in a scalar-only or 386-only file
// is refused even when the host configuration never selects that file.
func TestLibraryDependencyAuditCoversEveryConfiguration(t *testing.T) {
	for _, constraint := range []string{"//go:build !goexperiment.simd", "//go:build 386", "//go:build wasm"} {
		t.Run(constraint, func(t *testing.T) {
			root := t.TempDir()
			knob := filepath.Join(root, "internal", "knob")
			if err := os.MkdirAll(knob, 0o700); err != nil {
				t.Fatal(err)
			}
			files := map[string]string{
				filepath.Join(root, "go.mod"):   "module github.com/0xCarbon/decimal\n\ngo 1.27\n",
				filepath.Join(root, "d.go"):     "package decimal\n",
				filepath.Join(root, "gated.go"): constraint + "\n\npackage decimal\nimport \"github.com/0xCarbon/decimal/internal/knob\"\nvar _ = knob.Precision\n",
				filepath.Join(knob, "k.go"):     "package knob\nvar Precision = 16\n",
			}
			for path, content := range files {
				if err := os.WriteFile(path, []byte(content), 0o600); err != nil {
					t.Fatal(err)
				}
			}
			if err := audit(root); err == nil || !strings.Contains(err.Error(), "non-standard dependency github.com/0xCarbon/decimal/internal/knob") {
				t.Fatalf("gated in-module dependency accepted: %v", err)
			}
		})
	}
}
