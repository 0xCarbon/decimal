// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"go/ast"
	"go/parser"
	"go/token"
	"math"
	"math/bits"
	"path/filepath"
	"regexp"
	"runtime"
	"slices"
	"strings"
	"testing"
)

// evaluationObjectOracle is an independently written allocator envelope: the
// Go size-class rounding of an n-byte object, as a test oracle.
func evaluationObjectOracle(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	if n <= 32768 {
		return (n + n/4 + 31) / 16 * 16
	}
	return (n + 8191) / 8192 * 8192
}

// TestEvaluationPhaseAdmission checks the admission boundaries of the
// evaluation phases.
func TestEvaluationPhaseAdmission(t *testing.T) {
	for _, tc := range []struct{ a, h uint64 }{{0, 0}, {7, 0}, {4, 96}, {100, 8192}} {
		q := 1 + tc.a + tc.h
		m := newEvaluationMeter(Budget{MaxWork: q})
		if s := m.phase(tc.a, tc.h); s.code != 0 || m.remaining != 0 {
			t.Fatalf("equality: %+v remaining=%d", s, m.remaining)
		}
		if s := m.phase(0, 0); s.resource != EvaluationUnits || s.limit != q {
			t.Fatalf("exhausted: %+v", s)
		}
		if q > 1 {
			m = newEvaluationMeter(Budget{MaxWork: q - 1})
			if s := m.phase(tc.a, tc.h); s.code != ErrInsufficientStorage || m.remaining != q-1 {
				t.Fatalf("q-1: %+v remaining=%d", s, m.remaining)
			}
		}
	}
	for _, ab := range [][2]uint64{{math.MaxUint64, 0}, {math.MaxUint64 - 1, 1}, {1, math.MaxUint64}} {
		m := newEvaluationMeter(Budget{MaxWork: math.MaxUint64})
		if s := m.phase(ab[0], ab[1]); s.resource != EvaluationUnits || m.remaining != math.MaxUint64 {
			t.Fatalf("overflow admitted: %+v", s)
		}
	}
}

// TestEvaluationUnlimitedAndDigits covers zero axes, stored digits, and no lifetime counter.
func TestEvaluationUnlimitedAndDigits(t *testing.T) {
	m := newEvaluationMeter(Budget{})
	for range 3 {
		if s := m.phase(math.MaxUint64, math.MaxUint64); s.code != 0 {
			t.Fatalf("unlimited acquired counter cap: %+v", s)
		}
	}
	if s := m.resultDigits(math.MaxUint64); s.code != 0 {
		t.Fatal(s)
	}
	m = newEvaluationMeter(Budget{MaxDigits: 3})
	for _, n := range []uint64{0, 1, 3} {
		if s := m.resultDigits(n); s.code != 0 {
			t.Fatal(s)
		}
	}
	if s := m.resultDigits(4); s.resource != EvaluationCoefficientDigits || s.limit != 3 {
		t.Fatalf("digit refusal: %+v", s)
	}
	m = newEvaluationMeter(Budget{MaxWork: 5})
	for range 5 {
		if s := m.phase(0, 0); s.code != 0 {
			t.Fatal(s)
		}
	}
	if s := m.phase(0, 0); s.resource != EvaluationUnits {
		t.Fatalf("uncharged controller: %+v", s)
	}
}

// TestEvaluationObjectAdmission covers preallocation, ownership release and physical aggregation.
func TestEvaluationObjectAdmission(t *testing.T) {
	for _, n := range []uint64{0, 1, 16, 17, 4097, 32768, 32769} {
		q := 1 + n + evaluationObjectOracle(n)
		m := newEvaluationMeter(Budget{MaxWork: q})
		ticket, s := m.admitObject(n)
		if s.code != 0 || m.remaining != 0 {
			t.Fatalf("size %d: %+v remainder %d", n, s, m.remaining)
		}
		live := m.liveBytes
		m.release(ticket)
		if m.liveBytes != 0 || m.remaining != 0 {
			t.Fatalf("release refunded quota or retained live bytes: %+v", m)
		}
		if n > 0 && live < n {
			t.Fatalf("physical ticket too small: %d < %d", live, n)
		}
		if n > 0 {
			m = newEvaluationMeter(Budget{MaxWork: q - 1})
			if _, s = m.admitObject(n); s.resource != EvaluationUnits || m.liveBytes != 0 {
				t.Fatalf("allocated denied object: %+v", s)
			}
		}
	}
	_, maxAddress, _ := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	m := newEvaluationMeter(Budget{})
	m.liveBytes = maxAddress
	if _, s := m.admitObject(1); s.code != ErrInsufficientStorage || s.resource != 0 || m.liveBytes != maxAddress {
		t.Fatalf("aggregate physical bypass: %+v", s)
	}
	m = newEvaluationMeter(Budget{})
	if _, s := m.admitObject(math.MaxUint64); s.code != ErrInsufficientStorage || s.resource != 0 {
		t.Fatalf("physical overflow: %+v", s)
	}
}

// TestEvaluationLedgerAllocationFree covers charged scan/planning paths and denial before allocation.
func TestEvaluationLedgerAllocationFree(t *testing.T) {
	var status evaluationStatus
	allocs := testing.AllocsPerRun(100, func() {
		m := newEvaluationMeter(Budget{MaxWork: 100})
		_ = m.phase(9, 0)
		ticket, s := m.admitObject(16)
		status = s
		if status.code == 0 {
			m.release(ticket)
		}
		status = m.phase(100, 0)
	})
	if allocs != 0 || status.resource != EvaluationUnits {
		t.Fatalf("ledger allocated %g or failed denial: %+v", allocs, status)
	}
}

// TestEvaluationCumulativeAllocation covers prior discarded objects, shared child admission and one outer error.
func TestEvaluationCumulativeAllocation(t *testing.T) {
	const n = 4097
	q := uint64(1+n) + evaluationObjectOracle(n)
	budget := Budget{MaxWork: 2 * q}
	bound, err := BoundEvaluation(budget)
	if err != nil {
		t.Fatal(err)
	}
	var sink []byte
	var failure error
	run := func() {
		m := newEvaluationMeter(budget)
		for range 3 {
			ticket, s := m.admitObject(n)
			if s.code != 0 {
				failure = evaluationFailure("ExpWithContext", s)
				return
			}
			sink = make([]byte, n)
			sink[n-1] = 1
			// The object is now garbage to the evaluator: live ownership ends,
			// but its admission cannot be refunded to a nested/retried phase.
			m.release(ticket)
		}
	}
	got := coldAllocatedWithin(run, bound.HeapBytes)
	if got > bound.HeapBytes {
		t.Fatalf("allocated %d > bound %d", got, bound.HeapBytes)
	}
	var limit *Error
	if !errors.As(failure, &limit) || limit.Resource == 0 || limit.Resource != EvaluationUnits || len(sink) != n {
		t.Fatalf("nested attempt escaped quota: %v", failure)
	}
}

// TestEvaluationBudgetDocNamesEveryBudgetedFunction pins the Budget doc
// comment to the functions that take one: every exported function or method
// with a Budget parameter is the budgeted form of an operation the comment
// names, so the family list cannot fall behind the API.
func TestEvaluationBudgetDocNamesEveryBudgetedFunction(t *testing.T) {
	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	fset := token.NewFileSet()
	doc := ""
	var functions []string
	for _, name := range files {
		if strings.HasSuffix(name, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(fset, name, nil, parser.ParseComments|parser.SkipObjectResolution)
		if err != nil {
			t.Fatal(err)
		}
		for _, decl := range f.Decls {
			switch d := decl.(type) {
			case *ast.GenDecl:
				for _, spec := range d.Specs {
					if ts, ok := spec.(*ast.TypeSpec); ok && ts.Name.Name == "Budget" {
						doc = d.Doc.Text()
					}
				}
			case *ast.FuncDecl:
				if !d.Name.IsExported() || strings.HasPrefix(d.Name.Name, "Estimate") {
					continue
				}
				for _, field := range d.Type.Params.List {
					if id, ok := field.Type.(*ast.Ident); ok && id.Name == "Budget" {
						base := strings.TrimSuffix(d.Name.Name, "WithBudget")
						if !slices.Contains(functions, base) {
							functions = append(functions, base)
						}
					}
				}
			}
		}
	}
	if doc == "" || len(functions) < 12 {
		t.Fatalf("found doc %q and %d budgeted functions: the scan is vacuous", doc, len(functions))
	}
	slices.Sort(functions)
	for _, fn := range functions {
		if !regexp.MustCompile(`\b` + fn + `\b`).MatchString(doc) {
			t.Errorf("Budget doc does not name %s, which takes a Budget", fn)
		}
	}
}
