// SPDX-License-Identifier: Apache-2.0

// Matched-accuracy precondition machinery: a
// family's timing output is void unless its matched-accuracy check passes in
// the same run. Families call these helpers from both their tests and their
// benchmark setup.

package benchmarks

import (
	"fmt"
	"testing"
)

// matchedAccuracyError compares a family's computed outputs against the
// expected outputs for the same committed-seed inputs. Any mismatch voids
// the family's timing for the run.
func matchedAccuracyError(family string, got, want []string) error {
	if len(got) != len(want) {
		return fmt.Errorf("family %s: matched-accuracy arity mismatch: got %d outputs, want %d (family timing is void for this run)",
			family, len(got), len(want))
	}
	for i := range got {
		if got[i] != want[i] {
			return fmt.Errorf("family %s: matched-accuracy mismatch at %d: got %q, want %q (family timing is void for this run)",
				family, i, got[i], want[i])
		}
	}
	return nil
}

// requireMatchedAccuracy is the benchmark-side entry: it fails the benchmark
// before any timing is reported when the precondition does not hold.
func requireMatchedAccuracy(tb testing.TB, family string, got, want []string) {
	if err := matchedAccuracyError(family, got, want); err != nil {
		tb.Fatal(err)
	}
}

// TestMatchedAccuracyPrecondition demonstrates both modes of the
// precondition helper: acceptance on agreement and rejection on divergence
// (the mode that voids a family's timing).
func TestMatchedAccuracyPrecondition(t *testing.T) {
	if err := matchedAccuracyError("F1", []string{"1.25", "3.75"}, []string{"1.25", "3.75"}); err != nil {
		t.Fatalf("agreeing outputs rejected: %v", err)
	}
	err := matchedAccuracyError("F1", []string{"1.25", "3.76"}, []string{"1.25", "3.75"})
	if err == nil {
		t.Fatal("diverging outputs accepted: the family's timing would not be void")
	}
	want := `family F1: matched-accuracy mismatch at 1: got "3.76", want "3.75" (family timing is void for this run)`
	if err.Error() != want {
		t.Fatalf("rejection diagnostic = %q, want %q", err.Error(), want)
	}
	err = matchedAccuracyError("F2", []string{"1"}, []string{"1", "2"})
	if err == nil || err.Error() != "family F2: matched-accuracy arity mismatch: got 1 outputs, want 2 (family timing is void for this run)" {
		t.Fatalf("arity mismatch diagnostic = %v", err)
	}
	requireMatchedAccuracy(t, "F6", []string{"x"}, []string{"x"}) // must not fatal
}

// TestMismatchVoidsTiming pins that matched accuracy voids mismatched
// timing: a row whose oracle check fails is never timed (testing.Benchmark
// reports no iterations and the timed operation never runs), while the same
// row with a passing check is timed.
func TestMismatchVoidsTiming(t *testing.T) {
	calls := 0
	row := func(check error) []oracleRow {
		return []oracleRow{{
			variant: "probe", size: 1,
			check: func() error { return check },
			run:   func(int) error { calls++; return nil },
		}}
	}
	void := testing.Benchmark(func(b *testing.B) { benchOracleRows(b, row(fmt.Errorf("oracle mismatch"))) })
	if void.N != 0 || calls != 0 {
		t.Fatalf("mismatched row was timed: N=%d, %d timed calls", void.N, calls)
	}
	timed := testing.Benchmark(func(b *testing.B) { benchOracleRows(b, row(nil)) })
	if timed.N == 0 || calls == 0 {
		t.Fatalf("matched row was not timed: N=%d, %d timed calls", timed.N, calls)
	}
}
