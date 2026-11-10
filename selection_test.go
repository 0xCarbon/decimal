// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/big"
	"math/rand"
	"strings"
	"sync"
	"testing"
)

func TestSelectionSignaturesAndSignCohorts(t *testing.T) {
	var _ func(Decimal) Decimal = Decimal.Neg
	var _ func(Decimal) Decimal = Decimal.Abs
	var _ func(Decimal) int = Decimal.Sign
	var _ func(Decimal) bool = Decimal.IsZero
	var _ func(Decimal, Decimal) Decimal = Decimal.Min
	var _ func(Decimal, Decimal) Decimal = Decimal.Max

	for _, tc := range []struct {
		input string
		sign  int
		zero  bool
		neg   string
		abs   string
	}{
		{"12.30", 1, false, "-12.30", "12.30"},
		{"-12.30", -1, false, "12.30", "12.30"},
		{"1.4700", 1, false, "-1.4700", "1.4700"},
		{"-1.4700", -1, false, "1.4700", "1.4700"},
		{"0.00", 0, true, "0.00", "0.00"},
		{"0E+7", 0, true, "0E+7", "0E+7"},
	} {
		d := MustParse(tc.input)
		before := d.String()
		if got := d.Sign(); got != tc.sign {
			t.Errorf("%s.Sign()=%d, want %d", tc.input, got, tc.sign)
		}
		if got := d.IsZero(); got != tc.zero {
			t.Errorf("%s.IsZero()=%t, want %t", tc.input, got, tc.zero)
		}
		if got := d.Neg().String(); got != tc.neg {
			t.Errorf("%s.Neg()=%s, want %s", tc.input, got, tc.neg)
		}
		if got := d.Abs().String(); got != tc.abs {
			t.Errorf("%s.Abs()=%s, want %s", tc.input, got, tc.abs)
		}
		if got := d.String(); got != before {
			t.Errorf("%s changed to %s", before, got)
		}
	}
}

func TestSelectionMinMaxCohortTies(t *testing.T) {
	for _, tc := range []struct {
		a, b, min, max string
		tie            bool
	}{
		{"1.0", "1", "1.0", "1", true},
		{"-1.0", "-1", "-1", "-1.0", true},
		{"0.00", "0E+3", "0.00", "0E+3", true},
		{"0.00", "1", "0.00", "1", false},
		{"0E+3", "-1", "-1", "0E+3", false},
		{"-2", "3", "-2", "3", false},
		{"2.0", "3", "2.0", "3", false},
		{"-2", "-3.0", "-3.0", "-2", false},
	} {
		a, b := MustParse(tc.a), MustParse(tc.b)
		if tc.tie && (a.Compare(b) != 0 || b.Compare(a) != 0) {
			t.Errorf("tie inputs %s and %s must compare numerically equal", tc.a, tc.b)
		}
		for _, pair := range [][2]Decimal{{a, b}, {b, a}} {
			if got := pair[0].Min(pair[1]).String(); got != tc.min {
				t.Errorf("Min(%s,%s)=%s, want %s", pair[0], pair[1], got, tc.min)
			}
			if got := pair[0].Max(pair[1]).String(); got != tc.max {
				t.Errorf("Max(%s,%s)=%s, want %s", pair[0], pair[1], got, tc.max)
			}
		}
	}
	if got := MustParse("-0.00").Neg(); got.negative() || !got.IsZero() || got.exponent() != -2 {
		t.Errorf("negative zero must remain unsigned at its exponent: text=%s exponent=%d sign=%t", got.String(), got.exponent(), got.negative())
	}
}

func selectionRat(coefficient int64, exponent int32) *big.Rat {
	r := new(big.Rat).SetInt64(coefficient)
	pow := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(selectionAbs32(exponent))), nil)
	if exponent < 0 {
		return r.Quo(r, new(big.Rat).SetInt(pow))
	}
	return r.Mul(r, new(big.Rat).SetInt(pow))
}

func selectionAbs32(v int32) uint32 {
	if v < 0 {
		return uint32(-int64(v))
	}
	return uint32(v)
}

func TestSelectionIndependentRatOracle(t *testing.T) {
	rng := rand.New(rand.NewSource(20260924))
	for i := range 256 {
		ac, bc := rng.Int63n(2_000_001)-1_000_000, rng.Int63n(2_000_001)-1_000_000
		ae, be := int32(rng.Intn(13)-6), int32(rng.Intn(13)-6)
		a, b := New(ac, ae), New(bc, be)
		cmp := selectionRat(ac, ae).Cmp(selectionRat(bc, be))
		if cmp == 0 {
			continue // Equal-cohort direction has directed vectors above.
		}
		wantMin, wantMax := a, b
		if cmp > 0 {
			wantMin, wantMax = b, a
		}
		if got := a.Min(b); got.String() != wantMin.String() {
			t.Fatalf("case %d: Min(%s,%s)=%s, want %s", i, a, b, got, wantMin)
		}
		if got := a.Max(b); got.String() != wantMax.String() {
			t.Fatalf("case %d: Max(%s,%s)=%s, want %s", i, a, b, got, wantMax)
		}
	}
}

func TestSelectionExponentEdgesAndSlowOwnership(t *testing.T) {
	checkPair := func(name string, a, b, wantMin, wantMax Decimal) {
		t.Helper()
		for _, pair := range [][2]Decimal{{a, b}, {b, a}} {
			if got := pair[0].Min(pair[1]); got.String() != wantMin.String() {
				t.Errorf("%s Min(%s,%s)=%s, want %s", name, pair[0], pair[1], got, wantMin)
			}
			if got := pair[0].Max(pair[1]); got.String() != wantMax.String() {
				t.Errorf("%s Max(%s,%s)=%s, want %s", name, pair[0], pair[1], got, wantMax)
			}
		}
	}
	low, high := New(0, math.MinInt32), New(0, math.MaxInt32)
	checkPair("zero far endpoints", low, high, low, high)
	positiveA, positiveB := New(1, math.MaxInt32), New(10, math.MaxInt32-1)
	checkPair("positive max-endpoint tie", positiveA, positiveB, positiveB, positiveA)
	negativeA, negativeB := New(-1, math.MaxInt32), New(-10, math.MaxInt32-1)
	checkPair("negative max-endpoint tie", negativeA, negativeB, negativeA, negativeB)
	minPositiveA, minPositiveB := New(10, math.MinInt32), New(1, math.MinInt32+1)
	checkPair("positive min-endpoint tie", minPositiveA, minPositiveB, minPositiveA, minPositiveB)
	minNegativeA, minNegativeB := New(-10, math.MinInt32), New(-1, math.MinInt32+1)
	checkPair("negative min-endpoint tie", minNegativeA, minNegativeB, minNegativeB, minNegativeA)
	farPositiveLow, farPositiveHigh := New(1, math.MinInt32), New(1, math.MaxInt32)
	checkPair("far positive endpoints", farPositiveLow, farPositiveHigh, farPositiveLow, farPositiveHigh)
	farNegativeLow, farNegativeHigh := New(-1, math.MinInt32), New(-1, math.MaxInt32)
	checkPair("far negative endpoints", farNegativeLow, farNegativeHigh, farNegativeHigh, farNegativeLow)

	literal := strings.Repeat("9", 1_000) + "E-100"
	shared := MustParse(literal)
	if shared.slow == nil {
		t.Fatal("large test operand did not use slow storage")
	}
	sharedCopy := shared
	before := shared.String()
	if sharedCopy.Sign() != 1 || sharedCopy.IsZero() {
		t.Fatal("shallow copy sign or zero inspection changed")
	}
	if got := sharedCopy.Neg(); got.slow != shared.slow || got.Sign() != -1 {
		t.Fatalf("Neg copied or changed slow coefficient: text=%s exponent=%d", got.String(), got.exponent())
	}
	negativeShared := sharedCopy.Neg()
	if got := negativeShared.Abs(); got.slow != shared.slow || got.Sign() != 1 {
		t.Fatalf("Abs copied or changed slow coefficient: text=%s exponent=%d", got.String(), got.exponent())
	}
	if got := sharedCopy.Max(One()); got.slow != shared.slow || got.String() != before {
		t.Fatal("Max did not return the chosen slow operand")
	}
	if got := negativeShared.Min(One()); got.slow != shared.slow || got.String() != negativeShared.String() {
		t.Fatal("Min did not return the chosen negative slow operand")
	}
	if got := sharedCopy.Min(One()); got.String() != "1" {
		t.Fatalf("Min selected %s, want 1", got)
	}
	if got := sharedCopy.Compare(shared); got != 0 {
		t.Fatalf("shallow copy Compare=%d, want 0", got)
	}
	if got := sharedCopy.Reduce(); got.String() != before {
		t.Fatalf("shallow copy Reduce=%s, want %s", got, before)
	}
	if shared.String() != before || sharedCopy.String() != before {
		t.Fatal("shared slow operand or its shallow copy changed")
	}
}

func TestSelectionConcurrentSharedSlowReads(t *testing.T) {
	shared := MustParse(strings.Repeat("7", 500) + "E-200")
	if shared.slow == nil {
		t.Fatal("expected slow storage")
	}
	want := shared.String()
	start := make(chan struct{})
	var wg sync.WaitGroup
	for worker := range 6 {
		wg.Go(func() {
			<-start
			for range 100 {
				if shared.Sign() != 1 || shared.IsZero() || shared.Neg().Abs().String() != want ||
					shared.Max(One()).String() != want || shared.Min(One()).String() != "1" {
					t.Errorf("worker %d observed changed selection state", worker)
					return
				}
			}
		})
	}
	close(start)
	wg.Wait()
	if shared.String() != want {
		t.Fatal("shared value changed after concurrent reads")
	}
}
