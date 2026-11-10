// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"strings"
	"testing"
)

// sumOperands draws k signed operands: mostly short inline coefficients,
// some past 2^128 (limb-held), with exponents spread by up to gap places.
func sumOperands(r *rand.Rand, k int, gap int) []Decimal {
	values := make([]Decimal, k)
	for i := range values {
		digits := 1 + r.IntN(8)
		switch r.IntN(10) {
		case 0:
			digits = 39 + r.IntN(60)
		case 1:
			digits = 20 + r.IntN(19)
		case 2:
			values[i] = zeroDecimal(int32(r.IntN(gap+1) - gap/2))
			continue
		}
		text := make([]byte, digits)
		for j := range text {
			text[j] = byte('0' + r.IntN(10))
		}
		text[0] = byte('1' + r.IntN(9))
		v := MustParse(fmt.Sprintf("%sE%d", text, r.IntN(gap+1)-gap/2))
		if r.IntN(2) == 0 {
			v = v.Neg()
		}
		values[i] = v
	}
	return values
}

// sumOracle is the math/big exact sum and the fold's exponent (the
// smallest operand exponent); the empty sum is zero at 0.
func sumOracle(t *testing.T, values []Decimal) (*big.Rat, int32) {
	t.Helper()
	total := new(big.Rat)
	if len(values) == 0 {
		return total, 0
	}
	exponent := values[0].exponent()
	for _, v := range values {
		total.Add(total, divRat(t, v))
		exponent = min(exponent, v.exponent())
	}
	return total, exponent
}

// TestSumAgainstRationalOracle checks the variadic Sum: the exact
// fold of Add at the smallest operand exponent, with no conditions, equal
// to the math/big sum and to the left fold of Add in value, exponent and
// sign, over inline, limb-held, zero, cancelling and far-apart operands.
func TestSumAgainstRationalOracle(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 11))
	for range 4000 {
		values := sumOperands(r, r.IntN(40), []int{0, 6, 19, 40, 200}[r.IntN(5)])
		got, err := Sum(values...)
		if err != nil {
			t.Fatal(err)
		}
		want, exponent := sumOracle(t, values)
		if divRat(t, got).Cmp(want) != 0 || got.exponent() != exponent {
			t.Fatalf("Sum(%v) = %s, want %s at exponent %d", values, got, want.RatString(), exponent)
		}
		var fold Decimal
		if len(values) > 0 {
			fold = values[0]
			for _, v := range values[1:] {
				if fold, err = fold.Add(v); err != nil {
					t.Fatal(err)
				}
			}
		}
		if !got.Equal(fold) || got.exponent() != fold.exponent() || got.negative() != fold.negative() {
			t.Fatalf("Sum(%v) = %s, fold of Add %s", values, got, fold)
		}
	}
}

// TestSumInlineMatchesLimbs pins the 256-bit inline fast path to the limb
// path it may replace (fast paths never own semantics), over
// random inline operands within 19 exponent places, with a guard that
// results past 2^128 and exact cancellation are exercised.
func TestSumInlineMatchesLimbs(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 12))
	var wide, cancelled int
	for range 20000 {
		k := 1 + r.IntN(30)
		values := make([]Decimal, k)
		for i := range values {
			digits := 1 + r.IntN(38)
			text := make([]byte, digits)
			for j := range text {
				text[j] = byte('0' + r.IntN(10))
			}
			values[i] = MustParse(fmt.Sprintf("%sE%d", text, r.IntN(20)))
			if r.IntN(2) == 0 {
				values[i] = values[i].Neg()
			}
		}
		if r.IntN(10) == 0 {
			values = append(values, values...)
			for i := k; i < len(values); i++ {
				values[i] = values[i].Neg()
			}
		}
		p, ok := sumScan(values)
		if !ok || !p.inline {
			t.Fatalf("plan %+v for inline operands", p)
		}
		inline := sumInline(values, p.shape.MinExponent)
		general, err := sumLimbs(values, p, "Sum")
		if err != nil || !inline.Equal(general) || inline.exponent() != general.exponent() || inline.negative() != general.negative() || (inline.slow == nil) != (general.slow == nil) {
			t.Fatalf("inline %s (%v), limbs %s (%v)", inline, inline.slow == nil, general, err)
		}
		if inline.slow != nil {
			wide++
		}
		if inline.isZero() && p.shape.Nonzero {
			cancelled++
		}
	}
	// Coefficients of 2^128 − 1 at offset 19 carry into the top accumulator
	// word.
	top := inlineDecimal(uint128{^uint64(0), ^uint64(0)}, 19, false)
	for _, values := range [][]Decimal{
		{top, top, New(1, 0)},
		{top, top, top, top, top, top, top, top, New(-1, 0)},
		{top.Neg(), top.Neg(), top, New(3, 5)},
		// 2·(2^128−1)·10^19 − c·10^19 = 2^192 + r with r < 2^64: words
		// {r, 0, 0, 1}, the top word set while the third is zero (a zero
		// at exponent 0 puts emin, and so the scale, at 10^19).
		{top, top, MustParse("-52854560303208850543170272542769781299E+19"), New(0, 0)},
	} {
		p, _ := sumScan(values)
		inline := sumInline(values, p.shape.MinExponent)
		general, err := sumLimbs(values, p, "Sum")
		want, _ := sumOracle(t, values)
		if err != nil || !inline.Equal(general) || divRat(t, inline).Cmp(want) != 0 {
			t.Fatalf("top-word carry: inline %s, limbs %s (%v), want %s", inline, general, err, want.RatString())
		}
	}
	if wide < 100 || cancelled < 100 {
		t.Fatalf("vacuous: %d results past 2^128, %d cancellations", wide, cancelled)
	}
}

// TestSumEdges pins Sum's edges: the empty sum is 0E0, all-zero operands
// give zero at the smallest exponent, exact cancellation gives unsigned
// zero at that exponent, and the result keeps the largest scale.
func TestSumEdges(t *testing.T) {
	for _, tc := range []struct {
		values []string
		want   string
	}{
		{nil, "0"},
		{[]string{"0E-3", "0E+2"}, "0.000"},
		{[]string{"1.5", "-1.50"}, "0.00"},
		{[]string{"-2", "1"}, "-1"},
		{[]string{"1.10", "2.2", "3"}, "6.30"},
		{[]string{"1E+10", "1E-10"}, "10000000000.0000000001"},
	} {
		values := make([]Decimal, len(tc.values))
		for i, s := range tc.values {
			values[i] = MustParse(s)
		}
		got, err := Sum(values...)
		if err != nil || got.String() != tc.want || got.IsZero() && got.negative() {
			t.Fatalf("Sum(%v) = %s (%v), want %s", tc.values, got, err, tc.want)
		}
	}
}

// TestSumBudget checks the Sum tariff: the smallest admitting
// work cap is k + Σdᵢ + 2·t(L), the smallest admitting digit cap is the
// envelope L = amax − emin + 1 + ⌈log10 k⌉ (refused before anything is
// allocated), and a far-apart operand makes the envelope, and so the
// charge, grow as the exact result does.
func TestSumBudget(t *testing.T) {
	for _, tc := range [][]string{
		{"7.25"},
		{"1", "2", "3", "4", "5", "6", "7", "8", "9", "10"},
		{"1.5", "2.25", "-3"},
		{"99", "1"},
		{"9", "9", "9", "9", "9", "9", "9", "9", "9", "9", "9"},
		{strings.Repeat("9", 60), "1E-5", "-7"},
		{"1E+300", "1E-300"},
	} {
		values := make([]Decimal, len(tc))
		var digits uint64
		for i, s := range tc {
			values[i] = MustParse(s)
			digits += values[i].CoefficientDigits()
		}
		want, err := Sum(values...)
		if err != nil {
			t.Fatal(err)
		}
		// The envelope from the definition, independently of sumScan:
		// amax − emin + 1 + ⌈log10 k⌉.
		emin, amax := values[0].exponent(), int64(math.MinInt64)
		for _, v := range values {
			emin = min(emin, v.exponent())
			amax = max(amax, int64(v.exponent())+int64(v.CoefficientDigits())-1)
		}
		carries := uint64(len(fmt.Sprint(len(values) - 1)))
		if len(values) == 1 {
			carries = 0
		}
		envelope := uint64(amax-int64(emin)+1) + carries
		p := sumPlan{envelope: envelope}
		work := smallestAdmitting(1<<40, func(w uint64) bool {
			_, err := SumWithBudget(values, Budget{MaxWork: w})
			return err == nil
		})
		if expect := uint64(len(values)) + digits + 2*(1+(p.envelope-1)/9); work != expect {
			t.Fatalf("Sum(%v): smallest admitting work %d, want k + Σd + 2·t(L) = %d", tc, work, expect)
		}
		cap := smallestAdmitting(1<<20, func(n uint64) bool {
			_, err := SumWithBudget(values, Budget{MaxDigits: n})
			return err == nil
		})
		if cap != p.envelope {
			t.Fatalf("Sum(%v): smallest admitting digit cap %d, want the envelope %d", tc, cap, p.envelope)
		}
		got, err := SumWithBudget(values, Budget{MaxDigits: cap, MaxWork: work})
		if err != nil || !got.Equal(want) || got.exponent() != want.exponent() {
			t.Fatalf("Sum(%v) budgeted %s (%v), want %s", tc, got, err, want)
		}
		if heap := coldAllocatedWithin(func() {
			_, _ = SumWithBudget(values, Budget{MaxDigits: cap - 1})
		}, 128); heap > 128 {
			t.Fatalf("Sum(%v): digit refusal allocated %d bytes", tc, heap)
		}
	}
	if _, err := SumWithBudget([]Decimal{MustParse("1"), MustParse("2"), MustParse("3")}, Budget{MaxWork: 2}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("header precharge: %v", err)
	}
}

// TestSumAllocations pins the allocation class of Sum: inline
// operands with an inline result allocate nothing, and a limb-held result
// of at most 81 digits costs one allocation.
func TestSumAllocations(t *testing.T) {
	small := []Decimal{MustParse("1.25"), MustParse("-3.5"), MustParse("100")}
	if n := testing.AllocsPerRun(100, func() { _, _ = Sum(small...) }); n != 0 {
		t.Fatalf("inline Sum: %v allocations", n)
	}
	wide := []Decimal{MustParse(strings.Repeat("9", 38)), MustParse(strings.Repeat("9", 38)), MustParse("1E-30")}
	if n := testing.AllocsPerRun(100, func() { _, _ = Sum(wide...) }); n != 1 {
		t.Fatalf("limb-held Sum: %v allocations", n)
	}
}

// TestSumEstimateMatchesPhysicalAdmission pins that EstimateSum
// and Sum share one scratch plan, so on 32-bit targets, where 2·(t(L)+1)
// limbs for an envelope of four billion digits exceed the addressable
// window, both refuse; on 64-bit targets the plan is admitted by both.
func TestSumEstimateMatchesPhysicalAdmission(t *testing.T) {
	values := []Decimal{New(1, 2_000_000_000), New(1, -2_000_000_000)}
	p, _ := sumScan(values)
	_, _, planErr := sumScratch(p.envelope, "Sum")
	_, estimateErr := EstimateSum(ShapeOfSum(values...))
	if (planErr == nil) != (estimateErr == nil) {
		t.Fatalf("plan %v, estimate %v", planErr, estimateErr)
	}
	if bits.UintSize == 32 {
		if !errors.Is(estimateErr, ErrInsufficientStorage) {
			t.Fatalf("32-bit estimate admitted a four-billion-digit envelope")
		}
		if _, err := Sum(values...); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("32-bit Sum: %v", err)
		}
	}
}
