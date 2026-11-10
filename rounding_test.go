// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math/big"
	"math/rand/v2"
	"strings"
	"testing"
)

// roundingOperand draws a signed decimal with up to maxDigits coefficient
// digits at an exponent in [lo, hi].
func roundingOperand(r *rand.Rand, maxDigits int, lo, hi int32) Decimal {
	digits := 1 + r.IntN(maxDigits)
	text := make([]byte, digits)
	for i := range text {
		text[i] = byte('0' + r.IntN(10))
	}
	if r.IntN(8) == 0 {
		text[len(text)-1] = '5' // bias toward ties
	}
	d := MustParse(fmt.Sprintf("%sE%d", text, lo+int32(r.IntN(int(hi-lo+1)))))
	if r.IntN(2) == 0 {
		d = d.Neg()
	}
	return d
}

// roundingExpect checks one directed outcome against an exact oracle value
// and a changed flag: the numeric result, its exponent, and the Conditions
// Inexact|Rounded plus the direction exactly when the value changed, or
// the Exact refusal.
func roundingExpect(t *testing.T, label string, got Decimal, conditions Conditions, err error, want *big.Rat, exponent int32, changed bool, exact *big.Rat, mode RoundingMode) {
	t.Helper()
	if mode == Exact && changed {
		var ce *Error
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || !got.Equal(Decimal{}) {
			t.Fatalf("%s: (%v, %v, %v), want the Exact refusal", label, got, conditions, err)
		}
		return
	}
	if err != nil {
		t.Fatalf("%s: %v", label, err)
	}
	if divRat(t, got).Cmp(want) != 0 || got.Exponent() != exponent {
		t.Fatalf("%s: %s, want %s at exponent %d", label, got, want.RatString(), exponent)
	}
	wantConditions := Conditions(0)
	if changed {
		wantConditions = Inexact | Rounded | oracleDirection(want, exact)
	}
	if conditions != wantConditions {
		t.Fatalf("%s: conditions %v, want %v", label, conditions, wantConditions)
	}
}

// TestRoundToMultipleAgainstRationalOracle checks every mode: r·m with r the
// integer nearest the exact rational v/m (a math/big oracle), at m's exponent,
// exact iff v/m is integral, with the result direction.
func TestRoundToMultipleAgainstRationalOracle(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 1))
	for range 20000 {
		v := roundingOperand(r, 30, -25, 15)
		m := roundingOperand(r, 6, -6, 3).Abs()
		if m.IsZero() {
			continue
		}
		mode := allDivModes[r.IntN(len(allDivModes))]
		exact := divRat(t, v)
		mRat := divRat(t, m)
		quotient := new(big.Rat).Quo(new(big.Rat).Abs(exact), mRat)
		n, changed := oracleRound(quotient, mode, v.Sign() < 0)
		want := new(big.Rat).Mul(new(big.Rat).SetInt(n), mRat)
		if v.Sign() < 0 {
			want.Neg(want)
		}
		got, conditions, err := v.RoundToMultiple(m, mode)
		roundingExpect(t, fmt.Sprintf("RoundToMultiple(%s, %s, %v)", v, m, mode), got, conditions, err, want, m.Exponent(), changed, exact, mode)
		if err == nil && got.IsZero() && got.Sign() != 0 {
			t.Fatalf("RoundToMultiple(%s, %s): signed zero", v, m)
		}
	}
}

// TestRoundToMultipleVectors pins the documented scenarios and the
// double-rounding witnesses: cash rounding decided on the exact rational, the
// already-multiple case with no conditions, and the non-positive multiple.
func TestRoundToMultipleVectors(t *testing.T) {
	for _, tc := range []struct {
		v, m       string
		mode       RoundingMode
		want       string
		conditions Conditions
	}{
		{"2.525", "0.05", TiesToEven, "2.50", Inexact | Rounded | Decreased},
		{"2.525", "0.05", TiesAwayFromZero, "2.55", Inexact | Rounded | Increased},
		{"12.35", "0.05", TiesToEven, "12.35", 0},
		{"1.00", "0.5", TiesToEven, "1.0", 0},
		{"1.499999999999999999999999999997", "3", TiesToEven, "0", Inexact | Rounded | Decreased},
		{"-0.03", "0.05", TiesAwayFromZero, "-0.05", Inexact | Rounded | Decreased},
		{"-0.025", "0.05", TiesToEven, "0.00", Inexact | Rounded | Increased},
		{"1.075", "0.05", TiesToEven, "1.10", Inexact | Rounded | Increased},
		{"7", "0.25", TowardZero, "7.00", 0},
	} {
		got, conditions, err := MustParse(tc.v).RoundToMultiple(MustParse(tc.m), tc.mode)
		if err != nil || got.String() != tc.want || conditions != tc.conditions {
			t.Fatalf("RoundToMultiple(%s, %s, %v) = (%s, %v, %v), want (%s, %v)", tc.v, tc.m, tc.mode, got, conditions, err, tc.want, tc.conditions)
		}
	}
	for _, m := range []string{"0", "0E-5", "-0.05"} {
		if _, _, err := MustParse("1").RoundToMultiple(MustParse(m), TiesToEven); !errors.Is(err, ErrInvalidOperation) {
			t.Fatalf("RoundToMultiple(1, %s): %v, want ErrInvalidOperation", m, err)
		}
	}
	if _, _, err := MustParse("1").RoundToMultiple(MustParse("1"), Exact+1); !errors.Is(err, ErrInvalidContext) {
		t.Fatalf("invalid mode: %v", err)
	}
}

// TestRoundToMultipleBudget checks the RoundToMultiple tariff:
// the smallest admitting work cap is the DivToExponent charge completed
// with the quotient's digits, plus the Mul charge of r·m, and the digit
// cap is the envelope digits(r) + digits(m); a far-away tiny value costs
// work independent of the exponent gap.
func TestRoundToMultipleBudget(t *testing.T) {
	for _, tc := range []struct{ v, m string }{
		{"123456.789", "0.05"},
		{"98765432109876543210.5", "0.25"},
		{"1E-100000", "0.05"},
		{"1E-1000", "0.05"},
	} {
		v, m := MustParse(tc.v), MustParse(tc.m)
		want, wantConditions, err := v.RoundToMultiple(m, TiesToEven)
		if err != nil {
			t.Fatal(err)
		}
		work := smallestAdmitting(1<<40, func(w uint64) bool {
			_, _, err := v.RoundToMultipleWithBudget(m, TiesToEven, Budget{MaxWork: w})
			return err == nil
		})
		got, conditions, err := v.RoundToMultipleWithBudget(m, TiesToEven, Budget{MaxWork: work})
		if err != nil || !got.Equal(want) || got.Exponent() != want.Exponent() || conditions != wantConditions {
			t.Fatalf("%s to %s: budgeted (%s, %v, %v), want (%s, %v)", tc.v, tc.m, got, conditions, err, want, wantConditions)
		}
		if tc.v[:2] == "1E" && work > 64 {
			t.Fatalf("%s to %s: tiny value charged %d work units", tc.v, tc.m, work)
		}
		quotient, _, _ := v.DivToExponent(inlineDecimal(m.words, 0, false), m.Exponent(), TiesToEven)
		nr, dm := max(quotient.CoefficientDigits(), 1), m.CoefficientDigits()
		digits := smallestAdmitting(1<<20, func(n uint64) bool {
			_, _, err := v.RoundToMultipleWithBudget(m, TiesToEven, Budget{MaxDigits: n})
			return err == nil
		})
		if quotient.IsZero() {
			nr, dm = 1, 0
		}
		if digits != nr+dm {
			t.Fatalf("%s to %s: smallest admitting digit cap %d, want the envelope %d", tc.v, tc.m, digits, nr+dm)
		}
	}
}

// TestRoundToPrecisionAgainstOracle checks the significant-digit
// target in every mode against the math/big precision oracle: GDA plus,
// unchanged when the value fits, otherwise one rounding with Inexact or
// a zero-only Rounded, and the direction.
func TestRoundToPrecisionAgainstOracle(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 2))
	for range 20000 {
		v := roundingOperand(r, 40, -30, 30)
		precision := uint32(1 + r.IntN(40))
		mode := allDivModes[r.IntN(len(allDivModes))]
		got, conditions, err := v.RoundToPrecision(precision, mode)
		label := fmt.Sprintf("RoundToPrecision(%s, %d, %v)", v, precision, mode)
		oracleMode := mode
		if mode == Exact {
			oracleMode = TowardZero
		}
		coefficient, exponent, negative, oracleConditions := contextOracle(v, zeroDecimal(v.exponent()), "add", precision, oracleMode)
		if mode == Exact && oracleConditions&Inexact != 0 {
			if _, ok := errors.AsType[*Error](err); !ok {
				t.Fatalf("%s: (%v, %v, %v), want the Exact refusal", label, got, conditions, err)
			}
			continue
		}
		if err != nil {
			t.Fatalf("%s: %v", label, err)
		}
		want := coefficient + fmt.Sprintf("E%d", exponent)
		if negative {
			want = "-" + want
		}
		w := MustParse(want)
		if !got.Equal(w) || got.Exponent() != w.Exponent() {
			t.Fatalf("%s = %s, want %s", label, got, w)
		}
		if oracleConditions&Inexact != 0 {
			oracleConditions |= oracleDirection(divRat(t, w), divRat(t, v))
		}
		if conditions != oracleConditions {
			t.Fatalf("%s: conditions %v, want %v", label, conditions, oracleConditions)
		}
	}
}

// TestRoundToPrecisionIdentityAndEdges pins RoundToPrecision's edges:
// a fitting value keeps its cohort with no Conditions, precision 0 and
// Context{} are the identity, an invalid direct mode is InvalidContext
// first, Exact permits a zero-only discard, zero keeps its exponent, and
// guards apply through the context finisher.
func TestRoundToPrecisionIdentityAndEdges(t *testing.T) {
	check := func(label string, got Decimal, conditions Conditions, err error, want string, wantConditions Conditions) {
		t.Helper()
		if err != nil || got.String() != want || conditions != wantConditions {
			t.Fatalf("%s = (%s, %v, %v), want (%s, %v)", label, got, conditions, err, want, wantConditions)
		}
	}
	got, c, err := MustParse("1.20").RoundToPrecision(3, TiesToEven)
	check("1.20 at 3", got, c, err, "1.20", 0)
	got, c, err = MustParse("12345").RoundToPrecision(3, TiesToEven)
	check("12345 at 3", got, c, err, "1.23E+4", Inexact|Rounded|Decreased)
	got, c, err = MustParse("1.2000").RoundToPrecision(2, Exact)
	check("1.2000 at 2 Exact", got, c, err, "1.2", Rounded)
	got, c, err = MustParse("0E-7").RoundToPrecision(1, TiesToEven)
	check("0E-7 at 1", got, c, err, "0E-7", 0)
	got, c, err = MustParse("123.456").RoundToPrecision(0, TiesToEven)
	check("precision 0", got, c, err, "123.456", 0)
	got, c, err = MustParse("123.456").RoundToPrecisionWithContext(Context{})
	check("Context{}", got, c, err, "123.456", 0)
	if _, _, err := MustParse("1").RoundToPrecision(0, Exact+1); !errors.Is(err, ErrInvalidContext) {
		t.Fatalf("invalid mode: %v", err)
	}
	if _, _, err := MustParse("1.25").RoundToPrecision(2, Exact); err == nil {
		t.Fatal("Exact accepted a nonzero discard")
	}
	guarded, err := NewContext(3, TiesToEven, &ExponentGuards{Emin: -10, Emax: 10}, 0)
	if err != nil {
		t.Fatal(err)
	}
	got, c, err = MustParse("1.5E+11").RoundToPrecisionWithContext(guarded)
	check("overflow", got, c, err, "9.99E+10", Overflow|Inexact|Rounded|Decreased)
	got, c, err = MustParse("1.234E-11").RoundToPrecisionWithContext(guarded)
	check("subnormal", got, c, err, "1.2E-11", Subnormal|Underflow|Inexact|Rounded|Decreased)
	work := smallestAdmitting(1<<20, func(w uint64) bool {
		_, _, err := MustParse("123456789").RoundToPrecisionWithContext(guarded.WithBudget(Budget{MaxWork: w}))
		return err == nil
	})
	if work != 9+2*3+1 {
		t.Fatalf("RoundToPrecision work %d, want B + 2N + 1 = %d", work, 9+2*3+1)
	}
}

// TestRoundToMultipleRefusesBeforeAllocating checks that a digit cap
// below the quotient's minimum length plus digits(m) refuses before the
// division scratch is allocated, and an invalid mode is InvalidContext for
// RoundToMultiple and for the DivToExponent core it shares.
func TestRoundToMultipleRefusesBeforeAllocating(t *testing.T) {
	// A quotient beyond the stack scratch. The smallest admitting cap is the
	// envelope N_r + dm; every cap up to N_r = admit − dm refuses before the
	// heap scratch, because the quotient's minimum length already exceeds
	// cap − dm, including caps the quotient alone would fit. Caps in
	// (N_r, N_r + dm) may allocate the division scratch, as DivToExponent
	// does, and refuse before the product.
	v := MustParse(strings.Repeat("7", 3000) + "E-5")
	m := MustParse("0.25")
	admit := smallestAdmitting(1<<20, func(n uint64) bool {
		_, _, err := v.RoundToMultipleWithBudget(m, TiesToEven, Budget{MaxDigits: n})
		return err == nil
	})
	for limit := admit - 6; limit <= admit-m.CoefficientDigits(); limit++ {
		budget := Budget{MaxDigits: limit}
		if _, _, err := v.RoundToMultipleWithBudget(m, TiesToEven, budget); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("cap %d: %v", limit, err)
		}
		if heap := coldAllocatedWithin(func() { _, _, _ = v.RoundToMultipleWithBudget(m, TiesToEven, budget) }, 256); heap > 256 {
			t.Fatalf("cap %d: refusal allocated %d bytes before refusing", limit, heap)
		}
	}
	for _, call := range []func() error{
		func() error { _, _, err := v.RoundToMultiple(m, Exact+1); return err },
		func() error { _, _, err := v.DivToExponent(m, 0, Exact+1); return err },
	} {
		if err := call(); !errors.Is(err, ErrInvalidContext) {
			t.Fatalf("invalid mode: %v", err)
		}
	}
}

// TestRoundToMultipleSlowResults extends the rational oracle to limb-held
// operands and results: values up to 300 digits and multiples
// up to 60 digits, whose products exceed the inline and small-holder
// bands, against the exact math/big rational in every mode.
func TestRoundToMultipleSlowResults(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 4))
	var wide int
	for range 3000 {
		v := roundingOperand(r, 300, -150, 150)
		m := roundingOperand(r, 60, -30, 30).Abs()
		if m.IsZero() {
			continue
		}
		mode := allDivModes[r.IntN(len(allDivModes))]
		exact := divRat(t, v)
		mRat := divRat(t, m)
		n, changed := oracleRound(new(big.Rat).Quo(new(big.Rat).Abs(exact), mRat), mode, v.Sign() < 0)
		want := new(big.Rat).Mul(new(big.Rat).SetInt(n), mRat)
		if v.Sign() < 0 {
			want.Neg(want)
		}
		got, conditions, err := v.RoundToMultiple(m, mode)
		roundingExpect(t, fmt.Sprintf("RoundToMultiple(%s, %s, %v)", v, m, mode), got, conditions, err, want, m.Exponent(), changed, exact, mode)
		if got.CoefficientDigits() > 90 {
			wide++
		}
	}
	if wide < 300 {
		t.Fatalf("vacuous: %d results over 90 digits", wide)
	}
}

// TestRoundToMultipleChargesAndEarlyRefusals pins the RoundToMultiple
// budget edges:
//   - a zero value costs exactly W = 4, as its estimate says;
//   - a tiny value whose quotient rounds to zero costs exactly the
//     DivToExponent estimate of the quotient;
//   - a work cap below the division's precharge refuses before its scratch;
//   - every digit cap at or below digits(m) refuses before any scratch when
//     |v| ≥ m, since only a zero quotient could fit.
func TestRoundToMultipleChargesAndEarlyRefusals(t *testing.T) {
	smallestWork := func(v, m Decimal) uint64 {
		return smallestAdmitting(1<<40, func(w uint64) bool {
			_, _, err := v.RoundToMultipleWithBudget(m, TiesToEven, Budget{MaxWork: w})
			return err == nil
		})
	}
	m := MustParse("0.05")
	if work := smallestWork(MustParse("0E-9"), m); work != 4 {
		t.Fatalf("zero value: work %d, want 4", work)
	}
	if c, _ := EstimateRoundToMultiple(Shape{Exponent: -9}, m.Shape()); c.WorkUnits != 4 {
		t.Fatalf("zero-value estimate %+v", c)
	}
	tiny := MustParse("1E-1000")
	want, _ := EstimateDivToExponent(tiny.Shape(), Shape{Digits: m.CoefficientDigits()}, m.Exponent())
	if work := smallestWork(tiny, m); work != want.WorkUnits {
		t.Fatalf("tiny value: work %d, want the DivToExponent estimate %d", work, want.WorkUnits)
	}
	long := MustParse(strings.Repeat("7", 5001) + "E-2")
	large := MustParse(strings.Repeat("3", 5000) + "E-2")
	refusal := func(budget Budget) {
		t.Helper()
		if _, _, err := long.RoundToMultipleWithBudget(large, TiesToEven, budget); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("%+v: %v", budget, err)
		}
		if heap := coldAllocatedWithin(func() { _, _, _ = long.RoundToMultipleWithBudget(large, TiesToEven, budget) }, 256); heap > 256 {
			t.Fatalf("%+v: refusal allocated %d bytes", budget, heap)
		}
	}
	refusal(Budget{MaxWork: 10})
	for _, limit := range []uint64{1, 2, 4999, 5000} {
		refusal(Budget{MaxDigits: limit})
	}
	// |d| = m at a cap ≤ digits(m): the quotient is exactly 1, so it
	// refuses before any scratch too.
	if _, _, err := large.RoundToMultipleWithBudget(large, TiesToEven, Budget{MaxDigits: 5000}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("|d| = m at cap 5000: %v", err)
	}
	if heap := coldAllocatedWithin(func() {
		_, _, _ = large.RoundToMultipleWithBudget(large, TiesToEven, Budget{MaxDigits: 5000})
	}, 256); heap > 256 {
		t.Fatalf("|d| = m at cap 5000: refusal allocated %d bytes", heap)
	}
}

// TestRoundingAllocationClass pins the allocation class of the
// rounding operations:
// - inline results allocate nothing;
// - a limb-held result of at most 81 digits costs one allocation;
// - longer RoundToMultiple results follow DivToExponent's count.
func TestRoundingAllocationClass(t *testing.T) {
	cash, nickel := MustParse("2.525"), MustParse("0.05")
	long, quarter := MustParse(strings.Repeat("9", 60)+".5"), MustParse("0.25")
	small, hundred := MustParse("12345.678"), MustParse(strings.Repeat("8", 100))
	for _, tc := range []struct {
		name  string
		run   func()
		allow float64
	}{
		{"multiple inline", func() { _, _, _ = cash.RoundToMultiple(nickel, TiesToEven) }, 0},
		{"multiple 62 digits", func() { _, _, _ = long.RoundToMultiple(quarter, TiesToEven) }, 1},
		{"precision inline", func() { _, _, _ = small.RoundToPrecision(4, TiesToEven) }, 0},
		{"precision 60 of 100 digits", func() { _, _, _ = hundred.RoundToPrecision(60, TiesToEven) }, 1},
	} {
		if n := testing.AllocsPerRun(50, tc.run); n != tc.allow {
			t.Fatalf("%s: %v allocations, want %v", tc.name, n, tc.allow)
		}
	}
	v, m := MustParse(strings.Repeat("7", 300)), MustParse("0.25")
	div := testing.AllocsPerRun(20, func() { _, _, _ = v.DivToExponent(inlineDecimal(m.words, 0, false), m.exponent(), TiesToEven) })
	if n := testing.AllocsPerRun(20, func() { _, _, _ = v.RoundToMultiple(m, TiesToEven) }); n > div {
		t.Fatalf("300-digit RoundToMultiple: %v allocations, DivToExponent %v", n, div)
	}
}
