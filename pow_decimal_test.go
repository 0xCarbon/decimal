// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"testing"
)

// oraclePow encloses |x|^y = exp(y·ln|x|) from the oracle's ln and exp.
func oraclePow(x, y Decimal, prec uint) (lo, hi *big.Rat) {
	l, h := oracleLn(x.Abs(), prec+64)
	yr := oracleRat(y)
	a, b := new(big.Rat).Mul(yr, l), new(big.Rat).Mul(yr, h)
	if a.Cmp(b) > 0 {
		a, b = b, a
	}
	lo, _ = oracleExp(a, prec+64)
	_, hi = oracleExp(b, prec+64)
	return lo, hi
}

// TestPowDecimalMatchesOracleInEveryMode checks that every mode certifies
// nontrivial values for noninteger PowDecimal.
func TestPowDecimalMatchesOracleInEveryMode(t *testing.T) {
	rng := rand.New(rand.NewPCG(66, 4))
	checked := 0
	for i := range 400 {
		x := randomElementaryInput(rng, false)
		y := randomElementaryInput(rng, rng.IntN(2) == 0)
		if y.Reduce().Exponent() >= 0 {
			continue // integral: covered by the Pow differential
		}
		lx := oracleRat(x)
		if lx.Cmp(big.NewRat(1, 1000)) < 0 || oracleRat(y.Abs()).Cmp(big.NewRat(40, 1)) > 0 {
			continue
		}
		p := uint32(1 + rng.IntN(40))
		mode := inexactModes[i%len(inexactModes)]
		got, c, err := x.PowDecimalWithContext(y, mustContext(t, p, mode))
		if err == nil && c&Inexact == 0 {
			continue // an exact power; the exact controls cover those
		}
		want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) { return oraclePow(x, y, prec) }, int64(p), mode)
		oracleMatch(t, fmt.Sprintf("%s^%s p=%d %v", x, y, p, mode), got, c, err, want)
		checked++
	}
	if checked < 150 {
		t.Fatalf("only %d cases checked", checked)
	}
}

// TestPowDecimalExactCohortsAndTies covers rational power midpoints
// and directions and the exact cohorts of noninteger powers.
func TestPowDecimalExactCohortsAndTies(t *testing.T) {
	for _, tc := range []struct{ x, y, want string }{
		{"4", "0.5", "2"}, {"4.00", "0.5", "2"}, {"32", "0.2", "2"}, {"1024", "0.1", "2"},
		{"0.25", "0.5", "0.5"}, {"100", "0.5", "1E+1"}, {"4", "1.5", "8"}, {"4", "-1.5", "0.125"},
		{"5.0625", "0.5", "2.25"}, {"1E+10", "0.5", "1E+5"}, {"1", "0.123", "1"}, {"-1", "1E+10", "1"},
		{"-1", "10000000001", "-1"}, {"1", "-1E+300", "1"}, {"0", "0.5", "0"}, {"0.0", "12.5", "0"},
		{"1E-100", "0.25", "1E-25"}, {"16", "0.25", "2"}, {"6.25", "-0.5", "0.4"},
	} {
		x, _ := Parse(tc.x)
		y, _ := Parse(tc.y)
		got, err := x.PowDecimal(y)
		if err != nil || got.String() != tc.want {
			t.Fatalf("%s^%s = %s %v, want %s", tc.x, tc.y, got, err, tc.want)
		}
	}
	// (81/16)^0.5 = 2.25 is an exact midpoint at two digits.
	x, _ := Parse("5.0625")
	y, _ := Parse("0.5")
	for _, tc := range []struct {
		mode RoundingMode
		want string
		c    Conditions
	}{
		{TiesToEven, "2.2", Inexact | Rounded | Decreased},
		{TiesAwayFromZero, "2.3", Inexact | Rounded | Increased},
		{TiesTowardZero, "2.2", Inexact | Rounded | Decreased},
		{TowardZero, "2.2", Inexact | Rounded | Decreased},
		{AwayFromZero, "2.3", Inexact | Rounded | Increased},
		{TowardPositiveInfinity, "2.3", Inexact | Rounded | Increased},
		{TowardNegativeInfinity, "2.2", Inexact | Rounded | Decreased},
	} {
		// A finite quota turns a skipped exact filter into a refusal
		// instead of endless refinement around the midpoint.
		got, c, err := x.PowDecimalWithContext(y, mustContext(t, 2, tc.mode).WithBudget(Budget{MaxWork: 1 << 24}))
		if err != nil || got.String() != tc.want || c != tc.c {
			t.Fatalf("2.25 %v = %s %v %v", tc.mode, got, c, err)
		}
	}
	if _, _, err := x.PowDecimalWithContext(y, mustContext(t, 2, Exact)); !errors.Is(err, ErrInexact) {
		t.Fatalf("Exact tie: %v", err)
	}
	got, c, err := x.PowDecimalWithContext(y, mustContext(t, 3, Exact))
	if err != nil || got.String() != "2.25" || c != 0 {
		t.Fatalf("Exact fit: %s %v %v", got, c, err)
	}
	// 4^0.5 at precision 5 is exactly 2, without GDA's forced Inexact.
	got, c, err = New(4, 0).PowDecimalWithContext(y, mustContext(t, 5, TiesToEven))
	if err != nil || got.String() != "2" || c != 0 {
		t.Fatalf("4^0.5 context: %s %v %v", got, c, err)
	}
	// (9/4)^−0.5 = 2/3: rational, not a finite decimal.
	x, _ = Parse("2.25")
	y, _ = Parse("-0.5")
	var ce *Error
	if _, err := x.PowDecimal(y); !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Remedy != powDecimalRemedy {
		t.Fatalf("2/3 bare: %v", err)
	}
	if _, _, err := x.PowDecimalWithContext(y, mustContext(t, 9, Exact)); !errors.Is(err, ErrInexact) {
		t.Fatalf("2/3 Exact: %v", err)
	}
	got, c, err = x.PowDecimalWithContext(y, mustContext(t, 5, TiesToEven))
	if err != nil || got.String() != "0.66667" || c != Inexact|Rounded|Increased {
		t.Fatalf("2/3 context: %s %v %v", got, c, err)
	}
	// Cohort zeros restore toward an integral cohort only as far as fit.
	got, c, err = New(1, 0).PowDecimalWithContext(New(1, 12), mustContext(t, 4, TiesToEven))
	if err != nil || got.String() != "1" || c != 0 {
		t.Fatalf("1^1E12: %s %v %v", got, c, err)
	}
	one, _ := Parse("1.0")
	got, c, err = one.PowDecimalWithContext(New(1, 12), mustContext(t, 4, TiesToEven))
	if err != nil || got.String() != "1.000" || c != Rounded {
		t.Fatalf("1.0^1E12: %s %v %v", got, c, err)
	}
}

// TestPowDecimalDomains covers domains and full exponent parity.
func TestPowDecimalDomains(t *testing.T) {
	half, _ := Parse("0.5")
	for _, tc := range []struct {
		x, y Decimal
		err  error
	}{
		{New(-4, 0), half, ErrInvalidOperation},
		{New(-8, 0), New(333333, -6), ErrInvalidOperation},
		{New(0, 0), half.Neg(), ErrDivisionByZero},
		{New(0, 3), New(-1, 12), ErrDivisionByZero},
		{New(0, 3), New(1, 12), ErrExponentRange},
	} {
		_, _, err := tc.x.PowDecimalWithContext(tc.y, mustContext(t, 5, TiesToEven).WithBudget(Budget{}))
		if !errors.Is(err, tc.err) {
			t.Fatalf("%s^%s: %v, want %v", tc.x, tc.y, err, tc.err)
		}
	}
	// Parity comes from the full exponent, never an int32 truncation.
	for _, tc := range []struct {
		y    string
		want string
	}{{"4294967297", "-2"}, {"4294967296", "2"}, {"1E+10", "2"}, {"12345678901234567891", "-2"}} {
		y, _ := Parse(tc.y)
		got, c, err := New(-2, 0).PowDecimalWithContext(y, Decimal64Context())
		if err != nil || c&Overflow == 0 || got.negative() != (tc.want[0] == '-') {
			t.Fatalf("(-2)^%s: %s %v %v", tc.y, got, c, err)
		}
	}
}

// TestPowDecimalCompactExtremes covers compact extreme-scale
// evaluation: huge and tiny exponents, bases 1, −1, 10 and near one.
func TestPowDecimalCompactExtremes(t *testing.T) {
	huge := New(1, 2147483647)
	tiny := New(1, -2147483648)
	near, _ := Parse("1.0000001")
	ctx := mustContext(t, 16, TiesToEven)
	for _, tc := range []struct {
		x, y Decimal
		want string
		c    Conditions
		err  error
	}{
		{New(1, 0), huge, "1", 0, nil},
		{New(-1, 0), huge, "1", 0, nil},
		{New(10, 0), huge, "", 0, ErrExponentRange},
		{near, huge, "", 0, ErrExponentRange},
		{near.Neg(), huge, "", 0, ErrExponentRange},
		{New(1, 2147483647), tiny, "1.000000000000000", Inexact | Rounded | Decreased, nil},
		{New(1, -2147483648), tiny, "1.000000000000000", Inexact | Rounded | Increased, nil},
		{near, New(1, 10), "1.969972612930461E+434", Inexact | Rounded | Increased, nil},
	} {
		got, c, err := tc.x.PowDecimalWithContext(tc.y, ctx)
		if tc.err != nil {
			if !errors.Is(err, tc.err) {
				t.Fatalf("%s^%s: %s %v %v, want %v", tc.x, tc.y, got, c, err, tc.err)
			}
			continue
		}
		if err != nil || got.String() != tc.want || c != tc.c {
			t.Fatalf("%s^%s = %s %v %v, want %s %v", tc.x, tc.y, got, c, err, tc.want, tc.c)
		}
	}
	d64 := Decimal64Context()
	got, c, err := New(10, 0).PowDecimalWithContext(huge, d64)
	if err != nil || got.String() != "9.999999999999999E+384" || c != Overflow|Inexact|Rounded|Decreased {
		t.Fatalf("10^huge guarded: %s %v %v", got, c, err)
	}
	got, c, err = New(10, 0).PowDecimalWithContext(huge.Neg(), d64)
	if err != nil || !got.isZero() || c != Subnormal|Underflow|Inexact|Rounded|Decreased {
		t.Fatalf("10^-huge guarded: %s %v %v", got, c, err)
	}
}

// TestPowDecimalMatchesPowOnInt32 covers the adaptive public forms on
// the integer subdomain: value, cohort, conditions and refusals equal Pow.
func TestPowDecimalMatchesPowOnInt32(t *testing.T) {
	rng := rand.New(rand.NewPCG(66, 5))
	ctxs := []Context{{}, mustContext(t, 5, TiesToEven), mustContext(t, 3, Exact), mustContext(t, 12, TowardPositiveInfinity), Decimal32Context()}
	for i := range 2000 {
		x := New(rng.Int64N(2001)-1000, int32(rng.IntN(9)-4))
		n := int32(rng.IntN(25) - 12)
		if i%50 == 0 {
			n = int32(rng.IntN(3) - 1)
		}
		ctx := ctxs[i%len(ctxs)]
		// The exponent as a Decimal with random trailing-zero cohorts.
		yz := rng.IntN(3)
		y := New(int64(n)*[]int64{1, 10, 100}[yz], -int32(yz))
		want, wc, werr := x.PowWithContext(n, ctx)
		got, gc, gerr := x.PowDecimalWithContext(y, ctx)
		if (werr == nil) != (gerr == nil) || werr != nil && werr.Error() != "" && !sameErrorIdentity(werr, gerr) {
			t.Fatalf("%s^%d %v: error %v, want %v", x, n, ctx, gerr, werr)
		}
		if werr == nil && (got.String() != want.String() || gc != wc) {
			t.Fatalf("%s^%d %v: %s %v, want %s %v", x, n, ctx, got, gc, want, wc)
		}
	}
}

func sameErrorIdentity(want, got error) bool {
	var wc, gc *Error
	if errors.As(want, &wc) {
		return errors.As(got, &gc) && gc.Condition == wc.Condition
	}
	var wo, gop *Error
	return errors.As(want, &wo) && errors.As(got, &gop) && errors.Is(got, wo.Code)
}

// TestAdaptiveExactShortcutsFinalize checks that exact shortcuts obey
// finalization: an exact result still meets guards, precision and digit
// admission, and a noninteger power whose shortest exponent exceeds
// MaxInt32 keeps only the coefficient zeros it needs.
func TestAdaptiveExactShortcutsFinalize(t *testing.T) {
	below, err := NewContext(3, TiesToEven, &ExponentGuards{Emin: -10, Emax: -1}, 0)
	if err != nil {
		t.Fatal(err)
	}
	got, c, err := Zero().ExpWithContext(below)
	if err != nil || got.String() != "0.999" || c != Overflow|Inexact|Rounded|Decreased {
		t.Fatalf("Exp(0) under Emax −1: %s %v %v", got, c, err)
	}
	got, c, err = New(1, 123456).Log10WithContext(mustContext(t, 3, TiesToEven))
	if err != nil || got.String() != "1.23E+5" || c != Inexact|Rounded|Decreased {
		t.Fatalf("Log10 beyond precision: %s %v %v", got, c, err)
	}
	// (10^1431655766)^1.5 = 10^2147483649 = 100E+2147483647.
	x, y := New(1, 1431655766), New(15, -1)
	got, err = x.PowDecimal(y)
	if err != nil || got.String() != "1.00E+2147483649" || got.Exponent() != 2147483647 {
		t.Fatalf("bare padded cohort: %s %v", got, err)
	}
	got, c, err = x.PowDecimalWithContext(y, mustContext(t, 3, Exact))
	if err != nil || got.String() != "1.00E+2147483649" || c != 0 {
		t.Fatalf("p=3 padded cohort: %s %v %v", got, c, err)
	}
	if _, _, err = x.PowDecimalWithContext(y, mustContext(t, 2, TiesToEven)); !errors.Is(err, ErrExponentRange) {
		t.Fatalf("p=2 unrepresentable: %v", err)
	}
	var limit *Error
	if _, _, err = x.PowDecimalWithContext(y, Context{}.WithBudget(Budget{MaxDigits: 2})); !errors.As(err, &limit) || limit.Resource == 0 || limit.Resource != EvaluationCoefficientDigits {
		t.Fatalf("cohort zeros bypassed the digit cap: %v", err)
	}
}

// TestPowDecimalDigitCapAndCohortRefusals pins digit-cap edge cases: the
// digit cap counts cohort zeros and refuses before allocating on both the
// int32 and the general path; the digit lower bound saturates honestly;
// bare ten-power and other cohorts at exponent 0 share one refusal.
func TestPowDecimalDigitCapAndCohortRefusals(t *testing.T) {
	var limit *Error
	for _, tc := range []struct{ x, y Decimal }{
		{New(10, 0), New(2147483648, 0)}, // S = 1 followed by 2^31 cohort zeros
		{New(10, 0), New(100000000, 0)},  // int32 exponent through Pow
	} {
		var err error
		used := coldAllocatedWithin(func() { _, _, err = tc.x.PowDecimalWithContext(tc.y, Context{}.WithBudget(Budget{MaxDigits: 5})) }, 1024)
		if !errors.As(err, &limit) || limit.Resource == 0 || limit.Resource != EvaluationCoefficientDigits || used > 1024 {
			t.Fatalf("%s^%s cap 5: %v after %d bytes", tc.x, tc.y, err, used)
		}
	}
	three := powBase{c: []uint32{3}}
	r := powValue{m: 1_000_000_000_000, n: 1}
	if r.longer(&three, 1_000_000_000_000) || !r.longer(&three, 100_000_000_000) {
		t.Fatal("3^1E12 has 4.77E11 digits")
	}
	for _, x := range []Decimal{New(10, 0), New(20, 0)} {
		if _, err := x.PowDecimal(New(1, 19)); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("%s^1E19: %v", x, err)
		}
	}
}

// TestPowDecimalMinInt32Cohort checks the one exponent above MaxInt32 whose
// cohort product is a stored exponent: y = 2^31 at a base exponent of −1
// gives y·e = MinInt32, in every spelling of y and for a zero base.
func TestPowDecimalMinInt32Cohort(t *testing.T) {
	const want = "1E-2147483648"
	for _, y := range []string{"2147483648", "2147483648.000", "2.147483648E+9"} {
		exponent := MustParse(y)
		got, err := MustParse("0.1").PowDecimal(exponent)
		if err != nil || got.String() != want {
			t.Fatalf("PowDecimal(0.1, %s) = %v, %v; want %s", y, got, err, want)
		}
		for _, p := range []uint32{1, 7, 16, 34} {
			got, conditions, err := MustParse("0.1").PowDecimalWithContext(exponent, mustContext(t, p, TiesToEven))
			if err != nil || got.String() != want || conditions != 0 {
				t.Fatalf("PowDecimalWithContext(0.1, %s) at precision %d = %v %v, %v; want %s", y, p, got, conditions, err, want)
			}
		}
		if got, err := MustParse("-0.1").PowDecimal(exponent); err != nil || got.String() != want {
			t.Fatalf("PowDecimal(-0.1, %s) = %v, %v; want %s", y, got, err, want)
		}
		zero, err := MustParse("0E-1").PowDecimal(exponent)
		if err != nil || !zero.IsZero() || zero.Exponent() != math.MinInt32 {
			t.Fatalf("PowDecimal(0E-1, %s) = %v, %v; want 0E-2147483648", y, zero, err)
		}
	}
	// The same value through an int32 exponent, and the neighbors that do leave the range.
	for _, c := range [][2]string{{"10", "-2147483648"}, {"0.01", "1073741824"}, {"1E-1073741824", "2"}} {
		if got, err := MustParse(c[0]).PowDecimal(MustParse(c[1])); err != nil || got.String() != want {
			t.Fatalf("PowDecimal(%s, %s) = %v, %v; want %s", c[0], c[1], got, err, want)
		}
	}
	for _, c := range [][2]string{{"0.1", "2147483649"}, {"0.01", "2147483648"}, {"1E+1", "2147483648"}, {"0E-1", "2147483649"}, {"0E+1", "2147483648"}} {
		if got, err := MustParse(c[0]).PowDecimal(MustParse(c[1])); !errors.Is(err, ErrExponentRange) {
			t.Fatalf("PowDecimal(%s, %s) = %v, %v; want the exponent-range refusal", c[0], c[1], got, err)
		}
	}
	if zero, err := MustParse("0E-1").PowDecimal(MustParse("2147483647")); err != nil || zero.Exponent() != -2147483647 {
		t.Fatalf("PowDecimal(0E-1, 2147483647) = %v, %v", zero, err)
	}
}
