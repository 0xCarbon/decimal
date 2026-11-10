// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math/big"
	"math/rand/v2"
	"testing"
)

// inexactModes are the seven value-changing catalogue modes.
var inexactModes = []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity}

// randomElementaryInput draws a decimal of 1–30 digits with an exponent
// placing it in [10^−8, 10^4).
func randomElementaryInput(rng *rand.Rand, negative bool) Decimal {
	digits := 1 + rng.IntN(30)
	var s []byte
	for i := range digits {
		d := byte('0' + rng.IntN(10))
		if i == 0 && d == '0' {
			d = '1'
		}
		s = append(s, d)
	}
	e := rng.IntN(12) - 8 - digits + 1
	d, err := Parse(fmt.Sprintf("%sE%d", s, e))
	if err != nil {
		panic(err)
	}
	if negative {
		d = d.Neg()
	}
	return d
}

// TestExpMatchesOracleInEveryMode checks that every mode certifies
// nontrivial values for Exp against the independent oracle.
func TestExpMatchesOracleInEveryMode(t *testing.T) {
	rng := rand.New(rand.NewPCG(66, 2))
	checked := 0
	for i := range 300 {
		x := randomElementaryInput(rng, rng.IntN(2) == 0)
		if oracleRat(x).Cmp(big.NewRat(9000, 1)) > 0 || oracleRat(x).Cmp(big.NewRat(-9000, 1)) < 0 {
			continue
		}
		p := uint32(1 + rng.IntN(40))
		if i%25 == 0 {
			p = uint32(60 + rng.IntN(80))
		}
		mode := inexactModes[i%len(inexactModes)]
		xr := oracleRat(x)
		want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) { return oracleExp(xr, prec) }, int64(p), mode)
		got, c, err := x.ExpWithContext(mustContext(t, p, mode))
		oracleMatch(t, fmt.Sprintf("Exp(%s) p=%d %v", x, p, mode), got, c, err, want)
		checked++
	}
	if checked < 250 {
		t.Fatalf("only %d cases checked", checked)
	}
}

// TestExpExactAndRefusals checks the exact zero context and special
// cohorts for Exp: Exp(0) is 1E0, other exact calls refuse with the remedy.
func TestExpExactAndRefusals(t *testing.T) {
	for _, zero := range []Decimal{New(0, 0), New(0, -7), New(0, 5)} {
		got, err := zero.Exp()
		if err != nil || got.String() != "1" || got.Exponent() != 0 {
			t.Fatalf("Exp(%s) = %s, %v", zero, got, err)
		}
		got, c, err := zero.ExpWithContext(mustContext(t, 5, Exact))
		if err != nil || got.String() != "1" || c != 0 {
			t.Fatalf("Exp(0) Exact = %s %v %v", got, c, err)
		}
	}
	var ce *Error
	for _, x := range []Decimal{New(1, 0), New(-1, -30), New(5, 3)} {
		got, err := x.Exp()
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Remedy != expRemedy || ce.Op != "Exp" || !got.isZero() {
			t.Fatalf("Exp(%s) = %s, %v", x, got, err)
		}
		_, c, err := x.ExpWithContext(mustContext(t, 9, Exact))
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || c != 0 {
			t.Fatalf("Exp(%s) Exact: %v %v", x, c, err)
		}
	}
}

// TestExpCompactExtremes checks compact extreme-scale evaluation:
// exp(±1E−2147483648) settles from strict one-sided tails, p=1 selects the
// predecessor 0.9 below one, and far arguments refuse or saturate from the
// range filter without exponent-sized work.
func TestExpCompactExtremes(t *testing.T) {
	tiny := New(1, -2147483648)
	cases := []struct {
		x    Decimal
		p    uint32
		mode RoundingMode
		want string
		c    Conditions
	}{
		{tiny, 1, TowardZero, "1", Inexact | Rounded | Decreased},
		{tiny, 1, TowardPositiveInfinity, "2", Inexact | Rounded | Increased},
		{tiny, 16, AwayFromZero, "1.000000000000001", Inexact | Rounded | Increased},
		{tiny, 16, TiesToEven, "1.000000000000000", Inexact | Rounded | Decreased},
		{tiny.Neg(), 1, TowardZero, "0.9", Inexact | Rounded | Decreased},
		{tiny.Neg(), 1, TiesToEven, "1", Inexact | Rounded | Increased},
		{tiny.Neg(), 16, TowardNegativeInfinity, "0.9999999999999999", Inexact | Rounded | Decreased},
		{tiny.Neg(), 16, TowardPositiveInfinity, "1.000000000000000", Inexact | Rounded | Increased},
	}
	for _, tc := range cases {
		got, c, err := tc.x.ExpWithContext(mustContext(t, tc.p, tc.mode))
		if err != nil || got.String() != tc.want || c != tc.c {
			t.Fatalf("Exp(%s) p=%d %v = %s %v %v, want %s %v", tc.x, tc.p, tc.mode, got, c, err, tc.want, tc.c)
		}
	}
	for _, x := range []Decimal{New(1, 11), New(-1, 11), New(5, 9), New(-5, 9), New(1, 2147483647)} {
		_, _, err := x.ExpWithContext(mustContext(t, 16, TiesToEven))
		if !errors.Is(err, ErrExponentRange) {
			t.Fatalf("Exp(%s) unguarded: %v", x, err)
		}
	}
	d64 := Decimal64Context()
	got, c, err := New(1, 2147483647).ExpWithContext(d64)
	if err != nil || got.String() != "9.999999999999999E+384" || c != Overflow|Inexact|Rounded|Decreased {
		t.Fatalf("guarded huge: %s %v %v", got, c, err)
	}
	got, c, err = New(-1, 2147483647).ExpWithContext(d64)
	if err != nil || !got.isZero() || got.Exponent() != -398 || c != Subnormal|Underflow|Inexact|Rounded|Decreased {
		t.Fatalf("guarded tiny: %s %v %v", got, c, err)
	}
	up, _ := d64.withRounding(TowardPositiveInfinity)
	got, c, err = New(-1000, 0).ExpWithContext(up)
	if err != nil || got.String() != "1E-398" || c != Subnormal|Underflow|Inexact|Rounded|Increased {
		t.Fatalf("guarded tiny up: %s %v %v", got, c, err)
	}
}

// withRounding derives a guarded context with another mode for tests.
func (c Context) withRounding(mode RoundingMode) (Context, error) {
	g, ok := c.ExponentGuards()
	if !ok {
		return NewContext(c.precision, mode, nil, c.traps)
	}
	return NewContext(c.precision, mode, &g, c.traps)
}

// TestAdaptiveExactZeroContext checks the exact zero context and
// special cohorts: bare and Context{} forms return Exp(0) = 1E0,
// Ln(1) = 0E0, Log10(1E+10) = 10E0 and 4^.5 = 2E0 exactly, and refuse the
// nondecimal Exp(1), Ln(2), Log10(2) and (9/4)^(−.5) with zero, Inexact and
// the context remedy; no default precision is introduced.
func TestAdaptiveExactZeroContext(t *testing.T) {
	half, _ := Parse("0.5")
	nine4, _ := Parse("2.25")
	type call func(ctx Context) (Decimal, Conditions, error)
	bare := func(f func() (Decimal, error)) call {
		return func(Context) (Decimal, Conditions, error) { d, err := f(); return d, 0, err }
	}
	for _, tc := range []struct {
		name    string
		bare    call
		context call
		want    string
		remedy  string
	}{
		{"Exp(0)", bare(Zero().Exp), Zero().ExpWithContext, "1", ""},
		{"Ln(1)", bare(One().Ln), One().LnWithContext, "0", ""},
		{"Log10(1E+10)", bare(New(1, 10).Log10), New(1, 10).Log10WithContext, "10", ""},
		{"4^.5", bare(func() (Decimal, error) { return New(4, 0).PowDecimal(half) }), func(c Context) (Decimal, Conditions, error) { return New(4, 0).PowDecimalWithContext(half, c) }, "2", ""},
		{"Exp(1)", bare(One().Exp), One().ExpWithContext, "", expRemedy},
		{"Ln(2)", bare(New(2, 0).Ln), New(2, 0).LnWithContext, "", lnRemedy},
		{"Log10(2)", bare(New(2, 0).Log10), New(2, 0).Log10WithContext, "", log10Remedy},
		{"(9/4)^-.5", bare(func() (Decimal, error) { return nine4.PowDecimal(half.Neg()) }), func(c Context) (Decimal, Conditions, error) { return nine4.PowDecimalWithContext(half.Neg(), c) }, "", powDecimalRemedy},
	} {
		for _, run := range []call{tc.bare, tc.context} {
			got, c, err := run(Context{})
			if tc.want != "" {
				if err != nil || got.String() != tc.want || got.Exponent() != 0 || c != 0 {
					t.Fatalf("%s = %s E%d %v %v", tc.name, got, got.Exponent(), c, err)
				}
				continue
			}
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Remedy != tc.remedy || !got.isZero() || c != 0 {
				t.Fatalf("%s = %s %v %v", tc.name, got, c, err)
			}
		}
	}
}
