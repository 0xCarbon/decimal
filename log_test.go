// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math/big"
	"math/rand/v2"
	"testing"
)

// TestLnLog10MatchOracleInEveryMode checks that every mode certifies
// nontrivial values for Ln and Log10 against the independent oracle,
// including operands next to one on either side.
func TestLnLog10MatchOracleInEveryMode(t *testing.T) {
	rng := rand.New(rand.NewPCG(66, 3))
	near := []string{"1.0000001", "0.99999999997", "1.000000000000000000000000000000000000000001", "0.9999999999999999999999999999999", "9.99999999", "10.0000000001", "3.1622776601", "3.1622776602"}
	for i := range 360 {
		var x Decimal
		if i < 2*len(near) {
			x, _ = Parse(near[i/2])
		} else {
			x = randomElementaryInput(rng, false)
		}
		p := uint32(1 + rng.IntN(40))
		if i%30 == 0 {
			p = uint32(60 + rng.IntN(60))
		}
		mode := inexactModes[i%len(inexactModes)]
		ctx := mustContext(t, p, mode)
		if oracleRat(x).Cmp(big.NewRat(1, 1)) != 0 {
			want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) { return oracleLn(x, prec) }, int64(p), mode)
			got, c, err := x.LnWithContext(ctx)
			oracleMatch(t, fmt.Sprintf("Ln(%s) p=%d %v", x, p, mode), got, c, err, want)
		}
		if new(big.Int).Rem(oracleCoefficient(x.Reduce()), big.NewInt(10)).Sign() != 0 && oracleCoefficient(x.Reduce()).Cmp(big.NewInt(1)) != 0 {
			want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) { return oracleLog10(x, prec) }, int64(p), mode)
			got, c, err := x.Log10WithContext(ctx)
			oracleMatch(t, fmt.Sprintf("Log10(%s) p=%d %v", x, p, mode), got, c, err, want)
		}
	}
}

// TestLogExactDomainsAndRefusals checks the exact zero context,
// special cohorts and domains for Ln and Log10.
func TestLogExactDomainsAndRefusals(t *testing.T) {
	for _, s := range []string{"1", "1.000", "100E-2"} {
		x, _ := Parse(s)
		got, err := x.Ln()
		if err != nil || !got.isZero() || got.Exponent() != 0 {
			t.Fatalf("Ln(%s) = %s %v", s, got, err)
		}
		got, err = x.Log10()
		if err != nil || !got.isZero() || got.Exponent() != 0 {
			t.Fatalf("Log10(%s) = %s %v", s, got, err)
		}
	}
	for _, tc := range []struct{ x, want string }{{"1E+10", "10"}, {"1000", "3"}, {"0.001", "-3"}, {"1E-2147483648", "-2147483648"}, {"1E+2147483647", "2147483647"}, {"10.00", "1"}} {
		x, _ := Parse(tc.x)
		got, err := x.Log10()
		if err != nil || got.String() != tc.want || got.Exponent() != 0 {
			t.Fatalf("Log10(%s) = %s %v", tc.x, got, err)
		}
	}
	// A power of ten beyond the precision loses only zeros, or rounds.
	x, _ := Parse("1E+123456")
	got, c, err := x.Log10WithContext(mustContext(t, 3, Exact))
	if !errors.Is(err, ErrInexact) {
		t.Fatalf("Log10 exact refusal: %s %v %v", got, c, err)
	}
	got, c, err = New(1, 100000).Log10WithContext(mustContext(t, 3, Exact))
	if err != nil || got.String() != "1.00E+5" || c != Rounded {
		t.Fatalf("Log10 zero-only rounding: %s %v %v", got, c, err)
	}
	got, c, err = x.Log10WithContext(mustContext(t, 3, TowardZero))
	if err != nil || got.String() != "1.23E+5" || c != Inexact|Rounded|Decreased {
		t.Fatalf("Log10 rounded integer: %s %v %v", got, c, err)
	}
	for _, name := range []string{"Ln", "Log10"} {
		for _, tc := range []struct {
			x    Decimal
			code error
		}{{New(0, 0), ErrDivisionByZero}, {New(0, -5), ErrDivisionByZero}, {New(-1, 0), ErrInvalidOperation}, {New(-5, -1), ErrInvalidOperation}} {
			var err error
			if name == "Ln" {
				_, _, err = tc.x.LnWithContext(mustContext(t, 5, TiesToEven).WithBudget(Budget{MaxWork: 1}))
			} else {
				_, _, err = tc.x.Log10WithContext(mustContext(t, 5, TiesToEven).WithBudget(Budget{MaxWork: 1}))
			}
			if !errors.Is(err, tc.code) {
				t.Fatalf("%s(%s): %v, want %v", name, tc.x, err, tc.code)
			}
		}
	}
	var ce *Error
	for _, x := range []Decimal{New(2, 0), New(5, -1), New(11, 0)} {
		_, err := x.Ln()
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Remedy != lnRemedy {
			t.Fatalf("Ln(%s): %v", x, err)
		}
		_, err = x.Log10()
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Remedy != log10Remedy {
			t.Fatalf("Log10(%s): %v", x, err)
		}
	}
}

// TestLnCompactExtremes checks compact extreme-scale evaluation for
// logarithms: Ln(1E+2147483647) multiplies a compact exponent by ln 10
// without materializing it.
func TestLnCompactExtremes(t *testing.T) {
	got, c, err := New(1, 2147483647).LnWithContext(mustContext(t, 20, TowardZero))
	// 2147483647·ln 10 = 4944763833.03068737479956…
	if err != nil || got.String() != "4944763833.0306873747" || c != Inexact|Rounded|Decreased {
		t.Fatalf("Ln(1E+2147483647) = %s %v %v", got, c, err)
	}
	got, c, err = New(1, -2147483648).LnWithContext(mustContext(t, 12, TiesToEven))
	if err != nil || got.String() != "-4944763835.33" || c != Inexact|Rounded|Increased {
		t.Fatalf("Ln(1E-2147483648) = %s %v %v", got, c, err)
	}
}
