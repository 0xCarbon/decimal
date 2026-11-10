// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"math/big"
	"strconv"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

var contextAddSink decimal.Decimal

// contextAddOracle rounds the exact sum x+y to p digits with TiesToEven
// using only math/big integers, and returns the coefficient digits, the
// exponent and the conditions (Inexact, Rounded and the direction)
// that AddWithContext must report.
func contextAddOracle(x, y *big.Int, ex, ey int64, p int) (string, int64, decimal.Conditions) {
	e := min(ex, ey)
	ten := big.NewInt(10)
	exact := new(big.Int).Add(
		new(big.Int).Mul(x, new(big.Int).Exp(ten, big.NewInt(ex-e), nil)),
		new(big.Int).Mul(y, new(big.Int).Exp(ten, big.NewInt(ey-e), nil)))
	negative := exact.Sign() < 0
	exact.Abs(exact)
	text := exact.String()
	if len(text) <= p {
		return text, e, 0
	}
	cut := len(text) - p
	quotient, remainder := new(big.Int).QuoRem(exact, new(big.Int).Exp(ten, big.NewInt(int64(cut)), nil), new(big.Int))
	half := new(big.Int).Mul(remainder, big.NewInt(2)).Cmp(new(big.Int).Exp(ten, big.NewInt(int64(cut)), nil))
	conditions := decimal.Rounded
	up := half > 0 || half == 0 && quotient.Bit(0) == 1
	if remainder.Sign() != 0 {
		conditions |= decimal.Inexact
		if up != negative {
			conditions |= decimal.Increased
		} else {
			conditions |= decimal.Decreased
		}
	}
	if up {
		quotient.Add(quotient, big.NewInt(1))
	}
	e += int64(cut)
	if digits := quotient.String(); len(digits) > p {
		quotient.Quo(quotient, ten)
		e++
	}
	return quotient.String(), e, conditions
}

// BenchmarkContextAddGap measures context Add at p=34 as the exponent gap
// between the operands grows, through AddWithContext with a context budget
// under a generous work cap and through AddWithContext: a remote nonzero
// operand (1E+g + −7.25, a borrow into the sticky digit), a zero far below
// the rounding position (1.5 + 0E−g) and a zero far above it
// (1E+g + 0). Every result is first checked against a math/big oracle.
func BenchmarkContextAddGap(b *testing.B) {
	ctx, err := decimal.NewContext(34, decimal.TiesToEven, nil, 0)
	if err != nil {
		b.Fatal(err)
	}
	budget := decimal.Budget{MaxWork: 1 << 40}
	type fixture struct {
		name   string
		x, y   decimal.Decimal
		xc, yc int64
		xe, ye int64
	}
	for _, gap := range []int64{40, 400, 4000, 40000} {
		g := strconv.FormatInt(gap, 10)
		for _, f := range []fixture{
			{name: "remote", x: decimal.MustParse("1E+" + g), y: decimal.MustParse("-7.25"), xc: 1, yc: -725, xe: gap, ye: -2},
			{name: "zero-below", x: decimal.MustParse("1.5"), y: decimal.MustParse("0E-" + g), xc: 15, yc: 0, xe: -1, ye: -gap},
			{name: "zero-above", x: decimal.MustParse("1E+" + g), y: decimal.MustParse("0"), xc: 1, yc: 0, xe: gap, ye: 0},
		} {
			digits, exponent, conditions := contextAddOracle(big.NewInt(f.xc), big.NewInt(f.yc), f.xe, f.ye, 34)
			check := func(got decimal.Decimal, gotConditions decimal.Conditions, err error, form string) {
				want := decimal.MustParse(digits + "E" + strconv.FormatInt(exponent, 10))
				if err != nil || !got.Equal(want) || got.Exponent() != want.Exponent() || gotConditions != conditions {
					b.Fatalf("%s %s g=%d: %v e%d %v %v; math/big %v e%d %v", form, f.name, gap, got, got.Exponent(), gotConditions, err, want, exponent, conditions)
				}
			}
			got, gotConditions, err := f.x.AddWithContext(f.y, ctx.WithBudget(budget))
			check(got, gotConditions, err, "budget")
			got, gotConditions, err = f.x.AddWithContext(f.y, ctx)
			check(got, gotConditions, err, "nobudget")
			b.Run("budget/"+f.name+"/g"+g, func(b *testing.B) {
				for b.Loop() {
					contextAddSink, _, _ = f.x.AddWithContext(f.y, ctx.WithBudget(budget))
				}
			})
			b.Run("nobudget/"+f.name+"/g"+g, func(b *testing.B) {
				for b.Loop() {
					contextAddSink, _, _ = f.x.AddWithContext(f.y, ctx)
				}
			})
		}
	}
}

// BenchmarkContextAddNear measures context Add at Decimal128 where no
// far-operand reduction can fire: near 37- and
// 33-digit operands whose sum rounds, and an exact fit (12.5 + 0.0000001),
// through AddWithContext with a context budget under a generous work cap
// and through
// AddWithContext. Every result is first checked against a math/big oracle.
func BenchmarkContextAddNear(b *testing.B) {
	ctx := decimal.Decimal128Context()
	budget := decimal.Budget{MaxWork: 1 << 40}
	coefficient := func(s string) *big.Int {
		v, ok := new(big.Int).SetString(s, 10)
		if !ok {
			b.Fatal(s)
		}
		return v
	}
	for _, f := range []struct {
		name   string
		x, y   string
		xc, yc *big.Int
		xe, ye int64
	}{
		{"round", "1234567890.123456789012345678901234567", "9876543210.98765432109876543210987",
			coefficient("1234567890123456789012345678901234567"), coefficient("987654321098765432109876543210987"), -27, -23},
		{"exactfit", "12.5", "0.0000001", big.NewInt(125), big.NewInt(1), -1, -7},
	} {
		x, y := decimal.MustParse(f.x), decimal.MustParse(f.y)
		digits, exponent, conditions := contextAddOracle(f.xc, f.yc, f.xe, f.ye, 34)
		want := decimal.MustParse(digits + "E" + strconv.FormatInt(exponent, 10))
		for form, run := range map[string]func() (decimal.Decimal, decimal.Conditions, error){
			"budget": func() (decimal.Decimal, decimal.Conditions, error) {
				return x.AddWithContext(y, ctx.WithBudget(budget))
			},
			"nobudget": func() (decimal.Decimal, decimal.Conditions, error) { return x.AddWithContext(y, ctx) },
		} {
			got, gotConditions, err := run()
			if err != nil || !got.Equal(want) || got.Exponent() != want.Exponent() || gotConditions != conditions {
				b.Fatalf("%s %s: %v e%d %v %v; math/big %v e%d %v", form, f.name, got, got.Exponent(), gotConditions, err, want, exponent, conditions)
			}
		}
		b.Run("budget/"+f.name, func(b *testing.B) {
			for b.Loop() {
				contextAddSink, _, _ = x.AddWithContext(y, ctx.WithBudget(budget))
			}
		})
		b.Run("nobudget/"+f.name, func(b *testing.B) {
			for b.Loop() {
				contextAddSink, _, _ = x.AddWithContext(y, ctx)
			}
		})
	}
}
