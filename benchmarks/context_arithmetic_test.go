// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"fmt"
	"math/big"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

var contextArithmeticVariants = []string{"add-d64", "mul-d64", "add-d128", "mul-d128"}

// contextArithmeticRows builds the fixed-precision rows: addition and
// multiplication of full-precision operands under the decimal64 and
// decimal128 contexts, whose exact results exceed the precision and round.
// Each result is checked against the math/big oracle of the context sum
// (a product is the sum of the exact product and zero).
func contextArithmeticRows(tb testing.TB) []oracleRow {
	rng := newPortfolioRNG()
	type corpus struct {
		x, y   []decimal.Decimal
		xc, yc []*big.Int
		xe, ye []int64
	}
	build := func(digits int) corpus {
		var c corpus
		for range 256 {
			for _, side := range []*[]decimal.Decimal{&c.x, &c.y} {
				exponent := int64(-rng.Intn(digits))
				text := randNonzeroDigits(rng, digits)
				d, err := decimal.Parse(text + "E" + fmt.Sprint(exponent))
				if err != nil {
					tb.Fatal(err)
				}
				coefficient, _ := new(big.Int).SetString(text, 10)
				*side = append(*side, d)
				if side == &c.x {
					c.xc, c.xe = append(c.xc, coefficient), append(c.xe, exponent)
				} else {
					c.yc, c.ye = append(c.yc, coefficient), append(c.ye, exponent)
				}
			}
		}
		return c
	}
	check := func(c corpus, precision int, multiply bool, op func(i int) (decimal.Decimal, decimal.Conditions, error)) func() error {
		return func() error {
			rounded := 0
			err := eachEntry(len(c.x), func(i int) error {
				got, conditions, err := op(i)
				if err != nil {
					return err
				}
				x, y, xe, ye := c.xc[i], c.yc[i], c.xe[i], c.ye[i]
				if multiply {
					x, y, xe = new(big.Int).Mul(x, y), new(big.Int), xe+ye
					ye = xe
				}
				digits, exponent, want := contextAddOracle(x, y, xe, ye, precision)
				coefficient, _ := new(big.Int).SetString(digits, 10)
				if err := sameCohort(got, false, coefficient, exponent); err != nil {
					return err
				}
				if conditions != want {
					return fmt.Errorf("conditions %v, oracle %v", conditions, want)
				}
				if conditions&decimal.Inexact != 0 {
					rounded++
				}
				return nil
			})
			if err == nil && rounded < 128 {
				err = fmt.Errorf("vacuous: only %d of %d results round", rounded, len(c.x))
			}
			return err
		}
	}
	d64, d128 := decimal.Decimal64Context(), decimal.Decimal128Context()
	c16, c34 := build(16), build(34)
	row := func(variant string, c corpus, precision int, multiply bool, op func(i int) (decimal.Decimal, decimal.Conditions, error)) oracleRow {
		return oracleRow{
			variant: variant, size: len(c.x), check: check(c, precision, multiply, op),
			run: func(i int) (err error) { sinkDecimal, _, err = op(i); return },
		}
	}
	return []oracleRow{
		row("add-d64", c16, 16, false, func(i int) (decimal.Decimal, decimal.Conditions, error) {
			return c16.x[i].AddWithContext(c16.y[i], d64)
		}),
		row("mul-d64", c16, 16, true, func(i int) (decimal.Decimal, decimal.Conditions, error) {
			return c16.x[i].MulWithContext(c16.y[i], d64)
		}),
		row("add-d128", c34, 34, false, func(i int) (decimal.Decimal, decimal.Conditions, error) {
			return c34.x[i].AddWithContext(c34.y[i], d128)
		}),
		row("mul-d128", c34, 34, true, func(i int) (decimal.Decimal, decimal.Conditions, error) {
			return c34.x[i].MulWithContext(c34.y[i], d128)
		}),
	}
}

// TestContextArithmeticOracle checks every fixed-precision row against its
// math/big oracle over the committed-seed corpus, as the benchmark does
// before timing.
func TestContextArithmeticOracle(t *testing.T) {
	testOracleRows(t, contextArithmeticRows(t), contextArithmeticVariants)
}

// BenchmarkContextArithmetic times addition and multiplication that round
// to the decimal64 and decimal128 precisions.
func BenchmarkContextArithmetic(b *testing.B) {
	benchOracleRows(b, contextArithmeticRows(b))
}
