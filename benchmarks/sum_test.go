// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"math/big"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

// BenchmarkSumVsFold measures Sum over the F2 ledger corpus against the
// fold of Add the same corpus uses in BenchmarkF2Aggregate, and SumWithBudget
// under a cap the total fits. Every row must first equal the math/big total,
// value and cohort, before timing.
func BenchmarkSumVsFold(b *testing.B) {
	values := make([]decimal.Decimal, len(portfolioF2Inputs))
	oracle := new(big.Rat)
	for i, input := range portfolioF2Inputs {
		values[i] = decimal.MustParse(input)
		operand, _ := new(big.Rat).SetString(input)
		oracle.Add(oracle, operand)
	}
	fold := func() decimal.Decimal {
		var accumulator decimal.Decimal
		for _, value := range values {
			var err error
			if accumulator, err = accumulator.Add(value); err != nil {
				b.Fatal(err)
			}
		}
		return accumulator
	}
	sum := func() decimal.Decimal {
		result, err := decimal.Sum(values...)
		if err != nil {
			b.Fatal(err)
		}
		return result
	}
	sumBudget := func() decimal.Decimal {
		result, err := decimal.SumWithBudget(values, decimal.Budget{MaxDigits: 64, MaxWork: 1 << 20})
		if err != nil {
			b.Fatal(err)
		}
		return result
	}
	for _, row := range []struct {
		name string
		run  func() decimal.Decimal
	}{{"fold", fold}, {"sum", sum}, {"sum-budget", sumBudget}} {
		got := row.run()
		text, _ := got.Text(0)
		numeric, _ := new(big.Rat).SetString(text)
		if numeric.Cmp(oracle) != 0 || got.Exponent() != fold().Exponent() {
			b.Fatalf("%s: %s, oracle %s", row.name, text, oracle.RatString())
		}
		b.Run(row.name, func(b *testing.B) {
			b.ReportAllocs()
			for b.Loop() {
				sinkDecimal = row.run()
			}
		})
	}
}
