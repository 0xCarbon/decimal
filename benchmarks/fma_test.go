// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"math/big"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

// BenchmarkFMAVsMulAdd measures an exact fused multiply-add against Mul then
// Add, in the same binary:
//   - f3: the F3 money corpus accumulated as acc = price·qty + acc
//     (acc += price·qty; the receiver is x in x·y + z), against
//     acc = acc.Add(price.Mul(qty));
//   - f6: one F6 19-digit product plus a 19-digit addend.
//
// muladd2 repeats muladd's code in its own closure: a within-binary null
// pair, measured exactly as FMA is.
// Every row's result must first equal the math/big value and the
// composition's cohort before timing.
func BenchmarkFMAVsMulAdd(b *testing.B) {
	prices, qtys := f3MoneyLoopInputs()
	lines := make([][2]decimal.Decimal, len(prices))
	f3Oracle := new(big.Rat)
	for i := range prices {
		lines[i] = [2]decimal.Decimal{decimal.MustParse(prices[i]), decimal.MustParse(qtys[i])}
		f3Oracle.Add(f3Oracle, new(big.Rat).Mul(f3Rat(b, prices[i]), f3Rat(b, qtys[i])))
	}
	mul19 := portfolioF6Inputs["mul19"]
	x, y, z := decimal.MustParse(mul19[0]), decimal.MustParse(mul19[1]), decimal.MustParse(portfolioF6Inputs["add19"][0])
	f6Oracle := new(big.Rat).Add(new(big.Rat).Mul(f3Rat(b, mul19[0]), f3Rat(b, mul19[1])), f3Rat(b, portfolioF6Inputs["add19"][0]))
	must := func(d decimal.Decimal, err error) decimal.Decimal {
		if err != nil {
			b.Fatal(err)
		}
		return d
	}
	type row struct {
		name   string
		run    func() decimal.Decimal
		oracle *big.Rat
	}
	rows := []row{
		{"f3/muladd", func() decimal.Decimal {
			var acc decimal.Decimal
			for _, line := range lines {
				acc = must(acc.Add(must(line[0].Mul(line[1]))))
			}
			return acc
		}, f3Oracle},
		{"f3/fma", func() decimal.Decimal {
			var acc decimal.Decimal
			for _, line := range lines {
				acc = must(fmaExact(line[0], line[1], acc))
			}
			return acc
		}, f3Oracle},
		{"f3/muladd2", func() decimal.Decimal {
			var acc decimal.Decimal
			for _, line := range lines {
				acc = must(acc.Add(must(line[0].Mul(line[1]))))
			}
			return acc
		}, f3Oracle},
		{"f6/muladd", func() decimal.Decimal { return must(must(x.Mul(y)).Add(z)) }, f6Oracle},
		{"f6/fma", func() decimal.Decimal { return must(fmaExact(x, y, z)) }, f6Oracle},
		{"f6/muladd2", func() decimal.Decimal { return must(must(x.Mul(y)).Add(z)) }, f6Oracle},
	}
	for i, r := range rows {
		got := r.run()
		text, err := got.Text(0)
		if err != nil {
			b.Fatal(err)
		}
		composition := rows[i-i%3].run()
		if f3Rat(b, text).Cmp(r.oracle) != 0 || got.Exponent() != composition.Exponent() || got.CoefficientDigits() != composition.CoefficientDigits() {
			b.Fatalf("%s: %s, math/big %s, composition %v", r.name, text, r.oracle.RatString(), composition)
		}
		b.Run(r.name, func(b *testing.B) {
			b.ReportAllocs()
			for b.Loop() {
				sinkDecimal = r.run()
			}
		})
	}
}

// fmaExact is the exact x·y + z, FMAWithContext at Context{}. There is no
// bare FMA method: it does not beat Mul then Add, which this benchmark
// measures.
func fmaExact(x, y, z decimal.Decimal) (decimal.Decimal, error) {
	result, _, err := x.FMAWithContext(y, z, decimal.Context{})
	return result, err
}
