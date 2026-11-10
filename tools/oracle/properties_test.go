// SPDX-License-Identifier: Apache-2.0

package main

import (
	"encoding/binary"
	"maps"
	"math"
	"math/big"
	"math/rand/v2"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/0xCarbon/decimal"
)

// propertyCases is the number of seeded cases per law in the test run.
const propertyCases = 400

// TestPropertyLaws is the property-law suite:
// commutativity, exact sums and products at the GDA exponents,
// associativity (exact, and exactness-conditioned under a context),
// monotone and idempotent rounding, directed-mode enclosure, negation
// symmetry, Compare/Equal/Hasher/Reduce agreement and text and JSON round
// trips, on the recorded seed.
func TestPropertyLaws(t *testing.T) {
	violations := runLaws(propertySeed, propertyCases, libraryOps)
	for _, l := range laws {
		for _, v := range violations[l.name] {
			t.Errorf("%s: %s", l.name, v)
		}
	}
}

// TestPropertyLawControls is the suite's negative control:
// each deliberately defective operation must be reported by the law named
// beside it, and every law has such a defect, so weakening any law fails
// this test.
func TestPropertyLawControls(t *testing.T) {
	quantizeWith := func(o *lawOps, f func(x decimal.Decimal, k int32, m decimal.RoundingMode) (decimal.Decimal, decimal.Conditions, error)) {
		o.quantize = f
	}
	defects := []struct {
		name, law string
		inject    func(o *lawOps)
	}{
		{"add keeps the left cohort", "add-commutes", func(o *lawOps) {
			o.add = func(x, y decimal.Decimal) (decimal.Decimal, error) {
				s, err := x.Add(y)
				if err != nil {
					return s, err
				}
				if q, _, qerr := s.Quantize(max(x.Exponent(), s.Exponent()), decimal.TiesToEven); qerr == nil {
					return q, nil
				}
				return s, nil
			}
		}},
		{"mul reduces its result", "mul-commutes", func(o *lawOps) {
			o.mul = func(x, y decimal.Decimal) (decimal.Decimal, error) {
				if x.Compare(y) < 0 {
					p, err := x.Mul(y)
					return p.Reduce(), err
				}
				return x.Mul(y)
			}
		}},
		{"add is off by one unit", "exact-add-is-rational-sum-at-min-exponent", func(o *lawOps) {
			o.add = func(x, y decimal.Decimal) (decimal.Decimal, error) {
				s, err := x.Add(y)
				if err != nil {
					return s, err
				}
				return s.Add(decimal.New(1, s.Exponent()))
			}
		}},
		{"mul publishes a reduced cohort", "exact-mul-is-rational-product-at-exponent-sum", func(o *lawOps) {
			o.mul = func(x, y decimal.Decimal) (decimal.Decimal, error) {
				p, err := x.Mul(y)
				return p.Reduce(), err
			}
		}},
		{"add rounds to 18 digits", "add-associates", func(o *lawOps) {
			o.add = func(x, y decimal.Decimal) (decimal.Decimal, error) {
				c, _ := decimal.NewContext(18, decimal.TiesToEven, nil, 0)
				s, _, err := x.AddWithContext(y, c)
				return s, err
			}
		}},
		{"context add drops the addend's low digit", "context-add-associates-when-exact", func(o *lawOps) {
			o.addCtx = func(x, y decimal.Decimal, c decimal.Context) (decimal.Decimal, decimal.Conditions, error) {
				if cut, _, err := y.Quantize(y.Exponent()+1, decimal.TowardZero); err == nil {
					y = cut
				}
				return x.AddWithContext(y, c)
			}
		}},
		{"rounding bumps results ending in 9", "rounding-is-monotone", func(o *lawOps) {
			quantizeWith(o, func(x decimal.Decimal, k int32, m decimal.RoundingMode) (decimal.Decimal, decimal.Conditions, error) {
				q, c, err := x.Quantize(k, m)
				if err == nil && m != decimal.Exact && x.Exponent() < k {
					if s := x.String(); strings.HasSuffix(strings.Split(s, "E")[0], "9") {
						q, _ = q.Add(decimal.New(1, k))
					}
				}
				return q, c, err
			})
		}},
		{"precision rounding drifts", "rounding-is-idempotent", func(o *lawOps) {
			o.toPrec = func(x decimal.Decimal, p uint32, m decimal.RoundingMode) (decimal.Decimal, decimal.Conditions, error) {
				if m == decimal.Exact && p > 1 {
					p--
				}
				return x.RoundToPrecision(p, m)
			}
		}},
		{"directed modes swapped", "directed-modes-enclose-the-exact-value", func(o *lawOps) {
			quantizeWith(o, func(x decimal.Decimal, k int32, m decimal.RoundingMode) (decimal.Decimal, decimal.Conditions, error) {
				switch m {
				case decimal.TowardPositiveInfinity:
					m = decimal.TowardNegativeInfinity
				case decimal.TowardNegativeInfinity:
					m = decimal.TowardPositiveInfinity
				}
				return x.Quantize(k, m)
			})
		}},
		{"ties round by the sign", "negation-mirrors-the-modes", func(o *lawOps) {
			quantizeWith(o, func(x decimal.Decimal, k int32, m decimal.RoundingMode) (decimal.Decimal, decimal.Conditions, error) {
				if m == decimal.TiesToEven && x.Sign() < 0 {
					m = decimal.TiesAwayFromZero
				}
				return x.Quantize(k, m)
			})
		}},
		{"compare ignores the exponent", "compare-equal-and-hash-agree", func(o *lawOps) {
			o.compare = func(x, y decimal.Decimal) int {
				xc, _, _ := x.CoefficientInt128()
				yc, _, _ := y.CoefficientInt128()
				return cmpInt(xc, yc)
			}
		}},
		{"text drops trailing zeros", "text-round-trips", func(o *lawOps) {
			o.text = func(x decimal.Decimal) string { return x.Reduce().String() }
		}},
	}
	covered := map[string]bool{}
	for _, d := range defects {
		covered[d.law] = true
		t.Run(d.name, func(t *testing.T) {
			o := libraryOps
			d.inject(&o)
			if v := runLaws(propertySeed, 200, o); len(v[d.law]) == 0 {
				t.Fatalf("law %s did not report the defect (reports: %v)", d.law, slices.Sorted(maps.Keys(v)))
			}
		})
	}
	for _, l := range laws {
		if !covered[l.name] {
			t.Errorf("law %s has no defect control", l.name)
		}
	}
}

func cmpInt(a, b int64) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

// TestOperationsNeverPanicOnArbitraryInput checks that no operation panics,
// over seeded arbitrary inputs: random bytes as
// text, JSON, two's complement and scan sources; extreme exponents,
// precisions, modes (including an out-of-range mode) and zero budgets, fed
// to every public operation family. Any panic fails, with the input.
func TestOperationsNeverPanicOnArbitraryInput(t *testing.T) {
	rng := rand.New(rand.NewPCG(propertySeed, 0xE8C01))
	exps := []int32{0, 1, -1, 2, -30, 30, math.MaxInt32, math.MinInt32, math.MaxInt32 - 1, math.MinInt32 + 1}
	randBytes := func() []byte {
		if rng.IntN(2) == 0 {
			// A decimal literal, sometimes with one byte replaced.
			b := []byte(strconv.FormatInt(rng.Int64N(1<<40)-(1<<39), 10) + "." + strconv.Itoa(rng.IntN(1000)) + "E" + strconv.Itoa(rng.IntN(80)-40))
			if rng.IntN(3) == 0 {
				b[rng.IntN(len(b))] = byte(rng.IntN(256))
			}
			return b
		}
		b := make([]byte, rng.IntN(40))
		alphabet := []byte("0123456789.eE+-_ xNaInf\x00\xff9")
		for i := range b {
			if rng.IntN(4) == 0 {
				b[i] = byte(rng.IntN(256))
			} else {
				b[i] = alphabet[rng.IntN(len(alphabet))]
			}
		}
		return b
	}
	value := func() decimal.Decimal {
		switch rng.IntN(4) {
		case 0:
			return decimal.New(rng.Int64(), exps[rng.IntN(len(exps))])
		case 1:
			return decimal.NewInt128(rng.Int64(), rng.Uint64(), exps[rng.IntN(len(exps))])
		case 2:
			d, err := decimal.Parse(strconv.Itoa(rng.IntN(1000)) + "E" + strconv.Itoa(-50+rng.IntN(100)))
			if err != nil {
				t.Fatal(err)
			}
			return d
		}
		return decimal.Zero()
	}
	admitted, parsed := 0, 0
	for i := range 1500 {
		x, y := value(), value()
		mode := decimal.RoundingMode(rng.IntN(10))
		p := []uint32{0, 1, 3, 34, math.MaxUint32}[rng.IntN(5)]
		g := &decimal.ExponentGuards{Emin: exps[rng.IntN(len(exps))], Emax: exps[rng.IntN(len(exps))]}
		if rng.IntN(2) == 0 {
			g = nil
		}
		c, _ := decimal.NewContext(p, mode, g, decimal.Conditions(rng.IntN(1<<13)))
		k, n := exps[rng.IntN(len(exps))], int32(rng.IntN(7)-3)
		b := randBytes()
		// Every call is budgeted or bounded by its own contract: the
		// extreme exponents make unbudgeted exact work gap-sized.
		budget := decimal.Budget{MaxDigits: 1 + uint64(rng.IntN(512)), MaxWork: 1 + uint64(rng.IntN(4096))}
		display := decimal.DisplayOptions{Mode: mode, Budget: decimal.Budget{MaxOutputBytes: 1 + uint64(rng.IntN(512)), MaxWork: 1 + uint64(rng.IntN(4096))}}
		conv := decimal.Budget{MaxInputDigits: 64, MaxDigits: 64, MaxWork: 4096}
		parseBudget := decimal.Budget{MaxInputBytes: 64, MaxDigits: 64}
		func() {
			defer func() {
				if r := recover(); r != nil {
					t.Fatalf("case %d panicked: %v (x=%v y=%v mode=%d p=%d guards=%v k=%d n=%d bytes=%q)", i, r, x, y, mode, p, g, k, n, b)
				}
			}()
			if _, _, err := x.AddWithContext(y, decimal.Context{}.WithBudget(budget)); err == nil {
				admitted++
			}
			if _, _, err := decimal.ParseWithContext(b, decimal.Context{}.WithBudget(parseBudget)); err == nil {
				parsed++
			}
			_, _, _ = x.AddWithContext(y, c.WithBudget(budget))
			_, _, _ = x.SubWithContext(y, c.WithBudget(budget))
			_, _, _ = x.MulWithContext(y, decimal.Context{}.WithBudget(budget))
			_, _, _ = x.MulWithContext(y, c.WithBudget(budget))
			_, _, _ = x.DivWithContext(y, decimal.Context{}.WithBudget(budget))
			_, _, _ = x.DivWithContext(y, c.WithBudget(budget))
			_, _, _ = x.DivToExponentWithBudget(y, k, mode, budget)
			_, _, _ = x.QuantizeWithContext(k, c.WithBudget(budget))
			_, _, _ = x.RoundToIntegralWithContext(c.WithBudget(budget))
			_, _, _ = x.RoundToPrecisionWithContext(c.WithBudget(budget))
			_, _, _ = x.RoundToMultipleWithBudget(y, mode, budget)
			_, _, _ = x.SqrtWithContext(c.WithBudget(budget))
			_, _, _ = x.PowWithContext(n, decimal.Context{}.WithBudget(budget))
			_, _, _ = x.PowWithContext(n, c.WithBudget(budget))
			_, _, _ = x.Float64Rounded(mode)
			_, _ = x.CompareFloat64(math.Float64frombits(rng.Uint64()))
			_, _ = x.Text(uint64(rng.IntN(64)))
			_, _ = x.FixedWithOptions(uint64(rng.IntN(64)), display)
			_, _ = x.ScientificWithOptions(uint64(rng.IntN(64)), display)
			_, _ = x.EngineeringWithBudget(display.Budget)
			_, _ = x.BigIntWithBudget(nil, conv)
			_, _ = x.RatWithBudget(nil, conv)
			_, _ = x.Int64()
			_, _ = x.AppendTwosComplement(nil, rng.IntN(20), binary.BigEndian)
			_, _ = decimal.SumWithBudget([]decimal.Decimal{x, y}, budget)
			_, _, _ = decimal.ParseWithContext(b, decimal.Context{}.WithBudget(parseBudget))
			_, _, _ = decimal.ParseToExponentWithBudget(b, k, mode, parseBudget)
			_, _, _ = decimal.ParseWithContext(b, c.WithBudget(parseBudget))
			_, _ = decimal.ParseJSONWithBudget(b, parseBudget)
			_, _ = decimal.NewTwosComplementWithBudget(b, binary.LittleEndian, k, conv)
			_, _, _ = decimal.FromFloat64ToExponentWithBudget(math.Float64frombits(rng.Uint64()), k, mode, budget)
			_, _, _ = decimal.FromFloat64WithContext(math.Float64frombits(rng.Uint64()), c)
			_, _, _ = decimal.FromRatToExponentWithBudget(big.NewRat(rng.Int64(), 1+rng.Int64N(1<<40)), k, mode, budget)
			var d decimal.Decimal
			_ = d.ScanWithBudget(b, decimal.Budget{MaxInputBytes: 64, MaxDigits: 64, MaxWork: 4096})
			_ = d.ScanWithBudget(string(b), decimal.Budget{MaxInputBytes: 64, MaxDigits: 64, MaxWork: 4096})
			_ = d.ComposeWithBudget(byte(rng.IntN(4)), rng.IntN(2) == 0, b, k, conv)
		}()
	}
	// Non-vacuity: the inputs reach the operations, not only their
	// refusals.
	if admitted < 100 || parsed < 300 {
		t.Fatalf("only %d admitted additions and %d parsed texts in 1500 cases", admitted, parsed)
	}
}

// TestPropertyLawsOnAnotherSeed runs the laws on a second recorded seed,
// the smallest search the command's -laws mode runs.
func TestPropertyLawsOnAnotherSeed(t *testing.T) {
	v := runLaws(propertySeed+1, 50, libraryOps)
	for _, name := range slices.Sorted(maps.Keys(v)) {
		t.Errorf("%s: %v", name, v[name][0])
	}
}

// propertySeed is the fixed seed of the property-law test run.
const propertySeed = 0xDEC055C
