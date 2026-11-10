// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"errors"
	"fmt"
	"math/big"
	"math/rand"
	"strconv"
	"strings"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

var quantizeVariants = []string{
	"oneword-cut1", "oneword-cut2", "oneword-cut3", "oneword-cut4", "oneword-cut19",
	"twoword-cut2", "slow-cut2", "oneword-cut20", "oneword-grow2", "oneword-same", "zero", "exact-cut2",
}

var integralVariants = []string{
	"ties-even", "ties-away", "ties-toward", "toward-zero", "away-from-zero", "positive-infinity", "negative-infinity", "exact",
}

type quantizeFixture struct {
	name     string
	width    string
	exponent int32
	target   int32
	mode     decimal.RoundingMode
	exact    bool
	integral bool
}

// quantizeFixtureTexts generates the same committed-seed corpus for both arms.
// Directed coefficients cover exact discards, odd/even ties, sticky remainders,
// carry, uint64 boundaries, and both signs. No result is taken from the library.
func quantizeFixtureTexts(spec quantizeFixture) []string {
	r := rand.New(rand.NewSource(portfolioSeed + 77))
	limit := new(big.Int).SetUint64(^uint64(0))
	directed := []*big.Int{
		big.NewInt(1), big.NewInt(15), big.NewInt(25), big.NewInt(999995),
		new(big.Int).Set(limit), new(big.Int).Sub(new(big.Int).Set(limit), big.NewInt(1)),
		pow10(19), new(big.Int).Sub(pow10(19), big.NewInt(1)),
	}
	cut := int(spec.target - spec.exponent)
	if cut > 0 && cut <= 19 {
		unit := pow10(cut)
		half := new(big.Int).Quo(new(big.Int).Set(unit), big.NewInt(2))
		for _, q := range []int64{0, 1, 2} {
			for _, offset := range []int64{-1, 0, 1} {
				c := new(big.Int).Mul(big.NewInt(q), unit)
				c.Add(c, half).Add(c, big.NewInt(offset))
				if c.Sign() > 0 && c.Cmp(limit) <= 0 {
					directed = append(directed, c)
				}
			}
		}
	}
	texts := make([]string, 256)
	for i := 0; i < len(texts); i += 2 {
		var coefficient *big.Int
		switch spec.width {
		case "zero":
			coefficient = new(big.Int)
		case "two":
			coefficient = new(big.Int).SetUint64(r.Uint64() | 1)
			coefficient.Lsh(coefficient, 64).Add(coefficient, new(big.Int).SetUint64(r.Uint64()))
			if i == 0 {
				coefficient.Lsh(big.NewInt(1), 64)
			} else if i == 2 {
				coefficient.Sub(new(big.Int).Lsh(big.NewInt(1), 128), big.NewInt(1))
			}
		case "slow":
			coefficient, _ = new(big.Int).SetString(randNonzeroDigits(r, 40), 10)
		default:
			if i/2 < len(directed) {
				coefficient = new(big.Int).Set(directed[i/2])
			} else {
				coefficient = new(big.Int).SetUint64(r.Uint64() | 1)
			}
		}
		if spec.exact && cut > 0 {
			unit := pow10(cut)
			coefficient.Quo(coefficient, unit).Mul(coefficient, unit)
			if coefficient.Sign() == 0 {
				coefficient.Set(unit)
			}
		}
		text := coefficient.String() + "E" + strconv.Itoa(int(spec.exponent))
		texts[i], texts[i+1] = text, "-"+text
	}
	return texts
}

// quantizePortfolioOracle applies the rounding catalogue to a big.Int quotient
// and remainder. Its direction attribute compares independently constructed
// rational values; it never reads a rounded result to decide the expectation.
func quantizePortfolioOracle(text string, target int32, mode decimal.RoundingMode) (negative bool, coefficient *big.Int, events decimal.Conditions, err error) {
	negative, coefficient, exponent, err := decimalParts(text)
	if err != nil {
		return false, nil, 0, err
	}
	if coefficient.Sign() == 0 {
		return false, coefficient, 0, nil
	}
	if difference := exponent - int64(target); difference >= 0 {
		coefficient.Mul(coefficient, pow10(int(difference)))
		return negative, coefficient, 0, nil
	}
	unit := pow10(int(int64(target) - exponent))
	q, remainder := new(big.Int).QuoRem(coefficient, unit, new(big.Int))
	events = decimal.Rounded
	if remainder.Sign() != 0 {
		if mode == decimal.Exact {
			return false, nil, 0, decimal.ErrInexact
		}
		events |= decimal.Inexact
	}
	half := new(big.Int).Lsh(new(big.Int).Set(remainder), 1).Cmp(unit)
	up := false
	switch mode {
	case decimal.TiesToEven:
		up = half > 0 || half == 0 && q.Bit(0) == 1
	case decimal.TiesAwayFromZero:
		up = half >= 0
	case decimal.TiesTowardZero:
		up = half > 0
	case decimal.TowardZero, decimal.Exact:
	case decimal.AwayFromZero:
		up = remainder.Sign() != 0
	case decimal.TowardPositiveInfinity:
		up = remainder.Sign() != 0 && !negative
	case decimal.TowardNegativeInfinity:
		up = remainder.Sign() != 0 && negative
	default:
		return false, nil, 0, fmt.Errorf("unknown fixture mode %d", mode)
	}
	if up {
		q.Add(q, big.NewInt(1))
	}
	if events&decimal.Inexact != 0 {
		source, ok := new(big.Rat).SetString(text)
		if !ok {
			return false, nil, 0, fmt.Errorf("invalid rational fixture %q", text)
		}
		rounded := new(big.Rat).SetInt(q)
		if target >= 0 {
			rounded.Mul(rounded, new(big.Rat).SetInt(pow10(int(target))))
		} else {
			rounded.Quo(rounded, new(big.Rat).SetInt(pow10(int(-target))))
		}
		if negative {
			rounded.Neg(rounded)
		}
		if rounded.Cmp(source) > 0 {
			events |= decimal.Increased
		} else {
			events |= decimal.Decreased
		}
	}
	return negative && q.Sign() != 0, q, events, nil
}

func quantizePortfolioRows(integral bool) []oracleRow {
	var specs []quantizeFixture
	if integral {
		modes := []decimal.RoundingMode{
			decimal.TiesToEven, decimal.TiesAwayFromZero, decimal.TiesTowardZero, decimal.TowardZero,
			decimal.AwayFromZero, decimal.TowardPositiveInfinity, decimal.TowardNegativeInfinity, decimal.Exact,
		}
		for i, mode := range modes {
			specs = append(specs, quantizeFixture{name: integralVariants[i], width: "one", exponent: -2, mode: mode, exact: mode == decimal.Exact, integral: true})
		}
	} else {
		for _, cut := range []int32{1, 2, 3, 4, 19} {
			specs = append(specs, quantizeFixture{name: "oneword-cut" + strconv.Itoa(int(cut)), width: "one", exponent: -cut, mode: decimal.TiesToEven})
		}
		specs = append(specs,
			quantizeFixture{name: "twoword-cut2", width: "two", exponent: -2},
			quantizeFixture{name: "slow-cut2", width: "slow", exponent: -2},
			quantizeFixture{name: "oneword-cut20", width: "one", exponent: -20},
			quantizeFixture{name: "oneword-grow2", width: "one", exponent: 0, target: -2},
			quantizeFixture{name: "oneword-same", width: "one", exponent: -2, target: -2},
			quantizeFixture{name: "zero", width: "zero", exponent: -5, target: -2},
			quantizeFixture{name: "exact-cut2", width: "one", exponent: -4, target: -2, mode: decimal.Exact, exact: true},
		)
	}
	rows := make([]oracleRow, 0, len(specs))
	for _, spec := range specs {
		texts := quantizeFixtureTexts(spec)
		values := make([]decimal.Decimal, len(texts))
		var inputErr error
		for i, text := range texts {
			var err error
			values[i], err = decimal.Parse(text)
			if err != nil {
				inputErr = fmt.Errorf("fixture %d: %w", i, err)
				break
			}
		}
		call := func(i int) (decimal.Decimal, decimal.Conditions, error) {
			if spec.integral {
				return values[i].RoundToIntegral(spec.mode)
			}
			return values[i].Quantize(spec.target, spec.mode)
		}
		rows = append(rows, oracleRow{variant: spec.name, size: len(values), check: func() error {
			if inputErr != nil {
				return inputErr
			}
			return eachEntry(len(values), func(i int) error {
				negative, coefficient, events, wantErr := quantizePortfolioOracle(texts[i], spec.target, spec.mode)
				if wantErr != nil {
					return fmt.Errorf("unexpected fixture refusal: %w", wantErr)
				}
				got, conditions, err := call(i)
				if err != nil || conditions != events {
					return fmt.Errorf("conditions %v error %v; want %v and nil", conditions, err, events)
				}
				if coefficient.Sign() == 0 && strings.HasPrefix(got.String(), "-") {
					return fmt.Errorf("signed zero %s; want unsigned zero at exponent %d", got, spec.target)
				}
				return sameCohort(got, negative, coefficient, int64(spec.target))
			})
		}, run: func(i int) (err error) { sinkDecimal, _, err = call(i); return }})
	}
	return rows
}

// TestQuantizePortfolioOracle checks that each of the twenty
// supplemental public rows checks 256 committed-seed cases before timing.
func TestQuantizePortfolioOracle(t *testing.T) {
	// Hand-derived catalogue answers independently pin the test-side oracle.
	inputs := []string{"2.30", "2.34", "2.35", "2.45", "2.36", "-2.34", "-2.35", "-2.45", "-2.36"}
	answers := [][]string{
		{"23", "23", "24", "24", "24", "-23", "-24", "-24", "-24"},
		{"23", "23", "24", "25", "24", "-23", "-24", "-25", "-24"},
		{"23", "23", "23", "24", "24", "-23", "-23", "-24", "-24"},
		{"23", "23", "23", "24", "23", "-23", "-23", "-24", "-23"},
		{"23", "24", "24", "25", "24", "-24", "-24", "-25", "-24"},
		{"23", "24", "24", "25", "24", "-23", "-23", "-24", "-23"},
		{"23", "23", "23", "24", "23", "-24", "-24", "-25", "-24"},
		{"23", "refuse", "refuse", "refuse", "refuse", "refuse", "refuse", "refuse", "refuse"},
	}
	for mode, row := range answers {
		for i, want := range row {
			negative, coefficient, events, err := quantizePortfolioOracle(inputs[i], -1, decimal.RoundingMode(mode))
			if want == "refuse" {
				if !errors.Is(err, decimal.ErrInexact) || coefficient != nil || events != 0 {
					t.Fatalf("oracle Exact(%s): %v %v %v; want Inexact refusal", inputs[i], coefficient, events, err)
				}
				continue
			}
			if err != nil {
				t.Fatal(err)
			}
			if negative {
				coefficient.Neg(coefficient)
			}
			if coefficient.String() != want || events&decimal.Rounded == 0 || (events&decimal.Inexact != 0) != (i != 0) {
				t.Fatalf("oracle mode %d(%s): %s %v; want %s and expected discard flags", mode, inputs[i], coefficient, events, want)
			}
		}
	}
	testOracleRows(t, quantizePortfolioRows(false), quantizeVariants)
	testOracleRows(t, quantizePortfolioRows(true), integralVariants)
}

// TestQuantizePortfolioExactRefusal checks the Exact entry points against
// hand-derived inexact vectors and typed errors.
func TestQuantizePortfolioExactRefusal(t *testing.T) {
	refusals := 0
	for _, text := range []string{"0.01", "-0.01", "1.245", "-1.245", "2.5", "-2.5"} {
		input := decimal.MustParse(text)
		for _, integral := range []bool{false, true} {
			op := "Quantize"
			target := int32(-2)
			if integral {
				op, target = "RoundToIntegral", 0
			}
			_, _, _, wantErr := quantizePortfolioOracle(text, target, decimal.Exact)
			if wantErr == nil {
				continue
			}
			var got decimal.Decimal
			var events decimal.Conditions
			var err error
			if integral {
				got, events, err = input.RoundToIntegral(decimal.Exact)
			} else {
				got, events, err = input.Quantize(target, decimal.Exact)
			}
			var condition *decimal.Error
			if got.String() != "0" || got.Exponent() != 0 || events != 0 || !errors.Is(err, wantErr) || !errors.As(err, &condition) || condition.Op != op || condition.Condition != decimal.Inexact {
				t.Fatalf("%s(%s): got %v, %v, %v; want unsigned zero, no events, %s Inexact refusal", op, text, got, events, err, op)
			}
			refusals++
		}
	}
	if refusals != 8 {
		t.Fatalf("checked %d Exact refusals, want 8", refusals)
	}
}

// BenchmarkQuantize times the direct public Quantize rows; the oracle runs before the timer for every corpus result.
func BenchmarkQuantize(b *testing.B) { benchOracleRows(b, quantizePortfolioRows(false)) }

// BenchmarkRoundToIntegral times all eight public rounding modes, with exact-only inputs for the Exact success row.
func BenchmarkRoundToIntegral(b *testing.B) { benchOracleRows(b, quantizePortfolioRows(true)) }
