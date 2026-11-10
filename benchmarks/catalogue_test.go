// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"errors"
	"fmt"
	"math/big"
	"math/rand"
	"regexp"
	"strconv"
	"strings"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

// oracleRow is one supplemental portfolio row: a 256-entry
// committed-seed corpus, a check that compares every corpus result with an
// independent math/big, strconv or hand-derived oracle, and the timed
// operation on entry i. The check runs in the plain suite and again before
// timing, so a wrong result voids the row before it is measured.
type oracleRow struct {
	variant string
	size    int
	check   func() error
	run     func(i int) error
}

// benchOracleRows times each row as Family/decimal/variant after its check.
func benchOracleRows(b *testing.B, rows []oracleRow) {
	for _, row := range rows {
		if err := row.check(); err != nil {
			b.Fatalf("%s: %v (timing void)", row.variant, err)
		}
		b.Run("decimal/"+row.variant, func(b *testing.B) {
			b.ReportAllocs()
			i := 0
			for b.Loop() {
				if err := row.run(i); err != nil {
					b.Fatal(err)
				}
				if i++; i == row.size {
					i = 0
				}
			}
		})
	}
}

// procSuffixName matches a benchmark name ending in -<digits>.
var procSuffixName = regexp.MustCompile(`-[0-9]+$`)

// testOracleRows runs every row's check and counts the corpus it covered, a
// guard against a vacuous pass.
func testOracleRows(t *testing.T, rows []oracleRow, want []string) {
	if len(rows) != len(want) {
		t.Fatalf("%d rows, want %d", len(rows), len(want))
	}
	for i, row := range rows {
		// go test strips a trailing -<digits> as the GOMAXPROCS suffix, so
		// such a name would be mangled in raw output at GOMAXPROCS=1.
		if procSuffixName.MatchString(row.variant) {
			t.Errorf("row %d name %q ends in -<digits>, which go test reads as a GOMAXPROCS suffix", i, row.variant)
		}
		if row.variant != want[i] {
			t.Errorf("row %d is %q, want %q (fixed name table)", i, row.variant, want[i])
		}
		if row.size != 256 {
			t.Errorf("%s: corpus has %d entries, want 256", row.variant, row.size)
		}
		if err := row.check(); err != nil {
			t.Errorf("%s: %v", row.variant, err)
		}
	}
}

// decimalParts splits decimal text (optional sign, digits with an optional
// point, optional E exponent) into sign, coefficient and exponent, without
// the library: the cohort oracle for every row.
func decimalParts(s string) (negative bool, coefficient *big.Int, exponent int64, err error) {
	if s != "" && (s[0] == '-' || s[0] == '+') {
		negative = s[0] == '-'
		s = s[1:]
	}
	if at := strings.IndexAny(s, "Ee"); at >= 0 {
		exponent, err = strconv.ParseInt(s[at+1:], 10, 64)
		if err != nil {
			return false, nil, 0, err
		}
		s = s[:at]
	}
	integer, fraction, _ := strings.Cut(s, ".")
	exponent -= int64(len(fraction))
	coefficient, ok := new(big.Int).SetString(integer+fraction, 10)
	if !ok || integer+fraction == "" {
		return false, nil, 0, fmt.Errorf("not decimal text: %q", s)
	}
	return negative, coefficient, exponent, nil
}

// cohortOf is decimalParts applied to the library's canonical String.
func cohortOf(d decimal.Decimal) (bool, *big.Int, int64, error) { return decimalParts(d.String()) }

// sameCohort compares a result's sign, coefficient and exponent with the
// oracle's.
func sameCohort(got decimal.Decimal, negative bool, coefficient *big.Int, exponent int64) error {
	gn, gc, ge, err := cohortOf(got)
	if err != nil {
		return err
	}
	if gn != negative && gc.Sign() != 0 || gc.Cmp(coefficient) != 0 || ge != exponent {
		sign := ""
		if negative {
			sign = "-"
		}
		return fmt.Errorf("got %s, oracle %s%sE%d", got, sign, coefficient, exponent)
	}
	return nil
}

var bigTen = big.NewInt(10)

func pow10(n int) *big.Int { return new(big.Int).Exp(bigTen, big.NewInt(int64(n)), nil) }

func digitCount(x *big.Int) int {
	if x.Sign() == 0 {
		return 1
	}
	return len(new(big.Int).Abs(x).String())
}

// roundDigits rounds the magnitude c to at most p digits, ties to even or
// away from zero, and returns the kept digits, the number of digits cut and
// whether a nonzero digit was discarded.
func roundDigits(c *big.Int, p int, tiesAway bool) (*big.Int, int, bool) {
	cut := digitCount(c) - p
	if cut <= 0 {
		return new(big.Int).Set(c), 0, false
	}
	unit := pow10(cut)
	q, r := new(big.Int).QuoRem(c, unit, new(big.Int))
	half := new(big.Int).Lsh(r, 1).Cmp(unit)
	if half > 0 || half == 0 && (tiesAway || q.Bit(0) == 1) {
		q.Add(q, big.NewInt(1))
	}
	if digitCount(q) > p {
		q.Quo(q, bigTen)
		cut++
	}
	return q, cut, r.Sign() != 0
}

// checkInexact requires the Inexact condition exactly when the oracle
// discarded a nonzero digit, and Rounded whenever it cut digits.
func checkInexact(c decimal.Conditions, cut int, inexact bool) error {
	if (c&decimal.Inexact != 0) != inexact || cut > 0 && c&decimal.Rounded == 0 {
		return fmt.Errorf("conditions %v, oracle cut %d inexact %t", c, cut, inexact)
	}
	return nil
}

func eachEntry(n int, check func(i int) error) error {
	for i := range n {
		if err := check(i); err != nil {
			return fmt.Errorf("entry %d: %w", i, err)
		}
	}
	return nil
}

var catalogueVariants = []string{
	"roundprecision-p7", "roundprecision-d128", "roundmultiple-nickel",
	"sqrt-exact", "sqrt-d128", "pow-cube", "pow365-d128", "contextsub-d128-budget",
}

// catalogueCorpora returns the committed-seed inputs of the catalogue
// operations: 19-digit values at exponents 0..−4 (with
// clean and sticky ties to seven digits), money prices with three or four
// fractional digits (with cash-rounding ties), four-digit rates 1.0xxxx and
// 37/33-digit operand pairs whose difference rounds at Decimal128 (with one
// clean tie).
func catalogueCorpora() (p7, prices, rates []string, pairs [][2]string) {
	r := rand.New(rand.NewSource(portfolioSeed))
	p7 = []string{"1234565500000000000", "1234566500000000000", "1234565500000000001", "9999999500000000000"}
	for len(p7) < 256 {
		p7 = append(p7, randNonzeroDigits(r, 19)+"E-"+strconv.Itoa(r.Intn(5)))
	}
	prices = []string{"2.525", "2.575", "0.025", "0.0249", "19.975", "99.975"}
	for len(prices) < 256 {
		prices = append(prices, randNonzeroDigits(r, 1+r.Intn(3))+"."+randDigits(r, 3+r.Intn(2)))
	}
	for range 256 {
		rates = append(rates, "1.0"+randDigits(r, 3)+strconv.Itoa(1+r.Intn(9)))
	}
	// The first pair's difference is a clean tie at 34 digits (…000|500).
	pairs = [][2]string{{"5000000000.000000000000000000000000500", "1000000000.00000000000000000000000"}}
	for len(pairs) < 256 {
		x := strconv.Itoa(5+r.Intn(5)) + randDigits(r, 36)
		y := strconv.Itoa(1+r.Intn(4)) + randDigits(r, 32)
		pairs = append(pairs, [2]string{x[:10] + "." + x[10:], y[:10] + "." + y[10:]})
	}
	return p7, prices, rates, pairs
}

func parseAll(inputs []string) ([]decimal.Decimal, error) {
	out := make([]decimal.Decimal, len(inputs))
	for i, s := range inputs {
		var err error
		if out[i], err = decimal.Parse(s); err != nil {
			return nil, fmt.Errorf("Parse(%q): %w", s, err)
		}
	}
	return out, nil
}

// catalogueRows builds the catalogue family: RoundToPrecision,
// RoundToMultiple, Sqrt, Pow and budgeted context Sub on money- and
// Decimal128-shaped operands. Sum and SumWithBudget are timed by
// BenchmarkSumVsFold, context Add by BenchmarkContextAddGap/Near and binary64
// egress by BenchmarkBinary64Egress.
func catalogueRows(tb testing.TB) []oracleRow {
	p7Text, priceText, rateText, pairText := catalogueCorpora()
	money6 := portfolioF1Inputs["money6"]
	big40 := portfolioF1Inputs["big40"]
	must := func(values []decimal.Decimal, err error) []decimal.Decimal {
		if err != nil {
			tb.Fatal(err)
		}
		return values
	}
	p7, prices, rates := must(parseAll(p7Text)), must(parseAll(priceText)), must(parseAll(rateText))
	moneyValues, big40Values := must(parseAll(money6)), must(parseAll(big40))
	squares := make([]decimal.Decimal, len(money6))
	for i, s := range money6 {
		_, c, e, err := decimalParts(s)
		if err != nil {
			tb.Fatal(err)
		}
		squares[i] = decimal.MustParse(new(big.Int).Mul(c, c).String() + "E" + strconv.FormatInt(2*e, 10))
	}
	xs, ys := make([]decimal.Decimal, len(pairText)), make([]decimal.Decimal, len(pairText))
	for i, pair := range pairText {
		xs[i], ys[i] = decimal.MustParse(pair[0]), decimal.MustParse(pair[1])
	}
	d128 := decimal.Decimal128Context()
	nickel := decimal.MustParse("0.05")
	budget := decimal.Budget{MaxWork: 1 << 40}

	// roundTo checks a precision rounding of text to p digits (ties to even).
	roundTo := func(text string, got decimal.Decimal, c decimal.Conditions, p int) error {
		negative, coefficient, exponent, err := decimalParts(text)
		if err != nil {
			return err
		}
		q, cut, inexact := roundDigits(coefficient, p, false)
		if err := sameCohort(got, negative, q, exponent+int64(cut)); err != nil {
			return err
		}
		return checkInexact(c, cut, inexact)
	}

	return []oracleRow{
		{
			variant: "roundprecision-p7", size: len(p7),
			check: func() error {
				return eachEntry(len(p7), func(i int) error {
					got, c, err := p7[i].RoundToPrecision(7, decimal.TiesToEven)
					if err != nil {
						return err
					}
					return roundTo(p7Text[i], got, c, 7)
				})
			},
			run: func(i int) (err error) { sinkDecimal, _, err = p7[i].RoundToPrecision(7, decimal.TiesToEven); return },
		},
		{
			variant: "roundprecision-d128", size: len(big40Values),
			check: func() error {
				return eachEntry(len(big40Values), func(i int) error {
					got, c, err := big40Values[i].RoundToPrecisionWithContext(d128)
					if err != nil {
						return err
					}
					return roundTo(big40[i], got, c, 34)
				})
			},
			run: func(i int) (err error) {
				sinkDecimal, _, err = big40Values[i].RoundToPrecisionWithContext(d128)
				return
			},
		},
		{
			// Cash rounding to 0.05, ties away from zero: the multiple r·5 at
			// exponent −2 with r = x/0.05 = 20x rounded half away.
			variant: "roundmultiple-nickel", size: len(prices),
			check: func() error {
				return eachEntry(len(prices), func(i int) error {
					got, c, err := prices[i].RoundToMultiple(nickel, decimal.TiesAwayFromZero)
					if err != nil {
						return err
					}
					x, _ := new(big.Rat).SetString(priceText[i])
					q := new(big.Rat).Mul(x, big.NewRat(20, 1))
					r, rem := new(big.Int).QuoRem(q.Num(), q.Denom(), new(big.Int))
					if new(big.Int).Lsh(rem, 1).Cmp(q.Denom()) >= 0 {
						r.Add(r, big.NewInt(1))
					}
					if err := sameCohort(got, false, r.Mul(r, big.NewInt(5)), -2); err != nil {
						return err
					}
					return checkInexact(c, 0, rem.Sign() != 0)
				})
			},
			run: func(i int) (err error) {
				sinkDecimal, _, err = prices[i].RoundToMultiple(nickel, decimal.TiesAwayFromZero)
				return
			},
		},
		{
			// √(C²·10^2e) is exactly C·10^e: the F1 money6 value itself.
			variant: "sqrt-exact", size: len(squares),
			check: func() error {
				return eachEntry(len(squares), func(i int) error {
					got, err := squares[i].Sqrt()
					if err != nil {
						return err
					}
					_, c, e, _ := decimalParts(money6[i])
					return sameCohort(got, false, c, e)
				})
			},
			run: func(i int) (err error) { sinkDecimal, err = squares[i].Sqrt(); return },
		},
		{
			// √(C·10^−2) for six-digit C lies in [31.6, 100): 34 digits at
			// exponent −32 from ⌊√(C·10^62)⌋, rounded half-even by comparing
			// 4N with (2s+1)². A perfect square C is exact at ⌊−2/2⌋ = −1.
			variant: "sqrt-d128", size: len(moneyValues),
			check: func() error {
				return eachEntry(len(moneyValues), func(i int) error {
					got, c, err := moneyValues[i].SqrtWithContext(d128)
					if err != nil {
						return err
					}
					_, coefficient, _, _ := decimalParts(money6[i])
					if root := new(big.Int).Sqrt(coefficient); new(big.Int).Mul(root, root).Cmp(coefficient) == 0 {
						if err := sameCohort(got, false, root, -1); err != nil {
							return err
						}
						return checkInexact(c, 0, false)
					}
					n := new(big.Int).Mul(coefficient, pow10(62))
					s := new(big.Int).Sqrt(n)
					odd := new(big.Int).Lsh(s, 1)
					odd.Add(odd, big.NewInt(1))
					switch cmp := new(big.Int).Lsh(n, 2).Cmp(odd.Mul(odd, odd)); {
					case cmp > 0, cmp == 0 && s.Bit(0) == 1:
						s.Add(s, big.NewInt(1))
					}
					if digitCount(s) != 34 {
						return fmt.Errorf("oracle root %s is not 34 digits", s)
					}
					if err := sameCohort(got, false, s, -32); err != nil {
						return err
					}
					return checkInexact(c, 1, true)
				})
			},
			run: func(i int) (err error) { sinkDecimal, _, err = moneyValues[i].SqrtWithContext(d128); return },
		},
		{
			variant: "pow-cube", size: len(moneyValues),
			check: func() error {
				return eachEntry(len(moneyValues), func(i int) error {
					got, err := moneyValues[i].Pow(3)
					if err != nil {
						return err
					}
					_, c, e, _ := decimalParts(money6[i])
					return sameCohort(got, false, new(big.Int).Exp(c, big.NewInt(3), nil), 3*e)
				})
			},
			run: func(i int) (err error) { sinkDecimal, err = moneyValues[i].Pow(3); return },
		},
		{
			// Daily compounding for a year: C^365 exactly (up to 2,190
			// digits), rounded once to 34 digits half-even.
			variant: "pow365-d128", size: len(rates),
			check: func() error {
				return eachEntry(len(rates), func(i int) error {
					got, c, err := rates[i].PowWithContext(365, d128)
					if err != nil {
						return err
					}
					_, coefficient, exponent, _ := decimalParts(rateText[i])
					q, cut, inexact := roundDigits(new(big.Int).Exp(coefficient, big.NewInt(365), nil), 34, false)
					if !inexact {
						return errors.New("vacuous: the oracle power is exact")
					}
					if err := sameCohort(got, false, q, 365*exponent+int64(cut)); err != nil {
						return err
					}
					return checkInexact(c, cut, inexact)
				})
			},
			run: func(i int) (err error) { sinkDecimal, _, err = rates[i].PowWithContext(365, d128); return },
		},
		{
			// x − y with x a 37-digit and y a 33-digit operand near 10^9..10^10
			// (x > y), under a generous work cap, against the math/big oracle.
			variant: "contextsub-d128-budget", size: len(xs),
			check: func() error {
				rounded := 0
				err := eachEntry(len(xs), func(i int) error {
					got, c, err := xs[i].SubWithContext(ys[i], d128.WithBudget(budget))
					if err != nil {
						return err
					}
					_, xc, xe, _ := decimalParts(pairText[i][0])
					_, yc, ye, _ := decimalParts(pairText[i][1])
					digits, exponent, conditions := contextAddOracle(xc, new(big.Int).Neg(yc), xe, ye, 34)
					want, _ := new(big.Int).SetString(digits, 10)
					if err := sameCohort(got, false, want, exponent); err != nil {
						return err
					}
					if c != conditions {
						return fmt.Errorf("conditions %v, oracle %v", c, conditions)
					}
					if c&decimal.Inexact != 0 {
						rounded++
					}
					return nil
				})
				if err == nil && rounded < 128 {
					err = fmt.Errorf("vacuous: only %d of %d differences round", rounded, len(xs))
				}
				return err
			},
			run: func(i int) (err error) {
				sinkDecimal, _, err = xs[i].SubWithContext(ys[i], d128.WithBudget(budget))
				return
			},
		},
	}
}

// TestCatalogueOracle checks every catalogue row against its
// independent oracle over the full committed-seed corpus, as the benchmark
// does before timing.
func TestCatalogueOracle(t *testing.T) {
	testOracleRows(t, catalogueRows(t), catalogueVariants)
}

// BenchmarkCatalogue is the supplemental catalogue family:
// RoundToPrecision, RoundToMultiple, Sqrt, Pow and budgeted context Sub.
func BenchmarkCatalogue(b *testing.B) {
	benchOracleRows(b, catalogueRows(b))
}
