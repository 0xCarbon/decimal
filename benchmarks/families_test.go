// SPDX-License-Identifier: Apache-2.0

// Benchmark families F1–F8 (see portfolio_test.go for the portfolio
// contract).

package benchmarks

import (
	"crypto/sha256"
	"fmt"
	"math/big"
	"strconv"
	"strings"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

var sinkDecimal decimal.Decimal

const f4ExtraCorpusSHA = "247bdfe0740c2ba31e6054eaae48d32171db561462f677b1c631eb88e6c69e16"

func TestF4DisplayExtraIndependentOracle(t *testing.T) {
	for _, tc := range []struct{ input, want string }{
		{"0", "0E+0"},
		{"-0.000E+8", "0E+0"},
		{"1E+2", "100E+0"},
		{"1E-1", "100E-3"},
		{"12345", "12.345E+3"},
		{"-123.4500", "-123.4500E+0"},
		{"-5.0E-12", "-5.0E-12"},
	} {
		if got := f4ExtraEngineeringOracle(tc.input); got != tc.want {
			t.Errorf("engineering oracle(%q) = %q, want %q", tc.input, got, tc.want)
		}
	}
	if got := f4ExtraInputs(); len(got) != 256 {
		t.Errorf("supplemental F4 corpus has %d inputs, want 256", len(got))
	}
}

func TestF4DisplayExtraCorpusDigest(t *testing.T) {
	inputs := f4ExtraInputs()
	if len(inputs) != 256 {
		t.Fatalf("supplemental F4 corpus has %d inputs, want 256", len(inputs))
	}
	for i, want := range []string{"0", "-0.000E+8", "1E+2", "1E-1", "12345", "-123.4500", "9.995", "-9.995"} {
		if inputs[i] != want {
			t.Fatalf("anchor %d = %q, want %q", i, inputs[i], want)
		}
	}
	gotSHA := f4ExtraDigest(inputs)
	if gotSHA != f4ExtraCorpusSHA {
		t.Fatalf("supplemental F4 corpus SHA-256 = %s, want %s", gotSHA, f4ExtraCorpusSHA)
	}
}

func TestF4DisplayExtraRejectsCorpusDrift(t *testing.T) {
	inputs := f4ExtraInputs()
	inputs[20] = "2"
	if _, err := f4ExtraAccuracy(inputs); err == nil {
		t.Fatal("supplemental F4 accuracy accepted a changed corpus")
	}
}

func TestF4DisplayExtraPublicAccuracy(t *testing.T) {
	inputs := f4ExtraInputs()
	checks, err := f4ExtraAccuracy(inputs)
	if err != nil {
		t.Fatal(err)
	}
	if len(checks.values) != 256 || len(checks.engineeringGot) != 256 || len(checks.fmtGot) != 256 {
		t.Fatalf("supplemental F4 checks cover %d values, %d Engineering and %d fmt outputs; want 256 each", len(checks.values), len(checks.engineeringGot), len(checks.fmtGot))
	}
	requireMatchedAccuracy(t, "F4DisplayExtra/engineering", checks.engineeringGot, checks.engineeringWant)
	requireMatchedAccuracy(t, "F4DisplayExtra/fmt", checks.fmtGot, checks.fmtWant)
}

type f4ExtraCheck struct {
	values                          []decimal.Decimal
	engineeringGot, engineeringWant []string
	fmtGot, fmtWant                 []string
}

// f4ExtraInputs is a supplemental workload, separate from the three F4
// variants.
func f4ExtraInputs() []string {
	inputs := append([]string(nil), portfolioF4Inputs["scientific"]...)
	for i := range inputs {
		if i%2 == 1 {
			inputs[i] = "-" + inputs[i]
		}
	}
	anchors := [...]string{
		"0", "-0.000E+8", "1E+2", "1E-1", "12345", "-123.4500", "9.995", "-9.995",
		"1.235", "1.245", "1.2451", "0.000012345", "9999999999999999999999999999999999999999",
		"-0.0000000012300", "1000E+9", "-5.0E-12",
	}
	copy(inputs, anchors[:])
	return inputs
}

func f4ExtraDigest(inputs []string) string {
	return fmt.Sprintf("%x", sha256.Sum256([]byte(strings.Join(inputs, "\n")+"\n")))
}

// f4ExtraEngineeringOracle derives grouped exponent and coefficient placement
// from the raw decimal syntax, without parsing or displaying a Decimal.
func f4ExtraEngineeringOracle(input string) string {
	negative := strings.HasPrefix(input, "-")
	input = strings.TrimPrefix(input, "-")
	exponent := int64(0)
	if at := strings.IndexAny(input, "Ee"); at >= 0 {
		var err error
		exponent, err = strconv.ParseInt(input[at+1:], 10, 64)
		if err != nil {
			panic("invalid F4 supplemental exponent: " + input)
		}
		input = input[:at]
	}
	integer, fraction, hasPoint := strings.Cut(input, ".")
	if !hasPoint {
		fraction = ""
	}
	digits := strings.TrimLeft(integer+fraction, "0")
	if digits == "" {
		return "0E+0"
	}
	exponent -= int64(len(fraction))
	adjusted := exponent + int64(len(digits)-1)
	group := adjusted / 3 * 3
	if adjusted < 0 && adjusted%3 != 0 {
		group -= 3
	}
	before := int(adjusted - group + 1)
	if len(digits) < before {
		digits += strings.Repeat("0", before-len(digits))
	}
	coefficient := digits[:before]
	if len(digits) > before {
		coefficient += "." + digits[before:]
	}
	if negative {
		coefficient = "-" + coefficient
	}
	groupText := strconv.FormatInt(group, 10)
	if group >= 0 {
		groupText = "+" + groupText
	}
	return coefficient + "E" + groupText
}

func f4ExtraAccuracy(inputs []string) (f4ExtraCheck, error) {
	if len(inputs) != 256 || f4ExtraDigest(inputs) != f4ExtraCorpusSHA {
		return f4ExtraCheck{}, fmt.Errorf("F4 supplemental corpus size or digest mismatch")
	}
	checks := f4ExtraCheck{
		values:          make([]decimal.Decimal, len(inputs)),
		engineeringGot:  make([]string, len(inputs)),
		engineeringWant: make([]string, len(inputs)),
		fmtGot:          make([]string, len(inputs)),
		fmtWant:         make([]string, len(inputs)),
	}
	for i, input := range inputs {
		value, err := decimal.Parse(input)
		if err != nil {
			return f4ExtraCheck{}, fmt.Errorf("F4 supplemental input %d %q: %w", i, input, err)
		}
		checks.values[i] = value
		checks.engineeringGot[i], err = value.Engineering()
		if err != nil {
			return f4ExtraCheck{}, fmt.Errorf("F4 Engineering input %d %q: %w", i, input, err)
		}
		checks.engineeringWant[i] = f4ExtraEngineeringOracle(input)
		checks.fmtGot[i] = fmt.Sprintf("%12.3e", value)
		body := f4ExpectedScientific3(input)
		checks.fmtWant[i] = strings.Repeat(" ", max(0, 12-len(body))) + body
		inputRat, inputOK := new(big.Rat).SetString(input)
		engRat, engOK := new(big.Rat).SetString(checks.engineeringGot[i])
		wantEngRat, wantEngOK := new(big.Rat).SetString(checks.engineeringWant[i])
		fmtRat, fmtOK := new(big.Rat).SetString(strings.TrimSpace(checks.fmtGot[i]))
		wantFmtRat, wantFmtOK := new(big.Rat).SetString(body)
		if !inputOK || !engOK || !wantEngOK || !fmtOK || !wantFmtOK || engRat.Cmp(inputRat) != 0 || wantEngRat.Cmp(inputRat) != 0 || fmtRat.Cmp(wantFmtRat) != 0 {
			return f4ExtraCheck{}, fmt.Errorf("F4 supplemental numeric mismatch at %d: input %q, Engineering %q/%q, fmt %q/%q", i, input, checks.engineeringGot[i], checks.engineeringWant[i], checks.fmtGot[i], checks.fmtWant[i])
		}
	}
	return checks, nil
}

// f1ExpectedCanonical follows the F1 corpus shapes, independently
// of Decimal's parser and emitter. The expform variant shifts its explicit
// four fractional digits by the one-digit positive exponent when plain
// notation is selected; the other variants are already canonical.
func f1ExpectedCanonical(variant, input string) string {
	if variant != "expform" {
		return input
	}
	shift := int(input[len(input)-1] - '0')
	if shift > 4 {
		return input
	}
	digits := input[:1] + input[2:6]
	point := 1 + shift
	if point == len(digits) {
		return digits
	}
	return digits[:point] + "." + digits[point:]
}

// benchF1Parse measures public Parse on the F1 money6/int19/big40/expform
// corpus after checking its numeric result against independent big.Rat values.
func benchF1Parse(b *testing.B) {
	inputs := portfolioF1Inputs
	for _, variant := range portfolioFamilyVariants["F1Parse"] {
		corpus := inputs[variant]
		b.Run("decimal/"+variant, func(b *testing.B) {
			got := make([]string, len(corpus))
			want := make([]string, len(corpus))
			for i, input := range corpus {
				value, err := decimal.Parse(input)
				if err != nil {
					b.Fatalf("Parse(%q): %v", input, err)
				}
				text, err := value.Text(0)
				if err != nil {
					b.Fatalf("Text(Parse(%q)): %v", input, err)
				}
				parsed, ok := new(big.Rat).SetString(text)
				if !ok {
					b.Fatalf("canonical text %q is not a rational", text)
				}
				oracle, ok := new(big.Rat).SetString(input)
				if !ok {
					b.Fatalf("portfolio input %q is not a rational", input)
				}
				if parsed.Cmp(oracle) != 0 {
					b.Fatalf("numeric mismatch on F1 %s input %q: got %s, want %s", variant, input, parsed.RatString(), oracle.RatString())
				}
				got[i], want[i] = text, f1ExpectedCanonical(variant, input)
			}
			requireMatchedAccuracy(b, "F1Parse/"+variant, got, want)
			b.ReportAllocs()
			b.ResetTimer()
			i := 0
			for b.Loop() {
				var err error
				sinkDecimal, err = decimal.Parse(corpus[i])
				if err != nil {
					b.Fatal(err)
				}
				if i++; i == len(corpus) {
					i = 0
				}
			}
		})
	}
}

// BenchmarkF1Parse measures the parse family (conversion family; reported
// separately from arithmetic families).
func BenchmarkF1Parse(b *testing.B) { benchF1Parse(b) }

// BenchmarkF2Aggregate measures 1000 public exact adds per iteration. The
// setup compares every prefix sum with an independent math/big.Rat oracle.
func BenchmarkF2Aggregate(b *testing.B) {
	inputs := portfolioF2Inputs
	if len(inputs) != 1000 {
		b.Fatalf("F2 corpus has %d operands, want 1000", len(inputs))
	}
	values := make([]decimal.Decimal, len(inputs))
	got, want := make([]string, len(inputs)), make([]string, len(inputs))
	cohortGot, cohortWant := make([]string, len(inputs)), make([]string, len(inputs))
	var sum decimal.Decimal
	oracle := new(big.Rat)
	scale := 0
	for i, input := range inputs {
		var err error
		values[i], err = decimal.Parse(input)
		if err != nil {
			b.Fatalf("Parse(%q): %v", input, err)
		}
		sum, err = sum.Add(values[i])
		if err != nil {
			b.Fatalf("F2 prefix %d Add: %v", i, err)
		}
		text, err := sum.Text(0)
		if err != nil {
			b.Fatalf("F2 prefix %d Text: %v", i, err)
		}
		numeric, ok := new(big.Rat).SetString(text)
		if !ok {
			b.Fatalf("F2 prefix %d invalid result %q", i, text)
		}
		operand, ok := new(big.Rat).SetString(input)
		if !ok {
			b.Fatalf("F2 invalid input %q", input)
		}
		oracle.Add(oracle, operand)
		got[i], want[i] = numeric.RatString(), oracle.RatString()
		if dot := strings.IndexByte(input, '.'); dot >= 0 {
			scale = max(scale, len(input)-dot-1)
		}
		cohortGot[i], cohortWant[i] = text, oracle.FloatString(scale)
	}
	b.Run("decimal/mixed1000", func(b *testing.B) {
		requireMatchedAccuracy(b, "F2Aggregate/mixed1000", got, want)
		requireMatchedAccuracy(b, "F2Aggregate/mixed1000-cohort", cohortGot, cohortWant)
		b.ReportAllocs()
		b.ResetTimer()
		for b.Loop() {
			var accumulator decimal.Decimal
			for _, value := range values {
				var err error
				accumulator, err = accumulator.Add(value)
				if err != nil {
					b.Fatal(err)
				}
			}
			sinkDecimal = accumulator
		}
	})
}

// BenchmarkF3MoneyLoop runs price×qty→round→accumulate→fee→net per iteration.
// The independent rational and cohort check completes before timing begins.
func BenchmarkF3MoneyLoop(b *testing.B) {
	prices, qtys := f3MoneyLoopInputs()
	b.Run("decimal/price-qty-round-fee", func(b *testing.B) {
		lines, rate, _ := f3MoneyLoopAccuracy(b, prices, qtys)
		b.ReportAllocs()
		b.ResetTimer()
		for b.Loop() {
			result, err := f3MoneyLoop(lines, rate, nil)
			if err != nil {
				b.Fatal(err)
			}
			sinkDecimal = result.net
		}
	})
}

// BenchmarkF4Format measures the format family (conversion family; reported
// separately from arithmetic families).
func BenchmarkF4Format(b *testing.B) {
	inputs := portfolioF4Inputs
	for _, variant := range portfolioFamilyVariants["F4Format"] {
		corpus := inputs[variant]
		if variant == "plain" {
			values := make([]decimal.Decimal, len(corpus))
			got := make([]string, len(corpus))
			want := make([]string, len(corpus))
			for i, input := range corpus {
				var err error
				values[i], err = decimal.Parse(input)
				if err != nil {
					b.Fatalf("Parse(%q): %v", input, err)
				}
				got[i], err = values[i].Text(0)
				if err != nil {
					b.Fatalf("Text(Parse(%q)): %v", input, err)
				}
				oracle, ok := new(big.Int).SetString(input, 10)
				if !ok {
					b.Fatalf("portfolio input %q is not an integer", input)
				}
				want[i] = oracle.String()
			}
			b.Run("decimal/plain", func(b *testing.B) {
				requireMatchedAccuracy(b, "F4Format/plain", got, want)
				b.ReportAllocs()
				b.ResetTimer()
				i := 0
				for b.Loop() {
					var err error
					sinkString, err = values[i].Text(0)
					if err != nil {
						b.Fatal(err)
					}
					if i++; i == len(values) {
						i = 0
					}
				}
			})
			continue
		}
		values := make([]decimal.Decimal, len(corpus))
		got, want := make([]string, len(corpus)), make([]string, len(corpus))
		gotNumeric, wantNumeric := make([]string, len(corpus)), make([]string, len(corpus))
		for i, input := range corpus {
			var err error
			values[i], err = decimal.Parse(input)
			if err != nil {
				b.Fatalf("Parse(%q): %v", input, err)
			}
			got[i], err = f4FormatValue(variant, values[i])
			if err != nil {
				b.Fatalf("F4 %s(%q): %v", variant, input, err)
			}
			switch variant {
			case "fixed2dp":
				want[i] = f4ExpectedFixed2dp(input)
			case "scientific":
				want[i] = f4ExpectedScientific3(input)
			}
			actual, actualOK := new(big.Rat).SetString(got[i])
			expected, expectedOK := new(big.Rat).SetString(want[i])
			if !actualOK || !expectedOK {
				b.Fatalf("F4 %s input %q produced invalid rational text: got %q, want %q", variant, input, got[i], want[i])
			}
			gotNumeric[i], wantNumeric[i] = actual.RatString(), expected.RatString()
		}
		b.Run("decimal/"+variant, func(b *testing.B) {
			requireMatchedAccuracy(b, "F4Format/"+variant, got, want)
			requireMatchedAccuracy(b, "F4Format/"+variant+"-numeric", gotNumeric, wantNumeric)
			b.ReportAllocs()
			b.ResetTimer()
			i := 0
			for b.Loop() {
				var err error
				sinkString, err = f4FormatValue(variant, values[i])
				if err != nil {
					b.Fatal(err)
				}
				if i++; i == len(values) {
					i = 0
				}
			}
		})
	}
}

// BenchmarkF4DisplayExtra supplements the F4 plain/fixed2dp/scientific
// table with public Engineering and fmt.Formatter paths. Both complete 256-row
// independent accuracy checks before either timing row can start.
func BenchmarkF4DisplayExtra(b *testing.B) {
	inputs := f4ExtraInputs()
	if len(inputs) != 256 {
		b.Fatalf("F4 supplemental corpus has %d inputs, want 256", len(inputs))
	}
	checks, err := f4ExtraAccuracy(inputs)
	if err != nil {
		b.Fatal(err)
	}
	requireMatchedAccuracy(b, "F4DisplayExtra/engineering", checks.engineeringGot, checks.engineeringWant)
	requireMatchedAccuracy(b, "F4DisplayExtra/fmt", checks.fmtGot, checks.fmtWant)
	b.Run("decimal/engineering", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			var err error
			sinkString, err = checks.values[i].Engineering()
			if err != nil {
				b.Fatal(err)
			}
			i = (i + 1) & 255
		}
	})
	b.Run("decimal/fmt", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			sinkString = fmt.Sprintf("%12.3e", checks.values[i])
			i = (i + 1) & 255
		}
	})
}

// BenchmarkF5MapKey measures two public numeric-key recipes over matched
// 1024-entry churn. The consumer-owned Hasher table lives in f5_test.go.
func BenchmarkF5MapKey(b *testing.B) {
	benchF5MapKey(b)
}

// BenchmarkF6TightArith measures public 19-digit add, multiply, small
// multiply, division and comparison paths.
func BenchmarkF6TightArith(b *testing.B) {
	inputs := portfolioF6Inputs
	for _, variant := range portfolioFamilyVariants["F6TightArith"] {
		pair := inputs[variant]
		if variant == "cmp19" {
			left, lerr := decimal.Parse(pair[0])
			right, rerr := decimal.Parse(pair[1])
			li, lok := new(big.Int).SetString(pair[0], 10)
			ri, rok := new(big.Int).SetString(pair[1], 10)
			if lerr != nil || rerr != nil || !lok || !rok {
				b.Fatalf("invalid F6 cmp19 inputs: %q, %q", pair[0], pair[1])
			}
			// Accuracy covers both orders and self-comparison.
			got := []string{strconv.Itoa(left.Compare(right)), strconv.Itoa(right.Compare(left)), strconv.Itoa(left.Compare(left))}
			want := []string{strconv.Itoa(li.Cmp(ri)), strconv.Itoa(ri.Cmp(li)), "0"}
			b.Run("decimal/"+variant, func(b *testing.B) {
				requireMatchedAccuracy(b, "F6TightArith/"+variant, got, want)
				b.ReportAllocs()
				b.ResetTimer()
				for b.Loop() {
					sinkInt = left.Compare(right)
				}
			})
			continue
		}
		if variant == "add19" || variant == "mul19" || variant == "mulsmall" {
			left, err := decimal.Parse(pair[0])
			if err != nil {
				b.Fatal(err)
			}
			right, err := decimal.Parse(pair[1])
			if err != nil {
				b.Fatal(err)
			}
			li, lok := new(big.Int).SetString(pair[0], 10)
			ri, rok := new(big.Int).SetString(pair[1], 10)
			if !lok || !rok {
				b.Fatalf("invalid F6 integer inputs: %q, %q", pair[0], pair[1])
			}
			var result decimal.Decimal
			var expected *big.Int
			if variant == "add19" {
				result, err = left.Add(right)
				expected = new(big.Int).Add(li, ri)
			} else {
				result, err = left.Mul(right)
				expected = new(big.Int).Mul(li, ri)
			}
			if err != nil {
				b.Fatalf("F6 %s accuracy operation: %v", variant, err)
			}
			actual, err := result.Text(0)
			if err != nil {
				b.Fatalf("F6 %s accuracy Text: %v", variant, err)
			}
			b.Run("decimal/"+variant, func(b *testing.B) {
				requireMatchedAccuracy(b, "F6TightArith/"+variant, []string{actual}, []string{expected.String()})
				b.ReportAllocs()
				b.ResetTimer()
				for b.Loop() {
					if variant == "add19" {
						sinkDecimal, err = left.Add(right)
					} else {
						sinkDecimal, err = left.Mul(right)
					}
					if err != nil {
						b.Fatal(err)
					}
				}
			})
			continue
		}
		// div2dp rounds a 19-by-19-digit quotient once to two decimal places
		// (DivToExponent, TiesToEven); divby4 is an exact terminating Div.
		left, err := decimal.Parse(pair[0])
		if err != nil {
			b.Fatal(err)
		}
		right, err := decimal.Parse(pair[1])
		if err != nil {
			b.Fatal(err)
		}
		q, ok := new(big.Rat).SetString(pair[0] + "/" + pair[1])
		if !ok {
			b.Fatalf("invalid F6 division inputs: %q, %q", pair[0], pair[1])
		}
		var actual, expected string
		if variant == "div2dp" {
			result, _, err := left.DivToExponent(right, -2, decimal.TiesToEven)
			if err != nil {
				b.Fatalf("F6 div2dp accuracy operation: %v", err)
			}
			actual, expected = result.String(), roundRatTiesToEven(q, 2)
		} else {
			result, err := left.Div(right)
			if err != nil {
				b.Fatalf("F6 divby4 accuracy operation: %v", err)
			}
			places := 0
			for !new(big.Rat).Mul(q, new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(places)), nil))).IsInt() {
				places++
			}
			actual, expected = result.String(), q.FloatString(places)
		}
		b.Run("decimal/"+variant, func(b *testing.B) {
			requireMatchedAccuracy(b, "F6TightArith/"+variant, []string{actual}, []string{expected})
			b.ReportAllocs()
			b.ResetTimer()
			for b.Loop() {
				if variant == "div2dp" {
					sinkDecimal, _, err = left.DivToExponent(right, -2, decimal.TiesToEven)
				} else {
					sinkDecimal, err = left.Div(right)
				}
				if err != nil {
					b.Fatal(err)
				}
			}
		})
	}
}

// roundRatTiesToEven renders a nonnegative rational rounded half-to-even at
// the given number of decimal places, independently of the library.
func roundRatTiesToEven(q *big.Rat, places int64) string {
	scale := new(big.Int).Exp(big.NewInt(10), big.NewInt(places), nil)
	v := new(big.Rat).Mul(q, new(big.Rat).SetInt(scale))
	floor, rem := new(big.Int).QuoRem(v.Num(), v.Denom(), new(big.Int))
	twice := new(big.Int).Mul(rem, big.NewInt(2))
	if c := twice.Cmp(v.Denom()); c > 0 || c == 0 && floor.Bit(0) == 1 {
		floor.Add(floor, big.NewInt(1))
	}
	return new(big.Rat).SetFrac(floor, scale).FloatString(int(places))
}

// BenchmarkF7JSON measures family F7 JSON (stdlib encoding/json only;
// plain and quoted variants).
func BenchmarkF7JSON(b *testing.B) {
	inputs := f7JSONValues()
	for _, variant := range portfolioFamilyVariants["F7JSON"] {
		corpus := make([][]byte, len(inputs[variant]))
		got, want := make([]string, len(corpus)), make([]string, len(corpus))
		for i, token := range inputs[variant] {
			corpus[i] = []byte(token)
			// Library-independent oracle: MarshalJSON of a two-place value
			// is the bare token text, with any JSON quotes removed.
			want[i] = strings.Trim(token, `"`)
			var d decimal.Decimal
			if err := d.UnmarshalJSON(corpus[i]); err != nil {
				b.Fatalf("F7 %s accuracy UnmarshalJSON(%s): %v", variant, token, err)
			}
			blob, err := d.MarshalJSON()
			if err != nil {
				b.Fatalf("F7 %s accuracy MarshalJSON: %v", variant, err)
			}
			got[i] = string(blob)
		}
		b.Run("decimal/"+variant, func(b *testing.B) {
			requireMatchedAccuracy(b, "F7JSON/"+variant, got, want)
			b.ReportAllocs()
			b.ResetTimer()
			i := 0
			for b.Loop() {
				var d decimal.Decimal
				if err := d.UnmarshalJSON(corpus[i]); err != nil {
					b.Fatal(err)
				}
				blob, err := d.MarshalJSON()
				if err != nil {
					b.Fatal(err)
				}
				sinkInt = len(blob)
				if i++; i == len(corpus) {
					i = 0
				}
			}
		})
	}
}

// BenchmarkF8Database times family F8: a database/sql round trip through
// the in-tree fake driver (f8_test.go). Each
// variant's matched-accuracy precondition runs first against the
// independent canonical-form oracle.
func BenchmarkF8Database(b *testing.B) {
	db := openF8(b)
	defer db.Close()
	values, _, valid := f8Corpus()
	for _, variant := range portfolioFamilyVariants["F8Database"] {
		got, want := f8Accuracy(b, db, variant)
		b.Run("decimal/"+variant, func(b *testing.B) {
			requireMatchedAccuracy(b, "F8Database/"+variant, got, want)
			b.ReportAllocs()
			b.ResetTimer()
			i := 0
			for b.Loop() {
				var err error
				switch variant {
				case "valuer-scan":
					var out decimal.Decimal
					err = db.QueryRow("echo", values[i]).Scan(&out)
				case "sqldecimal-compose":
					var out decimal.Decimal
					err = db.QueryRow("echo", decimal.SQLDecimal{Decimal: values[i]}).Scan(&out)
				case "null-roundtrip":
					var out decimal.NullDecimal
					err = db.QueryRow("echo", decimal.NullDecimal{Decimal: values[i], Valid: valid[i]}).Scan(&out)
				}
				if err != nil {
					b.Fatal(err)
				}
				if i++; i == len(values) {
					i = 0
				}
			}
		})
	}
}
