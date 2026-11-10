// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"crypto/sha256"
	"fmt"
	"math/rand"
	"strconv"
	"strings"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

type f1ValuePair struct{ x, y string }
type f1ValueValues struct{ x, y decimal.Decimal }
type f1ValueCheck struct {
	name      string
	got, want []string
}

var (
	f1SinkValue decimal.Decimal
	f1SinkInt   int
	f1SinkBool  bool
)

// BenchmarkF1ValueOps supplements the F1–F8 portfolio table. The
// outer preflight checks all eight operations before the first timing line.
func BenchmarkF1ValueOps(b *testing.B) {
	pairs := f1ValuePairs()
	values, err := f1ValueParse(pairs)
	if err != nil {
		b.Fatal(err)
	}
	checks, err := f1ValueAccuracy(pairs, values)
	if err != nil {
		b.Fatal(err)
	}
	for _, check := range checks {
		requireMatchedAccuracy(b, "F1ValueOps/"+check.name, check.got, check.want)
	}
	b.Run("decimal/neg", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			f1SinkValue = values[i].x.Neg()
			i = (i + 1) & 255
		}
	})
	b.Run("decimal/abs", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			f1SinkValue = values[i].x.Abs()
			i = (i + 1) & 255
		}
	})
	b.Run("decimal/sign", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			f1SinkInt = values[i].x.Sign()
			i = (i + 1) & 255
		}
	})
	b.Run("decimal/iszero", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			f1SinkBool = values[i].x.IsZero()
			i = (i + 1) & 255
		}
	})
	b.Run("decimal/min", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			f1SinkValue = values[i].x.Min(values[i].y)
			i = (i + 1) & 255
		}
	})
	b.Run("decimal/max", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			f1SinkValue = values[i].x.Max(values[i].y)
			i = (i + 1) & 255
		}
	})
	b.Run("decimal/compare", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			f1SinkInt = values[i].x.Compare(values[i].y)
			i = (i + 1) & 255
		}
	})
	b.Run("decimal/reduce", func(b *testing.B) {
		b.ReportAllocs()
		b.ResetTimer()
		i := 0
		for b.Loop() {
			f1SinkValue = values[i].x.Reduce()
			i = (i + 1) & 255
		}
	})
}

func f1ValueParse(pairs []f1ValuePair) ([]f1ValueValues, error) {
	values := make([]f1ValueValues, len(pairs))
	for i, p := range pairs {
		var err error
		values[i].x, err = decimal.Parse(p.x)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d x: %w", i, err)
		}
		values[i].y, err = decimal.Parse(p.y)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d y: %w", i, err)
		}
	}
	return values, nil
}

func f1ValueCanonical(raw string) (string, error) {
	d, err := decimal.Parse(raw)
	if err != nil {
		return "", err
	}
	return d.Text(0)
}

func f1ValueCohortMatches(raw f1Symbolic, canonical string) bool {
	got, err := f1ValueSplit(canonical)
	return err == nil && got.sign == raw.sign && got.digits == raw.digits && got.exponent == raw.exponent
}

func f1ValueExpectedMinX(x, y f1Symbolic, cmp int) bool {
	if cmp != 0 {
		return cmp < 0
	}
	if x.sign < 0 {
		return x.exponent >= y.exponent
	}
	return x.exponent <= y.exponent
}

func f1ValueExpectedMaxX(x, y f1Symbolic, cmp int) bool {
	if cmp != 0 {
		return cmp > 0
	}
	if x.sign < 0 {
		return x.exponent <= y.exponent
	}
	return x.exponent >= y.exponent
}

// f1ValueAccuracy computes all eight vectors before any benchmark timer.
// Its expected values use raw text and a symbolic decimal comparator.
func f1ValueAccuracy(pairs []f1ValuePair, values []f1ValueValues) ([]f1ValueCheck, error) {
	if len(pairs) != 256 || len(values) != len(pairs) || f1ValueDigest(pairs) != f1ValueCorpusSHA {
		return nil, fmt.Errorf("F1ValueOps corpus size or digest mismatch")
	}
	names := [...]string{"neg", "abs", "sign", "iszero", "min", "max", "compare", "reduce"}
	checks := make([]f1ValueCheck, len(names))
	for i, name := range names {
		checks[i] = f1ValueCheck{name: name, got: make([]string, 256), want: make([]string, 256)}
	}
	for i, p := range pairs {
		x, err := f1ValueSplit(p.x)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d symbolic x: %w", i, err)
		}
		y, err := f1ValueSplit(p.y)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d symbolic y: %w", i, err)
		}
		cmp := f1ValueCompare(x, y)
		if !f1ValueShapeValid(i%8, x, y, cmp) {
			return nil, fmt.Errorf("F1ValueOps row %d shape mismatch", i)
		}
		xText, err := values[i].x.Text(0)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d x Text: %w", i, err)
		}
		yText, err := values[i].y.Text(0)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d y Text: %w", i, err)
		}
		if !f1ValueCohortMatches(x, xText) || !f1ValueCohortMatches(y, yText) {
			return nil, fmt.Errorf("F1ValueOps row %d input cohort mismatch", i)
		}

		neg := x
		if neg.sign != 0 {
			neg.sign = -neg.sign
		}
		checks[0].want[i], err = f1ValueCanonical(f1ValueRaw(neg))
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d Neg oracle: %w", i, err)
		}
		checks[0].got[i], err = values[i].x.Neg().Text(0)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d Neg Text: %w", i, err)
		}
		if actual, err := f1ValueSplit(checks[0].got[i]); err != nil || f1ValueCompare(actual, neg) != 0 {
			return nil, fmt.Errorf("F1ValueOps row %d Neg numeric mismatch", i)
		}

		abs := x
		if abs.sign < 0 {
			abs.sign = 1
		}
		checks[1].want[i], err = f1ValueCanonical(f1ValueRaw(abs))
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d Abs oracle: %w", i, err)
		}
		checks[1].got[i], err = values[i].x.Abs().Text(0)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d Abs Text: %w", i, err)
		}
		if actual, err := f1ValueSplit(checks[1].got[i]); err != nil || f1ValueCompare(actual, abs) != 0 {
			return nil, fmt.Errorf("F1ValueOps row %d Abs numeric mismatch", i)
		}

		checks[2].want[i], checks[2].got[i] = strconv.Itoa(x.sign), strconv.Itoa(values[i].x.Sign())
		checks[3].want[i], checks[3].got[i] = strconv.FormatBool(x.sign == 0), strconv.FormatBool(values[i].x.IsZero())

		minText := yText
		if f1ValueExpectedMinX(x, y, cmp) {
			minText = xText
		}
		checks[4].want[i] = minText
		checks[4].got[i], err = values[i].x.Min(values[i].y).Text(0)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d Min Text: %w", i, err)
		}
		maxText := yText
		if f1ValueExpectedMaxX(x, y, cmp) {
			maxText = xText
		}
		checks[5].want[i] = maxText
		checks[5].got[i], err = values[i].x.Max(values[i].y).Text(0)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d Max Text: %w", i, err)
		}
		checks[6].want[i], checks[6].got[i] = strconv.Itoa(cmp), strconv.Itoa(values[i].x.Compare(values[i].y))

		reducedRaw := f1ValueReducedRaw(x)
		checks[7].want[i], err = f1ValueCanonical(reducedRaw)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d Reduce oracle: %w", i, err)
		}
		checks[7].got[i], err = values[i].x.Reduce().Text(0)
		if err != nil {
			return nil, fmt.Errorf("F1ValueOps row %d Reduce Text: %w", i, err)
		}
		if actual, err := f1ValueSplit(checks[7].got[i]); err != nil || f1ValueCompare(actual, x) != 0 {
			return nil, fmt.Errorf("F1ValueOps row %d Reduce numeric mismatch", i)
		}
	}
	return checks, nil
}

func TestF1ValueOpsCorpusDigest(t *testing.T) {
	pairs := f1ValuePairs()
	if len(pairs) != 256 {
		t.Fatalf("F1ValueOps has %d ordered pairs, want 256", len(pairs))
	}
	const want = "8f8363d7b8d20d6da318564b63afd878c1f1918efcb27632b16ac16e6ce83963"
	if got := f1ValueDigest(pairs); got != want {
		t.Fatalf("F1ValueOps corpus SHA-256 = %s, want %s", got, want)
	}
	for _, tc := range []struct {
		row  int
		want f1ValuePair
	}{
		{0, f1ValuePair{"1.0", "1"}},
		{1, f1ValuePair{"-1.0", "-1"}},
		{2, f1ValuePair{"0.00", "0E+3"}},
		{3, f1ValuePair{"1E+2147483647", "1E+2147483646"}},
		{4, f1ValuePair{"-1E-2147483648", "-1E-2147483647"}},
		{8, f1ValuePair{"1", "1.0"}},
		{9, f1ValuePair{"-1", "-1.0"}},
		{10, f1ValuePair{"0E+2147483647", "0E-2147483648"}},
	} {
		if pairs[tc.row] != tc.want {
			t.Fatalf("anchor row %d changed", tc.row)
		}
	}
	if len(pairs[14].x) != 1001 || !strings.HasSuffix(pairs[14].y, "1") {
		t.Fatal("1,000-digit negative anchor changed")
	}
	for shape := range 8 {
		count := 0
		for i := shape; i < len(pairs); i += 8 {
			count++
		}
		if count != 32 {
			t.Fatalf("shape %d has %d pairs, want 32", shape, count)
		}
	}
}

func TestF1ValueOpsAccuracy(t *testing.T) {
	pairs := f1ValuePairs()
	values, err := f1ValueParse(pairs)
	if err != nil {
		t.Fatal(err)
	}
	checks, err := f1ValueAccuracy(pairs, values)
	if err != nil {
		t.Fatal(err)
	}
	if len(checks) != 8 {
		t.Fatalf("got %d accuracy vectors, want eight", len(checks))
	}
	wantNames := [...]string{"neg", "abs", "sign", "iszero", "min", "max", "compare", "reduce"}
	for i, check := range checks {
		if check.name != wantNames[i] {
			t.Fatalf("accuracy vector %d name %q, want %q", i, check.name, wantNames[i])
		}
		if len(check.got) != 256 || len(check.want) != 256 {
			t.Fatalf("%s checked %d/%d pairs, want 256/256", check.name, len(check.got), len(check.want))
		}
		requireMatchedAccuracy(t, "F1ValueOps/"+check.name, check.got, check.want)
	}
}

func TestF1ValueOpsShapeValidation(t *testing.T) {
	for _, tc := range []struct {
		shape int
		x, y  string
		want  bool
	}{
		{0, "1.0", "1", true},
		{0, "-1.0", "-1", false},
		{1, "-1.0", "-1", true},
		{2, "0.00", "0E+3", true},
		{3, "1234.50", "1234.51", true},
		{3, "1.0", "1", false},
		{5, "-1", "1", true},
		{5, "1", "2", false},
		{7, "1234567890123456789012345678901234567890", "12345678901234567890123456789012345678900E-1", true},
		{7, "1.0", "1", false},
	} {
		x, err := f1ValueSplit(tc.x)
		if err != nil {
			t.Fatal(err)
		}
		y, err := f1ValueSplit(tc.y)
		if err != nil {
			t.Fatal(err)
		}
		if got := f1ValueShapeValid(tc.shape, x, y, f1ValueCompare(x, y)); got != tc.want {
			t.Errorf("shape %d (%s, %s) = %t, want %t", tc.shape, tc.x, tc.y, got, tc.want)
		}
	}
}

const f1ValueSeed int64 = 20260918
const f1ValueCorpusSHA = "8f8363d7b8d20d6da318564b63afd878c1f1918efcb27632b16ac16e6ce83963"

func f1ValueDigits(r *rand.Rand, n int) string {
	var b strings.Builder
	b.Grow(n)
	b.WriteByte('1' + byte(r.Intn(9)))
	for i := 1; i < n; i++ {
		b.WriteByte('0' + byte(r.Intn(10)))
	}
	return b.String()
}

// f1ValuePairs is the fixed-seed corpus of value-operation pairs.
// The digest test makes any accidental change to this copy fail explicitly.
func f1ValuePairs() []f1ValuePair {
	long := strings.Repeat("1234567890", 100)
	forty := "1234567890123456789012345678901234567890"
	anchors := [8][2]f1ValuePair{
		{{"1.0", "1"}, {"1", "1.0"}},
		{{"-1.0", "-1"}, {"-1", "-1.0"}},
		{{"0.00", "0E+3"}, {"0E+2147483647", "0E-2147483648"}},
		{{"1E+2147483647", "1E+2147483646"}, {strings.Repeat("9", 38), "1" + strings.Repeat("0", 38)}},
		{{"-1E-2147483648", "-1E-2147483647"}, {"-" + strings.Repeat("9", 39), "-1" + strings.Repeat("0", 39)}},
		{{"-1", "1"}, {"1", "-1"}},
		{{forty, "1234567890123456789012345678901234567891"}, {"-" + long, "-" + long[:len(long)-1] + "1"}},
		{{forty, forty + "0E-1"}, {forty + "0E-1", forty}},
	}
	r := rand.New(rand.NewSource(f1ValueSeed))
	out := make([]f1ValuePair, 0, 256)
	for cycle := range 32 {
		for shape := range 8 {
			var p f1ValuePair
			if cycle < 2 {
				p = anchors[shape][cycle]
			} else {
				switch shape {
				case 0:
					a := f1ValueDigits(r, 6)
					p = f1ValuePair{a + "E-2", a + "0E-3"}
				case 1:
					a := f1ValueDigits(r, 19)
					p = f1ValuePair{"-" + a + "E-2", "-" + a + "0E-3"}
				case 2:
					p = f1ValuePair{"0E-" + strconv.Itoa(1+r.Intn(4)), "0E+" + strconv.Itoa(1+r.Intn(4))}
				case 3:
					a := 100000 + r.Intn(899999)
					p = f1ValuePair{strconv.Itoa(a) + "E-2", strconv.Itoa(a+1) + "E-2"}
				case 4:
					a := f1ValueDigits(r, 18)
					last := r.Intn(9)
					p = f1ValuePair{"-" + a + strconv.Itoa(last), "-" + a + strconv.Itoa(last+1)}
				case 5:
					a := f1ValueDigits(r, 19)
					p = f1ValuePair{"-" + a, a}
				case 6:
					a := f1ValueDigits(r, 39)
					last := r.Intn(9)
					p = f1ValuePair{a + strconv.Itoa(last), a + strconv.Itoa(last+1)}
					if cycle%2 != 0 {
						p.x, p.y = "-"+p.x, "-"+p.y
					}
				case 7:
					a := f1ValueDigits(r, 40)
					p = f1ValuePair{a, a + "0E-1"}
					if cycle%2 != 0 {
						p.x, p.y = "-"+p.x, "-"+p.y
					}
				}
				if cycle%2 != 0 {
					p.x, p.y = p.y, p.x
				}
			}
			out = append(out, p)
		}
	}
	return out
}

func f1ValueDigest(pairs []f1ValuePair) string {
	h := sha256.New()
	for _, p := range pairs {
		fmt.Fprintf(h, "%s\t%s\n", p.x, p.y)
	}
	return fmt.Sprintf("%x", h.Sum(nil))
}

type f1Symbolic struct {
	sign     int
	digits   string
	exponent int64
}

// f1ValueSplit is independent of Decimal's coefficient representation.
func f1ValueSplit(raw string) (f1Symbolic, error) {
	p := f1Symbolic{sign: 1}
	if strings.HasPrefix(raw, "-") {
		p.sign, raw = -1, raw[1:]
	}
	if i := strings.IndexAny(raw, "Ee"); i >= 0 {
		var err error
		p.exponent, err = strconv.ParseInt(raw[i+1:], 10, 64)
		if err != nil {
			return p, err
		}
		raw = raw[:i]
	}
	if i := strings.IndexByte(raw, '.'); i >= 0 {
		p.exponent -= int64(len(raw) - i - 1)
		raw = raw[:i] + raw[i+1:]
	}
	p.digits = strings.TrimLeft(raw, "0")
	if p.digits == "" {
		p.digits, p.sign = "0", 0
	}
	return p, nil
}

func f1ValueCompare(a, b f1Symbolic) int {
	if a.sign != b.sign {
		if a.sign < b.sign {
			return -1
		}
		return 1
	}
	if a.sign == 0 {
		return 0
	}
	ae, be := int64(len(a.digits)-1)+a.exponent, int64(len(b.digits)-1)+b.exponent
	cmp := 0
	if ae < be {
		cmp = -1
	} else if ae > be {
		cmp = 1
	} else {
		width := max(len(a.digits), len(b.digits))
		cmp = strings.Compare(a.digits+strings.Repeat("0", width-len(a.digits)), b.digits+strings.Repeat("0", width-len(b.digits)))
	}
	if a.sign < 0 {
		cmp = -cmp
	}
	return cmp
}

func f1ValueShapeValid(shape int, x, y f1Symbolic, cmp int) bool {
	switch shape {
	case 0:
		return x.sign == 1 && y.sign == 1 && cmp == 0 && x.exponent != y.exponent
	case 1:
		return x.sign == -1 && y.sign == -1 && cmp == 0 && x.exponent != y.exponent
	case 2:
		return x.sign == 0 && y.sign == 0 && cmp == 0 && x.exponent != y.exponent
	case 3:
		return x.sign == 1 && y.sign == 1 && cmp != 0
	case 4:
		return x.sign == -1 && y.sign == -1 && cmp != 0
	case 5:
		return x.sign*y.sign == -1 && cmp != 0
	case 6:
		return x.sign == y.sign && x.sign != 0 && cmp != 0 && len(x.digits) >= 40 && len(y.digits) >= 40
	case 7:
		return x.sign == y.sign && x.sign != 0 && cmp == 0 && x.exponent != y.exponent && len(x.digits) >= 40 && len(y.digits) >= 40
	default:
		return false
	}
}

func f1ValueRaw(p f1Symbolic) string {
	sign := ""
	if p.sign < 0 {
		sign = "-"
	}
	return sign + p.digits + "E" + strconv.FormatInt(p.exponent, 10)
}

func f1ValueReducedRaw(p f1Symbolic) string {
	if p.sign == 0 {
		return "0E0"
	}
	for len(p.digits) > 1 && p.digits[len(p.digits)-1] == '0' && p.exponent < 2147483647 {
		p.digits = p.digits[:len(p.digits)-1]
		p.exponent++
	}
	return f1ValueRaw(p)
}
