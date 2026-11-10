// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"context"
	"errors"
	"fmt"
	"hash/maphash"
	"math"
	"math/big"
	"math/bits"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"
)

// coefficientDigits is a test-only inspection of the stored unsigned
// coefficient, including trailing zeros. Production algorithms use their
// read-only limb cursor and never depend on this decimal string.
func (d Decimal) coefficientDigits() string {
	if d.slow != nil {
		limbs := d.slow.limbs
		out := strconv.AppendUint(nil, uint64(limbs[len(limbs)-1]), 10)
		for i := len(limbs) - 1; i > 0; i-- {
			var block [9]byte
			n := limbs[i-1]
			for j := 8; j >= 0; j-- {
				block[j] = byte(n%10) + '0'
				n /= 10
			}
			out = append(out, block[:]...)
		}
		return string(out)
	}
	if d.words.hi == 0 {
		return strconv.FormatUint(d.words.lo, 10)
	}
	var chunks [5]uint32
	n := 0
	hi, lo := d.words.hi, d.words.lo
	for hi != 0 || lo != 0 {
		qhi, rem := bits.Div64(0, hi, 1_000_000_000)
		qlo, digit := bits.Div64(rem, lo, 1_000_000_000)
		chunks[n] = uint32(digit)
		n++
		hi, lo = qhi, qlo
	}
	out := strconv.AppendUint(nil, uint64(chunks[n-1]), 10)
	for i := n - 1; i > 0; i-- {
		var block [9]byte
		v := chunks[i-1]
		for j := 8; j >= 0; j-- {
			block[j] = byte(v%10) + '0'
			v /= 10
		}
		out = append(out, block[:]...)
	}
	return string(out)
}

func TestNewPreservesCohortAndUnsignedZero(t *testing.T) {
	cases := []struct {
		name     string
		input    int64
		exponent int32
		digits   string
		negative bool
	}{
		{"zero at negative scale", 0, -2, "0", false},
		{"zero at positive exponent", 0, 9, "0", false},
		{"one", 1, 0, "1", false},
		{"negative", -12, -3, "12", true},
		{"min int64", math.MinInt64, math.MaxInt32, "9223372036854775808", true},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := New(tc.input, tc.exponent)
			if got.exponent() != tc.exponent || got.negative() != tc.negative || got.coefficientDigits() != tc.digits || got.slow != nil {
				t.Fatalf("New(%d,%d) = %+v digits %q", tc.input, tc.exponent, got, got.coefficientDigits())
			}
		})
	}
	zero := Zero()
	if !zero.isZero() || zero.exponent() != 0 || zero.negative() || zero.slow != nil {
		t.Fatalf("Zero = %+v", zero)
	}
	one := One()
	if one.coefficientDigits() != "1" || one.exponent() != 0 || one.negative() {
		t.Fatalf("One = %+v", one)
	}
}

func TestInlineCoefficientDigitsAgainstBigInt(t *testing.T) {
	values := []uint128{{0, 0}, {math.MaxUint64, 0}, {0, 1}, {math.MaxUint64, math.MaxUint64}}
	for _, words := range values {
		d := inlineDecimal(words, 0, false)
		want := new(big.Int).SetUint64(words.hi)
		want.Lsh(want, 64)
		want.Add(want, new(big.Int).SetUint64(words.lo))
		if got := d.coefficientDigits(); got != want.String() {
			t.Fatalf("words %v: got %s, want %s", words, got, want)
		}
	}
}

func TestParseAcceptedLiberalForms(t *testing.T) {
	for _, tc := range []struct{ input, canonical string }{
		{"+5", "5"},
		{".5", "0.5"},
		{"5.", "5"},
		{"007", "7"},
		{"007.0100", "7.0100"},
		{"2.5e-3", "0.0025"},
		{"1E+2", "1E+2"},
		{"-.7", "-0.7"},
	} {
		got, err := Parse(tc.input)
		if err != nil {
			t.Fatalf("Parse(%q): %v", tc.input, err)
		}
		text, err := got.Text(0)
		if err != nil || text != tc.canonical {
			t.Fatalf("Parse(%q).Text(0) = %q, %v; want %q", tc.input, text, err, tc.canonical)
		}
	}
}

func TestParsedNegativeZeroEmitsUnsigned(t *testing.T) {
	for _, tc := range []struct{ input, canonical string }{
		{"-0", "0"}, {"-0.00", "0.00"}, {"-0E+9", "0E+9"},
	} {
		got, err := Parse(tc.input)
		if err != nil {
			t.Fatalf("Parse(%q): %v", tc.input, err)
		}
		text, err := got.Text(0)
		if err != nil || text != tc.canonical || got.negative() {
			t.Fatalf("Parse(%q) = %q, negative %v, error %v; want %q unsigned", tc.input, text, got.negative(), err, tc.canonical)
		}
	}
}

func TestParseAndParseWithZeroBudgetEquivalent(t *testing.T) {
	inputs := []string{"", "1.2300", "+5", "-0.00", "1E+2147483648", "NaN", "1e999999999", "1234567890123456789012345678901234567890"}
	for _, input := range inputs {
		plain, plainErr := Parse(input)
		budgeted, _, budgetErr := ParseWithContext(input, Context{})
		if (plainErr == nil) != (budgetErr == nil) {
			t.Fatalf("%q: Parse error %v, zero-budget error %v", input, plainErr, budgetErr)
		}
		if plainErr != nil {
			var left, right *Error
			if !errors.As(plainErr, &left) || !errors.As(budgetErr, &right) || left.Condition != right.Condition || left.Input != right.Input || left.Op != "Parse" || right.Op != "ParseWithContext" {
				t.Fatalf("%q: mismatched Error pair: %v / %v", input, plainErr, budgetErr)
			}
			for _, code := range []ErrorCode{ErrConversionSyntax, ErrExponentRange, ErrInsufficientStorage} {
				if errors.Is(plainErr, code) != errors.Is(budgetErr, code) {
					t.Fatalf("%q: error code %v differs", input, code)
				}
			}
			continue
		}
		if plain.negative() != budgeted.negative() || plain.exponent() != budgeted.exponent() || plain.coefficientDigits() != budgeted.coefficientDigits() {
			t.Fatalf("%q: zero budget changed the constructed cohort", input)
		}
	}
}

func TestCanonicalRoundTripCohortProperty(t *testing.T) {
	rng := rand.New(rand.NewSource(20260923))
	values := []Decimal{Zero(), New(0, -20), New(0, 20), MustParse("1.2300"), MustParse("1234567890123456789012345678901234567890.00")}
	for range 500 {
		coefficient := rng.Int63n(1_000_000_000_000)
		if rng.Intn(2) == 0 {
			coefficient = -coefficient
		}
		values = append(values, New(coefficient, int32(rng.Intn(41)-20)))
	}
	for _, original := range values {
		text, err := original.Text(0)
		if err != nil {
			t.Fatalf("Text(%+v): %v", original, err)
		}
		parsed, err := Parse(text)
		if err != nil {
			t.Fatalf("Parse(Text(%+v)=%q): %v", original, text, err)
		}
		again, err := parsed.Text(0)
		if err != nil || again != text || parsed.negative() != original.negative() || parsed.exponent() != original.exponent() || parsed.coefficientDigits() != original.coefficientDigits() {
			t.Fatalf("round-trip changed cohort: %q -> %q; before %+v, after %+v, error %v", text, again, original, parsed, err)
		}
	}
}

func TestSortFuncCompareNumericOrder(t *testing.T) {
	values := []Decimal{MustParse("1.00"), MustParse("-1.5"), MustParse("2"), MustParse("0.00"), MustParse("-2.0")}
	slices.SortFunc(values, Decimal.Compare)
	want := []string{"-2.0", "-1.5", "0.00", "1.00", "2"}
	for i, value := range values {
		if text := value.String(); text != want[i] {
			t.Fatalf("sorted value %d = %q, want %q", i, text, want[i])
		}
	}
}

var parsedExponentSink Decimal

func TestParseLargeValidExponentBounded(t *testing.T) {
	short := "1e999999999"
	deep := "1e+" + strings.Repeat("0", 4096) + "999999999"
	for _, input := range []string{short, deep} {
		value, err := Parse(input)
		if err != nil || value.exponent() != 999999999 || value.coefficientDigits() != "1" {
			t.Fatalf("Parse(%q): value %+v, error %v", input[:min(len(input), 24)], value, err)
		}
		if got := value.String(); got != "1E+999999999" {
			t.Fatalf("large exponent text %q", got)
		}
	}
	allocs := func(input string) float64 {
		return testing.AllocsPerRun(20, func() {
			var err error
			parsedExponentSink, err = Parse(input)
			if err != nil {
				t.Fatal(err)
			}
		})
	}
	shortAllocs, deepAllocs := allocs(short), allocs(deep)
	if deepAllocs > shortAllocs {
		t.Fatalf("deep exponent added allocation growth: short %.1f, deep %.1f", shortAllocs, deepAllocs)
	}
}

func TestParseLexicalExponentBeyondInt32CanonicalText(t *testing.T) {
	value, err := Parse("1.2E+2147483648")
	if err != nil || value.coefficientDigits() != "12" || value.exponent() != math.MaxInt32 {
		t.Fatalf("adjusted exponent: value %+v, error %v", value, err)
	}
	if text := value.String(); text != "1.2E+2147483648" {
		t.Fatalf("adjusted exponent text = %q", text)
	}
	if _, err := Parse("1e2147483648"); !errors.Is(err, ErrExponentRange) {
		t.Fatalf("out-of-domain exponent = %v", err)
	}
}

func TestParseFullInt32ExponentDomain(t *testing.T) {
	for _, tc := range []struct {
		literal  string
		exponent int32
	}{
		{"1E+2147483647", math.MaxInt32},
		{"1E-2147483648", math.MinInt32},
		{"1E+1000000000", 1_000_000_000},
		{"1E-999999999", -999_999_999},
	} {
		value, err := Parse(tc.literal)
		if err != nil || value.exponent() != tc.exponent || value.coefficientDigits() != "1" || value.String() != tc.literal {
			t.Fatalf("Parse(%q): value %+v, error %v", tc.literal, value, err)
		}
	}
}

func TestComparisonMethodSet(t *testing.T) {
	// Reflect an actual value: TypeFor[Decimal] triggers Go 1.27.1 linker crashes for a comparable variant of the type.
	var value Decimal
	typ := reflect.TypeOf(value)
	method, ok := typ.MethodByName("Compare")
	if !ok || method.Type.NumIn() != 2 || method.Type.In(1) != typ || method.Type.NumOut() != 1 || method.Type.Out(0) != reflect.TypeFor[int]() {
		t.Fatalf("Compare method shape = %v, present %v", method.Type, ok)
	}
	if _, ok := typ.MethodByName("Cmp"); ok {
		t.Fatal("unexpected Cmp alias is exported")
	}
}

func TestSharedDecimalConcurrentUse(t *testing.T) {
	const literal = "1234567890123456789012345678901234567890.00"
	const cohort = "1234567890123456789012345678901234567890.000"
	const wantReduced = "1.23456789012345678901234567890123456789E+39"
	shared := MustParse(literal) // slow backing storage is shared by shallow copies
	if shared.slow == nil {
		t.Fatal("test value did not enter the slow coefficient band")
	}
	seed := maphash.MakeSeed()
	var baseline maphash.Hash
	baseline.SetSeed(seed)
	(Hasher{}).Hash(&baseline, shared)
	wantHash := baseline.Sum64()
	const workers, iterations = 8, 300
	start := make(chan struct{})
	var wg sync.WaitGroup
	for worker := range workers {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			<-start
			for j := range iterations {
				// Other values are constructed while every goroutine reads the
				// same slow coefficient and its shallow copies.
				fresh, err := Parse(cohort)
				if err != nil {
					t.Errorf("worker %d iteration %d: Parse: %v", worker, j, err)
					return
				}
				copyOfShared := shared
				text, err := copyOfShared.Text(0)
				if err != nil || text != literal || copyOfShared.String() != literal {
					t.Errorf("worker %d iteration %d: shared text %q, error %v", worker, j, text, err)
					return
				}
				if !copyOfShared.Equal(fresh) || copyOfShared.Compare(fresh) != 0 || copyOfShared.Reduce().String() != wantReduced {
					t.Errorf("worker %d iteration %d: shared numeric relation/reduction changed", worker, j)
					return
				}
				var h maphash.Hash
				h.SetSeed(seed)
				(Hasher{}).Hash(&h, copyOfShared)
				if h.Sum64() != wantHash {
					t.Errorf("worker %d iteration %d: shared hash changed", worker, j)
					return
				}
			}
		}(worker)
	}
	close(start)
	wg.Wait()
	if got := shared.String(); got != literal {
		t.Fatalf("shared value changed after concurrent reads: %q", got)
	}
}

// TestPublishersCanonicalAndUnaliased pins the publishers: trailing
// zero limbs are trimmed; zero and every value below 2^128 publish inline
// (canonical band); a scratch coefficient of at most slowSmallLimbs limbs
// lives in its holder's own array and a longer one in an exact copy, and
// neither retains the caller's scratch; an owned slice is kept as is.
func TestPublishersCanonicalAndUnaliased(t *testing.T) {
	limbsOf := func(n *big.Int) []uint32 {
		var out []uint32
		base := big.NewInt(1_000_000_000)
		for n = new(big.Int).Set(n); n.Sign() != 0; {
			var r big.Int
			n.QuoRem(n, base, &r)
			out = append(out, uint32(r.Uint64()))
		}
		return out
	}
	two128 := new(big.Int).Lsh(big.NewInt(1), 128)
	r := rand.New(rand.NewSource(52))
	for _, n := range []*big.Int{
		big.NewInt(0), big.NewInt(1), new(big.Int).Sub(two128, big.NewInt(1)), two128,
		new(big.Int).Exp(big.NewInt(10), big.NewInt(80), nil),
		new(big.Int).Sub(new(big.Int).Exp(big.NewInt(10), big.NewInt(81), nil), big.NewInt(1)),
		new(big.Int).Exp(big.NewInt(10), big.NewInt(81), nil),
		new(big.Int).Rand(r, new(big.Int).Exp(big.NewInt(10), big.NewInt(300), nil)),
	} {
		want := n.String()
		limbs := limbsOf(n)
		for publisher, publish := range map[string]func([]uint32) Decimal{
			"scratch": func(l []uint32) Decimal { return publishScratch(l, -3, true) },
			"owned":   func(l []uint32) Decimal { return publishOwned(l, -3, true) },
		} {
			scratch := append(slices.Clone(limbs), 0, 0) // untrimmed
			d := publish(scratch)
			if got := d.coefficientDigits(); got != want || d.exponent() != -3 || d.negative() != (n.Sign() != 0) {
				t.Fatalf("%s %s: %s E%d negative=%t", publisher, want, got, d.exponent(), d.negative())
			}
			if inline := n.Cmp(two128) < 0; inline != (d.slow == nil) {
				t.Fatalf("%s %s: slow=%t, want inline=%t", publisher, want, d.slow != nil, inline)
			}
			if d.slow == nil {
				continue
			}
			if len(d.slow.limbs) != len(limbs) {
				t.Fatalf("%s %s: %d limbs, want %d trimmed", publisher, want, len(d.slow.limbs), len(limbs))
			}
			fused := &d.slow.limbs[0] == &d.slow.small[0]
			if publisher == "scratch" {
				if fused != (len(limbs) <= slowSmallLimbs) {
					t.Fatalf("scratch %s: fused=%t for %d limbs", want, fused, len(limbs))
				}
				clear(scratch)
				if d.coefficientDigits() != want {
					t.Fatalf("scratch %s: the holder aliases the caller's scratch", want)
				}
			} else if &d.slow.limbs[0] != &scratch[0] {
				t.Fatalf("owned %s: the holder copied an owned slice", want)
			}
		}
	}
}

// TestBandInvisibleObservers checks equal values across bands:
// the same coefficient and exponent presented inline and through a slow
// holder give identical text, accessors, Equal, Compare, hash, arithmetic
// results and emitted conditions, over random values across 0..2^128.
func TestBandInvisibleObservers(t *testing.T) {
	seed := maphash.MakeSeed()
	ctx := Decimal64Context()
	observe := func(d, other Decimal) string {
		var b strings.Builder
		w := func(v ...any) { b.WriteString(fmt.Sprintln(v...)) }
		text, err := d.Text(0)
		w(d.String(), text, err, d.Exponent(), d.Sign(), d.IsZero(), d.CoefficientDigits())
		w(d.CoefficientInt128())
		w(d.Float64())
		w(d.Int64())
		w(d.Reduce().String(), d.Abs().String(), d.Neg().String())
		w(d.Scientific(0))
		w(d.Engineering())
		w(d.Equal(other), d.Compare(other), other.Compare(d))
		var h maphash.Hash
		h.SetSeed(seed)
		(Hasher{}).Hash(&h, d)
		w(h.Sum64())
		sum, err := d.Add(other)
		w(sum.String(), err)
		product, err := d.Mul(other)
		w(product.String(), err)
		rounded, conditions, err := d.AddWithContext(other, ctx)
		w(rounded.String(), conditions, err)
		rounded, conditions, err = d.MulWithContext(other, ctx)
		w(rounded.String(), conditions, err)
		rounded, conditions, err = d.Quantize(d.exponent()+3, TiesToEven)
		w(rounded.String(), conditions, err)
		if !other.IsZero() {
			rounded, conditions, err = d.DivToExponent(other, d.exponent(), TiesToEven)
			w(rounded.String(), conditions, err)
			rounded, conditions, err = d.DivWithContext(other, ctx)
			w(rounded.String(), conditions, err)
		}
		return b.String()
	}
	r := rand.New(rand.NewSource(1))
	checked := 0
	for range 3000 {
		a, b := inlineSample(r, 0), inlineSample(r, 0)
		if a.IsZero() || b.IsZero() {
			continue
		}
		want := observe(a, b)
		for name, got := range map[string]string{
			"slow receiver": observe(asSlowBand(a), b),
			"slow operand":  observe(a, asSlowBand(b)),
			"both slow":     observe(asSlowBand(a), asSlowBand(b)),
		} {
			if got != want {
				t.Fatalf("%s diverges for %v, %v:\ninline:\n%s\nslow:\n%s", name, a, b, want, got)
			}
		}
		checked++
	}
	if checked < 2500 {
		t.Fatalf("only %d nonzero pairs checked", checked)
	}
}

// TestNoInlineWidthWall checks that there is no width wall: chains of Add, Sub,
// Mul and exact Quantize whose coefficients cross 2^128 in both directions
// stay exact against math/big, raise no condition, and every result is
// published in the canonical band for its magnitude.
func TestNoInlineWidthWall(t *testing.T) {
	two128 := new(big.Int).Lsh(big.NewInt(1), 128)
	r := rand.New(rand.NewSource(128))
	digits := func() string {
		n := 1 + r.Intn(60)
		b := make([]byte, n)
		for i := range b {
			b[i] = byte('0' + r.Intn(10))
		}
		b[0] = byte('1' + r.Intn(9))
		return string(b)
	}
	check := func(step string, d Decimal, want *big.Rat) {
		t.Helper()
		if decimalRat(t, d).Cmp(want) != 0 {
			t.Fatalf("%s: %v, math/big %s", step, d, want.RatString())
		}
		coefficient, _ := new(big.Int).SetString(d.coefficientDigits(), 10)
		if inline := coefficient.Cmp(two128) < 0; inline != (d.slow == nil) {
			t.Fatalf("%s: %v stored slow=%t below 2^128=%t", step, d, d.slow != nil, inline)
		}
	}
	crossings := 0
	for range 2000 {
		x, y := MustParse(digits()+"E-"+strconv.Itoa(r.Intn(10))), MustParse(digits())
		xr, yr := decimalRat(t, x), decimalRat(t, y)
		sum, err := x.Add(y)
		if err != nil {
			t.Fatal(err)
		}
		check("Add", sum, new(big.Rat).Add(xr, yr))
		difference, err := sum.Sub(y)
		if err != nil {
			t.Fatal(err)
		}
		check("Sub back", difference, xr)
		product, err := x.Mul(y)
		if err != nil {
			t.Fatal(err)
		}
		check("Mul", product, new(big.Rat).Mul(xr, yr))
		widened, conditions, err := product.Quantize(product.exponent()-int32(r.Intn(40)), TiesToEven)
		if err != nil || conditions != 0 {
			t.Fatalf("exact Quantize of %v: %v, %v", product, conditions, err)
		}
		check("Quantize", widened, new(big.Rat).Mul(xr, yr))
		if (x.slow == nil) != (product.slow == nil) || (sum.slow == nil) != (difference.slow == nil) {
			crossings++
		}
	}
	if crossings < 500 {
		t.Fatalf("only %d chains crossed the inline width", crossings)
	}
}

// TestCohortStatesSurviveConstructionAndBands checks cohort
// preservation: "1.4700" parses to coefficient 14700 at
// exponent -4 with scale 4 visible through accessors and text; 1.0 and 1.00
// stay distinguishable states (exponent, digit count, text) while Equal;
// and a cohort crossing the internal inline/slow boundary, through
// arithmetic that passes the slow band, a forced slow copy, a coefficient
// interchange and JSON, keeps its coefficient and exponent. Expected
// states are hand-derived.
func TestCohortStatesSurviveConstructionAndBands(t *testing.T) {
	x := MustParse("1.4700")
	if hi, lo, ok := x.CoefficientInt128(); !ok || hi != 0 || lo != 14700 || x.Exponent() != -4 || x.CoefficientDigits() != 5 || x.String() != "1.4700" {
		t.Fatalf("1.4700 = (%d,%d,%v) e%d digits %d text %s; want 14700 e-4, 5 digits", hi, lo, ok, x.Exponent(), x.CoefficientDigits(), x)
	}
	one1, one2 := MustParse("1.0"), MustParse("1.00")
	if !one1.Equal(one2) || one1.Exponent() != -1 || one2.Exponent() != -2 || one1.CoefficientDigits() != 2 ||
		one2.CoefficientDigits() != 3 || one1.String() != "1.0" || one2.String() != "1.00" {
		t.Fatalf("1.0/1.00 collapsed: %s e%d, %s e%d", one1, one1.Exponent(), one2, one2.Exponent())
	}
	big40 := MustParse("1" + strings.Repeat("0", 40))
	must := func(d Decimal, err error) Decimal {
		t.Helper()
		if err != nil {
			t.Fatal(err)
		}
		return d
	}
	var decoded Decimal
	if err := decoded.UnmarshalJSON([]byte(`"1.4700"`)); err != nil {
		t.Fatal(err)
	}
	crossed := map[string]Decimal{
		"(x+B)-B":         must(must(x.Add(big40)).Sub(big40)),
		"x*B/B":           must(must(x.Mul(big40)).Div(big40)),
		"slow copy":       forceSlowBandForTest(t, x),
		"Int128 lane":     NewInt128(0, 14700, -4),
		"JSON":            decoded,
		"shallow copy":    x,
		"Neg().Neg()":     x.Neg().Neg(),
		"Max(1.46)":       x.Max(MustParse("1.46")),
		"Quantize(-4)":    func() Decimal { q, _, err := x.Quantize(-4, Exact); return must(q, err) }(),
		"Parse(String())": must(Parse(x.String())),
		"sum through B":   must(Sum(x, big40, big40.Neg())),
	}
	if must(x.Add(big40)).slow == nil {
		t.Fatal("x+B did not enter the slow band")
	}
	for path, d := range crossed {
		if d.String() != "1.4700" || d.Exponent() != -4 || d.CoefficientDigits() != 5 || d.coefficientDigits() != "14700" {
			t.Errorf("%s: cohort %s e%d (%s); want 14700 e-4", path, d, d.Exponent(), d.coefficientDigits())
		}
	}
}

// TestDecimalLayoutIsRegisterAssignable pins the value layout: on
// 64-bit targets Decimal satisfies Go's ssa.CanSSA shape (at most four
// fields at every struct level, no array of more than one element, 32
// bytes) and needs at most four integer registers, so two operands fit
// amd64's nine argument registers. It stays non-comparable.
func TestDecimalLayoutIsRegisterAssignable(t *testing.T) {
	// Reflect an actual value: TypeFor[Decimal] triggers Go 1.27.1 linker crashes for a comparable variant of the type.
	var value Decimal
	typ := reflect.TypeOf(value)
	wantSize := uintptr(32)
	if bits.UintSize == 32 {
		wantSize = 28
	}
	if typ.Size() != wantSize {
		t.Errorf("Decimal is %d bytes, want %d", typ.Size(), wantSize)
	}
	if typ.Comparable() {
		t.Error("Decimal is comparable; == and map keys must be refused")
	}
	if bits.UintSize != 64 {
		return // Size/noncomparability apply on 386; register shape is 64-bit.
	}
	registers := 0
	var walk func(path string, t reflect.Type)
	walk = func(path string, ty reflect.Type) {
		switch ty.Kind() {
		case reflect.Struct:
			if ty.NumField() > 4 {
				t.Errorf("%s has %d fields, ssa.CanSSA allows at most 4", path, ty.NumField())
			}
			for f := range ty.Fields() {
				walk(path+"."+f.Name, f.Type)
			}
		case reflect.Array:
			if ty.Len() > 1 {
				t.Errorf("%s is %s, ssa.CanSSA and the register ABI refuse arrays longer than one", path, ty)
			}
			if ty.Len() == 1 {
				walk(path+"[0]", ty.Elem())
			}
		case reflect.Func:
			// only as the element of the zero-length marker array: no register
		default:
			registers++
		}
	}
	walk("Decimal", typ)
	if registers > 4 {
		t.Errorf("Decimal needs %d integer registers; two operands exceed amd64's nine", registers)
	}
}

// TestDecimalCrossesCallsInRegisters checks the value layout with the
// compiler itself: an external consumer's functions are compiled with -S for
// amd64 and arm64. Pick (a two-way select) must use neither a stack slot nor
// stack-assigned results (args=0x48 is the spill space of bool+2×32 bytes,
// locals=0x0), and Second must never load its second Decimal from the stack,
// which happens when two values need more than nine integer registers.
func TestDecimalCrossesCallsInRegisters(t *testing.T) {
	if runtime.GOOS == "js" || runtime.GOARCH == "wasm" {
		t.Skip("the compiler subprocess runs on native targets")
	}
	if _, err := exec.LookPath("go"); err != nil {
		t.Fatalf("compiler prerequisite go command unavailable: %v", err)
	}
	root, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	mod := "module decimalregisters\n\ngo 1.27\n\nrequire github.com/0xCarbon/decimal v0.0.0\nreplace github.com/0xCarbon/decimal => " + strconv.Quote(filepath.ToSlash(root)) + "\n"
	src := "package p\n\nimport d \"github.com/0xCarbon/decimal\"\n\n" +
		"func Pick(c bool, x, y d.Decimal) d.Decimal {\n\tif c {\n\t\treturn x\n\t}\n\treturn y\n}\n\n" +
		"func Second(x, y d.Decimal) d.Decimal { return y }\n"
	for name, body := range map[string]string{"go.mod": mod, "p.go": src} {
		if err := os.WriteFile(filepath.Join(dir, name), []byte(body), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	stackLoad := regexp.MustCompile(`\tMOV\w*\s+decimalregisters\.y\+\d+\((SP|FP)\),`)
	for _, profile := range []string{"simd", ""} {
		for _, arch := range []string{"amd64", "arm64"} {
			t.Run(arch+"/"+profile, func(t *testing.T) {
				ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
				defer cancel()
				cmd := exec.CommandContext(ctx, "go", "build", "-mod=mod", "-gcflags=decimalregisters=-S", "-o", os.DevNull, ".")
				cmd.Dir = dir
				cmd.Env = append(os.Environ(), "CGO_ENABLED=0", "GOOS=linux", "GOARCH="+arch, "GOEXPERIMENT="+profile, "GOWORK=off")
				out, err := cmd.CombinedOutput()
				if err != nil {
					t.Fatalf("consumer build failed: %v\n%s", err, out)
				}
				var pick string
				var second []string
				inSecond := false
				for line := range strings.Lines(string(out)) {
					fields := strings.Fields(line)
					if len(fields) > 1 && fields[1] == "STEXT" {
						inSecond = fields[0] == "decimalregisters.Second"
						if fields[0] == "decimalregisters.Pick" {
							pick = line
						}
						continue
					}
					if inSecond {
						second = append(second, line)
					}
				}
				if !strings.Contains(pick, " args=0x48 locals=0x0 ") {
					t.Errorf("Pick is not register-passed and SSA-assigned: %q", pick)
				}
				if len(second) == 0 {
					t.Fatalf("no assembly for Second in:\n%s", out)
				}
				for _, line := range second {
					if stackLoad.MatchString(line) {
						t.Errorf("Second loads its second operand from the stack: %s", strings.TrimSpace(line))
					}
				}
			})
		}
	}
}

// ValidRepresentationForTest exposes the representation invariant to the
// external public-API fuzz suite. It exists only in the test build.
func ValidRepresentationForTest(d Decimal) bool { return d.validRepresentation() }

// TestDecimalPackedMetadataPreservesFullExponentSign pins metadata packing
// against hand-derived full-int32 exponent and sign vectors, for both storage
// bands and zero. Every constructor and pure update must preserve the cohort,
// unsigned zero, reserved bits and immutable input.
func TestDecimalPackedMetadataPreservesFullExponentSign(t *testing.T) {
	for _, e := range []int32{math.MinInt32, math.MinInt32 + 1, -123456789, -1, 0, 1, math.MaxInt32 - 1, math.MaxInt32} {
		for _, coefficient := range []string{"0", "1", "18446744073709551616", "340282366920938463463374607431768211455", "340282366920938463463374607431768211456", "99999999999999999999999999999999999999999999999999999999999999999999999999999999999999"} {
			for _, negative := range []bool{false, true} {
				text := coefficient + "E" + strconv.FormatInt(int64(e), 10)
				if negative {
					text = "-" + text
				}
				d := MustParse(text)
				wantSign := negative && coefficient != "0"
				if !d.validRepresentation() || d.exponent() != e || d.negative() != wantSign || d.coefficientDigits() != coefficient {
					t.Fatalf("Parse(%q) has invalid representation: %#v", text, d)
				}
				original := d
				for _, update := range []struct {
					name         string
					value        Decimal
					wantNegative bool
				}{
					{"withExponent", d.withExponent(e), negative && coefficient != "0"},
					{"withNegative(input)", d.withNegative(negative), negative && coefficient != "0"},
					{"withNegative(false)", d.withNegative(false), false},
					{"withNegative(true)", d.withNegative(true), coefficient != "0"},
					{"negated", d.negated(), !negative && coefficient != "0"},
					{"Neg", d.Neg(), !negative && coefficient != "0"},
					{"Abs", d.Abs(), false},
					{"update chain", d.withExponent(-1).withNegative(false).withExponent(e).withNegative(negative), negative && coefficient != "0"},
				} {
					updated := update.value
					if !updated.validRepresentation() || updated.exponent() != e || updated.negative() != update.wantNegative || updated.coefficientDigits() != coefficient {
						t.Fatalf("%s(%q) has invalid representation or sign (want negative=%v): %#v", update.name, text, update.wantNegative, updated)
					}
				}
				if !reflect.DeepEqual(d, original) {
					t.Fatal("value update mutated its input")
				}
				if got := New(-1, e); !got.validRepresentation() || got.exponent() != e || !got.negative() {
					t.Fatalf("New(-1,%d) = %#v", e, got)
				}
				if got := inlineDecimal(uint128{}, e, true); !got.validRepresentation() || got.negative() || got.exponent() != e {
					t.Fatalf("signed zero not canonical: %#v", got)
				}
			}
		}
	}
}

// TestDecimalRepresentationRejectsInvalidBands checks the representation
// validity predicate against independently derived base-10^9 threshold limbs.
// These deliberately invalid carriers are test fixtures, never published values.
func TestDecimalRepresentationRejectsInvalidBands(t *testing.T) {
	for _, d := range []Decimal{
		{words: uint128{lo: 1}, slow: &slowCoefficient{limbs: []uint32{768211456, 374607431, 938463463, 282366920, 340}}},
		{slow: &slowCoefficient{limbs: []uint32{768211455, 374607431, 938463463, 282366920, 340}}},
		{slow: &slowCoefficient{limbs: []uint32{1}}},
		{slow: &slowCoefficient{}},
		{slow: &slowCoefficient{limbs: []uint32{0, 0, 0, 0, 0, 0}}},
		{slow: &slowCoefficient{limbs: []uint32{1000000000, 0, 0, 0, 340}}},
	} {
		if d.validRepresentation() {
			t.Fatalf("accepted invalid carrier: %#v", d)
		}
	}
	for _, d := range []Decimal{Zero(), slowDecimal(&slowCoefficient{limbs: []uint32{768211456, 374607431, 938463463, 282366920, 340}}, -1, true), slowDecimal(&slowCoefficient{limbs: []uint32{0, 0, 0, 0, 0, 1}}, math.MinInt32, false)} {
		if !d.validRepresentation() {
			t.Fatalf("refused valid carrier: %#v", d)
		}
	}
}

// validRepresentation checks the packed metadata and exact storage
// band without reconstructing a coefficient or allocating. The threshold
// is 2^128 expressed in little-endian base-10^9 limbs.
func (d Decimal) validRepresentation() bool {
	if d.meta&^(decimalSignBit|signExponent(1<<32-1)) != 0 {
		return false
	}
	if d.slow == nil {
		return !d.isZero() || !d.negative()
	}
	if d.words.lo|d.words.hi != 0 {
		return false
	}
	limbs := d.slow.limbs
	if len(limbs) < 5 || limbs[len(limbs)-1] == 0 {
		return false
	}
	for _, limb := range limbs {
		if uint64(limb) >= decimalLimbBase {
			return false
		}
	}
	if len(limbs) > 5 {
		return true
	}
	threshold := [...]uint32{768211456, 374607431, 938463463, 282366920, 340}
	for i := 4; i >= 0; i-- {
		if limbs[i] != threshold[i] {
			return limbs[i] > threshold[i]
		}
	}
	return true
}

// requireSameOutcome fails unless two calls agree on the result's
// representation, the conditions and the error's identity, operation and
// input. Differential tests use it to pin a fast path to its general path.
func requireSameOutcome(t *testing.T, what, input string, got Decimal, gc Conditions, gerr error, want Decimal, wc Conditions, werr error) {
	t.Helper()
	if (gerr == nil) != (werr == nil) || gerr != nil && gerr.Error() != werr.Error() {
		t.Fatalf("%s(%q): error %v, general %v", what, input, gerr, werr)
	}
	if gerr != nil {
		var ge, we *Error
		if !errors.As(gerr, &ge) || !errors.As(werr, &we) || ge.Code != we.Code || ge.Condition != we.Condition || ge.Input != we.Input || ge.Op != we.Op {
			t.Fatalf("%s(%q): error %#v, general %#v", what, input, gerr, werr)
		}
	}
	if gc != wc || got.meta != want.meta || got.words != want.words || (got.slow == nil) != (want.slow == nil) || got.Compare(want) != 0 || !got.validRepresentation() {
		t.Fatalf("%s(%q): %v %v (meta %x), general %v %v (meta %x)", what, input, got, gc, got.meta, want, wc, want.meta)
	}
}
