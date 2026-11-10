// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"os"
	"reflect"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"
)

func TestTextCanonicalVectors(t *testing.T) {
	tests := []struct {
		name  string
		value Decimal
		want  string
	}{
		{"zero", Zero(), "0"},
		{"zero scale two", New(0, -2), "0.00"},
		{"zero exponent positive", New(0, 2), "0E+2"},
		{"unsigned negative zero", New(0, -3), "0.000"},
		{"one", One(), "1"},
		{"plain decimal", New(12345, -2), "123.45"},
		{"trailing zeros", New(50, -7), "0.0000050"},
		{"plain boundary", New(1, -6), "0.000001"},
		{"scientific boundary", New(1, -7), "1E-7"},
		{"positive exponent", New(12345, 6), "1.2345E+10"},
		{"negative", New(-12345, -2), "-123.45"},
		{"constructed cohort", New(12300, -4), "1.2300"},
		{"max exponent", New(1, math.MaxInt32), "1E+2147483647"},
		{"min exponent", New(1, math.MinInt32), "1E-2147483648"},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got, err := tc.value.Text(0)
			if err != nil {
				t.Fatalf("Text(0): %v", err)
			}
			if got != tc.want {
				t.Fatalf("Text(0) = %q, want %q", got, tc.want)
			}
			if got := tc.value.String(); got != tc.want {
				t.Fatalf("String() = %q, want %q", got, tc.want)
			}
			if !json.Valid([]byte(got)) {
				t.Fatalf("canonical text %q is not a JSON number", got)
			}
		})
	}
}

func TestTextBudget(t *testing.T) {
	v := New(-12345, -2)
	if got, err := v.Text(7); err != nil || got != "-123.45" {
		t.Fatalf("Text(7) = %q, %v", got, err)
	}
	if got, err := v.Text(6); got != "" || !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("Text(6) = %q, %v; want checked resource refusal", got, err)
	}
	if got, err := New(1, math.MaxInt32).Text(12); got != "" || !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("large exponent output budget = %q, %v; want checked refusal", got, err)
	}
}

func TestTextSlowCoefficient(t *testing.T) {
	limbs := []uint32{123456789, 0, 999999999, 1, 1000}
	before := append([]uint32(nil), limbs...)
	v := slowDecimal(&slowCoefficient{limbs: limbs}, -2, false)
	// Build the coefficient with math/big only in this independent test.
	oracle := new(big.Int)
	base := big.NewInt(1_000_000_000)
	for _, limb := range slices.Backward(limbs) {
		oracle.Mul(oracle, base)
		oracle.Add(oracle, new(big.Int).SetUint64(uint64(limb)))
	}
	digits := oracle.String()
	want := digits[:len(digits)-2] + "." + digits[len(digits)-2:]
	if got, err := v.Text(0); err != nil || got != want {
		t.Fatalf("slow Text(0) = %q, %v; want %q", got, err, want)
	}
	if !reflect.DeepEqual(limbs, before) {
		t.Fatal("Text mutated a published slow coefficient")
	}
	forced := slowDecimal(&slowCoefficient{limbs: []uint32{1200}}, -3, false)
	if got, err := forced.Text(0); err != nil || got != "1.200" {
		t.Fatalf("forced slow cohort Text(0) = %q, %v; want 1.200", got, err)
	}
	if got, err := New(1200, -3).Text(0); err != nil || got != "1.200" {
		t.Fatalf("inline cohort Text(0) = %q, %v; want 1.200", got, err)
	}
}

func TestTextDigitCountAddressability(t *testing.T) {
	if got, ok := checkedDigitCount(1, 0); !ok || got != 1 {
		t.Fatalf("zero digit count = %d, %v; want 1", got, ok)
	}
	if got, ok := checkedDigitCount(5, 999); !ok || got != 39 {
		t.Fatalf("five-limb digit count = %d, %v; want 39", got, ok)
	}
	// No allocation is needed to simulate a coefficient whose decimal
	// length would cross Go's string addressability boundary.
	if got, ok := checkedDigitCount(math.MaxInt/9+1, 999_999_999); ok {
		t.Fatalf("near-MaxInt digit count = %d, %v; want refusal", got, ok)
	}
}

// strictJSONNumber is the RFC 8259 number grammar with the canonical
// emitter's uppercase E: no plus sign, no leading zeros, no bare point.
var strictJSONNumber = regexp.MustCompile(`^-?(0|[1-9][0-9]*)(\.[0-9]+)?(E[+-](0|[1-9][0-9]*))?$`)

// TestCanonicalTextIsStrictJSONNumber checks that emitted literals are
// grammar-legal and that canonical text serves the stricter grammar: for 2,000
// seeded values (up to 60 digits, both signs, zeros, exponents over the whole
// int32 domain) and the liberal inputs +1, 00, -0, -0.00, 007.0100, .5, 5. and
// +.5e+03, the canonical text matches the strict JSON number grammar, is
// accepted by encoding/json, never carries a sign on zero, is exactly the
// MarshalJSON bytes (no JSON-specific path) and, where math/big can hold it,
// has the value's math/big.Rat value; every text parses back to an Equal value.
func TestCanonicalTextIsStrictJSONNumber(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 54))
	var values []Decimal
	for _, liberal := range []string{"+1", "00", "-0", "-0.00", "007.0100", ".5", "5.", "+.5e+03", "0E-2147483648", "-9E+2147483647"} {
		values = append(values, MustParse(liberal))
	}
	for range 2000 {
		n := rng.IntN(61)
		digits := make([]byte, n)
		for i := range digits {
			digits[i] = byte('0' + rng.IntN(10))
		}
		exponent := int32(rng.Uint32())
		if rng.IntN(2) == 0 {
			exponent = int32(rng.IntN(81) - 40)
		}
		negative := rng.IntN(2) == 0
		coefficient := strings.TrimLeft(string(digits), "0")
		if coefficient == "" {
			coefficient = "0"
		}
		sign := ""
		if negative {
			sign = "-"
		}
		values = append(values, MustParse(sign+coefficient+"E"+strconv.FormatInt(int64(exponent), 10)))
	}
	zeroSign := regexp.MustCompile(`^-0(\.0*)?(E.*)?$`)
	checked := 0
	for _, d := range values {
		text, err := d.Text(0)
		if err != nil {
			t.Fatal(err)
		}
		if !strictJSONNumber.MatchString(text) || zeroSign.MatchString(text) || !json.Valid([]byte(text)) {
			t.Fatalf("canonical text %q is not a strict JSON number", text)
		}
		raw, err := d.MarshalJSON()
		if err != nil || string(raw) != text {
			t.Fatalf("MarshalJSON %q, %v differs from canonical text %q", raw, err, text)
		}
		back, err := Parse(text)
		if err != nil || !back.Equal(d) || back.exponent() != d.exponent() {
			t.Fatalf("canonical text %q parses back to %v at %d, %v", text, back, back.exponent(), err)
		}
		if d.exponent() > -400 && d.exponent() < 400 {
			got, ok := new(big.Rat).SetString(text)
			if !ok || got.Cmp(inboundTextOracle(d.coefficientDigits(), d.exponent(), d.negative())) != 0 {
				t.Fatalf("canonical text %q does not denote %sE%d", text, d.coefficientDigits(), d.exponent())
			}
			checked++
		}
	}
	for liberal, want := range map[string]string{"+1": "1", "00": "0", "-0": "0", "-0.00": "0.00", "007.0100": "7.0100", ".5": "0.5", "5.": "5", "+.5e+03": "5E+2"} {
		if got := MustParse(liberal).String(); got != want {
			t.Errorf("liberal %q emits %q, want %q", liberal, got, want)
		}
	}
	if checked < 900 {
		t.Fatalf("only %d values were checked against math/big", checked)
	}
}

// TestTextCheckedRefusalStringIsNonnumeric checks that the checked String
// refusal is nonnumeric: when the exact canonical output size crosses the
// address limit, Text(0) returns "" with ErrInsufficientStorage identity and
// String's shared mapping returns exactly %!decimal(resource limit), which
// Parse rejects and which is no value's canonical text. The limit is the
// text seam's parameter, so no unaddressable coefficient is allocated; the
// seam stands for the public calls only because requireTextDelegation
// proves from text.go's syntax that Text is exactly
// d.text(maxBytes, math.MaxInt) and String is exactly
// diagnoseText(d.Text(0)). Wants are hand-derived canonical strings.
func TestTextCheckedRefusalStringIsNonnumeric(t *testing.T) {
	requireTextDelegation(t)
	const digits = "123456789012345678901234567890123456789012345" // 45 digits: slow band
	for _, tc := range []struct {
		name, input, want string
	}{
		{"plain integer", digits + ".000", digits + ".000"},
		{"scientific", "-" + digits + "E+10", "-1." + digits[1:] + "E+54"},
		{"leading zeros", digits + "E-50", "0.00000" + digits},
	} {
		t.Run(tc.name, func(t *testing.T) {
			d := MustParse(tc.input)
			if d.slow == nil {
				t.Fatal("value is inline; the checked slow-path refusal would not be reached")
			}
			size := uint64(len(tc.want))
			if got, err := d.Text(0); err != nil || got != tc.want || d.String() != tc.want {
				t.Fatalf("Text(0) = %q, %v; String() = %q; want %q", got, err, d.String(), tc.want)
			}
			if got, err := d.text(0, size); err != nil || got != tc.want {
				t.Fatalf("text at exact address limit %d = %q, %v; want %q", size, got, err, tc.want)
			}
			got, err := d.text(0, size-1)
			if got != "" || !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("text below address limit = %q, %v; want checked ErrInsufficientStorage", got, err)
			}
			diagnostic := diagnoseText(got, err)
			if diagnostic != "%!decimal(resource limit)" {
				t.Fatalf("String diagnostic = %q", diagnostic)
			}
			if _, err := Parse(diagnostic); !errors.Is(err, ErrConversionSyntax) {
				t.Fatalf("Parse(diagnostic) = %v; want ErrConversionSyntax", err)
			}
			if _, ok := new(big.Rat).SetString(diagnostic); ok {
				t.Fatal("math/big accepts the diagnostic as a number")
			}
			if strictJSONNumber.MatchString(diagnostic) || json.Valid([]byte(diagnostic)) {
				t.Fatal("diagnostic matches the canonical number grammar")
			}
		})
	}
	// The successful path is untouched: String keeps its canonical text.
	if got := diagnoseText(New(1, -2).Text(0)); got != "0.01" {
		t.Fatalf("successful String mapping = %q, want 0.01", got)
	}
}

// funcNode parses src and returns the declaration of the function or
// method key ("Name" or "Recv.Name", pointer receivers written "*Recv").
func funcNode(fset *token.FileSet, src []byte, key string) (*ast.FuncDecl, error) {
	file, err := parser.ParseFile(fset, "", src, parser.SkipObjectResolution)
	if err != nil {
		return nil, err
	}
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok {
			continue
		}
		name := fn.Name.Name
		if fn.Recv != nil && len(fn.Recv.List) == 1 {
			var recv bytes.Buffer
			if err := printer.Fprint(&recv, fset, fn.Recv.List[0].Type); err != nil {
				return nil, err
			}
			name = recv.String() + "." + name
		}
		if name == key {
			return fn, nil
		}
	}
	return nil, fmt.Errorf("no declaration of %s", key)
}

// nodeText prints a syntax node without comments.
func nodeText(fset *token.FileSet, node ast.Node) (string, error) {
	var out bytes.Buffer
	if err := printer.Fprint(&out, fset, node); err != nil {
		return "", err
	}
	return out.String(), nil
}

// checkTextDelegation requires the Decimal.Text and Decimal.String bodies of
// src to be exactly the delegations the checked-refusal tests rely on: Text
// is return d.text(maxBytes, math.MaxInt) and String is return
// diagnoseText(d.Text(0)), so the text seam at math.MaxInt is Text and
// diagnoseText over Text(0) is String.
func checkTextDelegation(src []byte) error {
	fset := token.NewFileSet()
	for key, want := range map[string]string{
		"Decimal.Text":   "return d.text(maxBytes, math.MaxInt)",
		"Decimal.String": "return diagnoseText(d.Text(0))",
	} {
		fn, err := funcNode(fset, src, key)
		if err != nil {
			return err
		}
		if fn.Body == nil || len(fn.Body.List) != 1 {
			return fmt.Errorf("%s body is not a single statement", key)
		}
		got, err := nodeText(fset, fn.Body.List[0])
		if err != nil {
			return err
		}
		if got != want {
			return fmt.Errorf("%s body is %q, want %q", key, got, want)
		}
	}
	return nil
}

// requireTextDelegation checks text.go with checkTextDelegation, after
// proving the check rejects mutated delegations.
func requireTextDelegation(t *testing.T) {
	t.Helper()
	src, err := os.ReadFile("text.go")
	if err != nil {
		t.Fatal(err)
	}
	if err := checkTextDelegation(src); err != nil {
		t.Fatalf("text.go: %v", err)
	}
	for _, m := range []struct{ from, to string }{
		{"return d.text(maxBytes, math.MaxInt)", "return d.text(maxBytes, math.MaxInt-1)"},
		{"return d.text(maxBytes, math.MaxInt)", "return d.text(0, math.MaxInt)"},
		{"return diagnoseText(d.Text(0))", "return diagnoseText(d.Text(64))"},
		{"return diagnoseText(d.Text(0))", "s, _ := d.Text(0)\n\treturn s"},
	} {
		mutated := bytes.Replace(src, []byte(m.from), []byte(m.to), 1)
		if bytes.Equal(mutated, src) {
			t.Fatalf("delegation %q not found in text.go", m.from)
		}
		if checkTextDelegation(mutated) == nil {
			t.Fatalf("delegation check accepted the mutation %q", m.to)
		}
	}
}

// inlineTextOracle checks text against independent oracles:
// big.Rat reads it back as exactly w×10^e with d's sign, and its shape is
// the canonical one derived by hand from the coefficient's decimal digits
// (strconv) and the exponent.
func inlineTextOracle(t *testing.T, text string, w uint64, e int32, negative bool) {
	t.Helper()
	if e >= -1000 && e <= 1000 {
		// Exact rational value; extreme exponents are checked by shape only.
		want := new(big.Rat).SetInt(new(big.Int).SetUint64(w))
		scale := new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(max(e, -e))), nil))
		if e > 0 {
			want.Mul(want, scale)
		} else {
			want.Quo(want, scale)
		}
		if negative {
			want.Neg(want)
		}
		got, ok := new(big.Rat).SetString(text)
		if !ok || got.Cmp(want) != 0 {
			t.Fatalf("Text(%d, %d, %t) = %q, not the value %s", w, e, negative, text, want.RatString())
		}
	}
	digits := strconv.FormatUint(w, 10)
	n := int64(len(digits))
	sign := ""
	if negative {
		sign = "-"
	}
	var shape string
	switch exp := int64(e); {
	case exp == 0:
		shape = digits
	case exp < 0 && -exp <= n+5 && n+exp > 0:
		shape = digits[:n+exp] + "." + digits[n+exp:]
	case exp < 0 && -exp <= n+5:
		shape = "0." + strings.Repeat("0", int(-(n+exp))) + digits
	default:
		adjusted := n - 1 + exp
		shape = digits[:1]
		if n > 1 {
			shape += "." + digits[1:]
		}
		shape += "E" + map[bool]string{true: "-", false: "+"}[adjusted < 0] + strconv.FormatInt(max(adjusted, -adjusted), 10)
	}
	if text != sign+shape {
		t.Fatalf("Text(%d, %d, %t) = %q, want %q", w, e, negative, text, sign+shape)
	}
}

// TestInlineTextEmitterMatchesGeneralPath pins the one-word emitter
// (Text, AppendText, MarshalText, MarshalJSON, Value) to the strconv-based
// reference renderer (referenceWideText), to the limb path forced by slow
// storage, and to the independent oracles of inlineTextOracle and hand
// vectors, over boundary and random coefficients, exponents across the
// plain/scientific boundary and both extremes, both signs, and maxBytes in
// {0, size-1, size, size+1} with error identity and dst unchanged on
// refusal. Two-word coefficients are counted as deferrals.
func TestInlineTextEmitterMatchesGeneralPath(t *testing.T) {
	for _, tc := range []struct {
		value Decimal
		want  string
	}{
		{New(1, -6), "0.000001"},
		{New(1, -7), "1E-7"},
		{MustParse("-0.00"), "0.00"},
		{New(-5, -1), "-0.5"},
		{New(-12345, -2), "-123.45"},
		{New(0, 3), "0E+3"},
		{New(0, -11), "0E-11"},
		{New(0, -6), "0.000000"},
		{New(-1, 1), "-1E+1"},
		{New(math.MaxInt64, -25), "9.223372036854775807E-7"},
		{New(math.MinInt64, -24), "-0.000009223372036854775808"},
	} {
		if got, err := tc.value.Text(0); err != nil || got != tc.want {
			t.Fatalf("Text = %q, %v; want %q", got, err, tc.want)
		}
	}
	words := []uint64{0, 1, 9, 10, 99, 100, 1 << 63, math.MaxUint64}
	for k := 1; k <= 19; k++ {
		words = append(words, pow10Words[k]-1, pow10Words[k], pow10Words[k]+1)
	}
	rng := rand.New(rand.NewPCG(80, 81))
	for range 400 {
		bitLength := 1 + rng.IntN(64)
		words = append(words, rng.Uint64()>>(64-bitLength)|1<<(bitLength-1))
	}
	exponents := []int32{1, 2, 5, 19, 20, 1000, math.MaxInt32, math.MaxInt32 - 1, math.MinInt32, math.MinInt32 + 1, -1000}
	for e := int32(-45); e <= 0; e++ {
		exponents = append(exponents, e)
	}
	var plain, scientific, zero, refusals, deferrals int
	check := func(d Decimal, w uint64, e int32, negative bool) {
		t.Helper()
		ref, refErr := referenceWideText(d, nil, 0)
		if refErr != nil {
			t.Fatalf("reference refused %v", refErr)
		}
		want := string(ref)
		got, err := d.Text(0)
		if err != nil || got != want {
			t.Fatalf("Text(%d, %d, %t) = %q, %v; reference %q", w, e, negative, got, err, want)
		}
		// Slow storage holds a nonzero coefficient; zero is inline only.
		slowText := func(maxBytes uint64) (string, error) {
			if w == 0 {
				return d.Text(maxBytes)
			}
			return asSlowBand(d).Text(maxBytes)
		}
		if slow, err := slowText(0); err != nil || slow != want {
			t.Fatalf("slow storage Text = %q, %v; want %q", slow, err, want)
		}
		inlineTextOracle(t, got, w, e, negative)
		if strings.Contains(got, "E") {
			scientific++
		} else {
			plain++
		}
		if w == 0 {
			zero++
		}
		for name, marshal := range map[string]func() ([]byte, error){"MarshalText": d.MarshalText, "MarshalJSON": d.MarshalJSON} {
			b, err := marshal()
			if err != nil || string(b) != want || cap(b) != len(b) {
				t.Fatalf("%s = %q (cap %d), %v; want %q exactly sized", name, b, cap(b), err, want)
			}
		}
		if v, err := d.Value(); err != nil || v != any(want) {
			t.Fatalf("Value = %v, %v; want %q", v, err, want)
		}
		prefix := append(make([]byte, 0, 3), "ab:"...)
		if b, err := d.AppendText(prefix); err != nil || string(b) != "ab:"+want {
			t.Fatalf("AppendText = %q, %v", b, err)
		}
		size := uint64(len(want))
		for _, maxBytes := range []uint64{0, size - 1, size, size + 1} {
			got, err := d.Text(maxBytes)
			_, wantErr := referenceWideText(d, nil, maxBytes)
			_, slowErr := slowText(maxBytes)
			if !reflect.DeepEqual(err, wantErr) || !reflect.DeepEqual(err, slowErr) {
				t.Fatalf("Text(%d) of %q: error %#v, reference %#v, slow %#v", maxBytes, want, err, wantErr, slowErr)
			}
			dst := append(make([]byte, 0, 64), "keep"...)
			appended, appendErr := d.appendInlineText(dst, maxBytes)
			if !reflect.DeepEqual(appendErr, wantErr) {
				t.Fatalf("appendInlineText(%d) error %#v, want %#v", maxBytes, appendErr, wantErr)
			}
			if maxBytes == size-1 && maxBytes != 0 {
				var op *Error
				if got != "" || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &op) || op.Op != "Text" {
					t.Fatalf("Text(%d) of %q = %q, %v; want the Text storage refusal", maxBytes, want, got, err)
				}
				if string(appended) != "keep" || len(appended) != 4 || cap(appended) != 64 || &appended[0] != &dst[0] {
					t.Fatalf("refused appendInlineText changed dst: %q", appended)
				}
				refusals++
			} else if err != nil || got != want || string(appended) != "keep"+want {
				t.Fatalf("Text(%d) of %q = %q, %v; append %q", maxBytes, want, got, err, appended)
			}
		}
	}
	for _, w := range words {
		for _, e := range exponents {
			for _, negative := range []bool{false, true} {
				d := inlineDecimal(uint128{lo: w}, e, negative)
				check(d, w, e, negative && w != 0)
			}
		}
	}
	for _, text := range []string{"18446744073709551616", "-1.8446744073709551616", "340282366920938463463374607431768211455E-45", "100000000000000000000000000000000000000", "-99999999999999999999E-25"} {
		d := MustParse(text)
		if d.slow != nil || d.words.hi == 0 {
			t.Fatalf("%s is not a two-word inline coefficient", text)
		}
		ref, _ := referenceWideText(d, nil, 0)
		got, err := d.Text(0)
		slow, slowErr := asSlowBand(d).Text(0)
		if err != nil || slowErr != nil || got != string(ref) || slow != got {
			t.Fatalf("two-word %s: %q %v, reference %q, slow %q", text, got, err, ref, slow)
		}
		deferrals++
	}
	t.Logf("plain %d, scientific %d, zero %d, refusals %d, two-word deferrals %d", plain, scientific, zero, refusals, deferrals)
	if plain < 10000 || scientific < 5000 || zero < 50 || refusals < 15000 || deferrals < 5 {
		t.Fatalf("vacuous coverage: plain %d, scientific %d, zero %d, refusals %d, deferrals %d", plain, scientific, zero, refusals, deferrals)
	}
	d := New(-12345, -2)
	if allocs := testing.AllocsPerRun(100, func() { _, _ = d.Text(0) }); allocs != 1 {
		t.Fatalf("Text allocates %.0f times, want 1", allocs)
	}
	if allocs := testing.AllocsPerRun(100, func() { _, _ = d.MarshalJSON() }); allocs != 1 {
		t.Fatalf("MarshalJSON allocates %.0f times, want 1", allocs)
	}
	buf := make([]byte, 0, 64)
	if allocs := testing.AllocsPerRun(100, func() { _, _ = d.AppendText(buf) }); allocs != 0 {
		t.Fatalf("AppendText into spare capacity allocates %.0f times, want 0", allocs)
	}
}

// referenceWideText is a test reference for the inline renderer: it renders the coefficient's digits with strconv, then lays out
// Text's canonical form, refusing before any append when the exact size
// exceeds a positive quota.
func referenceWideText(d Decimal, dst []byte, maxBytes uint64) ([]byte, error) {
	var digitBuf [39]byte
	digits := referenceUint128(digitBuf[:0], d.words)
	n, e := int64(len(digits)), int64(d.exponent())
	plain := e <= 0 && -e <= n+5
	adjusted := n - 1 + e
	size, point := n, n+e
	if d.negative() {
		size++
	}
	if plain {
		if e < 0 {
			if point > 0 {
				size++
			} else {
				size += 2 - point
			}
		}
	} else {
		if n > 1 {
			size++
		}
		size += 2 + int64(len(strconv.FormatInt(max(adjusted, -adjusted), 10)))
	}
	if maxBytes != 0 && uint64(size) > maxBytes {
		return dst, newError("Text", ErrInsufficientStorage)
	}
	if d.negative() {
		dst = append(dst, '-')
	}
	switch {
	case plain && e == 0:
		dst = append(dst, digits...)
	case plain && point > 0:
		dst = append(append(append(dst, digits[:point]...), '.'), digits[point:]...)
	case plain:
		dst = append(dst, "0."...)
		dst = append(dst, "00000"[:-point]...)
		dst = append(dst, digits...)
	default:
		dst = append(dst, digits[0])
		if n > 1 {
			dst = append(append(dst, '.'), digits[1:]...)
		}
		if adjusted < 0 {
			dst = append(dst, "E-"...)
			adjusted = -adjusted
		} else {
			dst = append(dst, "E+"...)
		}
		dst = strconv.AppendUint(dst, uint64(adjusted), 10)
	}
	return dst, nil
}

// referenceUint128 appends the decimal digits of an unsigned 128-bit value
// by hardware division and strconv.
func referenceUint128(dst []byte, w uint128) []byte {
	const base = 10_000_000_000_000_000_000
	if w.hi == 0 {
		return strconv.AppendUint(dst, w.lo, 10)
	}
	qhi, rem := bits.Div64(0, w.hi, base)
	qlo, low := bits.Div64(rem, w.lo, base)
	if qhi == 0 {
		dst = strconv.AppendUint(dst, qlo, 10)
	} else {
		top, middle := bits.Div64(qhi, qlo, base)
		dst = strconv.AppendUint(dst, top, 10)
		dst = fmt.Appendf(dst, "%019d", middle)
	}
	return fmt.Appendf(dst, "%019d", low)
}

// referenceText is a test reference for the renderers of every storage
// band: one digit at a time through a strings.Builder,
// with the same checked refusals as text.
func referenceText(d Decimal, maxBytes, addressLimit uint64) (string, error) {
	v := coefficientViewOf(d)
	if v.count == 0 {
		v.inline[0] = 0
		v.count = 1
	}
	top := v.limb(v.count - 1)
	n, ok := checkedDigitCount(v.count, top)
	if !ok {
		return "", newError("Text", ErrInsufficientStorage)
	}
	var expMagnitude uint64
	var expNegative bool
	if d.exponent() < 0 {
		e := uint64(-int64(d.exponent()))
		if n-1 >= e {
			expMagnitude = n - 1 - e
		} else {
			expMagnitude = e - (n - 1)
			expNegative = true
		}
	} else {
		expMagnitude = n - 1 + uint64(d.exponent())
	}
	plain := d.exponent() <= 0 && uint64(-int64(d.exponent())) <= n+5
	var pointPos int64
	size := n
	if d.negative() {
		size++
	}
	if plain {
		pointPos = int64(n) + int64(d.exponent())
		if d.exponent() < 0 {
			if pointPos > 0 {
				size++
			} else {
				size += 2 + uint64(-pointPos)
			}
		}
	} else {
		if n > 1 {
			size++
		}
		size += 2 + uint64(len(strconv.FormatUint(expMagnitude, 10)))
	}
	if maxBytes != 0 && size > maxBytes || size > addressLimit {
		return "", newError("Text", ErrInsufficientStorage)
	}
	var b strings.Builder
	if d.negative() {
		b.WriteByte('-')
	}
	if plain && d.exponent() < 0 && pointPos <= 0 {
		b.WriteString("0.")
		b.WriteString(strings.Repeat("0", int(-pointPos)))
	}
	var splitAt uint64
	if plain {
		if pointPos > 0 && uint64(pointPos) < n {
			splitAt = uint64(pointPos)
		}
	} else if n > 1 {
		splitAt = 1
	}
	var emitted uint64
	writeDigit := func(digit byte) {
		if emitted == splitAt && splitAt != 0 {
			b.WriteByte('.')
		}
		b.WriteByte(digit)
		emitted++
	}
	for _, digit := range []byte(strconv.FormatUint(uint64(top), 10)) {
		writeDigit(digit)
	}
	for i := v.count - 1; i > 0; i-- {
		for _, digit := range fmt.Appendf(nil, "%09d", v.limb(i-1)) {
			writeDigit(digit)
		}
	}
	if !plain {
		b.WriteByte('E')
		if expNegative {
			b.WriteByte('-')
		} else {
			b.WriteByte('+')
		}
		b.WriteString(strconv.FormatUint(expMagnitude, 10))
	}
	return b.String(), nil
}

// canonicalTextOracle derives canonical text from math/big digits and the
// exponent placement rules alone: plain when the exponent is at most zero
// and at most n+5 zeros follow the point, scientific otherwise.
func canonicalTextOracle(coefficient *big.Int, e int64, negative bool) string {
	digits := coefficient.Text(10)
	n := int64(len(digits))
	var shape string
	switch {
	case e == 0:
		shape = digits
	case e < 0 && -e <= n+5 && n+e > 0:
		shape = digits[:n+e] + "." + digits[n+e:]
	case e < 0 && -e <= n+5:
		shape = "0." + strings.Repeat("0", int(-(n+e))) + digits
	default:
		adjusted := n - 1 + e
		shape = digits[:1]
		if n > 1 {
			shape += "." + digits[1:]
		}
		sign := "+"
		if adjusted < 0 {
			sign = "-"
		}
		shape += "E" + sign + strconv.FormatInt(max(adjusted, -adjusted), 10)
	}
	if negative {
		return "-" + shape
	}
	return shape
}

// decimalOfBig builds the canonical representation of ±coefficient×10^e:
// inline below 2^128, slow limbs otherwise. Zero has no sign.
func decimalOfBig(coefficient *big.Int, e int32, negative bool) Decimal {
	if coefficient.BitLen() <= 128 {
		lo := new(big.Int).And(coefficient, new(big.Int).SetUint64(math.MaxUint64)).Uint64()
		hi := new(big.Int).Rsh(coefficient, 64).Uint64()
		return inlineDecimal(uint128{lo: lo, hi: hi}, e, negative && coefficient.Sign() != 0)
	}
	var limbs []uint32
	base := big.NewInt(int64(decimalLimbBase))
	for q, r := new(big.Int).Set(coefficient), new(big.Int); q.Sign() != 0; {
		q.QuoRem(q, base, r)
		limbs = append(limbs, uint32(r.Uint64()))
	}
	return slowDecimal(&slowCoefficient{limbs: limbs}, e, negative)
}

// TestEmitEightExhaustive checks the branch-free eight-digit SWAR
// emitter, whose multiply-shift reciprocals are exact only on bounded
// lanes, against digits peeled by %10 for every v below 10^8, and that it
// writes only its eight bytes.
func TestEmitEightExhaustive(t *testing.T) {
	var buf [10]byte
	var want [8]byte
	for v := range uint32(100_000_000) {
		buf[0], buf[9] = 'x', 'y'
		emitEight(buf[:], 9, v)
		x := v
		for i := 7; i >= 0; i-- {
			want[i] = byte('0' + x%10)
			x /= 10
		}
		if [8]byte(buf[1:9]) != want || buf[0] != 'x' || buf[9] != 'y' {
			t.Fatalf("emitEight(%d) wrote %q", v, buf[:])
		}
	}
}

// TestTextEmittersMatchReference pins the emitters (the inline
// split into two-word groups, the chunked word emitter and the slow limb
// layout shared by Text, String, AppendText, MarshalText, MarshalJSON and
// Value) to the reference renderers referenceText and referenceWideText and to the independent math/big oracle
// canonicalTextOracle, over random coefficients of 1 to 200 digits, long
// coefficients whose text crosses Text's 512-byte staging chunk, power-of-
// ten, word and limb boundaries, both signs, exponents across the
// plain/scientific threshold and at the int32 limits, budgets that refuse
// or admit, the address-limit refusal, error identity and allocation
// counts. The vacuity guard counts every band and layout.
func TestTextEmittersMatchReference(t *testing.T) {
	rng := rand.New(rand.NewPCG(88, 89))
	randomDigits := func(n int) *big.Int {
		b := make([]byte, n)
		for i := range b {
			b[i] = byte('0' + rng.IntN(10))
		}
		b[0] = byte('1' + rng.IntN(9))
		v, _ := new(big.Int).SetString(string(b), 10)
		return v
	}
	coefficients := []*big.Int{big.NewInt(0), big.NewInt(1), big.NewInt(9)}
	for k := 1; k <= 200; k++ {
		p := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(k)), nil)
		coefficients = append(coefficients, new(big.Int).Sub(p, big.NewInt(1)), p, new(big.Int).Add(p, big.NewInt(1)))
	}
	for _, shift := range []uint{63, 64, 65, 127, 128, 129} {
		p := new(big.Int).Lsh(big.NewInt(1), shift)
		coefficients = append(coefficients, new(big.Int).Sub(p, big.NewInt(1)), p)
	}
	ten19 := new(big.Int).Exp(big.NewInt(10), big.NewInt(19), nil)
	coefficients = append(coefficients, new(big.Int).Lsh(ten19, 64), new(big.Int).Sub(new(big.Int).Lsh(ten19, 64), big.NewInt(1)))
	for range 1500 {
		coefficients = append(coefficients, randomDigits(1+rng.IntN(200)))
	}
	for range 60 {
		coefficients = append(coefficients, randomDigits(400+rng.IntN(800)))
	}
	var oneWord, twoWord, slow, forcedSlow, plain, scientific, zeroPrefix, refusals, flushed int
	check := func(d Decimal, coefficient *big.Int, e int32) {
		t.Helper()
		want := canonicalTextOracle(coefficient, int64(e), d.negative())
		ref, refErr := referenceText(d, 0, math.MaxInt)
		if refErr != nil || ref != want {
			t.Fatalf("reference %q, %v; oracle %q", ref, refErr, want)
		}
		if d.slow == nil {
			if wide, err := referenceWideText(d, nil, 0); err != nil || string(wide) != want {
				t.Fatalf("referenceWideText %q, %v; oracle %q", wide, err, want)
			}
		}
		if got, err := d.Text(0); err != nil || got != want {
			t.Fatalf("Text(0) = %q, %v; want %q", got, err, want)
		}
		if got := d.String(); got != want {
			t.Fatalf("String = %q; want %q", got, want)
		}
		for name, marshal := range map[string]func() ([]byte, error){"MarshalText": d.MarshalText, "MarshalJSON": d.MarshalJSON} {
			b, err := marshal()
			if err != nil || string(b) != want || cap(b) != len(b) {
				t.Fatalf("%s = %q (cap %d), %v; want %q exactly sized", name, b, cap(b), err, want)
			}
		}
		if v, err := d.Value(); err != nil || v != any(want) {
			t.Fatalf("Value = %v, %v; want %q", v, err, want)
		}
		if b, err := d.AppendText([]byte("ab:")); err != nil || string(b) != "ab:"+want {
			t.Fatalf("AppendText = %q, %v; want ab:%q", b, err, want)
		}
		spare := append(make([]byte, 0, len(want)+8), "xy"...)
		if b, err := d.AppendText(spare); err != nil || string(b) != "xy"+want || &b[0] != &spare[0] {
			t.Fatalf("AppendText into spare capacity = %q, %v", b, err)
		}
		size := uint64(len(want))
		for _, maxBytes := range []uint64{size - 1, size, size + 1, 1} {
			got, err := d.Text(maxBytes)
			refGot, refErr := referenceText(d, maxBytes, math.MaxInt)
			if got != refGot || !reflect.DeepEqual(err, refErr) {
				t.Fatalf("Text(%d) = %q, %#v; reference %q, %#v", maxBytes, got, err, refGot, refErr)
			}
			if err != nil {
				refusals++
			}
		}
		if d.slow != nil {
			got, err := d.text(0, size-1)
			refGot, refErr := referenceText(d, 0, size-1)
			if got != "" || refGot != "" || !reflect.DeepEqual(err, refErr) || !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("text(0, %d) = %q, %#v; reference %q, %#v", size-1, got, err, refGot, refErr)
			}
			if got, err := d.text(0, size); err != nil || got != want {
				t.Fatalf("text(0, %d) = %q, %v; want %q", size, got, err, want)
			}
			if size > 512 {
				flushed++
			}
		}
		switch {
		case d.slow != nil && coefficient.BitLen() <= 128:
			forcedSlow++
		case d.slow != nil:
			slow++
		case d.words.hi != 0:
			twoWord++
		default:
			oneWord++
		}
		switch {
		case strings.Contains(want, "E"):
			scientific++
		case strings.HasPrefix(strings.TrimPrefix(want, "-"), "0.0"):
			zeroPrefix++
			plain++
		default:
			plain++
		}
	}
	for _, coefficient := range coefficients {
		n := int32(len(coefficient.Text(10)))
		exponents := []int32{0, 1, 7, -1, -n + 1, -n, -n - 1, -n - 5, -n - 6, -n - 7,
			int32(rng.IntN(int(n)+12)) - n - 6, math.MaxInt32, math.MinInt32, math.MinInt32 + 1, math.MaxInt32 - 1}
		for i, e := range exponents {
			d := decimalOfBig(coefficient, e, i%2 == 1)
			check(d, coefficient, e)
			if coefficient.Sign() != 0 && d.slow == nil && i < 11 {
				check(asSlowBand(d), coefficient, e)
			}
		}
	}
	t.Logf("one-word %d, two-word %d, slow %d, forced slow %d, plain %d, scientific %d, zero prefix %d, refusals %d, flushed %d",
		oneWord, twoWord, slow, forcedSlow, plain, scientific, zeroPrefix, refusals, flushed)
	if oneWord < 3000 || twoWord < 2000 || slow < 15000 || forcedSlow < 4000 || plain < 10000 ||
		scientific < 10000 || zeroPrefix < 3000 || refusals < 50000 || flushed < 500 {
		t.Fatal("vacuous coverage")
	}
	for _, text := range []string{"-0." + strings.Repeat("7", 60), strings.Repeat("9", 40) + "E+300", "1" + strings.Repeat("0", 2000) + "E-2001"} {
		d := MustParse(text)
		if d.slow == nil {
			t.Fatalf("%s is inline", text)
		}
		if allocs := testing.AllocsPerRun(100, func() { _, _ = d.Text(0) }); allocs != 1 {
			t.Fatalf("slow Text allocates %.0f times, want 1", allocs)
		}
		for name, marshal := range map[string]func() ([]byte, error){"MarshalText": d.MarshalText, "MarshalJSON": d.MarshalJSON} {
			if allocs := testing.AllocsPerRun(100, func() { _, _ = marshal() }); allocs != 1 {
				t.Fatalf("slow %s allocates %.0f times, want 1", name, allocs)
			}
		}
		buf := make([]byte, 0, 4096)
		if allocs := testing.AllocsPerRun(100, func() { _, _ = d.AppendText(buf) }); allocs != 0 {
			t.Fatalf("slow AppendText into spare capacity allocates %.0f times, want 0", allocs)
		}
	}
}

// TestOneWordPlainTextMatchesPlannedPath pins the right-aligned path
// for one-word plain text to the planned inline emitter (emitWordText at
// inlineTextSize) and, at exponent 0, to strconv: over both signs, zero,
// every digit count up to MaxUint64, exponents from 0 down past the
// plain/scientific threshold and maxBytes at size-1, size and 0, the text,
// the refusal and its error identity agree.
func TestOneWordPlainTextMatchesPlannedPath(t *testing.T) {
	r := rand.New(rand.NewPCG(88, 4))
	served := 0
	values := []uint64{0, 1, 9, 10, 99, 100, 1e8 - 1, 1e8, 1e16, 1e19 - 1, 1e19, math.MaxUint64}
	for range 20000 {
		values = append(values, r.Uint64()>>r.IntN(64))
	}
	for _, w := range values {
		for _, negative := range []bool{false, true} {
			for _, e := range []int32{0, -1, -2, -7, -int32(wordDigits(w)) - 5, -int32(wordDigits(w)) - 6, 3} {
				d := inlineDecimal(uint128{lo: w}, e, negative && w != 0)
				n := wordDigits(w)
				size := d.inlineTextSize(n)
				planned := make([]byte, size)
				d.emitWordText(planned, n)
				want := string(planned)
				if e == 0 {
					want = strconv.FormatUint(w, 10)
					if d.negative() {
						want = "-" + want
					}
				}
				for _, maxBytes := range []uint64{0, uint64(size), uint64(size) - 1} {
					got, err := d.Text(maxBytes)
					if maxBytes != 0 && maxBytes < uint64(size) {
						var e *Error
						if got != "" || !errors.As(err, &e) || e.Op != "Text" || e.Code != ErrInsufficientStorage {
							t.Fatalf("Text(%s, %d) = %q, %v; want the refusal", want, maxBytes, got, err)
						}
						continue
					}
					if err != nil || got != want || got != string(planned) {
						t.Fatalf("Text(%s, %d) = %q, %v; planned %q", want, maxBytes, got, err, planned)
					}
					served++
				}
			}
		}
	}
	if served < 300000 {
		t.Fatalf("vacuous: %d direct-path texts", served)
	}
}
