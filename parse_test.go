// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"reflect"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"
)

func TestParseCohortAndEffectiveExponent(t *testing.T) {
	cases := []struct {
		input    string
		digits   string
		exponent int32
		negative bool
	}{
		{"+5", "5", 0, false},
		{".5", "5", -1, false},
		{"5.", "5", 0, false},
		{"007.0100", "70100", -4, false},
		{"-0.00", "0", -2, false},
		{"0E+9", "0", 9, false},
		{"1.2E+2147483648", "12", math.MaxInt32, false},
		{"1.2E-2147483647", "12", math.MinInt32, false},
	}
	for _, tc := range cases {
		t.Run(tc.input, func(t *testing.T) {
			got, err := Parse(tc.input)
			if err != nil {
				t.Fatal(err)
			}
			if got.coefficientDigits() != tc.digits || got.exponent() != tc.exponent || got.negative() != tc.negative {
				t.Fatalf("got digits=%q exponent=%d negative=%v", got.coefficientDigits(), got.exponent(), got.negative())
			}
		})
	}
}

func TestParsePromotionAndIndependentMagnitudeOracle(t *testing.T) {
	cases := []string{
		"340282366920938463463374607431768211455", // 2^128-1
		"340282366920938463463374607431768211456", // 2^128
		strings.Repeat("9", 1000),
	}
	for i, input := range cases {
		got, err := Parse(input)
		if err != nil {
			t.Fatal(err)
		}
		want, ok := new(big.Int).SetString(input, 10)
		if !ok || got.coefficientDigits() != want.String() {
			t.Fatalf("magnitude %d mismatch", i)
		}
		if (got.slow != nil) != (i > 0) {
			t.Fatalf("magnitude %d slow=%v", i, got.slow != nil)
		}
		copy := got
		if copy.coefficientDigits() != input {
			t.Fatalf("copy lost magnitude %d", i)
		}
	}
}

func TestParseErrorsAndPrecedence(t *testing.T) {
	tests := []struct {
		name      string
		input     string
		budget    Budget
		code      ErrorCode
		condition Conditions
	}{
		{"syntax", "1_0", Budget{}, ErrConversionSyntax, ConversionSyntax},
		{"special", "NaN", Budget{}, ErrConversionSyntax, ConversionSyntax},
		{"range", "1e2147483648", Budget{}, ErrExponentRange, 0},
		{"zero range", "0e2147483648", Budget{}, ErrExponentRange, 0},
		{"input before syntax", "1_0", Budget{MaxInputBytes: 2}, ErrInsufficientStorage, InsufficientStorage},
		{"long leading zeros before scan", strings.Repeat("0", 2048) + "1", Budget{MaxInputBytes: 64}, ErrInsufficientStorage, InsufficientStorage},
		{"deep exponent before scan", "1e+" + strings.Repeat("0", 2048) + "7", Budget{MaxInputBytes: 64}, ErrInsufficientStorage, InsufficientStorage},
		{"syntax before digit budget", "1_0", Budget{MaxDigits: 1}, ErrConversionSyntax, ConversionSyntax},
		{"range before digit budget", "123e2147483648", Budget{MaxDigits: 1}, ErrExponentRange, 0},
		{"digit budget", "0001200", Budget{MaxDigits: 3}, ErrInsufficientStorage, InsufficientStorage},
		{"zero digit budget", "00000", Budget{MaxDigits: 1}, 0, 0},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got, _, err := ParseWithContext(tc.input, Context{}.WithBudget(tc.budget))
			if tc.code == 0 {
				if err != nil || !got.isZero() {
					t.Fatalf("zero success got %+v, %v", got, err)
				}
				return
			}
			if !errors.Is(err, tc.code) || !got.isZero() || got.exponent() != 0 {
				t.Fatalf("got %+v, %v; want %v", got, err, tc.code)
			}
			var pe *Error
			if !errors.As(err, &pe) || pe.Op != "ParseWithContext" || pe.Input != tc.input || pe.Condition != tc.condition || pe.Code != tc.code {
				t.Fatalf("parse error mismatch: %+v", pe)
			}
		})
	}
}

func TestParseAndMustParseShareOnePath(t *testing.T) {
	if _, err := Parse("bad"); err != nil {
		var pe *Error
		if !errors.As(err, &pe) || pe.Op != "Parse" || pe.Input != "bad" || pe.Condition != ConversionSyntax || !errors.Is(err, ErrConversionSyntax) {
			t.Fatalf("Parse error = %v", err)
		}
	} else {
		t.Fatal("Parse accepted invalid literal")
	}
	got, err := Parse("0001.2300")
	if err != nil || got.coefficientDigits() != "12300" || got.exponent() != -4 {
		t.Fatalf("Parse = %+v, %v", got, err)
	}
	if must := MustParse("0001.2300"); must.coefficientDigits() != got.coefficientDigits() || must.exponent() != got.exponent() {
		t.Fatal("MustParse diverged")
	}
	defer func() {
		pe, ok := recover().(*Error)
		if !ok || pe.Op != "Parse" || !errors.Is(pe, ErrConversionSyntax) {
			t.Fatalf("panic = %#v", pe)
		}
	}()
	MustParse("bad")
}

func TestParseGrammarAndDeepExponent(t *testing.T) {
	for _, input := range []string{"", " ", " 1", "1 ", "1_0", "1_000", "1,0", "1,5", "0x10", "e5", "1e", "1e+", "1.2.3", ".", "+.", "1ee2", "Infinity", "-Infinity", "-sNaN5", ".nan", ".inf"} {
		_, err := Parse(input)
		if !errors.Is(err, ErrConversionSyntax) {
			t.Errorf("Parse(%q) = %v, want syntax", input, err)
		}
	}
	for _, input := range []string{"1e2147483648", "1e-2147483649", "0e2147483648"} {
		_, err := Parse(input)
		if !errors.Is(err, ErrExponentRange) {
			t.Errorf("Parse(%q) = %v, want range", input, err)
		}
	}
	deep := "1e+" + strings.Repeat("0", 100_000) + "7"
	got, err := Parse(deep)
	if err != nil || got.words != (uint128{lo: 1}) || got.exponent() != 7 {
		t.Fatalf("deep exponent = %+v, %v", got, err)
	}
	_, _, err = ParseWithContext(deep, Context{}.WithBudget(Budget{MaxInputBytes: 100}))
	if !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("deep input budget = %v", err)
	}
}

var sinkHostile Decimal

func TestParseHostileExponentBoundedWork(t *testing.T) {
	const input = "1e999999999"
	got, err := Parse(input)
	if err != nil {
		t.Fatal(err)
	}
	if got.words != (uint128{lo: 1}) || got.slow != nil || got.exponent() != 999_999_999 || got.negative() {
		t.Fatalf("hostile exponent parsed as %+v", got)
	}
	allocs := testing.AllocsPerRun(100, func() {
		value, err := Parse(input)
		if err != nil {
			t.Fatal(err)
		}
		sinkHostile = value
	})
	if allocs != 0 {
		t.Fatalf("Parse(%q) allocated %g times per call; coefficient/exponent fit inline", input, allocs)
	}
}

func TestParseCoefficientAgainstIndependentBigInt(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260922, 16))
	for trial := range 500 {
		length := 1 + rng.IntN(150)
		var input strings.Builder
		input.WriteString(strings.Repeat("0", rng.IntN(16)))
		for range length {
			input.WriteByte(byte('0' + rng.IntN(10)))
		}
		literal := input.String()
		got, err := Parse(literal)
		if err != nil {
			t.Fatalf("trial %d: %v", trial, err)
		}
		want, ok := new(big.Int).SetString(literal, 10)
		if !ok || got.coefficientDigits() != want.String() || got.exponent() != 0 || got.negative() {
			t.Fatalf("trial %d: got %q, want %s", trial, got.coefficientDigits(), want)
		}
		if got.slow != nil {
			if got.words != (uint128{}) || got.slow.limbs[len(got.slow.limbs)-1] == 0 {
				t.Fatalf("trial %d: bad slow normalization", trial)
			}
			for _, limb := range got.slow.limbs {
				if limb >= 1_000_000_000 {
					t.Fatalf("trial %d: limb out of range", trial)
				}
			}
		}
	}
}

func TestParseErrorZeroValueTotal(t *testing.T) {
	var zero Error
	if text := zero.Error(); text == "" {
		t.Fatal("zero Error has no diagnostic")
	}
	if errors.Unwrap(&zero) != nil {
		t.Fatal("zero Error unwraps to a cause")
	}
	var absent *Error
	if text := absent.Error(); text == "" {
		t.Fatal("nil Error has no diagnostic")
	}
	if errors.Unwrap(absent) != nil {
		t.Fatal("nil Error unwraps to a cause")
	}
}

// errorIdentity is the error comparison key: the errors.Is
// sentinel, or the trapped conditions of an *Error.
func errorIdentity(err error) string {
	var ce *Error
	switch {
	case err == nil:
		return ""
	case errors.As(err, &ce) && ce.Code == 0:
		return "trapped " + ce.Condition.String()
	}
	for _, code := range []ErrorCode{ErrConversionSyntax, ErrExponentRange, ErrInsufficientStorage, ErrInvalidContext, ErrInvalidOperation} {
		if errors.Is(err, code) {
			return code.Error()
		}
	}
	return "unknown " + err.Error()
}

// randomRoundingLiteral draws literals of 1–400 digits with leading and
// trailing zeros, points in every position and exponents that place a
// target on both sides of the value.
func randomRoundingLiteral(rng *rand.Rand) string {
	var b strings.Builder
	if rng.IntN(3) == 0 {
		b.WriteByte('-')
	}
	digits := 1 + rng.IntN(40)
	if rng.IntN(6) == 0 {
		digits = 1 + rng.IntN(400)
	}
	body := make([]byte, digits)
	for i := range body {
		body[i] = byte('0' + rng.IntN(10))
		if rng.IntN(5) == 0 {
			body[i] = '0'
		}
	}
	if rng.IntN(4) == 0 { // a tie or near-tie tail
		body[len(body)-1] = '5'
	}
	point := rng.IntN(digits + 1)
	b.Write(body[:point])
	if point < digits || rng.IntN(2) == 0 {
		b.WriteByte('.')
		b.Write(body[point:])
	}
	if rng.IntN(2) == 0 {
		b.WriteString("e")
		b.WriteString(fmt.Sprint(rng.IntN(120) - 60))
	}
	return b.String()
}

// TestParseToExponentMatchesParseQuantize checks that a rounding parse
// equals parse then quantize: over
// random literals and targets on both sides, in every mode, for string and
// []byte carriers, ParseToExponent equals Parse followed by Quantize in
// value, cohort, Conditions and error identity.
func TestParseToExponentMatchesParseQuantize(t *testing.T) {
	rng := rand.New(rand.NewPCG(48, 1))
	for range 30000 {
		s := randomRoundingLiteral(rng)
		parsed, err := Parse(s)
		if err != nil {
			t.Fatalf("corpus literal %q: %v", s, err)
		}
		target := parsed.exponent() + int32(rng.IntN(80)-40)
		mode := allDivModes[rng.IntN(len(allDivModes))]
		want, wc, we := parsed.Quantize(target, mode)
		for _, got := range []struct {
			d   Decimal
			c   Conditions
			err error
		}{
			func() (r struct {
				d   Decimal
				c   Conditions
				err error
			}) {
				r.d, r.c, r.err = ParseToExponent(s, target, mode)
				return
			}(),
			func() (r struct {
				d   Decimal
				c   Conditions
				err error
			}) {
				r.d, r.c, r.err = ParseToExponent([]byte(s), target, mode)
				return
			}(),
		} {
			if errorIdentity(got.err) != errorIdentity(we) || we == nil && (!got.d.Equal(want) || got.d.exponent() != want.exponent() || got.c != wc) {
				t.Fatalf("%q t=%d %v: (%v, %v, %v), want (%v, %v, %v)", s, target, mode, got.d, got.c, got.err, want, wc, we)
			}
		}
	}
}

// TestParseWithContextAgainstRationalOracle covers ParseWithContext against
// the context oracles on the literal's exact rational (literals
// with |E| ≤ 10^6), unguarded and guarded, in every mode.
func TestParseWithContextAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(48, 2))
	for range 12000 {
		s := randomRoundingLiteral(rng)
		r, ok := new(big.Rat).SetString(s)
		if !ok {
			t.Fatalf("oracle cannot read %q", s)
		}
		parsed, _ := Parse(s)
		if parsed.isZero() {
			continue // zeros keep their exponent unclamped; TestParseRoundingZeros
		}
		p := int64(1 + rng.IntN(50))
		mode := allDivModes[rng.IntN(len(allDivModes))]
		var ctx Context
		var want divExpect
		if rng.IntN(2) == 0 {
			ctx, _ = NewContext(uint32(p), mode, nil, 0)
			want = oracleContext(r, int64(parsed.exponent()), p, mode)
		} else {
			emin := int64(rng.IntN(120) - 100)
			emax := emin + int64(rng.IntN(120))
			ctx, _ = NewContext(uint32(p), mode, &ExponentGuards{Emin: int32(emin), Emax: int32(emax)}, 0)
			want = oracleGuarded(r, int64(parsed.exponent()), p, emin, emax, mode)
		}
		got, conditions, err := ParseWithContext(s, ctx)
		checkDivOutcome(t, fmt.Sprintf("%q p=%d %v", s, p, mode), got, conditions, err, want, r.Sign() < 0)
	}
}

// TestParseRoundingMagnitudeVectors checks that a rounding parse resolves
// exponents by magnitude: literals whose
// effective exponent lies outside int32 round by value downward, refuse
// with ErrExponentRange upward, and saturation boundaries classify exactly.
func TestParseRoundingMagnitudeVectors(t *testing.T) {
	for _, tc := range []struct {
		s    string
		t    int32
		mode RoundingMode
		want string
		cond Conditions
	}{
		{"1e-99999999999", -2, TiesToEven, "0.00", Inexact | Rounded | Decreased},
		{"1e-99999999999", -2, TowardPositiveInfinity, "0.01", Inexact | Rounded | Increased},
		{"-1e-99999999999", -2, TowardNegativeInfinity, "-0.01", Inexact | Rounded | Decreased},
		{"-1e-99999999999", -2, TiesToEven, "0.00", Inexact | Rounded | Increased},
		{"1e-99999999999", -2, AwayFromZero, "0.01", Inexact | Rounded | Increased},
		{"0.5e-9223372036854775808", 0, AwayFromZero, "1", Inexact | Rounded | Increased},
		{"1e-4611686018427387904", 5, TowardZero, "0E+5", Inexact | Rounded | Decreased},
		{"0e+99999999999", -2, TiesToEven, "0.00", 0},
		{"0e-99999999999", 7, TiesToEven, "0E+7", 0},
		{"12.5e-2147483650", 0, TiesToEven, "0", Inexact | Rounded | Decreased},
		{"1" + strings.Repeat("0", 50) + "e-2147483690", -2147483640, Exact, "1E-2147483640", Rounded},
	} {
		got, conditions, err := ParseToExponent(tc.s, tc.t, tc.mode)
		if err != nil || got.String() != tc.want || conditions != tc.cond {
			t.Fatalf("ParseToExponent(%.40q, %d, %v) = (%v, %v, %v), want (%s, %v)", tc.s, tc.t, tc.mode, got, conditions, err, tc.want, tc.cond)
		}
	}
	for _, s := range []string{"1e+99999999999", "1e2147483648", "-5e4611686018427387903", "1e4611686018427387904", "1e18446744073709551616", "1e+" + strings.Repeat("9", 100000)} {
		var got Decimal
		var err error
		allocs := testing.AllocsPerRun(3, func() { got, _, err = ParseToExponent(s, -2, TiesToEven) })
		var pe *Error
		if !errors.As(err, &pe) || !errors.Is(err, ErrExponentRange) || pe.Condition != 0 || !got.isZero() || allocs > 2 {
			t.Fatalf("ParseToExponent(%.30q, -2): (%v, %v) after %v allocations, want ErrExponentRange", s, got, err, allocs)
		}
	}
	if _, err := Parse("1e-99999999999"); !errors.Is(err, ErrExponentRange) {
		t.Fatalf("Parse keeps the range error: %v", err)
	}
	deep := "1e-" + strings.Repeat("0", 1000000) + "3"
	if got, _, err := ParseToExponent(deep, -2, TiesToEven); err != nil || got.String() != "0.00" {
		t.Fatalf("deep exponent: (%v, %v)", got, err)
	}
}

// TestParseRoundingZeros pins the zero rule: the exponent target
// gives zero at the target for any E; the context target keeps E unclamped
// and refuses an E outside int32, as Div and Mul do.
func TestParseRoundingZeros(t *testing.T) {
	ctx := Decimal64Context()
	if got, c, err := ParseWithContext("0E-500", ctx); err != nil || c != 0 || got.exponent() != -500 || !got.isZero() {
		t.Fatalf("0E-500: (%v, %v, %v)", got, c, err)
	}
	if _, _, err := ParseWithContext("0e-99999999999", ctx); !errors.Is(err, ErrExponentRange) {
		t.Fatalf("0e-99999999999: %v", err)
	}
	if got, c, err := ParseToExponent("-0.000", 3, Exact); err != nil || c != 0 || got.exponent() != 3 || got.negative() {
		t.Fatalf("-0.000 at 3: (%v, %v, %v)", got, c, err)
	}
}

// TestParseRoundingFarTies covers a tie decided by a digit 10^6 places to
// the right, in both spans, and the exact tie.
func TestParseRoundingFarTies(t *testing.T) {
	zeros := strings.Repeat("0", 1000000)
	for _, tc := range []struct{ s, want string }{
		{"0.125" + zeros + "1", "0.13"},
		{"0.125" + zeros, "0.12"},
		{"125" + zeros + "1e-1000004", "0.13"},
		{"12.5" + zeros + "0", "12"},
		{"13.5" + zeros + "0", "14"},
	} {
		target := int32(-2)
		if !strings.HasPrefix(tc.s, "0.") && !strings.Contains(tc.s, "e") {
			target = 0
		}
		got, _, err := ParseToExponent(tc.s, target, TiesToEven)
		if err != nil || got.String() != tc.want {
			t.Fatalf("%.12q…: (%v, %v), want %s", tc.s, got, err, tc.want)
		}
	}
}

// TestParseRoundingContextVectors covers the context target's paths:
// exact-first below Etiny, a raised t′ with digits kept, a carry at p
// digits, a carry into Overflow, and traps.
func TestParseRoundingContextVectors(t *testing.T) {
	guarded := func(p uint32, emin, emax int32, mode RoundingMode, traps Conditions) Context {
		ctx, err := NewContext(p, mode, &ExponentGuards{Emin: emin, Emax: emax}, traps)
		if err != nil {
			t.Fatal(err)
		}
		return ctx
	}
	for _, tc := range []struct {
		s    string
		ctx  Context
		want string
		cond Conditions
		err  ErrorCode
	}{
		{"1.5E-26", guarded(7, -20, 20, TiesToEven, 0), "2E-26", Inexact | Rounded | Subnormal | Underflow | Increased, 0},
		{"1.5E-30", guarded(7, -20, 20, TiesToEven, 0), "0E-26", Inexact | Rounded | Subnormal | Underflow | Decreased, 0},
		{"1.23456789E-24", guarded(7, -20, 20, TiesToEven, 0), "1.23E-24", Inexact | Rounded | Subnormal | Underflow | Decreased, 0},
		{"9999999.5", guarded(7, -20, 20, TiesToEven, 0), "1.000000E+7", Inexact | Rounded | Increased, 0},
		{"9999999.5E+14", guarded(7, -20, 20, TiesToEven, 0), "9.999999E+20", Inexact | Rounded | Overflow | Decreased, 0},
		{"1.00000001", guarded(7, -20, 20, TiesToEven, Inexact), "", 0, ErrInexact},
		{"1.10", Decimal64Context(), "1.10", 0, 0},
	} {
		got, c, err := ParseWithContext(tc.s, tc.ctx)
		if tc.err != 0 {
			if !errors.Is(err, tc.err) {
				t.Fatalf("%s: %v, want %v", tc.s, err, tc.err)
			}
			continue
		}
		if err != nil || got.String() != tc.want || c != tc.cond {
			t.Fatalf("%s: (%v, %v, %v), want (%s, %v)", tc.s, got, c, err, tc.want, tc.cond)
		}
	}
}

// TestParseRoundingAllocations checks that rounding parse memory is
// result-sized: a 1 MiB literal rounded to a short result
// allocates nothing for string and []byte carriers, and a published slow
// result below the stack threshold allocates only its holder and limbs.
func TestParseRoundingAllocations(t *testing.T) {
	long := "1." + strings.Repeat("7", 1<<20)
	raw := []byte(long)
	ctx := Decimal128Context()
	for name, f := range map[string]func(){
		"string to exponent": func() { _, _, _ = ParseToExponent(long, -30, TiesToEven) },
		"bytes to exponent":  func() { _, _, _ = ParseToExponent(raw, -30, TiesToEven) },
		"string context":     func() { _, _, _ = ParseWithContext(long, ctx) },
		"bytes context":      func() { _, _, _ = ParseWithContext(raw, ctx) },
		"bytes Parse":        func() { _, _ = Parse(raw[:30]) },
		"pad inline":         func() { _, _, _ = ParseToExponent("7", -2, TiesToEven) },
	} {
		if allocs := testing.AllocsPerRun(5, f); allocs != 0 {
			t.Fatalf("%s allocated %v times", name, allocs)
		}
	}
	if allocs := testing.AllocsPerRun(5, func() { _, _, _ = ParseToExponent(long, -99, TiesToEven) }); allocs != 2 {
		t.Fatalf("100-digit result allocated %v times, want 2", allocs)
	}
}

// TestParseRoundingBudgets covers Budget on the rounding forms: input
// bytes at |s|−1 and |s|, result digits at N−1 and N (including a carry
// that adds a digit), and refusals that allocate only the error.
func TestParseRoundingBudgets(t *testing.T) {
	s := "99.996"
	if _, _, err := ParseToExponentWithBudget(s, -2, TiesToEven, Budget{MaxInputBytes: uint64(len(s) - 1)}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("input |s|−1: %v", err)
	}
	if got, _, err := ParseToExponentWithBudget(s, -2, TiesToEven, Budget{MaxInputBytes: uint64(len(s))}); err != nil || got.String() != "100.00" {
		t.Fatalf("input |s|: (%v, %v)", got, err)
	}
	// 99.996 at −2 carries to 100.00: 5 digits although 4 are retained.
	// The finisher's refusal is adapted to the parse family's *Error.
	var carry *Error
	if _, _, err := ParseToExponentWithBudget(s, -2, TiesToEven, Budget{MaxDigits: 4}); !errors.As(err, &carry) || !errors.Is(err, ErrInsufficientStorage) || carry.Input != s {
		t.Fatalf("carry beyond N−1: %v", err)
	}
	if got, _, err := ParseToExponentWithBudget(s, -2, TiesToEven, Budget{MaxDigits: 5}); err != nil || got.String() != "100.00" {
		t.Fatalf("N: (%v, %v)", got, err)
	}
	var pe *Error
	pad := func() error {
		_, _, err := ParseToExponentWithBudget("1e9", -1000000, TiesToEven, Budget{MaxDigits: 1000009})
		return err
	}
	if err := pad(); !errors.As(err, &pe) || !errors.Is(err, ErrInsufficientStorage) || pe.Op != "ParseToExponentWithBudget" {
		t.Fatalf("pad N−1: %v", err)
	}
	if allocs := testing.AllocsPerRun(3, func() { _ = pad() }); allocs > 2 {
		t.Fatalf("pad refusal allocated %v times", allocs)
	}
	if got, _, err := ParseWithContext("1234567", Decimal32Context().WithBudget(Budget{MaxDigits: 6})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("context N−1: (%v, %v)", got, err)
	}
}

// TestParseResourceBoundGrowthRefusesBeforeAllocation checks that
// resource-bound growth reports a condition: a result beyond a caller
// digit budget, or on 32-bit targets beyond checked addressability, is
// refused with Insufficient-storage identity before the allocation.
func TestParseResourceBoundGrowthRefusesBeforeAllocation(t *testing.T) {
	grow := func() error {
		_, _, err := ParseToExponentWithBudget("1e2147483647", -1000, TiesToEven, Budget{MaxDigits: 1 << 20})
		return err
	}
	if err := grow(); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("budgeted growth: %v", err)
	}
	if allocs := testing.AllocsPerRun(3, func() { _ = grow() }); allocs > 2 {
		t.Fatalf("refusal allocated %v times", allocs)
	}
	if bits.UintSize == 32 {
		unbounded := func() error { _, _, err := ParseToExponent("1e2147483647", math.MinInt32, TiesToEven); return err }
		if err := unbounded(); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("32-bit addressability: %v", err)
		}
		if allocs := testing.AllocsPerRun(3, func() { _ = unbounded() }); allocs > 2 {
			t.Fatalf("32-bit refusal allocated %v times", allocs)
		}
	}
}

// TestParseGenericCarriersShareOnePath covers the single parse path: the
// string and []byte instantiations give the same value, cohort and error
// identity for Parse, ParseWithContext under a budget and both rounding forms, and a
// positive budget only ever adds a checked resource refusal, never a
// different numeric result.
func TestParseGenericCarriersShareOnePath(t *testing.T) {
	rng := rand.New(rand.NewPCG(48, 3))
	inputs := []string{"", "1_000", "NaN", "1e2147483648", "0001.2300", "-0.000"}
	for range 2000 {
		inputs = append(inputs, randomRoundingLiteral(rng))
	}
	for _, s := range inputs {
		a, ae := Parse(s)
		b, be := Parse([]byte(s))
		c, _, ce := ParseWithContext(s, Context{})
		if errorIdentity(ae) != errorIdentity(be) || errorIdentity(ae) != errorIdentity(ce) || ae == nil && (a.Compare(b) != 0 || a.exponent() != b.exponent() || a.Compare(c) != 0 || a.exponent() != c.exponent()) {
			t.Fatalf("%q: (%v, %v) (%v, %v) (%v, %v)", s, a, ae, b, be, c, ce)
		}
		for _, b := range []Budget{{MaxInputBytes: 5}, {MaxDigits: 3}, {MaxInputBytes: 64, MaxDigits: 20}} {
			for _, got := range []func() (Decimal, error){
				func() (Decimal, error) {
					res, _, resErr := ParseWithContext(s, Context{}.WithBudget(b))
					return res, resErr
				},
				func() (Decimal, error) {
					res, _, resErr := ParseWithContext([]byte(s), Context{}.WithBudget(b))
					return res, resErr
				},
			} {
				d, err := got()
				if err == nil && (ae != nil || d.Compare(a) != 0 || d.exponent() != a.exponent()) || err != nil && ae == nil && !errors.Is(err, ErrInsufficientStorage) {
					t.Fatalf("%q under %+v: (%v, %v), zero budget (%v, %v)", s, b, d, err, a, ae)
				}
			}
		}
		x, xc, xe := ParseWithContext(s, Decimal64Context())
		y, yc, ye := ParseWithContext([]byte(s), Decimal64Context())
		if errorIdentity(xe) != errorIdentity(ye) || xe == nil && (x.Compare(y) != 0 || x.exponent() != y.exponent() || xc != yc) {
			t.Fatalf("%q context: (%v, %v, %v) vs (%v, %v, %v)", s, x, xc, xe, y, yc, ye)
		}
	}
}

// TestParseWithContextUnlimitedPrecision pins precision 0: it
// publishes the exact literal at its written exponent through the Parse
// path, and an exponent outside int32 is ErrExponentRange.
func TestParseWithContextUnlimitedPrecision(t *testing.T) {
	for _, s := range []string{"1.10", "-123456789012345678901234567890.000", "7E+5", "0.000"} {
		want, _ := Parse(s)
		got, c, err := ParseWithContext(s, Context{})
		if err != nil || c != 0 || got.Compare(want) != 0 || got.exponent() != want.exponent() {
			t.Fatalf("%s: (%v, %v, %v), want %v", s, got, c, err, want)
		}
	}
	var pe *Error
	if _, _, err := ParseWithContext("1e-99999999999", Context{}); !errors.As(err, &pe) || !errors.Is(err, ErrExponentRange) {
		t.Fatalf("unlimited precision outside int32: %v", err)
	}
}

// BenchmarkParseToExponent is a smoke benchmark: a money
// literal to scale 2, a 1 MiB literal to scale 30, and a deep-tiny literal.
func BenchmarkParseToExponent(b *testing.B) {
	long := "1." + strings.Repeat("7", 1<<20)
	for _, bc := range []struct {
		name string
		s    string
		t    int32
	}{{"money", "12345.6789", -2}, {"1MiB", long, -30}, {"tiny", "1e-99999999999", -2}} {
		b.Run(bc.name, func(b *testing.B) {
			b.ReportAllocs()
			for b.Loop() {
				_, _, _ = ParseToExponent(bc.s, bc.t, TiesToEven)
			}
		})
	}
}

// TestParseWithContextBudgetBelowEtiny pins the digit budget below Etiny:
// a literal that fits the precision but lies below Etiny is rounded at
// Etiny, so the digit budget counts only the result's digits, as
// FromRatWithContext and DivWithContext do under a budget.
func TestParseWithContextBudgetBelowEtiny(t *testing.T) {
	for _, tc := range []struct {
		s    string
		ctx  Context
		want string
	}{
		{"9999999e-6200", Decimal128Context(), "0E-6176"},
		{"9999999e-99999999999", Decimal128Context(), "0E-6176"},
	} {
		got, c, err := ParseWithContext(tc.s, tc.ctx.WithBudget(Budget{MaxDigits: 1}))
		if err != nil || got.String() != tc.want || c != Inexact|Rounded|Subnormal|Underflow|Decreased {
			t.Fatalf("%s: (%v, %v, %v), want %s", tc.s, got, c, err, tc.want)
		}
		r, _ := new(big.Rat).SetString(strings.Replace(tc.s, "e-99999999999", "e-9999", 1))
		if want, wc, werr := FromRatWithContext(r, tc.ctx.WithBudget(Budget{MaxDigits: 1})); werr != nil || !sameCohort(got, want) || wc != c {
			t.Fatalf("%s: FromRat sibling (%v, %v, %v)", tc.s, want, wc, werr)
		}
	}
	ctx, err := NewContext(5, TiesToEven, &ExponentGuards{Emin: 0, Emax: 10}, 0)
	if err != nil {
		t.Fatal(err)
	}
	if got, _, err := ParseWithContext(".99999E-42", ctx.WithBudget(Budget{MaxDigits: 1})); err != nil || got.String() != "0.0000" {
		t.Fatalf(".99999E-42: (%v, %v)", got, err)
	}
	wide, err := NewContext(450, TiesToEven, &ExponentGuards{Emin: 0, Emax: 10}, 0)
	if err != nil {
		t.Fatal(err)
	}
	if got, _, err := ParseWithContext("000000.5E-4611686018427387904", wide.WithBudget(Budget{MaxDigits: 1})); err != nil || got.String() != "0E-449" {
		t.Fatalf("saturated below Etiny: (%v, %v)", got, err)
	}
	// A context digit budget refuses before retaining any digits: a 1000-digit literal at p = 500 under a 10-digit cap allocates
	// only the error.
	long := "1." + strings.Repeat("3", 999)
	wide500, _ := NewContext(500, TiesToEven, nil, 0)
	refuse := func() { _, _, _ = ParseWithContext(long, wide500.WithBudget(Budget{MaxDigits: 10})) }
	if _, _, err := ParseWithContext(long, wide500.WithBudget(Budget{MaxDigits: 10})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("context digit budget: %v", err)
	}
	if allocs := testing.AllocsPerRun(5, refuse); allocs > 1 {
		t.Fatalf("context digit refusal allocated %v times", allocs)
	}
}

// sameCohort reports value and exponent equality.
func sameCohort(a, b Decimal) bool { return a.Compare(b) == 0 && a.exponent() == b.exponent() }

// TestParseRoundingCarryAndPrecedence pins carry and precedence edges: a carry
// out of the stack scratch (424–432 digits) and out of heap scratch (more
// than 432 digits), the adapted refusal's condition, the precision-0 digit
// budget, and the order of unknown mode, input budget and syntax.
func TestParseRoundingCarryAndPrecedence(t *testing.T) {
	for _, n := range []int{424, 432, 500} {
		got, c, err := ParseToExponent(strings.Repeat("9", n)+".9", 0, TiesToEven)
		if err != nil || got.String() != "1"+strings.Repeat("0", n) || c != Inexact|Rounded|Increased {
			t.Fatalf("carry at %d digits: (%d digits, %v, %v)", n, got.CoefficientDigits(), c, err)
		}
	}
	var pe *Error
	if _, _, err := ParseToExponentWithBudget("99.996", -2, TiesToEven, Budget{MaxDigits: 4}); !errors.As(err, &pe) || pe.Condition != InsufficientStorage {
		t.Fatalf("adapted carry refusal condition: %v", err)
	}
	if _, _, err := ParseWithContext("12345", Context{}.WithBudget(Budget{MaxDigits: 3})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("precision-0 digit budget: %v", err)
	}
	var ce *Error
	if _, _, err := ParseToExponentWithBudget("x", 0, RoundingMode(9), Budget{MaxInputBytes: 0}); !errors.As(err, &ce) || ce.Code != ErrInvalidContext {
		t.Fatalf("unknown mode before syntax: %v", err)
	}
	if _, _, err := ParseToExponentWithBudget("xx", 0, RoundingMode(9), Budget{MaxInputBytes: 1}); !errors.As(err, &ce) || ce.Code != ErrInvalidContext {
		t.Fatalf("unknown mode before the input budget: %v", err)
	}
	if _, _, err := ParseToExponentWithBudget("x_y", 0, TiesToEven, Budget{MaxInputBytes: 2}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("input budget before syntax: %v", err)
	}
}

// TestParseWithContextTraps covers traps on the context target against
// the guarded oracle at ideal exponent E: the trapped conditions
// are exactly the oracle's conditions within the trap set, reported as an
// *Error beside the finite result and the remaining conditions.
func TestParseWithContextTraps(t *testing.T) {
	rng := rand.New(rand.NewPCG(48, 4))
	trapSets := []Conditions{Inexact, Underflow, Overflow | Subnormal, Rounded, Inexact | Rounded | Subnormal}
	for range 6000 {
		s := randomRoundingLiteral(rng)
		r, _ := new(big.Rat).SetString(s)
		parsed, _ := Parse(s)
		if r.Sign() == 0 {
			continue
		}
		p := int64(1 + rng.IntN(40))
		mode := allDivModes[rng.IntN(7)]
		emin := int64(rng.IntN(120) - 100)
		emax := emin + int64(rng.IntN(120))
		traps := trapSets[rng.IntN(len(trapSets))]
		ctx, err := NewContext(uint32(p), mode, &ExponentGuards{Emin: int32(emin), Emax: int32(emax)}, traps)
		if err != nil {
			t.Fatal(err)
		}
		want := oracleGuarded(r, int64(parsed.exponent()), p, emin, emax, mode)
		got, conditions, err := ParseWithContext(s, ctx)
		label := fmt.Sprintf("%q p=%d %v traps %v", s, p, mode, traps)
		selected := want.conditions & traps
		if selected == 0 {
			checkDivOutcome(t, label, got, conditions, err, want, r.Sign() < 0)
			continue
		}
		var ce *Error
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != selected || conditions != want.conditions&^selected {
			t.Fatalf("%s: (%v, %v, %v), want trapped %v", label, got, conditions, err, selected)
		}
		want.conditions &^= selected
		checkDivOutcome(t, label, got, conditions, nil, want, r.Sign() < 0)
	}
}

// TestParseRefusalsDoNotCopy checks that every
// resource refusal (ErrInsufficientStorage) of []byte text returns an
// *Error without copying the input, in every budgeted text entry
// point (ParseToExponentWithBudget, ParseWithContext under a budget,
// ParseJSONWithBudget, ScanWithBudget); a string
// keeps an *Error whose Input is the caller's own string. Each refusal of a
// 1 MiB input allocates at most its error value.
func TestParseRefusalsDoNotCopy(t *testing.T) {
	digits := []byte(strings.Repeat("7", 1<<20))
	quoted := append(append([]byte{'"'}, digits...), '"')
	ctx := Decimal128Context()
	boxed := any(digits) // boxed once, outside the measured calls
	byteCap, digitCap := Budget{MaxInputBytes: 1}, Budget{MaxDigits: 3}
	cases := map[string]func() error{
		"Parse/byte-cap":  func() error { _, _, err := ParseWithContext(digits, Context{}.WithBudget(byteCap)); return err },
		"Parse/digit-cap": func() error { _, _, err := ParseWithContext(digits, Context{}.WithBudget(digitCap)); return err },
		"ParseToExponent/byte-cap": func() error {
			_, _, err := ParseToExponentWithBudget(digits, 0, TiesToEven, byteCap)
			return err
		},
		"ParseToExponent/digit-cap": func() error {
			_, _, err := ParseToExponentWithBudget(digits, 0, TiesToEven, digitCap)
			return err
		},
		"ParseWithContext/byte-cap": func() error {
			_, _, err := ParseWithContext(digits, ctx.WithBudget(byteCap))
			return err
		},
		"ParseWithContext/digit-cap": func() error {
			_, _, err := ParseWithContext(digits, ctx.WithBudget(Budget{MaxDigits: 3}))
			return err
		},
		"ParseJSON/digit-cap": func() error { _, err := ParseJSONWithBudget(quoted, digitCap); return err },
		"Scan/digit-cap": func() error {
			var d Decimal
			return d.ScanWithBudget(boxed, Budget{MaxDigits: 3})
		},
	}
	for name, call := range cases {
		err := call()
		oe, ok := errors.AsType[*Error](err)
		if !ok || oe.Input != "" || !errors.Is(err, ErrInsufficientStorage) || oe.Condition != InsufficientStorage {
			t.Errorf("%s: %T (%v), want *Error/ErrInsufficientStorage", name, err, errors.Is(err, ErrInsufficientStorage))
			continue
		}
		if allocs := testing.AllocsPerRun(3, func() { _ = call() }); allocs > 1 {
			t.Errorf("%s: %v allocations for a refusal of 1 MiB", name, allocs)
		}
	}
	// A string keeps an *Error whose Input is the caller's own string.
	text := string(digits)
	_, _, err := ParseWithContext(text, Context{}.WithBudget(Budget{MaxDigits: 3}))
	if pe, ok := errors.AsType[*Error](err); !ok || pe.Input != text || !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("string refusal: %T", err)
	}
	if allocs := testing.AllocsPerRun(3, func() { _, _, _ = ParseWithContext(text, Context{}.WithBudget(Budget{MaxDigits: 3})) }); allocs > 1 {
		t.Fatalf("string refusal allocated %v times", allocs)
	}
}

// TestMustParsePanicsWithParseError checks that MustParse returns
// Parse's value for a valid literal and otherwise panics with exactly the
// error Parse returns (same dynamic type, identity and fields), for string
// and []byte input and every refusal class a test can build: syntax, int32
// exponent range, and the checked resource refusal through the shared
// parseFailure carrier (Input set for a string, empty for bytes,
// which ParseWithContext under a budget exercises). An unbudgeted resource refusal needs
// more than 2^61 digits on 64-bit targets, which no test can allocate;
// MustParse reaches it through the same Parse call.
func TestMustParsePanicsWithParseError(t *testing.T) {
	panicOf := func(f func()) (recovered any) {
		defer func() { recovered = recover() }()
		f()
		return nil
	}
	for _, text := range []string{"bad", "1e2147483648", "1.2.3"} {
		_, want := Parse(text)
		got := panicOf(func() { MustParse(text) })
		if got == nil || fmt.Sprintf("%#v", got) != fmt.Sprintf("%#v", want) {
			t.Fatalf("MustParse(%q) panicked with %#v, Parse returned %#v", text, got, want)
		}
		_, wantBytes := Parse([]byte(text))
		gotBytes := panicOf(func() { MustParse([]byte(text)) })
		if gotBytes == nil || fmt.Sprintf("%#v", gotBytes) != fmt.Sprintf("%#v", wantBytes) {
			t.Fatalf("MustParse([]byte(%q)) panicked with %#v, Parse returned %#v", text, gotBytes, wantBytes)
		}
	}
	if got := panicOf(func() { MustParse("12.50") }); got != nil {
		t.Fatalf("MustParse of a valid literal panicked: %v", got)
	}
	// The resource carriers MustParse would panic with.
	_, _, stringErr := ParseWithContext("123456", Context{}.WithBudget(Budget{MaxDigits: 2}))
	_, _, bytesErr := ParseWithContext([]byte("123456"), Context{}.WithBudget(Budget{MaxDigits: 2}))
	var pe *Error
	var oe *Error
	if !errors.As(stringErr, &pe) || !errors.Is(stringErr, ErrInsufficientStorage) || !errors.As(bytesErr, &oe) || !errors.Is(bytesErr, ErrInsufficientStorage) {
		t.Fatalf("resource carriers: string %T %v, bytes %T %v", stringErr, stringErr, bytesErr, bytesErr)
	}
}

// TestParseKeepsWrittenScale covers scale fidelity on parse (1.10 keeps
// scale 2, 1.1 scale 1), no trimming of parsed zeros (1.2300 re-emits bit
// for bit) and fixed-scale fields served by the generic contract (a
// fixed-scale plain field such as 1234.56 parses and re-emits
// at the schema's scale through Parse, Text, Fixed and Quantize alone).
// Coefficients and exponents are hand-derived; values are checked against
// math/big.Rat.
func TestParseKeepsWrittenScale(t *testing.T) {
	for _, tc := range []struct {
		input    string
		digits   string
		exponent int32
	}{
		{"1.10", "110", -2},
		{"1.1", "11", -1},
		{"1.2300", "12300", -4},
		{"1234.56", "123456", -2},
		{"1234.50", "123450", -2},
		{"0.000", "0", -3},
		{"-7.00", "700", -2},
	} {
		d, err := Parse(tc.input)
		if err != nil {
			t.Fatal(err)
		}
		text, err := d.Text(0)
		if err != nil || d.coefficientDigits() != tc.digits || d.Exponent() != tc.exponent || text != tc.input {
			t.Errorf("Parse(%q) = %s E%d, text %q, %v; want %s E%d re-emitted verbatim", tc.input, d.coefficientDigits(), d.Exponent(), text, err, tc.digits, tc.exponent)
		}
		want, _ := new(big.Rat).SetString(tc.input)
		got, _ := new(big.Rat).SetString(text)
		if want.Cmp(got) != 0 {
			t.Errorf("Parse(%q) changed the value to %s", tc.input, text)
		}
	}
	// A two-place field re-emitted at its schema scale with the generic
	// two-level contract: Fixed for display, Quantize for the stored scale.
	for _, tc := range []struct{ input, fixed string }{{"1234.56", "1234.56"}, {"1234.5", "1234.50"}, {"1234", "1234.00"}} {
		d := MustParse(tc.input)
		fixed, err := d.Fixed(2)
		if err != nil || fixed != tc.fixed {
			t.Errorf("%s.Fixed(2) = %q, %v; want %s", tc.input, fixed, err, tc.fixed)
		}
		q, c, err := d.Quantize(-2, Exact)
		if err != nil || c&Inexact != 0 || q.String() != tc.fixed || q.Exponent() != -2 {
			t.Errorf("%s.Quantize(-2, Exact) = %s, %v, %v; want %s", tc.input, q, c, err, tc.fixed)
		}
	}
}

// TestParseStrictGrammar pins four edges of the strict decimal grammar at
// the public entry points: empty input, a missing exponent, whitespace in
// the exponent and the uppercase E.
func TestParseStrictGrammar(t *testing.T) {
	for _, tc := range []struct{ name, input, want string }{
		{"empty", "", ""}, {"space exponent", "1e 2", ""}, {"tab exponent", "1e\t2", ""}, {"exponent", "12e3", "1.2E+4"}, {"uppercase", "12E3", "1.2E+4"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			d, err := Parse(tc.input)
			if tc.want == "" {
				if !errors.Is(err, ErrConversionSyntax) {
					t.Fatalf("want syntax, got %v %v", d, err)
				}
			} else if err != nil || d.String() != tc.want {
				t.Fatalf("want %s, got %v %v", tc.want, d, err)
			}
		})
	}
}

// TestParseAcceptedAndRejectedForms covers the carrier coverage matrix: every
// accepted
// carrier form (ISO 6093 NR1/NR2/NR3-shaped, XSD decimal lexical, JSON
// number, GDA numeric-string, FIX envelope, engine-rendered text) is a
// named case whose hand-derived coefficient, exponent and sign match Parse
// and whose value matches math/big.Rat; every rejected form class is a
// named case asserting ErrConversionSyntax through errors.Is and a
// *Error carrying the input.
func TestParseAcceptedAndRejectedForms(t *testing.T) {
	accepted := []struct {
		carrier, form, input, digits string
		exponent                     int32
		negative                     bool
	}{
		{"NR1", "unsigned integer", "123", "123", 0, false},
		{"NR1", "signed integer", "-123", "123", 0, true},
		{"NR1", "plus sign", "+123", "123", 0, false},
		{"NR1", "leading zeros", "000123", "123", 0, false},
		{"NR2", "point inside", "123.45", "12345", -2, false},
		{"NR2", "trailing point", "123.", "123", 0, false},
		{"NR2", "leading point", ".45", "45", -2, false},
		{"NR2", "signed fraction", "-0.50", "50", -2, true},
		{"NR3", "uppercase exponent", "1.23E+4", "123", 2, false},
		{"NR3", "unsigned exponent", "1.23E4", "123", 2, false},
		{"NR3", "negative exponent", "-1.5E-3", "15", -4, true},
		{"NR3", "signed mantissa and exponent", "+0.5E+03", "5", 2, false},
		{"XSD", "plus sign", "+5", "5", 0, false},
		{"XSD", "bare trailing point", "5.", "5", 0, false},
		{"XSD", "bare leading point", ".5", "5", -1, false},
		{"XSD", "negative zero", "-0.0", "0", -1, false},
		{"XSD", "leading and trailing zeros", "007.0100", "70100", -4, false},
		{"JSON", "zero", "0", "0", 0, false},
		{"JSON", "negative zero", "-0", "0", 0, false},
		{"JSON", "fraction", "0.001", "1", -3, false},
		{"JSON", "lowercase exponent", "1e10", "1", 10, false},
		{"JSON", "fraction and signed exponent", "-1.5e+3", "15", 2, true},
		{"JSON", "wide integer", "123456789012345678901234567890123456789012345", "123456789012345678901234567890123456789012345", 0, false},
		{"GDA", "scientific", "2.5e-3", "25", -4, false},
		{"GDA", "zero with exponent", "0.00E+3", "0", 1, false},
		{"GDA", "maximum exponent", "1E+2147483647", "1", 2147483647, false},
		{"GDA", "minimum exponent", "1E-2147483648", "1", -2147483648, false},
		{"GDA", "deep exponent digits", "1e+0000000007", "1", 7, false},
		{"FIX", "leading zeros", "00015.25", "1525", -2, false},
		{"FIX", "bare trailing point", "1500.", "1500", 0, false},
		{"FIX", "negative bare leading point", "-.5", "5", -1, true},
		{"engine", "PostgreSQL numeric scale", "123.4500", "1234500", -4, false},
		{"engine", "PostgreSQL small negative", "-0.000123", "123", -6, true},
		{"engine", "SQLite REAL", "1.0e+20", "10", 19, false},
		{"engine", "canonical scientific", "1.2345E+10", "12345", 6, false},
	}
	for _, tc := range accepted {
		t.Run("accept/"+tc.carrier+"/"+tc.form, func(t *testing.T) {
			d, err := Parse(tc.input)
			if err != nil || d.coefficientDigits() != tc.digits || d.exponent() != tc.exponent || d.negative() != tc.negative {
				t.Fatalf("Parse(%q) = %s E%d negative=%v, %v; want %s E%d negative=%v", tc.input, d.coefficientDigits(), d.exponent(), d.negative(), err, tc.digits, tc.exponent, tc.negative)
			}
			if tc.exponent > -100 && tc.exponent < 100 {
				want, ok := new(big.Rat).SetString(tc.input)
				if !ok || want.Cmp(inboundTextOracle(tc.digits, tc.exponent, tc.negative)) != 0 {
					t.Fatalf("math/big reads %q as %v, not %sE%d", tc.input, want, tc.digits, tc.exponent)
				}
			}
		})
	}
	rejected := []struct {
		class  string
		inputs []string
	}{
		{"whitespace", []string{" 1", "1 ", "1 000", "\t1", "1\n", "1e 2", "1 "}},
		{"underscore", []string{"1_000", "_1", "1e1_0"}},
		{"comma decimal mark", []string{"1,5", ",5", "1,5E+3"}},
		{"digit grouping", []string{"1,000", "1,000.00", "1'000", "1.000.000"}},
		{"hexadecimal", []string{"0x10", "0X1A", "0x1p4"}},
		{"empty", []string{""}},
		{"bare exponent", []string{"e5", "E5", "+e5", ".e5"}},
		{"incomplete exponent", []string{"1e", "1E+", "1e-", "1e2e3", "1d5"}},
		{"sign or point only", []string{"+", "-", ".", "+.", "-."}},
		{"repeated sign or point", []string{"+-1", "--1", "1.2.3", "..5"}},
		{"non-ASCII digits", []string{"١", "１", "1²"}},
		{"non-finite", []string{"NaN", "Infinity", "-Infinity", "sNaN", ".nan", ".inf"}},
		{"carrier framing", []string{`"1"`, "1%", "$1", "(1)", "1-", "\x001"}},
	}
	for _, tc := range rejected {
		t.Run("reject/"+tc.class, func(t *testing.T) {
			for _, input := range tc.inputs {
				_, err := Parse(input)
				var parseErr *Error
				if !errors.Is(err, ErrConversionSyntax) || !errors.As(err, &parseErr) || parseErr.Input != input {
					t.Errorf("Parse(%q) = %v; want *Error with ErrConversionSyntax", input, err)
				}
				if decimalGrammarOracle.MatchString(input) {
					t.Errorf("%q matches the independent grammar oracle; not a rejected form", input)
				}
			}
		})
	}
}

var sinkBoundedWork Decimal

// TestParseBoundedWork covers the bounded-work fault schedule.
// Each fixture runs as []byte under an explicit Budget:
//   - compact full-range exponents (1E+2147483647, 1E-2147483648, a
//     39-digit inline and a 100-digit slow coefficient at both ends) admit at
//     byte cap len and digit cap d with the exponent kept compact: inline
//     values allocate nothing and slow ones only their limbs, never
//     exponent-sized storage;
//   - a one-million-digit coefficient admits at cap d with allocation within
//     its limb plan, each limb matching strconv on its nine-digit group;
//   - deep exponent strings (100,000 leading exponent zeros) admit at
//     cap len with no allocation, and over-range deep exponents are
//     ErrExponentRange rather than a resource refusal;
//   - caps len-1 and d-1 refuse with *Error/ErrInsufficientStorage,
//     allocating only the error;
//   - ParseToExponentWithBudget growth of 1e2147483647 to exponent
//     -2147483648 (a 2^32-digit result) refuses before allocating it, and on
//     32-bit targets the unbudgeted form refuses by checked addressability.
//
// Oracles: exponents and digit counts are computed from the literal by
// strconv, coefficient limbs by strconv.ParseUint on each digit group.
func TestParseBoundedWork(t *testing.T) {
	slow100 := strings.Repeat("1234567890", 10)
	million := make([]byte, 1_000_000)
	rng := rand.New(rand.NewPCG(8, 1_000_000))
	for i := range million {
		million[i] = byte('0' + rng.IntN(10))
	}
	million[0] = '7'
	deepZeros := strings.Repeat("0", 100_000)
	for _, tc := range []struct {
		name       string
		input      string
		exponent   int32
		negative   bool
		digits     string // expected coefficient digits, most significant first
		allocLimit uint64 // admitted heap bytes
	}{
		{"max-exponent", "1E+2147483647", math.MaxInt32, false, "1", 0},
		{"min-exponent", "1E-2147483648", math.MinInt32, false, "1", 0},
		{"inline-39-max", "-" + strings.Repeat("1", 39) + "E+2147483647", math.MaxInt32, true, strings.Repeat("1", 39), 0},
		{"fraction-to-min", "-12.5E-2147483647", math.MinInt32, true, "125", 0},
		{"slow-100-max", slow100 + "E2147483647", math.MaxInt32, false, slow100, 2 * bigIntPage},
		{"slow-100-min", "0." + slow100 + "E-2147483548", math.MinInt32, false, slow100, 2 * bigIntPage},
		{"million-digits", string(million) + "E-2147483648", math.MinInt32, false, string(million), 2*bigIntPage + (4*111_112+bigIntPage-1)&^(bigIntPage-1)},
		{"deep-exponent", "1e+" + deepZeros + "7", 7, false, "1", 0},
		{"deep-full-range", "-9e-" + deepZeros + "2147483648", math.MinInt32, true, "9", 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			input := []byte(tc.input)
			d := uint64(len(tc.digits))
			exact := Budget{MaxInputBytes: uint64(len(input)), MaxDigits: d}
			got, _, err := ParseWithContext(input, Context{}.WithBudget(exact))
			if err != nil || got.exponent() != tc.exponent || got.negative() != tc.negative {
				t.Fatalf("exact budget: %+v, %v", got, err)
			}
			checkParsedDigits(t, got, tc.digits)
			used := coldAllocatedWithin(func() { sinkBoundedWork, _, _ = ParseWithContext(input, Context{}.WithBudget(exact)) }, tc.allocLimit)
			if used > tc.allocLimit {
				t.Fatalf("admitted parse allocated %d bytes, planned at most %d", used, tc.allocLimit)
			}
			for _, refuse := range []Budget{
				{MaxInputBytes: uint64(len(input)) - 1, MaxDigits: d},
				{MaxInputBytes: uint64(len(input)), MaxDigits: d - 1},
			} {
				if refuse.MaxDigits == 0 {
					continue // d-1 == 0 is no quota
				}
				got, _, err := ParseWithContext(input, Context{}.WithBudget(refuse))
				oe, ok := errors.AsType[*Error](err)
				if !ok || oe.Op != "ParseWithContext" || !errors.Is(err, ErrInsufficientStorage) ||
					oe.Condition != InsufficientStorage || !got.isZero() || got.exponent() != 0 {
					t.Fatalf("budget %+v: %+v, %v", refuse, got, err)
				}
				if allocs := testing.AllocsPerRun(5, func() { sinkBoundedWork, _, _ = ParseWithContext(input, Context{}.WithBudget(refuse)) }); allocs > 1 {
					t.Fatalf("budget %+v: refusal allocated %g times", refuse, allocs)
				}
			}
		})
	}
	for _, input := range []string{"1e+" + deepZeros + "2147483648", "1e-" + deepZeros + "2147483649"} {
		_, _, err := ParseWithContext(input, Context{}.WithBudget(Budget{MaxInputBytes: uint64(len(input)), MaxDigits: 1}))
		if !errors.Is(err, ErrExponentRange) || errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("over-range deep exponent: %v", err)
		}
	}
	growth := []byte("1e2147483647")
	grow := func() error {
		_, _, err := ParseToExponentWithBudget(growth, math.MinInt32, TiesToEven, Budget{MaxDigits: 1 << 30})
		return err
	}
	if err := grow(); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("budgeted 2^32-digit growth: %v", err)
	}
	if bytes := coldAllocatedWithin(func() { _ = grow() }, 256); bytes > 256 {
		t.Fatalf("budgeted growth refusal allocated %d bytes", bytes)
	}
	if bits.UintSize == 32 {
		unbounded := func() error { _, _, err := ParseToExponent(growth, math.MinInt32, TiesToEven); return err }
		if err := unbounded(); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("32-bit addressability: %v", err)
		}
		if bytes := coldAllocatedWithin(func() { _ = unbounded() }, 256); bytes > 256 {
			t.Fatalf("32-bit addressability refusal allocated %d bytes", bytes)
		}
	}
}

// checkParsedDigits compares got's coefficient with the expected digit
// string: inline words through strconv.ParseUint on the leading 19 digits
// and the remainder, slow limbs group by group.
func checkParsedDigits(t *testing.T, got Decimal, digits string) {
	t.Helper()
	if got.slow == nil {
		want, ok := new(big.Int).SetString(digits, 10)
		have := new(big.Int).Lsh(new(big.Int).SetUint64(got.words.hi), 64)
		have.Or(have, new(big.Int).SetUint64(got.words.lo))
		if !ok || have.Cmp(want) != 0 {
			t.Fatalf("inline coefficient %s, want %s", have, digits)
		}
		return
	}
	limbs := got.slow.limbs
	if want := (len(digits) + 8) / 9; len(limbs) != want {
		t.Fatalf("limb count %d, want %d", len(limbs), want)
	}
	end := len(digits)
	for i, limb := range limbs {
		start := max(end-9, 0)
		want, err := strconv.ParseUint(digits[start:end], 10, 32)
		if err != nil || uint64(limb) != want {
			t.Fatalf("limb %d = %d, want %s", i, limb, digits[start:end])
		}
		end = start
	}
}

// parseOracleGrammar is the literal grammar written independently of
// scanDecimal and parseInline.
var parseOracleGrammar = regexp.MustCompile(`^([+-]?)([0-9]*)(?:\.([0-9]*))?(?:[eE]([+-]?[0-9]+))?$`)

// parseOracleOutcome is a literal's expected parse outcome under a budget,
// derived with regexp, math/big and strconv only: the refusal code (nil on
// success), or the coefficient, exponent and sign of the result.
type parseOracleOutcome struct {
	code        error
	coefficient *big.Int
	exponent    int32
	negative    bool
	significant int
}

func parseOracle(s string, budget Budget) parseOracleOutcome {
	if budget.MaxInputBytes != 0 && uint64(len(s)) > budget.MaxInputBytes {
		return parseOracleOutcome{code: ErrInsufficientStorage}
	}
	m := parseOracleGrammar.FindStringSubmatch(s)
	if m == nil || m[2]+m[3] == "" {
		return parseOracleOutcome{code: ErrConversionSyntax}
	}
	exponent := new(big.Int)
	if m[4] != "" {
		exponent.SetString(strings.TrimPrefix(m[4], "+"), 10)
	}
	exponent.Sub(exponent, big.NewInt(int64(len(m[3]))))
	if !exponent.IsInt64() || exponent.Int64() < math.MinInt32 || exponent.Int64() > math.MaxInt32 {
		return parseOracleOutcome{code: ErrExponentRange}
	}
	digits := strings.TrimLeft(m[2]+m[3], "0")
	significant := max(len(digits), 1)
	if budget.MaxDigits != 0 && uint64(significant) > budget.MaxDigits {
		return parseOracleOutcome{code: ErrInsufficientStorage}
	}
	coefficient, _ := new(big.Int).SetString("0"+digits, 10)
	return parseOracleOutcome{
		coefficient: coefficient, exponent: int32(exponent.Int64()),
		negative: m[1] == "-" && coefficient.Sign() != 0, significant: significant,
	}
}

// parseInlinePins counts the literals checked by checkParseInline and how
// the fast path treated them; the counts are the test's, not production's.
type parseInlinePins struct {
	cases, fast, deferred, deferredValid, refused, fastZero, fastSigned, fastExponent, digitBudgetDeferred int
}

// checkParseInline pins parseWithBudget (with its inline fast path) to
// parseGeneral for both carriers, field for field and error for error, and
// both to the independent parseOracle; accepted values are also checked
// against big.Rat.SetString when their exponent is small.
func checkParseInline(t *testing.T, s string, budget Budget, pins *parseInlinePins) {
	want := parseOracle(s, budget)
	pins.cases++
	_, _, _, significant, inline := parseInline(s)
	fast := inline && (budget.MaxInputBytes == 0 || uint64(len(s)) <= budget.MaxInputBytes) &&
		(budget.MaxDigits == 0 || uint64(significant) <= budget.MaxDigits)
	switch {
	case fast:
		pins.fast++
		if want.code != nil || significant != want.significant {
			t.Fatalf("%q under %+v: fast path accepted %d digits, oracle %v with %d", s, budget, significant, want.code, want.significant)
		}
	case inline:
		pins.digitBudgetDeferred++ // a budget, not the grammar, defers it
		fallthrough
	default:
		pins.deferred++
	}
	if want.code != nil {
		pins.refused++
	} else if !fast {
		pins.deferredValid++ // 20+ digits, ten exponent digits, 31+ bytes
	}
	for _, carrier := range []string{"string", "bytes"} {
		var got, general Decimal
		var gotErr, generalErr error
		if carrier == "string" {
			got, gotErr = parseWithBudget(s, budget.text(), "ParseWithContext")
			general, generalErr = parseGeneral(s, budget.text(), "ParseWithContext")
		} else {
			got, gotErr = parseWithBudget([]byte(s), budget.text(), "ParseWithContext")
			general, generalErr = parseGeneral([]byte(s), budget.text(), "ParseWithContext")
		}
		if !sameParseFailure(gotErr, generalErr) || got.words != general.words || got.meta != general.meta ||
			(got.slow == nil) != (general.slow == nil) || got.slow != nil && !slices.Equal(got.slow.limbs, general.slow.limbs) {
			t.Fatalf("%s %q under %+v: (%+v %#x %v, %v) differs from the general path (%+v %#x %v, %v)", carrier, s, budget,
				got.words, uint64(got.meta), got.slow != nil, gotErr, general.words, uint64(general.meta), general.slow != nil, generalErr)
		}
		if want.code != nil {
			if !errors.Is(gotErr, want.code) {
				t.Fatalf("%s %q under %+v: error %v, oracle %v", carrier, s, budget, gotErr, want.code)
			}
			var pe *Error
			switch {
			case errors.As(gotErr, &pe) && (pe.Input != "" || s == ""):
				if pe.Op != "ParseWithContext" || pe.Input != s || !errors.Is(pe.Code, want.code) ||
					(want.code == ErrConversionSyntax) != (pe.Condition == ConversionSyntax) || (want.code == ErrExponentRange) != (pe.Condition == 0) {
					t.Fatalf("%s %q: Error %+v", carrier, s, pe)
				}
				if carrier == "bytes" && want.code == ErrInsufficientStorage {
					t.Fatalf("bytes %q: a resource refusal copied the input", s)
				}
			case carrier == "bytes" && want.code == ErrInsufficientStorage:
				var oe *Error
				if !errors.As(gotErr, &oe) || oe.Op != "ParseWithContext" || oe.Condition != InsufficientStorage {
					t.Fatalf("bytes %q: refusal %#v", s, gotErr)
				}
			default:
				t.Fatalf("%s %q: error %#v is not an *Error", carrier, s, gotErr)
			}
			continue
		}
		if gotErr != nil {
			t.Fatalf("%s %q under %+v: %v, oracle accepts", carrier, s, budget, gotErr)
		}
		coefficient := new(big.Int).Lsh(new(big.Int).SetUint64(got.words.hi), 64)
		coefficient.Or(coefficient, new(big.Int).SetUint64(got.words.lo))
		if got.slow != nil {
			coefficient.SetString(got.coefficientDigits(), 10)
		}
		if coefficient.Cmp(want.coefficient) != 0 || got.exponent() != want.exponent || got.negative() != want.negative {
			t.Fatalf("%s %q: got %s E%d negative=%v, oracle %s E%d negative=%v", carrier, s, coefficient, got.exponent(), got.negative(), want.coefficient, want.exponent, want.negative)
		}
	}
	if want.code == nil && fast {
		if want.coefficient.Sign() == 0 {
			pins.fastZero++
		}
		if want.negative {
			pins.fastSigned++
		}
		if strings.ContainsAny(s, "eE") {
			pins.fastExponent++
		}
		if want.exponent > -400 && want.exponent < 400 {
			rat, ok := new(big.Rat).SetString(s)
			value := new(big.Rat).SetInt(want.coefficient)
			scale := new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(max(want.exponent, -want.exponent))), nil))
			if want.exponent < 0 {
				value.Quo(value, scale)
			} else {
				value.Mul(value, scale)
			}
			if want.negative {
				value.Neg(value)
			}
			if !ok || rat.Cmp(value) != 0 {
				t.Fatalf("%q: big.Rat %v (ok=%v), oracle value %v", s, rat, ok, value)
			}
		}
	}
}

// sameParseFailure reports whether two parse-family errors are the same
// concrete type with equal fields (reflect.DeepEqual, without its cost).
func sameParseFailure(a, b error) bool {
	switch a := a.(type) {
	case nil:
		return b == nil
	case *Error:
		b, ok := b.(*Error)
		return ok && a != nil && b != nil && *a == *b
	}
	return reflect.DeepEqual(a, b)
}

// TestParseInlineMatchesGeneralPath pins the single-pass parse fast
// path to the general path (parseGeneral) and to independent oracles
// (regexp grammar with math/big coefficient and exponent, big.Rat value):
// every string up to six bytes over a grammar-stressing alphabet, random
// literals up to 45 bytes, and directed boundaries (19 and 20 digits,
// leading zeros past 19 digits, signed zeros, partial forms, nine and ten
// exponent digits, int32 exponent edges) under coefficient-digit budgets
// sig-1, sig, sig+1 and input budgets len-1, len. Fast-path and deferral
// counts must exceed floors, and the fast path allocates nothing.
func TestParseInlineMatchesGeneralPath(t *testing.T) {
	var pins parseInlinePins
	alphabet := []byte("019.+-eEx\"\\ ")
	var exhaustive func(prefix []byte)
	exhaustive = func(prefix []byte) {
		checkParseInline(t, string(prefix), Budget{}, &pins)
		if len(prefix) == 6 {
			return
		}
		for _, c := range alphabet {
			exhaustive(append(prefix, c))
		}
	}
	exhaustive(make([]byte, 0, 6))
	exhaustiveFast, exhaustiveDeferred := pins.fast, pins.deferred

	directed := []string{
		"9999999999999999999", "-9999999999999999999", "10000000000000000000", "18446744073709551615",
		"18446744073709551616", "99999999999999999999", "1844674407370955161.6", "1.8446744073709551616",
		"0000000000000000000000000001", "0.00000000000000000000000001", "00000000000.000000000000001234",
		"000000000000000000000000000000", "1000000000000000000", "1.000000000000000000", "100000000000000000.0",
		"-0.000", "-0", "+0", "-0e5", "0.0e-0000000003", "-.0", "-0.000e+000000009",
		"1.", ".5", "-.5", "+.5e1", "5.e3", ".", "+", "-", "e5", ".e5", "1e", "1e+", "1e-", "1.5e-3", "1.5E+3",
		"1e000000005", "1e0000000005", "1e999999999", "1e-999999999", "9.999999999999999999e-999999999",
		"1e2147483647", "1e2147483648", "1e-2147483648", "1e-2147483649", "1.5e2147483648", "15e-2147483647",
		"1e0002147483647", "12345678901234567890123456789", "123456789012345678901234567890",
		"1234567890123456789012345678901", "+1234.5678", "-1234.5678", "1_000", "1e5x", "x1", "1..2", "1.2.3",
		"--1", "+-1", "1e+-5", "1 ", " 1", "١", "1\x00", "0x10", "Inf", "NaN",
	}
	for digits := 1; digits <= 21; digits++ {
		for _, d := range []string{"1", "9", "0"} {
			body := "1" + strings.Repeat(d, digits-1)
			directed = append(directed, body, "-"+body, body[:digits/2]+"."+body[digits/2:], body+"e-7", "0."+body)
		}
	}
	rng := rand.New(rand.NewPCG(78, 1))
	literal := func() string {
		n := rng.IntN(46)
		b := make([]byte, n)
		for i := range b {
			switch r := rng.IntN(20); {
			case r < 13:
				b[i] = byte('0' + rng.IntN(10))
			case r < 15:
				b[i] = '0'
			default:
				b[i] = ".+-eEx "[rng.IntN(7)]
			}
		}
		return string(b)
	}
	for range 40000 {
		directed = append(directed, literal())
	}
	for range 20000 {
		// Well-formed literals with 1-21 digits, a point and an exponent.
		digits := randDigitString(rng, 1+rng.IntN(21))
		point := rng.IntN(len(digits) + 1)
		s := []string{"", "-", "+"}[rng.IntN(3)] + digits[:point] + "." + digits[point:]
		if rng.IntN(2) == 0 {
			s += "e" + []string{"", "-", "+"}[rng.IntN(3)] + strconv.Itoa(rng.IntN(2_000_000_000))
		}
		directed = append(directed, s)
	}
	for _, s := range directed {
		checkParseInline(t, s, Budget{}, &pins)
		if want := parseOracle(s, Budget{}); want.code == nil {
			for _, digits := range []int{want.significant - 1, want.significant, want.significant + 1} {
				if digits > 0 {
					checkParseInline(t, s, Budget{MaxDigits: uint64(digits)}, &pins)
				}
			}
		}
		for _, n := range []int{len(s) - 1, len(s)} {
			if n > 0 {
				checkParseInline(t, s, Budget{MaxInputBytes: uint64(n), MaxDigits: 19}, &pins)
			}
		}
	}
	t.Logf("exhaustive fast %d deferred %d; total %+v", exhaustiveFast, exhaustiveDeferred, pins)
	if exhaustiveFast < 10000 || exhaustiveDeferred < 3_000_000 || pins.fast < 60000 || pins.deferred < 3_200_000 ||
		pins.fastZero < 2000 || pins.fastSigned < 15000 || pins.fastExponent < 20000 || pins.digitBudgetDeferred < 20000 || pins.deferredValid < 20000 {
		t.Fatalf("vacuous coverage: %+v", pins)
	}

	for _, s := range []string{"1234.56", "-9999999999999999999", "1.2345E+5", "-0.000"} {
		b := []byte(s)
		if n := testing.AllocsPerRun(100, func() { _, _ = Parse(s) }); n != 0 {
			t.Errorf("Parse(%q) allocates %v", s, n)
		}
		if n := testing.AllocsPerRun(100, func() { _, _ = Parse(b) }); n != 0 {
			t.Errorf("Parse([]byte(%q)) allocates %v", s, n)
		}
	}
}

// randDigitString returns n random ASCII digits.
func randDigitString(rng *rand.Rand, n int) string {
	b := make([]byte, n)
	for i := range b {
		b[i] = byte('0' + rng.IntN(10))
	}
	return string(b)
}

// parseEither is a caller-side generic wrapper that forwards any text type
// through the exported Literal constraint.
func parseEither[T Literal](s T) (Decimal, error) { return Parse(s) }

// TestLiteralConstraintIsNameable checks that callers can name
// the parse constraint in their own generic code, and both carriers parse
// to the same cohort (strconv-independent hand-derived vector).
func TestLiteralConstraintIsNameable(t *testing.T) {
	type label string
	a, errA := parseEither("1.50")
	b, errB := parseEither([]byte("1.50"))
	c, errC := parseEither(label("1.50"))
	if errA != nil || errB != nil || errC != nil || !sameCohort(a, b) || !sameCohort(a, c) || a.String() != "1.50" {
		t.Fatalf("Literal wrapper: %v %v %v / %v %v %v", a, b, c, errA, errB, errC)
	}
}

// TestParseWithContextZeroPrecisionMatchesParse pins the one-pass
// precision-0 ParseWithContext to the rounding-source path and to
// Parse: over valid, invalid, out-of-range and budget-refused literals, in
// both carriers, the value, cohort, error code, condition and input match;
// a vacuity guard requires every outcome class.
func TestParseWithContextZeroPrecisionMatchesParse(t *testing.T) {
	r := rand.New(rand.NewPCG(87, 1))
	inputs := []string{"0", "-0.00", "1.50", "1e2147483647", "1e2147483648", "0e99999999999", "1e-99999999999",
		"", "x", "1_0", "NaN", "+.5", "12345678901234567890123456789012345678901234567890", "9E-2147483648"}
	for range 3000 {
		var b strings.Builder
		for range 1 + r.IntN(60) {
			b.WriteByte("0123456789.eE+-_x"[r.IntN(17)])
		}
		inputs = append(inputs, b.String())
	}
	budgets := []Budget{{}, {MaxDigits: 3}, {MaxInputBytes: 5}, {MaxDigits: 40, MaxInputBytes: 64}}
	classes := map[string]int{}
	for _, s := range inputs {
		for _, budget := range budgets {
			for _, carrier := range []string{"string", "bytes"} {
				var got, want Decimal
				var gotErr, wantErr error
				var c Conditions
				if carrier == "string" {
					got, c, gotErr = ParseWithContext(s, Context{}.WithBudget(budget))
					want, wantErr = parseReferenceZeroPrecision(s, budget)
				} else {
					got, c, gotErr = ParseWithContext([]byte(s), Context{}.WithBudget(budget))
					want, wantErr = parseReferenceZeroPrecision([]byte(s), budget)
				}
				if c != 0 || !sameCohort(got, want) || (gotErr == nil) != (wantErr == nil) {
					t.Fatalf("%s %q %+v: (%v, %v, %v), reference (%v, %v)", carrier, s, budget, got, c, gotErr, want, wantErr)
				}
				if gotErr == nil {
					classes["ok"]++
					continue
				}
				var g, w *Error
				if !errors.As(gotErr, &g) || !errors.As(wantErr, &w) || g.Code != w.Code || g.Condition != w.Condition || g.Input != w.Input || g.Op != "ParseWithContext" {
					t.Fatalf("%s %q %+v: error %#v, reference %#v", carrier, s, budget, gotErr, wantErr)
				}
				classes[g.Code.text()]++
			}
		}
	}
	for _, class := range []string{"ok", "conversion syntax", "exponent out of range", "insufficient storage"} {
		if classes[class] < 10 {
			t.Fatalf("vacuous differential: %q seen %d times: %v", class, classes[class], classes)
		}
	}
}

// parseReferenceZeroPrecision is the two-pass reference for precision 0: the
// rounding-source scan, then the exact parse.
func parseReferenceZeroPrecision[T Literal](s T, budget Budget) (Decimal, error) {
	const op = "ParseWithContext"
	src, err := scanRoundingSource(s, budget.text(), op)
	if err != nil {
		return Decimal{}, err
	}
	if e := src.parts.exponent; e < math.MinInt32 || e > math.MaxInt32 {
		return Decimal{}, parseFailure(s, op, ErrExponentRange, 0)
	}
	return parseWithBudget(s, textLimits{MaxDigits: budget.MaxDigits}, op)
}

// straddleSwitchLimbs is the reference for fillCoefficientLimbs: every limb is the nine-digit window [end-9, end) of the joined
// spans, classified by a three-way switch on the decimal point.
func straddleSwitchLimbs[T Literal](limbs []uint32, parts decimalParts[T]) {
	split := len(parts.integral)
	end := split + len(parts.fraction)
	for i := range limbs {
		start := max(end-9, 0)
		switch {
		case end <= split:
			limbs[i] = digitGroup(parts.integral[start:end])
		case start >= split:
			limbs[i] = digitGroup(parts.fraction[start-split : end-split])
		default:
			high, low := digitGroup(parts.integral[start:]), digitGroup(parts.fraction[:end-split])
			limbs[i] = high*decimalPowers[end-split] + low
		}
		end = start
	}
}

// longLiteralDigits returns n random digits, sometimes with a run of
// leading zeros, and now and then all nines (carries) or all zeros.
func longLiteralDigits(rng *rand.Rand, n int) string {
	switch rng.IntN(8) {
	case 0:
		return strings.Repeat("9", n)
	case 1:
		return strings.Repeat("0", n)
	}
	b := []byte(randDigitString(rng, n))
	for i := range min(rng.IntN(12), n) * rng.IntN(2) {
		b[i] = '0'
	}
	return string(b)
}

// TestFillCoefficientLimbsMatchesStraddleSwitch pins the split-loop
// limb conversion (full groups by nineDigits, one straddle limb) to the
// straddle-switch reference and to math/big: for integral and
// fraction spans of 0-130 digits at every limb count up to the full one
// (the full count is Parse's; shorter counts are the rounding prefixes),
// in both carriers. Long literals (40-300 digits, every point placement,
// signs, exponents near the int32 limits, syntax defects) then run through
// checkParseInline under digit and input budgets that refuse and admit,
// pinning parseWithBudget's length guard and the limb band to
// parseGeneral, the regexp/math/big oracle and the Error identity rules;
// and ParseToExponent over them must equal Parse then Quantize in every
// mode. Vacuity guards count straddles, slow results and refusals.
func TestFillCoefficientLimbsMatchesStraddleSwitch(t *testing.T) {
	rng := rand.New(rand.NewPCG(88, 1))
	billion := big.NewInt(1_000_000_000)
	var spans, straddles, fullGroups int
	for range 20000 {
		integral := longLiteralDigits(rng, rng.IntN(131))
		fraction := longLiteralDigits(rng, rng.IntN(131))
		if rng.IntN(4) == 0 {
			fraction = fraction[:rng.IntN(len(fraction)+1)]
		}
		total := len(integral) + len(fraction)
		if total == 0 {
			continue
		}
		spans++
		if len(fraction)%9 != 0 && len(integral) != 0 {
			straddles++
		}
		if total >= 81 {
			fullGroups++
		}
		full := 1 + (total-1)/9
		for count := 1; count <= full; count++ {
			got, want := make([]uint32, count), make([]uint32, count)
			fillCoefficientLimbs(got, decimalParts[string]{integral: integral, fraction: fraction})
			straddleSwitchLimbs(want, decimalParts[string]{integral: integral, fraction: fraction})
			gotBytes := make([]uint32, count)
			fillCoefficientLimbs(gotBytes, decimalParts[[]byte]{integral: []byte(integral), fraction: []byte(fraction)})
			if !slices.Equal(got, want) || !slices.Equal(gotBytes, want) {
				t.Fatalf("%q.%q count %d: %v / bytes %v, reference %v", integral, fraction, count, got, gotBytes, want)
			}
			if count != full {
				continue
			}
			value := new(big.Int)
			for i := count - 1; i >= 0; i-- {
				if got[i] >= 1_000_000_000 {
					t.Fatalf("%q.%q: limb %d = %d", integral, fraction, i, got[i])
				}
				value.Mul(value, billion).Add(value, big.NewInt(int64(got[i])))
			}
			oracle, _ := new(big.Int).SetString("0"+integral+fraction, 10)
			if value.Cmp(oracle) != 0 {
				t.Fatalf("%q.%q: limbs %v, math/big %s", integral, fraction, got, oracle)
			}
		}
	}

	var pins parseInlinePins
	var slow, rounded int
	exponents := []string{"", "e0", "E+7", "e-7", "e2147483647", "e-2147483648", "e2147483900", "e-2147483400",
		"e2147483648", "e-2147483649", "e+0000000000000003", "e-999999999999999999999"}
	for range 10000 {
		digits := longLiteralDigits(rng, 40+rng.IntN(261))
		if rng.IntN(3) == 0 {
			digits = "1" + digits // a nonzero lead keeps the limb band
		}
		point := rng.IntN(len(digits) + 2)
		body := digits
		if point <= len(digits) {
			body = digits[:point] + "." + digits[point:]
		}
		s := []string{"", "-", "+"}[rng.IntN(3)] + body + exponents[rng.IntN(len(exponents))]
		if rng.IntN(10) == 0 { // a syntax defect anywhere
			b := []byte(s)
			b[rng.IntN(len(b))] = ".eE+-x "[rng.IntN(7)]
			s = string(b)
		}
		want := parseOracle(s, Budget{})
		checkParseInline(t, s, Budget{}, &pins)
		for _, n := range []int{len(s) - 1, len(s)} {
			checkParseInline(t, s, Budget{MaxInputBytes: uint64(n)}, &pins)
		}
		if want.code != nil {
			continue
		}
		for _, d := range []int{want.significant - 1, want.significant} {
			if d > 0 {
				checkParseInline(t, s, Budget{MaxDigits: uint64(d)}, &pins)
			}
		}
		parsed, err := Parse(s)
		if err != nil {
			t.Fatalf("%q: %v", s, err)
		}
		if parsed.slow != nil {
			slow++
		}
		if parsed.exponent() > math.MaxInt32-400 || parsed.exponent() < math.MinInt32+400 {
			continue
		}
		target := parsed.exponent() + int32(1+rng.IntN(want.significant+2))
		mode := allDivModes[rng.IntN(len(allDivModes))]
		q, qc, qe := parsed.Quantize(target, mode)
		for _, b := range []bool{false, true} {
			var d Decimal
			var c Conditions
			var e error
			if b {
				d, c, e = ParseToExponent([]byte(s), target, mode)
			} else {
				d, c, e = ParseToExponent(s, target, mode)
			}
			if errorIdentity(e) != errorIdentity(qe) || qe == nil && (!d.Equal(q) || d.exponent() != q.exponent() || c != qc) {
				t.Fatalf("%q at %d %v: (%v, %v, %v), Parse then Quantize (%v, %v, %v)", s, target, mode, d, c, e, q, qc, qe)
			}
		}
		rounded++
	}
	t.Logf("spans %d straddles %d fullGroups %d; slow %d rounded %d; %+v", spans, straddles, fullGroups, slow, rounded, pins)
	if spans < 19000 || straddles < 10000 || fullGroups < 5000 || slow < 3000 || rounded < 3000 ||
		pins.refused < 6000 || pins.deferredValid < 10000 || pins.fast != 0 {
		t.Fatalf("vacuous coverage: spans %d straddles %d fullGroups %d slow %d rounded %d %+v", spans, straddles, fullGroups, slow, rounded, pins)
	}
}

// shortLiteral draws a literal of at most 30 bytes: signs, runs of zeros,
// nines and fives, an optional point and exponent, and now and then a
// stray byte.
func shortLiteral(rng *rand.Rand) string {
	var b strings.Builder
	switch rng.IntN(6) {
	case 0:
		b.WriteByte('-')
	case 1:
		b.WriteByte('+')
	}
	digit := func(n int) {
		for range n {
			switch rng.IntN(6) {
			case 0:
				b.WriteByte('0')
			case 1:
				b.WriteByte('9')
			case 2:
				b.WriteByte('5')
			default:
				b.WriteByte(byte('0' + rng.IntN(10)))
			}
		}
	}
	digit(rng.IntN(12))
	if rng.IntN(3) != 0 {
		b.WriteByte('.')
		digit(rng.IntN(12))
	}
	if rng.IntN(5) == 0 {
		b.WriteByte("eE"[rng.IntN(2)])
		if rng.IntN(2) == 0 {
			b.WriteByte("+-"[rng.IntN(2)])
		}
		switch rng.IntN(4) {
		case 0:
			b.WriteString("400")
		case 1:
			b.WriteString("6144")
		case 2:
			b.WriteString("2147483647")
		default:
			digit(1 + rng.IntN(2))
		}
	}
	if rng.IntN(40) == 0 {
		b.WriteByte('x')
	}
	return b.String()
}

// TestParseRoundingInlineMatchesGeneral pins the short-literal paths of
// ParseToExponent and ParseWithContext to the rounding-source path and to
// Parse followed by Quantize, with the conditions and every refusal.
func TestParseRoundingInlineMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(23, 29))
	contexts := []Context{Decimal32Context(), Decimal64Context(), Decimal128Context()}
	for _, mode := range []RoundingMode{TiesAwayFromZero, TowardZero, Exact} {
		c, err := NewContext(9, mode, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		contexts = append(contexts, c)
		c, err = NewContext(5, mode, &ExponentGuards{Emin: -10, Emax: 12}, Inexact|Subnormal)
		if err != nil {
			t.Fatal(err)
		}
		contexts = append(contexts, c, c.WithBudget(Budget{MaxDigits: 4}), c.WithBudget(Budget{MaxInputBytes: 9}))
	}
	taken, errs, plain := 0, 0, 0
	for range 100000 {
		s := shortLiteral(rng)
		target := int32(rng.IntN(31) - 20)
		mode := RoundingMode(rng.IntN(8))
		if p, perr := Parse(s); perr == nil && int64(p.Exponent())-int64(target) > 60 {
			// A far target pads that many zeros on either path: the short
			// path defers there (inlineScale stops at 10^38).
			target = p.Exponent() - int32(rng.IntN(60))
		}
		got, gc, gerr := ParseToExponent(s, target, mode)
		// A never-binding digit cap keeps the call on the rounding source.
		want, wc, werr := parseToExponent(s, target, mode, textLimits{MaxDigits: 1 << 62}, "ParseToExponent")
		if werr != nil {
			errs++
		}
		requireSameOutcome(t, "ParseToExponent", s, got, gc, gerr, want, wc, werr)
		if p, perr := Parse(s); perr == nil && gerr == nil {
			q, qc, qerr := p.Quantize(target, mode)
			requireSameOutcome(t, "Parse+Quantize", s, got, gc, gerr, q, qc, qerr)
			taken++
		}
		gotB, gcB, gerrB := ParseToExponent([]byte(s), target, mode)
		requireSameOutcome(t, "ParseToExponent[]byte", s, gotB, gcB, gerrB, got, gc, gerr)

		ctx := contexts[rng.IntN(len(contexts))]
		got, gc, gerr = ParseWithContext(s, ctx)
		want, wc, werr = parseRounded(s, ctx, textLimits{MaxInputBytes: ctx.inputBytes, MaxDigits: ctx.arith.MaxDigits}, "ParseWithContext")
		requireSameOutcome(t, "ParseWithContext", s, got, gc, gerr, want, wc, werr)
		if gerr == nil && gc == 0 {
			plain++
		}
	}
	if taken < 25000 || errs < 250 || plain < 12000 {
		t.Fatalf("vacuous path coverage: %d taken, %d errors, %d plain", taken, errs, plain)
	}
}
