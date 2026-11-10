// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"math"
	"math/big"
	"math/bits"
	"math/rand"
	"reflect"
	"runtime"
	"runtime/debug"
	"strconv"
	"strings"
	"sync"
	"testing"
)

func TestFromInt64ExactExponentZero(t *testing.T) {
	cases := []struct {
		name  string
		input int64
		want  string
	}{
		{"zero", 0, "0"},
		{"one", 1, "1"},
		{"negative_one", -1, "-1"},
		{"spec_12345", 12345, "12345"},
		{"minimum", math.MinInt64, "-9223372036854775808"},
		{"maximum", math.MaxInt64, "9223372036854775807"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := FromInt64(tc.input)
			checkFixedIntegerConstructor(t, got, tc.want)
		})
	}
}

func TestFromUint64ExactExponentZero(t *testing.T) {
	cases := []struct {
		name  string
		input uint64
		want  string
	}{
		{"zero", 0, "0"},
		{"one", 1, "1"},
		{"signed_maximum", math.MaxInt64, "9223372036854775807"},
		{"high_bit", uint64(math.MaxInt64) + 1, "9223372036854775808"},
		{"maximum", math.MaxUint64, "18446744073709551615"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := FromUint64(tc.input)
			checkFixedIntegerConstructor(t, got, tc.want)
		})
	}
}

// TestFromUint64CanonicalPublication pins the unsigned factory to
// independent uint64 text, including its zero metadata and inline carrier.
func TestFromUint64CanonicalPublication(t *testing.T) {
	values := []uint64{0, 1, math.MaxInt64, uint64(math.MaxInt64) + 1, math.MaxUint64}
	r := rand.New(rand.NewSource(20261001))
	for range 4096 {
		values = append(values, r.Uint64())
	}
	for _, value := range values {
		got := FromUint64(value)
		if got.words != (uint128{lo: value}) || got.exponent() != 0 || got.negative() || got.slow != nil || !got.validRepresentation() {
			t.Fatalf("FromUint64(%d) published words=%#v exponent=%d negative=%v slow=%v", value, got.words, got.exponent(), got.negative(), got.slow)
		}
		want := strconv.FormatUint(value, 10)
		checkFixedIntegerConstructor(t, got, want)
		copied := got
		if !sameRepresentation(got, copied) || copied.String() != want {
			t.Fatalf("FromUint64(%d) copy changed its representation or value", value)
		}
	}
}

var fixedUint64ConstructorResult Decimal

// TestFromUint64PublicationAllocation retains the public factory's result
// as its benchmark does; inline construction must allocate nothing.
func TestFromUint64PublicationAllocation(t *testing.T) {
	values := [...]uint64{0, 1, math.MaxInt64, uint64(math.MaxInt64) + 1, math.MaxUint64}
	i := 0
	allocs := testing.AllocsPerRun(1000, func() {
		fixedUint64ConstructorResult = FromUint64(values[i])
		i = (i + 1) % len(values)
	})
	if allocs != 0 {
		t.Fatalf("retained FromUint64 result allocated %v times; want 0", allocs)
	}
	want := values[(i+len(values)-1)%len(values)]
	if fixedUint64ConstructorResult.words != (uint128{lo: want}) || fixedUint64ConstructorResult.exponent() != 0 || fixedUint64ConstructorResult.negative() || fixedUint64ConstructorResult.slow != nil {
		t.Fatal("retained allocation result lost its canonical inline representation")
	}
}

func TestFixedWidthConstructorCopyAndConcurrentRead(t *testing.T) {
	values := []struct {
		value Decimal
		want  string
	}{
		{FromInt64(math.MinInt64), "-9223372036854775808"},
		{FromUint64(math.MaxUint64), "18446744073709551615"},
	}
	var workers sync.WaitGroup
	for _, tc := range values {
		original, copied := tc.value, tc.value
		for range 8 {
			workers.Go(func() {
				for range 100 {
					for _, value := range []Decimal{original, copied} {
						got, err := value.Text(0)
						if err != nil || got != tc.want {
							t.Errorf("concurrent copied Text(0) = %q, %v; want %q", got, err, tc.want)
							return
						}
					}
				}
			})
		}
	}
	workers.Wait()
}

func checkFixedIntegerConstructor(t *testing.T, got Decimal, want string) {
	t.Helper()
	if got.exponent() != 0 {
		t.Fatalf("exponent = %d, want 0", got.exponent())
	}
	text, err := got.Text(0)
	if err != nil {
		t.Fatalf("Text(0): %v", err)
	}
	wantInteger, ok := new(big.Int).SetString(want, 10)
	if !ok {
		t.Fatalf("invalid oracle %q", want)
	}
	actualInteger, ok := new(big.Int).SetString(text, 10)
	if !ok || actualInteger.Cmp(wantInteger) != 0 || text != want {
		t.Fatalf("Text(0) = %q, want %q", text, want)
	}
	if wantInteger.Sign() != got.Sign() {
		t.Fatalf("Sign() = %d, want %d", got.Sign(), wantInteger.Sign())
	}
	if got.IsZero() && got.negative() {
		t.Fatal("zero retains a negative sign")
	}
}

func TestInt64ReturnsExactNumericValue(t *testing.T) {
	for _, tc := range []struct {
		text string
		want int64
	}{
		{"1.00", 1},
		{"100E-2", 1},
		{"-9223372036854775808", -9223372036854775808},
		{"9223372036854775807", 9223372036854775807},
		{"0E2147483647", 0},
		{"0E-2147483648", 0},
	} {
		got, err := MustParse(tc.text).Int64()
		if err != nil || got != tc.want {
			t.Fatalf("Int64(%q) = %d, %v; want %d, nil", tc.text, got, err, tc.want)
		}
	}
}

func TestInt64RejectsFractionBeforeRange(t *testing.T) {
	for _, input := range []string{"1.1", "9223372036854775808.1", "1E-2147483648", "-999E-2"} {
		got, err := MustParse(input).Int64()
		var operation *Error
		if got != 0 || !errors.Is(err, ErrNonIntegral) || !errors.As(err, &operation) || operation.Op != "Int64" || operation.Condition != 0 {
			t.Fatalf("Int64(%q) = %d, %v; want zero and conditionless NonIntegral", input, got, err)
		}
	}
}

func TestInt64RejectsIntegralOverflow(t *testing.T) {
	for _, input := range []string{"9223372036854775808", "-9223372036854775809", "1E2147483647"} {
		got, err := MustParse(input).Int64()
		var operation *Error
		if got != 0 || !errors.Is(err, ErrIntegerRange) || !errors.As(err, &operation) || operation.Op != "Int64" || operation.Condition != 0 {
			t.Fatalf("Int64(%q) = %d, %v; want zero and conditionless IntegerRange", input, got, err)
		}
	}
}

func TestUint64ReturnsExactNumericValue(t *testing.T) {
	for _, tc := range []struct {
		text string
		want uint64
	}{
		{"1.00", 1},
		{"100E-2", 1},
		{"9223372036854775808", 9223372036854775808},
		{"18446744073709551615", 18446744073709551615},
		{"0E2147483647", 0},
		{"0E-2147483648", 0},
	} {
		got, err := MustParse(tc.text).Uint64()
		if err != nil || got != tc.want {
			t.Fatalf("Uint64(%q) = %d, %v; want %d, nil", tc.text, got, err, tc.want)
		}
	}
}

func TestUint64RejectsFractionBeforeRange(t *testing.T) {
	for _, input := range []string{"-0.1", "-18446744073709551616.1", "1E-2147483648"} {
		got, err := MustParse(input).Uint64()
		var operation *Error
		if got != 0 || !errors.Is(err, ErrNonIntegral) || !errors.As(err, &operation) || operation.Op != "Uint64" || operation.Condition != 0 {
			t.Fatalf("Uint64(%q) = %d, %v; want zero and conditionless NonIntegral", input, got, err)
		}
	}
}

func TestUint64RejectsIntegralOverflow(t *testing.T) {
	for _, input := range []string{"-1", "18446744073709551616", "1E2147483647"} {
		got, err := MustParse(input).Uint64()
		var operation *Error
		if got != 0 || !errors.Is(err, ErrIntegerRange) || !errors.As(err, &operation) || operation.Op != "Uint64" || operation.Condition != 0 {
			t.Fatalf("Uint64(%q) = %d, %v; want zero and conditionless IntegerRange", input, got, err)
		}
	}
}

func TestFixedIntegerEgressAgainstBigIntegerOracle(t *testing.T) {
	coefficients := []string{
		"0", "1", "-1", "9", "-9", "100000000000000000000000000000",
		"9223372036854775807", "9223372036854775808", "-9223372036854775808",
		"-9223372036854775809", "18446744073709551615", "18446744073709551616",
		"1234567890123456789012345678901234567890",
	}
	exponents := []int{-25, -20, -9, -2, -1, 0, 1, 2, 9, 20, 25}
	for _, coefficient := range coefficients {
		for _, exponent := range exponents {
			input := coefficient + "E" + strconv.Itoa(exponent)
			d := MustParse(input)
			want, _ := new(big.Int).SetString(coefficient, 10)
			integral := true
			factor := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(absTestExponent(exponent))), nil)
			if exponent < 0 {
				quotient, remainder := new(big.Int), new(big.Int)
				quotient.QuoRem(want, factor, remainder)
				integral = remainder.Sign() == 0
				want = quotient
			} else {
				want.Mul(want, factor)
			}
			gotSigned, signedErr := d.Int64()
			gotUnsigned, unsignedErr := d.Uint64()
			if !integral {
				if gotSigned != 0 || gotUnsigned != 0 || !errors.Is(signedErr, ErrNonIntegral) || !errors.Is(unsignedErr, ErrNonIntegral) {
					t.Fatalf("%s: fractional oracle, got Int64=(%d,%v) Uint64=(%d,%v)", input, gotSigned, signedErr, gotUnsigned, unsignedErr)
				}
				continue
			}
			if want.IsInt64() {
				if signedErr != nil || gotSigned != want.Int64() {
					t.Fatalf("%s: Int64=(%d,%v), oracle=%s", input, gotSigned, signedErr, want)
				}
			} else if gotSigned != 0 || !errors.Is(signedErr, ErrIntegerRange) {
				t.Fatalf("%s: Int64=(%d,%v), oracle range refusal", input, gotSigned, signedErr)
			}
			if want.Sign() >= 0 && want.BitLen() <= 64 {
				if unsignedErr != nil || gotUnsigned != want.Uint64() {
					t.Fatalf("%s: Uint64=(%d,%v), oracle=%s", input, gotUnsigned, unsignedErr, want)
				}
			} else if gotUnsigned != 0 || !errors.Is(unsignedErr, ErrIntegerRange) {
				t.Fatalf("%s: Uint64=(%d,%v), oracle range refusal", input, gotUnsigned, unsignedErr)
			}
		}
	}
}

func absTestExponent(exponent int) int {
	if exponent < 0 {
		return -exponent
	}
	return exponent
}

// isZeroValue reports whether d is the Decimal{} zero value field by field;
// Decimal is deliberately not comparable.
func isZeroValue(d Decimal) bool {
	return d.words == (uint128{}) && d.exponent() == 0 && !d.negative() && d.slow == nil
}

func bigIntFixture(t *testing.T, text string) *big.Int {
	t.Helper()
	x, ok := new(big.Int).SetString(text, 10)
	if !ok {
		t.Fatalf("invalid fixture %q", text)
	}
	return x
}

// bigIntIngressOracle derives the conservative digit envelope U and work
// envelope W with arbitrary-precision arithmetic, independently of the
// checked uint64 quotient/remainder implementation.
func bigIntIngressOracle(t *testing.T, x *big.Int) (uint64, uint64) {
	t.Helper()
	if x.Sign() == 0 {
		return 1, 1
	}
	u := new(big.Int).Mul(big.NewInt(int64(x.BitLen())), big.NewInt(30103))
	u.Div(u, big.NewInt(100000)).Add(u, big.NewInt(1))
	tiles := new(big.Int).Add(u, big.NewInt(8))
	tiles.Div(tiles, big.NewInt(9)).Mul(tiles, big.NewInt(2))
	w := new(big.Int).Mul(tiles, tiles)
	w.Add(w, tiles)
	if !u.IsUint64() || !w.IsUint64() {
		t.Fatal("oracle fixture overflow")
	}
	return u.Uint64(), w.Uint64()
}

// checkIngressError asserts a failed FromBigInt call: Decimal{} and an
// *Error with the given cause and condition.
func checkIngressError(t *testing.T, got Decimal, err error, op string, code ErrorCode, condition Conditions) {
	t.Helper()
	var operation *Error
	if !isZeroValue(got) || !errors.Is(err, code) || !errors.As(err, &operation) ||
		operation.Op != op || operation.Condition != condition {
		t.Fatalf("got (%+v, %v), want Decimal{} and %s/%v/%v", got, err, op, code, condition)
	}
}

// checkEgressError asserts a failed BigInt call: nil and an exact-method
// *Error with the given cause and condition.
func checkEgressError(t *testing.T, got *big.Int, err error, op string, code ErrorCode, condition Conditions) {
	t.Helper()
	var operation *Error
	if got != nil || !errors.Is(err, code) || !errors.As(err, &operation) ||
		operation.Op != op || operation.Condition != condition {
		t.Fatalf("got (%v, %v), want nil and %s/%v/%v", got, err, op, code, condition)
	}
}

// bigIntEgressOracle computes coefficient×10^exponent with math/big and
// reports whether the value is integral.
func bigIntEgressOracle(t *testing.T, coefficient string, exponent int) (*big.Int, bool) {
	t.Helper()
	want := bigIntFixture(t, coefficient)
	if exponent >= 0 {
		return want.Mul(want, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(exponent)), nil)), true
	}
	divisor := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(-exponent)), nil)
	quotient, remainder := new(big.Int), new(big.Int)
	quotient.QuoRem(want, divisor, remainder)
	return quotient, remainder.Sign() == 0
}

type bigIntIngressCall struct {
	name string
	fn   func(*big.Int) (Decimal, error)
}

// bigIntIngressCalls pairs the bare constructor with a budgeted call whose
// quotas are restrictive for every nonzero source.
var bigIntIngressCalls = []bigIntIngressCall{
	{"FromBigInt", FromBigInt},
	{"FromBigIntWithBudget", func(x *big.Int) (Decimal, error) {
		return FromBigIntWithBudget(x, Budget{MaxInputDigits: 1, MaxDigits: 1, MaxWork: 1})
	}},
}

// TestFromBigIntOwnsExactScaleZeroResult checks that big integer ingress
// owns an exact scale-zero result: a negative multiword source converts exactly
// at exponent zero through both forms, and later mutation of the source or its
// Bits slice cannot reach the result; zero is canonical and nil is
// ConversionSyntax.
func TestFromBigIntOwnsExactScaleZeroResult(t *testing.T) {
	literal := "-" + strings.Repeat("123456789", 12)
	for _, call := range []bigIntIngressCall{
		{"FromBigInt", FromBigInt},
		{"FromBigIntWithBudget", func(x *big.Int) (Decimal, error) {
			if x == nil {
				return FromBigIntWithBudget(nil, Budget{MaxInputDigits: 1})
			}
			u, w := bigIntIngressOracle(t, x)
			return FromBigIntWithBudget(x, Budget{MaxInputDigits: u, MaxDigits: u, MaxWork: w})
		}},
	} {
		t.Run(call.name, func(t *testing.T) {
			source := bigIntFixture(t, literal)
			if len(source.Bits()) < 2 || source.Sign() >= 0 {
				t.Fatal("fixture is not a negative multiword source")
			}
			got, err := call.fn(source)
			if err != nil || got.exponent() != 0 || got.String() != literal {
				t.Fatalf("got %s exponent=%d err=%v", got, got.exponent(), err)
			}
			copyValue := got
			source.Bits()[0] ^= 1
			source.SetInt64(7)
			if got.String() != literal || copyValue.String() != literal {
				t.Fatal("source mutation changed the result")
			}
			zero, err := call.fn(new(big.Int))
			if err != nil || !isZeroValue(zero) {
				t.Fatalf("zero: got %+v err=%v", zero, err)
			}
			got, err = call.fn(nil)
			checkIngressError(t, got, err, call.name, ErrConversionSyntax, ConversionSyntax)
		})
	}
}

func TestFromBigIntExactCohortAndOwnedSource(t *testing.T) {
	fixtures := []string{
		"0", "1", "-1", "4294967295", "4294967296", "-4294967297",
		"18446744073709551615", "18446744073709551616", "340282366920938463463374607431768211455",
		"340282366920938463463374607431768211456",
		"1" + strings.Repeat("0", 999), "-1" + strings.Repeat("0", 999),
	}
	for _, literal := range fixtures {
		source := bigIntFixture(t, literal)
		want := source.String()
		got, err := FromBigInt(source)
		if err != nil || got.exponent() != 0 || got.String() != want || got.isZero() != (source.Sign() == 0) {
			t.Fatalf("%s: got %s exponent=%d err=%v", literal, got.String(), got.exponent(), err)
		}
		copyResult := got
		if source.Sign() != 0 {
			source.Bits()[0] ^= 1
		}
		source.SetInt64(7)
		if got.String() != want || copyResult.String() != want {
			t.Fatalf("source mutation changed result %s", literal)
		}
		if len(want) > 39 && (got.slow == nil || got.slow != copyResult.slow) {
			t.Fatalf("large result was not a copy-safe slow value: %s", literal)
		}
	}
}

func TestFromBigIntSeededIndependentOracle(t *testing.T) {
	r := rand.New(rand.NewSource(0xdec018))
	for i := range 512 {
		width := 1 + r.Intn(1030)
		data := make([]byte, 1+(width-1)/8)
		for j := range data {
			data[j] = byte(r.Intn(256))
		}
		data[0] &= byte(0xff >> (8*len(data) - width))
		x := new(big.Int).SetBytes(data)
		if i%3 == 0 {
			x.Neg(x)
		}
		u, w := bigIntIngressOracle(t, x)
		got, err := FromBigIntWithBudget(x, Budget{MaxInputDigits: u, MaxDigits: u, MaxWork: w})
		if err != nil || got.String() != x.String() || got.exponent() != 0 {
			t.Fatalf("case %d bits=%d: got %s want %s err=%v", i, width, got.String(), x, err)
		}
	}
}

// TestFromBigIntBudgetBoundaries covers the big integer ingress envelope
// boundaries: each positive cap one below the conservative envelope refuses
// with the exact method's InsufficientStorage, equality admits, nil wins over
// restrictive caps and a zero work cap imposes no W ceiling.
func TestFromBigIntBudgetBoundaries(t *testing.T) {
	for _, literal := range []string{"0", "1", "999999999", "4294967296", "-18446744073709551617", "1" + strings.Repeat("0", 79)} {
		x := bigIntFixture(t, literal)
		u, w := bigIntIngressOracle(t, x)
		for _, tc := range []struct {
			name string
			b    Budget
		}{
			{"input", Budget{MaxInputDigits: u - 1}},
			{"output", Budget{MaxDigits: u - 1}},
			{"work", Budget{MaxWork: w - 1}},
		} {
			if tc.b == (Budget{}) { // zero means unlimited
				continue
			}
			got, err := FromBigIntWithBudget(x, tc.b)
			checkIngressError(t, got, err, "FromBigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
		}
		got, err := FromBigIntWithBudget(x, Budget{MaxInputDigits: u, MaxDigits: u, MaxWork: w})
		if err != nil || got.String() != x.String() {
			t.Fatalf("%s exact caps U=%d W=%d: got=%s err=%v", literal, u, w, got.String(), err)
		}
		got, err = FromBigIntWithBudget(x, Budget{MaxInputDigits: u, MaxDigits: u})
		if err != nil || got.String() != x.String() {
			t.Fatalf("%s zero work cap: got=%s err=%v", literal, got.String(), err)
		}
	}
	x := bigIntFixture(t, "999999999") // nine actual digits, conservative U=10
	if u, _ := bigIntIngressOracle(t, x); u != 10 {
		t.Fatalf("conservative U=%d, want 10", u)
	}
	got, err := FromBigIntWithBudget(x, Budget{MaxDigits: 9})
	checkIngressError(t, got, err, "FromBigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	for _, call := range bigIntIngressCalls {
		got, err := call.fn(nil)
		checkIngressError(t, got, err, call.name, ErrConversionSyntax, ConversionSyntax)
	}

	// A below-envelope cap refuses before the scan or result buffer.
	long := bigIntFixture(t, "1"+strings.Repeat("0", 999))
	u, w := bigIntIngressOracle(t, long)
	for _, budget := range []Budget{{MaxInputDigits: u - 1}, {MaxDigits: u - 1}, {MaxWork: w - 1}} {
		allocs := testing.AllocsPerRun(20, func() {
			bigIntIngressResultSink, bigIntIngressErrorSink = FromBigIntWithBudget(long, budget)
		})
		checkIngressError(t, bigIntIngressResultSink, bigIntIngressErrorSink, "FromBigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
		if allocs > 1 {
			t.Fatalf("cap %+v: allocations=%g, want only the error", budget, allocs)
		}
	}

	// A zero work cap never evaluates W, so a source whose W formula would
	// overflow uint64 is still admitted; a positive cap refuses it.
	unbounded := bigIntTarget{wordBits: uint64(bits.UintSize), maxInt: math.MaxUint64, maxAddressBytes: math.MaxUint64, maxObjectBytes: math.MaxUint64}
	if _, admitted := bigIntIngressPreflight(1<<40, Budget{}, unbounded); !admitted {
		t.Fatal("zero work cap imposed the W formula ceiling")
	}
	if _, admitted := bigIntIngressPreflight(1<<40, Budget{MaxWork: math.MaxUint64}, unbounded); admitted {
		t.Fatal("positive work cap admitted an overflowing W")
	}
}

// TestFromBigIntRejectsMalformedSourceBeforeQuota checks that a malformed big
// integer source is refused before restrictive quotas apply: a nonempty Bits
// view with a zero top word, made through Bits or shared SetBits backing, is
// ConversionSyntax even under one-unit quotas, while an empty view is canonical
// zero at the one-digit, one-work tariff.
func TestFromBigIntRejectsMalformedSourceBeforeQuota(t *testing.T) {
	positive := new(big.Int).SetBits([]big.Word{7, 1})
	positive.Bits()[1] = 0
	negative := new(big.Int).Neg(new(big.Int).SetBits([]big.Word{7, 1}))
	negative.Bits()[1] = 0
	oneWordZero := big.NewInt(1)
	oneWordZero.Bits()[0] = 0
	negativeZero := big.NewInt(-1)
	negativeZero.Bits()[0] = 0
	twoWordZero := new(big.Int).SetBits([]big.Word{1, 1})
	twoWordZero.Bits()[0], twoWordZero.Bits()[1] = 0, 0
	shared := []big.Word{7, 1}
	sharedSource := new(big.Int).SetBits(shared)
	shared[1] = 0

	for _, tc := range []struct {
		name string
		x    *big.Int
	}{
		{"positive-padded", positive},
		{"negative-padded", negative},
		{"positive-zero-word", oneWordZero},
		{"negative-zero-word", negativeZero},
		{"two-zero-words", twoWordZero},
		{"setbits-shared-backing", sharedSource},
	} {
		for _, call := range bigIntIngressCalls {
			t.Run(tc.name+"/"+call.name, func(t *testing.T) {
				got, err := call.fn(tc.x)
				checkIngressError(t, got, err, call.name, ErrConversionSyntax, ConversionSyntax)
			})
		}
	}

	// A long padded source must be classified from its top word alone:
	// no lower-word scan or result buffer, only the error allocation.
	padded := make([]big.Word, 4096)
	for i := range padded {
		padded[i] = ^big.Word(0)
	}
	long := new(big.Int).SetBits(padded)
	padded[len(padded)-1] = 0
	for _, call := range bigIntIngressCalls {
		allocs := testing.AllocsPerRun(20, func() {
			bigIntIngressResultSink, bigIntIngressErrorSink = call.fn(long)
		})
		checkIngressError(t, bigIntIngressResultSink, bigIntIngressErrorSink, call.name, ErrConversionSyntax, ConversionSyntax)
		if allocs > 1 {
			t.Fatalf("%s padded zero-top source: allocations=%g, want only the error", call.name, allocs)
		}
	}

	for _, empty := range []*big.Int{new(big.Int), new(big.Int).SetBits(nil), new(big.Int).SetBits([]big.Word{})} {
		for _, call := range bigIntIngressCalls {
			got, err := call.fn(empty)
			if err != nil || !isZeroValue(got) {
				t.Fatalf("empty view %s: got %+v err=%v", call.name, got, err)
			}
		}
		for _, budget := range []Budget{{MaxInputDigits: 1}, {MaxDigits: 1}, {MaxWork: 1}} {
			if got, err := FromBigIntWithBudget(empty, budget); err != nil || !isZeroValue(got) {
				t.Fatalf("empty view at tariff %+v: got %+v err=%v", budget, got, err)
			}
		}
	}
}

func TestFromBigIntSetBitsNormalizationAndInteriorZero(t *testing.T) {
	for _, tc := range []struct {
		name  string
		words []big.Word
		want  string
	}{
		{"leading-zero-trimmed", []big.Word{7, 0}, "7"},
		{"all-zero-trimmed", []big.Word{0, 0}, "0"},
		{"interior-zero-valid", []big.Word{0, 0, 1}, new(big.Int).SetBits([]big.Word{0, 0, 1}).String()},
	} {
		t.Run(tc.name, func(t *testing.T) {
			x := new(big.Int).SetBits(tc.words)
			got, err := FromBigInt(x)
			if err != nil || got.String() != tc.want || got.exponent() != 0 {
				t.Fatalf("got=%s want=%s err=%v", got.String(), tc.want, err)
			}
			if len(x.Bits()) > 0 {
				x.Bits()[0] ^= 1
			}
			if got.String() != tc.want {
				t.Fatalf("source mutation changed result to %s", got.String())
			}
		})
	}
}

// TestFromBigIntSourceBitLength386Wrap pins the BitLen erratum: on
// 386 a 134,217,729-word source has 2^32+1 bits while big.Int.BitLen wraps to
// one, and the checked metadata length refuses it at input cap one.
func TestFromBigIntSourceBitLength386Wrap(t *testing.T) {
	wordCount := uint64(134217729)
	n, ok := bigIntIngressSafeBitLength(wordCount, 1, 32)
	if !ok || n != 1<<32+1 || int32((wordCount-1)*32+1) != 1 {
		t.Fatalf("safe n=%d ok=%t; BitLen wrap not reproduced", n, ok)
	}
	if _, admitted := bigIntIngressPreflight(n, Budget{MaxInputDigits: 1},
		bigIntTarget{wordBits: 32, maxInt: math.MaxInt32, maxAddressBytes: math.MaxInt32, maxObjectBytes: 1 << 32}); admitted {
		t.Fatal("wrapped-length quota admitted a giant source at input cap one")
	}
	if small, ok := bigIntIngressSafeBitLength(1, 1, 32); !ok || small != 1 {
		t.Fatalf("tiny source n=%d ok=%t", small, ok)
	}
}

func TestFromBigIntSourceBitLengthCheckedMetadata(t *testing.T) {
	for _, tc := range []struct{ words, top, width, want uint64 }{
		{1, 1, 32, 1}, {2, 1, 32, 33}, {134217729, 1, 32, 1<<32 + 1},
		{1, 1, 64, 1}, {2, 1, 64, 65},
	} {
		got, ok := bigIntIngressSafeBitLength(tc.words, tc.top, tc.width)
		if !ok || got != tc.want {
			t.Fatalf("%+v: n=%d ok=%t", tc, got, ok)
		}
	}
	for _, tc := range []struct{ words, top, width uint64 }{
		{0, 0, 32}, {1, 0, 32}, {2, 1 << 32, 32}, {1 << 63, 1, 64},
	} {
		if n, ok := bigIntIngressSafeBitLength(tc.words, tc.top, tc.width); ok {
			t.Fatalf("invalid metadata %+v admitted n=%d", tc, n)
		}
	}
}

func TestFromBigIntPhysicalPlanBoundaries(t *testing.T) {
	target := bigIntIngressRuntimeTarget()
	x := bigIntFixture(t, "18446744073709551617")
	n := uint64(x.BitLen())
	plan, ok := bigIntIngressPreflight(n, Budget{}, target)
	if !ok || plan.outputBytes == 0 || plan.outputRoundedBytes != bigIntPage || plan.holderRoundedBytes != bigIntPage {
		t.Fatalf("plan=%+v ok=%t", plan, ok)
	}
	sourceRounded, ok := bigIntRoundObject(uint64(len(x.Bits())) * uint64(bits.UintSize/8))
	if !ok {
		t.Fatal("source round overflow")
	}
	withoutSource := plan.outputRoundedBytes + plan.holderRoundedBytes
	limit := target
	for _, tc := range []struct {
		address uint64
		admit   bool
	}{
		{withoutSource, false}, // the live source words count
		{withoutSource + sourceRounded - 1, false},
		{withoutSource + sourceRounded, true},
	} {
		limit.maxAddressBytes = tc.address
		if _, admitted := bigIntIngressPreflight(n, Budget{}, limit); admitted != tc.admit {
			t.Fatalf("address window %d: admitted=%t", tc.address, admitted)
		}
	}
	wide := bigIntTarget{wordBits: 64, maxInt: math.MaxUint64, maxAddressBytes: math.MaxUint64, maxObjectBytes: 1 << 48}
	if _, admitted := bigIntIngressPreflight(1<<52, Budget{}, wide); admitted {
		t.Fatal("amd64 maxAlloc counterexample admitted")
	}
	wasm := bigIntTarget{wordBits: 64, maxInt: math.MaxInt64, maxAddressBytes: 1<<32 - 1, maxObjectBytes: 1 << 32}
	if _, admitted := bigIntIngressPreflight(1<<35, Budget{}, wasm); admitted {
		t.Fatal("wasm 4 GiB counterexample admitted")
	}
	unbounded := bigIntTarget{wordBits: uint64(bits.UintSize), maxInt: math.MaxUint64, maxAddressBytes: math.MaxUint64, maxObjectBytes: math.MaxUint64}
	if _, admitted := bigIntIngressPreflight(1<<40, Budget{MaxWork: math.MaxUint64}, unbounded); admitted {
		t.Fatal("positive W overflow admitted")
	}
	if _, admitted := bigIntIngressPreflight(1<<40, Budget{}, unbounded); !admitted {
		t.Fatal("zero W cap imposed formula ceiling")
	}
}

var (
	bigIntIngressResultSink Decimal
	bigIntIngressErrorSink  error
)

func TestFromBigIntRefusesBeforeAllocating(t *testing.T) {
	x := bigIntFixture(t, "1"+strings.Repeat("0", 999))
	target := bigIntIngressRuntimeTarget()
	plan, ok := bigIntIngressPreflight(uint64(x.BitLen()), Budget{}, target)
	if !ok {
		t.Fatal("fixture physical plan refused")
	}
	limit := target
	limit.maxObjectBytes = plan.outputRoundedBytes - 1
	refused := testing.AllocsPerRun(20, func() {
		bigIntIngressResultSink, bigIntIngressErrorSink = fromBigIntOnTarget(x, Budget{}, "FromBigIntWithBudget", limit)
	})
	checkIngressError(t, bigIntIngressResultSink, bigIntIngressErrorSink, "FromBigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	if refused > 1 {
		t.Fatalf("physical refusal allocations=%g, want at most the error", refused)
	}
	u, _ := bigIntIngressOracle(t, x)
	refused = testing.AllocsPerRun(20, func() {
		bigIntIngressResultSink, bigIntIngressErrorSink = FromBigIntWithBudget(x, Budget{MaxInputDigits: u - 1})
	})
	checkIngressError(t, bigIntIngressResultSink, bigIntIngressErrorSink, "FromBigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	if refused > 1 {
		t.Fatalf("quota refusal allocations=%g, want at most the error", refused)
	}
	accepted := testing.AllocsPerRun(20, func() {
		bigIntIngressResultSink, bigIntIngressErrorSink = FromBigInt(x)
	})
	if bigIntIngressErrorSink != nil || bigIntIngressResultSink.slow == nil ||
		bigIntIngressResultSink.String() != x.String() || accepted > 2 {
		t.Fatalf("admission: allocs=%g result=%s err=%v", accepted, bigIntIngressResultSink.String(), bigIntIngressErrorSink)
	}
}

// TestBigIntEgressIsNumericAndFresh checks that big integer egress is
// numeric and fresh: zero at both exponent endpoints, 1.00, its cohort and a
// large integral value return exact fresh results through both forms whose
// mutation reaches neither the source nor its shallow copies, and a
// fractional value returns nil with NonIntegral.
func TestBigIntEgressIsNumericAndFresh(t *testing.T) {
	large := "-" + strings.Repeat("9", 120)
	for _, tc := range []struct {
		name string
		d    Decimal
		want *big.Int
	}{
		{"zero-low-endpoint", New(0, math.MinInt32), new(big.Int)},
		{"zero-high-endpoint", New(0, math.MaxInt32), new(big.Int)},
		{"one-point-zero-zero", MustParse("1.00"), big.NewInt(1)},
		{"equivalent-cohort", MustParse("100E-2"), big.NewInt(1)},
		{"large-integral", MustParse(large), bigIntFixture(t, large)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			before := tc.d.String()
			shallow := tc.d
			bare, err := tc.d.BigInt(nil)
			if err != nil || bare == nil || bare.Cmp(tc.want) != 0 {
				t.Fatalf("bare: (%v,%v), want %v", bare, err, tc.want)
			}
			bounded, err := tc.d.BigIntWithBudget(nil, Budget{})
			if err != nil || bounded == nil || bounded.Cmp(tc.want) != 0 || bounded == bare {
				t.Fatalf("budgeted: (%v,%v), want fresh %v", bounded, err, tc.want)
			}
			bare.Add(bare, big.NewInt(1))
			if bounded.Cmp(tc.want) != 0 {
				t.Fatal("bare result mutation changed budgeted result")
			}
			bounded.Sub(bounded, big.NewInt(1))
			if bare.Cmp(new(big.Int).Add(tc.want, big.NewInt(1))) != 0 {
				t.Fatal("budgeted result mutation changed bare result")
			}
			if tc.d.String() != before || shallow.String() != before {
				t.Fatal("returned big.Int mutation changed source or shallow copy")
			}
		})
	}
	fractional := MustParse("1.01")
	got, err := fractional.BigInt(nil)
	checkEgressError(t, got, err, "BigInt", ErrNonIntegral, 0)
	got, err = fractional.BigIntWithBudget(nil, Budget{})
	checkEgressError(t, got, err, "BigIntWithBudget", ErrNonIntegral, 0)
}

func TestBigIntExactOracleAndFreshOwnership(t *testing.T) {
	coefficients := []string{"0", "1", "-1", "100", "-100", "1000000000", "1000000001", "-1000000001", "18446744073709551616", "-" + strings.Repeat("9", 160)}
	exponents := []int{-25, -20, -9, -2, -1, 0, 1, 2, 9, 20, 25}
	for _, coefficient := range coefficients {
		for _, exponent := range exponents {
			label := coefficient + "E" + strconv.Itoa(exponent)
			d := MustParse(label)
			before := d.String()
			copyValue := d
			want, integral := bigIntEgressOracle(t, coefficient, exponent)
			got, err := d.BigInt(nil)
			if !integral {
				checkEgressError(t, got, err, "BigInt", ErrNonIntegral, 0)
				continue
			}
			if err != nil || got == nil || got.Cmp(want) != 0 {
				t.Fatalf("%s: got (%v,%v), want %s", label, got, err, want)
			}
			other, err := d.BigInt(nil)
			if err != nil || other == got || other.Cmp(want) != 0 {
				t.Fatalf("%s: second result not fresh", label)
			}
			got.Add(got, big.NewInt(1))
			if other.Cmp(want) != 0 || d.String() != before || copyValue.String() != before {
				t.Fatalf("%s: result mutation changed source or second result", label)
			}
		}
	}
}

func TestBigIntZeroExponentEndpoints(t *testing.T) {
	for _, exponent := range []int32{math.MinInt32, math.MaxInt32} {
		d := New(0, exponent)
		got, err := d.BigIntWithBudget(nil, Budget{MaxInputDigits: 1, MaxDigits: 1, MaxWork: 1})
		if err != nil || got == nil || got.Sign() != 0 {
			t.Fatalf("zero exponent %d: (%v,%v)", exponent, got, err)
		}
		got.SetInt64(12)
		if !d.isZero() {
			t.Fatalf("zero exponent %d changed source", exponent)
		}
	}
}

func TestBigIntQuotaPriorityAndExactCaps(t *testing.T) {
	integral := MustParse("12000E-2") // d=5, L=3, W=(1+1)^2+2=6
	for _, budget := range []Budget{{MaxInputDigits: 4}, {MaxWork: 5}, {MaxDigits: 2}} {
		got, err := integral.BigIntWithBudget(nil, budget)
		checkEgressError(t, got, err, "BigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	}
	got, err := integral.BigIntWithBudget(nil, Budget{MaxInputDigits: 5, MaxDigits: 3, MaxWork: 6})
	if err != nil || got == nil || got.Cmp(big.NewInt(120)) != 0 {
		t.Fatalf("equality caps: (%v,%v)", got, err)
	}
	fractional := MustParse("12001E-2")
	got, err = fractional.BigIntWithBudget(nil, Budget{MaxDigits: 1, MaxWork: 6})
	checkEgressError(t, got, err, "BigIntWithBudget", ErrNonIntegral, 0)
	got, err = fractional.BigIntWithBudget(nil, Budget{MaxDigits: 1, MaxWork: 5})
	checkEgressError(t, got, err, "BigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	tooSmall := New(12, math.MinInt32)
	got, err = tooSmall.BigIntWithBudget(nil, Budget{MaxInputDigits: 2, MaxDigits: 1, MaxWork: 1})
	checkEgressError(t, got, err, "BigIntWithBudget", ErrNonIntegral, 0)
	got, err = tooSmall.BigIntWithBudget(nil, Budget{MaxInputDigits: 1})
	checkEgressError(t, got, err, "BigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
}

func TestBigIntPositiveExponentQuotaCaps(t *testing.T) {
	d := New(12, 2) // d=2, L=4, W=(1+1)^2+2=6
	for _, budget := range []Budget{{MaxInputDigits: 1}, {MaxDigits: 3}, {MaxWork: 5}} {
		got, err := d.BigIntWithBudget(nil, budget)
		checkEgressError(t, got, err, "BigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	}
	got, err := d.BigIntWithBudget(nil, Budget{MaxInputDigits: 2, MaxDigits: 4, MaxWork: 6})
	if err != nil || got == nil || got.Cmp(big.NewInt(1200)) != 0 {
		t.Fatalf("positive exponent equality caps: (%v,%v)", got, err)
	}
}

var (
	bigIntEgressResultSink *big.Int
	bigIntEgressErrorSink  error
)

func TestBigIntRefusesBeforeAllocatingResult(t *testing.T) {
	d := MustParse("1" + strings.Repeat("0", 9999) + "E9")
	allocs := testing.AllocsPerRun(20, func() {
		bigIntEgressResultSink, bigIntEgressErrorSink = d.BigIntWithBudget(nil, Budget{MaxDigits: 1})
	})
	checkEgressError(t, bigIntEgressResultSink, bigIntEgressErrorSink, "BigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	if allocs != 1 {
		t.Fatalf("pre-result refusal allocations=%g, want one fixed error object", allocs)
	}
	got, err := New(1, math.MaxInt32).BigIntWithBudget(nil, Budget{MaxDigits: 1})
	checkEgressError(t, got, err, "BigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	d = MustParse("1" + strings.Repeat("0", 10000) + "E-10000")
	allocs = testing.AllocsPerRun(20, func() {
		bigIntEgressResultSink, bigIntEgressErrorSink = d.BigInt(nil)
	})
	if bigIntEgressErrorSink != nil || bigIntEgressResultSink == nil || bigIntEgressResultSink.Cmp(big.NewInt(1)) != 0 || allocs > 2 {
		t.Fatalf("long exact drop: result=%v err=%v allocations=%g", bigIntEgressResultSink, bigIntEgressErrorSink, allocs)
	}
}

func TestBigIntCrossLimbOracle(t *testing.T) {
	for drop := 1; drop <= 27; drop++ {
		for _, sign := range []string{"", "-"} {
			coefficient := sign + "17" + strings.Repeat("0", drop)
			got, err := MustParse(coefficient + "E-" + strconv.Itoa(drop)).BigInt(nil)
			want, integral := bigIntEgressOracle(t, coefficient, -drop)
			if !integral || err != nil || got == nil || got.Cmp(want) != 0 {
				t.Fatalf("drop=%d coefficient=%s: (%v,%v), want %v", drop, coefficient, got, err, want)
			}
		}
	}
	r := rand.New(rand.NewSource(0xdec018))
	for i := range 512 {
		data := make([]byte, 1+r.Intn(128))
		for j := range data {
			data[j] = byte(r.Intn(256))
		}
		coefficient := new(big.Int).SetBytes(data)
		if i%3 == 0 {
			coefficient.Neg(coefficient)
		}
		exponent := r.Intn(55) - 27
		literal := coefficient.String() + "E" + strconv.Itoa(exponent)
		got, err := MustParse(literal).BigInt(nil)
		want, integral := bigIntEgressOracle(t, coefficient.String(), exponent)
		if !integral {
			checkEgressError(t, got, err, "BigInt", ErrNonIntegral, 0)
		} else if err != nil || got == nil || got.Cmp(want) != 0 {
			t.Fatalf("case %d %s: (%v,%v), want %v", i, literal, got, err, want)
		}
	}
}

func TestBigIntPhysicalPlanBoundaries(t *testing.T) {
	if size := reflect.TypeFor[big.Int]().Size(); uint64(size) > bigIntObjectBytes {
		t.Fatalf("Go big.Int object size %d exceeds planned constant", size)
	}
	if size := reflect.TypeFor[big.Word]().Size(); size != uintptr(strconv.IntSize/8) {
		t.Fatalf("Go big.Word size %d differs from uint width", size)
	}
	if count, ok := bigIntEgressWordsForTarget(80, hostBigIntTarget(bigIntPage, 2*bigIntPage)); !ok || count < 1 {
		t.Fatalf("page-boundary plan: count=%d ok=%v", count, ok)
	}
	if _, ok := bigIntEgressWordsForTarget(80, hostBigIntTarget(bigIntPage-1, 2*bigIntPage)); ok {
		t.Fatal("rounded object one byte below page must refuse")
	}
	if _, ok := bigIntEgressWordsForTarget(80, hostBigIntTarget(bigIntPage, 2*bigIntPage-1)); ok {
		t.Fatal("combined address one byte below plan must refuse")
	}
	if _, ok := bigIntEgressWordsForTarget(1<<52, hostBigIntTarget(1<<48, 1<<48-1)); ok {
		t.Fatal("requested native object above Go maxAlloc must refuse")
	}
	if _, ok := bigIntEgressWordsForTarget(1<<35, hostBigIntTarget(1<<32, 1<<32-1)); ok {
		t.Fatal("requested wasm object above address window must refuse")
	}
}

// hostBigIntTarget plans the running word width against synthetic object
// and address ceilings.
func hostBigIntTarget(maxObject, maxAddress uint64) bigIntTarget {
	return bigIntTarget{wordBits: uint64(bits.UintSize), maxInt: math.MaxInt, maxObjectBytes: maxObject, maxAddressBytes: maxAddress}
}

// TestBigIntRuntimeLimitsMatchGoMalloc pins the Go 1.27.1 heapAddrBits and
// maxAlloc map shared by both conversion directions.
func TestBigIntRuntimeLimitsMatchGoMalloc(t *testing.T) {
	for _, tc := range []struct {
		goos, goarch          string
		wordBits              uint64
		maxObject, maxAddress uint64
	}{
		{"linux", "amd64", 64, 1 << 48, 1<<48 - 1},
		{"darwin", "arm64", 64, 1 << 48, 1<<48 - 1},
		{"windows", "amd64", 64, 1 << 48, 1<<48 - 1},
		{"ios", "arm64", 64, 1 << 40, 1<<40 - 1},
		{"linux", "386", 32, 1<<32 - 1, 1<<31 - 1},
		{"linux", "mipsle", 32, 1<<31 - 1, 1<<31 - 1},
		{"js", "wasm", 64, 1 << 32, 1<<32 - 1},
		{"wasip1", "wasm", 64, 1 << 32, 1<<32 - 1},
	} {
		object, address, ok := bigIntRuntimeLimits(tc.goos, tc.goarch, tc.wordBits)
		if !ok || object != tc.maxObject || address != tc.maxAddress {
			t.Fatalf("%s/%s: object=%d address=%d ok=%v", tc.goos, tc.goarch, object, address, ok)
		}
		target := bigIntTargetFor(tc.goos, tc.goarch, tc.wordBits)
		if target.wordBits != tc.wordBits || target.maxInt != 1<<(tc.wordBits-1)-1 ||
			target.maxObjectBytes != object || target.maxAddressBytes != address {
			t.Fatalf("%s/%s: target %+v", tc.goos, tc.goarch, target)
		}
		if _, fits := bigIntEgressWordsForTarget(1, target); !fits {
			t.Fatalf("%s/%s: small integer spuriously refused", tc.goos, tc.goarch)
		}
		if _, fits := bigIntIngressPreflight(64, Budget{}, target); !fits {
			t.Fatalf("%s/%s: small source spuriously refused", tc.goos, tc.goarch)
		}
	}
	if _, _, ok := bigIntRuntimeLimits("linux", "amd64", 16); ok {
		t.Fatal("unknown word size admitted")
	}
	if unknown := bigIntTargetFor("linux", "amd64", 16); unknown != (bigIntTarget{}) {
		t.Fatalf("unknown word size planned %+v", unknown)
	}
}

// TestExactIntegerIngressAcrossCarriers covers exact integer ingress:
// int64, uint64 and admitted big.Int values convert exactly at
// scale zero; nil and zero-top big.Int sources are ConversionSyntax and a
// checked refusal is InsufficientStorage with no result.
func TestExactIntegerIngressAcrossCarriers(t *testing.T) {
	for _, v := range []int64{math.MinInt64, -1, 0, 1, math.MaxInt64} {
		if got := FromInt64(v); got.exponent() != 0 || got.String() != strconv.FormatInt(v, 10) {
			t.Fatalf("FromInt64(%d) = %s exponent %d", v, got, got.exponent())
		}
	}
	for _, v := range []uint64{0, 1, math.MaxUint64} {
		if got := FromUint64(v); got.exponent() != 0 || got.String() != strconv.FormatUint(v, 10) {
			t.Fatalf("FromUint64(%d) = %s exponent %d", v, got, got.exponent())
		}
	}
	for _, literal := range []string{"-9223372036854775809", "18446744073709551616", "-" + strings.Repeat("7", 200)} {
		x := bigIntFixture(t, literal)
		got, err := FromBigInt(x)
		if err != nil || got.exponent() != 0 || got.String() != literal {
			t.Fatalf("FromBigInt(%s) = %s exponent %d err=%v", literal, got, got.exponent(), err)
		}
		got, err = FromBigIntWithBudget(x, Budget{MaxDigits: 1})
		checkIngressError(t, got, err, "FromBigIntWithBudget", ErrInsufficientStorage, InsufficientStorage)
	}
	malformed := big.NewInt(5)
	malformed.Bits()[0] = 0
	for _, x := range []*big.Int{nil, malformed} {
		got, err := FromBigInt(x)
		checkIngressError(t, got, err, "FromBigInt", ErrConversionSyntax, ConversionSyntax)
	}
}

// TestBigIntegerBoundaryOwnsData checks that the big integer boundary owns
// its data: after FromBigInt the caller may mutate the source, and after BigInt
// the caller may mutate the returned value, without changing the other side
// or its shallow copies.
func TestBigIntegerBoundaryOwnsData(t *testing.T) {
	literal := "-" + strings.Repeat("31415926535", 10)
	source := bigIntFixture(t, literal)
	d, err := FromBigInt(source)
	if err != nil || d.exponent() != 0 {
		t.Fatalf("FromBigInt: exponent %d err=%v", d.exponent(), err)
	}
	shallow := d
	source.Bits()[0] ^= 1
	source.Neg(source)
	if d.String() != literal || shallow.String() != literal {
		t.Fatal("source mutation reached the Decimal")
	}
	out, err := d.BigInt(nil)
	if err != nil || out.String() != literal {
		t.Fatalf("BigInt: %v err=%v", out, err)
	}
	again, err := d.BigInt(nil)
	if err != nil || again == out || &again.Bits()[0] == &out.Bits()[0] {
		t.Fatal("BigInt results share storage")
	}
	out.Bits()[0] ^= 1
	out.SetInt64(3)
	if d.String() != literal || shallow.String() != literal || again.String() != literal {
		t.Fatal("returned big.Int mutation reached the Decimal or another result")
	}
}

// TestFromBigIntHugeSourceRefusedBelowEnvelope checks that a huge
// normalized big integer cannot truncate through a BitLen wrap: the public
// source 2^(2^32)+1 (134,217,729 32-bit words on 386, where Go 1.27.1's
// BitLen wraps to 1; 67,108,865 words on 64-bit targets), given to
// FromBigIntWithBudget with the input cap U−1 for its hand-derived safe
// envelope U = floor((2^32+1)·0.30103)+1 = 1,292,914,006, returns Decimal{}
// and an *Error with ErrInsufficientStorage before any
// coefficient scan, never the truncated value one. The source (~512 MiB) is
// released before the test returns.
func TestFromBigIntHugeSourceRefusedBelowEnvelope(t *testing.T) {
	const wantU = 1292914006
	n, ok := bigIntIngressSafeBitLength(uint64((1<<32)/bits.UintSize+1), 1, uint64(bits.UintSize))
	if !ok || n != 1<<32+1 {
		t.Fatalf("safe bit length %d, %v; want 2^32+1", n, ok)
	}
	if u := (n/100000)*30103 + (n%100000)*30103/100000 + 1; u != wantU {
		t.Fatalf("envelope U = %d, want %d", u, wantU)
	}
	words := make([]big.Word, (1<<32)/bits.UintSize+1)
	words[0], words[len(words)-1] = 1, 1
	x := new(big.Int).SetBits(words)
	defer func() {
		words, x = nil, nil
		runtime.GC()
		debug.FreeOSMemory()
	}()
	if bits.UintSize == 32 && x.BitLen() != 1 {
		t.Fatalf("386 BitLen = %d; the wrap witness is not live", x.BitLen())
	}
	got, err := FromBigIntWithBudget(x, Budget{MaxInputDigits: wantU - 1})
	var opErr *Error
	if !reflect.DeepEqual(got, Decimal{}) || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &opErr) ||
		opErr.Op != "FromBigIntWithBudget" || opErr.Condition != InsufficientStorage {
		t.Fatalf("giant source at cap U-1 = %v, %#v; want Decimal{} and FromBigIntWithBudget InsufficientStorage", got, err)
	}
}

// TestIntegerConversionTypedCauses covers the exact typed causes of the
// integer conversions in one table: FromBigInt(nil) and a
// nonempty zero-top Bits source give ErrConversionSyntax with condition
// ConversionSyntax; an exceeded FromBigIntWithBudget cap gives
// ErrInsufficientStorage; a fractional Int64/Uint64/BigInt input gives
// ErrNonIntegral and an integral fixed-width overflow ErrIntegerRange, both
// with zero conditions. Every failure pairs a zero or nil result with an
// *Error; cohorts of integral values convert.
func TestIntegerConversionTypedCauses(t *testing.T) {
	zeroTopWords := []big.Word{1, 1}
	zeroTop := new(big.Int).SetBits(zeroTopWords)
	zeroTopWords[1] = 0 // raw mutation leaves a nonempty zero-top Bits view
	type result struct {
		zero bool
		err  error
	}
	fromBig := func(d Decimal, err error) result { return result{reflect.DeepEqual(d, Decimal{}), err} }
	toInt64 := func(v int64, err error) result { return result{v == 0, err} }
	toUint64 := func(v uint64, err error) result { return result{v == 0, err} }
	toBig := func(v *big.Int, err error) result { return result{v == nil, err} }
	for _, tc := range []struct {
		name      string
		got       result
		op        string
		cause     error
		condition Conditions
	}{
		{"FromBigInt nil", fromBig(FromBigInt(nil)), "FromBigInt", ErrConversionSyntax, ConversionSyntax},
		{"FromBigInt zero top", fromBig(FromBigInt(zeroTop)), "FromBigInt", ErrConversionSyntax, ConversionSyntax},
		{"FromBigIntWithBudget cap", fromBig(FromBigIntWithBudget(big.NewInt(123), Budget{MaxInputDigits: 2})),
			"FromBigIntWithBudget", ErrInsufficientStorage, InsufficientStorage},
		{"Int64 fraction", toInt64(MustParse("1.5").Int64()), "Int64", ErrNonIntegral, 0},
		{"Uint64 fraction", toUint64(MustParse("1.5").Uint64()), "Uint64", ErrNonIntegral, 0},
		{"BigInt fraction", toBig(MustParse("1.5").BigInt(nil)), "BigInt", ErrNonIntegral, 0},
		{"Int64 overflow", toInt64(MustParse("9223372036854775808").Int64()), "Int64", ErrIntegerRange, 0},
		{"Int64 underflow", toInt64(MustParse("-9223372036854775809").Int64()), "Int64", ErrIntegerRange, 0},
		{"Uint64 overflow", toUint64(MustParse("18446744073709551616").Uint64()), "Uint64", ErrIntegerRange, 0},
		{"Uint64 negative", toUint64(MustParse("-1").Uint64()), "Uint64", ErrIntegerRange, 0},
	} {
		var opErr *Error
		if !tc.got.zero || !errors.Is(tc.got.err, tc.cause) || !errors.As(tc.got.err, &opErr) ||
			opErr.Op != tc.op || opErr.Condition != tc.condition {
			t.Errorf("%s: zero=%v err=%#v; want zero result and %s %v condition %v", tc.name, tc.got.zero, tc.got.err, tc.op, tc.cause, tc.condition)
		}
	}
	for _, tc := range []struct {
		literal string
		want    int64
	}{{"1.00", 1}, {"100E-2", 1}, {"0E+2147483647", 0}, {"-7E+1", -70}} {
		d := MustParse(tc.literal)
		i, err := d.Int64()
		b, bigErr := d.BigInt(nil)
		if err != nil || i != tc.want || bigErr != nil || b.Cmp(big.NewInt(tc.want)) != 0 {
			t.Errorf("%s converts to %d/%v, %v/%v; want %d", tc.literal, i, b, err, bigErr, tc.want)
		}
	}
}

// TestIntegerConversionSignatures pins the integer conversion
// signatures: the
// compiler pins FromBigInt and FromBigIntWithBudget to (Decimal, error),
// Int64 and Uint64 to a machine integer and error, BigInt and
// BigIntWithBudget to (*big.Int, error), and FromInt64 and FromUint64 to
// value-only constructors. A go/parser scan pins each bare growth
// method (FromBigInt, BigInt, and likewise Rat and NewTwosComplement) to a
// single call of its budgeted twin's private path, differing only in a
// zero Budget{} and the method name; seeded values then
// give identical results and causes through the bare form and the
// zero-budget form.
func TestIntegerConversionSignatures(t *testing.T) {
	var (
		fromBig       func(*big.Int) (Decimal, error)                   = FromBigInt
		fromBigBudget func(*big.Int, Budget) (Decimal, error)           = FromBigIntWithBudget
		toInt64       func(Decimal) (int64, error)                      = Decimal.Int64
		toUint64      func(Decimal) (uint64, error)                     = Decimal.Uint64
		toBig         func(Decimal, *big.Int) (*big.Int, error)         = Decimal.BigInt
		toBigBudget   func(Decimal, *big.Int, Budget) (*big.Int, error) = Decimal.BigIntWithBudget
		fromInt64     func(int64) Decimal                               = FromInt64
		fromUint64    func(uint64) Decimal                              = FromUint64
	)
	if fromBig == nil || fromBigBudget == nil || toInt64 == nil || toUint64 == nil || toBig == nil || toBigBudget == nil || fromInt64 == nil || fromUint64 == nil {
		t.Fatal("a required integer-conversion signature is absent")
	}

	fset := token.NewFileSet()
	decls := map[string]*ast.FuncDecl{}
	for _, file := range []string{"integer.go", "rational.go", "coefficient.go"} {
		f, err := parser.ParseFile(fset, file, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatal(err)
		}
		for _, decl := range f.Decls {
			if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.IsExported() {
				decls[fn.Name.Name] = fn
			}
		}
	}
	onlyCall := func(name string) *ast.CallExpr {
		fn := decls[name]
		if fn == nil || fn.Body == nil || len(fn.Body.List) != 1 {
			t.Fatalf("%s is not a single-statement delegation", name)
		}
		ret, ok := fn.Body.List[0].(*ast.ReturnStmt)
		if !ok || len(ret.Results) != 1 {
			t.Fatalf("%s does not return one call", name)
		}
		call, ok := ret.Results[0].(*ast.CallExpr)
		if !ok {
			t.Fatalf("%s does not return a call", name)
		}
		return call
	}
	for _, bare := range []string{"FromBigInt", "BigInt", "Rat", "NewTwosComplement"} {
		budgeted := bare + "WithBudget"
		b, w := onlyCall(bare), onlyCall(budgeted)
		if types.ExprString(b.Fun) != types.ExprString(w.Fun) || len(b.Args) != len(w.Args) {
			t.Errorf("%s calls %s and %s calls %s: not the same private path", bare, types.ExprString(b.Fun), budgeted, types.ExprString(w.Fun))
			continue
		}
		var sawBudget, sawName bool
		for i, arg := range w.Args {
			got, want := types.ExprString(b.Args[i]), types.ExprString(arg)
			switch want {
			case "budget":
				want, sawBudget = "Budget{}", true
			case strconv.Quote(budgeted):
				want, sawName = strconv.Quote(bare), true
			}
			if got != want {
				t.Errorf("%s passes %s where %s passes %s; want %s", bare, got, budgeted, types.ExprString(arg), want)
			}
		}
		if !sawBudget || !sawName {
			t.Errorf("%s: the budget or method-name argument was not found (budget %v, name %v)", budgeted, sawBudget, sawName)
		}
	}

	rng := rand.New(rand.NewSource(18))
	var integral, fractional int
	for i := range 200 {
		x := new(big.Int).Rand(rng, new(big.Int).Lsh(big.NewInt(1), uint(1+rng.Intn(2000))))
		if i%2 == 1 {
			x.Neg(x)
		}
		d, err := FromBigInt(x)
		z, zErr := FromBigIntWithBudget(x, Budget{})
		if err != nil || zErr != nil || d.coefficientDigits() != z.coefficientDigits() || d.exponent() != z.exponent() || d.negative() != z.negative() {
			t.Fatalf("FromBigInt(%s) = %s, %v; zero budget %s, %v", x, d, err, z, zErr)
		}
		scaled := New(int64(rng.Intn(1000))-500, int32(rng.Intn(9))-4)
		for _, v := range []Decimal{d, scaled} {
			b, bErr := v.BigInt(nil)
			zb, zbErr := v.BigIntWithBudget(nil, Budget{})
			switch {
			case bErr == nil && zbErr == nil && b.Cmp(zb) == 0:
				integral++
			case errors.Is(bErr, ErrNonIntegral) && errors.Is(zbErr, ErrNonIntegral):
				fractional++
			default:
				t.Fatalf("BigInt(%s) = %v, %v; zero budget %v, %v", v, b, bErr, zb, zbErr)
			}
		}
	}
	if integral < 100 || fractional < 50 {
		t.Fatalf("BigInt parity saw %d integral and %d fractional values; want both", integral, fractional)
	}
	if _, err := FromBigInt(nil); !errors.Is(err, ErrConversionSyntax) {
		t.Errorf("FromBigInt(nil) = %v", err)
	}
	if _, err := FromBigIntWithBudget(nil, Budget{}); !errors.Is(err, ErrConversionSyntax) {
		t.Errorf("FromBigIntWithBudget(nil, zero) = %v", err)
	}
}

// TestBigIntNegativeExponentEgressPriority covers the refusal priority of
// integer egress at a negative exponent. For nonzero coefficients of d digits
// at exponent -k with k<d (inline, multi-limb and 1,000-digit, both signs,
// integral and fractional low digits, including a single nonzero digit just
// below the point), it sweeps input cap d-1/d, work cap W-1/W and output cap
// L-1/L, where L=d-k and W=T²+T with T=⌈d/9⌉+⌈L/9⌉ come from the egress tariff
// over the literal's digit string. Input cap d-1 refuses before the integrality
// scan (a fractional value refuses with InsufficientStorage, not NonIntegral);
// a positive W-1 refuses even a fractional value (no scan before the
// precharge); input and work refusals share ErrInsufficientStorage, so their
// mutual order is not observable and is not asserted. An admitted fractional
// value is NonIntegral before the output cap, and an integral value refuses at
// L-1 and admits at L/W with the math/big quotient. For k>=d (k=d, k>d, k=2^31)
// the call is NonIntegral after input admission at work and output caps of one,
// and InsufficientStorage at input cap d-1. Refusals allocate at most the error
// object.
func TestBigIntNegativeExponentEgressPriority(t *testing.T) {
	const op = "BigIntWithBudget"
	limbs := func(n uint64) uint64 { return (n + 8) / 9 }
	type fixture struct {
		name, digits string
		k            int
	}
	var fixtures []fixture
	for _, base := range []struct {
		name, top string
		k         int
	}{
		{"inline", "12", 3},
		{"inline-L1", "7", 18},
		{"multi-limb", "98765432109876543210", 10},
		{"cross-limb", "123456789", 22},
		{"long", strings.Repeat("31415926", 50), 600},
	} {
		zeros := strings.Repeat("0", base.k)
		fixtures = append(fixtures,
			fixture{base.name + "/integral", base.top + zeros, base.k},
			fixture{base.name + "/fractional-low", base.top + zeros[1:] + "1", base.k},
			fixture{base.name + "/fractional-high", base.top + "5" + zeros[1:], base.k})
	}
	for _, f := range fixtures {
		for _, sign := range []string{"", "-"} {
			name := sign + f.name
			x := MustParse(sign + f.digits + "E-" + strconv.Itoa(f.k))
			d := uint64(len(f.digits))
			l := d - uint64(f.k)
			T := limbs(d) + limbs(l)
			w := T*T + T
			want, integral := bigIntEgressOracle(t, sign+f.digits, -f.k)
			if strings.HasSuffix(f.name, "integral") != integral {
				t.Fatalf("%s: fixture integrality %t", name, integral)
			}
			check := func(label string, budget Budget, code ErrorCode) {
				t.Helper()
				got, err := x.BigIntWithBudget(nil, budget)
				if code == 0 {
					if err != nil || got == nil || got.Cmp(want) != 0 {
						t.Fatalf("%s %s %+v: (%v, %v), want %v", name, label, budget, got, err, want)
					}
					return
				}
				condition := Conditions(0)
				if code == ErrInsufficientStorage {
					condition = InsufficientStorage
				}
				checkEgressError(t, got, err, op, code, condition)
				if allocs := testing.AllocsPerRun(5, func() { bigIntEgressResultSink, bigIntEgressErrorSink = x.BigIntWithBudget(nil, budget) }); allocs > 1 {
					t.Fatalf("%s %s: refusal allocations=%g", name, label, allocs)
				}
			}
			const success = ErrorCode(0)
			exact := ErrNonIntegral
			if integral {
				exact = success
			}
			all := func(in, work, out uint64) Budget {
				return Budget{MaxInputDigits: in, MaxWork: work, MaxDigits: out}
			}
			check("input d-1", all(d-1, w-1, max(l-1, 1)), ErrInsufficientStorage)
			check("input d-1 alone", all(d-1, 0, 0), ErrInsufficientStorage)
			check("work W-1", all(d, w-1, max(l-1, 1)), ErrInsufficientStorage)
			check("work W-1 alone", all(0, w-1, 0), ErrInsufficientStorage)
			if integral {
				if l > 1 {
					check("output L-1", all(d, w, l-1), ErrInsufficientStorage)
				}
				check("caps d/W/L", all(d, w, l), success)
			} else {
				check("output one", all(d, w, 1), ErrNonIntegral)
				check("caps d/W/L", all(d, w, l), ErrNonIntegral)
			}
			check("unlimited", Budget{}, exact)
		}
	}
	for _, tc := range []struct {
		name   string
		digits string
		k      int64
	}{
		{"k=d", "12", 2},
		{"k>d", "12", 3},
		{"k=2^31", "12", 1 << 31},
		{"long k=d", strings.Repeat("9", 1000), 1000},
	} {
		x := MustParse("-" + tc.digits + "E-" + strconv.FormatInt(tc.k, 10))
		d := uint64(len(tc.digits))
		got, err := x.BigIntWithBudget(nil, Budget{MaxInputDigits: d, MaxWork: 1, MaxDigits: 1})
		checkEgressError(t, got, err, op, ErrNonIntegral, 0)
		got, err = x.BigIntWithBudget(nil, Budget{MaxInputDigits: d - 1, MaxWork: 1, MaxDigits: 1})
		checkEgressError(t, got, err, op, ErrInsufficientStorage, InsufficientStorage)
		if allocs := testing.AllocsPerRun(5, func() {
			bigIntEgressResultSink, bigIntEgressErrorSink = x.BigIntWithBudget(nil, Budget{MaxInputDigits: d, MaxWork: 1})
		}); allocs > 1 {
			t.Fatalf("%s: NonIntegral allocations=%g", tc.name, allocs)
		}
	}
}

// bigIntPlanTargets are the executed Go targets whose physical conversion
// plans are checked: native 64-bit, 386 and wasm.
var bigIntPlanTargets = []struct{ goos, goarch string }{
	{"linux", "amd64"}, {"linux", "386"}, {"js", "wasm"}, {"wasip1", "wasm"},
}

func bigIntPlanWordBits(goarch string) uint64 {
	if goarch == "386" {
		return 32
	}
	return 64
}

// bigIntPlanRound is the page-rounded allocation envelope, in math/big.
func bigIntPlanRound(bytes *big.Int) *big.Int {
	page := big.NewInt(int64(bigIntPage))
	r := new(big.Int).Add(bytes, big.NewInt(int64(bigIntPage-1)))
	return r.Mul(r.Quo(r, page), page)
}

// bigIntEgressPlanOracle recomputes the BigInt egress word plan in
// math/big: B=⌈L·332193/100000⌉ bits, N=⌈B/wordbits⌉ target words, and the
// page-rounded word slice plus big.Int object against the target ceilings.
func bigIntEgressPlanOracle(l uint64, target bigIntTarget) (uint64, bool) {
	b := new(big.Int).Mul(new(big.Int).SetUint64(l), big.NewInt(332193))
	b.Add(b, big.NewInt(99999)).Quo(b, big.NewInt(100000))
	wb := new(big.Int).SetUint64(target.wordBits)
	n := new(big.Int).Add(b, new(big.Int).Sub(wb, big.NewInt(1)))
	n.Quo(n, wb)
	bytes := new(big.Int).Mul(n, new(big.Int).Quo(wb, big.NewInt(8)))
	maxInt, maxObject := new(big.Int).SetUint64(target.maxInt), new(big.Int).SetUint64(target.maxObjectBytes)
	slice, object := bigIntPlanRound(bytes), bigIntPlanRound(big.NewInt(int64(bigIntObjectBytes)))
	total := new(big.Int).Add(slice, object)
	fits := n.Cmp(maxInt) <= 0 && bytes.Cmp(maxInt) <= 0 && slice.Cmp(maxObject) <= 0 &&
		object.Cmp(maxObject) <= 0 && total.Cmp(new(big.Int).SetUint64(target.maxAddressBytes)) <= 0
	if !n.IsUint64() {
		return 0, fits
	}
	return n.Uint64(), fits
}

// bigIntIngressPlanOracle recomputes the FromBigInt ingress plan in
// math/big for an n-bit source: U=1+⌊n·30103/100000⌋ digits, ⌈U/9⌉ uint32
// limbs, the base-10⁹ holder (a three-word slice header plus nine limbs) and
// the live ⌈n/wordbits⌉-word source, each page-rounded, against the target.
func bigIntIngressPlanOracle(n uint64, target bigIntTarget) (outputBytes, sourceBytes uint64, fits bool) {
	u := new(big.Int).Mul(new(big.Int).SetUint64(n), big.NewInt(30103))
	u.Quo(u, big.NewInt(100000)).Add(u, big.NewInt(1))
	limbs := new(big.Int).Add(u, big.NewInt(8))
	limbs.Quo(limbs, big.NewInt(9))
	output := new(big.Int).Mul(limbs, big.NewInt(4))
	holder := big.NewInt(int64(3*target.wordBits/8 + 4*slowSmallLimbs))
	wb := new(big.Int).SetUint64(target.wordBits)
	words := new(big.Int).Add(new(big.Int).SetUint64(n), new(big.Int).Sub(wb, big.NewInt(1)))
	words.Quo(words, wb)
	source := new(big.Int).Mul(words, new(big.Int).Quo(wb, big.NewInt(8)))
	maxInt, maxObject := new(big.Int).SetUint64(target.maxInt), new(big.Int).SetUint64(target.maxObjectBytes)
	total := new(big.Int).Add(bigIntPlanRound(output), bigIntPlanRound(holder))
	total.Add(total, bigIntPlanRound(source))
	fits = limbs.Cmp(maxInt) <= 0 && output.Cmp(maxInt) <= 0 && words.Cmp(maxInt) <= 0 && source.Cmp(maxInt) <= 0 &&
		bigIntPlanRound(output).Cmp(maxObject) <= 0 && bigIntPlanRound(holder).Cmp(maxObject) <= 0 &&
		total.Cmp(new(big.Int).SetUint64(target.maxAddressBytes)) <= 0
	return output.Uint64(), source.Uint64(), fits
}

// bigIntPlanBoundary returns the largest x in [1, hi) that fits, for a
// monotone predicate true at one.
func bigIntPlanBoundary(hi uint64, fits func(uint64) bool) uint64 {
	lo := uint64(1)
	for hi-lo > 1 {
		mid := lo + (hi-lo)/2
		if fits(mid) {
			lo = mid
		} else {
			hi = mid
		}
	}
	return lo
}

// TestIntegerConversionPhysicalWordPlans covers the physical word plans of the
// integer conversions. For native amd64, 386, js/wasm and wasip1/wasm, the
// BigInt egress planner and the FromBigInt ingress preflight, run with no
// logical quota, agree with an independent math/big recomputation of the plan
// at the largest admitted size, one past it, and 200 sizes per target spread
// over that range: a word slice, base-10⁹ holder or combined
// source+holder+result footprint beyond the target's Go int, maxAlloc or
// address window refuses. Word counts and snapshot bytes use the target
// big.Word width (32-bit on 386), not the host's. On the running target, a real
// source whose planned output, holder or combined scratch is one byte beyond a
// synthetic ceiling refuses with InsufficientStorage allocating
// only the error, and the equality ceiling admits the exact value. Runtime OOM
// stays outside the returned-error guarantee.
func TestIntegerConversionPhysicalWordPlans(t *testing.T) {
	r := rand.New(rand.NewSource(0xdec018))
	var egressLimits, ingressLimits []uint64
	for _, tc := range bigIntPlanTargets {
		target := bigIntTargetFor(tc.goos, tc.goarch, bigIntPlanWordBits(tc.goarch))
		if target.wordBits == 0 {
			t.Fatalf("%s/%s: no plan", tc.goos, tc.goarch)
		}
		name := tc.goos + "/" + tc.goarch
		oracleEgress := func(l uint64) bool { _, fits := bigIntEgressPlanOracle(l, target); return fits }
		lMax := bigIntPlanBoundary(1<<50, oracleEgress)
		egressLimits = append(egressLimits, lMax)
		for _, l := range []uint64{1, 10, 19, 20, lMax - 1, lMax, lMax + 1, 1 << 50, math.MaxUint64} {
			wantCount, wantFits := bigIntEgressPlanOracle(l, target)
			count, fits := bigIntEgressWordsForTarget(l, target)
			if fits != wantFits || fits && count != wantCount {
				t.Fatalf("%s egress L=%d: (%d, %t), oracle (%d, %t)", name, l, count, fits, wantCount, wantFits)
			}
		}
		for range 200 {
			l := 1 + r.Uint64()%(2*lMax)
			wantCount, wantFits := bigIntEgressPlanOracle(l, target)
			if count, fits := bigIntEgressWordsForTarget(l, target); fits != wantFits || fits && count != wantCount {
				t.Fatalf("%s egress L=%d: (%d, %t), oracle (%d, %t)", name, l, count, fits, wantCount, wantFits)
			}
		}
		oracleIngress := func(n uint64) bool { _, _, fits := bigIntIngressPlanOracle(n, target); return fits }
		nMax := bigIntPlanBoundary(1<<56, oracleIngress)
		ingressLimits = append(ingressLimits, nMax)
		for _, n := range []uint64{1, 33, 65, nMax - 1, nMax, nMax + 1, 1 << 56} {
			wantOutput, wantSource, wantFits := bigIntIngressPlanOracle(n, target)
			plan, fits := bigIntIngressPreflight(n, Budget{}, target)
			if fits != wantFits || fits && (plan.outputBytes != wantOutput || plan.sourceBytes != wantSource) {
				t.Fatalf("%s ingress n=%d: (%+v, %t), oracle (%d, %d, %t)", name, n, plan, fits, wantOutput, wantSource, wantFits)
			}
		}
		for range 200 {
			n := 1 + r.Uint64()%(2*nMax)
			_, _, wantFits := bigIntIngressPlanOracle(n, target)
			if _, fits := bigIntIngressPreflight(n, Budget{}, target); fits != wantFits {
				t.Fatalf("%s ingress n=%d: fits=%t, oracle %t", name, n, fits, wantFits)
			}
		}
		// Target word width: one bit needs one 4-byte word on 386 and one
		// 8-byte word elsewhere; ten digits need two 32-bit or one 64-bit word.
		plan, _ := bigIntIngressPreflight(1, Budget{}, target)
		count, _ := bigIntEgressWordsForTarget(10, target)
		if plan.sourceBytes != target.wordBits/8 || count != 64/target.wordBits {
			t.Fatalf("%s: snapshot bytes %d and ten-digit words %d ignore the %d-bit word", name, plan.sourceBytes, count, target.wordBits)
		}
	}
	// 386 has the narrowest window, native 64-bit the widest.
	if !(egressLimits[1] < egressLimits[2] && egressLimits[2] < egressLimits[0]) ||
		!(ingressLimits[1] < ingressLimits[2] && ingressLimits[2] < ingressLimits[0]) {
		t.Fatalf("target windows not ordered: egress %v ingress %v", egressLimits, ingressLimits)
	}

	// Live refusal on the running target, logical quotas zero.
	x := bigIntFixture(t, "-"+strings.Repeat("7", 500))
	host := bigIntIngressRuntimeTarget()
	plan, ok := bigIntIngressPreflight(uint64(x.BitLen()), Budget{}, host)
	if !ok {
		t.Fatal("live fixture refused on the running target")
	}
	total := plan.sourceRoundedBytes + plan.outputRoundedBytes + plan.holderRoundedBytes
	exactObject := max(plan.outputRoundedBytes, plan.holderRoundedBytes)
	for _, tc := range []struct {
		name            string
		object, address uint64
		admit           bool
	}{
		{"object ceiling one below", exactObject - 1, total, false},
		{"combined scratch one below", exactObject, total - 1, false},
		{"equality ceilings", exactObject, total, true},
	} {
		limit := host
		limit.maxObjectBytes, limit.maxAddressBytes = tc.object, tc.address
		allocs := testing.AllocsPerRun(10, func() {
			bigIntIngressResultSink, bigIntIngressErrorSink = fromBigIntOnTarget(x, Budget{}, "FromBigInt", limit)
		})
		if !tc.admit {
			checkIngressError(t, bigIntIngressResultSink, bigIntIngressErrorSink, "FromBigInt", ErrInsufficientStorage, InsufficientStorage)
			if allocs > 1 {
				t.Fatalf("%s: refusal allocations=%g, want at most the error", tc.name, allocs)
			}
			continue
		}
		if bigIntIngressErrorSink != nil || bigIntIngressResultSink.String() != x.String() {
			t.Fatalf("%s: (%s, %v)", tc.name, bigIntIngressResultSink.String(), bigIntIngressErrorSink)
		}
	}
}

// TestBigIntRatReuseDestination checks that BigInt and Rat set
// and return a non-nil destination, BigInt reusing its words when they have
// room (no allocation), a nil destination allocates, and a refusal leaves
// the destination unmodified. The oracle is math/big's SetString.
func TestBigIntRatReuseDestination(t *testing.T) {
	z := new(big.Int).Lsh(big.NewInt(1), 400) // room for any value below
	for _, tc := range []struct{ text, want string }{
		{"0", "0"}, {"-7", "-7"}, {"123456789012345678901234567890", "123456789012345678901234567890"},
		{"-9E+30", "-9000000000000000000000000000000"}, {"4.50E+1", "45"},
	} {
		want, _ := new(big.Int).SetString(tc.want, 10)
		got, err := MustParse(tc.text).BigInt(z)
		if err != nil || got != z || got.Cmp(want) != 0 {
			t.Fatalf("BigInt(%s, z) = %v (%p, z %p), %v; want %s in z", tc.text, got, got, z, err, tc.want)
		}
		if fresh, err := MustParse(tc.text).BigInt(nil); err != nil || fresh == z || fresh.Cmp(want) != 0 {
			t.Fatalf("BigInt(%s, nil) = %v, %v", tc.text, fresh, err)
		}
	}
	d := MustParse("123456789012345678901234567890")
	if allocs := testing.AllocsPerRun(20, func() { _, _ = d.BigInt(z) }); allocs != 0 {
		t.Fatalf("BigInt into a roomy destination allocated %v times", allocs)
	}
	before := new(big.Int).Set(z)
	if _, err := MustParse("1.5").BigInt(z); !errors.Is(err, ErrNonIntegral) || z.Cmp(before) != 0 {
		t.Fatalf("refusal modified z: %v, %v", z, err)
	}
	r := new(big.Rat).SetFrac64(22, 7)
	for _, tc := range []struct{ text, want string }{{"0", "0"}, {"-1.25", "-5/4"}, {"3E+2", "300"}, {"0.1", "1/10"}} {
		want, _ := new(big.Rat).SetString(tc.want)
		got, err := MustParse(tc.text).Rat(r)
		if err != nil || got != r || got.Cmp(want) != 0 {
			t.Fatalf("Rat(%s, r) = %v, %v; want %s in r", tc.text, got, err, tc.want)
		}
	}
	rb := new(big.Rat).Set(r)
	if _, err := MustParse("1E+100").RatWithBudget(r, Budget{MaxDigits: 3}); !errors.Is(err, ErrInsufficientStorage) || r.Cmp(rb) != 0 {
		t.Fatalf("Rat refusal modified r: %v, %v", r, err)
	}
}

// TestBigIntInlineMatchesGeneral pins FromBigInt of at most 128 bits and
// BigInt of an inline coefficient to the general conversions, which a
// never-binding budget selects, and to math/big itself: every bit length
// around the word and inline boundaries, both signs, scaled and exactly
// divisible exponents, the fractional refusal and a reused destination.
func TestBigIntInlineMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewSource(0x626967))
	general := Budget{MaxWork: math.MaxUint64}
	var ingress, egress, fractional int
	for i := range 100000 {
		v := new(big.Int).SetUint64(rng.Uint64())
		v.Lsh(v, 64).Or(v, new(big.Int).SetUint64(rng.Uint64()))
		switch i % 4 {
		case 0:
			v.Rsh(v, uint(rng.Intn(129)))
		case 1: // around a power of two
			v.Lsh(big.NewInt(1), uint(rng.Intn(131))).Add(v, big.NewInt(int64(rng.Intn(5)-2)))
		case 2:
			v.Rsh(v, uint(64+rng.Intn(64)))
		}
		if rng.Intn(2) == 0 {
			v.Neg(v)
		}
		got, err := FromBigInt(v)
		want, werr := fromBigIntOnTarget(v, Budget{}, "FromBigInt", bigIntIngressRuntimeTarget())
		requireSameOutcome(t, "FromBigInt", v.String(), got, 0, err, want, 0, werr)
		if err != nil || got.coefficientDigits() != new(big.Int).Abs(v).String() || got.negative() != (v.Sign() < 0) {
			t.Fatalf("FromBigInt(%s) = %v, %v", v, got, err)
		}
		if v.BitLen() <= 128 {
			ingress++
		}

		// Egress at an exponent that scales, divides exactly or leaves a
		// fraction.
		d := got
		if d.slow == nil {
			d = d.withExponent(int32(rng.Intn(31) - 20))
		}
		z, err := d.BigInt(nil)
		reference, werr := d.bigIntWithBudget(nil, general, "BigInt")
		if (err == nil) != (werr == nil) || err != nil && err.Error() != werr.Error() {
			t.Fatalf("%v.BigInt(): %v, general %v", d, err, werr)
		}
		if err != nil {
			fractional++
			continue
		}
		if z.Cmp(reference) != 0 || cap(z.Bits()) != cap(reference.Bits()) {
			t.Fatalf("%v.BigInt() = %s (cap %d), general %s (cap %d)", d, z, cap(z.Bits()), reference, cap(reference.Bits()))
		}
		reused := new(big.Int).Lsh(big.NewInt(1), 300)
		if again, err := d.BigInt(reused); err != nil || again != reused || again.Cmp(reference) != 0 {
			t.Fatalf("%v.BigInt(reused) = %s, %v", d, again, err)
		}
		egress++
	}
	if ingress < 50000 || egress < 20000 || fractional < 10000 {
		t.Fatalf("vacuous path coverage: %d ingress, %d egress, %d fractional", ingress, egress, fractional)
	}
	var nilInt *big.Int
	if _, err := FromBigInt(nilInt); !errors.Is(err, ErrConversionSyntax) {
		t.Fatalf("FromBigInt(nil): %v", err)
	}
}
