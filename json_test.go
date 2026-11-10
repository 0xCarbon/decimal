// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"math/big"
	"math/rand"
	"slices"
	"strconv"
	"strings"
	"testing"
	"unicode/utf8"
)

var _ json.Marshaler = Decimal{}
var _ json.Unmarshaler = (*Decimal)(nil)

func TestInteropJSONMarshalRoundTripCohort(t *testing.T) {
	for _, tc := range []struct {
		input, digits, canonical string
		exponent                 int32
	}{
		{"1.10", "110", "1.10", -2},
		{"-12.300", "12300", "-12.300", -3},
		{"0E+2", "0", "0E+2", 2},
		{"-0.00", "0", "0.00", -2},
		{"1E-7", "1", "1E-7", -7},
		{strings.Repeat("9", 70) + ".00", strings.Repeat("9", 70) + "00", strings.Repeat("9", 70) + ".00", -2},
	} {
		t.Run(tc.input, func(t *testing.T) {
			original := MustParse(tc.input)
			raw, err := original.MarshalJSON()
			if err != nil || string(raw) != tc.canonical || !json.Valid(raw) || raw[0] == '"' {
				t.Fatalf("MarshalJSON=%q, %v", raw, err)
			}
			std, err := json.Marshal(original)
			if err != nil || !bytes.Equal(std, raw) {
				t.Fatalf("json.Marshal=%q, %v", std, err)
			}
			var decoded Decimal
			if err := json.Unmarshal(std, &decoded); err != nil {
				t.Fatal(err)
			}
			if decoded.coefficientDigits() != tc.digits || decoded.exponent() != tc.exponent || decoded.negative() != original.negative() {
				t.Fatalf("round-trip cohort: digits=%q exponent=%d negative=%v", decoded.coefficientDigits(), decoded.exponent(), decoded.negative())
			}
			got, ok := new(big.Rat).SetString(decoded.String())
			if !ok || got.Cmp(inboundTextOracle(tc.digits, tc.exponent, decoded.negative())) != 0 {
				t.Fatal("round-trip numerical oracle disagrees")
			}
		})
	}
}

func TestInteropJSONFramingAndBudget(t *testing.T) {
	for _, tc := range []struct {
		name, raw, canonical, digits string
		exponent                     int32
	}{
		{"bare-cohort", ` 1.10 `, "1.10", "110", -2},
		{"quoted-scale", `"2.50"`, "2.50", "250", -2},
		{"escaped-digit", ` "\u0031.10" `, "1.10", "110", -2},
		{"quoted-liberal", `"01"`, "1", "1", 0},
		{"quoted-exponent", `"+1e2"`, "1E+2", "1", 2},
		{"integer-above-binary64-exact-range", `9007199254740993`, "9007199254740993", "9007199254740993", 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			raw := []byte(tc.raw)
			got, err := ParseJSONWithBudget(raw, Budget{MaxInputBytes: uint64(len(raw)), MaxDigits: uint64(len(tc.digits))})
			if err != nil {
				t.Fatal(err)
			}
			if got.String() != tc.canonical || got.coefficientDigits() != tc.digits || got.exponent() != tc.exponent {
				t.Fatalf("cohort=%q/%q/%d", got.String(), got.coefficientDigits(), got.exponent())
			}
			var method Decimal
			if err := method.UnmarshalJSON(raw); err != nil || !method.Equal(got) || method.exponent() != got.exponent() {
				t.Fatalf("UnmarshalJSON=%q, %v", method.String(), err)
			}
			for i := range raw {
				raw[i] = '!'
			}
			if got.String() != tc.canonical || method.String() != tc.canonical {
				t.Fatal("result aliases caller raw bytes")
			}
		})
	}

	raw := []byte(` "\u0031.10" `)
	checkJSONOperationError(t, raw, Budget{MaxInputBytes: uint64(len(raw) - 1)}, "ParseJSONWithBudget", ErrInsufficientStorage)
	// A decoded digit-cap refusal is a resource refusal of bytes: an
	// *Error without a copy.
	checkJSONOperationError(t, raw, Budget{MaxInputBytes: uint64(len(raw)), MaxDigits: 2}, "ParseJSONWithBudget", ErrInsufficientStorage)
	checkJSONOperationError(t, []byte(`01`), Budget{MaxInputBytes: 1}, "ParseJSONWithBudget", ErrInsufficientStorage)
	checkJSONParseError(t, []byte(`01`), Budget{}, "ParseJSONWithBudget", ErrConversionSyntax, "01")
	checkJSONParseError(t, []byte(`"123e9999999999999999999"`), Budget{MaxDigits: 1}, "ParseJSONWithBudget", ErrExponentRange, "123e9999999999999999999")
	for _, raw := range [][]byte{[]byte(`null`), []byte(`true`), []byte(`[]`), []byte(`{}`), []byte("\v\"1\"")} {
		checkJSONParseError(t, raw, Budget{}, "ParseJSONWithBudget", ErrConversionSyntax, string(bytes.Trim(raw, " \t\r\n")))
	}
	checkJSONParseError(t, []byte(`"null"`), Budget{}, "ParseJSONWithBudget", ErrConversionSyntax, "null")
	badUTF8 := []byte{'"', 0xff, '"'}
	if !json.Valid(badUTF8) {
		t.Fatal("active Go JSON validity path changed")
	}
	checkJSONParseError(t, badUTF8, Budget{}, "ParseJSONWithBudget", ErrConversionSyntax, string(badUTF8))
	checkJSONParseError(t, []byte(`"\ud800"`), Budget{}, "ParseJSONWithBudget", ErrConversionSyntax, string(utf8.RuneError))
}

func checkJSONOperationError(t *testing.T, raw []byte, budget Budget, op string, code ErrorCode) {
	t.Helper()
	got, err := ParseJSONWithBudget(raw, budget)
	var oe *Error
	if !errors.Is(err, code) || !errors.As(err, &oe) || oe.Op != op || oe.Code != code || oe.Condition != InsufficientStorage || got.coefficientDigits() != "0" || got.exponent() != 0 {
		t.Fatalf("operation error: result=%q error=%#v", got.String(), err)
	}
}

func checkJSONParseError(t *testing.T, raw []byte, budget Budget, op string, code ErrorCode, input string) {
	t.Helper()
	got, err := ParseJSONWithBudget(raw, budget)
	var pe *Error
	condition := ConversionSyntax
	if code == ErrExponentRange {
		condition = 0
	} else if code == ErrInsufficientStorage {
		condition = InsufficientStorage
	}
	if !errors.Is(err, code) || !errors.As(err, &pe) || pe.Op != op || pe.Input != input || pe.Code != code || pe.Condition != condition || got.coefficientDigits() != "0" || got.exponent() != 0 {
		t.Fatalf("parse error: result=%q error=%#v; want input %q", got.String(), err, input)
	}
}

func TestInteropJSONReceiverAtomicityAndPointerSlot(t *testing.T) {
	previous := MustParse(strings.Repeat("9", 70) + ".00")
	before := previous.slow
	for _, tc := range []struct {
		raw, input []byte
	}{
		{[]byte(`null`), []byte(`null`)},
		{[]byte(`01`), []byte(`01`)},
		{[]byte(`"invalid"`), []byte(`invalid`)},
		{[]byte{'"', 0xff, '"'}, []byte{'"', 0xff, '"'}},
	} {
		got := previous
		err := got.UnmarshalJSON(tc.raw)
		var pe *Error
		if !errors.Is(err, ErrConversionSyntax) || !errors.As(err, &pe) || pe.Op != "UnmarshalJSON" || got.slow != before || got.String() != previous.String() {
			t.Fatalf("receiver changed on %q: error=%v", tc.raw, err)
		}
		tc.raw[0] = '!'
		if pe.Input != string(tc.input) {
			t.Fatalf("error Input aliases caller bytes: got %q, want %q", pe.Input, tc.input)
		}
	}
	var nilReceiver *Decimal
	err := nilReceiver.UnmarshalJSON([]byte(`01`))
	var oe *Error
	if !errors.Is(err, ErrInvalidOperation) || !errors.As(err, &oe) || oe.Op != "UnmarshalJSON" || oe.Condition != InvalidOperation {
		t.Fatalf("nil receiver precedence: %v", err)
	}
	var invalidArgument *json.InvalidUnmarshalError
	if err := json.Unmarshal([]byte(`01`), nilReceiver); !errors.As(err, &invalidArgument) {
		t.Fatalf("top-level nil destination must retain stdlib error: %v", err)
	}
	var slot struct{ Value *Decimal }
	if err := json.Unmarshal([]byte(`{"Value":"invalid"}`), &slot); err == nil || slot.Value == nil {
		t.Fatalf("stdlib pointer slot behavior: slot=%+v error=%v", slot, err)
	}
	if err := json.Unmarshal([]byte(`{"Value":null}`), &slot); err != nil || slot.Value != nil {
		t.Fatalf("stdlib null slot behavior: slot=%+v error=%v", slot, err)
	}
	preloaded := previous
	err = json.Unmarshal([]byte(`null`), &preloaded)
	if !errors.Is(err, ErrConversionSyntax) || preloaded.slow != before || preloaded.String() != previous.String() {
		t.Fatalf("stdlib bare Decimal null behavior: result=%q error=%v", preloaded.String(), err)
	}
}

func TestJSONDecodeEnvelopeBoundaries(t *testing.T) {
	for _, tc := range []struct {
		raw, decoded, maxObject uint64
		ok                      bool
	}{
		{2, 0, 2, true}, {10, 8, 10, true}, {10, 9, 10, false}, {10, 8, 9, false},
		{(1 << 32) - 1, (1 << 32) - 3, (1 << 32) - 1, true},
		{^uint64(0), ^uint64(0) - 2, ^uint64(0), false},
	} {
		_, ok := jsonDecodeEnvelope(tc.raw, tc.decoded, tc.maxObject)
		if ok != tc.ok {
			t.Fatalf("jsonDecodeEnvelope(%d,%d,%d)=%v", tc.raw, tc.decoded, tc.maxObject, ok)
		}
	}
}

func TestJSONQuotedDecoderMatchesStdlib(t *testing.T) {
	atoms := []string{"0", "1", ".", "e", "-", "+", `\u0031`, `\uD800`, `\uD834\uDD1E`, `\n`, "é", `/`, `\/`}
	count := 0
	for _, a := range atoms {
		for _, b := range atoms {
			token := []byte(`"` + a + b + `"`)
			if !json.Valid(token) {
				continue
			}
			var want string
			if err := json.Unmarshal(token, &want); err != nil {
				t.Fatal(err)
			}
			n, ok := walkJSONQuoted(token, nil)
			if !ok {
				t.Fatalf("count refused %q", token)
			}
			buf := make([]byte, n)
			m, ok := walkJSONQuoted(token, buf)
			if !ok || m != n || string(buf) != want {
				t.Fatalf("decode %q = %q, want %q", token, buf, want)
			}
			count++
		}
	}
	for value := range 256 {
		token := []byte(fmt.Sprintf("\"\\u%04x\"", value))
		var want string
		if err := json.Unmarshal(token, &want); err != nil {
			t.Fatal(err)
		}
		n, ok := walkJSONQuoted(token, nil)
		if !ok {
			t.Fatalf("hex count refused %q", token)
		}
		buf := make([]byte, n)
		m, ok := walkJSONQuoted(token, buf)
		if !ok || m != n || string(buf) != want {
			t.Fatalf("hex decode %q = %q, want %q", token, buf, want)
		}
		count++
	}
	if count != 425 {
		t.Fatalf("valid pair count=%d", count)
	}
}

// TestJSONNullIntoPointerField decodes JSON null into a pointer
// slot directly.
func TestJSONNullIntoPointerField(t *testing.T) {
	preloaded := MustParse(strings.Repeat("9", 70) + ".00")
	holder := preloaded.slow
	err := preloaded.UnmarshalJSON([]byte(`null`))
	var parse *Error
	if !errors.Is(err, ErrConversionSyntax) || !errors.As(err, &parse) ||
		parse.Op != "UnmarshalJSON" || parse.Input != "null" ||
		preloaded.slow != holder || preloaded.exponent() != -2 {
		t.Fatalf("direct null changed preloaded Decimal: error=%#v", err)
	}
	var nilReceiver *Decimal
	err = nilReceiver.UnmarshalJSON([]byte(`1.10`))
	var operation *Error
	if !errors.Is(err, ErrInvalidOperation) || !errors.As(err, &operation) ||
		operation.Op != "UnmarshalJSON" || operation.Condition != InvalidOperation {
		t.Fatalf("valid input on direct nil receiver: error=%#v", err)
	}
	var slot struct{ Value *Decimal }
	err = json.Unmarshal([]byte(`{"Value":"bad"}`), &slot)
	if !errors.Is(err, ErrConversionSyntax) || slot.Value == nil {
		t.Fatalf("failed callback did not retain allocated pointer slot: slot=%+v error=%v", slot, err)
	}
}

// TestInteropJSONQuotedInputAccepted accepts quoted JSON input.
func TestInteropJSONQuotedInputAccepted(t *testing.T) {
	var got Decimal
	if err := got.UnmarshalJSON([]byte(`"2.50"`)); err != nil {
		t.Fatal(err)
	}
	if got.coefficientDigits() != "250" || got.exponent() != -2 || got.negative() {
		t.Fatalf("quoted scale lost: digits=%q exponent=%d negative=%v", got.coefficientDigits(), got.exponent(), got.negative())
	}
}

// TestInteropJSONQuotedLiberalBeforeParser applies the quoted-literal
// syntax before the parser.
func TestInteropJSONQuotedLiberalBeforeParser(t *testing.T) {
	scaled, err := ParseJSONWithBudget([]byte(`"1.10"`), Budget{})
	if err != nil || scaled.coefficientDigits() != "110" || scaled.exponent() != -2 {
		t.Fatalf("quoted 1.10 scale changed: digits=%q exponent=%d error=%v", scaled.coefficientDigits(), scaled.exponent(), err)
	}
	got, err := ParseJSONWithBudget([]byte(`"01"`), Budget{})
	if err != nil || got.coefficientDigits() != "1" || got.exponent() != 0 {
		t.Fatalf("quoted liberal decimal=%q, %v", got.String(), err)
	}
	_, err = ParseJSONWithBudget([]byte(`01`), Budget{})
	var parse *Error
	if !errors.Is(err, ErrConversionSyntax) || !errors.As(err, &parse) || parse.Op != "ParseJSONWithBudget" || parse.Input != "01" {
		t.Fatalf("bare invalid JSON number=%#v", err)
	}
}

// TestInteropJSONRawPrechargeAndDecodedDigitCap covers the raw-byte
// precharge and the decoded digit cap.
func TestInteropJSONRawPrechargeAndDecodedDigitCap(t *testing.T) {
	raw := []byte(` "\u0031.10" `)
	R := uint64(len(raw))
	value, err := ParseJSONWithBudget(raw, Budget{MaxInputBytes: R - 1})
	var operation *Error
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) ||
		operation.Op != "ParseJSONWithBudget" || operation.Condition != InsufficientStorage ||
		value.coefficientDigits() != "0" || value.exponent() != 0 {
		t.Fatalf("R-1 precharge: value=%q error=%#v", value.String(), err)
	}
	// The decoded digit-cap refusal is a resource refusal of bytes: an
	// *Error without a copy.
	value, err = ParseJSONWithBudget(raw, Budget{MaxInputBytes: R, MaxDigits: 2})
	operation = nil
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) ||
		operation.Op != "ParseJSONWithBudget" || operation.Condition != InsufficientStorage ||
		value.coefficientDigits() != "0" || value.exponent() != 0 {
		t.Fatalf("decoded d-1 cap: value=%q error=%#v", value.String(), err)
	}
	value, err = ParseJSONWithBudget(raw, Budget{MaxInputBytes: R, MaxDigits: 3})
	if err != nil || value.coefficientDigits() != "110" || value.exponent() != -2 {
		t.Fatalf("R/d exact admission: value=%q error=%v", value.String(), err)
	}
	_, err = ParseJSONWithBudget([]byte(`01`), Budget{MaxInputBytes: 1})
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) {
		t.Fatalf("invalid JSON must still be precharged before framing: %v", err)
	}
	_, err = ParseJSONWithBudget([]byte(`"12x"`), Budget{MaxDigits: 1})
	var parse *Error
	if !errors.Is(err, ErrConversionSyntax) || !errors.As(err, &parse) || parse.Input != "12x" {
		t.Fatalf("decoded syntax must precede digit cap: %v", err)
	}
}

// TestJSONNumberAgainstEncodingJSON pins the direct number-token validator
// to encoding/json on random strings over the number alphabet: a string is a
// number token exactly when json.Valid accepts it and it starts like one.
func TestJSONNumberAgainstEncodingJSON(t *testing.T) {
	r := rand.New(rand.NewSource(20261005))
	const alphabet = "-+0123456789.eE"
	accepted := 0
	for range 500_000 {
		b := make([]byte, 1+r.Intn(8))
		for i := range b {
			b[i] = alphabet[r.Intn(len(alphabet))]
		}
		want := json.Valid(b) && (b[0] == '-' || '0' <= b[0] && b[0] <= '9')
		if got := jsonNumber(b); got != want {
			t.Fatalf("jsonNumber(%q) = %v, encoding/json says %v", b, got, want)
		}
		if want {
			accepted++
		}
	}
	if accepted < 10_000 {
		t.Fatalf("only %d valid numbers sampled", accepted)
	}
}

// TestInteropJSONInboundCarriersAndReceiverOwnership covers the inbound
// predecode and postdecode error carriers, error identity and receiver
// ownership with escaped quoted tokens, so the
// decoded text differs from the raw bytes:
//   - a nil *Decimal receiver gives UnmarshalJSON
//     *Error / ErrInvalidOperation before reading its input;
//   - a raw byte cap of R−1 refuses before decode with ParseJSONWithBudget
//     *Error / ErrInsufficientStorage;
//   - decoded syntax ("\u0031_0" decodes to 1_0) and decoded exponent range
//     ("\u0031e2147483648") give *Error carrying the decoded Input
//     with ErrConversionSyntax/ConversionSyntax and ErrExponentRange with
//     zero condition respectively;
//   - a decoded coefficient-budget failure is an *Error with
//     ErrInsufficientStorage and an empty Input;
//   - after each receiver failure a preexisting slow-band Decimal keeps its
//     holder, exponent, sign and text.
func TestInteropJSONInboundCarriersAndReceiverOwnership(t *testing.T) {
	syntax := []byte("\"\\u0031_0\"")
	rangeToken := []byte("\"\\u0031e2147483648\"")
	digits := []byte("\"\\u0031234\"")
	for _, raw := range [][]byte{syntax, rangeToken, digits} {
		if !bytes.Contains(raw, []byte(`\u0031`)) || raw[0] != '"' {
			t.Fatalf("token %q lost its escape", raw)
		}
	}
	var nilReceiver *Decimal
	err := nilReceiver.UnmarshalJSON(syntax)
	var op *Error
	if !errors.Is(err, ErrInvalidOperation) || !errors.As(err, &op) || op.Op != "UnmarshalJSON" || op.Condition != InvalidOperation {
		t.Fatalf("nil receiver: %#v", err)
	}
	value, err := ParseJSONWithBudget(digits, Budget{MaxInputBytes: uint64(len(digits)) - 1})
	op = nil
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &op) || op.Op != "ParseJSONWithBudget" ||
		op.Condition != InsufficientStorage || !isZeroValue(value) {
		t.Fatalf("predecode R-1 refusal: %v, %#v", value, err)
	}
	value, err = ParseJSONWithBudget(digits, Budget{MaxDigits: 3})
	op = nil
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &op) || op.Op != "ParseJSONWithBudget" ||
		op.Condition != InsufficientStorage || op.Input != "" || !isZeroValue(value) {
		t.Fatalf("decoded coefficient cap: %v, %#v", value, err)
	}
	if value, err = ParseJSONWithBudget(digits, Budget{MaxDigits: 4}); err != nil || value.String() != "1234" {
		t.Fatalf("decoded coefficient at cap: %v, %v", value, err)
	}
	holder := MustParse(strings.Repeat("9", 70) + ".00")
	slow, exponent, text := holder.slow, holder.exponent(), holder.String()
	for _, tc := range []struct {
		raw       []byte
		input     string
		code      error
		condition Conditions
	}{
		{syntax, "1_0", ErrConversionSyntax, ConversionSyntax},
		{rangeToken, "1e2147483648", ErrExponentRange, 0},
	} {
		got := holder
		err := got.UnmarshalJSON(tc.raw)
		var parse *Error
		if !errors.Is(err, tc.code) || !errors.As(err, &parse) || parse.Op != "UnmarshalJSON" ||
			parse.Input != tc.input || parse.Condition != tc.condition {
			t.Fatalf("UnmarshalJSON(%s): %#v; want Error input %q", tc.raw, err, tc.input)
		}
		if got.slow != slow || got.exponent() != exponent || got.negative() || got.String() != text {
			t.Fatalf("UnmarshalJSON(%s) changed its receiver to %v", tc.raw, got)
		}
	}
	got := holder
	if err := got.UnmarshalJSON([]byte("\"\\u0031.10\"")); err != nil || got.String() != "1.10" || got.exponent() != -2 {
		t.Fatalf("escaped success: %v, %v", got, err)
	}
}

// TestJSONQuotedDecoderAllocationPlan checks the JSON decoder allocation
// plan on the actual quoted decoder, with
// counted allocations (testing.AllocsPerRun) and allocated bytes
// (runtime.MemStats) on every executed target, including js/wasm:
//   - predecode refusal: a raw byte cap of R−1 refuses with one small
//     allocation (the error) whose bytes do not grow with R (64 KiB and
//     256 KiB tokens);
//   - an escaped token of D = 64 KiB decoded bytes succeeds with exactly
//     one more allocation than the equivalent unescaped token (the single
//     decode buffer), and the extra bytes lie in [D − 1 KiB, D + 8 KiB]
//     (size classes of the other objects differ by a few bytes);
//   - a decoded coefficient-budget refusal allocates only the decode buffer
//     and the error, with no copy of the input (two allocations);
//   - a short escaped token decodes without heap allocation.
func TestJSONQuotedDecoderAllocationPlan(t *testing.T) {
	const d = 64 << 10
	token := func(n int, escaped bool) []byte {
		body := strings.Repeat("7", n-1)
		if escaped {
			return []byte("\"\\u0031" + body + "\"")
		}
		return []byte("\"1" + body + "\"")
	}
	allocs := func(raw []byte, budget Budget) (float64, uint64) {
		run := func() { _, _ = ParseJSONWithBudget(raw, budget) }
		// Both operands of the byte comparison need an uncontaminated
		// sample. A zero limit takes the least of all three cold readings;
		// unrelated goroutines can only add to TotalAlloc.
		bytes := coldAllocatedWithin(run, 0)
		return testing.AllocsPerRun(20, run), bytes
	}
	var refusalBytes []uint64
	for _, n := range []int{d, 4 * d} {
		raw := token(n, true)
		count, bytes := allocs(raw, Budget{MaxInputBytes: uint64(len(raw)) - 1})
		if count != 1 || bytes >= 256 {
			t.Fatalf("predecode refusal at R=%d: %v allocations, %d bytes; want one small error", len(raw), count, bytes)
		}
		refusalBytes = append(refusalBytes, bytes)
	}
	if refusalBytes[0] != refusalBytes[1] {
		t.Fatalf("predecode refusal bytes grow with R: %v", refusalBytes)
	}
	escaped, plain := token(d, true), token(d, false)
	if n, ok := walkJSONQuoted(escaped, nil); !ok || n != d {
		t.Fatalf("escaped token decodes to %d bytes, %v; want %d", n, ok, d)
	}
	escapedCount, escapedBytes := allocs(escaped, Budget{})
	plainCount, plainBytes := allocs(plain, Budget{})
	if escapedCount != plainCount+1 || escapedBytes+1<<10 < plainBytes+d || escapedBytes > plainBytes+d+8<<10 {
		t.Fatalf("escaped success: %v allocations, %d bytes; unescaped %v, %d; want one D-byte decode buffer more",
			escapedCount, escapedBytes, plainCount, plainBytes)
	}
	capCount, capBytes := allocs(escaped, Budget{MaxDigits: 2})
	if capCount != 2 || capBytes+1<<10 < d || capBytes > d+8<<10 {
		t.Fatalf("decoded digit-cap refusal: %v allocations, %d bytes; want the decode buffer and the error only", capCount, capBytes)
	}
	if count := testing.AllocsPerRun(20, func() { _, _ = ParseJSONWithBudget([]byte("\"\\u0031.10\""), Budget{}) }); count != 0 {
		t.Fatalf("short escaped token: %v allocations, want 0", count)
	}
}

// jsonFastPins counts the tokens checked by checkJSONDecodeFast and how the
// fast path treated them; the counts are the test's.
type jsonFastPins struct {
	cases, fastBare, fastQuoted, deferred, deferredValid, budgetDeferred int
}

// checkJSONDecodeFast pins parseJSONWithBudget (with decodeJSONInline) to
// parseJSONGeneral, result for result and error for error, and every
// fast-path result to independent oracles: encoding/json.Valid and
// json.Unmarshal for the token's text, then parseOracle (regexp, math/big)
// and big.Rat for its value.
func checkJSONDecodeFast(t *testing.T, raw string, budget Budget, pins *jsonFastPins) {
	pins.cases++
	token := trimJSONSpace([]byte(raw))
	_, inline := decodeJSONInline(token, 0)
	_, fast := decodeJSONInline(token, budget.MaxDigits)
	fast = fast && (budget.MaxInputBytes == 0 || uint64(len(raw)) <= budget.MaxInputBytes)
	got, gotErr := parseJSONWithBudget([]byte(raw), budget.text(), "ParseJSONWithBudget")
	general, generalErr := parseJSONGeneral([]byte(raw), budget.text(), "ParseJSONWithBudget")
	if !sameParseFailure(gotErr, generalErr) || got.words != general.words || got.meta != general.meta ||
		(got.slow == nil) != (general.slow == nil) || got.slow != nil && !slices.Equal(got.slow.limbs, general.slow.limbs) {
		t.Fatalf("%q under %+v: (%+v %#x, %v) differs from the general path (%+v %#x, %v)", raw, budget,
			got.words, uint64(got.meta), gotErr, general.words, uint64(general.meta), generalErr)
	}
	valid := json.Valid([]byte(raw))
	if !fast {
		pins.deferred++
		if inline {
			pins.budgetDeferred++
		} else if valid && gotErr == nil {
			pins.deferredValid++
		}
		return
	}
	if !valid || gotErr != nil {
		t.Fatalf("%q under %+v: fast path accepted an input encoding/json rejects (valid=%v, err=%v)", raw, budget, valid, gotErr)
	}
	text := string(token)
	if token[0] == '"' {
		pins.fastQuoted++
		if err := json.Unmarshal([]byte(raw), &text); err != nil || text != string(token[1:len(token)-1]) {
			t.Fatalf("%q: quoted fast path on a token whose decoded text %q is not its raw body (%v)", raw, text, err)
		}
	} else {
		pins.fastBare++
	}
	want := parseOracle(text, Budget{MaxDigits: budget.MaxDigits})
	if want.code != nil || got.slow != nil || got.words != (uint128{lo: want.coefficient.Uint64()}) || !want.coefficient.IsUint64() ||
		got.exponent() != want.exponent || got.negative() != want.negative {
		t.Fatalf("%q: fast path (%+v E%d negative=%v), oracle %+v", raw, got.words, got.exponent(), got.negative(), want)
	}
	if want.exponent > -400 && want.exponent < 400 {
		rat, ok := new(big.Rat).SetString(text)
		mine, ok2 := new(big.Rat).SetString(got.String())
		if !ok || !ok2 || rat.Cmp(mine) != 0 {
			t.Fatalf("%q: big.Rat %v, decoded %v", raw, rat, got)
		}
	}
}

// TestJSONDecodeFastPathMatchesGeneralPath pins the fused JSON decode
// fast path to the general JSON path (parseJSONGeneral) and to
// encoding/json.Valid, json.Unmarshal and big.Rat: every token up to five
// bytes over a JSON-stressing alphabet (with and without whitespace),
// RFC 8259 edge forms (01, -, 1., .5, +1, -0, escaped quoted tokens such as
// "1\u0030"), 19 and 20 digits, random F7-shaped and malformed tokens, and
// input and coefficient-digit budgets at their boundaries with error
// identity. Fast-path counts for bare and quoted tokens and for deferrals
// must exceed floors, and the fast path allocates nothing.
func TestJSONDecodeFastPathMatchesGeneralPath(t *testing.T) {
	var pins jsonFastPins
	alphabet := []byte("019.+-eE\"\\ u")
	var exhaustive func(prefix []byte)
	exhaustive = func(prefix []byte) {
		checkJSONDecodeFast(t, string(prefix), Budget{}, &pins)
		if len(prefix) == 5 {
			return
		}
		for _, c := range alphabet {
			exhaustive(append(prefix, c))
		}
	}
	exhaustive(make([]byte, 0, 5))
	exhaustiveBare, exhaustiveQuoted := pins.fastBare, pins.fastQuoted

	tokens := []string{
		"0", "-0", "01", "-01", "00", "-", "1.", "-1.", ".5", "-.5", "+1", "1e", "1e+", "1E-0", "1.5e-3", "-0.000",
		"0.0e00", "1e000000005", "1e0000000005", "1e999999999", "1e-999999999", "1e2147483648", " 1", "1 ", "\t-2.50\r\n",
		`"1"`, `"01"`, `"+1"`, `".5"`, `"1."`, `"-0.000"`, `"1e5"`, `"1\u0030"`, `"\u0031"`, `"1\/"`, `"1`, `1"`, `"`, `""`,
		`" 1"`, `"1 "`, " \"12.5\" ", `"1x"`, `"NaN"`, "9999999999999999999", "-9999999999999999999", "10000000000000000000",
		"18446744073709551616", `"18446744073709551616"`, "1234567890.123456789", "1234567890.1234567890",
		"0.0000000000000000000000001", `"0.00000000000000000000000001"`, "123456789012345678901234567890",
		"1234567890123456789012345678901", "[1]", "true", "null", "{}",
	}
	rng := rand.New(rand.NewSource(79))
	for range 20000 {
		// F7-shaped tokens, bare and quoted, with occasional exponents.
		v := strconv.Itoa(rng.Intn(1_000_000)) + "." + strconv.Itoa(10+rng.Intn(90))
		if rng.Intn(4) == 0 {
			v = "-" + v
		}
		if rng.Intn(4) == 0 {
			v += "e" + []string{"", "+", "-"}[rng.Intn(3)] + strconv.Itoa(rng.Intn(1000))
		}
		tokens = append(tokens, v, `"`+v+`"`)
	}
	for range 20000 {
		n := rng.Intn(34)
		b := make([]byte, n)
		for i := range b {
			if r := rng.Intn(10); r < 7 {
				b[i] = byte('0' + rng.Intn(10))
			} else {
				b[i] = "-+.eE\" \\"[rng.Intn(8)]
			}
		}
		tokens = append(tokens, string(b))
	}
	for range 3000 {
		// Valid tokens the fast path must defer: 20-40 digits, escapes.
		v := strconv.Itoa(1+rng.Intn(9)) + strconv.FormatUint(rng.Uint64(), 10) + "." + strconv.Itoa(rng.Intn(1_000_000))
		tokens = append(tokens, v, `"`+v+`"`, `"\u003`+v+`"`, `"`+v[:2]+`\u002e5"`)
	}
	for digits := 1; digits <= 21; digits++ {
		body := "9" + strings.Repeat("1", digits-1)
		tokens = append(tokens, body, "-"+body, `"`+body+`"`, "0."+body, body[:1]+"."+body[1:]+"E-3")
	}
	for _, raw := range tokens {
		checkJSONDecodeFast(t, raw, Budget{}, &pins)
		for _, n := range []int{len(raw) - 1, len(raw)} {
			if n > 0 {
				checkJSONDecodeFast(t, raw, Budget{MaxInputBytes: uint64(n)}, &pins)
			}
		}
		token := trimJSONSpace([]byte(raw))
		if len(token) > 1 && token[0] == '"' {
			token = token[1 : len(token)-1]
		}
		if want := parseOracle(string(token), Budget{}); want.code == nil {
			for _, digits := range []int{want.significant - 1, want.significant, want.significant + 1} {
				if digits > 0 {
					checkJSONDecodeFast(t, raw, Budget{MaxDigits: uint64(digits)}, &pins)
				}
			}
		}
	}
	t.Logf("exhaustive bare %d quoted %d; total %+v", exhaustiveBare, exhaustiveQuoted, pins)
	if exhaustiveBare < 500 || exhaustiveQuoted < 100 || pins.fastBare < 40000 || pins.fastQuoted < 40000 ||
		pins.deferred < 250000 || pins.deferredValid < 5000 || pins.budgetDeferred < 20000 {
		t.Fatalf("vacuous coverage: %+v", pins)
	}

	// Refusals keep the general path's identity: the input-byte refusal is an
	// Error, the digit refusal of a quoted or bare token too.
	for _, raw := range []string{"12.50", `"12.50"`} {
		for _, budget := range []Budget{{MaxInputBytes: uint64(len(raw) - 1)}, {MaxDigits: 3}} {
			_, err := ParseJSONWithBudget([]byte(raw), budget)
			var oe *Error
			if !errors.As(err, &oe) || oe.Op != "ParseJSONWithBudget" || !errors.Is(err, ErrInsufficientStorage) || oe.Condition != InsufficientStorage {
				t.Fatalf("%s under %+v: %#v", raw, budget, err)
			}
		}
	}

	for _, raw := range []string{"123456.78", `"123456.78"`, "-0.000", `"1.5e-3"`} {
		b := []byte(raw)
		var d Decimal
		if n := testing.AllocsPerRun(100, func() { _ = d.UnmarshalJSON(b) }); n != 0 {
			t.Errorf("UnmarshalJSON(%s) allocates %v", raw, n)
		}
	}
}

// TestNullDecimalJSON checks that NullDecimal round-trips JSON
// null and numbers through encoding/json (the oracle), a null field clears
// a populated value, invalid input leaves both fields unchanged, and a bare
// Decimal still refuses null.
func TestNullDecimalJSON(t *testing.T) {
	type row struct {
		Price NullDecimal `json:"price"`
	}
	for _, tc := range []struct {
		value NullDecimal
		want  string
	}{
		{NullDecimal{}, `{"price":null}`},
		{NullDecimal{Decimal: MustParse("-1.250"), Valid: true}, `{"price":-1.250}`},
	} {
		out, err := json.Marshal(row{tc.value})
		if err != nil || string(out) != tc.want {
			t.Fatalf("Marshal(%+v) = %s, %v; want %s", tc.value, out, err, tc.want)
		}
		back := row{Price: NullDecimal{Decimal: MustParse("7"), Valid: true}}
		if err := json.Unmarshal(out, &back); err != nil || back.Price.Valid != tc.value.Valid || !sameCohort(back.Price.Decimal, tc.value.Decimal) {
			t.Fatalf("Unmarshal(%s) = %+v, %v", out, back, err)
		}
	}
	populated := NullDecimal{Decimal: MustParse("7"), Valid: true}
	if err := populated.UnmarshalJSON([]byte(`"x"`)); !errors.Is(err, ErrConversionSyntax) || !populated.Valid || populated.Decimal.String() != "7" {
		t.Fatalf("invalid input: %+v, %v", populated, err)
	}
	var bare Decimal
	if err := json.Unmarshal([]byte(`null`), &bare); !errors.Is(err, ErrConversionSyntax) {
		t.Fatalf("bare Decimal accepted null: %v", err)
	}
	if err := (*NullDecimal)(nil).UnmarshalJSON([]byte(`1`)); !errors.Is(err, ErrInvalidOperation) {
		t.Fatalf("nil receiver: %v", err)
	}
}
