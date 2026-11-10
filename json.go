// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"bytes"
	"math/bits"
	"unicode/utf16"
	"unicode/utf8"
)

// MarshalJSON emits checked canonical text as a bare JSON number.
func (d Decimal) MarshalJSON() ([]byte, error) {
	return d.marshalCanonical()
}

// UnmarshalJSON accepts one JSON number or string and assigns only on
// success. JSON null is refused as ErrConversionSyntax, because Decimal has
// no null state: decode nullable fields into NullDecimal.
func (d *Decimal) UnmarshalJSON(raw []byte) error {
	if d == nil {
		return newError("UnmarshalJSON", ErrInvalidOperation)
	}
	value, err := parseJSONWithBudget(raw, textLimits{}, "UnmarshalJSON")
	if err != nil {
		return err
	}
	*d = value
	return nil
}

// MarshalJSON emits null for an invalid value and the Decimal's bare JSON
// number otherwise.
func (n NullDecimal) MarshalJSON() ([]byte, error) {
	if !n.Valid {
		return []byte("null"), nil
	}
	return n.Decimal.MarshalJSON()
}

// UnmarshalJSON sets Valid false and clears Decimal for JSON null, and
// otherwise decodes as Decimal.UnmarshalJSON does with Valid true. On error
// both fields are unchanged.
func (n *NullDecimal) UnmarshalJSON(raw []byte) error {
	if n == nil {
		return newError("UnmarshalJSON", ErrInvalidOperation)
	}
	if string(raw) == "null" {
		*n = NullDecimal{}
		return nil
	}
	value, err := parseJSONWithBudget(raw, textLimits{}, "UnmarshalJSON")
	if err != nil {
		return err
	}
	*n = NullDecimal{Decimal: value, Valid: true}
	return nil
}

// ParseJSONWithBudget charges raw input bytes before framing and significant
// decoded coefficient digits after decimal syntax and range checks.
func ParseJSONWithBudget(raw []byte, budget Budget) (Decimal, error) {
	return parseJSONWithBudget(raw, budget.text(), "ParseJSONWithBudget")
}

// parseJSONWithBudget returns a short token within both budgets from
// decodeJSONInline's single pass; everything else, including
// every refusal, is parseJSONGeneral's.
func parseJSONWithBudget(raw []byte, budget textLimits, op string) (Decimal, error) {
	if budget.MaxInputBytes == 0 || uint64(len(raw)) <= budget.MaxInputBytes {
		if d, ok := decodeJSONInline(trimJSONSpace(raw), budget.MaxDigits); ok {
			return d, nil
		}
	}
	return parseJSONGeneral(raw, budget, op)
}

// parseJSONGeneral owns JSON decoding: the input-byte budget, framing,
// RFC 8259 number and string validation, escape decoding and the decimal
// parse of the decoded text.
func parseJSONGeneral(raw []byte, budget textLimits, op string) (Decimal, error) {
	if budget.MaxInputBytes != 0 && uint64(len(raw)) > budget.MaxInputBytes {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	token := trimJSONSpace(raw)
	if len(token) == 0 {
		return jsonSyntaxError(op, token)
	}
	digits := textLimits{MaxDigits: budget.MaxDigits}
	switch {
	case token[0] == '"':
		// walkJSONQuoted is a complete validator for one JSON string.
		n, ok := walkJSONQuoted(token, nil)
		if !ok {
			return jsonSyntaxError(op, token)
		}
		if n == len(token)-2 {
			// Every escape shortens the decoded text, so an equal length
			// means no escapes: parse the quoted body in place.
			return parseWithBudget(token[1:len(token)-1], digits, op)
		}
		if _, ok := jsonDecodeEnvelope(uint64(len(raw)), uint64(n), uint64(len(raw))); !ok {
			return Decimal{}, newError(op, ErrInsufficientStorage)
		}
		buf := make([]byte, n)
		filled, ok := walkJSONQuoted(token, buf)
		if !ok || filled != n {
			return jsonSyntaxError(op, token)
		}
		return parseWithBudget(buf, digits, op)
	case jsonNumber(token):
		return parseWithBudget(token, digits, op)
	default:
		return jsonSyntaxError(op, token)
	}
}

// decodeJSONInline is the fused one-pass decode of a short token:
// a bare token in the strict RFC 8259 number subset, or a quoted token
// whose body parseInline accepts. That body's alphabet [0-9.eE+-] has no
// escape, quote, control or non-ASCII byte, so walkJSONQuoted would accept
// it unchanged, and a bare token that parseInline accepts in jsonShape is a
// jsonNumber; either way the general path would reach parseWithBudget's
// parseInline on the same bytes. ok is false whenever that path might
// decide anything else, including the coefficient-digit refusal.
func decodeJSONInline(token []byte, maxDigits uint64) (Decimal, bool) {
	if len(token) == 0 {
		return Decimal{}, false
	}
	body := token
	if token[0] == '"' {
		if len(token) < 2 || token[len(token)-1] != '"' {
			return Decimal{}, false
		}
		body = token[1 : len(token)-1]
	} else if !jsonShape(token) {
		return Decimal{}, false
	}
	c, exponent, negative, significant, ok := parseInline(body)
	if !ok || maxDigits != 0 && uint64(significant) > maxDigits {
		return Decimal{}, false
	}
	return inlineDecimal(uint128{lo: c}, exponent, negative), true
}

// jsonShape checks what RFC 8259 adds to parseInline's grammar: no '+'
// sign, an integral digit with no leading zero, and a digit after the
// point. A literal in both is a JSON number, since parseInline's exponent
// already requires a digit and its grammar admits one point.
func jsonShape(b []byte) bool {
	i := 0
	if b[0] == '-' {
		i = 1
	}
	if i == len(b) || b[i]-'0' > 9 || b[i] == '0' && i+1 < len(b) && b[i+1]-'0' <= 9 {
		return false
	}
	p := bytes.IndexByte(b, '.')
	return p < 0 || p+1 < len(b) && b[p+1]-'0' <= 9
}

// jsonNumber reports whether b is exactly one RFC 8259 number token:
// -?(0|[1-9][0-9]*)(.[0-9]+)?([eE][+-]?[0-9]+)?
func jsonNumber(b []byte) bool {
	i := 0
	if i < len(b) && b[i] == '-' {
		i++
	}
	switch {
	case i == len(b):
		return false
	case b[i] == '0':
		i++
	case '1' <= b[i] && b[i] <= '9':
		i += digitSpan(b[i:])
	default:
		return false
	}
	if i < len(b) && b[i] == '.' {
		i++
		n := digitSpan(b[i:])
		if n == 0 {
			return false
		}
		i += n
	}
	if i < len(b) && (b[i] == 'e' || b[i] == 'E') {
		i++
		if i < len(b) && (b[i] == '+' || b[i] == '-') {
			i++
		}
		n := digitSpan(b[i:])
		if n == 0 {
			return false
		}
		i += n
	}
	return i == len(b)
}

func jsonSyntaxError(op string, token []byte) (Decimal, error) {
	return Decimal{}, &Error{Op: op, Input: string(token), Code: ErrConversionSyntax, Condition: ConversionSyntax}
}

func trimJSONSpace(raw []byte) []byte {
	for len(raw) > 0 && jsonSpace(raw[0]) {
		raw = raw[1:]
	}
	for len(raw) > 0 && jsonSpace(raw[len(raw)-1]) {
		raw = raw[:len(raw)-1]
	}
	return raw
}

func jsonSpace(b byte) bool { return b == ' ' || b == '\t' || b == '\n' || b == '\r' }

// jsonDecodeEnvelope checks the two decoded D-byte objects against resident
// raw R. Its result accounts for payload bytes, not opaque stdlib allocations.
func jsonDecodeEnvelope(rawBytes, decodedBytes, maxObject uint64) (uint64, bool) {
	if rawBytes < 2 || rawBytes > maxObject || decodedBytes > rawBytes-2 || decodedBytes > maxObject {
		return 0, false
	}
	hi, twice := bits.Mul64(decodedBytes, 2)
	if hi != 0 {
		return 0, false
	}
	total, carry := bits.Add64(rawBytes, twice, 0)
	return total, carry == 0
}

func jsonHex4(raw []byte) (rune, bool) {
	if len(raw) < 4 {
		return 0, false
	}
	var value rune
	for _, b := range raw[:4] {
		value <<= 4
		switch {
		case '0' <= b && b <= '9':
			value += rune(b - '0')
		case 'a' <= b && b <= 'f':
			value += rune(b-'a') + 10
		case 'A' <= b && b <= 'F':
			value += rune(b-'A') + 10
		default:
			return 0, false
		}
	}
	return value, true
}

// walkJSONQuoted counts with dst=nil, then fills the same exact length. The
// caller has validated JSON framing; invalid raw UTF-8 is rejected here.
func walkJSONQuoted(token, dst []byte) (int, bool) {
	if len(token) < 2 || token[0] != '"' || token[len(token)-1] != '"' {
		return 0, false
	}
	n := 0
	emit := func(src []byte) bool {
		if len(src) > len(token)-2-n || dst != nil && n+len(src) > len(dst) {
			return false
		}
		if dst != nil {
			copy(dst[n:], src)
		}
		n += len(src)
		return true
	}
	emitByte := func(b byte) bool {
		if n >= len(token)-2 || dst != nil && n >= len(dst) {
			return false
		}
		if dst != nil {
			dst[n] = b
		}
		n++
		return true
	}
	emitRune := func(r rune) bool {
		var buf [utf8.UTFMax]byte
		size := utf8.EncodeRune(buf[:], r)
		return emit(buf[:size])
	}
	for i := 1; i < len(token)-1; {
		c := token[i]
		switch {
		case c == '\\':
			if i+1 >= len(token)-1 {
				return 0, false
			}
			var value byte
			switch token[i+1] {
			case '"', '\\', '/':
				value = token[i+1]
			case 'b':
				value = '\b'
			case 'f':
				value = '\f'
			case 'n':
				value = '\n'
			case 'r':
				value = '\r'
			case 't':
				value = '\t'
			case 'u':
				if len(token)-1-i < 6 {
					return 0, false
				}
				r, ok := jsonHex4(token[i+2 : i+6])
				if !ok {
					return 0, false
				}
				i += 6
				if 0xD800 <= r && r <= 0xDBFF && len(token)-1-i >= 6 && token[i] == '\\' && token[i+1] == 'u' {
					if low, ok := jsonHex4(token[i+2 : i+6]); ok && 0xDC00 <= low && low <= 0xDFFF {
						r = utf16.DecodeRune(r, low)
						i += 6
					}
				}
				if 0xD800 <= r && r <= 0xDFFF {
					r = utf8.RuneError
				}
				if !emitRune(r) {
					return 0, false
				}
				continue
			default:
				return 0, false
			}
			if !emitByte(value) {
				return 0, false
			}
			i += 2
		case c < utf8.RuneSelf:
			if c < ' ' || c == '"' || !emit(token[i:i+1]) {
				return 0, false
			}
			i++
		default:
			r, size := utf8.DecodeRune(token[i : len(token)-1])
			if r == utf8.RuneError && size == 1 || !emit(token[i:i+size]) {
				return 0, false
			}
			i += size
		}
	}
	return n, true
}
