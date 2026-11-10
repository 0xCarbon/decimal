// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"encoding"
	"errors"
	"math/big"
	"strings"
	"testing"
)

var _ encoding.TextUnmarshaler = (*Decimal)(nil)

func inboundTextOracle(coefficient string, exponent int32, negative bool) *big.Rat {
	c, ok := new(big.Int).SetString(coefficient, 10)
	if !ok {
		panic("invalid test coefficient")
	}
	if negative {
		c.Neg(c)
	}
	power := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(abs32(exponent))), nil)
	if exponent >= 0 {
		return new(big.Rat).SetInt(c.Mul(c, power))
	}
	return new(big.Rat).SetFrac(c, power)
}

func abs32(n int32) uint64 {
	if n < 0 {
		return uint64(-int64(n))
	}
	return uint64(n)
}

func TestInteropTextUnmarshalCohortAndOracle(t *testing.T) {
	tests := []struct {
		name, input, digits, canonical string
		exponent                       int32
		negative                       bool
	}{
		{"scale", "1.10", "110", "1.10", -2, false},
		{"unsigned-zero", "-0.00", "0", "0.00", -2, false},
		{"positive-zero-exponent", "0E+2", "0", "0E+2", 2, false},
		{"negative", "-12.300", "12300", "-12.300", -3, true},
		{"leading-zeros", "007.0100", "70100", "7.0100", -4, false},
		{"slow", strings.Repeat("9", 70) + ".00", strings.Repeat("9", 70) + "00", strings.Repeat("9", 70) + ".00", -2, false},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			input := []byte(tc.input)
			var got Decimal
			if err := got.UnmarshalText(input); err != nil {
				t.Fatal(err)
			}
			if got.coefficientDigits() != tc.digits || got.exponent() != tc.exponent || got.negative() != tc.negative {
				t.Fatalf("cohort digits=%q exponent=%d negative=%v", got.coefficientDigits(), got.exponent(), got.negative())
			}
			text, err := got.Text(0)
			if err != nil || text != tc.canonical {
				t.Fatalf("canonical text=%q, %v, want %q", text, err, tc.canonical)
			}
			actual, ok := new(big.Rat).SetString(text)
			if !ok || actual.Cmp(inboundTextOracle(tc.digits, tc.exponent, tc.negative)) != 0 {
				t.Fatalf("numeric value=%q diverges from independent coefficient/exponent oracle", text)
			}
			if len(input) != 0 {
				input[0] = '!'
			}
			after, err := got.Text(0)
			if err != nil || after != tc.canonical {
				t.Fatalf("caller byte mutation changed Decimal: %q, %v", after, err)
			}
		})
	}
}

func TestInteropTextUnmarshalErrorIdentityAndAtomicity(t *testing.T) {
	prior := MustParse("-" + strings.Repeat("1234567890", 5) + ".00")
	if prior.slow == nil {
		t.Fatal("test prerequisite: prior value must use slow holder")
	}
	tests := []struct {
		input     []byte
		cause     ErrorCode
		condition Conditions
	}{
		{[]byte(".nan"), ErrConversionSyntax, ConversionSyntax},
		{[]byte("1_0"), ErrConversionSyntax, ConversionSyntax},
		{[]byte("1e2147483648"), ErrExponentRange, 0},
		{[]byte{0xff, '1'}, ErrConversionSyntax, ConversionSyntax},
	}
	for _, tc := range tests {
		got := prior
		input := string(tc.input)
		err := got.UnmarshalText(tc.input)
		var pe *Error
		if !errors.Is(err, tc.cause) || !errors.As(err, &pe) || pe.Op != "UnmarshalText" || pe.Input != input || pe.Code != tc.cause || pe.Condition != tc.condition {
			t.Fatalf("input %q error=%#v, want exact method-owned %v", input, err, tc.cause)
		}
		if got.words != prior.words || got.exponent() != prior.exponent() || got.negative() != prior.negative() || got.slow != prior.slow {
			t.Fatalf("input %q changed failed receiver or slow holder", input)
		}
		if len(tc.input) != 0 {
			tc.input[0] = '!'
		}
		if pe.Input != input {
			t.Fatalf("error input retained caller byte slice: %q", pe.Input)
		}
	}
}

func TestInteropTextUnmarshalNilReceiverPriority(t *testing.T) {
	var target *Decimal
	for _, input := range [][]byte{[]byte("1.10"), []byte("bad"), nil} {
		err := target.UnmarshalText(input)
		var op *Error
		if !errors.Is(err, ErrInvalidOperation) || !errors.As(err, &op) || op.Op != "UnmarshalText" || op.Code != ErrInvalidOperation || op.Condition != InvalidOperation {
			t.Fatalf("nil destination with %q = %#v", input, err)
		}
	}
}

// TestInteropTextRawTextAndOwnership pins UnmarshalText's ownership rules:
// a decode replaces the receiver's value and cohort without touching the
// previous slow holder, never aliases the caller's bytes, and a rejected
// input leaves the receiver unchanged.
func TestInteropTextRawTextAndOwnership(t *testing.T) {
	raw := []byte("1.10")
	prior := MustParse(strings.Repeat("9", 50) + ".00")
	if prior.slow == nil {
		t.Fatal("test prerequisite: preexisting receiver must own a slow holder")
	}
	got := prior
	if err := got.UnmarshalText(raw); err != nil {
		t.Fatal(err)
	}
	if got.coefficientDigits() != "110" || got.exponent() != -2 || got.negative() || got.slow != nil {
		t.Fatalf("raw 1.10 cohort or replacement wrong: digits=%q exponent=%d negative=%v slow=%v", got.coefficientDigits(), got.exponent(), got.negative(), got.slow != nil)
	}
	raw[0] = '!'
	if text, err := got.Text(0); err != nil || text != "1.10" {
		t.Fatalf("caller byte mutation changed accepted value: %q, %v", text, err)
	}
	if text, err := prior.Text(0); err != nil || text != strings.Repeat("9", 50)+".00" {
		t.Fatalf("successful decode changed the old slow holder: %q, %v", text, err)
	}

	before := got
	bad := []byte(".nan")
	err := got.UnmarshalText(bad)
	var parse *Error
	if !errors.Is(err, ErrConversionSyntax) || !errors.As(err, &parse) || parse.Op != "UnmarshalText" || parse.Input != ".nan" || parse.Condition != ConversionSyntax {
		t.Fatalf(".nan error=%#v, want method-owned ConversionSyntax", err)
	}
	bad[0] = '!'
	if parse.Input != ".nan" || got.words != before.words || got.exponent() != before.exponent() || got.negative() != before.negative() || got.slow != before.slow {
		t.Fatal("failed decode changed receiver or retained caller bytes")
	}
}
