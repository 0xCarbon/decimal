// SPDX-License-Identifier: Apache-2.0

package decimal

import "math"

// decimalParts is a lexical view into the input, before coefficient storage.
// Neither exponent magnitude nor leading/trailing zeros cause an allocation.
// The constructor owns zero-sign normalization and coefficient storage.
type decimalParts[T Literal] struct {
	integral T
	fraction T
	exponent int64 // effective exponent, saturated to ±2^62
	negative bool
}

// scanSaturation bounds the effective exponent. Inputs are shorter than
// 2^58 bytes on every supported address space (callers refuse longer), so
// a saturated exponent stays beyond every int32 exponent, guard and Etiny.
const scanSaturation = int64(1) << 62

type scanResult uint8

const (
	scanOK scanResult = iota
	scanSyntax
	scanRange
)

// scanDecimal splits a decimal literal into its parts. The stored exponent is the lexical exponent
// minus the number of fractional digits, not the lexical exponent alone.
// In particular 1.2E+2147483648 is in-domain and must round-trip.
func scanDecimal[T Literal](s T) (decimalParts[T], scanResult) {
	if len(s) == 0 {
		return decimalParts[T]{}, scanSyntax
	}
	negative := false
	if s[0] == '+' || s[0] == '-' {
		negative = s[0] == '-'
		s = s[1:]
	}
	// One left-to-right pass: integral digits, an optional point and
	// fraction digits, then an optional exponent. Any other byte is syntax.
	n := digitSpan(s)
	integral, fraction := s[:n], s[n:n]
	s = s[n:]
	if len(s) != 0 && s[0] == '.' {
		s = s[1:]
		n = digitSpan(s)
		fraction, s = s[:n], s[n:]
	}
	if len(integral)+len(fraction) == 0 {
		return decimalParts[T]{}, scanSyntax
	}
	// len(fraction) < 2^58, so the exponent stays within int64.
	exponent := -int64(len(fraction))
	if len(s) != 0 {
		var ok bool
		if exponent, ok = scanExponent(s, exponent); !ok {
			return decimalParts[T]{}, scanSyntax
		}
	}
	p := decimalParts[T]{integral: integral, fraction: fraction, exponent: exponent, negative: negative}
	if exponent < math.MinInt32 || exponent > math.MaxInt32 {
		// Parse refuses; the rounding forms resolve by magnitude with p.
		return p, scanRange
	}
	return p, scanOK
}

// scanExponent validates the exponent suffix s (from its 'e' or 'E') and
// returns base plus its value, saturated to ±scanSaturation.
func scanExponent[T Literal](s T, base int64) (int64, bool) {
	if s[0] != 'e' && s[0] != 'E' || len(s) == 1 {
		return 0, false
	}
	exp := s[1:]
	negativeExp := false
	if exp[0] == '+' || exp[0] == '-' {
		negativeExp = exp[0] == '-'
		exp = exp[1:]
		if len(exp) == 0 {
			return 0, false
		}
	}
	if !validDigits(exp) {
		return 0, false
	}
	exp = exp[zeroSpan(exp):] // leading exponent zeros change nothing
	// Accumulate after validating every digit, saturating before overflow,
	// so arbitrarily deep exponents neither wrap nor hide syntax.
	var magnitude int64
	for i := range len(exp) {
		if magnitude > scanSaturation/10 {
			magnitude = scanSaturation
			break
		}
		magnitude = magnitude*10 + int64(exp[i]-'0')
	}
	magnitude = min(magnitude, scanSaturation)
	if negativeExp {
		magnitude = -magnitude
	}
	return min(max(magnitude+base, -scanSaturation), scanSaturation), true
}
