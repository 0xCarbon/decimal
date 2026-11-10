// SPDX-License-Identifier: Apache-2.0

package decimal

import "math/bits"

// Literal is the text type Parse and its forms accept: any string or byte
// slice type. Both carriers share one implementation, and byte input is
// never copied on success. Generic wrappers can name it to forward either.
type Literal interface{ ~string | ~[]byte }

// digitSpan returns the length of the leading run of ASCII digits in s.
// Byte input can be loaded into vectors without a copy, so it may take the
// portable SIMD kernel (goexperiment.simd builds); strings, whose vector load
// would first copy, always use the SWAR kernel.
func digitSpan[T Literal](s T) int {
	if len(s) >= vectorSpanMin {
		if b, ok := any(s).([]byte); ok {
			return vectorDigitSpanBytes(b)
		}
	}
	return swarDigitSpan(s)
}

// swarDigitSpan classifies eight bytes per step with SWAR arithmetic on one
// 64-bit load: for each byte b with its high bit cleared, (b|0x80)-0x30
// keeps the high bit iff b >= '0' and b+0x46 sets it iff b > '9'; neither
// step carries across byte lanes. Bytes with the high bit set are never
// digits. TrailingZeros64 then locates the first non-digit.
func swarDigitSpan[T Literal](s T) int {
	const high = 0x8080808080808080
	i := 0
	for ; len(s)-i >= 8; i += 8 {
		x := load64(s[i : i+8])
		low := x &^ high
		atLeastZero := (low | high) - 0x3030303030303030
		aboveNine := low + 0x4646464646464646
		if other := (^atLeastZero | aboveNine | x) & high; other != 0 {
			return i + bits.TrailingZeros64(other)>>3
		}
	}
	for ; i < len(s); i++ {
		if s[i]-'0' > 9 {
			return i
		}
	}
	return i
}

// validDigits accepts an empty span. The grammar separately requires at
// least one coefficient digit and digits after an exponent marker/sign.
func validDigits[T Literal](s T) bool { return digitSpan(s) == len(s) }

// zeroSpan returns the length of the leading run of '0' bytes in s, eight
// bytes per step.
func zeroSpan[T Literal](s T) int {
	const zeros = 0x3030303030303030
	i := 0
	for ; len(s)-i >= 8; i += 8 {
		if other := load64(s[i:i+8]) ^ zeros; other != 0 {
			return i + bits.TrailingZeros64(other)>>3
		}
	}
	for ; i < len(s); i++ {
		if s[i] != '0' {
			return i
		}
	}
	return i
}

// load64 reads eight bytes little-endian; the compiler fuses it into one load.
func load64[T Literal](t T) uint64 {
	_ = t[7]
	return uint64(t[0]) | uint64(t[1])<<8 | uint64(t[2])<<16 | uint64(t[3])<<24 |
		uint64(t[4])<<32 | uint64(t[5])<<40 | uint64(t[6])<<48 | uint64(t[7])<<56
}
