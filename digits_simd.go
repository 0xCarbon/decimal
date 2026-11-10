// SPDX-License-Identifier: Apache-2.0

//go:build goexperiment.simd

package decimal

import "simd"

// vectorSpanMin is one eight-vector chunk at the minimum 16-byte portable
// width. Shorter spans skip the dispatch entirely: SWAR is faster there.
const vectorSpanMin = 8 * 16

// vectorDigitSpanBytes scans byte input with the Go 1.27 portable SIMD
// kernel once it holds a full eight-vector chunk at the actual width;
// emulated targets use the SWAR kernel.
func vectorDigitSpanBytes(b []byte) int {
	if simd.Emulated() || len(b) < 8*simd.BroadcastUint8s(0).Len() {
		return swarDigitSpan(b)
	}
	return vectorDigitSpan(b)
}

// vectorDigitSpan subtracts '0' from every byte, so digits become 0..9 and
// every other byte wraps above 9. The running unsigned maximum of eight
// vectors is checked once per chunk (the portable API has no mask-to-bits
// or horizontal reduction, so the check stores one vector). A chunk that
// holds a non-digit stops the vector loop, and the SWAR kernel locates the
// exact byte within it and scans the final partial chunk.
func vectorDigitSpan(b []byte) int {
	zero := simd.BroadcastUint8s('0')
	nine := simd.BroadcastUint8s(9)
	n := zero.Len()
	i := 0
	for len(b)-i >= 8*n {
		acc := simd.LoadUint8s(b[i:]).Sub(zero)
		acc = acc.Max(simd.LoadUint8s(b[i+n:]).Sub(zero))
		acc = acc.Max(simd.LoadUint8s(b[i+2*n:]).Sub(zero))
		acc = acc.Max(simd.LoadUint8s(b[i+3*n:]).Sub(zero))
		acc = acc.Max(simd.LoadUint8s(b[i+4*n:]).Sub(zero))
		acc = acc.Max(simd.LoadUint8s(b[i+5*n:]).Sub(zero))
		acc = acc.Max(simd.LoadUint8s(b[i+6*n:]).Sub(zero))
		acc = acc.Max(simd.LoadUint8s(b[i+7*n:]).Sub(zero))
		if !allDigits(acc, nine) {
			return i + swarDigitSpan(b[i:])
		}
		i += 8 * n
	}
	return i + swarDigitSpan(b[i:])
}

// allDigits reports whether every lane of x (bytes minus '0') is at most 9.
func allDigits(x, nine simd.Uint8s) bool {
	var lanes [64]byte // 512 bits, the widest portable vector
	count := x.SubSaturated(nine).StorePart(lanes[:])
	var over uint64
	for j := 0; j < count; j += 8 {
		over |= load64(lanes[j : j+8])
	}
	return over == 0
}
