// SPDX-License-Identifier: Apache-2.0

//go:build goexperiment.simd

package decimal

import (
	"simd"
	"strings"
	"testing"
)

// TestSIMDEnvironment records the portable vector width and emulation.
func TestSIMDEnvironment(t *testing.T) {
	var x simd.Uint8s
	if x.Len() != 16 && x.Len() != 32 && x.Len() != 64 {
		t.Fatalf("unexpected portable SIMD width: %d byte lanes", x.Len())
	}
	t.Logf("vector_bits=%d uint8_lanes=%d emulated=%v", simd.VectorBitSize(), x.Len(), simd.Emulated())
}

// TestSIMDDigitKernel drives vectorDigitSpan directly (bypassing the
// emulation and length dispatch) with every byte value at every position
// through the chunk loop and the SWAR remainder.
func TestSIMDDigitKernel(t *testing.T) {
	n := simd.BroadcastUint8s(0).Len()
	for _, length := range []int{n, n + 1, 2*n - 1, 8 * n, 8*n + n + 3, 17 * n} {
		data := []byte(strings.Repeat("7", length))
		if got := vectorDigitSpan(data); got != length {
			t.Fatalf("length=%d all digits: span %d", length, got)
		}
		for pos := range data {
			for b := range 256 {
				data[pos] = byte(b)
				want := length
				if byte(b)-'0' > 9 {
					want = pos
				}
				if got := vectorDigitSpan(data); got != want {
					t.Fatalf("length=%d position=%d byte=%d span=%d want=%d", length, pos, b, got, want)
				}
			}
			data[pos] = '7'
		}
	}
}
