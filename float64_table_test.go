// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/big"
	"testing"
)

// TestFloat64PowersTable checks every entry of the binary64 power table
// against math/big: M holds the leading 128 bits of 5^q (2^127 ≤ M <
// 2^128), 5^q lies in [M, M + 1)·2^s with s = float64PowerExponent(q),
// equality exactly where float64PowerExact holds, and M + 1 never wraps.
func TestFloat64PowersTable(t *testing.T) {
	five := big.NewInt(5)
	for q := int64(float64TableMin); q <= float64TableMax; q++ {
		entry := float64Powers[q-float64TableMin]
		m := new(big.Int).Lsh(new(big.Int).SetUint64(entry[0]), 64)
		m.Or(m, new(big.Int).SetUint64(entry[1]))
		if m.BitLen() != 128 || entry[0] == ^uint64(0) && entry[1] == ^uint64(0) {
			t.Fatalf("5^%d: M = %x is not a wrap-free 128-bit value", q, m)
		}
		// Compare 5^q with M·2^s and (M + 1)·2^s as integers: scale both
		// sides by 2^max(−s, 0) and 5^max(−q, 0).
		s := float64PowerExponent(q)
		left := big.NewInt(1) // 5^q·2^−s·5^−q' form
		lowSide := new(big.Int).Set(m)
		highSide := new(big.Int).Add(m, big.NewInt(1))
		if q >= 0 {
			left.Exp(five, big.NewInt(q), nil)
		} else {
			p := new(big.Int).Exp(five, big.NewInt(-q), nil)
			lowSide.Mul(lowSide, p)
			highSide.Mul(highSide, p)
		}
		if s >= 0 {
			lowSide.Lsh(lowSide, uint(s))
			highSide.Lsh(highSide, uint(s))
		} else {
			left.Lsh(left, uint(-s))
		}
		exact := left.Cmp(lowSide) == 0
		if left.Cmp(lowSide) < 0 || left.Cmp(highSide) >= 0 {
			t.Fatalf("5^%d outside [M, M+1)·2^%d", q, s)
		}
		if exact != float64PowerExact(q) {
			t.Fatalf("5^%d: exact = %v", q, exact)
		}
	}
}
