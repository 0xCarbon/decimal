// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/big"
	"math/rand"
	"slices"
	"testing"
)

// TestContextMulStreamCarrySplitMatchesBigOracle pins the product stream's
// carry split (a constant division when the column fits one word, one
// hardware division otherwise) to math/big base-10^9 product limbs over
// random coefficients and all-999999999 limbs whose columns exceed 2^64. The
// guard requires both the one-word and the two-word column branch to serve a
// substantial share of the groups.
func TestContextMulStreamCarrySplitMatchesBigOracle(t *testing.T) {
	rng := rand.New(rand.NewSource(20261032))
	base := big.NewInt(1_000_000_000)
	two64 := new(big.Int).Lsh(big.NewInt(1), 64)
	toBig := func(limbs []uint32) *big.Int {
		x := new(big.Int)
		for _, limb := range slices.Backward(limbs) {
			x.Mul(x, base)
			x.Add(x, big.NewInt(int64(limb)))
		}
		return x
	}
	var oneWord, twoWord int
	for i := range 3000 {
		na, nb := 1+rng.Intn(60), 1+rng.Intn(60)
		a, b := make([]uint32, na), make([]uint32, nb)
		for j := range a {
			a[j] = uint32(rng.Intn(1_000_000_000))
			if i%3 == 0 {
				a[j] = 999_999_999
			}
		}
		for j := range b {
			b[j] = uint32(rng.Intn(1_000_000_000))
			if i%3 == 0 {
				b[j] = 999_999_999
			}
		}
		a[na-1] = max(a[na-1], 1)
		b[nb-1] = max(b[nb-1], 1)
		p := contextPlan{mul: true}
		p.a.slow, p.a.count = a, na
		p.b.slow, p.b.count = b, nb
		product := new(big.Int).Mul(toBig(a), toBig(b))
		stream := contextGroupStream{plan: &p}
		carry := new(big.Int)
		for index := range na + nb {
			column := new(big.Int).Set(carry)
			for k := range na {
				if m := index - k; m >= 0 && m < nb {
					column.Add(column, new(big.Int).Mul(big.NewInt(int64(a[k])), big.NewInt(int64(b[m]))))
				}
			}
			if column.Cmp(two64) >= 0 {
				twoWord++
			} else {
				oneWord++
			}
			want := new(big.Int)
			carry.QuoRem(column, base, want)
			got, ok := stream.next()
			if !ok {
				t.Fatalf("stream refused %dx%d limbs at group %d", na, nb, index)
			}
			digit := new(big.Int)
			product.QuoRem(product, base, digit)
			if uint64(got) != want.Uint64() || uint64(got) != digit.Uint64() {
				t.Fatalf("group %d of %dx%d product = %d, oracle %d", index, na, nb, got, digit)
			}
		}
		if product.Sign() != 0 || stream.carryHi != 0 || stream.carryLo != 0 {
			t.Fatalf("%dx%d product stream left carry %d:%d", na, nb, stream.carryHi, stream.carryLo)
		}
	}
	if oneWord < 20_000 || twoWord < 10_000 {
		t.Fatalf("vacuous column coverage: one-word %d, two-word %d", oneWord, twoWord)
	}
}
