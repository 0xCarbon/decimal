// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"fmt"
	"math"
	"math/big"
	"math/bits"
	randv2 "math/rand/v2"
	"runtime"
	"slices"
	"strings"
	"testing"
)

// bigFromLimbs is the math/big value of base-10^9 limbs.
func bigFromLimbs(limbs []uint32) *big.Int {
	var sb strings.Builder
	sb.WriteString("0")
	for _, limb := range slices.Backward(limbs) {
		fmt.Fprintf(&sb, "%09d", limb)
	}
	v, _ := new(big.Int).SetString(sb.String(), 10)
	return v
}

// limbsFromBig returns exactly n base-10^9 limbs of v, or false when v
// needs more.
func limbsFromBig(v *big.Int, n int) ([]uint32, bool) {
	s := v.String()
	out := make([]uint32, n)
	for i := 0; len(s) > 0; i++ {
		cut := max(0, len(s)-9)
		var limb uint32
		for _, ch := range s[cut:] {
			limb = limb*10 + uint32(ch-'0')
		}
		if i >= n {
			if limb != 0 {
				return nil, false
			}
		} else {
			out[i] = limb
		}
		s = s[:cut]
	}
	return out, true
}

// limbView builds the view a multiply caller passes: inline for at most
// five limbs when inline is set, slow otherwise.
func limbView(limbs []uint32, inline bool) coefficientView {
	if inline && len(limbs) <= 5 {
		v := coefficientView{count: len(limbs)}
		copy(v.inline[:], limbs)
		return v
	}
	return coefficientView{slow: limbs, count: len(limbs)}
}

// TestPairDivStepAgainstBigInt pins the reciprocal division step to
// math/big (the carry argument): the reciprocal constant, and for
// x1 < pairNorm the quotient and remainder of x1:x0 / pairNorm, with the
// first estimate short by at most one (the bound in pairDivStep's doc)
// and a guard that both zero and one were observed.
func TestPairDivStepAgainstBigInt(t *testing.T) {
	if want, _ := bits.Div64(^uint64(pairNorm), math.MaxUint64, pairNorm); want != pairReciprocal {
		t.Fatalf("pairReciprocal = %#x, want %#x", uint64(pairReciprocal), want)
	}
	if pairNorm != pairBase<<pairShift || bits.LeadingZeros64(pairNorm) != 0 || bits.LeadingZeros64(pairBase) != pairShift {
		t.Fatalf("pairNorm is not 10^18 normalized")
	}
	d := new(big.Int).SetUint64(pairNorm)
	m := new(big.Int).SetUint64(pairReciprocal)
	two64 := new(big.Int).Lsh(big.NewInt(1), 64)
	var short [2]int
	check := func(x1, x0 uint64) {
		x := new(big.Int).Lsh(new(big.Int).SetUint64(x1), 64)
		x.Or(x, new(big.Int).SetUint64(x0))
		wantQ, wantR := new(big.Int).QuoRem(x, d, new(big.Int))
		q, r := pairDivStep(x1, x0)
		if wantQ.Uint64() != q || wantR.Uint64() != r || !wantQ.IsUint64() {
			t.Fatalf("pairDivStep(%#x, %#x) = %d, %d; want %s, %s", x1, x0, q, r, wantQ, wantR)
		}
		// Estimate ⌊(m·x1 + x0)/2^64⌋ + x1, formed independently.
		est := new(big.Int).Mul(m, new(big.Int).SetUint64(x1))
		est.Add(est, new(big.Int).SetUint64(x0))
		est.Quo(est, two64)
		est.Add(est, new(big.Int).SetUint64(x1))
		gap := new(big.Int).Sub(wantQ, est).Int64()
		if gap < 0 || gap > 1 {
			t.Fatalf("estimate gap %d at (%#x, %#x) outside the proven [0, 1]", gap, x1, x0)
		}
		short[gap]++
	}
	edges := []uint64{0, 1, pairShift, pairBase - 1, pairBase, pairNorm - 1, pairNorm, 1 << 63, math.MaxUint64 - 1, math.MaxUint64}
	for _, x1 := range []uint64{0, 1, 15, pairBase - 1, pairNorm/2 - 1, pairNorm - 2, pairNorm - 1} {
		for _, x0 := range edges {
			check(x1, x0)
		}
	}
	r := randv2.New(randv2.NewPCG(60, 1))
	for range 50_000 {
		x1 := r.Uint64N(pairNorm)
		if r.IntN(4) == 0 {
			x1 = pairNorm - 1 - r.Uint64N(1<<20)
		}
		check(x1, r.Uint64())
	}
	if short[0] == 0 || short[1] == 0 {
		t.Fatalf("vacuous: estimate gaps observed %v, want gaps 0 and 1", short)
	}
}

// TestPairDivideAgainstBigInt pins the three-word column reduction to
// math/big over each of its paths: a nonzero top word, a dividend below
// 10^18·2^64 (one step) and the two-step middle.
func TestPairDivideAgainstBigInt(t *testing.T) {
	base := new(big.Int).SetUint64(pairBase)
	var paths [3]int
	check := func(t2, t1, t0 uint64) {
		x := new(big.Int).SetUint64(t2)
		x.Lsh(x, 64).Or(x, new(big.Int).SetUint64(t1))
		x.Lsh(x, 64).Or(x, new(big.Int).SetUint64(t0))
		wantQ, wantR := new(big.Int).QuoRem(x, base, new(big.Int))
		q2, q1, q0, r := pairDivide(t2, t1, t0)
		got := new(big.Int).SetUint64(q2)
		got.Lsh(got, 64).Or(got, new(big.Int).SetUint64(q1))
		got.Lsh(got, 64).Or(got, new(big.Int).SetUint64(q0))
		if got.Cmp(wantQ) != 0 || wantR.Uint64() != r {
			t.Fatalf("pairDivide(%#x, %#x, %#x) = %s, %d; want %s, %s", t2, t1, t0, got, r, wantQ, wantR)
		}
		switch oneStep := new(big.Int).Lsh(base, 64); {
		case t2 != 0:
			paths[0]++
		case x.Cmp(oneStep) < 0:
			paths[1]++
		default:
			paths[2]++
		}
	}
	for _, t2 := range []uint64{0, 1, 15, 16, math.MaxUint64 >> 4, math.MaxUint64} {
		for _, t1 := range []uint64{0, 1, 1<<60 - 1, 1 << 60, pairBase, math.MaxUint64} {
			for _, t0 := range []uint64{0, 1, pairBase - 1, pairBase, math.MaxUint64} {
				check(t2, t1, t0)
			}
		}
	}
	// The one-step boundary 10^18·2^64 and its neighbours.
	check(0, pairBase-1, math.MaxUint64)
	check(0, pairBase, 0)
	r := randv2.New(randv2.NewPCG(60, 2))
	for range 30_000 {
		t2, t1 := uint64(0), r.Uint64()>>r.UintN(64)
		if r.IntN(3) == 0 {
			t2 = r.Uint64() >> r.UintN(64)
		}
		check(t2, t1, r.Uint64())
	}
	for i, n := range paths {
		if n < 100 {
			t.Fatalf("vacuous: pairDivide path %d ran %d times (%v)", i, n, paths)
		}
	}
}

// TestPairedMultiplyMatchesScalarKernel is the kernel differential test:
// the paired kernel writes exactly the scalar kernel's base-10^9 limbs and
// both equal math/big, over every shape up to 13×13 limbs (odd and even,
// one-limb operands, inline and slow views), all-nines, sparse and random
// limbs, and long operands up to 3001 limbs whose columns pass 2^128.
// A short out returns false from both kernels and from the dispatcher
// exactly when the product does not fit.
func TestPairedMultiplyMatchesScalarKernel(t *testing.T) {
	r := randv2.New(randv2.NewPCG(60, 3))
	nines := func(n int) []uint32 {
		s := make([]uint32, n)
		for i := range s {
			s[i] = uint32(decimalLimbBase - 1)
		}
		return s
	}
	random := func(n int) []uint32 {
		s := make([]uint32, n)
		for i := range s {
			s[i] = uint32(r.Uint64N(decimalLimbBase))
		}
		if s[n-1] == 0 {
			s[n-1] = 1
		}
		return s
	}
	sparse := func(n int) []uint32 {
		s := make([]uint32, n)
		s[n-1] = uint32(1 + r.Uint64N(decimalLimbBase-1))
		if r.IntN(2) == 0 {
			s[0] = uint32(decimalLimbBase - 1)
		}
		return s
	}
	patterns := []func(int) []uint32{nines, random, sparse}
	compared, wide := 0, 0
	run := func(as, bs []uint32, inline, useBig bool) {
		t.Helper()
		a, b := limbView(as, inline), limbView(bs, inline)
		n := len(as) + len(bs)
		paired, scalar := make([]uint32, n), make([]uint32, n)
		okP, okS := fillMultiplyPaired(paired, &a, &b), fillMultiplyScalar(scalar, &a, &b)
		if !okP || !okS || !slices.Equal(paired, scalar) {
			t.Fatalf("%d×%d limbs: paired %v %v, scalar %v %v", len(as), len(bs), okP, paired[max(0, n-4):], okS, scalar[max(0, n-4):])
		}
		if useBig {
			want, _ := limbsFromBig(new(big.Int).Mul(bigFromLimbs(as), bigFromLimbs(bs)), n)
			if !slices.Equal(paired, want) {
				t.Fatalf("%d×%d limbs: paired differs from math/big", len(as), len(bs))
			}
		}
		// One limb short: both kernels agree on whether the product fits.
		shortP, shortS := make([]uint32, n-1), make([]uint32, n-1)
		okP, okS = fillMultiplyPaired(shortP, &a, &b), fillMultiplyScalar(shortS, &a, &b)
		fits := paired[n-1] == 0
		shortD := make([]uint32, n-1)
		okD := fillMultiply(shortD, &a, &b)
		if okP != fits || okS != fits || okD != fits || (fits && (!slices.Equal(shortP, paired[:n-1]) || !slices.Equal(shortD, paired[:n-1]))) {
			t.Fatalf("%d×%d limbs, short out: paired %v scalar %v dispatch %v, product fits %v", len(as), len(bs), okP, okS, okD, fits)
		}
		compared++
		if min(len(as), len(bs)) >= 680 && as[0] == uint32(decimalLimbBase-1) && bs[0] == uint32(decimalLimbBase-1) {
			wide++ // ≥ 340 pair products near 10^36: the column passes 2^128
		}
	}
	for na := 1; na <= 13; na++ {
		for nb := 1; nb <= 13; nb++ {
			for _, pa := range patterns {
				for _, pb := range patterns {
					run(pa(na), pb(nb), true, true)
					run(pa(na), pb(nb), false, false)
				}
			}
		}
	}
	for range 200 {
		na, nb := 1+r.IntN(80), 1+r.IntN(80)
		run(random(na), random(nb), false, true)
	}
	run(nines(2000), nines(2000), false, true)
	run(nines(1001), nines(699), false, false)
	run(random(3001), random(1999), false, true)
	run(random(2999), nines(7), false, false)
	run(nines(1), random(3000), false, false)
	if compared < 3000 || wide < 2 {
		t.Fatalf("vacuous: %d comparisons, %d with columns past 2^128", compared, wide)
	}
}

// TestFillMultiplySelection pins the compile-time kernel choice:
// paired on amd64 only, and the public Mul equal to math/big on both sides
// of each dispatch threshold.
func TestFillMultiplySelection(t *testing.T) {
	if pairedMultiplyKernel != (runtime.GOARCH == "amd64") {
		t.Fatalf("pairedMultiplyKernel = %v on %s", pairedMultiplyKernel, runtime.GOARCH)
	}
	r := randv2.New(randv2.NewPCG(60, 4))
	checked := 0
	for _, na := range []int{pairedMultiplyMinLimbs - 1, pairedMultiplyMinLimbs, pairedMultiplyMaxLimbs - 1, pairedMultiplyMaxLimbs, pairedMultiplyOuterLimbs - 1, pairedMultiplyOuterLimbs, 40} {
		for _, nb := range []int{1, pairedMultiplyMinLimbs - 1, pairedMultiplyMinLimbs, pairedMultiplyMaxLimbs - 1, pairedMultiplyMaxLimbs, 41} {
			for range 20 {
				digits := func(n int) string {
					var sb strings.Builder
					sb.WriteByte(byte('1' + r.IntN(9)))
					for range 9*n - 1 {
						sb.WriteByte(byte('0' + r.IntN(10)))
					}
					return sb.String()
				}
				x, y := digits(na), digits(nb)
				got, err := MustParse(x + "E-3").Mul(MustParse("-" + y + "E+1"))
				if err != nil {
					t.Fatal(err)
				}
				bx, _ := new(big.Int).SetString(x, 10)
				by, _ := new(big.Int).SetString(y, 10)
				want := "-" + new(big.Int).Mul(bx, by).String() + "E-2"
				if got.String() != MustParse(want).String() {
					t.Fatalf("%d×%d limbs: Mul = %s, want %s", na, nb, got, want)
				}
				checked++
			}
		}
	}
	if checked != 840 {
		t.Fatalf("vacuous: %d products checked", checked)
	}
	// The measured crossovers (BenchmarkMultiplyKernels), pinned literally.
	for _, c := range []struct {
		outer, inner int
		paired       bool
	}{{8, 1, true}, {7, 1, false}, {7, 3, false}, {4, 6, true}, {6, 4, true}, {5, 5, false}, {4, 5, false}, {3, 40, false}, {1, 1000, false}, {9, 9, true}} {
		if got := pairedMultiplyShape(c.outer, c.inner); got != c.paired {
			t.Errorf("pairedMultiplyShape(%d, %d) = %v, want %v", c.outer, c.inner, got, c.paired)
		}
	}
	// The dispatch passes the scalar kernel's outer operand first: an asymmetric
	// shape decides differently in the two orders.
	long, short := limbView(make([]uint32, 8), false), limbView(make([]uint32, 1), false)
	if multiplyPaired(&long, &short) != pairedMultiplyKernel || multiplyPaired(&short, &long) {
		t.Errorf("multiplyPaired(8×1) = %v, (1×8) = %v; want %v, false",
			multiplyPaired(&long, &short), multiplyPaired(&short, &long), pairedMultiplyKernel)
	}
}

// BenchmarkMultiplyKernels times the paired and scalar kernels on square
// and unbalanced shapes; its crossovers are the dispatch thresholds.
func BenchmarkMultiplyKernels(b *testing.B) {
	r := randv2.New(randv2.NewPCG(60, 5))
	random := func(n int) []uint32 {
		s := make([]uint32, n)
		for i := range s {
			s[i] = uint32(r.Uint64N(decimalLimbBase))
		}
		return s
	}
	shapes := [][2]int{{4, 4}, {5, 5}, {4, 6}, {6, 6}, {6, 1}, {8, 1}, {20, 2}, {2, 20}, {34, 34}, {112, 112}, {112, 2}, {1000, 1000}}
	for _, shape := range shapes {
		a, v := limbView(random(shape[0]), true), limbView(random(shape[1]), true)
		out := make([]uint32, shape[0]+shape[1])
		for _, kernel := range []struct {
			name string
			fill func([]uint32, *coefficientView, *coefficientView) bool
		}{{"scalar", fillMultiplyScalar}, {"paired", fillMultiplyPaired}} {
			b.Run(fmt.Sprintf("%dx%d/%s", shape[0], shape[1], kernel.name), func(b *testing.B) {
				for b.Loop() {
					clear(out)
					kernel.fill(out, &a, &v)
				}
			})
		}
	}
}
