// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/big"
	"math/rand/v2"
	"testing"
)

// TestHyperbolicKernelsEncloseOracle checks the hyperbolic kernels
// behind the correct-rounding guarantee at two
// and three limbs: sinhCoshSmall's positive series with its t_N/7 tail for
// 0 < a ≤ 1/2, and asinhDirected (the atanh form up to 1/2, the logarithm
// above) for 0 < a ≤ 3, must enclose the independent oracle from
// the requested side (trigOracleHyper, trigOracle), and the enclosure must
// be narrow, at most two units of its L-th limb for the series (observed:
// one) and sixteen for asinh, which composes a square root, a division and
// a logarithm (observed: nine), so a loose or reversed bound cannot pass by
// containment alone.
func TestHyperbolicKernelsEncloseOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(67, 8))
	ev := newEvaluator(Budget{})
	size := 64
	st := evalStage{ar: ev.arena(uint64(size * 64)), L: 3, size: size}
	checked := [3]int{}
	for i := range 1500 {
		L := 2 + i%2
		k := 1 + rng.IntN(12)
		n := 1 + rng.Int64N(int64(3*decimalPowers[min(k, 8)]))
		a := New(n, -int32(k))
		if a.Compare(New(3, 0)) > 0 {
			continue
		}
		av := coefficientViewOf(a)
		ad, _ := arithmeticDigits(&av)
		mark := st.scope()
		x := ev.load(st.buf(&ev), &av, ad, int64(a.exponent()), false, 8, false)
		xr := enclosureRat(x)
		check := func(name string, j int, units int64, lo, hi evalNum, olo, ohi *big.Rat) {
			t.Helper()
			if olo == nil || enclosureRat(lo).Cmp(olo) > 0 || enclosureRat(hi).Cmp(ohi) < 0 {
				t.Fatalf("%s(%s) at L=%d: [%s, %s] excludes the oracle", name, xr.FloatString(20), L,
					enclosureRat(lo).FloatString(30), enclosureRat(hi).FloatString(30))
			}
			// At most units units of the L-th limb below hi's leading limb.
			unit := new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(1_000_000_000), big.NewInt(max(hi.top()-int64(L), 0)), nil))
			if hi.top()-int64(L) < 0 {
				unit.Inv(new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(1_000_000_000), big.NewInt(int64(L)-hi.top()), nil)))
			}
			width := new(big.Rat).Sub(enclosureRat(hi), enclosureRat(lo))
			if width.Cmp(new(big.Rat).Mul(unit, big.NewRat(units, 1))) > 0 {
				t.Fatalf("%s(%s) at L=%d: [%s, %s] is wider than %d units of %s", name, xr.FloatString(20), L,
					enclosureRat(lo).FloatString(30), enclosureRat(hi).FloatString(30), units, unit.FloatString(30))
			}
			checked[j]++
		}
		if a.Compare(New(5, -1)) <= 0 {
			for j, kind := range []evalKind{evalCosh, evalSinh} {
				olo, ohi := trigOracleHyper(kind, xr, 200)
				lo := ev.sinhCoshSmall(&st, st.buf(&ev), x, uint64(j), L, false)
				hi := ev.sinhCoshSmall(&st, st.buf(&ev), x, uint64(j), L, true)
				check([]string{"cosh", "sinh"}[j], j, 2, lo, hi, olo, ohi)
			}
		}
		olo, ohi := trigOracle(evalAsinh, xr, nil, 200)
		lo := ev.asinhDirected(&st, st.buf(&ev), x, L, false)
		hi := ev.asinhDirected(&st, st.buf(&ev), x, L, true)
		check("asinh", 2, 16, lo, hi, olo, ohi)
		st.restore(mark)
	}
	if !ev.ok() {
		t.Fatalf("status %+v", ev.status)
	}
	if checked[0] < 100 || checked[1] < 100 || checked[2] < 500 {
		t.Fatalf("checked cosh %d, sinh %d, asinh %d cases: the check is vacuous", checked[0], checked[1], checked[2])
	}
}

// positiveSumOracleCosh encloses cosh a for a rational 0 ≤ a ≤ 1/2 by eight
// exact terms and twice the first omitted term.
func positiveSumOracleCosh(a *big.Rat) (lo, hi *big.Rat) {
	lo = new(big.Rat)
	term, a2 := big.NewRat(1, 1), new(big.Rat).Mul(a, a)
	for j := int64(1); j <= 8; j++ {
		lo.Add(lo, term)
		term.Mul(term, a2)
		term.Quo(term, big.NewRat((2*j-1)*(2*j), 1))
	}
	return lo, new(big.Rat).Add(lo, new(big.Rat).Mul(big.NewRat(2, 1), term))
}

// TestPositiveSeriesEnclosesTailCriticalArguments checks the tail bound
// of the guard-limb cosh sum. At W = 5 limbs
// the sum near one has the unit u = 10^−36; a = m·10^−81 with m the
// largest integer such that a²/2 ≤ K·u, for the few K at which a⁴/24
// approaches u: 1 + a²/2 rounds up to 1 + K·u with almost no slack, a⁴/24
// lies below u, and the loop stops there with the sum 1 + (K+1)·u. The
// tail a⁶/720 + … then decides the bound and carries cosh a past that sum
// for one K. positiveSum and sinhCoshSmall must enclose cosh a from both
// sides.
func TestPositiveSeriesEnclosesTailCriticalArguments(t *testing.T) {
	ev := newEvaluator(Budget{})
	size := 64
	st := evalStage{ar: ev.arena(uint64(size * 32)), L: 5, size: size}
	const L, W = 4, 5
	inv := enclosurePow10(W - 1)    // 1/u
	grid := enclosurePow10(2*W - 1) // a = m·10^(−9(2W−1))
	// a0 = m0·grid⁻¹ with a0⁴/24 ≤ u, and K0 = ⌊a0²/(2u)⌋.
	g2 := new(big.Int).Mul(grid, grid)
	m0 := enclosureRoot(new(big.Int).Quo(new(big.Int).Mul(big.NewInt(24), new(big.Int).Mul(g2, g2)), inv), 4)
	K0 := new(big.Int).Quo(new(big.Int).Mul(new(big.Int).Mul(m0, m0), inv), new(big.Int).Mul(big.NewInt(2), g2))
	var one [3]uint32
	critical := 0
	for dk := int64(-3); dk <= 2; dk++ {
		K := new(big.Int).Add(K0, big.NewInt(dk))
		m := new(big.Int).Sqrt(new(big.Int).Quo(new(big.Int).Mul(new(big.Int).Mul(big.NewInt(2), K), g2), inv))
		mark := st.scope()
		a := enclosureNum(st.buf(&ev), m, -(2*W - 1))
		lo, hi := positiveSumOracleCosh(enclosureRat(a))
		var got [4]*big.Rat
		for i, up := range []bool{false, true} {
			ratio := ev.mul(st.buf(&ev), a, a, W, up)
			got[i] = enclosureRat(ev.positiveSum(&st, evalOne(one[:]), ratio, 0, W, up))
			got[2+i] = enclosureRat(ev.sinhCoshSmall(&st, st.buf(&ev), a, 0, L, up))
		}
		if !ev.ok() || got[0].Cmp(lo) > 0 || got[1].Cmp(hi) < 0 || got[2].Cmp(lo) > 0 || got[3].Cmp(hi) < 0 {
			t.Fatalf("cosh(%s·10^-%d) excludes the oracle: W sum [%s, %s], L bound [%s, %s] (%+v)", m, 9*(2*W-1),
				got[0].FloatString(45), got[1].FloatString(45), got[2].FloatString(45), got[3].FloatString(45), ev.status)
		}
		unit := new(big.Rat).SetFrac(big.NewInt(1), inv)
		if new(big.Rat).Sub(got[1], unit).Cmp(lo) < 0 {
			critical++
		}
		st.restore(mark)
	}
	if critical < 1 {
		t.Fatal("no tail-critical argument: the construction lost its witness")
	}
}

// TestPositiveSumAbsorbsRatioRounding checks that the guard-limb positive
// series stays sound when the ratio a² is rounded down in the upper bound.
// positiveSum stops at a term t_N below one unit u of its sum s and adds
// ⌈t_N/7⌉, so the upper bound is at least s + u, while the true tail after
// t_N is at most t_N/7 < u/7 (the true t_N exceeds the computed one by at
// most the factor 1 + N·ρ/a²). A ratio low by one unit ρ of its W-th limb
// lowers the exact partial sum by at most first·ρ/2·(48/47)² for cosh,
// where first·ρ ≤ u·10^−9, and first·ρ/6·(48/47)² for sinh, where
// first·ρ ≤ u/2 because s ≥ a > a² and a ≤ 1/2, so the bound exceeds the
// value by more than u·(1 − 1/7 − 1/11) > 3u/4 whichever way the ratio is
// rounded. At W = 2..5 for cosh and sinh, on random a in (1/4, 1/2]
// (where first·ρ/u is largest) and on the tail-critical cosh arguments of
// TestPositiveSeriesEnclosesTailCriticalArguments, both ratio directions
// must enclose the independent exp oracle (trigOracleHyper) with
// that margin, and some cases must give different upper bounds for the two
// directions, so the rounded-down ratio is observable and still sound.
func TestPositiveSumAbsorbsRatioRounding(t *testing.T) {
	rng := rand.New(rand.NewPCG(67, 4))
	ev := newEvaluator(Budget{})
	size := 64
	st := evalStage{ar: ev.arena(uint64(size * 64)), L: 5, size: size}
	var one [3]uint32
	differ, checked := 0, 0
	minMargin := big.NewRat(1, 1) // in units u
	check := func(a evalNum, off uint64, W int) {
		t.Helper()
		first := a
		if off == 0 {
			first = evalOne(one[:])
		}
		name := []string{"cosh", "sinh"}[off]
		olo, ohi := trigOracleHyper([]evalKind{evalCosh, evalSinh}[off], enclosureRat(a), 9*4*uint(W)+64)
		lower := ev.positiveSum(&st, first, ev.mul(st.buf(&ev), a, a, W, false), off, W, false)
		if !ev.ok() || enclosureRat(lower).Cmp(olo) > 0 {
			t.Fatalf("%s(%s) at W=%d: lower bound %s above the oracle (%+v)", name,
				enclosureRat(a).FloatString(9*2*W), W, enclosureRat(lower).FloatString(9*2*W), ev.status)
		}
		u := enclosureUnit(lower, W)
		var upper [2]*big.Rat
		for i, ratioUp := range []bool{false, true} {
			upper[i] = enclosureRat(ev.positiveSum(&st, first, ev.mul(st.buf(&ev), a, a, W, ratioUp), off, W, true))
			margin := new(big.Rat).Quo(new(big.Rat).Sub(upper[i], ohi), u)
			if !ev.ok() || margin.Cmp(big.NewRat(3, 4)) < 0 {
				t.Fatalf("%s(%s) at W=%d, ratio rounded up %v: upper bound %s lies %s units above the oracle, not 3/4 (%+v)",
					name, enclosureRat(a).FloatString(9*2*W), W, ratioUp, upper[i].FloatString(9*2*W), margin.FloatString(6), ev.status)
			}
			if margin.Cmp(minMargin) < 0 {
				minMargin = margin
			}
		}
		if upper[0].Cmp(upper[1]) != 0 {
			differ++
		}
		checked++
	}
	for i := range 4000 {
		W := 2 + i%4
		// a = m·10^(−9·2W) in (1/4, 1/2].
		grid := enclosurePow10(int64(2 * W))
		m := new(big.Int)
		for range 2 * W {
			m.Mul(m, big.NewInt(1_000_000_000)).Add(m, big.NewInt(rng.Int64N(1_000_000_000)))
		}
		m.Quo(m, big.NewInt(4)).Add(m, new(big.Int).Quo(grid, big.NewInt(4))).Add(m, big.NewInt(1))
		mark := st.scope()
		check(enclosureNum(st.buf(&ev), m, -int64(2*W)), uint64(i/4%2), W)
		st.restore(mark)
	}
	// The tail-critical cosh arguments at W = 5.
	const W = 5
	inv, grid := enclosurePow10(W-1), enclosurePow10(2*W-1)
	g2 := new(big.Int).Mul(grid, grid)
	m0 := enclosureRoot(new(big.Int).Quo(new(big.Int).Mul(big.NewInt(24), new(big.Int).Mul(g2, g2)), inv), 4)
	K0 := new(big.Int).Quo(new(big.Int).Mul(new(big.Int).Mul(m0, m0), inv), new(big.Int).Mul(big.NewInt(2), g2))
	for dk := int64(-3); dk <= 2; dk++ {
		K := new(big.Int).Add(K0, big.NewInt(dk))
		m := new(big.Int).Sqrt(new(big.Int).Quo(new(big.Int).Mul(new(big.Int).Mul(big.NewInt(2), K), g2), inv))
		mark := st.scope()
		check(enclosureNum(st.buf(&ev), m, -(2*W-1)), 0, W)
		st.restore(mark)
	}
	t.Logf("%d cases, %d with different upper bounds, least margin %s units", checked, differ, minMargin.FloatString(4))
	if differ < 10 {
		t.Fatalf("only %d of %d cases distinguish the ratio directions: the check is vacuous", differ, checked)
	}
}
