// SPDX-License-Identifier: Apache-2.0

package decimal

// Certified kernels for the trigonometric and hyperbolic functions.
// Every kernel takes an exact endpoint and encloses the function value from
// the requested side (up = toward +∞); monotone functions are then
// evaluated at the endpoints of a certified argument interval.

// pi encloses π at L limbs: the table, or Machin's
// 16·atan(1/5) − 4·atan(1/239) under the meter.
func (ev *evaluator) pi(st *evalStage, dst []uint32, L int, up bool) evalNum {
	if L < evalConstantLimbs {
		return ev.evalConstant(dst, evalPi, L, up)
	}
	mark := st.scope()
	defer st.restore(mark)
	a5, a239, t5, t239, sum := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	var k16, k4 [3]uint32
	x := ev.atanInverseAlternating(st, a5, 5, L+1, up)
	y := ev.atanInverseAlternating(st, a239, 239, L+1, !up)
	x = ev.mul(t5, x, evalSmall(k16[:], 16, false), L+1, up)
	y = ev.mul(t239, y, evalSmall(k4[:], 4, true), L+1, up)
	return ev.round(dst, ev.add(sum, x, y, L+1, up), L, up)
}

// atanInverseAlternating encloses atan(1/q) = Σ (−1)^j/((2j+1)·q^(2j+1)).
// The terms decrease, so the tail after the last added term lies between
// zero and the next term, whose magnitude the current one bounds. Every
// partial sum lies in [1/q − 1/(3q³), 1/q] ⊂ (10⁻⁹, 1) for 2 ≤ q < 2^16,
// so no addition crosses a power of 10⁹: without the tail addend the bound
// is one unit tighter and still sound, so no enclosure test can detect its
// omission.
func (ev *evaluator) atanInverseAlternating(st *evalStage, dst []uint32, q uint64, L int, up bool) evalNum {
	mark := st.scope()
	defer st.restore(mark)
	pu, pd, tb, sb, nb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	var one [3]uint32
	powUp := ev.divSmall(pu, evalOne(one[:]), q, L, true)
	powDown := ev.divSmall(pd, evalOne(one[:]), q, L, false)
	sum := ev.round(sb, powUp, L, up)
	if !up {
		sum = ev.round(sb, powDown, L, up)
	}
	var term evalNum
	for j := uint64(1); ev.ok(); j++ {
		if !ev.charge(1) {
			break
		}
		powUp = ev.divSmall(pu, powUp, q*q, L, true)
		powDown = ev.divSmall(pd, powDown, q*q, L, false)
		// Subtracted terms are rounded against the bound's direction.
		negative := j%2 == 1
		if negative == up {
			term = ev.divSmall(tb, powDown, 2*j+1, L, false)
		} else {
			term = ev.divSmall(tb, powUp, 2*j+1, L, true)
		}
		if negative {
			term = term.negate()
		}
		sum = ev.add(nb, sum, term, L, up)
		sb, nb = nb, sb
		if powUp.top() <= sum.top()-int64(L) {
			break
		}
	}
	// |tail| ≤ the next term ≤ powUp.
	tail := powUp
	if !up {
		tail = powUp.negate()
	}
	return ev.round(dst, ev.add(nb, sum, tail, L, up), L, up)
}

// alternatingSeries encloses Σ (−1)^j t_j for a decreasing positive term
// sequence t_0 = first and t_j = t_{j−1}·ratio/(den(j)), from the requested
// side. ratioUp and ratioDown enclose the exact ratio numerator (≥ 0).
// den(j) = (2j−1+off)(2j+off) with off 0 for cosine-like and 1 for
// sine-like series, or 2j+1 with the numerator carried by p (atan). A
// bound needs the tail when the last term's addition crosses a power of
// 10⁹ (TestAlternatingSeriesEnclosesAcrossLimbBoundary).
func (ev *evaluator) alternatingSeries(st *evalStage, dst []uint32, first, ratioUp, ratioDown evalNum, kind int, L int, up bool) evalNum {
	mark := st.scope()
	defer st.restore(mark)
	tu, td, pb, qb, sb, nb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	W := L + 1
	termUp := ev.round(tu, first, W, true)
	termDown := ev.round(td, first, W, false)
	sum := ev.round(sb, first, W, up)
	powUp, powDown := termUp, termDown // atan: v^(2j+1) before its divisor
	for j := uint64(1); ev.ok(); j++ {
		if !ev.charge(1) {
			break
		}
		var magUp, magDown evalNum
		switch kind {
		case seriesAtan:
			powUp = ev.round(tu, ev.mul(qb, powUp, ratioUp, W, true), W, true)
			powDown = ev.round(td, ev.mul(qb, powDown, ratioDown, W, false), W, false)
			magUp = ev.divSmall(pb, powUp, 2*j+1, W, true)
			magDown = ev.divSmall(qb, powDown, 2*j+1, W, false)
		default:
			off := uint64(kind) // 0 cosine, 1 sine
			termUp = ev.divPair(tu, ev.mul(qb, termUp, ratioUp, W, true), 2*j-1+off, 2*j+off, W, true)
			termDown = ev.divPair(td, ev.mul(pb, termDown, ratioDown, W, false), 2*j-1+off, 2*j+off, W, false)
			magUp, magDown = termUp, termDown
		}
		negative := j%2 == 1
		term := magUp
		if negative == up {
			term = magDown
		}
		if negative {
			term = term.negate()
		}
		sum = ev.add(nb, sum, term, W, up)
		sb, nb = nb, sb
		if magUp.isZero() || magUp.top() <= sum.top()-int64(W) {
			// The tail after this term is at most the next term, below
			// the current magnitude.
			tail := magUp
			if !up {
				tail = magUp.negate()
			}
			sum = ev.add(nb, sum, tail, W, up)
			break
		}
	}
	return ev.round(dst, sum, L, up)
}

const (
	seriesCosine = 0
	seriesSine   = 1
	seriesAtan   = 2
)

// sinDirected encloses sin a for an exact |a| ≤ 0.8 by its alternating
// Taylor series; negative arguments use odd symmetry.
func (ev *evaluator) sinDirected(st *evalStage, dst []uint32, a evalNum, L int, up bool) evalNum {
	if a.isZero() {
		return evalNum{}
	}
	if a.neg {
		return ev.sinDirected(st, dst, a.negate(), L, !up).negate()
	}
	mark := st.scope()
	defer st.restore(mark)
	su, sd := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	a2u, a2d := ev.mul(su, a, a, L+1, true), ev.mul(sd, a, a, L+1, false)
	return ev.alternatingSeries(st, dst, a, a2u, a2d, seriesSine, L, up)
}

// cosDirected encloses cos a for an exact |a| ≤ 0.8.
func (ev *evaluator) cosDirected(st *evalStage, dst []uint32, a evalNum, L int, up bool) evalNum {
	var one [3]uint32
	if a.isZero() {
		return ev.round(dst, evalOne(one[:]), L, up)
	}
	a.neg = false
	mark := st.scope()
	defer st.restore(mark)
	su, sd := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	a2u, a2d := ev.mul(su, a, a, L+1, true), ev.mul(sd, a, a, L+1, false)
	return ev.alternatingSeries(st, dst, evalOne(one[:]), a2u, a2d, seriesCosine, L, up)
}

// sqrtDirected encloses √a for an exact a ≥ 0 with the exact integer-root
// kernel of sqrt.go: a = N·10^(9E) with E even and N of at least 2L+2
// limbs (a longer N truncated, the truncation kept as sticky); ⌊√N⌋ is the
// lower bound and one more unit the upper unless the root is exact.
func (ev *evaluator) sqrtDirected(st *evalStage, dst []uint32, a evalNum, L int, up bool) evalNum {
	if a.isZero() || a.neg {
		return evalNum{}
	}
	mark := st.scope()
	defer st.restore(mark)
	nb, ub, wb := st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	e := a.e
	n := len(a.m)
	pre := 0 // zero limbs prepended
	if e%2 != 0 {
		pre = 1
	}
	want := 2*L + 2
	if n+pre < want {
		pre += (want - n - pre + 1) / 2 * 2
	}
	drop := 0
	if n+pre > want+1 {
		drop = (n + pre - want) / 2 * 2
	}
	if n+pre-drop+2 > cap(nb) || !ev.charge(uint64(n+pre)) {
		ev.broken()
		return evalNum{}
	}
	sticky := false
	for i := range min(drop, n+pre) {
		if i >= pre && a.m[i-pre] != 0 {
			sticky = true
		}
	}
	total := n + pre - drop
	for i := range total {
		src := i + drop - pre
		if src >= 0 && src < n {
			nb[i] = a.m[src]
		} else {
			nb[i] = 0
		}
	}
	N := trimLimbs(nb[:total])
	E := e - int64(pre) + int64(drop)
	s := limbsDigits(N)
	r := (s + 1) / 2
	charge, ok := sqrtCharge(s, r)
	l := newSqrtLayout(s, r)
	if !ok || l.u > uint64(cap(ub)) || 2*l.w > uint64(cap(wb)) {
		ev.broken()
		return evalNum{}
	}
	if !ev.charge(charge) {
		return evalNum{}
	}
	nn := nb[: len(N)+1 : len(N)+1]
	nn[len(N)] = 0
	root := sqrtNewton(nn[:len(N)], r, ub[:l.u], wb[:l.w], wb[l.w:2*l.w], nil)
	// Exact iff root² = N and nothing was truncated.
	exact := !sticky
	if exact {
		sq := ev.mul(ub, evalNum{m: root}, evalNum{m: root}, evalExact, false)
		exact = cmpMag(sq, evalNum{m: N}) == 0
	}
	res := evalNum{m: root, e: E / 2}
	if up && !exact {
		var one [3]uint32
		res = ev.add(dst, res, evalNum{m: evalOne(one[:]).m, e: E / 2}, L+1, true)
		return ev.round(dst, res, L, up)
	}
	return ev.round(dst, res, L, up)
}

// atanSmall encloses atan v for an exact 0 ≤ v ≤ 0.2 by its alternating
// series.
func (ev *evaluator) atanSmall(st *evalStage, dst []uint32, v evalNum, L int, up bool) evalNum {
	if v.isZero() {
		return evalNum{}
	}
	mark := st.scope()
	defer st.restore(mark)
	su, sd := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	v2u, v2d := ev.mul(su, v, v, L+1, true), ev.mul(sd, v, v, L+1, false)
	return ev.alternatingSeries(st, dst, v, v2u, v2d, seriesAtan, L, up)
}

// halfAngle encloses v/(1+√(1+v²)) = tan(atan(v)/2), increasing in v.
func (ev *evaluator) halfAngle(st *evalStage, dst []uint32, v evalNum, L int, up bool) evalNum {
	mark := st.scope()
	defer st.restore(mark)
	sq, rt, den := st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	var one [3]uint32
	// A larger denominator lowers the quotient: round it against up.
	s := ev.add(den, ev.mul(sq, v, v, L+1, !up), evalOne(one[:]), L+1, !up)
	r := ev.sqrtDirected(st, rt, s, L+1, !up)
	d := ev.add(sq, r, evalOne(one[:]), L+1, !up)
	return ev.div(dst, den, v, d, L, up)
}

// atanDirected encloses atan a for an exact a: odd symmetry, π/2 − atan(1/a)
// above one, two half-angle steps down to ≤ tan(π/16) < 0.2, then the
// series; atan v = 2^h·atan(v_h).
func (ev *evaluator) atanDirected(st *evalStage, dst []uint32, a evalNum, L int, up bool) evalNum {
	if a.isZero() {
		return evalNum{}
	}
	if a.neg {
		return ev.atanDirected(st, dst, a.negate(), L, !up).negate()
	}
	mark := st.scope()
	defer st.restore(mark)
	vb, wb, pb, qb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	var one [3]uint32
	oneN := evalOne(one[:])
	if !ev.charge(uint64(len(a.m))) {
		return evalNum{}
	}
	if cmpMag(a, oneN) > 0 {
		inv := ev.div(vb, qb, oneN, a, L+1, !up)
		t := ev.atanDirected(st, wb, inv, L+1, !up)
		half := ev.divSmall(pb, ev.pi(st, qb, L+1, up), 2, L+1, up)
		return ev.add(dst, half, t.negate(), L, up)
	}
	v := ev.round(vb, a, L+1, up)
	var h uint64
	fifth := [1]uint32{200_000_000}
	limit := evalNum{m: fifth[:], e: -1} // 0.2
	for h < 2 && cmpMag(v, limit) > 0 {
		v = ev.round(vb, ev.halfAngle(st, wb, v, L+1, up), L+1, up)
		h++
	}
	s := ev.atanSmall(st, wb, v, L+1, up)
	return ev.mul(dst, s, evalSmall(pb[:3], 1<<h, false), L, up)
}

// evalNudge encloses x ± one unit of its L-th limb (x > 0) from the side up;
// x must not live in dst.
func (ev *evaluator) evalNudge(dst []uint32, x evalNum, L int, up bool) evalNum {
	unit := [1]uint32{1}
	u := evalNum{m: unit[:], e: x.top() - int64(L)}
	if !up {
		u = u.negate()
	}
	return ev.add(dst, x, u, L+1, up)
}

// tinyOdd applies the one-sided filter of an odd function f with
// |f(a) − a| < 2·a^3 on a positive argument interval [alo, ahi]: when the
// displacement is below one unit of the L-th limb, f's enclosure is [alo
// less one unit, ahi] below the center or [alo, ahi plus one unit] above.
func (ev *evaluator) tinyOdd(lo, hi []uint32, alo, ahi evalNum, L int, above bool) (evalNum, evalNum, bool) {
	if alo.isZero() || !ev.charge(1) {
		return evalNum{}, evalNum{}, false
	}
	// 2·a³ < 10^(3(adj+1)+1); one unit of alo's L-th limb ≥ 10^(adj_lo+1−9L).
	if 3*(ahi.adjusted()+1)+1 > alo.adjusted()+1-9*int64(L) {
		return evalNum{}, evalNum{}, false
	}
	// The endpoint moved one unit of its L-th limb outward; x is not in dst.
	l, h := ev.round(lo, alo, L, false), ev.round(hi, ahi, L, true)
	if above {
		h = ev.evalNudge(hi, ahi, L, true)
	} else {
		l = ev.evalNudge(lo, alo, L, false)
	}
	return l, h, true
}

// tinyEven applies the filter of cos or cosh around 1 (displacement below
// a²): [1 − unit, 1] or [1, 1 + unit] at L limbs.
func (ev *evaluator) tinyEven(lo, hi []uint32, ahi evalNum, L int, above bool) (evalNum, evalNum, bool) {
	if !ev.charge(1) || !ahi.isZero() && 2*(ahi.adjusted()+1)+1 > 9-9*int64(L) {
		return evalNum{}, evalNum{}, false
	}
	var one [3]uint32
	oneN := evalOne(one[:])
	l, h := ev.round(lo, oneN, L, false), ev.round(hi, oneN, L, true)
	if above {
		h = ev.evalNudge(hi, oneN, L, true)
	} else {
		l = ev.evalNudge(lo, oneN, L, false)
	}
	return l, h, true
}

// reduce encloses r = a − q·π/2 for the argument interval [alo, ahi] ≥ 0
// with q the integer nearest 2·alo/π, and returns q mod 4. The reduction's
// π, quotient and products live in their own admitted arena, sized from
// the digits of q and released once r is copied into rl and rh.
func (ev *evaluator) reduce(rl, rh []uint32, alo, ahi evalNum, L int) (evalNum, evalNum, int, bool) {
	D := max(int64(0), ahi.adjusted()) + 1
	Lq := L + int((D+8)/9) + 1
	size := 3*Lq + 24
	ar := ev.arena(uint64(size) * 24)
	defer ev.release(&ar)
	rst := evalStage{ar: ar, L: Lq, size: size}
	pl, ph, ml, qb, xb, yb, sb := rst.buf(ev), rst.buf(ev), rst.buf(ev), rst.buf(ev), rst.buf(ev), rst.buf(ev), rst.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}, 0, false
	}
	piLo, piHi := ev.pi(&rst, pl, Lq, false), ev.pi(&rst, ph, Lq, true)
	var two [3]uint32
	twoN := evalSmall(two[:], 2, false)
	m := ev.div(ml, sb, ev.mul(xb, alo, twoN, evalExact, false), piHi, Lq, false)
	half := [1]uint32{500_000_000}
	q := evalFloor(ev.add(qb, m, evalNum{m: half[:], e: -1}, Lq, false))
	q4 := 0
	if !q.isZero() && q.e == 0 {
		q4 = int(q.m[0] % 4)
	}
	// q·π/2 lies in [q·π_lo/2, q·π_hi/2]; r = a − q·π/2.
	var rlo, rhi evalNum
	if q.isZero() {
		rlo, rhi = ev.round(rl, alo, L+1, false), ev.round(rh, ahi, L+1, true)
	} else {
		kl := ev.divSmall(xb, ev.mul(yb, q, piLo, evalExact, false), 2, Lq+1, false)
		kh := ev.divSmall(yb, ev.mul(sb, q, piHi, evalExact, true), 2, Lq+1, true)
		rlo = ev.round(rl, ev.add(sb, alo, kh.negate(), L+1, false), L+1, false)
		rhi = ev.round(rh, ev.add(ml, ahi, kl.negate(), L+1, true), L+1, true)
	}
	// 0.7862 lies above π/4·(1 + 10^−3).
	reduced := [1]uint32{786_200_000}
	limit := evalNum{m: reduced[:], e: -1}
	if !ev.charge(uint64(len(rlo.m)+len(rhi.m))) || evalCmp(rlo, limit.negate()) < 0 || evalCmp(rhi, limit) > 0 {
		return evalNum{}, evalNum{}, 0, false
	}
	return rlo, rhi, q4, true
}

// ivDiv encloses the quotient of two intervals whose denominator excludes
// zero: the extreme directed endpoint quotients.
func (ev *evaluator) ivDiv(st *evalStage, lo, hi []uint32, nlo, nhi, dlo, dhi evalNum, L int) (evalNum, evalNum) {
	mark := st.scope()
	defer st.restore(mark)
	tb, sb := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}
	}
	var l, h evalNum
	first := true
	for _, n := range [2]evalNum{nlo, nhi} {
		for _, d := range [2]evalNum{dlo, dhi} {
			if !ev.charge(uint64(len(n.m) + len(d.m))) {
				return evalNum{}, evalNum{}
			}
			if q := ev.div(tb, sb, n, d, L, false); first || evalCmp(q, l) < 0 {
				l = ev.round(lo, q, L, false)
			}
			if q := ev.div(tb, sb, n, d, L, true); first || evalCmp(q, h) > 0 {
				h = ev.round(hi, q, L, true)
			}
			first = false
		}
	}
	return l, h
}

// sinCosTanEnclose encloses sin, cos or tan of x at L limbs.
func (ev *evaluator) sinCosTanEnclose(st *evalStage, lo, hi []uint32, pr *evalProblem, L int) (evalNum, evalNum, evalRange) {
	mark := st.scope()
	defer st.restore(mark)
	al, ah, rl, rh, sl, sh, cl, ch, tb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}, evalInRange
	}
	alo := ev.load(al, &pr.x, pr.xDigits, pr.xExp, false, L+2, false)
	ahi := ev.load(ah, &pr.x, pr.xDigits, pr.xExp, false, L+2, true)
	neg := pr.xNeg
	// Tiny arguments: sin below a, tan above a, cos below one.
	switch pr.kind {
	case evalSin, evalTan:
		if l, h, ok := ev.tinyOdd(lo, hi, alo, ahi, L, pr.kind == evalTan); ok {
			return evalOdd(l, h, neg)
		}
	case evalCos:
		if l, h, ok := ev.tinyEven(lo, hi, ahi, L, false); ok {
			return l, h, evalInRange
		}
	}
	var rlo, rhi evalNum
	q4 := 0
	quarter := [1]uint32{785_398_100} // just below π/4
	if evalCmp(ahi, evalNum{m: quarter[:], e: -1}) < 0 {
		rlo, rhi = alo, ahi
	} else {
		var ok bool
		if rlo, rhi, q4, ok = ev.reduce(rl, rh, alo, ahi, L); !ok {
			return evalNum{}, evalNum{}, evalWide
		}
	}
	// The quadrant decides which of the reduced sine and cosine the result
	// reads; only the tangent needs both.
	needSin := pr.kind == evalTan || (pr.kind == evalSin) == (q4%2 == 0)
	needCos := pr.kind == evalTan || !needSin
	// sin is increasing on the reduced interval; cos peaks at zero.
	var sLo, sHi, cLo, cHi evalNum
	if needSin {
		sLo, sHi = ev.sinDirected(st, sl, rlo, L+1, false), ev.sinDirected(st, sh, rhi, L+1, true)
	}
	switch {
	case !needCos:
	case !rlo.neg && !rlo.isZero() || rlo.isZero() && !rhi.neg:
		cLo, cHi = ev.cosDirected(st, cl, rhi, L+1, false), ev.cosDirected(st, ch, rlo, L+1, true)
	case rhi.neg || rhi.isZero():
		cLo, cHi = ev.cosDirected(st, cl, rlo, L+1, false), ev.cosDirected(st, ch, rhi, L+1, true)
	default:
		c1 := ev.cosDirected(st, cl, rlo, L+1, false)
		c2 := ev.cosDirected(st, tb, rhi, L+1, false)
		if evalCmp(c2, c1) < 0 {
			c1 = ev.round(cl, c2, L+1, false)
		}
		var one [3]uint32
		cLo, cHi = c1, ev.round(ch, evalOne(one[:]), L+1, true)
	}
	// Quadrant q: (sin, cos)(r + q·π/2).
	switch q4 {
	case 1:
		sLo, sHi, cLo, cHi = cLo, cHi, sHi.negate(), sLo.negate()
	case 2:
		sLo, sHi, cLo, cHi = sHi.negate(), sLo.negate(), cHi.negate(), cLo.negate()
	case 3:
		sLo, sHi, cLo, cHi = cHi.negate(), cLo.negate(), sLo, sHi
	}
	switch pr.kind {
	case evalSin:
		return evalOdd(ev.round(lo, sLo, L, false), ev.round(hi, sHi, L, true), neg)
	case evalCos:
		return ev.round(lo, cLo, L, false), ev.round(hi, cHi, L, true), evalInRange
	}
	if evalSign(cLo) != evalSign(cHi) || cLo.isZero() {
		return evalNum{}, evalNum{}, evalWide // the enclosure still meets a pole
	}
	l, h := ev.ivDiv(st, lo, hi, sLo, sHi, cLo, cHi, L)
	return evalOdd(l, h, neg)
}

// evalOdd applies odd symmetry to an enclosure of f(|x|).
func evalOdd(l, h evalNum, neg bool) (evalNum, evalNum, evalRange) {
	if neg {
		return h.negate(), l.negate(), evalInRange
	}
	return l, h, evalInRange
}

// oneMinus encloses 1 − x (or 1 + x) from the side up; it is exact
// whenever x's limbs fit dst's window below one.
func (ev *evaluator) oneMinus(dst []uint32, x evalNum, plus, up bool) evalNum {
	var one [3]uint32
	if !plus {
		x = x.negate()
	}
	return ev.add(dst, evalOne(one[:]), x, evalExact, up)
}

// asinDirected encloses asin a for an exact 0 ≤ a ≤ 1:
// 2·atan(a/(1 + √((1−a)(1+a)))), increasing in a; asin 1 = π/2.
func (ev *evaluator) asinDirected(st *evalStage, dst []uint32, a evalNum, L int, up bool) evalNum {
	if a.isZero() {
		return evalNum{}
	}
	mark := st.scope()
	defer st.restore(mark)
	m, p, q, r, w := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	var one, two [3]uint32
	oneN := evalOne(one[:])
	if !ev.charge(uint64(len(a.m))) {
		return evalNum{}
	}
	if cmpMag(a, oneN) >= 0 {
		return ev.divSmall(dst, ev.pi(st, m, L+1, up), 2, L, up)
	}
	// A smaller denominator raises the quotient: round it against up.
	// 1 ± a are exact over a whole buffer for tiny a: keep L+2 limbs.
	oneLess := ev.round(m, ev.oneMinus(r, a, false, !up), L+2, !up)
	oneMore := ev.round(p, ev.oneMinus(r, a, true, !up), L+2, !up)
	rad := ev.mul(r, oneLess, oneMore, L+1, !up)
	den := ev.add(q, ev.sqrtDirected(st, w, rad, L+1, !up), oneN, L+1, !up)
	t := ev.atanDirected(st, w, ev.div(m, r, a, den, L+1, up), L+1, up)
	return ev.mul(dst, t, evalSmall(two[:], 2, false), L, up)
}

// acosDirected encloses acos x for an exact −1 ≤ x ≤ 1: for x ≥ 0,
// 2·atan(√((1−x)/(1+x))), decreasing in x; below zero, π − acos(−x).
func (ev *evaluator) acosDirected(st *evalStage, dst []uint32, x evalNum, L int, up bool) evalNum {
	mark := st.scope()
	defer st.restore(mark)
	m, p, q, r, w := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	if x.neg {
		t := ev.acosDirected(st, w, x.negate(), L+1, !up)
		return ev.add(dst, ev.pi(st, m, L+1, up), t.negate(), L, up)
	}
	var two [3]uint32
	// 1 ± x are exact over a whole buffer for tiny x: keep L+2 limbs, so
	// the division's scratch stays within the stage buffers.
	num := ev.round(m, ev.oneMinus(q, x, false, up), L+2, up)
	den := ev.round(p, ev.oneMinus(q, x, true, !up), L+2, !up)
	if num.isZero() {
		return evalNum{}
	}
	s := ev.sqrtDirected(st, r, ev.div(q, w, num, den, L+1, up), L+1, up)
	t := ev.atanDirected(st, w, s, L+1, up)
	return ev.mul(dst, t, evalSmall(two[:], 2, false), L, up)
}

// inverseTrigEnclose encloses asin, acos, atan or atan2 at L limbs.
func (ev *evaluator) inverseTrigEnclose(st *evalStage, lo, hi []uint32, pr *evalProblem, L int) (evalNum, evalNum, evalRange) {
	mark := st.scope()
	defer st.restore(mark)
	al, ah, bl, bh, tl, th, pb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}, evalInRange
	}
	var one [3]uint32
	oneN := evalOne(one[:])
	switch pr.kind {
	case evalAcos:
		xlo := ev.load(al, &pr.x, pr.xDigits, pr.xExp, pr.xNeg, L+2, false)
		xhi := ev.load(ah, &pr.x, pr.xDigits, pr.xExp, pr.xNeg, L+2, true)
		// |x| ≤ 1: a rounded endpoint beyond ±1 is clamped.
		if evalCmp(xhi, oneN) > 0 {
			xhi = oneN
		}
		if evalCmp(xlo, oneN.negate()) < 0 {
			xlo = oneN.negate()
		}
		return ev.acosDirected(st, lo, xhi, L, false), ev.acosDirected(st, hi, xlo, L, true), evalInRange
	case evalAtan2:
		return ev.atan2Enclose(st, lo, hi, pr, L)
	}
	alo := ev.load(al, &pr.x, pr.xDigits, pr.xExp, false, L+2, false)
	ahi := ev.load(ah, &pr.x, pr.xDigits, pr.xExp, false, L+2, true)
	if l, h, ok := ev.tinyOdd(lo, hi, alo, ahi, L, pr.kind == evalAsin); ok {
		return evalOdd(l, h, pr.xNeg)
	}
	_, _, _ = bl, bh, pb
	if pr.kind == evalAsin {
		if cmpMag(ahi, oneN) > 0 {
			ahi = oneN
		}
		return evalOdd(ev.asinDirected(st, tl, alo, L, false), ev.asinDirected(st, th, ahi, L, true), pr.xNeg)
	}
	return evalOdd(ev.atanDirected(st, tl, alo, L, false), ev.atanDirected(st, th, ahi, L, true), pr.xNeg)
}

// atan2Enclose encloses atan2(y, x) off the axes: the atan of the smaller
// over the larger magnitude, π/2 minus it when |y| > |x|, π minus that for
// x < 0, signed by y. pr.y is the receiver y and pr.x the argument x.
func (ev *evaluator) atan2Enclose(st *evalStage, lo, hi []uint32, pr *evalProblem, L int) (evalNum, evalNum, evalRange) {
	mark := st.scope()
	defer st.restore(mark)
	yl, yh, xl, xh, rl, rh, tl, th, pl, ph, sb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}, evalInRange
	}
	ylo := ev.load(yl, &pr.y, pr.yDigits, pr.yExp, false, L+2, false)
	yhi := ev.load(yh, &pr.y, pr.yDigits, pr.yExp, false, L+2, true)
	xlo := ev.load(xl, &pr.x, pr.xDigits, pr.xExp, false, L+2, false)
	xhi := ev.load(xh, &pr.x, pr.xDigits, pr.xExp, false, L+2, true)
	nlo, nhi, dlo, dhi := ylo, yhi, xlo, xhi
	if pr.swap {
		nlo, nhi, dlo, dhi = xlo, xhi, ylo, yhi
	}
	rlo, rhi := ev.div(rl, sb, nlo, dhi, L+1, false), ev.div(rh, sb, nhi, dlo, L+1, true)
	tlo, thi, ok := ev.tinyOdd(tl, th, rlo, rhi, L+1, false)
	if !ok {
		tlo, thi = ev.atanDirected(st, tl, rlo, L+1, false), ev.atanDirected(st, th, rhi, L+1, true)
	}
	if pr.swap {
		halfLo := ev.divSmall(pl, ev.pi(st, sb, L+1, false), 2, L+1, false)
		halfHi := ev.divSmall(ph, ev.pi(st, sb, L+1, true), 2, L+1, true)
		tlo, thi = ev.add(rl, halfLo, thi.negate(), L+1, false), ev.add(rh, halfHi, tlo.negate(), L+1, true)
	}
	if pr.xNeg {
		pLo, pHi := ev.pi(st, pl, L+1, false), ev.pi(st, ph, L+1, true)
		tlo, thi = ev.add(xl, pLo, thi.negate(), L+1, false), ev.add(xh, pHi, tlo.negate(), L+1, true)
	}
	return evalOdd(ev.round(lo, tlo, L, false), ev.round(hi, thi, L, true), pr.yNeg)
}

// Sin returns sin d (radians) exactly: Sin(0) is 0; every other finite d has
// a transcendental sine and returns a *Error with Condition Inexact
// and a remedy naming SinWithContext.
func (d Decimal) Sin() (Decimal, error) {
	result, _, err := d.elementary(evalSin, Decimal{}, Context{}, Budget{}, "Sin")
	return result, err
}

// SinWithContext rounds sin d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Sin.
func (d Decimal) SinWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalSin, Decimal{}, ctx, ctx.Budget(), "SinWithContext")
}

// Cos returns cos d (radians) exactly: Cos(0) is 1; every other finite d
// returns a *Error with Condition Inexact and a remedy naming
// CosWithContext.
func (d Decimal) Cos() (Decimal, error) {
	result, _, err := d.elementary(evalCos, Decimal{}, Context{}, Budget{}, "Cos")
	return result, err
}

// CosWithContext rounds cos d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Cos.
func (d Decimal) CosWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalCos, Decimal{}, ctx, ctx.Budget(), "CosWithContext")
}

// Tan returns tan d (radians) exactly: Tan(0) is 0; every other finite d
// returns a *Error with Condition Inexact and a remedy naming
// TanWithContext. No finite decimal is a pole.
func (d Decimal) Tan() (Decimal, error) {
	result, _, err := d.elementary(evalTan, Decimal{}, Context{}, Budget{}, "Tan")
	return result, err
}

// TanWithContext rounds tan d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Tan.
func (d Decimal) TanWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalTan, Decimal{}, ctx, ctx.Budget(), "TanWithContext")
}

// Asin returns arcsin d in [−π/2, π/2] exactly: Asin(0) is 0, other d in
// [−1, 1] return a *Error with Condition Inexact and a remedy naming
// AsinWithContext, and |d| > 1 returns ErrInvalidOperation.
func (d Decimal) Asin() (Decimal, error) {
	result, _, err := d.elementary(evalAsin, Decimal{}, Context{}, Budget{}, "Asin")
	return result, err
}

// AsinWithContext rounds asin d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Asin.
func (d Decimal) AsinWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalAsin, Decimal{}, ctx, ctx.Budget(), "AsinWithContext")
}

// Acos returns arccos d in [0, π] exactly: Acos(1) is 0, other d in [−1, 1]
// return a *Error with Condition Inexact and a remedy naming
// AcosWithContext, and |d| > 1 returns ErrInvalidOperation.
func (d Decimal) Acos() (Decimal, error) {
	result, _, err := d.elementary(evalAcos, Decimal{}, Context{}, Budget{}, "Acos")
	return result, err
}

// AcosWithContext rounds acos d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Acos.
func (d Decimal) AcosWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalAcos, Decimal{}, ctx, ctx.Budget(), "AcosWithContext")
}

// Atan returns arctan d in (−π/2, π/2) exactly: Atan(0) is 0; every other
// finite d returns a *Error with Condition Inexact and a remedy
// naming AtanWithContext.
func (d Decimal) Atan() (Decimal, error) {
	result, _, err := d.elementary(evalAtan, Decimal{}, Context{}, Budget{}, "Atan")
	return result, err
}

// AtanWithContext rounds atan d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Atan.
func (d Decimal) AtanWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalAtan, Decimal{}, ctx, ctx.Budget(), "AtanWithContext")
}

// Atan2 returns the angle of the point (x, d) in (−π, π], with the receiver
// d first as in math.Atan2(d, x). Atan2(0, x > 0) is 0; every other point
// but the origin returns a *Error with Condition Inexact and a remedy
// naming Atan2WithContext; the origin returns ErrInvalidOperation. There is
// one unsigned zero, so the negative x-axis gives +π.
func (d Decimal) Atan2(x Decimal) (Decimal, error) {
	result, _, err := d.elementary(evalAtan2, x, Context{}, Budget{}, "Atan2")
	return result, err
}

// Atan2WithContext rounds atan2(d, x) once to the context precision in the
// context's mode, with guards and traps. Context{} behaves as Atan2.
func (d Decimal) Atan2WithContext(x Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalAtan2, x, ctx, ctx.Budget(), "Atan2WithContext")
}

// elementaryRemedy is each function's constant exact-context remedy.
func elementaryRemedy(kind evalKind) string {
	switch kind {
	case evalSin:
		return "non-terminating sine: supply a finite-precision context (SinWithContext)"
	case evalCos:
		return "non-terminating cosine: supply a finite-precision context (CosWithContext)"
	case evalTan:
		return "non-terminating tangent: supply a finite-precision context (TanWithContext)"
	case evalAsin:
		return "non-terminating arcsine: supply a finite-precision context (AsinWithContext)"
	case evalAcos:
		return "non-terminating arccosine: supply a finite-precision context (AcosWithContext)"
	case evalAtan:
		return "non-terminating arctangent: supply a finite-precision context (AtanWithContext)"
	case evalAtan2:
		return "non-terminating arctangent: supply a finite-precision context (Atan2WithContext)"
	case evalSinh:
		return "non-terminating hyperbolic sine: supply a finite-precision context (SinhWithContext)"
	case evalCosh:
		return "non-terminating hyperbolic cosine: supply a finite-precision context (CoshWithContext)"
	case evalTanh:
		return "non-terminating hyperbolic tangent: supply a finite-precision context (TanhWithContext)"
	case evalAsinh:
		return "non-terminating inverse hyperbolic sine: supply a finite-precision context (AsinhWithContext)"
	case evalAcosh:
		return "non-terminating inverse hyperbolic cosine: supply a finite-precision context (AcoshWithContext)"
	case evalAtanh:
		return "non-terminating inverse hyperbolic tangent: supply a finite-precision context (AtanhWithContext)"
	}
	return ""
}

// elementary runs one trigonometric or hyperbolic function of d, with other the
// Atan2 argument d when the receiver is its y.
func (d Decimal) elementary(kind evalKind, other Decimal, ctx Context, budget Budget, op string) (Decimal, Conditions, error) {
	ev := newEvaluator(budget)
	return ev.elementary(kind, d, other, ctx, op)
}

// compareOne compares |x| with one, charging the digit scan an exact one
// needs.
func (ev *evaluator) compareOne(x Decimal) int {
	if x.isZero() {
		return -1
	}
	v := coefficientViewOf(x)
	digits, _ := arithmeticDigits(&v)
	adj := int64(x.exponent()) + int64(digits) - 1
	switch {
	case adj < 0:
		return -1
	case adj > 0:
		return 1
	}
	if !ev.charge(digits) {
		return 0
	}
	if quantizeDigit(&v, digits-1) != 1 {
		return 1
	}
	for pos := digits - 1; pos > 0; pos-- {
		if quantizeDigit(&v, pos-1) != 0 {
			return 1
		}
	}
	return 0
}

func (ev *evaluator) elementary(kind evalKind, x, other Decimal, ctx Context, op string) (Decimal, Conditions, error) {
	// Header-only domain facts first, then the charged comparison with one.
	switch kind {
	case evalAtan2:
		if x.isZero() && other.isZero() {
			return contextFailure(op, ErrInvalidOperation)
		}
	case evalAcosh:
		if x.negative() || x.isZero() {
			return contextFailure(op, ErrInvalidOperation)
		}
	}
	c := 0
	switch kind {
	case evalAsin, evalAcos, evalAtanh, evalAcosh:
		c = ev.compareOne(x)
		if !ev.ok() {
			return ev.failure(op)
		}
	}
	switch {
	case (kind == evalAsin || kind == evalAcos) && c > 0,
		kind == evalAtanh && c > 0,
		kind == evalAcosh && (c < 0 || x.negative()):
		return contextFailure(op, ErrInvalidOperation)
	case kind == evalAtanh && c == 0:
		return contextFailure(op, ErrDivisionByZero)
	}
	// Exact cases, at exponent 0.
	switch kind {
	case evalCos, evalCosh:
		if x.isZero() {
			one := [2]uint32{1}
			return ev.finishExact(one[:1], 0, 0, false, &ctx, op)
		}
	case evalAcos, evalAcosh:
		if c == 0 && !x.negative() {
			return ev.finishZero(op)
		}
	case evalAtan2:
		if x.isZero() && !other.negative() {
			return ev.finishZero(op)
		}
	default:
		if x.isZero() {
			return ev.finishZero(op)
		}
	}
	if ctx.precision == 0 {
		return Decimal{}, 0, conditionError(op, Inexact, elementaryRemedy(kind))
	}
	if ctx.rounding == Exact {
		return contextExactRefusal(op)
	}
	pr := evalProblem{kind: kind}
	pr.x.load(x)
	pr.xDigits, _ = arithmeticDigits(&pr.x)
	pr.xExp, pr.xNeg = int64(x.exponent()), x.negative() && !x.isZero()
	if kind == evalAtan2 {
		// The receiver is y; other is the point's x.
		pr.y, pr.yDigits, pr.yExp, pr.yNeg = pr.x, pr.xDigits, pr.xExp, pr.xNeg
		pr.x = coefficientView{}
		pr.x.load(other)
		pr.xDigits, _ = arithmeticDigits(&pr.x)
		pr.xExp, pr.xNeg = int64(other.exponent()), other.negative() && !other.isZero()
		if !ev.charge(uint64(pr.x.count + pr.y.count)) {
			return ev.failure(op)
		}
		pr.swap = x.Abs().Compare(other.Abs()) > 0
	}
	switch kind {
	case evalSinh, evalTanh, evalAsinh, evalAtanh, evalSin, evalTan, evalAtan, evalAsin:
		pr.neg = pr.xNeg // the sign of an out-of-range result
	}
	return ev.certify(&pr, &ctx, op)
}
