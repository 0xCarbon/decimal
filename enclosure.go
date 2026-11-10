// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
)

// The enclosure engine. A value is enclosed between two exact endpoints on
// admitted base-10⁹ limbs with a checked int64 limb exponent, far wider than
// Decimal's int32 exponent, so no virtual decimal gap is ever materialized.
// Every primitive rounds its exact result in a stated direction (toward +∞ or
// −∞), and every truncation and analytic tail is added outward, so an enclosure
// is a proof, never an estimate. A stage at w working digits is repeated at 2w
// until the enclosure certifies the context result: a proved sign, prefix and
// residual class against the half-quantum grid, handed to the shared round-once
// finisher. Every loop and allocation is charged to the one operation-local
// evaluationMeter before it runs.

// evalNum is the endpoint ±m·10^(9e): little-endian base-10⁹ limbs without
// a top zero limb (empty is zero) and a limb exponent e.
type evalNum struct {
	m   []uint32
	e   int64
	neg bool
}

// evalExponentLimit bounds limb exponents far beyond any certified result,
// whose adjusted exponents stay below 2^40, so exponent sums cannot wrap.
const evalExponentLimit = 1 << 58

// evalExact is a limb budget no exact integer here reaches, so primitives
// given it never round (math.MaxInt32 keeps it an int on 32-bit targets).
const evalExact = math.MaxInt32

func (x evalNum) isZero() bool { return len(x.m) == 0 }

// top is the limb exponent just above x's leading limb.
func (x evalNum) top() int64 { return x.e + int64(len(x.m)) }

func (x evalNum) view() coefficientView { return coefficientView{slow: x.m, count: len(x.m)} }

// adjusted is the decimal exponent of x's leading digit; x is nonzero.
func (x evalNum) adjusted() int64 {
	return 9*(x.top()-1) + int64(limbDigits(x.m[len(x.m)-1])) - 1
}

func (x evalNum) negate() evalNum {
	x.neg = !x.neg && !x.isZero()
	return x
}

// evaluator carries the shared meter and the first nonallocating failure.
// After a failure every primitive returns zero without work, so callers
// check ok at loop and stage boundaries only.
type evaluator struct {
	meter   evaluationMeter
	status  evaluationStatus
	stages  uint64 // working precisions tried, for the refinement tests
	objects uint64 // admitted arenas, for the allocation inventory test
}

func newEvaluator(budget Budget) evaluator {
	return evaluator{meter: newEvaluationMeter(budget)}
}

func (ev *evaluator) ok() bool { return ev.status.code == 0 }

func (ev *evaluator) fail(s evaluationStatus) {
	if ev.status.code == 0 {
		ev.status = s
	}
}

// broken records a violated internal invariant as a storage refusal, never
// as a numerical result.
func (ev *evaluator) broken() { ev.fail(evaluationStatus{code: ErrInsufficientStorage}) }

// charge admits one phase of at most a bounded steps before it runs.
func (ev *evaluator) charge(a uint64) bool {
	if ev.status.code != 0 {
		return false
	}
	if s := ev.meter.phase(a, 0); s.code != 0 {
		ev.status = s
		return false
	}
	return true
}

// chargeProduct admits a phase of x·y+z steps, checked.
func (ev *evaluator) chargeProduct(x, y, z uint64) bool {
	p, ok1 := arithmeticMul(x, y)
	a, ok2 := arithmeticAdd(p, z)
	if !ok1 || !ok2 {
		if ev.meter.budget.MaxWork != 0 {
			ev.fail(ev.meter.unitRefusal())
		} else {
			ev.broken()
		}
		return false
	}
	return ev.charge(a)
}

// evalArena is one admitted allocation carved into stage buffers. Its
// ticket is released when the stage ends; cumulative charges never are.
type evalArena struct {
	free   []uint32
	ticket evaluationAllocation
	owned  bool
}

func (ev *evaluator) arena(limbs uint64) evalArena {
	if !ev.ok() {
		return evalArena{}
	}
	// A finite quota is judged before addressability, so an arena no quota
	// can fund is a unit refusal on every target; admitObject then refuses
	// sizes beyond MaxInt, which keeps the make below indexable.
	bytes, ok := arithmeticMul(limbs, 4)
	if !ok {
		if ev.meter.budget.MaxWork != 0 {
			ev.fail(ev.meter.unitRefusal())
		} else {
			ev.fail(evaluationStatus{code: ErrInsufficientStorage})
		}
		return evalArena{}
	}
	ticket, s := ev.meter.admitObject(bytes)
	if s.code != 0 {
		ev.fail(s)
		return evalArena{}
	}
	ev.objects++
	return evalArena{free: make([]uint32, limbs), ticket: ticket, owned: true}
}

func (ev *evaluator) release(a *evalArena) {
	if a.owned {
		ev.meter.release(a.ticket)
		*a = evalArena{}
	}
}

// take carves n limbs; exhausting the planned arena is an invariant failure.
func (ev *evaluator) take(a *evalArena, n int) []uint32 {
	if !ev.ok() || n > len(a.free) {
		ev.broken()
		return nil
	}
	b := a.free[:n:n]
	a.free = a.free[n:]
	return b
}

// settle rounds the magnitude dst[:n]·10^(9e), plus a positive amount below
// its last limb when sticky, to at most L limbs toward +∞ (up) or −∞ for
// the sign neg. dst needs one limb beyond n for a carry.
func (ev *evaluator) settle(dst []uint32, n int, e int64, neg, sticky bool, L int, up bool) evalNum {
	// Trim, sticky scan, copy and carry each visit at most n limbs.
	if !ev.charge(4*uint64(n) + 1) {
		return evalNum{}
	}
	m := trimLimbs(dst[:n])
	away := up != neg
	if len(m) == 0 {
		if sticky && away {
			dst[0] = 1
			return ev.checked(evalNum{m: dst[:1], e: e, neg: neg})
		}
		return evalNum{}
	}
	if len(m) > L {
		drop := len(m) - L
		for _, limb := range m[:drop] {
			sticky = sticky || limb != 0
		}
		copy(dst, m[drop:])
		m = dst[:L]
		e += int64(drop)
	}
	if sticky && away {
		carry := true
		for i := range m {
			if m[i]++; uint64(m[i]) < decimalLimbBase {
				carry = false
				break
			}
			m[i] = 0
		}
		if carry {
			// Every retained limb was 10⁹−1: the value is one top limb.
			e += int64(len(m))
			dst[0] = 1
			m = dst[:1]
		}
	}
	return ev.checked(evalNum{m: m, e: e, neg: neg})
}

func (ev *evaluator) checked(x evalNum) evalNum {
	if x.e > evalExponentLimit || x.e < -evalExponentLimit {
		ev.broken()
		return evalNum{}
	}
	return x
}

// round encloses x in at most L limbs; dst holds min(len, L)+1 limbs.
func (ev *evaluator) round(dst []uint32, x evalNum, L int, up bool) evalNum {
	if !ev.charge(uint64(len(x.m))) || x.isZero() {
		return evalNum{}
	}
	keep := min(len(x.m), L)
	if keep+1 > cap(dst) {
		ev.broken()
		return evalNum{}
	}
	drop := len(x.m) - keep
	sticky := false
	for _, limb := range x.m[:drop] {
		sticky = sticky || limb != 0
	}
	copy(dst[:keep+1], x.m[drop:])
	return ev.settle(dst[:keep+1], keep, x.e+int64(drop), x.neg, sticky, L, up)
}

// add encloses a+b in at most L limbs. Operand limbs below the window of
// cap(dst)−2 limbs under the higher top are folded into directed unit
// corrections, so a far smaller operand never widens the work.
func (ev *evaluator) add(dst []uint32, a, b evalNum, L int, up bool) evalNum {
	if evalAliases(dst, a) || evalAliases(dst, b) {
		ev.broken()
		return evalNum{}
	}
	if a.isZero() {
		return ev.round(dst, b, L, up)
	}
	if b.isZero() {
		return ev.round(dst, a, L, up)
	}
	top := max(a.top(), b.top())
	bottom := max(min(a.e, b.e), top-int64(cap(dst)-2))
	span := int(top - bottom)
	if span < 1 || span+2 > cap(dst) {
		ev.broken()
		return evalNum{}
	}
	if !ev.charge(uint64(len(a.m)+len(b.m)) + 4*uint64(span+1)) {
		return evalNum{}
	}
	out := dst[:span+1]
	clear(out)
	stickyA := evalPlace(out, a, bottom)
	neg := a.neg
	if a.neg == b.neg {
		evalAccumulate(out, b, bottom, false)
	} else if evalAccumulate(out, b, bottom, true) {
		evalNegate(out)
		neg = !neg
	}
	stickyB := evalSticky(b, bottom)
	// T − V = sign(a)·δa + sign(b)·δb with 0 ≤ δ < 1 unit: toward +∞ add a
	// unit per positive truncated operand, toward −∞ subtract one per
	// negative truncated operand.
	var c int
	if up {
		c = evalUnit(stickyA && !a.neg) + evalUnit(stickyB && !b.neg)
	} else {
		c = -evalUnit(stickyA && a.neg) - evalUnit(stickyB && b.neg)
	}
	neg = evalAddUnits(out, neg, c)
	return ev.settle(dst, span+1, bottom, neg, false, L, up)
}

func evalUnit(b bool) int {
	if b {
		return 1
	}
	return 0
}

// evalPlace writes |x|'s limbs at or above bottom into out and reports
// whether a nonzero limb lies below it.
func evalPlace(out []uint32, x evalNum, bottom int64) bool {
	from := max(int64(0), bottom-x.e)
	for i := from; i < int64(len(x.m)); i++ {
		out[x.e+i-bottom] = x.m[i]
	}
	return evalSticky(x, bottom)
}

func evalSticky(x evalNum, bottom int64) bool {
	below := min(max(int64(0), bottom-x.e), int64(len(x.m)))
	for _, limb := range x.m[:below] {
		if limb != 0 {
			return true
		}
	}
	return false
}

// evalAccumulate adds (or subtracts) |x|'s limbs at or above bottom into
// out and reports a final borrow, which leaves out = B^len − |result|.
func evalAccumulate(out []uint32, x evalNum, bottom int64, subtract bool) bool {
	from := max(int64(0), bottom-x.e)
	var carry uint64
	i := x.e + from - bottom
	for j := from; j < int64(len(x.m)); j, i = j+1, i+1 {
		if subtract {
			v := uint64(out[i]) + decimalLimbBase - uint64(x.m[j]) - carry
			out[i], carry = uint32(v%decimalLimbBase), 1-v/decimalLimbBase
		} else {
			v := uint64(out[i]) + uint64(x.m[j]) + carry
			out[i], carry = uint32(v%decimalLimbBase), v/decimalLimbBase
		}
	}
	for ; carry != 0 && i < int64(len(out)); i++ {
		if subtract {
			v := uint64(out[i]) + decimalLimbBase - carry
			out[i], carry = uint32(v%decimalLimbBase), 1-v/decimalLimbBase
		} else {
			v := uint64(out[i]) + carry
			out[i], carry = uint32(v%decimalLimbBase), v/decimalLimbBase
		}
	}
	return carry != 0
}

// evalNegate replaces the base-10⁹ complement out with its magnitude.
func evalNegate(out []uint32) {
	carry := uint64(1)
	for i := range out {
		v := decimalLimbBase - 1 - uint64(out[i]) + carry
		out[i], carry = uint32(v%decimalLimbBase), v/decimalLimbBase
	}
}

// evalAddUnits adds c ∈ [−2, 2] units to the signed magnitude out, which
// has a spare top limb, and returns the new sign.
func evalAddUnits(out []uint32, neg bool, c int) bool {
	if c == 0 {
		return neg
	}
	mag := trimLimbs(out)
	units := uint64(c)
	if c < 0 {
		units = uint64(-c)
	}
	switch {
	case len(mag) == 0:
		out[0] = uint32(units)
		return c < 0
	case (c > 0) != neg:
		carry := units
		for i := 0; carry != 0; i++ {
			v := uint64(out[i]) + carry
			out[i], carry = uint32(v%decimalLimbBase), v/decimalLimbBase
		}
		return neg
	case len(mag) == 1 && uint64(mag[0]) < units:
		out[0] = uint32(units - uint64(mag[0]))
		return !neg
	default:
		borrow := units
		for i := 0; borrow != 0; i++ {
			v := uint64(out[i]) + decimalLimbBase - borrow
			out[i], borrow = uint32(v%decimalLimbBase), 1-v/decimalLimbBase
		}
		return neg
	}
}

// mul encloses a·b in at most L limbs; dst holds len(a)+len(b)+1 limbs.
func (ev *evaluator) mul(dst []uint32, a, b evalNum, L int, up bool) evalNum {
	if a.isZero() || b.isZero() {
		return evalNum{}
	}
	n := len(a.m) + len(b.m)
	if n+1 > cap(dst) || evalAliases(dst, a) || evalAliases(dst, b) {
		ev.broken()
		return evalNum{}
	}
	if !ev.chargeProduct(uint64(len(a.m)), uint64(len(b.m)), uint64(2*n)) {
		return evalNum{}
	}
	out := dst[:n]
	clear(out)
	av, bv := a.view(), b.view()
	if !fillMultiply(out, &av, &bv) {
		ev.broken()
		return evalNum{}
	}
	return ev.settle(dst, n, a.e+b.e, a.neg != b.neg, false, L, up)
}

// evalAliases reports that x's limbs live in dst's buffer. Stage buffers
// are carved with their own capacity, so a shared final element identifies
// a shared buffer; add and mul clear dst before reading their operands.
func evalAliases(dst []uint32, x evalNum) bool {
	if cap(dst) == 0 || cap(x.m) == 0 {
		return false
	}
	return &dst[:cap(dst)][cap(dst)-1] == &x.m[:cap(x.m)][cap(x.m)-1]
}

// divSmall encloses a/d for 0 < d < 2^32 in at most L limbs; dst holds
// max(len(a), L+1)+1 limbs and may alias a.
func (ev *evaluator) divSmall(dst []uint32, a evalNum, d uint64, L int, up bool) evalNum {
	if a.isZero() {
		return evalNum{}
	}
	ext := max(0, L+1-len(a.m))
	n := len(a.m) + ext
	if d == 0 || d >= 1<<32 || n+1 > cap(dst) {
		ev.broken()
		return evalNum{}
	}
	if !ev.charge(uint64(n)) {
		return evalNum{}
	}
	var r uint64
	for i := n - 1; i >= 0; i-- {
		cur := r * decimalLimbBase
		if i >= ext {
			cur += uint64(a.m[i-ext])
		}
		dst[i], r = uint32(cur/d), cur%d
	}
	return ev.settle(dst, n, a.e-int64(ext), a.neg, r != 0, L, up)
}

// divPair encloses a/(p·q) for a ≥ 0 and factors below 2^32: in one
// division while the product is below 2^32, otherwise in two, both rounded
// toward the same side, the first with a spare limb so that the pair stays
// within two units of the last. dst holds max(len(a), L+2)+1 limbs. The
// series divisors (2j−1)(2j) pass 2^32 at term 32768, which a precision of
// some 300,000 digits reaches.
func (ev *evaluator) divPair(dst []uint32, a evalNum, p, q uint64, L int, up bool) evalNum {
	if d := p * q; d < 1<<32 {
		return ev.divSmall(dst, a, d, L, up)
	}
	return ev.divSmall(dst, ev.divSmall(dst, a, p, L+1, up), q, L, up)
}

// div encloses a/b in at most L limbs by Knuth division of a numerator of
// len(b)+L+1 limbs; a longer a is truncated into the sticky remainder. dst
// holds L+3 limbs and scratch 2·len(b)+L+2.
func (ev *evaluator) div(dst, scratch []uint32, a, b evalNum, L int, up bool) evalNum {
	if b.isZero() {
		ev.broken()
		return evalNum{}
	}
	if a.isZero() {
		return evalNum{}
	}
	vn := len(b.m)
	un := vn + L + 1
	if L+3 > cap(dst) || un+1+vn > cap(scratch) {
		ev.broken()
		return evalNum{}
	}
	if !ev.chargeProduct(uint64(L+2), uint64(2*vn+2), uint64(4*un+2*vn+len(a.m))) {
		return evalNum{}
	}
	u, v := scratch[:un+1], scratch[un+1:un+1+vn]
	clear(u)
	shift := un - len(a.m)
	sticky := false
	if shift >= 0 {
		copy(u[shift:], a.m)
	} else {
		for _, limb := range a.m[:-shift] {
			sticky = sticky || limb != 0
		}
		copy(u, a.m[-shift:])
	}
	copy(v, b.m)
	q, remZero := divideLimbs(u, un, v, dst[:un-vn+1], nil)
	return ev.settle(dst, len(q), a.e-int64(shift)-b.e, a.neg != b.neg, sticky || !remZero, L, up)
}

// load encloses ±C·10^e10 in at most L limbs, reading only C's top limbs
// and scanning the rest for a nonzero digit.
func (ev *evaluator) load(dst []uint32, v *coefficientView, digits uint64, e10 int64, neg bool, L int, up bool) evalNum {
	if v.count == 0 {
		return evalNum{}
	}
	q := e10 / 9
	if e10%9 < 0 {
		q--
	}
	shift := uint64(e10 - 9*q)
	total := int((digits + shift + 8) / 9)
	keep := min(total, L)
	low := total - keep
	if keep+1 > cap(dst) {
		ev.broken()
		return evalNum{}
	}
	if !ev.charge(uint64(total)) {
		return evalNum{}
	}
	for i := range keep {
		dst[i] = alignedLimb(v, shift, uint64(low+i))
	}
	sticky := false
	for j := 0; j < low && !sticky; j++ {
		sticky = alignedLimb(v, shift, uint64(j)) != 0
	}
	return ev.settle(dst, keep, q+int64(low), neg, sticky, L, up)
}

// evalSmall writes k into buf (three limbs) as an exact endpoint.
func evalSmall(buf []uint32, k uint64, neg bool) evalNum {
	n := 0
	for ; k != 0; n++ {
		buf[n] = uint32(k % decimalLimbBase)
		k /= decimalLimbBase
	}
	return evalNum{m: buf[:n], neg: neg && n > 0}
}

// scale multiplies x by 10^k exactly: a limb shift and a one-limb factor.
// dst holds len(x)+2 limbs.
func (ev *evaluator) scale(dst []uint32, x evalNum, k int64) evalNum {
	q := k / 9
	if k%9 < 0 {
		q--
	}
	var f [3]uint32
	y := ev.mul(dst, x, evalSmall(f[:], uint64(decimalPowers[k-9*q]), false), len(x.m)+1, false)
	if y.isZero() {
		return y
	}
	y.e += q
	return ev.checked(y)
}

// cmpMag compares |a| and |b|; the caller charges max(len) steps.
func cmpMag(a, b evalNum) int {
	switch {
	case a.isZero() && b.isZero():
		return 0
	case a.isZero():
		return -1
	case b.isZero():
		return 1
	case a.top() != b.top():
		if a.top() < b.top() {
			return -1
		}
		return 1
	}
	for i := a.top() - 1; i >= min(a.e, b.e); i-- {
		var x, y uint32
		if i >= a.e {
			x = a.m[i-a.e]
		}
		if i >= b.e {
			y = b.m[i-b.e]
		}
		if x != y {
			if x < y {
				return -1
			}
			return 1
		}
	}
	return 0
}

// cut writes ⌊|x|/10^t⌋ into dst, with a spare zero limb beyond it for the
// finisher's carry, and classifies the fraction against one half.
func (ev *evaluator) cut(dst []uint32, x evalNum, t int64) ([]uint32, divHalf) {
	shift := 9*x.e - t
	if shift >= 0 {
		digits := limbsDigits(x.m) + uint64(shift)
		c := int((digits + 8) / 9)
		if c+1 > cap(dst) {
			ev.broken()
			return nil, divExactClass
		}
		if !ev.charge(uint64(c)) {
			return nil, divExactClass
		}
		v := x.view()
		for i := range c {
			dst[i] = alignedLimb(&v, uint64(shift), uint64(i))
		}
		dst[c] = 0
		return dst[:c], divExactClass
	}
	if len(x.m)+1 > cap(dst) {
		ev.broken()
		return nil, divExactClass
	}
	if !ev.charge(2 * uint64(len(x.m))) {
		return nil, divExactClass
	}
	copy(dst, x.m)
	dst[len(x.m)] = 0
	return dropDigits(dst[:len(x.m)], divExactClass, uint64(-shift))
}

// classify certifies the finisher input for a value v known to lie in
// [lo, hi] and to differ from every finite decimal of at most p+3
// significant digits, hence from every grid point and midpoint the finisher
// can see. It returns the prefix ⌊|v|/10^t′⌋ at t′ = adj(|lo|)−p (raised to
// Etiny), the class of v's fraction and v's sign, or false while the
// enclosure straddles zero, a power of ten or a half-quantum boundary. ra
// and rb each hold the prefix and a carry limb.
func (ev *evaluator) classify(lo, hi evalNum, ctx *Context, etiny int64, ra, rb []uint32) (r []uint32, tPrime int64, class divHalf, neg, ok bool) {
	if !ev.charge(uint64(len(lo.m) + len(hi.m))) {
		return nil, 0, 0, false, false
	}
	if evalCmp(lo, hi) > 0 {
		ev.broken() // an inverted enclosure is a defect: fail closed, never refine it
		return nil, 0, 0, false, false
	}
	if lo.isZero() || hi.isZero() || lo.neg != hi.neg {
		return nil, 0, 0, false, false
	}
	a, b := lo, hi
	if lo.neg {
		a, b = hi, lo
	}
	adjA, adjB := a.adjusted(), b.adjusted()
	if adjB > adjA+1 {
		return nil, 0, 0, false, false
	}
	tPrime = adjA - int64(ctx.precision)
	if ctx.guarded {
		tPrime = max(tPrime, etiny)
	}
	pa, ca := ev.cut(ra, a, tPrime)
	pb, cb := ev.cut(rb, b, tPrime)
	if !ev.ok() || !ev.charge(uint64(len(pa))) {
		return nil, 0, 0, false, false
	}
	upperA := ca == divHalfClass || ca == divAbove
	same := evalLimbsEqual(pa, pb)
	switch {
	case same && upperA == (cb == divHalfClass || cb == divAbove):
	case same && !upperA && cb == divHalfClass:
		// hi is the midpoint itself and v differs from it: v is below it.
	case upperA && cb == divExactClass && evalLimbsSuccessor(pa, pb):
		// hi is the next grid point and v differs from it: v is below it.
	default:
		return nil, 0, 0, false, false
	}
	class = divBelow
	if upperA {
		class = divAbove
	}
	return pa, tPrime, class, lo.neg, true
}

func evalLimbsEqual(a, b []uint32) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// evalLimbsSuccessor reports b = a+1 for trimmed limbs.
func evalLimbsSuccessor(a, b []uint32) bool {
	i := 0
	for i < len(a) && uint64(a[i]) == decimalLimbBase-1 {
		if i >= len(b) || b[i] != 0 {
			return false
		}
		i++
	}
	if i == len(a) {
		return len(b) == i+1 && b[i] == 1
	}
	if len(b) != len(a) || b[i] != a[i]+1 {
		return false
	}
	return evalLimbsEqual(a[i+1:], b[i+1:])
}

// finish rounds a certified prefix once through the shared round-once core and
// publishes it under the evaluation meter.
func (ev *evaluator) finish(r []uint32, class divHalf, tPrime, etiny, ideal int64, neg bool, ctx *Context, op string) (Decimal, Conditions, error) {
	if !ev.charge(2*uint64(len(r)) + 4) {
		return ev.failure(op)
	}
	out, verdict := roundContext(r, class, tPrime, etiny, ideal, neg, ctx)
	switch verdict {
	case contextOverflows:
		return ev.overflow(neg, ctx, op)
	case contextRefusesExact:
		return contextExactRefusal(op)
	case contextBroken:
		ev.broken()
		return ev.failure(op)
	}
	result := ev.publish(out.r, out.exponent, neg)
	if !ev.ok() {
		return ev.failure(op)
	}
	return contextOutcome(result, out.events, ctx.traps, op)
}

// finishZero publishes an exact zero at exponent 0 without guard handling,
// as every exact-zero result of the context arithmetic does.
func (ev *evaluator) finishZero(op string) (Decimal, Conditions, error) {
	result := ev.publish(nil, 0, false)
	if !ev.ok() {
		return ev.failure(op)
	}
	return result, 0, nil
}

// overflow publishes the largest finite p-digit value, as contextOverflow.
func (ev *evaluator) overflow(neg bool, ctx *Context, op string) (Decimal, Conditions, error) {
	n := uint64(ctx.precision)
	count := int((n + 8) / 9)
	a := ev.arena(uint64(count) + 1)
	defer ev.release(&a)
	out := ev.take(&a, count)
	if !ev.ok() || !ev.charge(uint64(count)) {
		return ev.failure(op)
	}
	for i := range out {
		out[i] = uint32(decimalLimbBase - 1)
	}
	if width := 1 + (n-1)%9; width < 9 {
		out[count-1] = decimalPowers[width] - 1
	}
	result := ev.publish(out, int64(ctx.guards.Emax)-int64(n)+1, neg)
	if !ev.ok() {
		return ev.failure(op)
	}
	events := Overflow | Inexact | Rounded | roundingDirection(false, neg)
	return contextOutcome(result, events, ctx.traps, op)
}

// publish admits and publishes a finished coefficient: stored exponent,
// digit quota, one charged write pass with the holder's allocator
// envelope, then physical addressability of the holder.
func (ev *evaluator) publish(r []uint32, exponent int64, neg bool) Decimal {
	if !ev.ok() {
		return Decimal{}
	}
	if exponent < math.MinInt32 || exponent > math.MaxInt32 {
		ev.fail(evaluationStatus{code: ErrExponentRange})
		return Decimal{}
	}
	r = trimLimbs(r)
	n := max(limbsDigits(r), 1)
	if s := ev.meter.resultDigits(n); s.code != 0 {
		ev.fail(s)
		return Decimal{}
	}
	var tally costTally
	heap := publishBytes(&tally, n, uint64(len(r)))
	if tally.overflow {
		ev.fail(evaluationStatus{code: ErrInsufficientStorage})
		return Decimal{}
	}
	if s := ev.meter.phase(n, heap); s.code != 0 {
		ev.fail(s)
		return Decimal{}
	}
	if heap != 0 {
		if s := ev.meter.physical(uint64(len(r))*4 + holderBytes); s.code != 0 {
			ev.fail(s)
			return Decimal{}
		}
	}
	if len(r) == 0 {
		return zeroDecimal(int32(exponent))
	}
	if n <= 38 {
		return publishInlineArithmetic(r, int32(exponent), neg)
	}
	return publishScratch(r, int32(exponent), neg)
}

// failure builds the one outer error from the retained status.
func (ev *evaluator) failure(op string) (Decimal, Conditions, error) {
	if ev.status.code == 0 {
		ev.broken()
	}
	return Decimal{}, 0, evaluationFailure(op, ev.status)
}

// evalLimbs is ⌈w/9⌉, at least one.
func evalLimbs(digits uint64) int {
	return int(max(1, (digits+8)/9))
}

// evalUint returns |x| when it is an integer below 2^64.
func evalUint(x evalNum) (uint64, bool) {
	if x.isZero() {
		return 0, true
	}
	if x.e < 0 || x.top() > 3 {
		return 0, false
	}
	var v uint64
	for i := x.top() - 1; i >= 0; i-- {
		var limb uint64
		if i >= x.e {
			limb = uint64(x.m[i-x.e])
		}
		hi, lo := bits.Mul64(v, decimalLimbBase)
		lo, carry := bits.Add64(lo, limb, 0)
		if hi != 0 || carry != 0 {
			return 0, false
		}
		v = lo
	}
	return v, true
}
