// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
	"slices"
)

// Sqrt is exact-then-round: the integer root r = ⌊√N⌋ of the scaled coefficient
// N is computed exactly, in machine words when N fits 256 bits and by integer
// Newton on base-10⁹ limbs otherwise, and the rounding class of the true root
// against r is decided exactly from the remainder N − r² (and the dropped
// input digits), never from an approximation. The context finisher then rounds
// once in the context's mode.

const sqrtRemedy = "non-terminating square root: supply a finite-precision context (SqrtWithContext)"

// Sqrt returns the exact square root at the ideal exponent ⌊e/2⌋: √4 is 2
// and √0.25 is 0.5. A root that is not a finite decimal, such as √2,
// returns a *Error with Condition Inexact and a remedy naming
// SqrtWithContext, never a silently rounded value. A negative nonzero
// operand returns ErrInvalidOperation; zero returns an unsigned zero at
// ⌊e/2⌋.
func (d Decimal) Sqrt() (Decimal, error) {
	result, _, err := d.sqrtUnlimited(limits{}, "Sqrt", nil)
	return result, err
}

// SqrtWithContext rounds the square root once to the context precision in
// the context's mode, with guards and traps. An exact root keeps the
// exponent nearest ⌊e/2⌋ that fits the precision; one that needs a higher
// exponent reports Rounded but not Inexact, which Exact permits: √1E+10 at
// precision 3 is 1.00E+5. A negative nonzero operand returns
// ErrInvalidOperation in every mode. Context{} behaves as Sqrt.
func (d Decimal) SqrtWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.sqrtContext(ctx, ctx.arith, "SqrtWithContext", nil)
}

// sqrtCount records work units, the Newton iterations from the float seed
// and the most iterations any seeded level ran, for the counted-loop tests.
// Production calls pass nil.
type sqrtCount struct {
	work       divCount
	iterations uint64
	levelSteps uint64
}

func (c *sqrtCount) divCounter() *divCount {
	if c == nil {
		return nil
	}
	return &c.work
}

// sqrtIterations is the planned Newton count max(1, ⌈log2(R/15)⌉) + 3
// for an R-digit root started from the float seed. The charge plans every
// one at full width; a root that sqrtNewton seeds from its top half does
// less work than planned.
func sqrtIterations(r uint64) uint64 {
	j := uint64(0)
	for j < 60 && uint64(15)<<j < r {
		j++
	}
	return max(1, j) + 3
}

// sqrtCharge is the precharge B = n + I(r)·D(2r, r) + t(r)² for an input
// of n digits and a planned root of r digits, where D is the Div family's
// charge for dividing a 2r-digit numerator by an r-digit divisor.
func sqrtCharge(n, r uint64) (uint64, bool) {
	s := divSource{dx: 2 * r, dy: r}
	p := s.plan(0)
	loop, ok1 := arithmeticMul(sqrtIterations(r), p.charge)
	t := 1 + (r-1)/9
	square, ok2 := arithmeticMul(t, t)
	total, ok3 := checkedSum(n, loop, square)
	return total, p.ok && r <= math.MaxUint64/4 && ok1 && ok2 && ok3
}

// sqrtLayout sizes the scratch for an s-digit N with an r-digit root, in
// limbs: N with the limb the shifted build may write, the division
// numerator (which also holds r² and N − r²), and two buffers that
// alternate as the current root and the next quotient. A root of one limb
// has N of at most two, so w also holds the one-limb divisor's quotient.
type sqrtLayout struct {
	n, u, w uint64
}

func newSqrtLayout(s, r uint64) sqrtLayout {
	tn, tr := 1+(s-1)/9, 1+(r-1)/9
	return sqrtLayout{
		n: tn + 1,
		u: max(tn+1, tr+2, 2*tr),
		w: max(tn-tr+1, tr+2),
	}
}

func (l sqrtLayout) total() (uint64, bool) {
	twice, ok1 := arithmeticMul(l.w, 2)
	total, ok2 := checkedSum(l.n, l.u, twice)
	return total, ok1 && ok2
}

// sqrtStackLimbs holds the scratch of every root of up to 82 digits, so a
// result of at most 81 digits allocates only its published holder.
const sqrtStackLimbs = 64

// sqrtScratch returns the plan's scratch, from the caller's stack array
// when it fits, after physical admission of the heap plan and a result of
// resultDigits digits.
func sqrtScratch(stack *[sqrtStackLimbs]uint32, l sqrtLayout, resultDigits uint64) ([]uint32, bool) {
	total, ok := l.total()
	if !ok || !divAdmitted(total, resultDigits) {
		return nil, false
	}
	if total <= sqrtStackLimbs {
		return stack[:total], true
	}
	return make([]uint32, total), true
}

// sqrtPlan is the scaled problem: the root of N = C·10^k (k ≥ 0), or of
// ⌊C/10^−k⌋ with the dropped digits read for the class (k < 0), whose
// s-digit value has an r-digit integer root.
type sqrtPlan struct {
	k    int64
	s, r uint64
}

func newSqrtPlan(dx uint64, k int64) sqrtPlan {
	p := sqrtPlan{k: k}
	if k < 0 && uint64(-k) >= dx {
		return p // every digit is dropped: N = 0
	}
	if k >= 0 {
		p.s = dx + uint64(k)
	} else {
		p.s = dx - uint64(-k)
	}
	p.r = (p.s + 1) / 2
	return p
}

// sqrtDigits returns r = ⌊√X⌋ for the scaled value X of the plan, and the
// class of √X − r against one half, decided exactly. With N = ⌊X⌋, δ =
// X − N and rem = N − r²: rem < r gives below (exact when rem = 0 and
// δ = 0), rem > r gives above, and rem = r compares δ with 1/4, since
// (r + 1/2)² = r² + r + 1/4. scratch must hold the plan's layout; r keeps
// a spare zero limb for the finisher's rounding carry.
func sqrtDigits(v *coefficientView, dx uint64, p sqrtPlan, scratch []uint32, c *sqrtCount) ([]uint32, divHalf) {
	dc := c.divCounter()
	dc.add(dx)
	tailNonzero, tailCmp := false, -1
	if p.k < 0 {
		tailNonzero, tailCmp = sqrtTail(v, uint64(-p.k))
	}
	if p.s == 0 {
		// X = δ < 1: r = 0 and rem = r.
		return scratch[:0], sqrtTieClass(tailCmp)
	}
	l := newSqrtLayout(p.s, p.r)
	n := scratch[:l.n:l.n]
	u := scratch[l.n : l.n+l.u : l.n+l.u]
	xb := scratch[l.n+l.u : l.n+l.u+l.w : l.n+l.u+l.w]
	qb := scratch[l.n+l.u+l.w : l.n+l.u+2*l.w : l.n+l.u+2*l.w]
	src := divSource{x: *v}
	un := src.buildNumerator(divPlan{k: p.k}, n, nil)
	nl := trimLimbs(n[:un])
	r := sqrtNewton(nl, p.r, u, xb, qb, c)
	// rem = N − r², in u.
	clear(u)
	rv := coefficientView{slow: r, count: len(r)}
	fillMultiply(u[:2*len(r)], &rv, &rv)
	var borrow int64
	for i := range nl {
		t := int64(nl[i]) - int64(u[i]) - borrow
		borrow = 0
		if t < 0 {
			t += int64(decimalLimbBase)
			borrow = 1
		}
		u[i] = uint32(t)
	}
	dc.add(uint64(len(r)*len(r) + len(nl)))
	rem := trimLimbs(u[:len(nl)])
	var class divHalf
	switch cmp := compareLimbs(rem, &rv); {
	case cmp < 0 && len(rem) == 0 && !tailNonzero:
		class = divExactClass
	case cmp < 0:
		class = divBelow
	case cmp > 0:
		class = divAbove
	default:
		class = sqrtTieClass(tailCmp)
	}
	dc.add(uint64(len(r)))
	// The root buffer's tail is zero for the finisher's carry.
	full := r[:cap(r)]
	clear(full[len(r):])
	return r, class
}

// sqrtTieClass classifies √X against r + 1/2 when rem = r, from the sign
// of δ − 1/4.
func sqrtTieClass(tailCmp int) divHalf {
	switch {
	case tailCmp < 0:
		return divBelow
	case tailCmp == 0:
		return divHalfClass
	default:
		return divAbove
	}
}

// sqrtTail reads the j ≥ 1 dropped low digits of C as the fraction δ =
// (C mod 10^j)/10^j: whether it is nonzero, and the sign of δ − 1/4 from
// its first two digits and the sticky rest.
func sqrtTail(v *coefficientView, j uint64) (nonzero bool, cmp int) {
	top := quantizeDigit(v, j-1) * 10
	if j >= 2 {
		top += quantizeDigit(v, j-2)
	}
	rest := false
	if j >= 3 {
		below := j - 2 // digits at positions [0, below)
		whole, part := below/9, below%9
		for i := uint64(0); i < whole && i < uint64(v.count) && !rest; i++ {
			rest = v.limb(int(i)) != 0
		}
		if !rest && part != 0 && whole < uint64(v.count) {
			rest = v.limb(int(whole))%decimalPowers[part] != 0
		}
	}
	nonzero = top != 0 || rest
	switch {
	case top < 25:
		cmp = -1
	case top > 25 || rest:
		cmp = 1
	}
	return nonzero, cmp
}

// sqrtLevelLimbs is the root length, in limbs, from which sqrtNewton seeds
// a root from the root of the operand's top half.
const sqrtLevelLimbs = 8

// sqrtNewton returns ⌊√N⌋ for a nonzero trimmed N whose root has rootDigits
// digits, in xb or qb. Newton's iteration x ← ⌊(x + ⌊N/x⌋)/2⌋ from a seed
// x₀ ≥ ⌊√N⌋ decreases monotonically to ⌊√N⌋ and stops at the first step
// that does not decrease.
//
// A root of fewer than sqrtLevelLimbs limbs starts from sqrtSeed. A longer
// root of t limbs first takes s = ⌊√⌊N/B^2m⌋⌋ for m = ⌊(t−2)/2⌋ and
// B = 10^9, by the same rule, and starts from x₀ = (s+1)·B^m. Since
// (s+1)² > ⌊N/B^2m⌋, x₀ > √N; and x₀ − √N ≤ B^m, so one step leaves an
// error of at most B^2m/(2√N) ≤ 1/(2B): the level ends within three steps,
// the last of which only confirms. The divisions therefore shrink
// geometrically below the full width instead of repeating at it.
func sqrtNewton(n []uint32, rootDigits uint64, u, xb, qb []uint32, c *sqrtCount) []uint32 {
	var drops [64]int // the m of each level, outermost first
	levels, low := 0, 0
	for {
		t := (len(n) - low + 1) / 2
		if t < sqrtLevelLimbs {
			break
		}
		m := (t - 2) / 2
		drops[levels] = m
		levels++
		low += 2 * m
	}
	top := n[low:]
	if levels > 0 {
		rootDigits = (limbsDigits(top) + 1) / 2
	}
	x := sqrtSeed(top, rootDigits, xb)
	x, xb, qb, steps := sqrtDescend(top, x, u, xb, qb, c.divCounter())
	if c != nil {
		c.iterations = steps
	}
	for i := levels - 1; i >= 0; i-- {
		m := drops[i]
		low -= 2 * m
		// x₀ = (s+1)·B^m, built in place: xb is zero beyond x.
		size := len(x)
		copy(xb[m:], x)
		clear(xb[:m])
		xb[m+size] = 0
		for k := m; ; k++ {
			if xb[k]++; uint64(xb[k]) < decimalLimbBase {
				break
			}
			xb[k] = 0
		}
		x, xb, qb, steps = sqrtDescend(n[low:], trimLimbs(xb[:m+size+1]), u, xb, qb, c.divCounter())
		if c != nil {
			c.levelSteps = max(c.levelSteps, steps)
		}
	}
	return x
}

// sqrtDescend runs Newton's iteration on N from x ≥ ⌊√N⌋, held in xb, and
// returns ⌊√N⌋ with its buffer, the spare one and the steps taken.
func sqrtDescend(n, x, u, xb, qb []uint32, dc *divCount) (root, held, spare []uint32, steps uint64) {
	for {
		steps++
		vn := len(x)
		work := u[:max(len(n), vn)+1]
		clear(work)
		copy(work, n)
		q, _ := divideLimbs(work, len(n), x, qb, dc)
		y := sqrtAverage(qb, x, q)
		dc.add(uint64(len(n) + 2*(max(len(x), len(q))+1)))
		if sqrtCompare(y, x) >= 0 {
			return x, xb, qb, steps
		}
		xb, qb = qb, xb
		x = y
	}
}

// sqrtAverage writes ⌊(x + q)/2⌋ into dst, which may alias q and has a limb
// beyond both operands.
func sqrtAverage(dst, x, q []uint32) []uint32 {
	n := max(len(x), len(q))
	var carry uint64
	for i := range n {
		s := carry
		if i < len(x) {
			s += uint64(x[i])
		}
		if i < len(q) {
			s += uint64(q[i])
		}
		dst[i] = uint32(s % decimalLimbBase)
		carry = s / decimalLimbBase
	}
	dst[n] = uint32(carry)
	var rem uint64
	for i := n; i >= 0; i-- {
		cur := rem*decimalLimbBase + uint64(dst[i])
		dst[i] = uint32(cur / 2)
		rem = cur % 2
	}
	clear(dst[n+1:])
	return trimLimbs(dst[:n+1])
}

// sqrtCompare compares two trimmed limb slices.
func sqrtCompare(a, b []uint32) int {
	if len(a) != len(b) {
		if len(a) < len(b) {
			return -1
		}
		return 1
	}
	for i := range slices.Backward(a) {
		if a[i] != b[i] {
			if a[i] < b[i] {
				return -1
			}
			return 1
		}
	}
	return 0
}

// sqrtSeed writes x₀ = lead·10^z ≥ ⌊√N⌋ into xb. lead = ⌊g·(1+2·10⁻¹⁵)⌋
// has L = min(R, 17) digits, with g a float64 root of N's leading three
// limbs scaled by 10^−z. g's relative error, below 6·10⁻¹⁶ from the float
// operations and 10⁻¹⁸ from the truncated limbs, is covered by the margin,
// so g·(1+2·10⁻¹⁵) > √N·10^−z: its floor is at least ⌊√N⌋ when z = 0, and
// exceeds √N·10^−z ≥ 10¹⁶ by more than one when z > 0. x₀ then exceeds √N
// by less than 2.8·10⁻¹⁵ relative, and Newton's quadratic convergence
// needs at most ⌈log2((R+0.3)/14.86)⌉ + 2 ≤ max(1, ⌈log2(R/15)⌉) + 3 steps
// (TestSqrtCountedWorkWithinTariff). The compiler may fuse the float
// expressions into FMADD (arm64), which rounds less and only tightens the
// error bound; the charges come from the plan, never from the seed.
func sqrtSeed(n []uint32, rootDigits uint64, xb []uint32) []uint32 {
	tn := len(n)
	var f float64
	for i := tn - 1; i >= max(0, tn-3); i-- {
		f = f*float64(decimalLimbBase) + float64(n[i])
	}
	e := 9 * max(0, tn-3)
	if e%2 == 1 {
		f *= 10
		e--
	}
	lead := min(rootDigits, 17)
	h := e/2 - int(rootDigits-lead)
	g := math.Sqrt(f) * math.Pow10(h)
	seed := uint64(g * (1 + 2e-15))
	z := rootDigits - lead
	clear(xb)
	whole, part := z/9, z%9
	factor := uint64(decimalPowers[part])
	var carry uint64
	i := whole
	for seed != 0 || carry != 0 {
		v := (seed%decimalLimbBase)*factor + carry
		xb[i] = uint32(v % decimalLimbBase)
		carry = v / decimalLimbBase
		seed /= decimalLimbBase
		i++
	}
	return trimLimbs(xb[:i])
}

// sqrtUnlimited is bare Sqrt and a context with unlimited precision: the
// integer root of the full parity-adjusted coefficient at exponent ⌊e/2⌋,
// refused unless exact.
func (d Decimal) sqrtUnlimited(budget limits, op string, c *sqrtCount) (Decimal, Conditions, error) {
	if d.negative() && !d.isZero() {
		return contextFailure(op, ErrInvalidOperation)
	}
	ideal := d.exponent() >> 1
	if d.isZero() {
		if !admitted(budget.MaxDigits, 1, true) || !admitted(budget.MaxWork, 1, true) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return zeroDecimal(ideal), 0, nil
	}
	if c == nil && d.slow == nil {
		if root, exact, ok := d.sqrtExactInline(ideal, budget); ok {
			if !exact {
				return Decimal{}, 0, conditionError(op, Inexact, sqrtRemedy)
			}
			return root, 0, nil
		}
	}
	v := coefficientViewOf(d)
	dx, ok := arithmeticDigits(&v)
	k := int64(d.exponent()) - 2*int64(ideal)
	p := newSqrtPlan(dx, k)
	charge, ok2 := sqrtCharge(p.s, p.r)
	if !ok || !admitted(budget.MaxWork, charge, ok2) || !admitted(budget.MaxDigits, p.r, true) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	var stack [sqrtStackLimbs]uint32
	scratch, admittedPlan := sqrtScratch(&stack, newSqrtLayout(p.s, p.r), p.r)
	if !admittedPlan {
		return contextFailure(op, ErrInsufficientStorage)
	}
	r, class := sqrtDigits(&v, dx, p, scratch, c)
	if class != divExactClass {
		return Decimal{}, 0, conditionError(op, Inexact, sqrtRemedy)
	}
	if p.r <= 38 {
		return publishInlineArithmetic(r, ideal, false), 0, nil
	}
	return publishScratch(r, ideal, false), 0, nil
}

// sqrtExactInline is sqrtUnlimited for a positive inline operand: the
// parity-adjusted coefficient N = C·10^k, k = 0 or 1, is below 2^132, and
// its integer root is the result exactly when the root's square is N.
// Otherwise exact is false: the remainder N − r² is not zero, which is
// sqrtUnlimited's Inexact refusal once the budget is admitted. A budget is
// priced as sqrtUnlimited prices it before it takes the root, by the
// planned root digits and the precharge of the same plan. ok is false for
// a refused budget, which sqrtUnlimited owns.
func (d Decimal) sqrtExactInline(ideal int32, budget limits) (root Decimal, exact, ok bool) {
	k := int64(d.exponent()) - 2*int64(ideal)
	if budget != (limits{}) {
		p := newSqrtPlan(inlineDigits(d.words), k)
		if charge, ok := sqrtCharge(p.s, p.r); !ok || !budget.admits(p.r, charge) {
			return Decimal{}, false, false
		}
	}
	n := wide256{d.words.lo, d.words.hi}
	if k != 0 {
		n.mulSmall(10)
	}
	r, ok := sqrtWide(n)
	if !ok {
		return Decimal{}, false, false
	}
	if mulWide(r, r) != n {
		return Decimal{}, false, true
	}
	return inlineDecimal(r, ideal, false), true, true
}

// sqrtInlineMaxPrecision bounds the precision the word path serves: its
// p+1-digit root stays below 10^38.
const sqrtInlineMaxPrecision = 37

// sqrtFinisherAdmitted reports whether budget certainly admits the rest of
// sqrtContext's charges once its precharge is admitted: the finisher's
// 2N+1 over the precharge at N = p, the most digits a context result has,
// and p digits. A budget below that bound may still admit a shorter result.
func sqrtFinisherAdmitted(budget limits, charge, precision uint64) bool {
	work, ok := contextFinalCharge(charge, precision)
	return ok && budget.admits(precision, work)
}

// sqrtContextInline is sqrtContext for a positive inline operand whose
// scaled value N = C·10^k (k ≥ 0) has at most 76 digits: the exact integer
// root of the 256-bit N and its class from the remainder N − r², as
// sqrtDigits decides them, handed to the word finisher. ok is false for a
// k < 0 plan and wherever the finisher defers.
func (d Decimal) sqrtContextInline(ctx *Context, op string) (Decimal, Conditions, error, bool) {
	dx := inlineDigits(d.words)
	tPrime, etiny := sqrtContextTarget(dx, d.exponent(), ctx)
	k := int64(d.exponent()) - 2*tPrime
	if k < 0 || int64(dx)+k > 76 {
		return Decimal{}, 0, nil, false
	}
	n := mulWide(d.words, pow10Wide[min(k, 38)])
	for rest := uint64(max(k, 38)) - 38; rest > 0; {
		step := min(rest, 19)
		n.mulSmall(pow10Words[step])
		rest -= step
	}
	root, ok := sqrtWide(n)
	if !ok {
		return Decimal{}, 0, nil, false
	}
	// rem = N − r² ≤ 2r: below a half when rem ≤ r (r + 1/2 squared is
	// r² + r + 1/4), exact when zero, above otherwise.
	rem := subWide(n, mulWide(root, root))
	class := divBelow
	switch {
	case rem == (wide256{}):
		class = divExactClass
	case rem[2]|rem[3] != 0 || inlineCompare(uint128{rem[0], rem[1]}, root) > 0:
		class = divAbove
	}
	return finishContextInline(root, class, tPrime, etiny, int64(d.exponent()>>1), false, ctx, op)
}

// sqrtWide returns ⌊√n⌋ for 0 < n < 2^253. The candidate is one Newton
// step from the root of the top 128 bits, rounded up; exactness rests only
// on the closing comparisons x² ≤ n < (x+1)², never on the candidate.
func sqrtWide(n wide256) (uint128, bool) {
	if n[2]|n[3] == 0 {
		return uint128{lo: sqrtWords(uint128{n[0], n[1]})}, true
	}
	top := 3
	if n[3] == 0 {
		top = 2
	}
	bitLength := top*64 + bits.Len64(n[top])
	if bitLength > 253 {
		return uint128{}, false
	}
	shift := uint((bitLength+1)&^1) - 128 // even, so the root shifts by half
	var head uint128
	switch {
	case shift >= 64:
		head = uint128{n[1]>>(shift-64) | n[2]<<(128-shift), n[2]>>(shift-64) | n[3]<<(128-shift)}
	default:
		head = uint128{n[0]>>shift | n[1]<<(64-shift), n[1]>>shift | n[2]<<(64-shift)}
	}
	// x = (⌊√head⌋ + 1)·2^(shift/2) > √n, at most 2^127.
	r, carry := bits.Add64(sqrtWords(head), 1, 0)
	j := shift / 2
	x := uint128{r << j, r>>(64-j) | carry<<j}
	q, _, ok := divWide(n, x)
	if !ok {
		return uint128{}, false
	}
	var c uint64
	x.lo, c = bits.Add64(x.lo, q.lo, 0)
	x.hi, _ = bits.Add64(x.hi, q.hi, c)
	x = uint128{x.lo>>1 | x.hi<<63, x.hi >> 1}
	for mulWide(x, x).cmp(n) > 0 {
		var b uint64
		x.lo, b = bits.Sub64(x.lo, 1, 0)
		x.hi -= b
	}
	for {
		next := x
		next.lo, c = bits.Add64(next.lo, 1, 0)
		next.hi += c
		if mulWide(next, next).cmp(n) > 0 {
			return x, true
		}
		x = next
	}
}

// sqrtWords returns ⌊√n⌋ for a two-word n. A binary64 square root seeds
// the candidate and one Newton step sharpens a two-word one; the closing
// comparisons make the result exact whatever the seed.
func sqrtWords(n uint128) uint64 {
	var x uint64
	if n.hi == 0 {
		x = min(uint64(math.Sqrt(float64(n.lo))), math.MaxUint32)
	} else {
		x = ^uint64(0)
		if s := math.Sqrt(float64(n.hi)*0x1p64 + float64(n.lo)); s < 0x1p64 {
			x = uint64(s)
		}
		if n.hi < x {
			q, _ := bits.Div64(n.hi, n.lo, x)
			x = x/2 + q/2 + x&q&1
		}
	}
	for {
		hi, lo := bits.Mul64(x, x)
		if hi < n.hi || hi == n.hi && lo <= n.lo {
			break
		}
		x--
	}
	for x != ^uint64(0) {
		hi, lo := bits.Mul64(x+1, x+1)
		if hi > n.hi || hi == n.hi && lo > n.lo {
			break
		}
		x++
	}
	return x
}

// sqrtContextTarget is the root's exponent t′ = ⌊(d + e − 2p − 1)/2⌋,
// which leaves p+1 root digits, raised to Etiny under guards.
func sqrtContextTarget(dx uint64, e int32, ctx *Context) (tPrime, etiny int64) {
	precision := int64(ctx.precision)
	sum := int64(dx) + int64(e) - 2*precision - 1
	tPrime = sum >> 1 // floor division by 2
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (precision - 1)
		tPrime = max(tPrime, etiny)
	}
	return tPrime, etiny
}

func (d Decimal) sqrtContext(ctx Context, budget limits, op string, c *sqrtCount) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		return d.sqrtUnlimited(budget, op, c)
	}
	if d.negative() && !d.isZero() {
		return contextFailure(op, ErrInvalidOperation)
	}
	ideal := int64(d.exponent() >> 1)
	if d.isZero() {
		if !admitted(budget.MaxDigits, 1, true) || !contextFinalWork(1, 1, budget.MaxWork) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return zeroDecimal(int32(ideal)), 0, nil
	}
	if c == nil && budget == (limits{}) && d.slow == nil && ctx.precision <= sqrtInlineMaxPrecision {
		if result, conditions, err, ok := d.sqrtContextInline(&ctx, op); ok {
			return result, conditions, err
		}
	}
	v := coefficientViewOf(d)
	dx, ok := arithmeticDigits(&v)
	precision := uint64(ctx.precision)
	charge, ok2 := sqrtCharge(dx, precision+1)
	if !ok || !admitted(budget.MaxWork, charge, ok2) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if c == nil && budget != (limits{}) && d.slow == nil && ctx.precision <= sqrtInlineMaxPrecision && ok2 && sqrtFinisherAdmitted(budget, charge, precision) {
		// A budget that admits this precharge and the finisher at p digits
		// is never refused below, so the word path serves the call.
		if result, conditions, err, ok := d.sqrtContextInline(&ctx, op); ok {
			return result, conditions, err
		}
	}
	tPrime, etiny := sqrtContextTarget(dx, d.exponent(), &ctx)
	p := newSqrtPlan(dx, int64(d.exponent())-2*tPrime)
	var stack [sqrtStackLimbs]uint32
	var scratch []uint32
	if p.s == 0 {
		scratch = stack[:2] // an empty root and its carry limb
	} else {
		var admittedPlan bool
		scratch, admittedPlan = sqrtScratch(&stack, newSqrtLayout(p.s, p.r), precision+1)
		if !admittedPlan {
			return contextFailure(op, ErrInsufficientStorage)
		}
	}
	r, class := sqrtDigits(&v, dx, p, scratch, c)
	return finishContext(r, class, tPrime, etiny, ideal, false, &ctx, charge, budget, op)
}
