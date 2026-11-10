// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"encoding/binary"
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"reflect"
	"strconv"
	"strings"
	"testing"
)

// observedCost is what a call actually needs: the smallest admitting value
// of each budget axis (found by binary search against the operation's own
// admission) and its cold-pool cumulative allocation.
type observedCost struct {
	work, digits, heap uint64
}

// smallestAdmitting returns the least v in [1, hi] with admits(v), given
// admits(hi); admission is monotone in each cap.
func smallestAdmitting(hi uint64, admits func(uint64) bool) uint64 {
	lo := uint64(1)
	for lo < hi {
		mid := lo + (hi-lo)/2
		if admits(mid) {
			hi = mid
		} else {
			lo = mid + 1
		}
	}
	return hi
}

// checkArithmeticEstimate asserts estimate soundness for one call of a Budget
// family: the call admits under c.Budget(), the smallest admitting work and
// digit caps are at most the estimate, and the cold-pool allocation is at
// most HeapBytes. It returns what was observed for the attainment and
// closed-form checks.
func checkArithmeticEstimate(t *testing.T, label string, c Cost, run func(Budget) error) observedCost {
	t.Helper()
	if err := run(c.Budget()); err != nil {
		t.Fatalf("%s: refused under its estimate %+v: %v", label, c, err)
	}
	var o observedCost
	if c.WorkUnits > 0 {
		o.work = smallestAdmitting(c.WorkUnits, func(w uint64) bool { return run(Budget{MaxWork: w}) == nil })
	}
	if c.Digits > 0 {
		o.digits = smallestAdmitting(c.Digits, func(n uint64) bool { return run(Budget{MaxDigits: n}) == nil })
	}
	o.heap = coldAllocatedWithin(func() { _ = run(c.Budget()) }, c.HeapBytes)
	if o.heap > c.HeapBytes {
		t.Fatalf("%s: allocated %d bytes > HeapBytes %d", label, o.heap, c.HeapBytes)
	}
	return o
}

// shapedDecimal returns a Decimal with exactly digits significant digits
// (the leading digit nonzero) drawn from r, at exponent e, with sign neg.
// fill, when not zero, forces every digit (for nines and carry witnesses).
func shapedDecimal(r *rand.Rand, digits uint64, e int32, neg bool, fill byte) Decimal {
	b := make([]byte, 0, digits+16)
	if neg {
		b = append(b, '-')
	}
	for i := range digits {
		switch {
		case fill != 0:
			b = append(b, fill)
		case i == 0:
			b = append(b, byte('1'+r.IntN(9)))
		default:
			b = append(b, byte('0'+r.IntN(10)))
		}
	}
	b = append(b, 'E')
	b = append(b, []byte(big.NewInt(int64(e)).String())...)
	return MustParse(string(b))
}

// sweepDigits is the estimator size sweep: small sizes, the inline and
// fused-holder edges, limb and page boundaries, and (outside -short) sizes
// crossing 32 KiB objects.
func sweepDigits() []uint64 {
	sizes := []uint64{1, 2, 9, 10, 18, 19, 37, 38, 39, 40, 80, 81, 82, 90, 91, 200, 1000}
	if !testing.Short() {
		sizes = append(sizes, 9000, 73728, 100000)
	}
	return sizes
}

// TestAllocBoundCoversSizeClasses pins allocBound: allocBound(n) bounds the
// TotalAlloc charge of one n-byte object, pointer-free and pointer-bearing,
// for every n up to 40,000 on the running toolchain.
func TestAllocBoundCoversSizeClasses(t *testing.T) {
	// Every size class is a multiple of 16, so the envelope can only fail
	// just above a class boundary, at n = 16k+1. Above 2 KiB a stride of 8
	// from 1 still visits every such n; -short samples more sparsely.
	next := func(n int) int {
		switch {
		case testing.Short():
			return n + 97
		case n < 2048:
			return n + 1
		}
		return n + 8
	}
	var sinkBytes []byte
	var sinkPointers []*int
	for n := 1; n <= 40000; n = next(n) {
		var tally costTally
		bound := allocBound(&tally, uint64(n))
		withPointers := allocBound(&tally, uint64((n+7)/8*8))
		noscan := coldAllocatedWithin(func() { sinkBytes = make([]byte, n) }, bound)
		pointers := coldAllocatedWithin(func() { sinkPointers = make([]*int, (n+7)/8) }, withPointers)
		if noscan > bound {
			t.Fatalf("pointer-free %d bytes charged %d > allocBound %d", n, noscan, bound)
		}
		if pointers > withPointers {
			t.Fatalf("pointer-bearing %d bytes charged %d > allocBound %d", (n+7)/8*8, pointers, withPointers)
		}
	}
	_, _ = sinkBytes, sinkPointers
	var tally costTally
	if allocBound(&tally, 0) != 0 || allocBound(&tally, 32<<10+1) != 40<<10 || tally.overflow {
		t.Fatal("allocBound edges")
	}
	if allocBound(&tally, 1<<64-1); !tally.overflow {
		t.Fatal("allocBound overflow not reported")
	}
}

// TestEstimateAddSubBound checks estimate soundness, attainment and closed
// form for Add and Sub: across the size sweep, exponent gaps and every sign
// relation, the estimate admits, bounds the smallest admitting caps and the
// cold-pool allocation, equals the closed forms written here (same effective
// signs: work d1+d2+L+1, digits L+1 when the aligned spans overlap and L
// otherwise; opposite: work 2(d1+d2)+L, digits L), and is attained by the
// worst-case witnesses (nines for the carry, unequal magnitudes for the
// subtraction).
func TestEstimateAddSubBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 1))
	for _, dx := range sweepDigits() {
		for _, dy := range []uint64{1, 9, 38, 81, 200} {
			for _, gap := range []int32{0, 1, 5, 40, 1000} {
				for _, subtract := range []bool{false, true} {
					for _, signs := range [][2]bool{{false, false}, {false, true}, {true, false}, {true, true}} {
						same := signs[0] == (signs[1] != subtract)
						var fill byte
						if same {
							fill = '9' // the carry witness
						}
						x := shapedDecimal(r, dx, gap, signs[0], fill)
						y := shapedDecimal(r, dy, 0, signs[1], fill)
						estimate, op := EstimateAdd, func(o Decimal, b Budget) (Decimal, error) { return addWithBudget(x, o, b) }
						if subtract {
							estimate, op = EstimateSub, func(o Decimal, b Budget) (Decimal, error) { return subWithBudget(x, o, b) }
						}
						c, err := estimate(x.Shape(), y.Shape(), Context{})
						if err != nil {
							t.Fatal(err)
						}
						// Closed forms, written independently of the planner.
						L := max(dx+uint64(gap), dy)
						wantWork, wantDigits := 2*(dx+dy)+L, L
						if same {
							wantWork = dx + dy + L + 1
							if uint64(gap) < dy { // spans overlap
								wantDigits = L + 1
							}
						}
						label := x.String()[:min(12, len(x.String()))] + "…"
						if c.WorkUnits != wantWork || c.Digits != wantDigits {
							t.Fatalf("%s dx=%d dy=%d gap=%d same=%t: estimate %+v, closed form work %d digits %d", label, dx, dy, gap, same, c, wantWork, wantDigits)
						}
						o := checkArithmeticEstimate(t, label, c, func(b Budget) error { _, err := op(y, b); return err })
						// Attainment: the work charge is exact for the shape; the
						// nines witness reaches the carry digit, and unequal
						// magnitudes reach L.
						// Exact cancellation stops after the precompare; it is
						// sound but cannot attain, so attainment needs unequal
						// magnitudes.
						cancels := !same && x.Abs().Compare(y.Abs()) == 0
						if !cancels && o.work != c.WorkUnits {
							t.Fatalf("%s dx=%d dy=%d gap=%d same=%t: work %d not attained (%d)", label, dx, dy, gap, same, c.WorkUnits, o.work)
						}
						if !cancels && o.digits != c.Digits {
							t.Fatalf("%s dx=%d dy=%d gap=%d same=%t: digits %d not attained (%d)", label, dx, dy, gap, same, c.Digits, o.digits)
						}
					}
				}
			}
		}
	}
	// A caller that knows no signs takes the Max over both relations: 99+1
	// needs 3 digits, 99+(−1) needs work 8.
	a, b := MustParse("99"), MustParse("1")
	same, _ := EstimateAdd(a.Shape(), b.Shape(), Context{})
	opposite, _ := EstimateAdd(a.Shape(), b.Neg().Shape(), Context{})
	agnostic := same.Max(opposite)
	for _, y := range []Decimal{b, b.Neg()} {
		if _, _, err := a.AddWithContext(y, Context{}.WithBudget(agnostic.Budget())); err != nil {
			t.Fatalf("sign-agnostic estimate refused 99%+v: %v", y, err)
		}
	}
	if same.Digits != 3 || opposite.WorkUnits != 8 || agnostic.Digits != 3 || agnostic.WorkUnits != 8 {
		t.Fatalf("99±1 estimates: same %+v opposite %+v", same, opposite)
	}
}

// TestEstimateMulBound checks estimate soundness, attainment and closed form
// for Mul: the estimate equals the closed form (digits d1+d2, work
// ⌈d1/9⌉·⌈d2/9⌉ + d1 + d2), admits, bounds the cold-pool allocation, and both
// axes are attained (the digit axis is checked before any work, and the work
// charge is exact for the shape); an exponent sum outside int32 is
// ErrExponentRange.
func TestEstimateMulBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 2))
	for _, dx := range sweepDigits() {
		for _, dy := range []uint64{1, 9, 19, 38, 41, 81, 200} {
			x, y := shapedDecimal(r, dx, -3, r.IntN(2) == 0, 0), shapedDecimal(r, dy, 7, r.IntN(2) == 0, 0)
			c, err := EstimateMul(x.Shape(), y.Shape(), Context{})
			if err != nil {
				t.Fatal(err)
			}
			wantWork := ((dx+8)/9)*((dy+8)/9) + dx + dy
			if c.Digits != dx+dy || c.WorkUnits != wantWork {
				t.Fatalf("dx=%d dy=%d: estimate %+v, closed form digits %d work %d", dx, dy, c, dx+dy, wantWork)
			}
			o := checkArithmeticEstimate(t, "mul", c, func(b Budget) error { _, _, err := x.MulWithContext(y, Context{}.WithBudget(b)); return err })
			if o.work != c.WorkUnits || o.digits != c.Digits {
				t.Fatalf("dx=%d dy=%d: estimate %+v not attained: work %d digits %d", dx, dy, c, o.work, o.digits)
			}
		}
	}
	if _, err := EstimateMul(Shape{Digits: 1, Exponent: 1 << 30}, Shape{Digits: 1, Exponent: 1 << 30}, Context{}); !isErrorCode(err, ErrExponentRange) {
		t.Fatalf("exponent overflow: %v", err)
	}
}

func isErrorCode(err error, code ErrorCode) bool {
	if c, ok := err.(ErrorCode); ok {
		return c == code
	}
	oe, ok := err.(*Error)
	return ok && oe.Code == code
}

// TestEstimateContextBound checks estimate soundness, attainment and closed
// form for the context forms of Add, Sub and Mul: the estimate is the closed
// form B + 2N + 1 with B the bare tariff and N = min(p, exact digits), or p
// when guards make an overflow reachable; it admits, bounds the allocation,
// and the nines witnesses (a carry for same signs, a dominant minuend for
// opposite signs, an exact product) attain both axes; a guarded overflow
// attains N = p.
func TestEstimateContextBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 3))
	unguarded := func(p uint32) Context {
		c, err := NewContext(p, TiesToEven, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		return c
	}
	contexts := []Context{unguarded(1), unguarded(16), unguarded(34), unguarded(60), unguarded(100), Decimal128Context()}
	sizes := []uint64{1, 9, 19, 38, 40, 81, 120}
	for _, ctx := range contexts {
		p := uint64(ctx.precision)
		for _, dx := range sizes {
			for _, dy := range []uint64{1, 5, 38, 90} {
				gap := int32(r.IntN(6))
				x := shapedDecimal(r, dx, gap, false, '9')
				ySame := shapedDecimal(r, dy, 0, false, '9')
				// Ones spanning less than x keep x dominant, so the difference
				// keeps x's span L (context Add checks the result's digits).
				oppositeDigits := max(1, min(dy/2, dx+uint64(gap)-1))
				yOpposite := shapedDecimal(r, oppositeDigits, 0, true, '1')
				sameBase, sameExact := reducedAddForm(dx, int64(gap), dy, 0, p, true)
				oppositeBase, oppositeExact := reducedAddForm(dx, int64(gap), oppositeDigits, 0, p, false)
				cases := []struct {
					name  string
					est   func() (Cost, error)
					run   func(Budget) error
					base  uint64
					exact uint64
				}{
					{"add-same", func() (Cost, error) { return EstimateAdd(x.Shape(), ySame.Shape(), ctx) },
						func(b Budget) error { _, _, err := x.AddWithContext(ySame, ctx.WithBudget(b)); return err },
						sameBase, sameExact},
					{"add-opposite", func() (Cost, error) { return EstimateAdd(x.Shape(), yOpposite.Shape(), ctx) },
						func(b Budget) error { _, _, err := x.AddWithContext(yOpposite, ctx.WithBudget(b)); return err },
						oppositeBase, oppositeExact},
					{"mul", func() (Cost, error) { return EstimateMul(x.Shape(), ySame.Shape(), ctx) },
						func(b Budget) error { _, _, err := x.MulWithContext(ySame, ctx.WithBudget(b)); return err },
						((dx+8)/9)*((dy+8)/9) + dx + dy, dx + dy},
				}
				for _, tc := range cases {
					c, err := tc.est()
					if err != nil {
						t.Fatal(err)
					}
					n := min(p, tc.exact)
					if c.Digits != n || c.WorkUnits != tc.base+2*n+1 {
						t.Fatalf("%s p=%d dx=%d dy=%d gap=%d: estimate %+v, closed form N %d W %d", tc.name, p, dx, dy, gap, c, n, tc.base+2*n+1)
					}
					o := checkArithmeticEstimate(t, tc.name, c, tc.run)
					if o.work != c.WorkUnits || o.digits != c.Digits {
						t.Fatalf("%s p=%d dx=%d dy=%d gap=%d: estimate %+v not attained: work %d digits %d", tc.name, p, dx, dy, gap, c, o.work, o.digits)
					}
				}
			}
		}
	}
	// At p=1 the sticky reduction already fires at gap 5 (dx=1, dy=5): 9E+5 +
	// (−11) is charged over 9E+5 + (−1E+2), with L=4, B=8 and W=11, not over
	// the unreduced span (L=6, B=12, W=15).
	nines, ones := MustParse("9E+5"), MustParse("-11")
	if c, err := EstimateAdd(nines.Shape(), ones.Shape(), contexts[0]); err != nil || c.WorkUnits != 11 || c.Digits != 1 {
		t.Fatalf("reduced p=1 witness: %+v %v", c, err)
	}
	checkZeroShapeEstimates(t)
	// The context estimate charges the reduced span, and the bare estimator's
	// physical refusal over the unreduced span (about 2^32 digits here,
	// beyond the 32-bit targets' window) does not apply: 1E+2147483647 +
	// 1E-2147483648 at p=34 is charged over 1E+2147483647 + 1E+2147483611
	// (L=37, B=40, N=34, W=109).
	top, bottom := New(1, math.MaxInt32), New(1, math.MinInt32)
	p34 := unguarded(34)
	if c, err := EstimateAdd(top.Shape(), bottom.Shape(), p34); err != nil || c.WorkUnits != 109 || c.Digits != 34 {
		t.Fatalf("int32-span witness: %+v %v", c, err)
	} else if o := checkArithmeticEstimate(t, "int32-span", c, func(b Budget) error { _, _, err := top.AddWithContext(bottom, p34.WithBudget(b)); return err }); o.work != 109 || o.digits != 34 {
		t.Fatalf("int32-span witness not attained: %+v", o)
	}
	// A billion-digit shape at MaxInt32 plus 1E-2147483648: the unreduced
	// span (about 5.3e9 digits) exceeds the 32-bit window, which the bare
	// EstimateAdd refuses there; the reduced span is 1e9+1 digits
	// (B=2e9+3, W=2e9+72) on every target.
	wide, low := Shape{Digits: 1_000_000_000, Exponent: math.MaxInt32}, Shape{Digits: 1, Exponent: math.MinInt32}
	if c, err := EstimateAdd(wide, low, p34); err != nil || c.WorkUnits != 2_000_000_072 || c.Digits != 34 {
		t.Fatalf("wide int32-span witness: %+v %v", c, err)
	}
	// A guarded overflow publishes p nines: N = p is attained even though
	// the exact product has two digits.
	ctx, err := NewContext(34, TiesToEven, &ExponentGuards{Emin: -99, Emax: 99}, 0)
	if err != nil {
		t.Fatal(err)
	}
	top, ten := MustParse("9E99"), MustParse("10")
	c, err := EstimateMul(top.Shape(), ten.Shape(), ctx)
	if err != nil || c.Digits != 34 {
		t.Fatalf("guarded overflow estimate: %+v %v", c, err)
	}
	o := checkArithmeticEstimate(t, "overflow", c, func(b Budget) error { _, _, err := top.MulWithContext(ten, ctx.WithBudget(b)); return err })
	if o.digits != 34 || o.work != c.WorkUnits {
		t.Fatalf("guarded overflow not attained: %+v vs %+v", o, c)
	}
	// Random operands under guarded contexts reaching subnormal and overflow
	// results: soundness only.
	for i := range 3000 {
		pr := uint32(1 + r.IntN(60))
		emax := int32(r.IntN(120))
		gctx, err := NewContext(pr, RoundingMode(r.IntN(7)), &ExponentGuards{Emin: -emax, Emax: emax}, 0)
		if err != nil {
			continue
		}
		a := shapedDecimal(r, uint64(1+r.IntN(70)), int32(r.IntN(200)-100), r.IntN(2) == 0, 0)
		b := shapedDecimal(r, uint64(1+r.IntN(70)), int32(r.IntN(200)-100), r.IntN(2) == 0, 0)
		if i%4 == 0 { // zero shapes, clamped or not, beside guards
			b = New(0, int32(r.IntN(400)-250))
		}
		if i%8 == 1 { // nines that round into the next decade or overflow
			a = shapedDecimal(r, uint64(1+r.IntN(70)), int32(r.IntN(200)-100), r.IntN(2) == 0, '9')
		}
		for name, pair := range map[string]struct {
			est func() (Cost, error)
			run func(Budget) error
		}{
			"add": {func() (Cost, error) { return EstimateAdd(a.Shape(), b.Shape(), gctx) },
				func(bd Budget) error { _, _, err := a.AddWithContext(b, gctx.WithBudget(bd)); return err }},
			"sub": {func() (Cost, error) { return EstimateSub(a.Shape(), b.Shape(), gctx) },
				func(bd Budget) error { _, _, err := a.SubWithContext(b, gctx.WithBudget(bd)); return err }},
			"mul": {func() (Cost, error) { return EstimateMul(a.Shape(), b.Shape(), gctx) },
				func(bd Budget) error { _, _, err := a.MulWithContext(b, gctx.WithBudget(bd)); return err }},
		} {
			c, err := pair.est()
			if err != nil {
				continue // shape-determined refusal, checked by TestEstimateErrorsMatchOperation
			}
			if pair.run(Budget{}) != nil {
				continue // a data-dependent refusal (range after rounding), not estimated
			}
			checkArithmeticEstimate(t, name+"-random-"+string(rune('0'+i%10)), c, pair.run)
		}
	}
	// Precision 0 is the bare estimate.
	x, y := MustParse("123.45"), MustParse("-6.7")
	bare, _ := EstimateAdd(x.Shape(), y.Shape(), Context{})
	zero, _ := EstimateAdd(x.Shape(), y.Shape(), Context{})
	if bare != zero {
		t.Fatalf("precision 0: %+v vs bare %+v", zero, bare)
	}
}

// reducedAddForm is the closed form of the context (p > 0) base charge B and
// exact digit bound for two nonzero operands of dx and dy digits at exponents
// ex and ey, over the planner's reduced operands: an operand lying wholly
// below P = min(e_large, adj_large−p−1)−1 counts as one digit at P.
func reducedAddForm(dx uint64, ex int64, dy uint64, ey int64, p uint64, same bool) (base, exact uint64) {
	adjX, adjY := ex+int64(dx)-1, ey+int64(dy)-1
	if adjY > adjX {
		if P := min(ey, adjY-int64(p)-1) - 1; adjX < P {
			dx, ex = 1, P
		}
	} else if P := min(ex, adjX-int64(p)-1) - 1; adjY < P {
		dy, ey = 1, P
	}
	e := min(ex, ey)
	sx, sy := uint64(ex-e), uint64(ey-e)
	L := max(dx+sx, dy+sy)
	if !same {
		return 2*(dx+dy) + L, L
	}
	return dx + dy + L + 1, L + boolDigit(sx < dy+sy && sy < dx+sx)
}

// checkZeroShapeEstimates checks that a zero shape stays out of the span L,
// which counts only the nonzero's digits down to the zero's reduced exponent
// max(e0, min(e, pos−1)), pos being the lowest kept digit position. The
// estimate charges B = L for one nonzero operand and B = 1 for two zeros,
// with N = min(p, L), and is attained, for zeros above the nonzero's
// exponent, between pos and it, at pos−1, and far below pos.
func checkZeroShapeEstimates(t *testing.T) {
	t.Helper()
	for _, p := range []uint32{1, 7, 16, 34} {
		ctx, err := NewContext(p, TiesToEven, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		for _, d := range []uint64{1, 5, 16, 40} {
			const e = 10
			pos := e + int64(d) - int64(p)
			nonzero := shapedDecimal(nil, d, e, d%2 == 0, '9')
			for _, ez := range []int64{100_000_000, e + 3, e, e - 1, pos + 1, pos, pos - 1, pos - 2, -100_000_000} {
				if ez < math.MinInt32 || ez > math.MaxInt32 {
					continue
				}
				zero := New(0, int32(ez))
				L := d
				if ez < e {
					L = d + uint64(e-max(ez, min(e, pos-1)))
				}
				n := min(uint64(p), L)
				for _, order := range []bool{false, true} {
					x, y := nonzero, zero
					if order {
						x, y = zero, nonzero
					}
					for _, sub := range []bool{false, true} {
						est, run := EstimateAdd, func(b Budget) error { _, _, err := x.AddWithContext(y, ctx.WithBudget(b)); return err }
						if sub {
							est, run = EstimateSub, func(b Budget) error { _, _, err := x.SubWithContext(y, ctx.WithBudget(b)); return err }
						}
						c, err := est(x.Shape(), y.Shape(), ctx)
						label := fmt.Sprintf("zero shape p=%d d=%d e0=%d order=%v sub=%v", p, d, ez, order, sub)
						if err != nil || c.WorkUnits != L+2*n+1 || c.Digits != n {
							t.Fatalf("%s: estimate %+v %v, closed form L %d N %d", label, c, err, L, n)
						}
						if o := checkArithmeticEstimate(t, label, c, run); o.work != c.WorkUnits || o.digits != c.Digits {
							t.Fatalf("%s: estimate %+v not attained: work %d digits %d", label, c, o.work, o.digits)
						}
					}
				}
			}
		}
		// Both zero: B = 1, N = 1, W = 4 whatever the exponents.
		a, b := New(0, 100_000_000), New(0, -100_000_000)
		c, err := EstimateAdd(a.Shape(), b.Shape(), ctx)
		if err != nil || c.WorkUnits != 4 || c.Digits != 1 {
			t.Fatalf("both zero p=%d: %+v %v", p, c, err)
		}
		checkArithmeticEstimate(t, "both zero", c, func(bd Budget) error { _, _, err := a.AddWithContext(b, ctx.WithBudget(bd)); return err })
	}
	// Under guards the zero is clamped below max(pos, Etiny): 9999E-30 +
	// 0E-1000 at p=16 with Emin -20 (Etiny -35) is charged over L = 10
	// (B=10, N=min(16,10), W=31); the tiny result keeps 9 digits, so W=29
	// is attained (the guarded slack of two units per dropped digit).
	gctx, err := NewContext(16, TiesToEven, &ExponentGuards{Emin: -20, Emax: 20}, 0)
	if err != nil {
		t.Fatal(err)
	}
	tiny, far := MustParse("9999E-30"), New(0, -1000)
	c, err := EstimateAdd(tiny.Shape(), far.Shape(), gctx)
	if err != nil || c.WorkUnits != 31 || c.Digits != 10 {
		t.Fatalf("guarded zero clamp at Etiny: %+v %v", c, err)
	}
	if o := checkArithmeticEstimate(t, "guarded zero clamp", c, func(b Budget) error { _, _, err := tiny.AddWithContext(far, gctx.WithBudget(b)); return err }); o.work != 29 || o.digits != 9 {
		t.Fatalf("guarded zero clamp at Etiny: observed %+v", o)
	}
	// A remote zero: 0E+100000000 + 1 at p=34 costs B = 1.
	c, err = EstimateAdd(MustParse("0E+100000000").Shape(), One().Shape(), Decimal128Context())
	if err != nil || c.WorkUnits != 4 || c.Digits != 1 {
		t.Fatalf("0E+100000000 + 1: %+v %v", c, err)
	}
}

func boolDigit(b bool) uint64 {
	if b {
		return 1
	}
	return 0
}

// TestEstimateQuantizeBound checks estimate soundness, attainment and closed
// form for Quantize and RoundToIntegral: the estimate equals the closed form
// (grow k: work and digits d+k; equal: work 1, digits d; shrink by c < d:
// work d+(d−c)+carry, digits (d−c)+carry; c = d: work d+1, digits 1; c > d:
// work 2, digits 1), with the carry counted exactly when the mode can round
// the magnitude up; it admits, bounds the allocation, and the nines witness
// attains both axes in every mode and sign; an unreachable target is
// ErrInvalidOperation.
func TestEstimateQuantizeBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 4))
	for _, d := range []uint64{1, 2, 9, 38, 39, 60, 81, 82, 200} {
		for _, k := range []int64{0, 1, 5, 21, 60, -1, -3, -int64(d) + 1, -int64(d), -int64(d) - 4} {
			if k < 0 && -k > int64(d)+10 || k == 0 && d == 0 {
				continue
			}
			for mode := TiesToEven; mode <= TowardNegativeInfinity; mode++ {
				for _, negative := range []bool{false, true} {
					x := shapedDecimal(r, d, 0, negative, '9')
					target := int32(-k) // x.exponent is 0, so e − t = k
					ctx, err := NewContext(0, mode, nil, 0)
					if err != nil {
						t.Fatal(err)
					}
					c, err := EstimateQuantize(x.Shape(), target, ctx)
					if err != nil {
						t.Fatal(err)
					}
					up := mode != TowardZero && !(mode == TowardPositiveInfinity && negative) && !(mode == TowardNegativeInfinity && !negative)
					var work, digits uint64
					switch cut := uint64(-k); {
					case k > 0:
						work, digits = d+uint64(k), d+uint64(k)
					case k == 0:
						work, digits = 1, d
					case cut < d:
						digits = d - cut + boolDigit(up)
						work = d + digits
					case cut == d:
						work, digits = d+1, 1
					default:
						work, digits = 2, 1
					}
					if c.WorkUnits != work || c.Digits != digits {
						t.Fatalf("d=%d k=%d mode=%d neg=%t: estimate %+v, closed form work %d digits %d", d, k, mode, negative, c, work, digits)
					}
					o := checkArithmeticEstimate(t, "quantize", c, func(b Budget) error {
						_, _, err := x.QuantizeWithContext(target, ctx.WithBudget(b))
						return err
					})
					if o.work != c.WorkUnits || o.digits != c.Digits {
						t.Fatalf("d=%d k=%d mode=%d neg=%t: estimate %+v not attained: %+v", d, k, mode, negative, c, o)
					}
				}
			}
		}
	}
	x := MustParse("123.456")
	ctx := Decimal64Context()
	c, err := EstimateRoundToIntegral(x.Shape(), ctx)
	if err != nil {
		t.Fatal(err)
	}
	checkArithmeticEstimate(t, "round-to-integral", c, func(b Budget) error {
		_, _, err := x.RoundToIntegralWithContext(ctx.WithBudget(b))
		return err
	})
	if _, err := EstimateQuantize(x.Shape(), 7000, Decimal128Context()); !isErrorCode(err, ErrInvalidOperation) {
		t.Fatalf("guarded target beyond Emax: %v", err)
	}
	if _, err := EstimateQuantize(Shape{Digits: 30}, -10, Decimal64Context()); !isErrorCode(err, ErrInvalidOperation) {
		t.Fatalf("result beyond precision: %v", err)
	}
}

// TestEstimateDivBound checks estimate soundness, attainment and closed form
// for Div, DivToExponent and DivWithContext. Random operands check soundness
// on every path (tiny, H0, divide) and scratch size; the witnesses check
// attainment within the family's slack: DivWithContext reaches N = p exactly
// with a non-terminating quotient, DivToExponent and the exact Div (y = 2^m,
// whose quotient 5^m·10^−m needs almost every fractional digit) reach within
// 2 digits, i.e. 4 work units, of the estimate.
func TestEstimateDivBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 5))
	ctx := Decimal128Context()
	for i := range 2000 {
		dx, dy := uint64(1+r.IntN(120)), uint64(1+r.IntN(80))
		if i%50 == 0 && !testing.Short() {
			dx, dy = uint64(300+r.IntN(900)), uint64(1+r.IntN(400)) // scratch above 48 limbs
		}
		x := shapedDecimal(r, dx, int32(r.IntN(40)-20), r.IntN(2) == 0, 0)
		y := shapedDecimal(r, dy, int32(r.IntN(40)-20), r.IntN(2) == 0, 0)
		target := int32(r.IntN(120) - 80)
		for name, pair := range map[string]struct {
			est func() (Cost, error)
			run func(Budget) error
		}{
			"div": {func() (Cost, error) { return EstimateDiv(x.Shape(), y.Shape(), Context{}) },
				func(b Budget) error { _, _, err := x.DivWithContext(y, Context{}.WithBudget(b)); return err }},
			"div-to-exponent": {func() (Cost, error) { return EstimateDivToExponent(x.Shape(), y.Shape(), target) },
				func(b Budget) error {
					_, _, err := x.DivToExponentWithBudget(y, target, TiesToEven, b)
					return err
				}},
			"div-context": {func() (Cost, error) { return EstimateDiv(x.Shape(), y.Shape(), ctx) },
				func(b Budget) error { _, _, err := x.DivWithContext(y, ctx.WithBudget(b)); return err }},
		} {
			c, err := pair.est()
			if err != nil {
				t.Fatalf("%s: %v", name, err)
			}
			if _, isCondition := pair.run(Budget{}).(*Error); isCondition {
				continue // a non-terminating exact quotient: refused, not estimated
			}
			checkArithmeticEstimate(t, name, c, pair.run)
		}
	}
	// Witnesses.
	for _, dy := range []int64{1, 3, 10, 30, 75} {
		// The largest power of two with dy digits needs the most fractional
		// digits of any dy-digit divisor.
		m := new(big.Int).Sub(new(big.Int).Exp(big.NewInt(10), big.NewInt(dy), nil), big.NewInt(1)).BitLen() - 1
		y := MustParse(new(big.Int).Lsh(big.NewInt(1), uint(m)).String())
		x := MustParse("1")
		c, err := EstimateDiv(x.Shape(), y.Shape(), Context{})
		if err != nil {
			t.Fatal(err)
		}
		o := checkArithmeticEstimate(t, "div-2^m", c, func(b Budget) error { _, _, err := x.DivWithContext(y, Context{}.WithBudget(b)); return err })
		if c.Digits-o.digits > 2 || c.WorkUnits-o.work > 4 {
			t.Fatalf("div 1/2^%d (%d digits): estimate %+v beyond slack of %+v", m, dy, c, o)
		}
	}
	for _, dy := range []uint64{1, 5, 19, 40, 90} {
		x, y := shapedDecimal(r, 1, 0, false, '1'), shapedDecimal(r, dy, 0, false, '3') // 1/33…3 never terminates
		c, err := EstimateDiv(x.Shape(), y.Shape(), ctx)
		if err != nil {
			t.Fatal(err)
		}
		o := checkArithmeticEstimate(t, "div-context", c, func(b Budget) error { _, _, err := x.DivWithContext(y, ctx.WithBudget(b)); return err })
		if o.digits != c.Digits || o.work != c.WorkUnits {
			t.Fatalf("div-context 1/3…(%d): %+v not attained: %+v", dy, c, o)
		}
		for _, target := range []int32{-5, -40} {
			nines := shapedDecimal(r, 30, 0, false, '9')
			c, err := EstimateDivToExponent(nines.Shape(), y.Shape(), target)
			if err != nil {
				t.Fatal(err)
			}
			o := checkArithmeticEstimate(t, "div-to-exponent", c, func(b Budget) error {
				_, _, err := nines.DivToExponentWithBudget(y, target, TiesToEven, b)
				return err
			})
			if c.Digits-o.digits > 2 || c.WorkUnits-o.work > 4 {
				t.Fatalf("div-to-exponent 9…9/3…3 at %d: estimate %+v beyond slack of %+v", target, c, o)
			}
		}
	}
	if _, err := EstimateDiv(Shape{Digits: 1, Exponent: -1 << 31}, Shape{Digits: 1, Exponent: 1<<31 - 1}, Context{}); !isErrorCode(err, ErrExponentRange) {
		t.Fatalf("ideal exponent below int32: %v", err)
	}
}

// TestEstimateFromRatBound checks estimate soundness and attainment for the
// FromRat family. Soundness: random rationals for the directed and context
// forms, and terminating ones (d = 2^a·5^b, every trailing-zero count a) for
// the exact form, each admitted under its estimate with the cold-pool
// allocation bounded. Attainment within the documented FromRat slack: over
// the witnesses of a shape, the best reaches the work estimate within a
// factor 1.25 and the digit estimate within 0.35·(bn+bd)+40 digits, because
// the result's digits come from the word-count conversion envelope.
func TestEstimateFromRatBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 6))
	slackDigits := func(bn, bd uint64) uint64 { return 35*(bn+bd)/100 + 40 }
	randomInt := func(bitLen int) *big.Int {
		v := big.NewInt(1)
		for range bitLen - 1 {
			v.Lsh(v, 1)
			v.SetBit(v, 0, uint(r.IntN(2)))
		}
		return v
	}
	for _, total := range []int{16, 64, 200, 1000} {
		bestWork, bestDigits := 1e18, uint64(1<<62)
		var bn, bd uint64
		for a := range total {
			five := new(big.Int).Exp(big.NewInt(5), big.NewInt(int64((total-a)*43/100)), nil)
			d := new(big.Int).Lsh(five, uint(a))
			n := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), uint(total)), big.NewInt(1))
			x := new(big.Rat).SetFrac(n, d)
			bn, bd = uint64(x.Num().BitLen()), uint64(x.Denom().BitLen())
			c, err := EstimateFromRat(bn, bd, Context{})
			if err != nil {
				t.Fatal(err)
			}
			o := checkArithmeticEstimate(t, "from-rat", c, func(b Budget) error { _, _, err := FromRatWithContext(x, Context{}.WithBudget(b)); return err })
			bestWork = min(bestWork, float64(c.WorkUnits)/float64(o.work))
			bestDigits = min(bestDigits, c.Digits-o.digits)
		}
		if bestWork > 1.25 || bestDigits > slackDigits(bn, bd) {
			t.Fatalf("from-rat %d bits: best work ratio %.3f, digit slack %d beyond the documented slack", total, bestWork, bestDigits)
		}
	}
	ctx := Decimal128Context()
	for range 1500 {
		n, d := randomInt(1+r.IntN(300)), randomInt(1+r.IntN(300))
		if r.IntN(2) == 0 {
			n.Neg(n)
		}
		x := new(big.Rat).SetFrac(n, d)
		bn, bd := uint64(x.Num().BitLen()), uint64(x.Denom().BitLen())
		target := int32(r.IntN(200) - 120)
		c, err := EstimateFromRatToExponent(bn, bd, target)
		if err != nil {
			t.Fatal(err)
		}
		checkArithmeticEstimate(t, "from-rat-to-exponent", c, func(b Budget) error {
			_, _, err := FromRatToExponentWithBudget(x, target, TiesToEven, b)
			return err
		})
		for _, p := range []uint32{1, 34, 400} {
			pctx := ctx
			if p != 34 {
				pctx, _ = NewContext(p, TiesToEven, nil, 0)
			}
			c, err := EstimateFromRat(bn, bd, pctx)
			if err != nil {
				t.Fatal(err)
			}
			checkArithmeticEstimate(t, "from-rat-context", c, func(b Budget) error {
				_, _, err := FromRatWithContext(x, pctx.WithBudget(b))
				return err
			})
		}
	}
	if c, err := EstimateFromRat(0, 1, Context{}); err != nil || c.WorkUnits != 4 || c.Digits != 1 {
		t.Fatalf("zero: %+v %v", c, err)
	}
}

// TestEstimateFromFloat64ToExponentBound checks estimate soundness and
// attainment for FromFloat64ToExponent: over random bit patterns (normal,
// subnormal, extreme exponents) and targets that pad or round, the estimate
// admits, bounds the allocation, and is attained on the work axis within the
// one carry digit it reserves when rounding (2 units), and exactly when
// padding.
func TestEstimateFromFloat64ToExponentBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 8))
	for i := range 4000 {
		f := math.Float64frombits(r.Uint64())
		if math.IsNaN(f) || math.IsInf(f, 0) {
			continue
		}
		target := int32(r.IntN(900) - 700)
		if i%10 == 0 {
			target = int32(r.IntN(4000) - 3000) // long pads
		}
		c, err := EstimateFromFloat64ToExponent(f, target)
		if err != nil {
			t.Fatal(err)
		}
		o := checkArithmeticEstimate(t, "from-float64", c, func(b Budget) error {
			_, _, err := FromFloat64ToExponentWithBudget(f, target, TiesToEven, b)
			return err
		})
		if f != 0 && (c.WorkUnits-o.work > 2 || c.Digits-o.digits > 1) {
			t.Fatalf("%v at %d: estimate %+v beyond the carry slack of %+v", f, target, c, o)
		}
	}
	if _, err := EstimateFromFloat64ToExponent(math.Inf(1), 0); !isErrorCode(err, ErrConversionSyntax) {
		t.Fatalf("infinity: %v", err)
	}
}

// checkIntegerEstimate is checkArithmeticEstimate for the
// integer-conversion family: work, output digits (Cost.Digits) and
// input digits.
func checkIntegerEstimate(t *testing.T, label string, c Cost, run func(Budget) error) (work, output, input uint64) {
	t.Helper()
	if err := run(c.Budget()); err != nil {
		t.Fatalf("%s: refused under its estimate %+v: %v", label, c, err)
	}
	if c.WorkUnits > 0 {
		work = smallestAdmitting(c.WorkUnits, func(w uint64) bool { return run(Budget{MaxWork: w}) == nil })
	}
	if c.Digits > 0 {
		output = smallestAdmitting(c.Digits, func(n uint64) bool { return run(Budget{MaxDigits: n}) == nil })
	}
	if c.InputDigits > 0 {
		input = smallestAdmitting(c.InputDigits, func(n uint64) bool { return run(Budget{MaxInputDigits: n}) == nil })
	}
	if heap := coldAllocatedWithin(func() { _ = run(c.Budget()) }, c.HeapBytes); heap > c.HeapBytes {
		t.Fatalf("%s: allocated %d bytes > HeapBytes %d", label, heap, c.HeapBytes)
	}
	return work, output, input
}

// TestEstimateIntegerConversionBound checks estimate soundness and attainment
// for FromBigInt, BigInt, Rat, Compose and NewTwosComplement: across the size
// sweep, integral and fractional exponents and trailing zeros, every estimate
// admits and bounds the allocation. Where the tariff is a function of the
// shape (FromBigInt, Compose, NewTwosComplement over the raw bit length;
// BigInt of an integral shape), the work is attained exactly; Rat is attained
// within its z = 0 / z = 1 maximum.
func TestEstimateIntegerConversionBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 9))
	for _, d := range sweepDigits() {
		x := shapedDecimal(r, d, 0, r.IntN(2) == 0, 0)
		v, _ := x.BigInt(nil)
		c, err := EstimateFromBigInt(uint64(v.BitLen()))
		if err != nil {
			t.Fatal(err)
		}
		work, _, _ := checkIntegerEstimate(t, "from-big-int", c, func(b Budget) error { _, err := FromBigIntWithBudget(v, b); return err })
		if work != c.WorkUnits {
			t.Fatalf("from-big-int %d digits: work %d not attained (%d)", d, c.WorkUnits, work)
		}
		raw := new(big.Int).Abs(v).Bytes()
		c, err = EstimateCompose(uint64(len(raw)))
		if err != nil {
			t.Fatal(err)
		}
		work, _, _ = checkIntegerEstimate(t, "compose", c, func(b Budget) error {
			var out Decimal
			return out.ComposeWithBudget(0, x.Sign() < 0, raw, 3, b)
		})
		if work != c.WorkUnits {
			t.Fatalf("compose %d bytes: work %d not attained (%d)", len(raw), c.WorkUnits, work)
		}
		lane := append([]byte{0}, raw...)
		c, err = EstimateNewTwosComplement(uint64(len(lane)))
		if err != nil {
			t.Fatal(err)
		}
		checkIntegerEstimate(t, "twos-complement", c, func(b Budget) error {
			_, err := NewTwosComplementWithBudget(lane, binary.BigEndian, 0, b)
			return err
		})
		for _, e := range []int32{0, 3, 40, -1, -int32(min(d, 60)) + 1} {
			y := shapedDecimal(r, d, e, r.IntN(2) == 0, 0)
			if e < 0 {
				// Integral with trailing zeros so BigInt admits.
				y = MustParse(strings.TrimSuffix(shapedDecimal(r, d, 0, false, 0).String(), "") + strings.Repeat("0", -int(e)) + "E" + big.NewInt(int64(e)).String())
			}
			c, err := EstimateBigInt(y.Shape())
			if err != nil {
				t.Fatal(err)
			}
			work, _, _ := checkIntegerEstimate(t, "big-int", c, func(b Budget) error { _, err := y.BigIntWithBudget(nil, b); return err })
			if work != c.WorkUnits {
				t.Fatalf("big-int %v: work %d not attained (%d)", y.Shape(), c.WorkUnits, work)
			}
		}
		for _, e := range []int32{0, 5, -1, -3, -int32(min(d+5, 90))} {
			for _, zeros := range []int{0, 1, 4} {
				z := shapedDecimal(r, d, 0, r.IntN(2) == 0, 0)
				y := MustParse(z.String() + strings.Repeat("0", zeros) + "E" + big.NewInt(int64(e)).String())
				c, err := EstimateRat(y.Shape())
				if err != nil {
					t.Fatal(err)
				}
				checkIntegerEstimate(t, "rat", c, func(b Budget) error { _, err := y.RatWithBudget(nil, b); return err })
			}
		}
	}
	if _, err := EstimateBigInt(Shape{Digits: 3, Exponent: -3}); !isErrorCode(err, ErrNonIntegral) {
		t.Fatalf("all digits dropped: %v", err)
	}
	if _, err := EstimateNewTwosComplement(uint64(0)); !isErrorCode(err, ErrConversionSyntax) {
		t.Fatalf("empty lane: %v", err)
	}
}

// TestEstimateDisplayBound checks estimate soundness and attainment for
// Fixed, Scientific and Engineering: across digit counts, exponents, places,
// signs and modes the estimate admits (work and output bytes) and bounds the
// string's allocation; the nines witness in a mode that rounds the magnitude
// up attains both axes exactly (sign kept, carry taken).
func TestEstimateDisplayBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 10))
	check := func(label string, c Cost, run func(Budget) error) (work, output uint64) {
		t.Helper()
		if err := run(c.Budget()); err != nil {
			t.Fatalf("%s: refused under %+v: %v", label, c, err)
		}
		work = smallestAdmitting(c.WorkUnits, func(w uint64) bool { return run(Budget{MaxWork: w}) == nil })
		output = smallestAdmitting(c.OutputBytes, func(b uint64) bool { return run(Budget{MaxOutputBytes: b}) == nil })
		if heap := coldAllocatedWithin(func() { _ = run(c.Budget()) }, c.HeapBytes); heap > c.HeapBytes {
			t.Fatalf("%s: allocated %d > HeapBytes %d", label, heap, c.HeapBytes)
		}
		return work, output
	}
	for _, d := range []uint64{1, 3, 9, 19, 38, 39, 81, 200} {
		for _, e := range []int32{-250, -40, -5, -1, 0, 2, 30} {
			for _, places := range []uint64{0, 1, 2, 7, 40} {
				for _, mode := range []RoundingMode{TiesToEven, TowardZero, AwayFromZero} {
					for _, negative := range []bool{false, true} {
						x := shapedDecimal(r, d, e, negative, '9')
						opts := DisplayOptions{Mode: mode}
						c, err := EstimateFixed(x.Shape(), places, opts.Mode)
						if err != nil {
							t.Fatal(err)
						}
						w, o := check("fixed", c, func(b Budget) error {
							_, err := x.FixedWithOptions(places, DisplayOptions{Mode: mode, Budget: b})
							return err
						})
						if w != c.WorkUnits || o != c.OutputBytes {
							t.Fatalf("fixed %v places %d mode %d: %+v not attained: work %d output %d", x.Shape(), places, mode, c, w, o)
						}
						if places > 0 {
							c, err = EstimateScientific(x.Shape(), places, opts.Mode)
							if err != nil {
								t.Fatal(err)
							}
							w, o = check("scientific", c, func(b Budget) error {
								_, err := x.ScientificWithOptions(places, DisplayOptions{Mode: mode, Budget: b})
								return err
							})
							if w != c.WorkUnits || o != c.OutputBytes {
								t.Fatalf("scientific %v digits %d mode %d: %+v not attained: work %d output %d", x.Shape(), places, mode, c, w, o)
							}
						}
					}
				}
			}
			x := shapedDecimal(r, d, e, r.IntN(2) == 0, 0)
			c, err := EstimateEngineering(x.Shape())
			if err != nil {
				t.Fatal(err)
			}
			w, o := check("engineering", c, func(b Budget) error { _, err := x.EngineeringWithBudget(b); return err })
			if w != c.WorkUnits || o != c.OutputBytes {
				t.Fatalf("engineering %v: %+v not attained: work %d output %d", x.Shape(), c, w, o)
			}
		}
	}
	// Random digits, where a carry may shorten the exponent: soundness only.
	for range 5000 {
		x := shapedDecimal(r, uint64(1+r.IntN(40)), int32(r.IntN(260)-130), r.IntN(2) == 0, 0)
		places := uint64(1 + r.IntN(12))
		mode := RoundingMode(r.IntN(7))
		for _, kind := range []string{"fixed", "scientific"} {
			var c Cost
			var err error
			var run func(Budget) error
			if kind == "fixed" {
				c, err = EstimateFixed(x.Shape(), places, mode)
				run = func(b Budget) error {
					_, err := x.FixedWithOptions(places, DisplayOptions{Mode: mode, Budget: b})
					return err
				}
			} else {
				c, err = EstimateScientific(x.Shape(), places, mode)
				run = func(b Budget) error {
					_, err := x.ScientificWithOptions(places, DisplayOptions{Mode: mode, Budget: b})
					return err
				}
			}
			if err != nil {
				t.Fatal(err)
			}
			if err := run(c.Budget()); err != nil {
				t.Fatalf("%s %v places %d mode %d: refused under %+v: %v", kind, x, places, mode, c, err)
			}
		}
	}
	for _, text := range []string{"7.12345E-10", "1.23E-100", "-9.96E-10"} {
		x := MustParse(text)
		for _, mode := range []RoundingMode{TiesToEven, AwayFromZero} {
			c, _ := EstimateScientific(x.Shape(), 2, mode)
			if _, err := x.ScientificWithOptions(2, DisplayOptions{Mode: mode, Budget: c.Budget()}); err != nil {
				t.Fatalf("%s mode %d: refused under %+v: %v", text, mode, c, err)
			}
		}
	}
	if _, err := EstimateScientific(Shape{Digits: 3}, 0, TiesToEven); !isErrorCode(err, ErrInvalidContext) {
		t.Fatalf("scientific with zero digits: %v", err)
	}
}

// TestEstimateTextBound checks estimate soundness and attainment for the text
// families: Parse, ParseToExponent (pads bounded by a digit cap),
// ParseWithContext, ParseJSON (numbers and escaped strings) and Scan (every
// source kind). Each call, including syntax errors whose Error copies byte
// input, allocates at most HeapBytes and is admitted under the estimate's
// budget (or refused only by a data-dependent error the estimate does not
// predict); an all-digit literal attains Parse's digit estimate.
func TestEstimateTextBound(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 11))
	literal := func() string {
		var b strings.Builder
		if r.IntN(3) == 0 {
			b.WriteByte('-')
		}
		b.WriteString(strings.TrimLeft(shapedDecimal(r, uint64(1+r.IntN(90)), 0, false, 0).String(), "-"))
		if r.IntN(2) == 0 {
			b.WriteString("." + strings.Repeat("7", r.IntN(30)+1))
		}
		if r.IntN(3) == 0 {
			b.WriteString("E" + big.NewInt(int64(r.IntN(80)-40)).String())
		}
		if r.IntN(15) == 0 {
			b.WriteString("x") // a syntax error
		}
		return b.String()
	}
	checkParse := func(label string, c Cost, run func(Budget) error) {
		t.Helper()
		err := run(c.Budget())
		if err != nil && !isErrorCode(err, ErrConversionSyntax) && !isParseErrorCode(err, ErrConversionSyntax) && !isParseErrorCode(err, ErrExponentRange) {
			t.Fatalf("%s: refused under %+v: %v", label, c, err)
		}
		if heap := coldAllocatedWithin(func() { _ = run(c.Budget()) }, c.HeapBytes); heap > c.HeapBytes {
			t.Fatalf("%s: allocated %d > HeapBytes %d", label, heap, c.HeapBytes)
		}
	}
	for range 3000 {
		s := literal()
		b := []byte(s)
		c, err := EstimateParse(uint64(len(s)), Context{})
		if err != nil {
			t.Fatal(err)
		}
		checkParse("parse/string", c, func(pb Budget) error { _, _, err := ParseWithContext(s, Context{}.WithBudget(pb)); return err })
		checkParse("parse/bytes", c, func(pb Budget) error { _, _, err := ParseWithContext(b, Context{}.WithBudget(pb)); return err })
		target := int32(r.IntN(120) - 80)
		capped := Budget{MaxDigits: uint64(1 + r.IntN(400))}
		c, err = EstimateParseToExponent(uint64(len(s)), target, capped)
		if err != nil {
			t.Fatal(err)
		}
		checkParse("parse-to-exponent", c, func(pb Budget) error {
			_, _, err := ParseToExponentWithBudget(b, target, TiesToEven, pb)
			if isErrorCode(err, ErrInsufficientStorage) && c.Digits == capped.MaxDigits {
				return nil // the literal needs more than the caller's cap: refused before allocating
			}
			return err
		})
		ctx := Decimal64Context()
		c, err = EstimateParse(uint64(len(s)), ctx.WithBudget(Budget{}))
		if err != nil {
			t.Fatal(err)
		}
		checkParse("parse-with-context", c, func(pb Budget) error {
			_, _, err := ParseWithContext(b, ctx.WithBudget(pb))
			return err
		})
		for _, raw := range [][]byte{b, []byte(`"` + s + `"`), []byte(`"1` + s + `"`)} {
			c, err = EstimateParseJSON(uint64(len(raw)), Budget{})
			if err != nil {
				t.Fatal(err)
			}
			checkParse("parse-json", c, func(pb Budget) error { _, err := ParseJSONWithBudget(raw, pb); return err })
		}
		for _, src := range []any{s, b} {
			c, err = EstimateScan(src, Budget{})
			if err != nil {
				t.Fatal(err)
			}
			checkParse("scan", c, func(pb Budget) error {
				var d Decimal
				return d.ScanWithBudget(src, Budget{MaxInputBytes: pb.MaxInputBytes, MaxDigits: pb.MaxDigits, MaxWork: c.WorkUnits})
			})
		}
	}
	// Attainment: an all-digit literal needs every byte as a digit.
	for _, n := range sweepDigits() {
		s := shapedDecimal(r, n, 0, false, 0).String()
		c, _ := EstimateParse(uint64(len(s)), Context{})
		if got := smallestAdmitting(c.Digits, func(v uint64) bool {
			_, _, err := ParseWithContext(s, Context{}.WithBudget(Budget{MaxDigits: v}))
			return err == nil
		}); got != c.Digits {
			t.Fatalf("parse %d digits: estimate %d not attained (%d)", n, c.Digits, got)
		}
	}
	// A guarded overflow publishes p nines.
	guarded, _ := NewContext(34, TiesToEven, &ExponentGuards{Emin: -100, Emax: 100}, 0)
	for range 1500 {
		text := shapedDecimal(r, uint64(1+r.IntN(8)), int32(r.IntN(400)-200), r.IntN(2) == 0, 0).String()
		c, err := EstimateParse(uint64(len(text)), guarded.WithBudget(Budget{}))
		if err != nil {
			t.Fatal(err)
		}
		b := []byte(text)
		run := func(pb Budget) error { _, _, err := ParseWithContext(b, guarded.WithBudget(pb)); return err }
		if err := run(c.Budget()); err != nil {
			t.Fatalf("guarded %s: refused under %+v: %v", text, c, err)
		}
		if heap := coldAllocatedWithin(func() { _ = run(c.Budget()) }, c.HeapBytes); heap > c.HeapBytes {
			t.Fatalf("guarded %s: allocated %d > %d", text, heap, c.HeapBytes)
		}
	}
	// Guarded slack: N = p whatever the literal's length, so a short literal
	// that cannot overflow the guards is over-estimated by exactly p − min(p,
	// n) digits: "123" at p = 200.
	guardedWide, _ := NewContext(200, TiesToEven, &ExponentGuards{Emin: -100, Emax: 100}, 0)
	c, err := EstimateParse(uint64(3), guardedWide.WithBudget(Budget{}))
	if err != nil || c.Digits != 200 {
		t.Fatalf("guarded slack estimate: %+v %v", c, err)
	}
	if got := smallestAdmitting(c.Digits, func(v uint64) bool {
		_, _, err := ParseWithContext([]byte("123"), guardedWide.WithBudget(Budget{MaxDigits: v}))
		return err == nil
	}); c.Digits-got != 200-3 {
		t.Fatalf("guarded slack: attained %d digits, want slack %d", got, 200-3)
	}
	// A pad that no digit cap bounds is still finite: the 12-byte literal
	// 1E2147483000 at target 0.
	c, err = EstimateParseToExponent(uint64(12), 0, Budget{})
	if err != nil || c.Digits < 2147483000 {
		t.Fatalf("uncapped pad: %+v %v", c, err)
	}
	// Scan kinds.
	for _, src := range []any{int64(-1234567), 0.1, math.SmallestNonzeroFloat64, nil} {
		c, err := EstimateScan(src, Budget{})
		if err != nil {
			t.Fatal(err)
		}
		var d NullDecimal
		if err := d.ScanWithBudget(src, c.Budget()); err != nil {
			t.Fatalf("scan %T under %+v: %v", src, c, err)
		}
		if heap := coldAllocatedWithin(func() { _ = d.ScanWithBudget(src, c.Budget()) }, c.HeapBytes); heap > c.HeapBytes {
			t.Fatalf("scan %T: allocated %d > %d", src, heap, c.HeapBytes)
		}
	}
	lane := make([]byte, 40)
	lane[0] = 7
	c, err = EstimateScan(decimalSource{coefficient: lane}, Budget{MaxInputBytes: 40})
	if err != nil {
		t.Fatal(err)
	}
	var d Decimal
	if err := d.ScanWithBudget(decimalSource{coefficient: lane}, c.Budget()); err != nil {
		t.Fatalf("scan decompose under %+v: %v", c, err)
	}
	// Byte caps beyond a 32-bit int: the estimate bounds a 4000-byte lane on
	// every target.
	wide := make([]byte, 4000)
	wide[0] = 9
	for _, limit := range []uint64{1 << 31, 1<<32 + 100, 1<<64 - 1} {
		c, err := EstimateScan(decimalSource{coefficient: wide}, Budget{MaxInputBytes: limit})
		if isErrorCode(err, ErrInsufficientStorage) {
			continue // a lane that large cannot be admitted: no finite bound, not a wrong one
		}
		if err != nil {
			t.Fatal(err)
		}
		var d Decimal
		if err := d.ScanWithBudget(decimalSource{coefficient: wide}, c.Budget()); err != nil {
			t.Fatalf("decompose under byte cap %d: refused under %+v: %v", limit, c, err)
		}
		if heap := coldAllocatedWithin(func() { _ = d.ScanWithBudget(decimalSource{coefficient: wide}, c.Budget()) }, c.HeapBytes); heap > c.HeapBytes {
			t.Fatalf("decompose under byte cap %d: allocated %d > %d", limit, heap, c.HeapBytes)
		}
	}
	if _, err := EstimateScan(decimalSource{}, Budget{}); !isErrorCode(err, ErrInsufficientStorage) {
		t.Fatalf("decompose without a byte cap: %v", err)
	}
	if _, err := EstimateScan(true, Budget{}); !isErrorCode(err, ErrConversionSyntax) {
		t.Fatalf("unsupported kind: %v", err)
	}
}

func isParseErrorCode(err error, code ErrorCode) bool {
	pe, ok := err.(*Error)
	return ok && pe.Code == code
}

// TestEstimatorsDoNotAllocate checks that every estimator runs without
// allocating, including on its refusal paths and for a Scan source the caller
// boxes once.
func TestEstimatorsDoNotAllocate(t *testing.T) {
	x, y := Shape{Digits: 81, Exponent: -20}, Shape{Digits: 38, Exponent: 5, Negative: true}
	ctx := Decimal128Context()
	var sink Cost
	var sinkErr error
	src := any([]byte("123.45"))
	decomposer := any(decimalSource{coefficient: []byte{1, 2}})
	calls := map[string]func(){
		"add":         func() { sink, sinkErr = EstimateAdd(x, y, Context{}) },
		"sub":         func() { sink, sinkErr = EstimateSub(x, y, Context{}) },
		"mul":         func() { sink, sinkErr = EstimateMul(x, y, Context{}) },
		"add-context": func() { sink, sinkErr = EstimateAdd(x, y, ctx) },
		"mul-context": func() { sink, sinkErr = EstimateMul(x, y, ctx) },
		"quantize":    func() { sink, sinkErr = EstimateQuantize(x, -40, ctx) },
		"integral":    func() { sink, sinkErr = EstimateRoundToIntegral(x, ctx) },
		"div":         func() { sink, sinkErr = EstimateDiv(x, y, Context{}) },
		"div-exp":     func() { sink, sinkErr = EstimateDivToExponent(x, y, -10) },
		"round-prec":  func() { sink, sinkErr = EstimateRoundToPrecision(x, ctx) },
		"sum": func() {
			sink, sinkErr = EstimateSum(SumShape{Count: 1000, Digits: 5000, MinExponent: -3, MaxAdjusted: 5, Nonzero: true})
		},
		"sqrt":         func() { sink, sinkErr = EstimateSqrt(x, Context{}) },
		"sqrt-context": func() { sink, sinkErr = EstimateSqrt(x, ctx) },
		"sqrt-refusal": func() { sink, sinkErr = EstimateSqrt(y, ctx) },
		"fma":          func() { sink, sinkErr = estimateFMA(x, y, x) },
		"fma-context":  func() { sink, sinkErr = EstimateFMA(x, y, x, ctx) },
		"fma-refusal":  func() { sink, sinkErr = estimateFMA(Shape{Exponent: math.MaxInt32}, y, x) },
		"round-mult":   func() { sink, sinkErr = EstimateRoundToMultiple(x, Shape{Digits: 2, Exponent: -2}) },
		"pow":          func() { sink, sinkErr = EstimatePow(x, 7, Context{}) },
		"pow-recip":    func() { sink, sinkErr = EstimatePow(x, -7, Context{}) },
		"pow-context":  func() { sink, sinkErr = EstimatePow(x, 1000000, ctx) },
		"pow-ctx-rcp":  func() { sink, sinkErr = EstimatePow(y, -3, ctx) },
		"pow-refusal":  func() { sink, sinkErr = EstimatePow(Shape{Exponent: 1 << 30}, 4, Context{}) },
		"div-context":  func() { sink, sinkErr = EstimateDiv(x, y, ctx) },
		"from-rat":     func() { sink, sinkErr = EstimateFromRat(500, 300, Context{}) },
		"from-rat-exp": func() { sink, sinkErr = EstimateFromRatToExponent(500, 300, -7) },
		"from-rat-ctx": func() { sink, sinkErr = EstimateFromRat(500, 300, ctx) },
		"from-float64": func() { sink, sinkErr = EstimateFromFloat64ToExponent(0.1, -60) },
		"from-big-int": func() { sink, sinkErr = EstimateFromBigInt(4000) },
		"big-int":      func() { sink, sinkErr = EstimateBigInt(x) },
		"rat":          func() { sink, sinkErr = EstimateRat(x) },
		"compose":      func() { sink, sinkErr = EstimateCompose(uint64(40)) },
		"twos":         func() { sink, sinkErr = EstimateNewTwosComplement(uint64(40)) },
		"parse":        func() { sink, sinkErr = EstimateParse(uint64(90), Context{}) },
		"parse-exp":    func() { sink, sinkErr = EstimateParseToExponent(uint64(90), -3, Budget{}) },
		"parse-ctx":    func() { sink, sinkErr = EstimateParse(uint64(90), ctx.WithBudget(Budget{})) },
		"parse-json":   func() { sink, sinkErr = EstimateParseJSON(uint64(90), Budget{}) },
		"scan":         func() { sink, sinkErr = EstimateScan(src, Budget{}) },
		"scan-decomp":  func() { sink, sinkErr = EstimateScan(decomposer, Budget{MaxInputBytes: 8}) },
		"fixed":        func() { sink, sinkErr = EstimateFixed(x, 3, TiesToEven) },
		"scientific":   func() { sink, sinkErr = EstimateScientific(x, 7, TiesToEven) },
		"engineering":  func() { sink, sinkErr = EstimateEngineering(x) },
		"shape":        func() { sink.Digits = MustParse("123").Shape().Digits },
		"refusal-range": func() {
			sink, sinkErr = EstimateMul(Shape{Digits: 1, Exponent: 1 << 30}, Shape{Digits: 1, Exponent: 1 << 30}, Context{})
		},
	}
	for name, call := range calls {
		if allocs := testing.AllocsPerRun(50, call); allocs != 0 {
			t.Errorf("%s allocated %v times (error %v)", name, allocs, sinkErr)
		}
	}
	_ = sink
}

// TestEstimateZeroShapes covers the zero shape: Digits 0 is zero, and a
// refusal predicted for nonzero values of a shape is not predicted for zero,
// whose operations succeed on their own paths.
func TestEstimateZeroShapes(t *testing.T) {
	five, _ := NewContext(5, TiesToEven, nil, 0)
	for _, tc := range []struct {
		name string
		est  func() (Cost, error)
		op   func() error
	}{
		{"big-int of 0E-5", func() (Cost, error) { return EstimateBigInt(MustParse("0E-5").Shape()) },
			func() error { _, err := MustParse("0E-5").BigIntWithBudget(nil, Budget{}); return err }},
		{"rat of 0E-5", func() (Cost, error) { return EstimateRat(MustParse("0E-5").Shape()) },
			func() error { _, err := MustParse("0E-5").RatWithBudget(nil, Budget{}); return err }},
		{"quantize 0E10 at p=5", func() (Cost, error) { return EstimateQuantize(MustParse("0E10").Shape(), 0, five) },
			func() error {
				_, _, err := MustParse("0E10").QuantizeWithContext(0, five.WithBudget(Budget{}))
				return err
			}},
		{"div 0 by 3", func() (Cost, error) { return EstimateDivToExponent(MustParse("0").Shape(), MustParse("3").Shape(), -4) },
			func() error {
				_, _, err := MustParse("0").DivToExponentWithBudget(MustParse("3"), -4, TiesToEven, Budget{})
				return err
			}},
	} {
		c, err := tc.est()
		if err != nil {
			t.Fatalf("%s: estimate predicts %v for a zero that succeeds", tc.name, err)
		}
		if err := tc.op(); err != nil {
			t.Fatalf("%s: %v", tc.name, err)
		}
		if heap := coldAllocatedWithin(func() { _ = tc.op() }, c.HeapBytes); heap > c.HeapBytes {
			t.Fatalf("%s: allocated %d > %d", tc.name, heap, c.HeapBytes)
		}
	}
	// A zero dividend is charged contextFinalWork(1, 1) = 4 by every division
	// form: W = 3 would refuse 0/x.
	three := MustParse("3")
	for _, tc := range []struct {
		name string
		est  func() (Cost, error)
		run  func(Budget) error
	}{
		{"div", func() (Cost, error) { return EstimateDiv(Zero().Shape(), three.Shape(), Context{}) },
			func(b Budget) error { _, _, err := Zero().DivWithContext(three, Context{}.WithBudget(b)); return err }},
		{"div-to-exponent", func() (Cost, error) { return EstimateDivToExponent(Zero().Shape(), three.Shape(), -4) },
			func(b Budget) error {
				_, _, err := Zero().DivToExponentWithBudget(three, -4, TiesToEven, b)
				return err
			}},
		{"div-with-context", func() (Cost, error) { return EstimateDiv(Zero().Shape(), three.Shape(), five) },
			func(b Budget) error {
				_, _, err := Zero().DivWithContext(three, five.WithBudget(b))
				return err
			}},
	} {
		c, err := tc.est()
		if err != nil || c.WorkUnits != 4 || c.Digits != 1 {
			t.Fatalf("zero dividend %s: %+v %v", tc.name, c, err)
		}
		if o := checkArithmeticEstimate(t, "zero dividend "+tc.name, c, tc.run); o.work != 4 || o.digits != 1 {
			t.Fatalf("zero dividend %s: attained %+v, want W=4 N=1", tc.name, o)
		}
	}
	if s := MustParse("0E7").Shape(); s.Digits != 0 || s.Exponent != 7 || s.Negative {
		t.Fatalf("zero shape: %+v", s)
	}
}

// TestEstimateErrorsMatchOperation checks that where the shape alone decides
// a refusal, the estimator returns the operation's own error code (errors.Is
// on both), and allocates nothing doing so.
func TestEstimateErrorsMatchOperation(t *testing.T) {
	big1 := MustParse("1E1073741824")
	tiny := MustParse("1E-2147483648")
	ctx := Decimal128Context()
	for _, tc := range []struct {
		name string
		est  func() error
		op   func() error
		code ErrorCode
	}{
		{"mul exponent", func() error { _, err := EstimateMul(big1.Shape(), big1.Shape(), Context{}); return err },
			func() error { _, _, err := big1.MulWithContext(big1, Context{}); return err }, ErrExponentRange},
		{"div ideal exponent", func() error { _, err := EstimateDiv(tiny.Shape(), MustParse("1E1").Shape(), Context{}); return err },
			func() error {
				_, _, err := tiny.DivWithContext(MustParse("1E1"), Context{})
				return err
			}, ErrExponentRange},
		{"quantize beyond Emax", func() error { _, err := EstimateQuantize(MustParse("1").Shape(), 7000, ctx); return err },
			func() error {
				_, _, err := MustParse("1").QuantizeWithContext(7000, ctx.WithBudget(Budget{}))
				return err
			}, ErrInvalidOperation},
		{"quantize beyond precision", func() error { _, err := EstimateQuantize(MustParse("123").Shape(), -40, ctx); return err },
			func() error {
				_, _, err := MustParse("123").QuantizeWithContext(-40, ctx.WithBudget(Budget{}))
				return err
			}, ErrInvalidOperation},
		{"big-int non-integral", func() error { _, err := EstimateBigInt(MustParse("0.25").Shape()); return err },
			func() error { _, err := MustParse("0.25").BigIntWithBudget(nil, Budget{}); return err }, ErrNonIntegral},
		{"empty lane", func() error { _, err := EstimateNewTwosComplement(uint64(0)); return err },
			func() error {
				_, err := NewTwosComplementWithBudget(nil, binary.BigEndian, 0, Budget{})
				return err
			}, ErrConversionSyntax},
		{"infinite float", func() error { _, err := EstimateFromFloat64ToExponent(math.Inf(-1), 0); return err },
			func() error {
				_, _, err := FromFloat64ToExponentWithBudget(math.Inf(-1), 0, TiesToEven, Budget{})
				return err
			}, ErrConversionSyntax},
		{"unsupported scan", func() error { _, err := EstimateScan(true, Budget{}); return err },
			func() error { var d Decimal; return d.ScanWithBudget(true, Budget{}) }, ErrConversionSyntax},
		{"scientific zero digits", func() error { _, err := EstimateScientific(MustParse("1").Shape(), 0, TiesToEven); return err },
			func() error { _, err := MustParse("1").ScientificWithOptions(0, DisplayOptions{}); return err }, ErrInvalidContext},
		{"zero divisor", func() error {
			_, err := EstimateDiv(MustParse("1").Shape(), MustParse("0").Shape(), Context{})
			return err
		},
			func() error {
				_, _, err := MustParse("1").DivWithContext(MustParse("0"), Context{})
				return err
			}, ErrDivisionByZero},
		{"zero over zero", func() error {
			_, err := EstimateDiv(MustParse("0").Shape(), MustParse("0E3").Shape(), ctx)
			return err
		},
			func() error {
				_, _, err := MustParse("0").DivWithContext(MustParse("0E3"), ctx.WithBudget(Budget{}))
				return err
			}, ErrDivisionUndefined},
	} {
		estimated, actual := tc.est(), tc.op()
		if !errors.Is(estimated, tc.code) || !errors.Is(actual, tc.code) {
			t.Errorf("%s: estimate %v, operation %v, want %v", tc.name, estimated, actual, tc.code)
		}
		if allocs := testing.AllocsPerRun(20, func() { _ = tc.est() }); allocs != 0 {
			t.Errorf("%s: estimator refusal allocated %v times", tc.name, allocs)
		}
	}
}

// TestEstimatesMatchClosedForms checks the closed forms of the families whose
// tariffs the other estimate tests do not already write out: each estimate's
// work and digits equal the tariff transcribed here (Div, FromRat, binary64
// conversion and radix conversion), without calling any planner.
func TestEstimatesMatchClosedForms(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 12))
	limbs := func(d uint64) uint64 { return 1 + (d-1)/9 }
	words := func(b uint64) uint64 { return (b + 63) / 64 }
	envelope := func(bitLen uint64) uint64 { return bitLen*30103/100000 + 1 }
	radix := func(u uint64) uint64 { t := 2 * limbs(u); return t*t + t }
	for range 3000 {
		// Div at an explicit target.
		dx, dy := uint64(1+r.IntN(200)), uint64(1+r.IntN(120))
		ex, ey, target := int32(r.IntN(60)-30), int32(r.IntN(60)-30), int32(r.IntN(200)-120)
		c, err := EstimateDivToExponent(Shape{Digits: dx, Exponent: ex}, Shape{Digits: dy, Exponent: ey}, target)
		if err != nil {
			t.Fatal(err)
		}
		k := int64(ex) - int64(ey) - int64(target)
		lower := min(limbs(dx), limbs(dy))
		var charge, n uint64
		switch {
		case k < 0 && dx+2 <= dy+uint64(-k) || k >= 0 && dx+uint64(k)+2 <= dy:
			charge, n = lower+1, 1
		case k < 0 && uint64(-k) >= dx:
			charge, n = dx+dy+lower, 1
		default:
			dn, reads := dx+uint64(max(k, 0)), dx+uint64(max(k, 0))
			if k < 0 {
				dn, reads = dx-uint64(-k), dx
			}
			tn, m := limbs(dn), limbs(dy)
			charge = reads + dy + lower
			if tn >= m {
				charge += 2*(tn-m+1)*(m+1) + 2*(tn+m+1)
			}
			n = 1
			if dn >= dy {
				n = dn - dy + 2
			}
		}
		if c.WorkUnits != charge+2*n+1 || c.Digits != n {
			t.Fatalf("div %d/%d at k=%d: estimate %+v, closed form B %d N %d", dx, dy, k, c, charge, n)
		}

		// FromRat toward a target.
		bn, bd := uint64(1+r.IntN(900)), uint64(1+r.IntN(900))
		rt := int32(r.IntN(300) - 150)
		c, err = EstimateFromRatToExponent(bn, bd, rt)
		if err != nil {
			t.Fatal(err)
		}
		power := func(w uint64) uint64 { return (4*w*w+2)/3 + w }
		powerWords := func(k uint64) uint64 { return words(k*332193/100000 + 1) }
		conversion := func(wq uint64) (uint64, uint64) { u := envelope(64 * wq); return u * limbs(u), u }
		wn, wd := words(bn), words(bd)
		var want, uq uint64
		tinyRat := false
		if kk := -int64(rt); kk < 0 {
			j := uint64(-kk)
			floor := j * 33219280948873623 / 10000000000000000
			if bn+1 < bd+floor {
				tinyRat = true
			} else {
				wj := powerWords(j)
				wD := wd + wj
				wq := uint64(1)
				if bn+1 > bd+floor {
					wq = words(bn + 1 - bd - floor)
				}
				conv, u := conversion(wq)
				want, uq = power(wj)+wd*wj+2*(wq+1)*(wD+1)+conv+wn+wD, u
			}
		} else {
			wk := powerWords(uint64(kk))
			wN := wn + wk
			division := wN + wd
			if wN >= wd {
				division = 2 * (wN - wd + 2) * (wd + 1)
			}
			wq := uint64(1)
			if wN >= wd {
				wq = wN - wd + 1
			}
			conv, u := conversion(wq)
			want, uq = power(wk)+wn*wk+division+conv+wN+wd, u
		}
		if tinyRat {
			if c.WorkUnits != 1+2+1 || c.Digits != 1 {
				t.Fatalf("from-rat tiny %d/%d at %d: %+v", bn, bd, rt, c)
			}
		} else if c.WorkUnits != want+2*(uq+1)+1 || c.Digits != uq+1 {
			t.Fatalf("from-rat %d/%d bits at %d: estimate %+v, closed form B %d Uq %d", bn, bd, rt, c, want, uq)
		}

		// FromBigInt and Compose.
		bits := uint64(1 + r.IntN(4000))
		c, err = EstimateFromBigInt(bits)
		if err != nil {
			t.Fatal(err)
		}
		if u := envelope(bits); c.Digits != u || c.InputDigits != u || c.WorkUnits != radix(u) {
			t.Fatalf("from-big-int %d bits: estimate %+v, closed form U %d W %d", bits, c, u, radix(u))
		}
		nb := 1 + r.IntN(500)
		c, err = EstimateCompose(uint64(nb))
		if err != nil {
			t.Fatal(err)
		}
		if u := envelope(8 * uint64(nb)); c.Digits != u || c.WorkUnits != radix(u) {
			t.Fatalf("compose %d bytes: estimate %+v, closed form U %d W %d", nb, c, u, radix(u))
		}

		// BigInt of an integral shape: T² + T with T = t(d) + t(d+e).
		d, e := uint64(1+r.IntN(300)), int32(r.IntN(100))
		c, err = EstimateBigInt(Shape{Digits: d, Exponent: e})
		if err != nil {
			t.Fatal(err)
		}
		if tt := limbs(d) + limbs(d+uint64(e)); c.WorkUnits != tt*tt+tt || c.Digits != d+uint64(e) {
			t.Fatalf("big-int %d digits e=%d: estimate %+v", d, e, c)
		}
	}
	// binary64: 87 per pass, one per padded limb, plus 2N+1.
	for range 2000 {
		f := math.Float64frombits(r.Uint64() &^ (1 << 63))
		if math.IsNaN(f) || math.IsInf(f, 0) || f == 0 {
			continue
		}
		target := int32(r.IntN(1500) - 1200)
		c, err := EstimateFromFloat64ToExponent(f, target)
		if err != nil {
			t.Fatal(err)
		}
		bitsF := math.Float64bits(f)
		mant, exp := bitsF&(1<<52-1), int64(bitsF>>52&0x7ff)
		if exp == 0 {
			exp = -1074
		} else {
			mant |= 1 << 52
			exp -= 1075
		}
		for mant&1 == 0 {
			mant >>= 1
			exp++
		}
		passes := uint64((exp + 28) / 29)
		if exp < 0 {
			passes = uint64((-exp + 12) / 13)
		}
		coefficient := new(big.Int).SetUint64(mant)
		x := min(exp, 0)
		if exp > 0 {
			coefficient.Lsh(coefficient, uint(exp))
		} else {
			coefficient.Mul(coefficient, new(big.Int).Exp(big.NewInt(5), big.NewInt(-exp), nil))
		}
		digits := uint64(len(coefficient.String()))
		var pad, n uint64
		if int64(target) < x {
			pad = uint64(x - int64(target))
			n = digits + pad
		} else if drop := uint64(int64(target) - x); digits > drop {
			n = digits - drop + 1
		} else {
			n = 1
		}
		want := 87*passes + (pad+8)/9 + 2*n + 1
		if c.WorkUnits != want || c.Digits != n {
			t.Fatalf("binary64 %v at %d: estimate %+v, closed form W %d N %d", f, target, c, want, n)
		}
	}
}

// TestEstimatesMatchMoreClosedForms extends the closed-form checks to the
// families TestEstimatesMatchClosedForms leaves out: exact Div,
// DivWithContext (unguarded), FromRat's worst case over every denominator of
// a size, Rat, NewTwosComplement, the Scan kinds, Parse and JSON, and the
// publication heap bound. Each formula is transcribed from the documented
// tariffs, calling no planner; allocBound's envelope is restated here too.
func TestEstimatesMatchMoreClosedForms(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 14))
	limbs := func(d uint64) uint64 { return 1 + (d-1)/9 }
	words := func(b uint64) uint64 { return (b + 63) / 64 }
	envelope := func(bitLen uint64) uint64 { return bitLen*30103/100000 + 1 }
	powerWords := func(k uint64) uint64 { return words(k*332193/100000 + 1) }
	power := func(w uint64) uint64 { return (4*w*w+2)/3 + w }
	division := func(wa, wb uint64) uint64 {
		if wa < wb {
			return wa + wb
		}
		return 2 * (wa - wb + 2) * (wb + 1)
	}
	divCharge := func(dx, dy uint64, k int64) uint64 {
		lower := min(limbs(dx), limbs(dy))
		switch {
		case k < 0 && dx+2 <= dy+uint64(-k) || k >= 0 && dx+uint64(k)+2 <= dy:
			return lower + 1
		case k < 0 && uint64(-k) >= dx:
			return dx + dy + lower
		}
		dn, reads := dx+uint64(max(k, 0)), dx+uint64(max(k, 0))
		if k < 0 {
			dn, reads = dx-uint64(-k), dx
		}
		tn, m := limbs(dn), limbs(dy)
		charge := reads + dy + lower
		if tn >= m {
			charge += 2*(tn-m+1)*(m+1) + 2*(tn+m+1)
		}
		return charge
	}
	bound := func(n uint64) uint64 { // allocBound, restated
		if n <= 32<<10 {
			return (n + n/4 + 16 + 15) &^ 15
		}
		return (n + 8191) &^ 8191
	}
	holder := uint64(3*strconv.IntSize/8 + 36)
	publish := func(digits uint64) uint64 {
		if digits <= 38 {
			return 0
		}
		if count := limbs(digits); count > 9 {
			return bound(holder) + bound(4*count)
		}
		return bound(holder)
	}
	for range 2000 {
		dx, dy := uint64(1+r.IntN(300)), uint64(1+r.IntN(120))
		ex, ey := int32(r.IntN(60)-30), int32(r.IntN(60)-30)
		x, y := Shape{Digits: dx, Exponent: ex}, Shape{Digits: dy, Exponent: ey}
		// Exact Div: divided at kMax = ⌈3.322·dy⌉ fractional digits.
		kMax := (dy*3322 + 999) / 1000
		c, err := EstimateDiv(x, y, Context{})
		if err != nil {
			t.Fatal(err)
		}
		n := dx + kMax - dy + 1
		if c.WorkUnits != divCharge(dx, dy, int64(kMax))+2*n+1 || c.Digits != n {
			t.Fatalf("div %d/%d: estimate %+v, closed form N %d", dx, dy, c, n)
		}
		// Unguarded DivWithContext: divided at k = p − dx + dy.
		p := uint64(1 + r.IntN(60))
		ctx, _ := NewContext(uint32(p), TiesToEven, nil, 0)
		c, err = EstimateDiv(x, y, ctx)
		if err != nil {
			t.Fatal(err)
		}
		if k := int64(p) - int64(dx) + int64(dy); c.WorkUnits != divCharge(dx, dy, k)+2*p+1 || c.Digits != p {
			t.Fatalf("div-context %d/%d p=%d: estimate %+v", dx, dy, p, c)
		}
		// Add's publication heap (inline up to 38 digits, one fused holder
		// up to nine limbs, a holder and a slice above).
		c, _ = EstimateAdd(x, Shape{Digits: dy, Exponent: ex}, Context{})
		if c.HeapBytes != publish(c.Digits) {
			t.Fatalf("add %d+%d: HeapBytes %d, closed form %d", dx, dy, c.HeapBytes, publish(c.Digits))
		}
		// FromRat's worst case over every denominator of bd bits.
		bn, bd := uint64(1+r.IntN(900)), uint64(1+r.IntN(900))
		c, err = EstimateFromRat(bn, bd, Context{})
		if err != nil {
			t.Fatal(err)
		}
		// ⌊bd·log5 2⌋ with the estimator's constant, in exact arithmetic.
		bMax := new(big.Int).Quo(new(big.Int).Mul(new(big.Int).SetUint64(bd), big.NewInt(430676558073393051)), big.NewInt(1_000_000_000_000_000_000)).Uint64()
		m := max(bMax, bd-1)
		wn, wd, wm := words(bn), words(bd), powerWords(m)
		u := envelope(64 * (wn + wm))
		charge := bMax*(wd+1) + division(wn, wd) + power(wm) + wn*wm + u*limbs(u) + wn + wd
		if c.WorkUnits != charge+2*u+1 || c.Digits != u {
			t.Fatalf("from-rat %d/%d bits: estimate %+v, closed form B %d U %d", bn, bd, c, charge, u)
		}
		// Rat of a fractional shape: the larger of z = 0 and z = 1.
		d, j := uint64(2+r.IntN(200)), uint64(1+r.IntN(200))
		c, err = EstimateRat(Shape{Digits: d, Exponent: -int32(j)})
		if err != nil {
			t.Fatal(err)
		}
		rat := func(z uint64) uint64 {
			nd, jj := d-z, j-z
			wc := words(nd*332193/100000 + 1)
			wj := powerWords(jj)
			tt := 2 * limbs(nd)
			strip := uint64(0)
			if z > 0 {
				strip = d
			}
			return tt*tt + tt + (jj+1)*wc + power(wj) + wj + strip
		}
		if want := max(rat(0), rat(1)); c.WorkUnits != want || c.Digits != max(d, j+1) || c.InputDigits != d {
			t.Fatalf("rat %d digits e=-%d: estimate %+v, closed form W %d", d, j, c, want)
		}
		// NewTwosComplement over the raw bit length.
		nb := 1 + r.IntN(300)
		c, _ = EstimateNewTwosComplement(uint64(nb))
		if uu := envelope(8 * uint64(nb)); c.Digits != uu || c.WorkUnits != (2*limbs(uu))*(2*limbs(uu))+2*limbs(uu) {
			t.Fatalf("twos-complement %d bytes: %+v", nb, c)
		}
		// Parse and JSON: every byte may be a digit.
		c, _ = EstimateParse(uint64(nb), Context{})
		if c.Digits != uint64(nb) || c.InputBytes != uint64(nb) || c.WorkUnits != 0 {
			t.Fatalf("parse %d bytes: %+v", nb, c)
		}
		c, _ = EstimateParseJSON(uint64(nb), Budget{})
		if c.Digits != uint64(nb) || c.InputBytes != uint64(nb) {
			t.Fatalf("parse-json %d bytes: %+v", nb, c)
		}
	}
	// Scan kinds: text work = bytes; int64 work 1 and its digits; float64
	// work 87 per pass and its exact digits.
	c, _ := EstimateScan("123.4500", Budget{})
	if c.WorkUnits != 8 || c.InputBytes != 8 || c.Digits != 8 {
		t.Fatalf("scan text: %+v", c)
	}
	c, _ = EstimateScan(int64(-120034), Budget{})
	if c.WorkUnits != 1 || c.Digits != 6 {
		t.Fatalf("scan int64: %+v", c)
	}
	c, _ = EstimateScan(0.1, Budget{})
	if c.WorkUnits != 5*87 || c.Digits != 55 { // 0.1 = 3602879701896397·2^−55
		t.Fatalf("scan float64: %+v", c)
	}
	var d Decimal
	if err := d.ScanWithBudget(int64(-120034), Budget{MaxWork: 1, MaxDigits: 5}); err == nil {
		t.Fatal("scan int64 admitted below its digit estimate")
	}
}

// TestEstimateHeapSlack pins the heap slack: on slow-result witnesses the
// heap estimate stays within 2× the measured cumulative allocation plus 128 B
// (allocBound's envelope over size classes), so a dropped planned allocation
// or a double count is caught.
func TestEstimateHeapSlack(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 15))
	// A quoted JSON token with escapes decodes into its own buffer before a
	// syntax error copies the decoded text: both are in HeapBytes.
	for _, n := range []int{100, 1000, 20000} {
		raw := []byte(`"\u0031` + strings.Repeat("7", n) + `x"`)
		c, err := EstimateParseJSON(uint64(len(raw)), Budget{})
		if err != nil {
			t.Fatal(err)
		}
		actual := coldAllocatedWithin(func() { _, _ = ParseJSONWithBudget(raw, Budget{}) }, c.HeapBytes)
		if actual > c.HeapBytes {
			t.Fatalf("escaped JSON of %d bytes: allocated %d > HeapBytes %d", len(raw), actual, c.HeapBytes)
		}
	}
	for _, n := range []uint64{40, 81, 82, 200, 1000, 9000} {
		x, y := shapedDecimal(r, n, 0, false, '9'), shapedDecimal(r, n/2+1, 0, false, '9')
		text := x.String()
		invalid := []byte(text[:len(text)-1] + "x")
		for name, pair := range map[string]struct {
			est func() (Cost, error)
			run func() error
		}{
			"add": {func() (Cost, error) { return EstimateAdd(x.Shape(), y.Shape(), Context{}) }, func() error { _, _, err := x.AddWithContext(y, Context{}); return err }},
			"mul": {func() (Cost, error) { return EstimateMul(x.Shape(), y.Shape(), Context{}) }, func() error { _, _, err := x.MulWithContext(y, Context{}); return err }},
			"quantize": {func() (Cost, error) { return EstimateQuantize(x.Shape(), -5, Context{}) }, func() error {
				_, _, err := x.QuantizeWithContext(-5, Context{})
				return err
			}},
			// Parse's bound also covers a syntax error of byte input, whose
			// Error copies the text: that is its worst witness.
			"parse": {func() (Cost, error) { return EstimateParse(uint64(len(text)), Context{}) }, func() error {
				_, err := Parse(invalid)
				return err
			}},
		} {
			c, err := pair.est()
			if err != nil {
				t.Fatal(err)
			}
			actual := coldAllocatedWithin(func() { _ = pair.run() }, c.HeapBytes)
			if c.HeapBytes > 2*actual+128 || actual > c.HeapBytes {
				t.Fatalf("%s %d digits: HeapBytes %d vs measured %d beyond the documented slack", name, n, c.HeapBytes, actual)
			}
		}
	}
}

// TestEstimateQuantizeCarryAtPrecision checks that a result of exactly p
// digits in a mode that can carry is not a predicted refusal (only an
// all-nines value carries past p, which the shape cannot decide), and the
// estimate admits the values that do not carry.
func TestEstimateQuantizeCarryAtPrecision(t *testing.T) {
	ctx, _ := NewContext(4, TiesToEven, nil, 0)
	x := MustParse("12345")
	c, err := EstimateQuantize(x.Shape(), 1, ctx)
	if err != nil {
		t.Fatalf("a 4-digit result at p = 4 predicted as %v", err)
	}
	if _, _, err := x.QuantizeWithContext(1, ctx.WithBudget(c.Budget())); err != nil {
		t.Fatalf("12345 → exponent 1 refused under %+v: %v", c, err)
	}
	if _, _, err := MustParse("99999").QuantizeWithContext(1, ctx.WithBudget(Budget{})); !errors.Is(err, ErrInvalidOperation) {
		t.Fatalf("99999 carries past p: %v", err)
	}
}

// TestEstimateRoundingBound checks estimate soundness, attainment and closed
// form for the rounding estimators: RoundToPrecision is context Add of a zero
// at the value's exponent (attained exactly when the value rounds), and
// RoundToMultiple is the DivToExponent estimate completed with the Mul charge
// over the digit envelope, attained within the Div family's two digits of
// slack plus the Mul charge of those digits, except when the quotient rounds
// to zero (one digit), which the shape cannot predict.
func TestEstimateRoundingBound(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 3))
	ctx, err := NewContext(16, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, digits := range []uint64{1, 5, 16, 17, 38, 39, 81, 200} {
		x := shapedDecimal(r, digits, int32(r.IntN(40)-20), r.IntN(2) == 0, 0)
		c, err := EstimateRoundToPrecision(x.Shape(), ctx)
		if err != nil {
			t.Fatal(err)
		}
		o := checkArithmeticEstimate(t, fmt.Sprintf("round-precision %d", digits), c, func(b Budget) error {
			_, _, err := x.RoundToPrecisionWithContext(ctx.WithBudget(b))
			return err
		})
		if digits > 16 && (o.work != c.WorkUnits || o.digits != c.Digits) {
			t.Fatalf("round-precision %d: estimate %+v not attained (%+v)", digits, c, o)
		}
		if want := digits + 2*min(digits, 16) + 1; c.WorkUnits != want || c.Digits != min(digits, 16) {
			t.Fatalf("round-precision %d: %+v, want the closed form W = d + 2·min(p, d) + 1 = %d", digits, c, want)
		}
		for _, m := range []Decimal{MustParse("0.05"), MustParse("25"), MustParse("0.0001234567")} {
			c, err := EstimateRoundToMultiple(x.Shape(), m.Shape())
			if err != nil {
				t.Fatal(err)
			}
			label := fmt.Sprintf("round-multiple %d to %s", digits, m)
			o := checkArithmeticEstimate(t, label, c, func(b Budget) error {
				_, _, err := x.RoundToMultipleWithBudget(m, TiesToEven, b)
				return err
			})
			dm := m.CoefficientDigits()
			// Closed form: the quotient estimate plus the multiple's digits.
			if q, _ := EstimateDivToExponent(x.Shape(), Shape{Digits: dm}, m.Exponent()); c.Digits != q.Digits+dm {
				t.Fatalf("%s: digits %d, want the envelope %d + %d", label, c.Digits, q.Digits, dm)
			}
			// A quotient that rounds to zero publishes one digit; the shape
			// cannot tell, so that case is sound but outside attainment.
			if o.digits > 1 && (c.Digits > o.digits+2 || c.WorkUnits > o.work+4+2*(2+(dm-1)/9)+4) {
				t.Fatalf("%s: estimate %+v beyond the documented slack of observed %+v", label, c, o)
			}
		}
	}
	// Guards that make an overflow reachable give N = p, attained by the Bmax
	// result; precision 0 is the exact identity charge W = d.
	guarded, err := NewContext(3, TiesToEven, &ExponentGuards{Emin: -10, Emax: 10}, 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, text := range []string{"9.996E+10", "1.5E+11", "1.2E+3"} {
		x := MustParse(text)
		c, err := EstimateRoundToPrecision(x.Shape(), guarded)
		if err != nil {
			t.Fatal(err)
		}
		o := checkArithmeticEstimate(t, "guarded round-precision "+text, c, func(b Budget) error {
			_, _, err := x.RoundToPrecisionWithContext(guarded.WithBudget(b))
			return err
		})
		if text != "1.2E+3" && (c.Digits != 3 || o.digits != 3 || o.work != c.WorkUnits) {
			t.Fatalf("guarded %s: estimate %+v, observed %+v, want N = p attained", text, c, o)
		}
	}
	for _, text := range []string{"123.456", "0E-4", "98765432109876543210987654321098765432109876"} {
		x := MustParse(text)
		c, err := EstimateRoundToPrecision(x.Shape(), Context{})
		if err != nil {
			t.Fatal(err)
		}
		o := checkArithmeticEstimate(t, "precision-0 round-precision "+text, c, func(b Budget) error {
			_, _, err := x.RoundToPrecisionWithContext(Context{}.WithBudget(b))
			return err
		})
		if d := max(x.CoefficientDigits(), 1); c.WorkUnits != d || o.work != d || c.Digits != d {
			t.Fatalf("precision 0 %s: estimate %+v, observed %+v, want W = N = %d", text, c, o, d)
		}
	}
	for _, m := range []Shape{{}, {Digits: 1, Negative: true}} {
		if _, err := EstimateRoundToMultiple(Shape{Digits: 3}, m); !errors.Is(err, ErrInvalidOperation) {
			t.Fatalf("EstimateRoundToMultiple(m=%+v): %v", m, err)
		}
	}
}

// TestEstimateSumBound checks estimate soundness, attainment and closed form
// for EstimateSum: over random operand lists (inline, limb-held, zero, far
// apart) the estimate admits, equals the smallest admitting work and digit
// caps (the tariff and the envelope are both functions of the shape), and
// bounds the cold-pool allocation; the empty sum costs nothing.
func TestEstimateSumBound(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 13))
	for range 200 {
		values := sumOperands(r, 1+r.IntN(40), []int{0, 6, 19, 40, 400}[r.IntN(5)])
		c, err := EstimateSum(ShapeOfSum(values...))
		if err != nil {
			t.Fatal(err)
		}
		o := checkArithmeticEstimate(t, fmt.Sprintf("sum of %d", len(values)), c, func(b Budget) error {
			_, err := SumWithBudget(values, b)
			return err
		})
		if o.work != c.WorkUnits || o.digits != c.Digits {
			t.Fatalf("sum of %d: estimate %+v not attained (%+v)", len(values), c, o)
		}
		// Heap slack: at most 2× measured + 128 B.
		if c.HeapBytes > 2*o.heap+128 {
			t.Fatalf("sum of %d: HeapBytes %d beyond the slack of measured %d", len(values), c.HeapBytes, o.heap)
		}
	}
	// k = 1 has no carry digit: its envelope is the operand's own span.
	if c, err := EstimateSum(ShapeOfSum(MustParse("12.50"))); err != nil || c.Digits != 4 || c.WorkUnits != 1+4+2 {
		t.Fatalf("single operand: %+v %v", c, err)
	}
	if c, err := EstimateSum(ShapeOfSum()); err != nil || c != (Cost{}) {
		t.Fatalf("empty sum: %+v %v", c, err)
	}
}

// TestEstimateSqrtBound checks estimate soundness, attainment and closed form
// for EstimateSqrt, bare and in context: over a size sweep, even and odd
// exponents, guards and precisions, each estimate admits its call, equals the
// closed form d + I·D + t(R)² (plus 2p + 1 in context), is attained exactly
// in work and digits (by perfect squares bare, and by inexact roots in
// context), and bounds the cold-pool allocation. A negative shape is
// ErrInvalidOperation, a zero shape costs (1, 1) bare and (4, 1) in context,
// and a charge that leaves uint64 is refused.
func TestEstimateSqrtBound(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 14))
	for _, digits := range sweepDigits() {
		if digits > 2000 {
			continue
		}
		root := randomDigits(r, int(1+digits/2))
		for _, e := range []int32{-12, -7, 0, 3, 40} {
			c := new(big.Int).Mul(root, root)
			if e%2 != 0 {
				c.Mul(c, big.NewInt(10))
			}
			v := sqrtDecimal(c, int64(e))
			est, err := EstimateSqrt(v.Shape(), Context{})
			if err != nil {
				t.Fatal(err)
			}
			d := v.CoefficientDigits() + uint64(boolInt(e%2 != 0))
			if want := sqrtClosedCharge(d, (d+1)/2); est.WorkUnits != want || est.Digits != (d+1)/2 {
				t.Fatalf("EstimateSqrt(%+v) = %+v, closed form W=%d N=%d", v.Shape(), est, want, (d+1)/2)
			}
			o := checkArithmeticEstimate(t, fmt.Sprintf("sqrt of %d digits", d), est, func(b Budget) error {
				_, _, err := v.SqrtWithContext(Context{}.WithBudget(b))
				return err
			})
			if o.work != est.WorkUnits || o.digits != est.Digits {
				t.Fatalf("sqrt of %d digits: estimate %+v not attained (%+v)", d, est, o)
			}
		}
	}
	guards := &ExponentGuards{Emin: -30, Emax: 30}
	attained := 0
	for _, p := range []uint32{1, 2, 8, 9, 16, 34, 38, 80, 81, 82, 200} {
		for _, digits := range []uint64{1, 5, 38, 81, 300} {
			for _, e := range []int32{-70, -9, 0, 1, 25} {
				v := shapedDecimal(r, digits, e, false, 0)
				for _, g := range []*ExponentGuards{nil, guards} {
					ctx, err := NewContext(p, TowardZero, g, 0)
					if err != nil {
						t.Fatal(err)
					}
					est, err := EstimateSqrt(v.Shape(), ctx)
					if err != nil {
						t.Fatal(err)
					}
					if want := sqrtClosedCharge(digits, uint64(p)+1) + 2*uint64(p) + 1; est.WorkUnits != want || est.Digits != uint64(p) {
						t.Fatalf("EstimateSqrt(%+v, p=%d) = %+v, closed form W=%d", v.Shape(), p, est, want)
					}
					run := func(b Budget) error { _, _, err := v.SqrtWithContext(ctx.WithBudget(b)); return err }
					o := checkArithmeticEstimate(t, fmt.Sprintf("sqrt p=%d of %d digits at %d", p, digits, e), est, run)
					_, conditions, _ := v.SqrtWithContext(ctx)
					if conditions&Inexact != 0 && conditions&Subnormal == 0 {
						if o.work != est.WorkUnits || o.digits != est.Digits {
							t.Fatalf("sqrt p=%d of %d digits at %d: estimate %+v not attained (%+v)", p, digits, e, est, o)
						}
						attained++
					}
				}
			}
		}
	}
	if attained < 300 {
		t.Fatalf("vacuous attainment: %d inexact context roots", attained)
	}
	for _, tc := range []struct {
		est  func() (Cost, error)
		code ErrorCode
	}{
		{func() (Cost, error) { return EstimateSqrt(Shape{Digits: 3, Negative: true}, Context{}) }, ErrInvalidOperation},
		{func() (Cost, error) {
			return EstimateSqrt(Shape{Digits: 3, Negative: true}, Decimal64Context())
		}, ErrInvalidOperation},
		{func() (Cost, error) { return EstimateSqrt(Shape{Digits: math.MaxUint64 / 2}, Context{}) }, ErrInsufficientStorage},
		{func() (Cost, error) {
			return EstimateSqrt(Shape{Digits: math.MaxUint64 - 10}, Decimal64Context())
		}, ErrInsufficientStorage},
	} {
		if _, err := tc.est(); !isErrorCode(err, tc.code) {
			t.Fatalf("refusal: %v, want %v", err, tc.code)
		}
	}
	for _, tc := range []struct {
		name string
		est  func() (Cost, error)
		run  func(Budget) error
		work uint64
	}{
		{"bare", func() (Cost, error) { return EstimateSqrt(MustParse("-0E-9").Shape(), Context{}) },
			func(b Budget) error {
				_, _, err := MustParse("-0E-9").SqrtWithContext(Context{}.WithBudget(b))
				return err
			}, 1},
		{"context", func() (Cost, error) { return EstimateSqrt(MustParse("0E-9").Shape(), Decimal32Context()) },
			func(b Budget) error {
				_, _, err := MustParse("0E-9").SqrtWithContext(Decimal32Context().WithBudget(b))
				return err
			}, 4},
	} {
		c, err := tc.est()
		if err != nil || c.WorkUnits != tc.work || c.Digits != 1 {
			t.Fatalf("zero %s: %+v %v", tc.name, c, err)
		}
		if o := checkArithmeticEstimate(t, "zero "+tc.name, c, tc.run); o.work != tc.work || o.digits != 1 {
			t.Fatalf("zero %s: attained %+v", tc.name, o)
		}
	}
}

// powTestContextEstimate is EstimatePow's worst case restated: every level
// from w = p+1+⌈log10(2m)⌉+2, doubling while w < m·d, then the exact tariff
// with every partial power c^k at k·d digits (plus one reciprocal division
// for n < 0), and the finisher's 2p+1.
func powTestContextEstimate(d, m, p uint64, reciprocal bool) uint64 {
	g := uint64(2)
	for q := uint64(1); q < 2*m; q *= 10 {
		g++
	}
	var total uint64
	for w := p + 1 + g; w < m*d; w *= 2 {
		total += powTestLevel(w, m, p, reciprocal)
	}
	total += powTestSteps(m, d, func(k uint64) uint64 { return k * d })
	if reciprocal {
		total += powTestDiv(m*d, p)
	}
	return total + 2*p + 1
}

// powTestReciprocalPlan restates the 2^a candidate of EstimatePow for
// n = −m on a d-digit shape: the power 5^M, M = ⌊3.322·d⌋·m, its digits
// ⌊M·log10 5⌋+1 and the monotone plan bound's buffer limbs, the largest of
// 2·t(D(⌊M/2^(i+1)⌋)) and t(D(⌊M/2^i⌋))+1 over the steps.
func powTestReciprocalPlan(d, m uint64) (exponent, digits, limbs uint64) {
	l, _, _ := new(big.Float).SetPrec(300).Parse("0.698970004336018804786261105275506973231810118537891458689", 10)
	size := func(k uint64) uint64 {
		f, _ := new(big.Float).SetPrec(300).Mul(l, new(big.Float).SetUint64(k)).Int(nil)
		return f.Uint64() + 1
	}
	M := d * 3322 / 1000 * m
	limbs = 1
	top := 63
	for M>>uint(top) == 0 {
		top--
	}
	for i := top - 1; i >= 0; i-- {
		limbs = max(limbs, 2*powTestLimbs(size(M>>uint(i+1))), powTestLimbs(size(M>>uint(i)))+1)
	}
	return M, size(M), limbs
}

// powTestReciprocalEstimate restates EstimatePow for n = −m ≤ −2: the
// worse of c = 2^a (the test t(d)·(1 + ⌊a_max/29⌋), a_max = ⌊3.322·d⌋,
// then the power 5^(a_max·m)) and c = 5^b (t(d)·(1 + ⌊b_max/12⌋), b_max =
// ⌊1.431·d⌋, then 2^(b_max·m)), each power charged by the monotone plan
// bound Σ over the steps i from the end of the square of the partial power
// ⌊M/2^(i+1)⌋ and the multiply of ⌊M/2^i⌋, with digits ⌊k·log10 base⌋+1
// from 60-digit constants.
func powTestReciprocalEstimate(d, m uint64) (work, digits uint64) {
	logs := map[uint64]string{
		5: "0.698970004336018804786261105275506973231810118537891458689",
		2: "0.301029995663981195213738894724493026768189881462108541310",
	}
	for _, tc := range []struct{ base, max, step uint64 }{{5, d * 3322 / 1000, 29}, {2, d * 1431 / 1000, 12}} {
		l, _, _ := new(big.Float).SetPrec(300).Parse(logs[tc.base], 10)
		size := func(k uint64) uint64 {
			f, _ := new(big.Float).SetPrec(300).Mul(l, new(big.Float).SetUint64(k)).Int(nil)
			return f.Uint64() + 1
		}
		M := tc.max * m
		total := powTestLimbs(d) * (1 + tc.max/tc.step)
		top := 63
		for M>>uint(top) == 0 {
			top--
		}
		for i := top - 1; i >= 0; i-- {
			sq, mul := size(M>>uint(i+1)), size(M>>uint(i))
			total += powTestLimbs(sq)*powTestLimbs(sq) + 2*sq + powTestLimbs(mul) + mul + 1
		}
		work, digits = max(work, total), max(digits, size(M))
	}
	return work, digits
}

// TestEstimatePowBound checks estimate soundness, attainment and closed form
// for EstimatePow:
//   - bare n ≥ 2: the closed form (the exact tariff at k·d digits per
//     partial power, N = n·d) admits every value of the shape, is attained
//     by all-nines coefficients whose partial powers have k·d digits, and
//     its digit slack over the result is below n (|n|·d − (Dlo + n·z) ≤
//     n − 1, plus the bracket's one digit);
//   - bare n ≤ −2: the powers of two with the most digits for the shape
//     (8, 64, 512, 8192) are admitted with their digits attained, and the
//     work slack of the monotone plan bound is logged;
//   - context: the closed form admits every value, and the all-nines
//     operand forced through every level to the exact fallback by the
//     test seam attains it exactly, in work and digits;
//   - |n| ≤ 1, zeros and range refusals follow the named rows.
func TestEstimatePowBound(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 49))
	attained := 0
	for _, digits := range []uint64{1, 2, 5, 9, 10, 19, 20, 38, 81, 200} {
		for _, n := range []int32{2, 3, 7, 16, 37} {
			m := uint64(n)
			for _, kind := range []string{"nines", "random", "zeros"} {
				v := shapedDecimal(r, digits, -2, false, 0)
				if kind == "nines" {
					v = shapedDecimal(r, digits, -2, false, '9')
				}
				if kind == "zeros" && digits > 1 {
					v = MustParse(shapedDecimal(r, digits/2, 0, false, 0).String() + strings.Repeat("0", int(digits-digits/2)) + "E-2")
				}
				est, err := EstimatePow(v.Shape(), n, Context{})
				if err != nil {
					t.Fatal(err)
				}
				if want := powTestSteps(m, digits, func(k uint64) uint64 { return k * digits }) + powTestLimbs(digits); est.WorkUnits != want || est.Digits != m*digits {
					t.Fatalf("EstimatePow(%+v, %d) = %+v, closed form W=%d N=%d", v.Shape(), n, est, want, m*digits)
				}
				label := fmt.Sprintf("%s %d digits ^%d", kind, digits, n)
				o := checkArithmeticEstimate(t, label, est, func(b Budget) error { _, _, err := v.PowWithContext(n, Context{}.WithBudget(b)); return err })
				c, _ := divOracleParts(t, v)
				stripped, _ := powStripped(c)
				// n·d − (D + n·z) = n·digits(c) − D ≤ n − 1.
				if est.Digits-o.digits > m-1 {
					t.Fatalf("%s: digit slack %d above n−1", label, est.Digits-o.digits)
				}
				if kind == "nines" && powActualDigits(stripped)(m) == m*digits {
					// Attained but for the scan, which reads one limb of
					// the t(d) the shape allows (slack t(d) − 1).
					if o.work != est.WorkUnits-(powTestLimbs(digits)-1) || o.digits != est.Digits {
						t.Fatalf("%s: estimate %+v not attained (%+v)", label, est, o)
					}
					attained++
				}
			}
		}
	}
	if attained < 20 {
		t.Fatalf("vacuous bare attainment: %d", attained)
	}
	for _, in := range []string{"8", "64", "512", "8192", "0.08", "-6.4E+5"} {
		for _, n := range []int32{-2, -3, -10} {
			v := MustParse(in)
			est, err := EstimatePow(v.Shape(), n, Context{})
			if err != nil {
				t.Fatal(err)
			}
			if work, digits := powTestReciprocalEstimate(v.Shape().Digits, powMagnitude(n)); est.WorkUnits != work+powTestLimbs(v.Shape().Digits) || est.Digits != digits {
				t.Fatalf("EstimatePow(%+v, %d) = %+v, closed form W=%d N=%d", v.Shape(), n, est, work, digits)
			}
			o := checkArithmeticEstimate(t, fmt.Sprintf("(%s)^%d", in, n), est, func(b Budget) error { _, _, err := v.PowWithContext(n, Context{}.WithBudget(b)); return err })
			if o.digits != est.Digits {
				t.Fatalf("(%s)^%d: digits %d not attained (%+v)", in, n, o.digits, est)
			}
			t.Logf("(%s)^%d: work slack %.2f", in, n, float64(est.WorkUnits)/float64(o.work))
		}
	}
	guards := &ExponentGuards{Emin: -400, Emax: 400}
	contextAttained := 0
	for _, p := range []uint32{1, 7, 16, 34} {
		for _, digits := range []uint64{1, 3, 5, 20} {
			for _, n := range []int32{2, 3, 13, 100, -3, -17} {
				m := powMagnitude(n)
				for _, g := range []*ExponentGuards{nil, guards} {
					ctx, err := NewContext(p, TowardZero, g, 0)
					if err != nil {
						t.Fatal(err)
					}
					nines := shapedDecimal(r, digits, -1, false, '9')
					est, err := EstimatePow(nines.Shape(), n, ctx)
					if err != nil {
						t.Fatal(err)
					}
					if want := powTestContextEstimate(digits, m, uint64(p), n < 0) + powTestLimbs(digits); est.WorkUnits != want || est.Digits != uint64(p) {
						t.Fatalf("EstimatePow(%+v, %d, p=%d) = %+v, closed form W=%d", nines.Shape(), n, p, est, want)
					}
					for _, v := range []Decimal{nines, shapedDecimal(r, digits, -1, true, 0)} {
						checkArithmeticEstimate(t, fmt.Sprintf("(%v)^%d p=%d", v, n, p), est, func(b Budget) error {
							_, _, err := v.PowWithContext(n, ctx.WithBudget(b))
							return err
						})
					}
					c, _ := divOracleParts(t, nines)
					_, conditions, err := nines.PowWithContext(n, ctx)
					if err != nil || conditions&Inexact == 0 || conditions&(Subnormal|Overflow) != 0 || powActualDigits(c)(m) != m*digits {
						continue
					}
					// The seam's counter lives outside the measured calls.
					seam := &powCount{escalate: true, levels: make([]uint64, 0, 64)}
					o := checkArithmeticEstimate(t, fmt.Sprintf("forced (%v)^%d p=%d", nines, n, p), est, func(b Budget) error {
						seam.levels = seam.levels[:0]
						_, _, err := nines.powContext(n, ctx, b.arith(), "PowWithContext", seam)
						return err
					})
					if o.work != est.WorkUnits-(powTestLimbs(digits)-1) || o.digits != est.Digits {
						t.Fatalf("forced (%v)^%d p=%d: estimate %+v not attained (%+v)", nines, n, p, est, o)
					}
					contextAttained++
				}
			}
		}
	}
	if contextAttained < 40 {
		t.Fatalf("vacuous context attainment: %d", contextAttained)
	}
	// Heap beyond the 160-limb stack scratch: pinned to restated closed
	// forms, since allocBound's envelope hides a single buffer from a
	// cold-pool measurement. (1) The bare reciprocal of a 1,506-digit c =
	// 2^5000: the test's copy of c (168 limbs) plus two product buffers of
	// the plan bound of 5^(a_max·2), a_max = 5002, and the published result.
	// (2) The context exact fallback of a 1,501-digit operand with a trailing
	// zero (z mod 9 ≠ 0), forced through every level: each level's buffers,
	// the exact plan's buffers, the stripped copy of c and the padded result.
	heapOf := func(limbs uint64) uint64 {
		if limbs <= 160 {
			return 0
		}
		return allocBound(new(costTally), 4*limbs)
	}
	big2 := powDecimal(new(big.Int).Lsh(big.NewInt(1), 5000), 0)
	est, err := EstimatePow(big2.Shape(), -2, Context{})
	if err != nil {
		t.Fatal(err)
	}
	checkArithmeticEstimate(t, "2^5000 ^-2", est, func(b Budget) error { _, _, err := big2.PowWithContext(-2, Context{}.WithBudget(b)); return err })
	_, digits5, limbs5 := powTestReciprocalPlan(1506, 2)
	var tally costTally
	if want := heapOf(powTestLimbs(1506)) + heapOf(2*(limbs5+1)) + publishBytes(&tally, digits5, powTestLimbs(digits5)); est.HeapBytes != want {
		t.Fatalf("EstimatePow(2^5000, -2) heap %d, closed form %d", est.HeapBytes, want)
	}
	zeroed := MustParse(strings.Repeat("9", 1500) + "0")
	ctx34 := mustContext(t, 34, TowardZero)
	est, err = EstimatePow(zeroed.Shape(), 2, ctx34)
	if err != nil {
		t.Fatal(err)
	}
	seam := &powCount{escalate: true, levels: make([]uint64, 0, 64)}
	checkArithmeticEstimate(t, "forced 1501-digit ^2", est, func(b Budget) error {
		seam.levels = seam.levels[:0]
		_, _, err := zeroed.powContext(2, ctx34, b.arith(), "PowWithContext", seam)
		return err
	})
	var levelHeap uint64
	for w := uint64(34 + 1 + 3); w < 2*1501; w *= 2 {
		tw := powTestLimbs(w)
		levelHeap += heapOf(4*(tw+1) + 2*tw + 1)
	}
	// m = 2: one squaring of c at 1,501 digits, 2·t(1501) = 334 limbs.
	exactLimbs := 2*(334+1) + powTestLimbs(1501) + powTestLimbs(34) + 1
	if want := levelHeap + heapOf(exactLimbs); est.HeapBytes != want {
		t.Fatalf("EstimatePow(1501 digits, 2, p=34) heap %d, closed form %d", est.HeapBytes, want)
	}
	// n = 0 under guards whose Emax < 0, where 1 overflows to Bmax of p
	// digits, costs contextFinalCharge(1, p) and Bmax's publication, not one
	// digit at W = 4.
	for _, p := range []uint32{4, 40, 100} {
		ctx, err := NewContext(p, TiesToEven, &ExponentGuards{Emin: -62, Emax: -38}, 0)
		if err != nil {
			t.Fatal(err)
		}
		v := MustParse("3162277660168379430")
		est, err := EstimatePow(v.Shape(), 0, ctx)
		work, _ := contextFinalCharge(1, uint64(p))
		var tally costTally
		if heap := publishBytes(&tally, uint64(p), powTestLimbs(uint64(p))); err != nil || est.WorkUnits != work || est.Digits != uint64(p) || est.HeapBytes != heap {
			t.Fatalf("n=0 with 1 overflowing, p=%d: %+v %v, want W=%d N=%d heap %d", p, est, err, work, p, heap)
		}
		o := checkArithmeticEstimate(t, fmt.Sprintf("n=0 overflow p=%d", p), est, func(b Budget) error {
			_, _, err := v.PowWithContext(0, ctx.WithBudget(b))
			return err
		})
		if o.work != est.WorkUnits || o.digits != est.Digits {
			t.Fatalf("n=0 overflow p=%d: estimate %+v not attained (%+v)", p, est, o)
		}
	}
	x := Shape{Digits: 12, Exponent: -3, Negative: true}
	for _, tc := range []struct {
		name      string
		got, want func() (Cost, error)
	}{
		{"n=1", func() (Cost, error) { return EstimatePow(x, 1, Context{}) }, func() (Cost, error) { return EstimateRoundToPrecision(x, Context{}) }},
		{"n=-1", func() (Cost, error) { return EstimatePow(x, -1, Context{}) }, func() (Cost, error) { return EstimateDiv(Shape{Digits: 1}, x, Context{}) }},
		{"ctx n=1", func() (Cost, error) { return EstimatePow(x, 1, Decimal64Context()) }, func() (Cost, error) { return EstimateRoundToPrecision(x, Decimal64Context()) }},
		{"ctx n=-1", func() (Cost, error) { return EstimatePow(x, -1, Decimal64Context()) }, func() (Cost, error) {
			return EstimateDiv(Shape{Digits: 1}, x, Decimal64Context())
		}},
		{"n=0", func() (Cost, error) { return EstimatePow(x, 0, Context{}) }, func() (Cost, error) { return Cost{WorkUnits: 1, Digits: 1}, nil }},
		{"ctx n=0", func() (Cost, error) { return EstimatePow(x, 0, Decimal64Context()) }, func() (Cost, error) { return Cost{WorkUnits: 4, Digits: 1}, nil }},
		{"zero", func() (Cost, error) { return EstimatePow(Shape{Exponent: 5}, 3, Context{}) }, func() (Cost, error) { return Cost{WorkUnits: 1, Digits: 1}, nil }},
		{"ctx zero", func() (Cost, error) { return EstimatePow(Shape{Exponent: 5}, 3, Decimal64Context()) }, func() (Cost, error) { return Cost{WorkUnits: 4, Digits: 1}, nil }},
		{"ctx p=0", func() (Cost, error) { return EstimatePow(x, 5, Context{}) }, func() (Cost, error) { return EstimatePow(x, 5, Context{}) }},
	} {
		got, err1 := tc.got()
		want, err2 := tc.want()
		if got != want || err1 != nil || err2 != nil {
			t.Fatalf("%s: %+v %v, want %+v %v", tc.name, got, err1, want, err2)
		}
	}
	for _, tc := range []struct {
		est  func() (Cost, error)
		code ErrorCode
	}{
		{func() (Cost, error) { return EstimatePow(Shape{}, -2, Context{}) }, ErrDivisionByZero},
		{func() (Cost, error) { return EstimatePow(Shape{}, -2, Decimal64Context()) }, ErrDivisionByZero},
		{func() (Cost, error) { return EstimatePow(Shape{Exponent: 1 << 30}, 4, Context{}) }, ErrExponentRange},
		{func() (Cost, error) { return EstimatePow(Shape{Digits: 3, Exponent: 1 << 30}, 4, Context{}) }, ErrExponentRange},
		{func() (Cost, error) {
			return EstimatePow(Shape{Exponent: -(1 << 30)}, 3, Decimal64Context())
		}, ErrExponentRange},
		{func() (Cost, error) { return EstimatePow(Shape{Digits: math.MaxUint64 / 4}, 3, Context{}) }, ErrInsufficientStorage},
		{func() (Cost, error) {
			return EstimatePow(Shape{Digits: math.MaxUint64 / 4}, -3, Decimal64Context())
		}, ErrInsufficientStorage},
		{func() (Cost, error) { return EstimatePow(Shape{Digits: 1 << 40}, -3, Context{}) }, ErrInsufficientStorage},
	} {
		if _, err := tc.est(); !isErrorCode(err, tc.code) {
			t.Fatalf("refusal: %v, want %v", err, tc.code)
		}
	}
}

// TestEstimateScanMathBig checks the math/big Scan estimates: constructor
// bounds plus the minimal magnitude-byte count, without inspecting binary
// float values.
func TestEstimateScanMathBig(t *testing.T) {
	for _, tc := range []struct {
		src   any
		bytes uint64
	}{
		{*big.NewInt(256), 2}, {big.NewInt(256), 2},
		{*big.NewRat(1, 256), 3}, {big.NewRat(1, 256), 3},
		{big.Int{}, 0}, {big.Rat{}, 1},
	} {
		bound, err := EstimateScan(tc.src, Budget{})
		if err != nil {
			t.Errorf("%T: %v", tc.src, err)
			continue
		}
		if bound.InputBytes != tc.bytes {
			t.Errorf("%T input bytes %d, want %d", tc.src, bound.InputBytes, tc.bytes)
		}
		var d Decimal
		if err := d.ScanWithBudget(tc.src, bound.Budget()); err != nil {
			t.Errorf("%T bound %+v: %v", tc.src, bound, err)
		}
		if n := testing.AllocsPerRun(20, func() { _, _ = EstimateScan(tc.src, Budget{}) }); n != 0 {
			t.Errorf("%T estimator allocations %g", tc.src, n)
		}
	}
	badInt := big.NewInt(1)
	badInt.Bits()[0] = 0
	badNum := big.NewRat(1, 2)
	badNum.Num().Bits()[0] = 0
	badDen := big.NewRat(1, 2)
	badDen.Denom().Bits()[0] = 0
	for _, src := range []any{badInt, *badInt, badNum, *badNum, badDen, *badDen} {
		if _, err := EstimateScan(src, Budget{}); !errors.Is(err, ErrConversionSyntax) {
			t.Errorf("malformed %T: %v", src, err)
		}
		if n := testing.AllocsPerRun(20, func() { _, _ = EstimateScan(src, Budget{}) }); n != 0 {
			t.Errorf("malformed estimator allocated %g", n)
		}
	}

	for _, src := range []any{big.Float{}, (*big.Float)(nil), (*big.Int)(nil), (*big.Rat)(nil)} {
		if _, err := EstimateScan(src, Budget{}); !errors.Is(err, ErrConversionSyntax) {
			t.Errorf("%T: %v", src, err)
		}
		if n := testing.AllocsPerRun(20, func() { _, _ = EstimateScan(src, Budget{}) }); n != 0 {
			t.Errorf("%T refusal allocations %g", src, n)
		}
	}
}

// TestEstimateScanMathBigBounds checks closed forms for 256 and 1/8, minimal
// admission on each axis, and cold-pool heap soundness.
func TestEstimateScanMathBigBounds(t *testing.T) {
	for _, tc := range []struct {
		src                 any
		work, digits, bytes uint64
	}{
		{big.NewInt(256), 6, 3, 2},
		// 1/8: a=3,bMax=0,wn=wd=wm=1; B=8+3+1+195+2=209,
		// N envelope=floor(128 log10(2))+1=39; W=209+79=288.
		{big.NewRat(1, 8), 288, 39, 2},
		{big.Rat{}, 4, 1, 1},
	} {
		c, err := EstimateScan(tc.src, Budget{})
		if err != nil || c.WorkUnits != tc.work || c.Digits != tc.digits || c.InputBytes != tc.bytes {
			t.Fatalf("%T: %+v %v", tc.src, c, err)
		}
	}
	for _, src := range []any{big.Int{}, new(big.Rat), big.NewInt(256), new(big.Int).Lsh(big.NewInt(1), 513), big.NewRat(1, 8), big.NewRat(3, 125), new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), 257))} {
		c, err := EstimateScan(src, Budget{})
		if err != nil {
			t.Fatal(err)
		}
		run := func(b Budget) error { var d Decimal; return d.ScanWithBudget(src, b) }
		if err := run(c.Budget()); err != nil {
			t.Fatalf("%T under bound: %v", src, err)
		}
		if heap := coldAllocatedWithin(func() { _ = run(c.Budget()) }, c.HeapBytes); heap > c.HeapBytes {
			t.Errorf("%T heap %d > %d", src, heap, c.HeapBytes)
		}
		for _, axis := range []string{"bytes", "digits", "work"} {
			bound := c.InputBytes
			if axis == "digits" {
				bound = c.Digits
			}
			if axis == "work" {
				bound = c.WorkUnits
			}
			if bound == 0 {
				continue
			}
			lo, hi := uint64(1), bound
			budget := func(n uint64) Budget {
				switch axis {
				case "bytes":
					return Budget{MaxInputBytes: n}
				case "digits":
					return Budget{MaxDigits: n}
				default:
					return Budget{MaxWork: n}
				}
			}
			for lo < hi {
				mid := (lo + hi) / 2
				if run(budget(mid)) == nil {
					hi = mid
				} else {
					lo = mid + 1
				}
			}
			if err := run(budget(lo)); err != nil {
				t.Fatal("no admission inside bound", axis, err)
			}
			if lo > 1 && !errors.Is(run(budget(lo-1)), ErrInsufficientStorage) {
				t.Fatal("boundary not discriminating", axis)
			}
		}
	}
}

// quoRemEstimate runs the estimator matching an operation and context.
func quoRemEstimate(x, y Shape, op intDivOp, ctx *Context) (Cost, error) {
	switch {
	case op == intDivQuo && ctx == nil:
		return EstimateQuo(x, y, Context{})
	case op == intDivQuo:
		return EstimateQuo(x, y, *ctx)
	case op == intDivRem && ctx == nil:
		return EstimateRem(x, y, Context{})
	case op == intDivRem:
		return EstimateRem(x, y, *ctx)
	case ctx == nil:
		return EstimateRemNear(x, y, Context{})
	}
	return EstimateRemNear(x, y, *ctx)
}

func quoRemRun(x, y Decimal, op intDivOp, ctx *Context) func(Budget) error {
	return func(b Budget) error {
		if ctx == nil {
			_, err := quoRemPublic(x, y, op, b)
			return err
		}
		_, _, err := quoRemContext(x, y, op, *ctx, b)
		return err
	}
}

// TestQuoRemEstimatesBound checks estimate soundness and attainment for the
// six integer-division estimators: over random operands on every path, bare
// and under contexts, each estimate admits its call and bounds its cold-pool
// allocation, and the observed smallest caps lie within the documented slack:
// Quo one digit and two work units; remainders Nenv−1 digits and 2(Nenv−1)
// units; at δ = 0 also the difference between the q = 0 and q ≠ 0 paths.
// Calls the shape cannot decide (Q = p+1 at δ = p, the remainder's
// adjusted-exponent guard) are skipped, and counted.
func TestQuoRemEstimatesBound(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 66))
	ctx128 := Decimal128Context()
	wide, err := NewContext(1000, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	checked, skipped := map[string]int{}, 0
	cases := 1500
	if testing.Short() {
		cases = 400
	}
	for i := range cases {
		x, y := quoRemPair(rng)
		if x.CoefficientDigits() > 120 || int64(x.Exponent())-int64(y.Exponent()) > 2000 && i%3 != 0 {
			continue
		}
		op := quoRemOps[rng.IntN(3)]
		var ctx *Context
		switch rng.IntN(3) {
		case 1:
			ctx = &ctx128
		case 2:
			ctx = &wide
		}
		c, err := quoRemEstimate(x.Shape(), y.Shape(), op, ctx)
		run := quoRemRun(x, y, op, ctx)
		if err != nil {
			if opErr := run(Budget{}); !errors.Is(opErr, err) {
				t.Fatalf("%v %s %v: estimate refuses %v, operation %v", x, op, y, err, opErr)
			}
			checked["refusal"]++
			continue
		}
		if opErr := run(Budget{}); opErr != nil {
			skipped++ // a value-dependent refusal the shape does not predict
			continue
		}
		o := checkArithmeticEstimate(t, fmt.Sprintf("%v %s %v", x, op, y), c, run)
		s := intDivShape{dx: max(x.Shape().Digits, 1), dy: y.Shape().Digits, ex: x.Exponent(), ey: y.Exponent()}
		slackDigits := uint64(1)
		if op != intDivQuo {
			slackDigits = c.Digits - 1
		}
		slackWork := 2 * slackDigits
		if !x.IsZero() && s.delta() == 0 {
			b, _ := intDivPrecharge(s.dx, s.dy, false)
			zero, one := planIntDiv(op, s, true, 1, intDivForceNone), planIntDiv(op, s, false, 1, intDivForceNone)
			wz, _ := intDivWork(b, zero.c, zero.nEnv)
			wq, _ := intDivWork(b, one.c, one.nEnv)
			slackWork += max(wz, wq) - min(wz, wq)
			slackDigits += max(zero.nEnv, one.nEnv) - min(zero.nEnv, one.nEnv)
		}
		if c.Digits-o.digits > slackDigits || c.WorkUnits-o.work > slackWork {
			t.Fatalf("%v %s %v: estimate %+v beyond slack (%d digits, %d work) of %+v", x, op, y, c, slackDigits, slackWork, o)
		}
		checked[op.String()]++
	}
	for _, k := range []string{"Quo", "Rem", "RemNear", "refusal"} {
		if checked[k] < 30 {
			t.Fatalf("vacuous estimate sweep: %v (skipped %d)", checked, skipped)
		}
	}
}

// TestQuoRemEstimatesAttained checks attainment on the integer-division
// witnesses, where the estimate is reached exactly on both axes: r = Cy − 1
// on the stream and modular paths, Hrem = Cy − 1 with a full low part on the
// split, 9…9 Quo 1, and (at δ = 0, digits exact) the q = 0 near case with n =
// ±1 and a full-width D.
func TestQuoRemEstimatesAttained(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 67))
	type witness struct {
		x, y       Decimal
		op         intDivOp
		path       intDivPath
		digitsOnly bool
	}
	var ws []witness
	for range 40 {
		dy := 1 + rng.IntN(60)
		cy, _ := new(big.Int).SetString(quoRemDigitsNoPower(rng, dy), 10)
		m := big.NewInt(int64(1 + rng.IntN(1000)))
		// Stream: Cx = Cy(m+1) − 1, k = 0.
		cx := new(big.Int).Sub(new(big.Int).Mul(cy, new(big.Int).Add(m, big.NewInt(1))), big.NewInt(1))
		ws = append(ws, witness{MustParse(cx.String()), MustParse(cy.String()), intDivRem, intDivStream, false})
		// Split: Hrem = Cy − 1 and L = 10^j − 1.
		j := 1 + rng.IntN(30)
		sx := cx.String() + strings.Repeat("9", j)
		ws = append(ws, witness{MustParse(sx + fmt.Sprintf("E-%d", j)), MustParse(cy.String()), intDivRem, intDivSplit, false})
		// Modular: Cy = 10^d − 1, 10^k ≡ 1 for d | k, Cx = Cy − 1.
		d := 1 + rng.IntN(20)
		nines := strings.Repeat("9", d)
		k := d * (4000/d + 1)
		ws = append(ws, witness{MustParse(strings.Repeat("9", d-1) + "8" + fmt.Sprintf("E%d", k)), MustParse(nines), intDivRem, intDivModular, false})
		// Quo: 9…9 Quo 1.
		q := 1 + rng.IntN(200)
		ws = append(ws, witness{MustParse(strings.Repeat("9", q)), MustParse("1"), intDivQuo, intDivQuotient, false})
	}
	// q = 0 near with a full-width D, at δ = 0: 60 RemNear 99 is −39.
	ws = append(ws, witness{MustParse("60"), MustParse("99"), intDivRemNear, intDivQZeroNear, true},
		witness{MustParse("6" + strings.Repeat("0", 70)), MustParse(strings.Repeat("9", 71)), intDivRemNear, intDivQZeroNear, true})
	for _, w := range ws {
		_, _, err, cnt := countedQuoRem(w.x, w.y, w.op, Context{}, Budget{}, intDivForceNone)
		if err != nil || cnt.taken != w.path {
			t.Fatalf("%v %s %v: path %s (%v), want %s", w.x, w.op, w.y, cnt.taken, err, w.path)
		}
		c, err := quoRemEstimate(w.x.Shape(), w.y.Shape(), w.op, nil)
		if err != nil {
			t.Fatal(err)
		}
		o := checkArithmeticEstimate(t, fmt.Sprintf("%v %s %v", w.x, w.op, w.y), c, quoRemRun(w.x, w.y, w.op, nil))
		if o.digits != c.Digits || !w.digitsOnly && o.work != c.WorkUnits {
			t.Fatalf("%v %s %v (%s): estimate %+v not attained: %+v", w.x, w.op, w.y, w.path, c, o)
		}
	}
}

// quoRemDigitsNoPower draws n random digits that are not a power of ten, so
// Cy − 1 keeps n digits.
func quoRemDigitsNoPower(rng *rand.Rand, n int) string {
	for {
		s := quoRemDigits(rng, n)
		if strings.Trim(s[1:], "0") != "" || s[0] != '1' {
			if s[0] != '0' {
				return s
			}
		}
	}
}

// TestQuoRemEstimatesMatchClosedForms checks the closed forms: the estimates
// equal the integer-division tariff written out, W = B + C + 2Nenv + 1: Rem
// 1E+2147483647 by 7 is 3 + 1,260 + 3 = 1,266 (modular), Quo 1E+40 by 1E−40
// is 3 + 141 + 163 = 307 (Q = δ+1 = 81), Rem 1E+40 by 1E−40 is 3 + 153 + 3 =
// 159 (stream), Rem 12345E−2 by 7E+1 (δ = 1) is 7 + 38 + 9 = 54 with Nenv =
// min(5, 1+3) = 4, RemNear 99 by 100 (δ = −1, near) is 6 + 20 + 7 = 33 with
// Nenv = L = 3, and Rem 1E−40 by 1E+40 is 3 + 0 + 3 = 6.
func TestQuoRemEstimatesMatchClosedForms(t *testing.T) {
	for _, c := range []struct {
		x, y string
		op   intDivOp
		w, n uint64
	}{
		{"1E+2147483647", "7", intDivRem, 1266, 1},
		{"1E+2147483647", "7", intDivRemNear, 1266, 1},
		{"1E+40", "1E-40", intDivQuo, 307, 81},
		{"1E+40", "1E-40", intDivRem, 159, 1},
		{"12345E-2", "7E+1", intDivRem, 54, 4},
		{"99", "100", intDivRemNear, 33, 3},
		{"1E-40", "1E+40", intDivRem, 6, 1},
		{"1E-40", "1E+40", intDivQuo, 6, 1},
	} {
		got, err := quoRemEstimate(MustParse(c.x).Shape(), MustParse(c.y).Shape(), c.op, nil)
		if err != nil || got.WorkUnits != c.w || got.Digits != c.n {
			t.Errorf("%s %s %s: %+v %v, want W=%d N=%d", c.x, c.op, c.y, got, err, c.w, c.n)
		}
	}
}

// TestQuoRemEstimatesPredictRefusals checks that the estimators predict only
// shape-decided refusals, in stage order, with the operation's own code,
// allocating nothing: a zero divisor (DivisionByZero, or DivisionUndefined
// for 0/0), δ > p (DivisionImpossible, before a failing guard), a stored
// exponent outside the guards and Quo's δ − 1 > Emax (InvalidOperation), and
// an unaddressable plan (InsufficientStorage). δ = p, a zero dividend (W = 4,
// N = 1) and a remainder adjusted-exponent guard are not predicted. At δ = p
// a failing guard must not predict InvalidOperation: the value can instead
// fail the earlier quotient-fit check with DivisionImpossible.
func TestQuoRemEstimatesPredictRefusals(t *testing.T) {
	p1, _ := NewContext(1, TiesToEven, &ExponentGuards{}, 0)
	p5, _ := NewContext(5, TiesToEven, nil, 0)
	g, _ := NewContext(5, TiesToEven, &ExponentGuards{Emin: -2, Emax: 2}, 0)
	for _, c := range []struct {
		name string
		x, y string
		op   intDivOp
		ctx  *Context
		code ErrorCode
	}{
		{"zero divisor", "5", "0", intDivRem, nil, ErrDivisionByZero},
		{"zero over zero", "0", "0E2", intDivRemNear, &g, ErrDivisionUndefined},
		{"quotient fit", "123", "1", intDivRem, &p1, ErrDivisionImpossible},
		{"quotient fit before guard", "100.0", "1.0", intDivRem, &p1, ErrDivisionImpossible},
		{"stored guard", "1E-9", "1", intDivRem, &g, ErrInvalidOperation},
		{"stored guard on zero", "0E-9", "1", intDivRemNear, &g, ErrInvalidOperation},
		{"Quo adjusted guard", "12345", "1", intDivQuo, &g, ErrInvalidOperation},
	} {
		x, y := MustParse(c.x), MustParse(c.y)
		_, est := quoRemEstimate(x.Shape(), y.Shape(), c.op, c.ctx)
		opErr := quoRemRun(x, y, c.op, c.ctx)(Budget{})
		if !isErrorCode(est, c.code) || !errors.Is(opErr, c.code) {
			t.Errorf("%s: estimate %v, operation %v, want %v", c.name, est, opErr, c.code)
		}
		if allocs := testing.AllocsPerRun(20, func() { _, _ = quoRemEstimate(x.Shape(), y.Shape(), c.op, c.ctx) }); allocs != 0 {
			t.Errorf("%s: estimator refusal allocated %g times", c.name, allocs)
		}
	}
	// Identical shapes straddle quotient fit at δ = p. A lower-priority
	// guard error is not a shape-decided error identity, even when every
	// possible value refuses. The hand-derived pairs cover all three ops.
	pairs := []struct {
		op                intDivOp
		x, smallY, largeY string
		precision         uint32
		guards            *ExponentGuards
		otherError        ErrorCode
	}{
		{intDivQuo, "100", "1", "9", 2, &ExponentGuards{}, ErrInvalidOperation},
		{intDivRem, "10.0", "1.0", "9.9", 1, &ExponentGuards{}, ErrInvalidOperation},
		{intDivRemNear, "10.0", "1.0", "9.9", 1, &ExponentGuards{}, ErrInvalidOperation},
		{intDivQuo, "1E2147483647", "1E-2147483648", "9E-2147483648", math.MaxUint32, &ExponentGuards{Emin: math.MaxInt32, Emax: math.MaxInt32}, ErrInvalidOperation},
		{intDivRem, "1E2147483647", "1E-2147483648", "9E-2147483648", math.MaxUint32, &ExponentGuards{Emin: math.MaxInt32, Emax: math.MaxInt32}, ErrInvalidOperation},
		{intDivRemNear, "1E2147483647", "1E-2147483648", "9E-2147483648", math.MaxUint32, &ExponentGuards{Emin: math.MaxInt32, Emax: math.MaxInt32}, ErrInvalidOperation},
	}
	// On 386 the unguarded quotient plan is physically inadmissible.
	// Do not execute this enormous, potentially reachable path on 64-bit.
	if strconv.IntSize == 32 {
		unguarded := pairs[3]
		unguarded.guards = nil
		unguarded.otherError = ErrInsufficientStorage
		pairs = append(pairs, unguarded)
	}
	for _, tc := range pairs {
		ctx, err := NewContext(tc.precision, TiesToEven, tc.guards, 0)
		if err != nil {
			t.Fatal(err)
		}
		for _, negative := range []bool{false, true} {
			x := MustParse(tc.x)
			if negative {
				x = x.Neg()
			}
			for _, operand := range []struct {
				value string
				want  ErrorCode
			}{
				{tc.smallY, ErrDivisionImpossible}, {tc.largeY, tc.otherError},
			} {
				y := MustParse(operand.value)
				bound, estErr := quoRemEstimate(x.Shape(), y.Shape(), tc.op, &ctx)
				if estErr != nil {
					t.Errorf("%s %s %s: shape-dependent collision predicted %v", x, tc.op, y, estErr)
				}
				if bound.WorkUnits != x.CoefficientDigits()+y.CoefficientDigits()+1 || bound.Digits != 0 || bound.HeapBytes == 0 {
					t.Errorf("%s %s %s: collision must bound only precharge and error: %+v", x, tc.op, y, bound)
				}
				run := quoRemRun(x, y, tc.op, &ctx)
				if opErr := run(bound.Budget()); !errors.Is(opErr, operand.want) {
					t.Errorf("%s %s %s: %v, want %v", x, tc.op, y, opErr, operand.want)
				}
				if heap := coldAllocatedWithin(func() { _ = run(bound.Budget()) }, bound.HeapBytes); estErr == nil && heap > bound.HeapBytes {
					t.Errorf("collision refusal allocated %d bytes, bound %d", heap, bound.HeapBytes)
				}
				if estErr == nil && !errors.Is(run(Budget{MaxWork: bound.WorkUnits - 1}), ErrInsufficientStorage) {
					t.Error("classification precharge below B was admitted")
				}
			}
		}
	}
	// Unaddressable shapes: no finite budget admits them.
	for _, digits := range []uint64{1 << 62, 1<<62 + 1, math.MaxUint64} {
		for _, op := range quoRemOps {
			if _, err := quoRemEstimate(Shape{Digits: digits}, Shape{Digits: 3}, op, nil); !isErrorCode(err, ErrInsufficientStorage) {
				t.Errorf("%s of %d digits: %v", op, digits, err)
			}
			if _, err := quoRemEstimate(Shape{Digits: 3}, Shape{Digits: digits}, op, nil); digits > 1<<62 && !isErrorCode(err, ErrInsufficientStorage) {
				t.Errorf("%s by %d digits: %v", op, digits, err)
			}
		}
	}
	// Not predicted: δ = p (Q may be p or p+1), a zero dividend, and the
	// remainder's adjusted exponent.
	for _, c := range []struct {
		x, y string
		op   intDivOp
		ctx  *Context
	}{
		{"99999", "1", intDivQuo, &p5},
		{"0E+7", "3", intDivRem, nil},
		{"0E+7", "3", intDivQuo, &g},
		{"99", "100", intDivRem, &g},
	} {
		est, err := quoRemEstimate(MustParse(c.x).Shape(), MustParse(c.y).Shape(), c.op, c.ctx)
		if err != nil {
			t.Errorf("%s %s %s: predicted %v", c.x, c.op, c.y, err)
		}
		if MustParse(c.x).IsZero() && (est.WorkUnits != 4 || est.Digits != 1) {
			t.Errorf("zero dividend %s %s %s: %+v, want W=4 N=1", c.x, c.op, c.y, est)
		}
	}
	x, y := Shape{Digits: 81, Exponent: -20}, Shape{Digits: 38, Exponent: 5, Negative: true}
	ctx := Decimal128Context()
	for _, op := range quoRemOps {
		if allocs := testing.AllocsPerRun(20, func() {
			_, _ = quoRemEstimate(x, y, op, nil)
			_, _ = quoRemEstimate(y, x, op, &ctx)
		}); allocs != 0 {
			t.Errorf("%s estimators allocated %g times", op, allocs)
		}
	}
}

// TestEstimateFMABound checks estimate soundness, attainment and closed form
// for EstimateFMA: over a size sweep, sign relations, zero factors and
// addends, exponent gaps, precisions and guards, each estimate admits its
// call, bounds its cold-pool allocation, equals the hand-derived tariff
// (Mul's charge plus the Add/Sub charge with the product as a (dx+dy)-digit
// operand; plus 2N+1 in context), and is attained in work by every
// non-cancelling product of dx+dy digits (all-nines factors) and in digits by
// a carry or an N-digit result. An exponent sum outside int32 is
// ErrExponentRange bare; in context only an exact zero at an ideal exponent
// outside int32 is, and a product exponent outside int32 is otherwise
// estimated, over the operands as the context planner reduces them.
func TestEstimateFMABound(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 64))
	var attainedDigits, contextAttained int
	for _, dx := range []uint64{1, 9, 10, 38, 39, 81, 82, 200, 1000} {
		for _, dy := range []uint64{1, 38, 300} {
			for _, dz := range []uint64{0, 1, 20, 90} {
				for _, gap := range []int32{-50, 0, 60} {
					for _, negative := range []bool{false, true} {
						x := shapedDecimal(r, dx, -7, false, '9')
						y := shapedDecimal(r, dy, 3, negative, '9')
						z := zeroDecimal(-4 + gap)
						if dz > 0 {
							z = shapedDecimal(r, dz, -4+gap, r.IntN(2) == 0, 0)
						}
						label := fmt.Sprintf("FMA(%d digits, %d digits, %d digits at gap %d, negative %v)", dx, dy, dz, gap, negative)
						est, err := estimateFMA(x.Shape(), y.Shape(), z.Shape())
						if err != nil {
							t.Fatalf("%s: %v", label, err)
						}
						// A zero addend shape is estimated as one digit, as
						// EstimateAdd estimates zero; only soundness binds it.
						want, _ := fmaClosedCharge(x, y, z, false)
						if dz > 0 && est.WorkUnits != want {
							t.Fatalf("%s: EstimateFMA work %d, closed form %d", label, est.WorkUnits, want)
						}
						o := checkArithmeticEstimate(t, label, est, func(b Budget) error {
							_, err := x.fmaExactBudget(y, z, b)
							return err
						})
						exact, _ := fmaExact(x, y, z)
						if dz > 0 && exact.Sign() != 0 && o.work != est.WorkUnits {
							t.Fatalf("%s: work estimate %d not attained (%d)", label, est.WorkUnits, o.work)
						}
						if o.digits == est.Digits {
							attainedDigits++
						}
						for _, p := range []uint32{1, 34} {
							for _, guards := range []*ExponentGuards{nil, {Emin: -40, Emax: 40}} {
								ctx := contextTestContext(t, p, TowardZero, guards, 0)
								est, err := EstimateFMA(x.Shape(), y.Shape(), z.Shape(), ctx)
								if err != nil {
									t.Fatalf("%s p=%d: %v", label, p, err)
								}
								run := func(b Budget) error {
									_, _, err := x.FMAWithContext(y, z, ctx.WithBudget(b))
									return err
								}
								o := checkArithmeticEstimate(t, fmt.Sprintf("%s p=%d guards %v", label, p, guards), est, run)
								got, conditions, _ := x.FMAWithContext(y, z, ctx)
								B := fmaContextCharge(x, y, z, ctx, false)
								if dz > 0 && conditions&Overflow == 0 && exact.Sign() != 0 && got.CoefficientDigits() == est.Digits {
									if est.WorkUnits != B+2*est.Digits+1 || o.work != est.WorkUnits || o.digits != est.Digits {
										t.Fatalf("%s p=%d: estimate %+v, closed form W=%d, observed %+v", label, p, est, B+2*est.Digits+1, o)
									}
									contextAttained++
								}
							}
						}
					}
				}
			}
		}
	}
	if attainedDigits < 300 || contextAttained < 800 {
		t.Fatalf("vacuous attainment: %d bare digit caps, %d context estimates", attainedDigits, contextAttained)
	}
	// Overflow reachable through the product alone: 81E40 + 1E38 has five
	// exact digits, but under Emax = 40 it publishes p nines, so the
	// estimate must count p digits from the product's adjusted exponent.
	over := contextTestContext(t, 34, TiesToEven, &ExponentGuards{Emin: -40, Emax: 40}, 0)
	ox, oy, oz := New(9, 40), New(9, 0), New(1, 38)
	oc, err := EstimateFMA(ox.Shape(), oy.Shape(), oz.Shape(), over)
	if err != nil || oc.Digits != 34 {
		t.Fatalf("overflow estimate %+v %v", oc, err)
	}
	checkArithmeticEstimate(t, "product overflow", oc, func(b Budget) error {
		_, conditions, err := ox.FMAWithContext(oy, oz, over.WithBudget(b))
		if err == nil && conditions&Overflow == 0 {
			t.Fatalf("product overflow witness did not overflow: %v", conditions)
		}
		return err
	})
	// Three boundary shapes: a 49-limb product (216×225 digits) is the
	// first beyond the stack, so its scratch is in HeapBytes; a zero
	// product above int32 with a zero addend at 0 is an exact zero at 0,
	// which fits; an addend whose digits alone overflow Emax needs p
	// digits.
	for _, tc := range []struct {
		name    string
		x, y, z Decimal
		ctx     Context
	}{
		{"49-limb product", shapedDecimal(r, 216, 0, false, 0), shapedDecimal(r, 225, 0, true, 0), New(5, 0), Decimal128Context()},
		{"zero product above int32", zeroDecimal(2000000000), zeroDecimal(2000000000), Zero(), Decimal128Context()},
		{"addend digits overflow", New(1, 35), New(1, 0), shapedDecimal(r, 9, 35, false, '9'), over},
	} {
		c, err := EstimateFMA(tc.x.Shape(), tc.y.Shape(), tc.z.Shape(), tc.ctx)
		if err != nil {
			t.Fatalf("%s: %v", tc.name, err)
		}
		checkArithmeticEstimate(t, tc.name, c, func(b Budget) error {
			_, _, err := tc.x.FMAWithContext(tc.y, tc.z, tc.ctx.WithBudget(b))
			return err
		})
		if bare, err := estimateFMA(tc.x.Shape(), tc.y.Shape(), tc.z.Shape()); err == nil {
			checkArithmeticEstimate(t, tc.name+" bare", bare, func(b Budget) error {
				_, err := tc.x.fmaExactBudget(tc.y, tc.z, b)
				return err
			})
		}
	}
	// A 56-limb product far below the addend is replaced by one sticky
	// digit and never built: the estimate carries no product scratch, and
	// the call allocates nothing (an inline result).
	far := contextTestContext(t, 34, TiesToEven, nil, 0)
	fx, fy := shapedDecimal(r, 250, -500, false, 0), shapedDecimal(r, 250, -500, false, 0)
	fc, err := EstimateFMA(fx.Shape(), fy.Shape(), Shape{Digits: 1}, far)
	if err != nil || fc.HeapBytes != 0 {
		t.Fatalf("replaced product estimate %+v %v, want no heap", fc, err)
	}
	if n := testing.AllocsPerRun(20, func() { _, _, _ = fx.FMAWithContext(fy, One(), far.WithBudget(fc.Budget())) }); n != 0 {
		t.Fatalf("replaced product: %v allocations", n)
	}
	tiny := Shape{Digits: 1, Exponent: -2000000000}
	for _, tc := range []struct {
		est  func() (Cost, error)
		code ErrorCode
	}{
		{func() (Cost, error) { return estimateFMA(tiny, tiny, Shape{Digits: 1}) }, ErrExponentRange},
		{func() (Cost, error) {
			return estimateFMA(Shape{Exponent: math.MaxInt32}, Shape{Exponent: 1}, Shape{Digits: 1})
		}, ErrExponentRange},
		{func() (Cost, error) {
			return EstimateFMA(Shape{Exponent: -2000000000}, tiny, Shape{}, Decimal128Context())
		}, ErrExponentRange},
		{func() (Cost, error) {
			return estimateFMA(Shape{Digits: math.MaxUint64 / 2}, Shape{Digits: math.MaxUint64 / 2}, Shape{Digits: 1})
		}, ErrInsufficientStorage},
		{func() (Cost, error) {
			return EstimateFMA(Shape{Digits: math.MaxUint64 / 2}, Shape{Digits: math.MaxUint64 / 2}, Shape{Digits: 1}, Decimal64Context())
		}, ErrInsufficientStorage},
	} {
		if _, err := tc.est(); !isErrorCode(err, tc.code) {
			t.Fatalf("refusal: %v, want %v", err, tc.code)
		}
	}
	// This witness has a product exponent below int32: the context planner,
	// over int64 exponents, reduces the remote product to one sticky digit at
	// P = min(0, 0−34−1)−1 = −36, so the estimate is O(p).
	c, err := EstimateFMA(tiny, tiny, Shape{Digits: 1}, mustContext(t, 34, TiesToEven))
	// Mul 1·1+1+1; same signs dP+dz+L+1 with the substitute's dP = 1 and
	// L = 37; the finisher 2·34+1; no product scratch.
	if want := uint64(3) + (1 + 1 + 37 + 1) + 2*34 + 1; err != nil || c.WorkUnits != want || c.Digits != 34 {
		t.Fatalf("witness estimate %+v %v, want work %d", c, err, want)
	}

}

// TestSpanTariffsMatchShapeTariffs pins FMA's span estimators to the Add/Sub
// estimators they restate: over the planner differential's shape pairs, both
// effective sign relations and guards, addSubTariffSpan equals addSubTariff,
// estimateAddSubSpans equals estimateAddSub, and contextAddSubEstimate over
// the span planner's reduction equals estimateContextAddSub, value and error,
// including refusals. A vacuity guard requires refusals and each reduction.
func TestSpanTariffsMatchShapeTariffs(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 68))
	var refused, reduced int
	for range 100000 {
		p := int64(1 + r.IntN(40))
		var guards *ExponentGuards
		if r.IntN(3) == 0 {
			emin := int32(-r.IntN(60))
			guards = &ExponentGuards{Emin: emin, Emax: emin + int32(r.IntN(80))}
		}
		ctx := contextTestContext(t, uint32(p), TiesToEven, guards, 0)
		x := Shape{Digits: uint64(1 + r.IntN(40)), Exponent: int32(r.IntN(81) - 40), Negative: r.IntN(2) == 0}
		y := reduceTestShape(r, x, p)
		if r.IntN(20) == 0 {
			// Digit counts whose charges leave uint64: the refusals.
			x.Digits, y.Digits = 1<<62, 1<<62+uint64(r.IntN(9))
		}
		subtract := r.IntN(2) == 0
		ey := spanOf(y)
		ey.negative = y.Negative != subtract
		var t1, t2 costTally
		w1, d1 := addSubTariff(&t1, x, y, subtract)
		w2, d2 := addSubTariffSpan(&t2, spanOf(x), ey)
		if w1 != w2 || d1 != d2 || t1.overflow != t2.overflow {
			t.Fatalf("tariff %+v %+v sub=%v: shape %d %d, span %d %d", x, y, subtract, w1, d1, w2, d2)
		}
		want, wantErr := estimateAddSub(x, y, subtract, "E")
		got, err := estimateAddSubSpans(spanOf(x), ey, "E")
		if got != want || (err == nil) != (wantErr == nil) {
			t.Fatalf("bare %+v %+v sub=%v: span %+v %v, shape %+v %v", x, y, subtract, got, err, want, wantErr)
		}
		want, wantErr = estimateContextAddSub(x, y, ctx, subtract, "E")
		rx, ry := contextReduceSpans(spanOf(x), ey, ctx)
		got, err = contextAddSubEstimate(rx, ry, 0, ctx, "E")
		if got != want || (err == nil) != (wantErr == nil) || err != nil && err.Error() != wantErr.Error() {
			t.Fatalf("context %+v %+v sub=%v %+v: span %+v %v, shape %+v %v", x, y, subtract, ctx, got, err, want, wantErr)
		}
		if err != nil {
			refused++
		}
		if rx != spanOf(x) || ry != ey {
			reduced++
		}
	}
	if refused < 100 || reduced < 10000 {
		t.Fatalf("vacuous: %d refusals, %d reductions", refused, reduced)
	}
}

// TestEstimateExactProbeHeap checks the split cumulative heap bound: both a
// successful heap-sized probe and a failed probe followed by the full
// division fit the estimator, as do the separate live power/division arenas.
func TestEstimateExactProbeHeap(t *testing.T) {
	var exact, fallback int
	for _, exponent := range []uint{200, 900} {
		den := new(big.Int).Lsh(big.NewInt(1), exponent)
		for _, offset := range []int64{0, 1} {
			y := MustParse(new(big.Int).Add(den, big.NewInt(offset)).String())
			x := One()
			ctx := mustContext(t, 262144, TiesToEven)
			s := newDivSource(x, y)
			target, etiny := divContextTarget(s.dx, s.dy, s.ideal, ctx)
			plan := s.plan(target)
			trial, tt, ok := s.exactProbe(plan, target)
			if !ok || s.scratchTotal(trial) <= divStackLimbs {
				t.Fatal("heap probe witness ineligible")
			}
			_, _, _, done := s.tryExactContext(trial, tt, etiny, &ctx, plan.charge, limits{}, "Div", nil, 0)
			if done {
				exact++
			} else {
				fallback++
			}
			est, err := EstimateDiv(x.Shape(), y.Shape(), ctx)
			if err != nil {
				t.Fatal(err)
			}
			checkArithmeticEstimate(t, fmt.Sprintf("probe 1/(2^%d+%d)", exponent, offset), est, func(b Budget) error { _, _, e := x.DivWithContext(y, ctx.WithBudget(b)); return e })
			for _, n := range []int32{-2, -3} {
				est, err := EstimatePow(y.Shape(), n, ctx)
				if err != nil {
					t.Fatal(err)
				}
				checkArithmeticEstimate(t, fmt.Sprintf("probe (2^%d+%d)^%d", exponent, offset, n), est, func(b Budget) error { _, _, e := y.PowWithContext(n, ctx.WithBudget(b)); return e })
			}
		}
	}
	if exact != 2 || fallback != 2 {
		t.Fatalf("vacuous heap routes exact%d fallback%d", exact, fallback)
	}
}

// TestEstimateNegativePowStrippedPhysicalPlan checks that a shape's worst
// power arena being unaddressable does not imply all values refuse. Decimal
// trailing zeros can leave a one-digit exact power.
func TestEstimateNegativePowStrippedPhysicalPlan(t *testing.T) {
	for _, tc := range []struct {
		x Decimal
		n int32
		p uint32
	}{
		{New(10, 0), math.MinInt32, math.MaxUint32},
		{New(100, -1), -400000000, 1 << 30},
	} {
		ctx := mustContext(t, tc.p, TiesToEven)
		got, cond, err := tc.x.PowWithContext(tc.n, ctx)
		if err != nil || cond != 0 || !got.Equal(New(1, tc.n)) || got.Exponent() != tc.n {
			t.Fatalf("10^%d: %v %v %v", tc.n, got, cond, err)
		}
		est, err := EstimatePow(tc.x.Shape(), tc.n, ctx)
		if err != nil {
			t.Errorf("successful stripped reciprocal %+v n%d p%d has refusing estimator: %v", tc.x.Shape(), tc.n, tc.p, err)
			continue
		}
		if _, _, err := tc.x.PowWithContext(tc.n, ctx.WithBudget(est.Budget())); err != nil {
			t.Fatal(err)
		}
	}
}

// TestBoundEvaluationContract covers the separate finite-attempt contract:
// allocator-derived E, no completion prediction, and no query allocation.
func TestBoundEvaluationContract(t *testing.T) {
	e := max(evaluationObjectOracle(uint64(reflect.TypeFor[Error]().Size())), evaluationObjectOracle(uint64(reflect.TypeFor[Error]().Size())), evaluationObjectOracle(uint64(reflect.TypeFor[Error]().Size())))
	for _, w := range []uint64{1, 17, 65536, math.MaxUint64 - e} {
		b, err := BoundEvaluation(Budget{MaxWork: w, MaxDigits: 1})
		if err != nil || b.Units != w || b.HeapBytes != w+e {
			t.Fatalf("W=%d bound=%+v err=%v E=%d", w, b, err, e)
		}
	}
	for _, tc := range []struct {
		w   uint64
		err error
	}{{0, ErrEvaluationBudgetRequired}, {math.MaxUint64, ErrEvaluationBoundOverflow}, {math.MaxUint64 - e + 1, ErrEvaluationBoundOverflow}} {
		b, err := BoundEvaluation(Budget{MaxWork: tc.w, MaxDigits: 1})
		if b != (EvaluationBound{}) || err != tc.err || errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("wrong query refusal: %+v %v", b, err)
		}
	}
	if n := testing.AllocsPerRun(100, func() {
		_, _ = BoundEvaluation(Budget{MaxWork: 1})
		_, _ = BoundEvaluation(Budget{})
		_, _ = BoundEvaluation(Budget{MaxWork: math.MaxUint64})
	}); n != 0 {
		t.Fatalf("bound query allocated %g", n)
	}
	// An unrepresentable *bound* does not invalidate an easy phase using
	// that same operation budget, nor affect Cost.Budget.
	m := newEvaluationMeter(Budget{MaxWork: math.MaxUint64})
	if s := m.phase(1, 0); s.code != 0 {
		t.Fatalf("query overflow predicted operation failure: %+v", s)
	}
	budget := Cost{WorkUnits: 7, Digits: 3}.Budget()
	if budget != (Budget{MaxWork: 7, MaxDigits: 3}) {
		t.Fatal("Cost.Budget changed")
	}
}

// TestEstimateFromFloat64WithContextBound checks: over random bit patterns
// and contexts (exact, rounding, guarded overflow and subnormal), the
// estimate admits FromFloat64WithContext under a budget and bounds its allocation,
// and a budget below a guarded overflow's p digits refuses before the p-digit
// largest value is allocated.
func TestEstimateFromFloat64WithContextBound(t *testing.T) {
	r := rand.New(rand.NewPCG(86, 3))
	narrow, err := NewContext(400, TiesToEven, &ExponentGuards{Emin: -50, Emax: 40}, 0)
	if err != nil {
		t.Fatal(err)
	}
	exact, _ := NewContext(0, TiesToEven, nil, 0)
	contexts := []Context{Decimal64Context(), Decimal128Context(), narrow, exact}
	for range 60 {
		f := math.Float64frombits(r.Uint64())
		if math.IsNaN(f) || math.IsInf(f, 0) {
			continue
		}
		for _, ctx := range contexts {
			c, err := EstimateFromFloat64(f, ctx)
			if err != nil {
				t.Fatal(err)
			}
			checkArithmeticEstimate(t, "from-float64-context", c, func(b Budget) error {
				_, _, err := FromFloat64WithContext(f, ctx.WithBudget(b))
				return err
			})
			want, wantC, wantErr := FromFloat64WithContext(f, ctx)
			got, gotC, gotErr := FromFloat64WithContext(f, ctx.WithBudget(c.Budget()))
			if !sameCohort(got, want) || gotC != wantC || (gotErr == nil) != (wantErr == nil) {
				t.Fatalf("%v: budgeted %v %v %v; unbudgeted %v %v %v", f, got, gotC, gotErr, want, wantC, wantErr)
			}
		}
	}
	huge, err := NewContext(100_000_000, TiesToEven, &ExponentGuards{Emin: -10, Emax: 0}, 0)
	if err != nil {
		t.Fatal(err)
	}
	c, err := EstimateFromFloat64(1e300, huge)
	if err != nil || c.Digits != 100_000_000 {
		t.Fatalf("overflow estimate %+v, %v; want p digits", c, err)
	}
	var refusal error
	allocs := testing.AllocsPerRun(5, func() {
		_, _, refusal = FromFloat64WithContext(1e300, huge.WithBudget(Budget{MaxDigits: 1000}))
	})
	if !errors.Is(refusal, ErrInsufficientStorage) || allocs > 2 {
		t.Fatalf("budgeted overflow: %v after %v allocations", refusal, allocs)
	}
	if _, err := EstimateFromFloat64(math.NaN(), huge); !isErrorCode(err, ErrConversionSyntax) {
		t.Fatalf("NaN: %v", err)
	}
}

// TestEstimateDisplayZeroShape checks that the display estimates price a
// zero as the zero it renders, at any exponent: the estimate equals the
// output of every form, and no exponent makes it refuse.
func TestEstimateDisplayZeroShape(t *testing.T) {
	for _, exponent := range []int32{math.MinInt32, -1000, -1, 0, 1, 1000, math.MaxInt32} {
		zero := New(0, exponent)
		for _, places := range []uint64{0, 2, 40} {
			text, err := zero.FixedWithOptions(places, DisplayOptions{Mode: TiesToEven})
			if err != nil {
				t.Fatal(err)
			}
			cost, err := EstimateFixed(zero.Shape(), places, TiesToEven)
			if err != nil || cost.OutputBytes != uint64(len(text)) {
				t.Fatalf("EstimateFixed(0E%d, %d) = %d bytes, %v; Fixed renders %q", exponent, places, cost.OutputBytes, err, text)
			}
			if places == 0 {
				continue
			}
			text, err = zero.ScientificWithOptions(places, DisplayOptions{Mode: TiesToEven})
			if err != nil {
				t.Fatal(err)
			}
			cost, err = EstimateScientific(zero.Shape(), places, TiesToEven)
			if err != nil || cost.OutputBytes != uint64(len(text)) {
				t.Fatalf("EstimateScientific(0E%d, %d) = %d bytes, %v; Scientific renders %q", exponent, places, cost.OutputBytes, err, text)
			}
		}
	}
}
