// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"slices"
	"testing"
)

// enclosureRat is an endpoint as an exact rational.
func enclosureRat(x evalNum) *big.Rat {
	z := new(big.Int)
	base := big.NewInt(1_000_000_000)
	for _, v := range slices.Backward(x.m) {
		z.Mul(z, base).Add(z, big.NewInt(int64(v)))
	}
	if x.neg {
		z.Neg(z)
	}
	r := new(big.Rat).SetInt(z)
	scale := new(big.Rat).SetInt(new(big.Int).Exp(base, big.NewInt(max(x.e, -x.e)), nil))
	if x.e < 0 {
		return r.Quo(r, scale)
	}
	return r.Mul(r, scale)
}

// enclosureNum writes m·10^(9e) for m > 0 into dst as an exact endpoint.
func enclosureNum(dst []uint32, m *big.Int, e int64) evalNum {
	base := big.NewInt(1_000_000_000)
	q, r := new(big.Int).Set(m), new(big.Int)
	n := 0
	for q.Sign() > 0 {
		q.QuoRem(q, base, r)
		dst[n] = uint32(r.Int64())
		n++
	}
	x := evalNum{m: dst[:n], e: e}
	for len(x.m) > 0 && x.m[0] == 0 {
		x.m, x.e = x.m[1:], x.e+1
	}
	return x
}

// enclosureUnit is one unit of the W-th limb below x's top.
func enclosureUnit(x evalNum, W int) *big.Rat {
	return enclosureRat(evalNum{m: []uint32{1}, e: x.top() - int64(W)})
}

// enclosureRoot is ⌊n^(1/k)⌋ for n ≥ 0.
func enclosureRoot(n *big.Int, k int64) *big.Int {
	lo, hi := new(big.Int), new(big.Int).Add(n, big.NewInt(1))
	for new(big.Int).Sub(hi, lo).Cmp(big.NewInt(1)) > 0 {
		mid := new(big.Int).Rsh(new(big.Int).Add(lo, hi), 1)
		if new(big.Int).Exp(mid, big.NewInt(k), nil).Cmp(n) <= 0 {
			lo = mid
		} else {
			hi = mid
		}
	}
	return lo
}

// enclosurePow10 is 10^(9e) for e ≥ 0 as an integer.
func enclosurePow10(e int64) *big.Int {
	return new(big.Int).Exp(big.NewInt(10), big.NewInt(9*e), nil)
}

// TestEnclosurePrimitivesAreDirected checks evaluation
// certification at the primitive level: every directed add, mul, div,
// divSmall and load bounds the exact rational result from the requested
// side within L limbs, including cancellation, far-apart operands and
// signs, and is exact whenever the exact result fits.
func TestEnclosurePrimitivesAreDirected(t *testing.T) {
	rng := rand.New(rand.NewPCG(66, 6))
	ev := newEvaluator(Budget{})
	buf := func() []uint32 { return make([]uint32, 64) }
	for i := range 4000 {
		x := randomElementaryInput(rng, rng.IntN(2) == 0)
		y := randomElementaryInput(rng, rng.IntN(2) == 0)
		switch i % 10 {
		case 0:
			y = x.Neg() // total cancellation
		case 1:
			y = New(int64(rng.IntN(9)+1), int32(-60-rng.IntN(200))) // far below
		case 2:
			z, _ := x.Add(New(1, x.Exponent()))
			y = z.Neg() // cancellation to one unit
		}
		L := 1 + rng.IntN(5)
		xv, yv := coefficientViewOf(x), coefficientViewOf(y)
		xd, _ := arithmeticDigits(&xv)
		yd, _ := arithmeticDigits(&yv)
		a := ev.load(buf(), &xv, xd, int64(x.exponent()), x.negative(), 40, false)
		b := ev.load(buf(), &yv, yd, int64(y.exponent()), y.negative(), 40, false)
		ar, br := enclosureRat(a), enclosureRat(b)
		if ar.Cmp(oracleRat(x)) != 0 || br.Cmp(oracleRat(y)) != 0 {
			t.Fatalf("exact load: %s %s", x, y)
		}
		for _, up := range []bool{false, true} {
			check := func(name string, got evalNum, exact *big.Rat) {
				t.Helper()
				g := enclosureRat(got)
				if c := g.Cmp(exact); up && c < 0 || !up && c > 0 {
					t.Fatalf("%s %s %s L=%d up=%v: %s beyond exact %s", name, x, y, L, up, g.FloatString(40), exact.FloatString(40))
				}
				if len(got.m) > L {
					t.Fatalf("%s: %d limbs > %d", name, len(got.m), L)
				}
			}
			check("add", ev.add(buf(), a, b, L, up), new(big.Rat).Add(ar, br))
			check("mul", ev.mul(buf(), a, b, L, up), new(big.Rat).Mul(ar, br))
			if !b.isZero() {
				check("div", ev.div(buf(), buf(), a, b, L, up), new(big.Rat).Quo(ar, br))
			}
			d := uint64(rng.Uint32N(1<<31)) + 1
			check("divSmall", ev.divSmall(buf(), a, d, L, up), new(big.Rat).Quo(ar, big.NewRat(int64(d), 1)))
			check("load", ev.load(buf(), &xv, xd, int64(x.exponent()), x.negative(), L, up), ar)
		}
	}
	if !ev.ok() {
		t.Fatalf("status %+v", ev.status)
	}
	// A destination aliasing an operand fails closed instead of computing.
	b := buf()
	a := ev.load(b, &coefficientView{inline: [5]uint32{7}, count: 1}, 1, 0, false, 4, false)
	if got := ev.add(b, a, a, 4, false); !got.isZero() || ev.ok() {
		t.Fatal("aliased add was not refused")
	}
}

// TestEvaluationRefinesAmbiguousStages checks that an ambiguous stage refines
// without a hidden cap: e^x for x within 10^−60 of ln 2.5 lies next to the
// one-digit midpoint 2.5, so the first stage cannot certify it; later stages
// must, in the direction the oracle proves.
func TestEvaluationRefinesAmbiguousStages(t *testing.T) {
	// Below Etiny the prefix is taken at the quantum itself, so the half
	// class decides: e^x within 10^−64 of 2.5·10^−398 rounds to 3E−398 above
	// the midpoint and to 2E−398 below it (Decimal64, Etiny −398).
	for _, tc := range []struct {
		x    string
		want string
		c    Conditions
	}{
		{"-915.5125762797560271739770717526089435537882912543433819934725367031", "3E-398", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"-915.5125762797560271739770717526089435537882912543433819934725367032", "2E-398", Subnormal | Underflow | Inexact | Rounded | Decreased},
	} {
		x, _ := Parse(tc.x)
		ev := newEvaluator(Budget{MaxWork: 1 << 26})
		got, c, err := ev.exp(x, Decimal64Context(), "ExpWithContext")
		if err != nil || got.String() != tc.want || c != tc.c {
			t.Fatalf("exp(%s) = %s %v %v, want %s %v", tc.x, got, c, err, tc.want, tc.c)
		}
		if ev.stages < 2 {
			t.Fatalf("exp(%s) certified in %d stage(s): the witness is vacuous", tc.x, ev.stages)
		}
	}
	// ln 2.5 = 0.916290731874155065183527211768011071450101219908262467791967881980785…
	for _, tc := range []struct {
		x    string
		want string
	}{
		{"0.916290731874155065183527211768011071450101219908262467791967881981", "3"},
		{"0.916290731874155065183527211768011071450101219908262467791967881980", "2"},
	} {
		x, _ := Parse(tc.x)
		ev := newEvaluator(Budget{})
		got, c, err := ev.exp(x, mustContext(t, 1, TiesToEven), "ExpWithContext")
		if err != nil || got.String() != tc.want || c&Inexact == 0 {
			t.Fatalf("exp(%s) = %s %v %v, want %s", tc.x, got, c, err, tc.want)
		}
		if ev.stages < 2 {
			t.Fatalf("exp(%s) certified in %d stage(s): the witness is vacuous", tc.x, ev.stages)
		}
	}
}

// TestEvaluationBudgetBoundsWholeCall checks the bounded attempt:
// with finite units W every call either succeeds or refuses with
// *Error, and its cumulative allocation, including discarded
// stages and the one outer error, stays within BoundEvaluation(W).HeapBytes.
func TestEvaluationBudgetBoundsWholeCall(t *testing.T) {
	two, _ := Parse("2")
	half, _ := Parse("0.5")
	tie, _ := Parse("5.0625")
	near, _ := Parse("1.000000000000000000000000000001")
	refined, _ := Parse("0.916290731874155065183527211768011071450101219908262467791967881981")
	calls := []struct {
		name string
		run  func(Budget) (Decimal, error)
	}{
		{"Exp p16", func(b Budget) (Decimal, error) {
			r, _, err := New(15, -1).ExpWithContext(mustContext(t, 16, TiesToEven).WithBudget(b))
			return r, err
		}},
		{"Exp p120", func(b Budget) (Decimal, error) {
			r, _, err := New(-37, -1).ExpWithContext(mustContext(t, 120, TowardZero).WithBudget(b))
			return r, err
		}},
		{"Exp 0", func(b Budget) (Decimal, error) {
			res, _, resErr := Zero().ExpWithContext(Context{}.WithBudget(b))
			return res, resErr
		}},
		{"Ln near one", func(b Budget) (Decimal, error) {
			r, _, err := near.LnWithContext(mustContext(t, 30, TiesToEven).WithBudget(b))
			return r, err
		}},
		{"Log10", func(b Budget) (Decimal, error) {
			r, _, err := New(3, 0).Log10WithContext(mustContext(t, 25, AwayFromZero).WithBudget(b))
			return r, err
		}},
		{"Log10 exact", func(b Budget) (Decimal, error) {
			res, _, resErr := New(1, 40).Log10WithContext(Context{}.WithBudget(b))
			return res, resErr
		}},
		{"Pow irrational", func(b Budget) (Decimal, error) {
			r, _, err := two.PowDecimalWithContext(half, mustContext(t, 20, TiesToEven).WithBudget(b))
			return r, err
		}},
		{"Pow tie", func(b Budget) (Decimal, error) {
			r, _, err := tie.PowDecimalWithContext(half, mustContext(t, 2, TiesToEven).WithBudget(b))
			return r, err
		}},
		{"Pow exact bare", func(b Budget) (Decimal, error) {
			res, _, resErr := tie.PowDecimalWithContext(half, Context{}.WithBudget(b))
			return res, resErr
		}},
		{"Pow int32", func(b Budget) (Decimal, error) {
			res, _, resErr := New(123, -2).PowDecimalWithContext(New(7, 0), Context{}.WithBudget(b))
			return res, resErr
		}},
		{"Exp refined", func(b Budget) (Decimal, error) {
			r, _, err := refined.ExpWithContext(mustContext(t, 1, TiesToEven).WithBudget(b))
			return r, err
		}},
	}
	for _, call := range calls {
		minimal := uint64(1)
		for hi := uint64(1); ; hi *= 2 {
			if _, err := call.run(Budget{MaxWork: hi}); err == nil {
				lo := hi / 2
				for lo+1 < hi {
					mid := lo + (hi-lo)/2
					if _, err := call.run(Budget{MaxWork: mid}); err == nil {
						hi = mid
					} else {
						lo = mid
					}
				}
				minimal = hi
				break
			}
			if hi > 1<<28 {
				t.Fatalf("%s: no finite budget succeeds", call.name)
			}
		}
		// The first admitted arena: its allocator envelope must already be
		// inside the units that admitted it.
		first := uint64(1)
		for lo, hi := uint64(1), minimal; lo < hi; {
			mid := lo + (hi-lo)/2
			if coldAllocatedWithin(func() { _, _ = call.run(Budget{MaxWork: mid}) }, 0) > 256 {
				hi = mid
			} else {
				lo = mid + 1
			}
			first = lo
		}
		for _, w := range []uint64{minimal, minimal - 1, minimal / 2, minimal / 7, first, 1} {
			if w == 0 {
				continue
			}
			bound, err := BoundEvaluation(Budget{MaxWork: w})
			if err != nil {
				t.Fatal(err)
			}
			var got error
			used := coldAllocatedWithin(func() { _, got = call.run(Budget{MaxWork: w}) }, bound.HeapBytes)
			if used > bound.HeapBytes {
				t.Fatalf("%s W=%d: allocated %d > bound %d", call.name, w, used, bound.HeapBytes)
			}
			var limit *Error
			if w < minimal && (!errors.As(got, &limit) || limit.Resource == 0 || limit.Resource != EvaluationUnits || limit.Limit != w || !errors.Is(got, ErrInsufficientStorage)) {
				t.Fatalf("%s W=%d: %v, want a unit refusal", call.name, w, got)
			}
			if w == minimal && got != nil {
				t.Fatalf("%s W=%d: %v", call.name, w, got)
			}
		}
	}
}

// TestEvaluationDigitCapRefusal checks the result digit axis: the cap
// counts stored digits and refuses with its own resource identity.
func TestEvaluationDigitCapRefusal(t *testing.T) {
	ctx := mustContext(t, 20, TiesToEven)
	for _, run := range []func(Budget) error{
		func(b Budget) error { _, _, err := New(2, 0).ExpWithContext(ctx.WithBudget(b)); return err },
		func(b Budget) error { _, _, err := New(2, 0).LnWithContext(ctx.WithBudget(b)); return err },
		func(b Budget) error { _, _, err := New(1, 25).Log10WithContext(Context{}.WithBudget(b)); return err },
		func(b Budget) error {
			_, _, err := New(4, 0).PowDecimalWithContext(New(25, 0), Context{}.WithBudget(b))
			return err
		},
		func(b Budget) error {
			_, _, err := New(4, 0).PowDecimalWithContext(New(10000000000005, -1), Context{}.WithBudget(b))
			return err
		},
	} {
		var limit *Error
		if err := run(Budget{MaxDigits: 1}); !errors.As(err, &limit) || limit.Resource == 0 || limit.Resource != EvaluationCoefficientDigits || limit.Limit != 1 {
			t.Fatalf("digit cap: %v", err)
		}
		// 4^(10^12+0.5) = 2^(2·10^12+1) needs about 6·10^11 digits.
		err := run(Budget{MaxDigits: 1 << 20})
		if err != nil && !errors.Is(err, ErrInexact) && !(errors.As(err, &limit) && limit.Limit == 1<<20) {
			t.Fatalf("admitted cap: %v", err)
		}
	}
}

// TestEvaluationFailureIdentities checks physical versus quota
// refusal: a physically unaddressable plan is an ordinary storage error.
func TestEvaluationFailureIdentities(t *testing.T) {
	ev := newEvaluator(Budget{})
	_ = ev.arena(math.MaxUint64 / 4)
	_, _, err := ev.failure("ExpWithContext")
	var op *Error
	if !errors.As(err, &op) || op.Resource != 0 || !errors.Is(err, ErrInsufficientStorage) || op.Op != "ExpWithContext" {
		t.Fatalf("physical refusal: %v", err)
	}
	var limit *Error
	for i, s := range []string{"Exp", "Ln", "Log10", "PowDecimal"} {
		var err error
		b := Budget{MaxWork: 1}
		switch i {
		case 0:
			_, _, err = New(2, 0).ExpWithContext(mustContext(t, 9, TiesToEven).WithBudget(b))
		case 1:
			_, _, err = New(2, 0).LnWithContext(mustContext(t, 9, TiesToEven).WithBudget(b))
		case 2:
			_, _, err = New(2, 0).Log10WithContext(mustContext(t, 9, TiesToEven).WithBudget(b))
		default:
			_, _, err = New(2, 0).PowDecimalWithContext(New(5, -1), mustContext(t, 9, TiesToEven).WithBudget(b))
		}
		if !errors.As(err, &limit) || limit.Resource == 0 || limit.Op != fmt.Sprintf("%sWithContext", s) {
			t.Fatalf("%s: %v", s, err)
		}
	}
}

// TestEvaluationFinalizationOrder checks the evaluation domain and
// finalization order: header-only domain errors precede any quota; a
// domain fact that needs a scan follows the scan's admission; an Exact
// refusal of an irrational result precedes work; and a trapped finite
// result is returned with its Error inside the attempt's units.
func TestEvaluationFinalizationOrder(t *testing.T) {
	tiny := Budget{MaxWork: 1}
	half, _ := Parse("0.5")
	ctx := mustContext(t, 9, TiesToEven)
	if _, _, err := New(-1, 0).LnWithContext(ctx.WithBudget(tiny)); !errors.Is(err, ErrInvalidOperation) {
		t.Fatalf("Ln(-1): %v", err)
	}
	if _, _, err := Zero().PowDecimalWithContext(half.Neg(), ctx.WithBudget(tiny)); !errors.Is(err, ErrDivisionByZero) {
		t.Fatalf("0^-0.5: %v", err)
	}
	// Integrality of y is a scan: a unit refusal may precede InvalidOperation.
	var limit *Error
	if _, _, err := New(-4, 0).PowDecimalWithContext(half, ctx.WithBudget(tiny)); !errors.As(err, &limit) || limit.Resource == 0 {
		t.Fatalf("(-4)^0.5 at W=1: %v", err)
	}
	if _, _, err := New(-4, 0).PowDecimalWithContext(half, ctx.WithBudget(Budget{MaxWork: 1 << 20})); !errors.Is(err, ErrInvalidOperation) {
		t.Fatalf("(-4)^0.5: %v", err)
	}
	exact := mustContext(t, 9, Exact)
	if _, _, err := New(2, 0).ExpWithContext(exact.WithBudget(tiny)); !errors.Is(err, ErrInexact) {
		t.Fatalf("Exp(2) Exact: %v", err)
	}
	trap, err := ctx.WithTraps(Inexact)
	if err != nil {
		t.Fatal(err)
	}
	w := uint64(1 << 20)
	bound, _ := BoundEvaluation(Budget{MaxWork: w})
	var got Decimal
	var c Conditions
	used := coldAllocatedWithin(func() { got, c, err = New(2, 0).LnWithContext(trap.WithBudget(Budget{MaxWork: w})) }, bound.HeapBytes)
	var ce *Error
	if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || got.String() != "0.693147181" || c != Rounded|Increased || used > bound.HeapBytes {
		t.Fatalf("trapped Ln(2): %s %v %v, %d > %d", got, c, err, used, bound.HeapBytes)
	}
}

// TestEvaluationEasyExactAtHugePrecision checks zero
// quotas and result digits: an exact result at precision 2^32−1 needs no
// precision-sized scratch.
func TestEvaluationEasyExactAtHugePrecision(t *testing.T) {
	ctx := mustContext(t, math.MaxUint32, TiesToEven)
	half, _ := Parse("0.5")
	for _, tc := range []struct {
		name string
		run  func() (Decimal, Conditions, error)
		want string
	}{
		{"Exp(0)", func() (Decimal, Conditions, error) { return Zero().ExpWithContext(ctx) }, "1"},
		{"Ln(1)", func() (Decimal, Conditions, error) { return One().LnWithContext(ctx) }, "0"},
		{"Log10(1E+5)", func() (Decimal, Conditions, error) { return New(1, 5).Log10WithContext(ctx) }, "5"},
		{"4^0.5", func() (Decimal, Conditions, error) { return New(4, 0).PowDecimalWithContext(half, ctx) }, "2"},
		{"1^1E+300", func() (Decimal, Conditions, error) { return One().PowDecimalWithContext(New(1, 300), ctx) }, "1"},
	} {
		var got Decimal
		var c Conditions
		var err error
		used := coldAllocatedWithin(func() { got, c, err = tc.run() }, 4096)
		if err != nil || got.String() != tc.want || c != 0 || used > 4096 {
			t.Fatalf("%s: %s %v %v after %d bytes", tc.name, got, c, err, used)
		}
	}
}

// TestEvaluationLongScanExhaustsUnits checks
// allocation-free loops and unlimited counters: the digit scan of an operand
// next to one is charged, so a small quota refuses it within its bound,
// while unlimited units add no lifetime ceiling.
func TestEvaluationLongScanExhaustsUnits(t *testing.T) {
	x, err := Parse("1." + fmt.Sprintf("%0100000d", 0) + "123456789")
	if err != nil {
		t.Fatal(err)
	}
	ctx := mustContext(t, 5, TiesToEven)
	w := uint64(20000)
	bound, _ := BoundEvaluation(Budget{MaxWork: w})
	var limit *Error
	used := coldAllocatedWithin(func() { _, _, err = x.LnWithContext(ctx.WithBudget(Budget{MaxWork: w})) }, bound.HeapBytes)
	if !errors.As(err, &limit) || limit.Resource == 0 || used > bound.HeapBytes {
		t.Fatalf("long scan: %v after %d > %d bytes", err, used, bound.HeapBytes)
	}
	ev := newEvaluator(Budget{})
	got, c, err := ev.ln(x, ctx, false, "LnWithContext")
	if err != nil || got.String() != "1.2346E-100001" || c != Inexact|Rounded|Increased {
		t.Fatalf("Ln(1+1.23456789E-100001) = %s %v %v", got, c, err)
	}
	// The leading zeros of t−1 size the loads, so one stage certifies.
	if ev.stages != 1 {
		t.Fatalf("Ln(1+1.23456789E-100001) took %d stages", ev.stages)
	}
}

// TestEvaluationAllocationInventory checks the bounded stack, the
// metered workspace, publication and live arenas: a
// call's heap allocations are exactly its admitted arenas plus the
// published holder, so no compiler-created escape is left uncharged.
func TestEvaluationAllocationInventory(t *testing.T) {
	half, _ := Parse("0.5")
	ctx16, ctx60 := mustContext(t, 16, TiesToEven), mustContext(t, 60, TowardZero)
	for _, tc := range []struct {
		name    string
		holders uint64 // publication allocations: 0 inline, 1 fused holder
		run     func() (uint64, error)
	}{
		{"Exp p16", 0, func() (uint64, error) {
			ev := newEvaluator(Budget{})
			_, _, err := ev.exp(New(15, -1), ctx16, "ExpWithContext")
			return ev.objects, err
		}},
		{"Exp p60", 1, func() (uint64, error) {
			ev := newEvaluator(Budget{})
			_, _, err := ev.exp(New(15, -1), ctx60, "ExpWithContext")
			return ev.objects, err
		}},
		{"Ln p16", 0, func() (uint64, error) {
			ev := newEvaluator(Budget{})
			_, _, err := ev.ln(New(2, 0), ctx16, false, "LnWithContext")
			return ev.objects, err
		}},
		{"Log10 p60", 1, func() (uint64, error) {
			ev := newEvaluator(Budget{})
			_, _, err := ev.ln(New(7, 0), ctx60, true, "Log10WithContext")
			return ev.objects, err
		}},
		{"Pow p16", 0, func() (uint64, error) {
			ev := newEvaluator(Budget{})
			_, _, err := ev.powDecimal(New(2, 0), half, ctx16, "PowDecimalWithContext")
			return ev.objects, err
		}},
		{"Pow exact", 0, func() (uint64, error) {
			ev := newEvaluator(Budget{})
			_, _, err := ev.powDecimal(New(50625, -4), half, Context{}, "PowDecimal")
			return ev.objects, err
		}},
	} {
		var objects uint64
		n := testing.AllocsPerRun(20, func() {
			var err error
			if objects, err = tc.run(); err != nil {
				t.Fatal(err)
			}
		})
		if uint64(n) != objects+tc.holders {
			t.Fatalf("%s: %v allocations, want %d arenas + %d holders", tc.name, n, objects, tc.holders)
		}
	}
}

// TestEvaluationScanIsCharged checks allocation-free
// loops: Log10 of 10^100000 written with 100000 zeros is exact and needs no
// arena, so its cost is the charged digit scan; a quota below the scan
// refuses and one above it succeeds.
func TestEvaluationScanIsCharged(t *testing.T) {
	x, err := Parse("1" + fmt.Sprintf("%0100000d", 0))
	if err != nil {
		t.Fatal(err)
	}
	var limit *Error
	if _, _, err := x.Log10WithContext(Context{}.WithBudget(Budget{MaxWork: 90000})); !errors.As(err, &limit) || limit.Resource == 0 {
		t.Fatalf("scan below quota: %v", err)
	}
	got, _, err := x.Log10WithContext(Context{}.WithBudget(Budget{MaxWork: 200000}))
	if err != nil || got.String() != "100000" {
		t.Fatalf("Log10(1E+100000) = %s %v", got, err)
	}
}

// TestEvaluationStagesShareOneLedger checks the nested
// cumulative ledger: every stage, constant and nested evaluation debits the
// one quota, so the charges of a refined attempt never exceed it.
func TestEvaluationStagesShareOneLedger(t *testing.T) {
	x, _ := Parse("0.916290731874155065183527211768011071450101219908262467791967881981")
	half, _ := Parse("0.5")
	for _, w := range []uint64{1 << 16, 1 << 18, 1 << 22} {
		ev := newEvaluator(Budget{MaxWork: w})
		_, _, err := ev.exp(x, mustContext(t, 1, TiesToEven), "ExpWithContext")
		if ev.meter.spent > w || ev.meter.spent != w-ev.meter.remaining {
			t.Fatalf("W=%d: spent %d, remaining %d (%v)", w, ev.meter.spent, ev.meter.remaining, err)
		}
		ev = newEvaluator(Budget{MaxWork: w})
		_, _, err = ev.powDecimal(New(3, 0), half, mustContext(t, 30, TiesToEven), "PowDecimalWithContext")
		if ev.meter.spent > w || ev.meter.spent != w-ev.meter.remaining {
			t.Fatalf("pow W=%d: spent %d, remaining %d (%v)", w, ev.meter.spent, ev.meter.remaining, err)
		}
	}
}

// TestDivPairIsDirectedBeyondOneWord checks the series divisor pairs on
// both sides of 2^32: each quotient bounds a/(p·q) from the requested
// side, keeps all but the limb a divisor above 10^9 costs, and leaves the
// evaluator valid. The series of Sin, Cos, Sinh and Tanh reach such a
// product near 300,000 digits.
func TestDivPairIsDirectedBeyondOneWord(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x64697670, 1))
	var split, single int
	for range 4000 {
		L := 3 + rng.IntN(12)
		m := new(big.Int).SetUint64(1 + rng.Uint64N(1<<62))
		for range rng.IntN(L + 3) {
			m.Mul(m, big.NewInt(1_000_000_000)).Add(m, new(big.Int).SetUint64(rng.Uint64N(1_000_000_000)))
		}
		src := make([]uint32, len(m.Bits())*3+4)
		a := enclosureNum(src, m, int64(rng.IntN(7)-3))
		j := uint64(1) << uint(rng.IntN(31))
		j += rng.Uint64N(j)
		p, q := 2*j-1, 2*j
		exact := enclosureRat(a)
		exact.Quo(exact, new(big.Rat).SetInt(new(big.Int).Mul(new(big.Int).SetUint64(p), new(big.Int).SetUint64(q))))
		// B^(top−1) ≤ a/(p·q) < B^top, so L−1 kept limbs err below
		// B^(top−L+1) at each of the two roundings.
		base := big.NewRat(1_000_000_000, 1)
		tolerance := big.NewRat(2, 1)
		for range L - 1 {
			tolerance.Quo(tolerance, base)
		}
		for scaled := new(big.Rat).Set(exact); scaled.Cmp(big.NewRat(1, 1)) >= 0; scaled.Quo(scaled, base) {
			tolerance.Mul(tolerance, base)
		}
		for scaled := new(big.Rat).Mul(exact, base); scaled.Cmp(big.NewRat(1, 1)) < 0; scaled.Mul(scaled, base) {
			tolerance.Quo(tolerance, base)
		}
		var bounds [2]*big.Rat
		for i, up := range []bool{false, true} {
			ev := newEvaluator(Budget{})
			dst := make([]uint32, max(len(a.m), L+1)+2)
			got := ev.divPair(dst, a, p, q, L, up)
			if !ev.ok() {
				t.Fatalf("divPair(%v, %d, %d) broke the evaluation", m, p, q)
			}
			bounds[i] = enclosureRat(got)
			if cmp := bounds[i].Cmp(exact); up && cmp < 0 || !up && cmp > 0 {
				t.Fatalf("divPair(%v, %d, %d, up=%t) = %v is on the wrong side of %v", m, p, q, up, bounds[i], exact)
			}
			if len(got.m) > L {
				t.Fatalf("divPair returned %d limbs, want at most %d", len(got.m), L)
			}
			if width := new(big.Rat).Sub(bounds[i], exact); width.Abs(width).Cmp(tolerance) > 0 {
				t.Fatalf("divPair(%v, %d, %d, up=%t) is %v from the quotient at %d limbs, beyond %v", m, p, q, up, width, L, tolerance)
			}
		}
		if p*q >= 1<<32 {
			split++
		} else {
			single++
		}
	}
	if split < 1000 || single < 1000 {
		t.Fatalf("vacuous path coverage: %d split, %d single", split, single)
	}
}
