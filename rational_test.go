// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"runtime"
	"runtime/debug"
	"slices"
	"strings"
	"testing"
	"time"
)

func randomRat(rng *rand.Rand, maxDigits int) *big.Rat {
	digits := func(n int) *big.Int {
		var b strings.Builder
		b.WriteByte(byte('1' + rng.IntN(9)))
		for range n - 1 {
			b.WriteByte(byte('0' + rng.IntN(10)))
		}
		v, _ := new(big.Int).SetString(b.String(), 10)
		return v
	}
	n := digits(1 + rng.IntN(maxDigits))
	var d *big.Int
	if rng.IntN(3) == 0 {
		// Terminating denominators: 2^a·5^b times a small odd factor.
		d = new(big.Int).Lsh(big.NewInt(1), uint(rng.IntN(40)))
		d.Mul(d, new(big.Int).Exp(big.NewInt(5), big.NewInt(int64(rng.IntN(30))), nil))
		d.Mul(d, big.NewInt([]int64{1, 1, 3, 7}[rng.IntN(4)]))
	} else {
		d = digits(1 + rng.IntN(maxDigits))
	}
	if rng.IntN(2) == 0 {
		n.Neg(n)
	}
	if rng.IntN(15) == 0 {
		n.SetInt64(0)
	}
	return new(big.Rat).SetFrac(n, d)
}

// TestFromRatToExponentAgainstRationalOracle covers non-terminating
// conversion with an explicit exponent target: FromRatToExponent
// rounds once from the exact rational in every mode, with the division
// oracle (ideal exponent 0) deciding value, conditions and direction.
func TestFromRatToExponentAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(46, 1))
	for range 8000 {
		r := randomRat(rng, 60)
		target := int64(rng.IntN(121) - 90)
		mode := allDivModes[rng.IntN(len(allDivModes))]
		want := oracleToExponent(r, 0, target, mode)
		if r.Sign() == 0 {
			want = divExpect{coefficient: new(big.Int), exponent: target}
		}
		got, conditions, err := FromRatToExponent(r, int32(target), mode)
		checkDivOutcome(t, fmt.Sprintf("%s t=%d %v", r.RatString(), target, mode), got, conditions, err, want, r.Sign() < 0)
	}
}

// TestFromRatWithContextAgainstRationalOracle covers FromRatWithContext:
// one rounding to p digits, unguarded and guarded (as for Div),
// against the division oracles with ideal exponent 0.
func TestFromRatWithContextAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(46, 2))
	for range 8000 {
		r := randomRat(rng, 60)
		if r.Sign() == 0 {
			continue
		}
		p := int64(1 + rng.IntN(50))
		mode := allDivModes[rng.IntN(len(allDivModes))]
		var ctx Context
		var want divExpect
		if rng.IntN(2) == 0 {
			ctx, _ = NewContext(uint32(p), mode, nil, 0)
			want = oracleContext(r, 0, p, mode)
		} else {
			emin := int64(rng.IntN(61) - 50)
			emax := emin + int64(rng.IntN(60))
			ctx, _ = NewContext(uint32(p), mode, &ExponentGuards{Emin: int32(emin), Emax: int32(emax)}, 0)
			want = oracleGuarded(r, 0, p, emin, emax, mode)
		}
		got, conditions, err := FromRatWithContext(r, ctx)
		checkDivOutcome(t, fmt.Sprintf("%s p=%d %v", r.RatString(), p, mode), got, conditions, err, want, r.Sign() < 0)
	}
}

// TestFromRatExactAgainstRationalOracle covers non-terminating
// conversion without a rounding instruction and the terminating case: FromRat is exact
// at the largest exponent not above zero, or refuses with the remedy.
func TestFromRatExactAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(46, 3))
	for range 8000 {
		r := randomRat(rng, 50)
		got, err := FromRat(r)
		want, terminates := oracleExact(r, 0)
		label := r.RatString()
		if r.Sign() == 0 {
			if err != nil || !got.IsZero() || got.Exponent() != 0 {
				t.Fatalf("%s: (%v, %v)", label, got, err)
			}
			continue
		}
		if !terminates {
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || !strings.Contains(err.Error(), "FromRatWithContext") || !isZeroValue(got) {
				t.Fatalf("%s: (%v, %v), want remedy refusal", label, got, err)
			}
			continue
		}
		checkDivOutcome(t, label, got, 0, err, want, r.Sign() < 0)
	}
}

// TestFromRatMatchesBigIntDivComposition pins the composition
// identity: every FromRat* result, conditions included, equals converting
// the numerator and denominator with FromBigInt and dividing.
func TestFromRatMatchesBigIntDivComposition(t *testing.T) {
	rng := rand.New(rand.NewPCG(46, 4))
	for range 3000 {
		r := randomRat(rng, 30)
		n, _ := FromBigInt(r.Num())
		d, _ := FromBigInt(r.Denom())
		mode := allDivModes[rng.IntN(len(allDivModes))]
		target := int32(rng.IntN(61) - 40)
		a, ac, ae := FromRatToExponent(r, target, mode)
		b, bc, be := n.DivToExponent(d, target, mode)
		if (ae == nil) != (be == nil) || ae == nil && (!a.Equal(b) || a.Exponent() != b.Exponent() || ac != bc) {
			t.Fatalf("%s t=%d %v: FromRat (%v,%v,%v) vs Div (%v,%v,%v)", r.RatString(), target, mode, a, ac, ae, b, bc, be)
		}
		ctx, _ := NewContext(uint32(1+rng.IntN(40)), mode, nil, 0)
		a, ac, ae = FromRatWithContext(r, ctx)
		b, bc, be = n.DivWithContext(d, ctx)
		if (ae == nil) != (be == nil) || ae == nil && (!a.Equal(b) || a.Exponent() != b.Exponent() || ac != bc) {
			t.Fatalf("%s ctx: FromRat (%v,%v,%v) vs Div (%v,%v,%v)", r.RatString(), a, ac, ae, b, bc, be)
		}
		a, ae = FromRat(r)
		b, be = n.Div(d)
		if (ae == nil) != (be == nil) || ae == nil && (!a.Equal(b) || a.Exponent() != b.Exponent()) {
			t.Fatalf("%s exact: FromRat (%v,%v) vs Div (%v,%v)", r.RatString(), a, ae, b, be)
		}
	}
}

// TestFromRatDirectedEnclosure covers directed rounding for rationals:
// Floor and Ceiling results bracket the exact value and are adjacent on the
// grid, reporting Decreased and Increased.
func TestFromRatDirectedEnclosure(t *testing.T) {
	for _, s := range []string{"1/3", "2/3", "-1/3", "1/7", "22/7", "-355/113"} {
		r, _ := new(big.Rat).SetString(s)
		for _, p := range []uint32{1, 5, 17, 34} {
			lo, lc, le := FromRatWithContext(r, mustContext(t, p, TowardNegativeInfinity))
			hi, hc, he := FromRatWithContext(r, mustContext(t, p, TowardPositiveInfinity))
			q := directionPrecisionQuantum(r, int64(p), false, 0)
			checkRoundingDirection(t, s, r, TowardNegativeInfinity, lo, lc, le)
			checkRoundingDirection(t, s, r, TowardPositiveInfinity, hi, hc, he)
			checkDirectedEnclosure(t, fmt.Sprintf("%s p=%d", s, p), r, q, lo, lc, hi, hc)
		}
	}
	lo, _, _ := FromRatWithContext(big.NewRat(1, 3), mustContext(t, 5, TowardNegativeInfinity))
	hi, _, _ := FromRatWithContext(big.NewRat(1, 3), mustContext(t, 5, TowardPositiveInfinity))
	if lo.String() != "0.33333" || hi.String() != "0.33334" {
		t.Fatalf("directed enclosure vector: %s, %s", lo, hi)
	}
}

// TestFromRatSourceValidation covers source validation: nil, malformed
// zero-top words and a nonpositive denominator written through the
// reference are ConversionSyntax; nil wins over an unknown mode; non-reduced
// pairs convert by value.
func TestFromRatSourceValidation(t *testing.T) {
	check := func(label string, err error, op string, code ErrorCode) {
		t.Helper()
		var oe *Error
		if !errors.Is(err, code) || !errors.As(err, &oe) || oe.Op != op {
			t.Fatalf("%s: %v, want %s %v", label, err, op, code)
		}
	}
	_, _, err := FromRatToExponent(nil, 0, RoundingMode(99))
	check("nil beats mode", err, "FromRatToExponent", ErrConversionSyntax)
	_, err = FromRat(nil)
	check("nil", err, "FromRat", ErrConversionSyntax)
	var ce *Error
	if _, _, err := FromRatToExponent(big.NewRat(1, 3), 0, RoundingMode(99)); !errors.As(err, &ce) || ce.Code != ErrInvalidContext {
		t.Fatalf("unknown mode: %v", err)
	}
	malformed := big.NewRat(7, 3)
	malformed.Num().SetBits([]big.Word{7, 1})
	malformed.Num().Bits()[1] = 0 // raw write leaves a zero top word
	_, err = FromRat(malformed)
	check("zero-top numerator", err, "FromRat", ErrConversionSyntax)
	negative := big.NewRat(1, 3)
	negative.Denom().SetInt64(-3)
	_, _, err = FromRatWithContext(negative, mustContext(t, 5, TiesToEven))
	check("negative denominator", err, "FromRatWithContext", ErrConversionSyntax)
	for _, tc := range []struct {
		n, d int64
		want string
	}{{2, 4, "0.5"}, {3, 6, "0.5"}, {10, 4, "2.5"}, {-6, 8, "-0.75"}} {
		r := big.NewRat(1, 7)
		r.Num().SetInt64(tc.n)
		r.Denom().SetInt64(tc.d)
		got, err := FromRat(r)
		if err != nil || got.String() != tc.want {
			t.Fatalf("non-reduced %d/%d: (%v, %v), want %s", tc.n, tc.d, got, err, tc.want)
		}
	}
}

// TestFromRatBoundaryWitnesses pins three boundary cases: a huge
// power of two at p=34 is correct (not zero), the tiny shortcut does not
// fire on a false premise, and the bare-path factor-5 loop is budgeted
// before any allocation.
func TestFromRatBoundaryWitnesses(t *testing.T) {
	huge := new(big.Rat).SetInt(new(big.Int).Lsh(big.NewInt(1), 10_000_000))
	got, _, err := FromRatWithContext(huge, mustContext(t, 34, TiesToEven))
	if err != nil || got.CoefficientDigits() != 34 {
		t.Fatalf("2^(10^7) at p=34: (%v, %v)", got, err)
	}
	wantExp := int32(len(new(big.Int).Lsh(big.NewInt(1), 10_000_000).String())) - 34
	if got.Exponent() != wantExp {
		t.Fatalf("2^(10^7) exponent %d, want %d", got.Exponent(), wantExp)
	}
	edge := new(big.Rat).SetInt(new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 332193), big.NewInt(1)))
	got, _, err = FromRatToExponent(edge, 100000, TiesToEven)
	if err != nil || got.IsZero() {
		t.Fatalf("tiny-shortcut premise: (%v, %v), want 1E+100000", got, err)
	}
	fives := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Exp(big.NewInt(5), big.NewInt(1_000_000), nil))
	allocs := testing.AllocsPerRun(3, func() {
		if _, _, err := FromRatWithContext(fives, Context{}.WithBudget(Budget{MaxWork: 1})); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("1/5^(10^6) under cap 1: %v", err)
		}
	})
	if allocs > 1 {
		t.Fatalf("1/5^(10^6) refusal allocated %g objects (want only the error)", allocs)
	}
}

// TestRatAdjustedLowBracket covers the a_lo bracket: for 400 random
// bit-length pairs in 1..3000 the computed a_lo never exceeds the true
// adjusted exponent of any value with those bit lengths and trails it by at
// most one, checked on the extreme values 2^(bn−1)/(2^bd−1) and
// (2^bn−1)/2^(bd−1) with exact integer logarithms; continued-fraction
// witnesses of log10 2 extend the check to |Δ−1| ≈ 5.8·10^11 arithmetically.
// The resulting p or p+1 quotient digits are exercised end to end by the
// context oracle tests.
func TestRatAdjustedLowBracket(t *testing.T) {
	rng := rand.New(rand.NewPCG(46, 5))
	floorLog10 := func(r *big.Rat) int64 {
		a := int64(len(new(big.Int).Quo(r.Num(), r.Denom()).String())) - 1
		if r.Cmp(big.NewRat(1, 1)) < 0 {
			a = -1
			for new(big.Rat).Mul(r, new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(-a), nil))).Cmp(big.NewRat(1, 1)) < 0 {
				a--
			}
		}
		return a
	}
	for range 400 {
		bn, bd := uint64(1+rng.IntN(3000)), uint64(1+rng.IntN(3000))
		aLow, ok := ratAdjustedLow(bn, bd)
		if !ok {
			t.Fatal("bracket overflow")
		}
		one := big.NewInt(1)
		minN := new(big.Int).Lsh(one, uint(bn-1))
		maxN := new(big.Int).Sub(new(big.Int).Lsh(one, uint(bn)), one)
		minD := new(big.Int).Lsh(one, uint(bd-1))
		maxD := new(big.Int).Sub(new(big.Int).Lsh(one, uint(bd)), one)
		low := floorLog10(new(big.Rat).SetFrac(minN, maxD))
		high := floorLog10(new(big.Rat).SetFrac(maxN, minD))
		if aLow > low || high-aLow > 1 {
			t.Fatalf("bn=%d bd=%d: a_lo=%d, adjusted range [%d,%d]", bn, bd, aLow, low, high)
		}
	}
	// Continued-fraction witnesses of log10 2: (Δ−1)·log10 2 lies within
	// |Δ−1|·10^−18 of an integer, where swapping the sign's constant breaks
	// a_lo ≤ ⌊(Δ−1)·log10 2⌋ or loosens the bracket past one.
	log2, _ := new(big.Rat).SetString("0.30102999566398119521373889472449302676818988146211")
	for _, x := range []int64{1923400330, -1923400330, 82361153417, -82361153417, 496090320832, -496090320832, 578451474249, -578451474249} {
		bn, bd := uint64(1), uint64(-x)
		if x >= 0 {
			bn, bd = uint64(x)+2, 1
		}
		aLow, ok := ratAdjustedLow(bn, bd)
		v := new(big.Rat).Mul(big.NewRat(x, 1), log2)
		floor := new(big.Int).Div(v.Num(), v.Denom()).Int64() // Euclidean: floor for a positive denominator
		if !ok || aLow > floor || floor-aLow > 1 {
			t.Fatalf("Δ−1=%d: a_lo=%d, ⌊(Δ−1)·log10 2⌋=%d", x, aLow, floor)
		}
	}
	if _, ok := ratAdjustedLow(1<<40, 1); !ok {
		t.Fatal("a_lo must handle 2^40-bit differences")
	}
}

// TestFromRatBudgetBoundaries covers budget boundaries for rationals: the precharge B
// and the complete charge W = B + 2N + 1 admit at equality and refuse one
// below through all three budgeted forms, as does the digit quota N.
func TestFromRatBudgetBoundaries(t *testing.T) {
	rng := rand.New(rand.NewPCG(46, 6))
	for range 1500 {
		r := randomRat(rng, 40)
		if r.Sign() == 0 {
			continue
		}
		s, _ := readRat(r)
		var (
			charge uint64
			f      func(Budget) (Decimal, error)
		)
		switch rng.IntN(2) {
		case 0:
			target := int64(rng.IntN(61) - 40)
			charge = s.plan(target).charge
			f = func(b Budget) (Decimal, error) {
				d, _, err := FromRatToExponentWithBudget(r, int32(target), TiesToEven, b)
				return d, err
			}
		default:
			p := int64(1 + rng.IntN(40))
			aLow, _ := ratAdjustedLow(s.bn, s.bd)
			charge = s.plan(aLow - p + 1).charge
			if uint64(p) > s.bn+s.bd { // exact-first attempt, then the division
				den := new(big.Int).Set(r.Denom())
				for _, f := range []int64{2, 5} {
					for new(big.Int).Mod(den, big.NewInt(f)).Sign() == 0 {
						den.Quo(den, big.NewInt(f))
					}
				}
				if den.Cmp(big.NewInt(1)) == 0 {
					charge = s.exactPlan().charge
				} else {
					charge += s.exactPlan().charge
				}
			}
			ctx, _ := NewContext(uint32(p), TiesToEven, nil, 0)
			f = func(b Budget) (Decimal, error) {
				d, _, err := FromRatWithContext(r, ctx.WithBudget(b))
				return d, err
			}
		}
		full, err := f(Budget{})
		if err != nil {
			t.Fatal(err)
		}
		n := max(full.CoefficientDigits(), 1)
		w := charge + 2*n + 1
		for _, tc := range []struct {
			budget Budget
			ok     bool
		}{
			{Budget{MaxWork: charge - 1}, false},
			{Budget{MaxWork: w - 1}, false},
			{Budget{MaxWork: w}, true},
			{Budget{MaxDigits: n - 1}, n == 1},
			{Budget{MaxDigits: n}, true},
		} {
			if tc.budget == (Budget{}) {
				continue
			}
			got, err := f(tc.budget)
			if tc.ok != (err == nil) || tc.ok && !got.Equal(full) || !tc.ok && !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("%s %+v (B=%d N=%d): (%v, %v)", r.RatString(), tc.budget, charge, n, got, err)
			}
		}
	}
}

// TestFromRatVectors checks the rational conversion vectors:
// 1/3, 2/3, −1/3 and 1/7 at several precisions and exponents in every
// mode; 1/8 and 3/40 exact and unflagged in every mode; and overflow and
// underflow at the guard boundaries, all against the division oracles.
func TestFromRatVectors(t *testing.T) {
	for _, text := range []string{"1/3", "2/3", "-1/3", "1/7", "1/8", "3/40"} {
		r, _ := new(big.Rat).SetString(text)
		terminating := text == "1/8" || text == "3/40"
		for _, mode := range allDivModes {
			for _, p := range []int64{1, 2, 7, 16, 34, 50} {
				got, conditions, err := FromRatWithContext(r, mustContext(t, uint32(p), mode))
				label := fmt.Sprintf("%s p=%d %v", text, p, mode)
				checkDivOutcome(t, label, got, conditions, err, oracleContext(r, 0, p, mode), r.Sign() < 0)
				if terminating && p >= 3 && (err != nil || conditions != 0) {
					t.Fatalf("%s: terminating value flagged: (%v, %v, %v)", label, got, conditions, err)
				}
			}
			for _, target := range []int64{-40, -6, -3, -1, 0, 1} {
				got, conditions, err := FromRatToExponent(r, int32(target), mode)
				label := fmt.Sprintf("%s t=%d %v", text, target, mode)
				checkDivOutcome(t, label, got, conditions, err, oracleToExponent(r, 0, target, mode), r.Sign() < 0)
				if terminating && target <= -3 && (err != nil || conditions != 0) {
					t.Fatalf("%s: terminating value flagged: (%v, %v, %v)", label, got, conditions, err)
				}
			}
			for _, g := range []struct {
				r          string
				emin, emax int64
			}{
				{"100000000000000000000000/3", -10, 20}, {"-100000000000000000000000/3", -10, 20},
				{"1/300000000000000000000", -20, 20}, {"-1/300000000000000000000", -20, 20},
				{"1/8", -2, 20}, {"99999999/1", -20, 7},
			} {
				r, _ := new(big.Rat).SetString(g.r)
				ctx, err := NewContext(7, mode, &ExponentGuards{Emin: int32(g.emin), Emax: int32(g.emax)}, 0)
				if err != nil {
					t.Fatal(err)
				}
				got, conditions, err := FromRatWithContext(r, ctx)
				checkDivOutcome(t, fmt.Sprintf("%s guards [%d,%d] %v", g.r, g.emin, g.emax, mode), got, conditions, err, oracleGuarded(r, 0, 7, g.emin, g.emax, mode), r.Sign() < 0)
			}
		}
		exact, err := FromRat(r)
		if terminating != (err == nil) || terminating && exact.String() != map[string]string{"1/8": "0.125", "3/40": "0.075"}[text] {
			t.Fatalf("FromRat(%s): (%v, %v)", text, exact, err)
		}
	}
}

// TestFromRatTinyShortcutBoundary pins the tiny shortcut (|r| < 10^t/2
// proved from bit lengths alone) at its edge: bn+1 = bd+⌊t·C⌋, the
// largest numerators that must still take the division, against the
// division oracle in every mode.
func TestFromRatTinyShortcutBoundary(t *testing.T) {
	one := big.NewInt(1)
	for target := int64(1); target <= 60; target++ {
		hi, lo := bits.Mul64(uint64(target), 33219280948873623)
		floor, _ := bits.Div64(hi, lo, 10_000_000_000_000_000)
		for _, d := range []int64{1, 3, 7, 1000003} {
			den := big.NewInt(d)
			bn := uint64(den.BitLen()) + floor - 1
			for _, n := range []*big.Int{
				new(big.Int).Sub(new(big.Int).Lsh(one, uint(bn)), one),
				new(big.Int).Lsh(one, uint(bn-1)),
			} {
				r := new(big.Rat).SetFrac(n, den)
				for _, mode := range allDivModes {
					got, conditions, err := FromRatToExponent(r, int32(target), mode)
					checkDivOutcome(t, fmt.Sprintf("%s t=%d %v", r.RatString(), target, mode), got, conditions, err, oracleToExponent(r, 0, target, mode), false)
				}
			}
		}
	}
}

// TestFromRatPlanningWitnesses pins charges derived independently
// of the planning code: a guarded context plans at max(t′, Etiny), so a
// deep subnormal rational costs the tiny shortcut, and the bare path
// precharges its factor-5 loop b_max·(wd+1) before running it.
func TestFromRatPlanningWitnesses(t *testing.T) {
	deep := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Mul(big.NewInt(3), new(big.Int).Exp(big.NewInt(10), big.NewInt(5000), nil)))
	ctx, err := NewContext(7, TiesToEven, &ExponentGuards{Emin: -20, Emax: 20}, 0)
	if err != nil {
		t.Fatal(err)
	}
	got, conditions, err := FromRatWithContext(deep, ctx.WithBudget(Budget{MaxWork: 1000}))
	if err != nil || !got.IsZero() || got.Exponent() != -26 || conditions&Underflow == 0 {
		t.Fatalf("deep subnormal under a 1000-unit budget: (%v, %v, %v)", got, conditions, err)
	}
	// 1/5^1000, computed from the tariff terms outside the code:
	// bd = 2322, a = 0, b_max = ⌊2322·0.430676558073393051⌋ = 1000,
	// wn = 1, wd = 37, wm = 52. Loop 1000·38 = 38,000; division 38; power
	// ⌈4·52²/3⌉+52 = 3,658; scale 52; conversion U = 1,022 digits,
	// 1022·114 = 116,508; reads 38. B = 158,294, N = 302 (2^1000), so
	// W = B+2N+1 = 158,899.
	fifth := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Exp(big.NewInt(5), big.NewInt(1000), nil))
	if _, _, err := FromRatWithContext(fifth, Context{}.WithBudget(Budget{MaxWork: 158_898})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("1/5^1000 at W−1: %v", err)
	}
	if got, _, err := FromRatWithContext(fifth, Context{}.WithBudget(Budget{MaxWork: 158_899})); err != nil || got.Exponent() != -1000 {
		t.Fatalf("1/5^1000 at W: (%v, %v)", got, err)
	}
	// Rat strips decimal zeros before its caps: 1.000000 is 1/1.
	plain, _ := Parse("1.000000")
	if back, err := plain.RatWithBudget(nil, Budget{MaxDigits: 1}); err != nil || back.Cmp(big.NewRat(1, 1)) != 0 {
		t.Fatalf("1.000000 under a one-digit cap: (%v, %v)", back, err)
	}
}

// TestFromRatNonReducedSharedTwos checks that twos shared by
// a non-reduced numerator and denominator cancel by value on the bare
// path, so its exponent is that of the reduced value.
func TestFromRatNonReducedSharedTwos(t *testing.T) {
	for _, tc := range []struct {
		numShift, denShift uint
		num, den           int64
		want               string
	}{
		{40, 45, 3, 1, "0.09375"},
		{45, 40, 3, 1, "96"},
		{64, 64, 1, 1, "1"},
		{200, 203, 5, 25, "0.025"},
	} {
		r := new(big.Rat).SetInt64(1)
		r.Num().Lsh(big.NewInt(tc.num), tc.numShift)
		r.Denom().Lsh(big.NewInt(tc.den), tc.denShift)
		got, err := FromRat(r)
		if err != nil || got.String() != tc.want {
			t.Fatalf("%d·2^%d / %d·2^%d: (%v, %v), want %s", tc.num, tc.numShift, tc.den, tc.denShift, got, err, tc.want)
		}
	}
}

// TestFromRatZeroTariff checks that a zero rational publishes
// under the division zero-dividend tariff (B = 1, N = 1, W = 4), like Div.
func TestFromRatZeroTariff(t *testing.T) {
	zero := new(big.Rat)
	for limit, ok := range map[uint64]bool{1: false, 3: false, 4: true} {
		got, _, err := FromRatWithContext(zero, Context{}.WithBudget(Budget{MaxWork: limit}))
		if ok != (err == nil) || ok && (!got.IsZero() || got.Exponent() != 0) || !ok && !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("zero at %d: (%v, %v)", limit, got, err)
		}
	}
}

// TestFromRatContextWorkIndependentOfUnusedPrecision covers the exact-first
// rule: at the largest valid
// context precision a terminating rational is published exactly with work and
// memory bounded by its own size, guarded or not, while its value, cohort
// and conditions equal the exact oracle's.
func TestFromRatContextWorkIndependentOfUnusedPrecision(t *testing.T) {
	tiny := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), 1074))
	for _, r := range []*big.Rat{big.NewRat(1, 2), big.NewRat(-3, 40), tiny, big.NewRat(123456789, 1)} {
		for _, guards := range []*ExponentGuards{nil, {Emin: -2000, Emax: 2000}, {Emin: -500, Emax: 500}} {
			precision := uint32(math.MaxUint32)
			if guards != nil { // the largest precision whose Etiny fits int32
				precision = uint32(int64(guards.Emin) - math.MinInt32 + 1)
			}
			ctx, err := NewContext(precision, TiesToEven, guards, 0)
			if err != nil {
				t.Fatal(err)
			}
			var before, after runtime.MemStats
			runtime.ReadMemStats(&before)
			got, conditions, err := FromRatWithContext(r, ctx)
			runtime.ReadMemStats(&after)
			// Each value's adjusted exponent lies inside every guard pair, so
			// the oracle is the exact value at the largest exponent ≤ 0 (a
			// precision oracle would itself build 10^(2^32)).
			want, ok := oracleExact(r, 0)
			if !ok {
				t.Fatalf("%s: vector must terminate", r.RatString())
			}
			checkDivOutcome(t, fmt.Sprintf("%s guards %v", r.RatString(), guards), got, conditions, err, want, r.Sign() < 0)
			if bytes := after.TotalAlloc - before.TotalAlloc; bytes > 64<<10 {
				t.Fatalf("%s: allocated %d bytes at p = %d", r.RatString(), bytes, precision)
			}
		}
	}
}

// TestRatAdmittedRefusesBeyondAddressSpace pins the physical admission check: a
// plan of 2^40 operand words needs a scratch envelope of
// 8·2^40·(8+41) bytes ≈ 431 TiB, beyond every supported target's address
// window, while a one-word plan is admitted; oversized result limbs are
// refused too.
func TestRatAdmittedRefusesBeyondAddressSpace(t *testing.T) {
	if !ratAdmitted(1, 1) {
		t.Fatal("a one-word plan must be admitted")
	}
	if ratAdmitted(1<<40, 1) {
		t.Fatal("a 2^40-word plan must be refused")
	}
	if ratAdmitted(1, math.MaxUint64) {
		t.Fatal("a 2^64-digit result must be refused")
	}
}

// TestFromRatTariffMatchesIndependentWitnesses pins the precharge B at values
// computed outside the code from the tariff formulas: the k ≥ 0, k < 0 and
// tiny paths and a huge shape, a 10^6-bit numerator and denominator
// at p = 34. Each is refused at B−1 (allocating at most the error) and at W−1, and
// admitted at W = B+2N+1 with the unbudgeted result.
func TestFromRatTariffMatchesIndependentWitnesses(t *testing.T) {
	pow := func(b, e int64) *big.Int { return new(big.Int).Exp(big.NewInt(b), big.NewInt(e), nil) }
	for _, tc := range []struct {
		name      string
		n, d      *big.Int
		target    int32
		precision uint32
		charge    uint64
	}{
		{"k>=0 (10^200+7)/3^300 at -50", new(big.Int).Add(pow(10, 200), big.NewInt(7)), pow(3, 300), -50, 0, 2239},
		// The quotient 10^300/7 has 995 bits, so wq =
		// ⌈(bn+1−bd−⌊j·C⌋)/64⌉ = ⌈995/64⌉ = 16 words (a plain word sum gives
		// 15, an undercount); Uq = 309, conversion 309·35 = 10815, division
		// 2·17·8 = 272, power 54, scale 6, wn 21, wD 7: B = 11175.
		{"k<0 10^400/7 at 100", pow(10, 400), big.NewInt(7), 100, 0, 11175},
		{"tiny 1/10^100 at 1", big.NewInt(1), pow(10, 100), 1, 0, 1},
		{"3^630000/7^356000 p=34", pow(3, 630000), pow(7, 356000), 0, 34, 406566},
		{"exact-first 3/40 p=34", big.NewInt(3), big.NewInt(40), 0, 34, 211},
	} {
		r := new(big.Rat).SetFrac(tc.n, tc.d)
		call := func(b Budget) (Decimal, error) {
			if tc.precision != 0 {
				ctx, _ := NewContext(tc.precision, TiesToEven, nil, 0)
				d, _, err := FromRatWithContext(r, ctx.WithBudget(b))
				return d, err
			}
			d, _, err := FromRatToExponentWithBudget(r, tc.target, TiesToEven, b)
			return d, err
		}
		start := time.Now()
		full, err := call(Budget{})
		elapsed := time.Since(start)
		if err != nil {
			t.Fatalf("%s: %v", tc.name, err)
		}
		w := tc.charge + 2*max(full.CoefficientDigits(), 1) + 1
		for _, limit := range []uint64{tc.charge - 1, w - 1} {
			if limit == 0 {
				continue
			}
			if _, err := call(Budget{MaxWork: limit}); !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("%s at %d (B=%d, W=%d): %v", tc.name, limit, tc.charge, w, err)
			}
		}
		// B−1 refuses in the precharge, before any math/big work; W−1 is
		// the final publish check after the division.
		if tc.charge > 1 {
			if allocs := testing.AllocsPerRun(3, func() { _, _ = call(Budget{MaxWork: tc.charge - 1}) }); allocs > 1 {
				t.Fatalf("%s: precharge refusal allocated %v times", tc.name, allocs)
			}
		}
		got, err := call(Budget{MaxWork: w})
		if err != nil || !got.Equal(full) || got.Exponent() != full.Exponent() {
			t.Fatalf("%s at W=%d: (%v, %v), want %v", tc.name, w, got, err, full)
		}
		t.Logf("%s: B=%d W=%d unbudgeted %v", tc.name, tc.charge, w, elapsed)
	}
}

// TestRatWithBudgetChargesConversionWork pins RatWithBudget's work quota
// at W_BigInt(digits) + (j+1)·wc, computed by hand for
// 200,000 sevens at exponent −1: W_BigInt = (22223+22223)² + 44446 =
// 1,975,491,362; wc = ⌈(664,386+1)/64⌉ = 10,382 so the loop is 20,764;
// 10^1 costs power 3 and 1 word; W = 1,975,512,130.
func TestRatWithBudgetChargesConversionWork(t *testing.T) {
	d, err := Parse(strings.Repeat("7", 200000) + "E-1")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := d.RatWithBudget(nil, Budget{MaxWork: 1_975_512_129}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("W−1: %v", err)
	}
	if allocs := testing.AllocsPerRun(3, func() { _, _ = d.RatWithBudget(nil, Budget{MaxWork: 1_000_000}) }); allocs > 1 {
		t.Fatalf("refusal allocated %v times", allocs)
	}
	got, err := d.RatWithBudget(nil, Budget{MaxWork: 1_975_512_130})
	if err != nil || got.Denom().Cmp(big.NewInt(10)) != 0 {
		t.Fatalf("W: (%v, %v)", got, err)
	}
	// With 50 trailing zeros at exponent −60 the strip charges digits(c):
	// W_BigInt(200,000) = 1,975,491,362; j = 10, so the loop is 11·10,382 =
	// 114,202; power 3; 1 word; strip 200,050; W = 1,975,805,618.
	zeros, err := Parse(strings.Repeat("7", 200000) + strings.Repeat("0", 50) + "E-60")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := zeros.RatWithBudget(nil, Budget{MaxWork: 1_975_805_617}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("stripped W−1: %v", err)
	}
	if got, err := zeros.RatWithBudget(nil, Budget{MaxWork: 1_975_805_618}); err != nil || got.Denom().Cmp(big.NewInt(10_000_000_000)) != 0 {
		t.Fatalf("stripped W: (%v, %v)", got, err)
	}
}

// TestFromRatExactFirstPhaseRefusals pins the two-phase precharge: when a
// non-terminating value leaves the exact-first attempt, the division phase
// is refused on the combined charge before it allocates (no more
// allocations than the bare attempt alone), and an Exact context refuses
// without dividing even at the largest precision.
func TestFromRatExactFirstPhaseRefusals(t *testing.T) {
	third := big.NewRat(1, 3)
	ctx, err := NewContext(10, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	s, _ := readRat(third)
	aLow, _ := ratAdjustedLow(s.bn, s.bd)
	limit := s.exactPlan().charge + s.plan(aLow-10+1).charge - 1
	call := func() error {
		_, _, err := FromRatWithContext(third, ctx.WithBudget(Budget{MaxWork: limit}))
		return err
	}
	if err := call(); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("combined charge − 1: %v", err)
	}
	bare := testing.AllocsPerRun(20, func() { _, _ = FromRat(third) })
	if phase := testing.AllocsPerRun(20, func() { _ = call() }); phase > bare {
		t.Fatalf("division-phase refusal allocated %v times, the bare attempt %v", phase, bare)
	}
	// The Exact short-circuit follows the division's precharge: one
	// unit below the combined charge is a storage refusal, and at the
	// charge the value's non-termination is refused as Inexact.
	exactTen, _ := NewContext(10, Exact, nil, 0)
	if _, _, err := FromRatWithContext(third, exactTen.WithBudget(Budget{MaxWork: limit})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("Exact below the combined charge: %v", err)
	}
	var trapped *Error
	if _, _, err := FromRatWithContext(third, exactTen.WithBudget(Budget{MaxWork: limit + 1})); !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Condition != Inexact {
		t.Fatalf("Exact at the combined charge: %v", err)
	}
	exact, err := NewContext(math.MaxUint32, Exact, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	var before, after runtime.MemStats
	runtime.ReadMemStats(&before)
	_, _, err = FromRatWithContext(third, exact)
	runtime.ReadMemStats(&after)
	// Admission precedes the Exact refusal: a target whose heap is at most
	// 4 GiB (32-bit targets and js/wasm) cannot admit the p = 2^32−1
	// division plan and refuses it first.
	maxObject, _, _ := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	var ce *Error
	refused := errors.As(err, &ce) && ce.Condition == Inexact || maxObject <= 1<<32 && errors.Is(err, ErrInsufficientStorage)
	if !refused || after.TotalAlloc-before.TotalAlloc > 64<<10 {
		t.Fatalf("Exact at p = 2^32−1: %v after %d bytes", err, after.TotalAlloc-before.TotalAlloc)
	}
}

// TestBigToLimbsPathsAgree pins both base conversions (the word loop and
// the text path above ratTextConversionWords) to strconv-free decimal
// text from big.Int.String, across the switch-over and with spare
// capacity for the finisher's carry.
func TestBigToLimbsPathsAgree(t *testing.T) {
	rng := rand.New(rand.NewPCG(46, 9))
	for _, words := range []int{1, 2, 31, 32, 33, 34, 64, 200, 1000} {
		for range 20 {
			raw := make([]byte, 8*words)
			for i := range raw {
				raw[i] = byte(rng.Uint32())
			}
			x := new(big.Int).SetBytes(raw)
			if rng.IntN(4) == 0 { // runs of zero limbs
				x.Mul(x, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(9*rng.IntN(5))), nil))
			}
			if x.Sign() == 0 {
				continue
			}
			text := x.String()
			for name, got := range map[string][]uint32{"dispatch": bigToLimbs(x), "words": bigToLimbsByWords(x, nil)} {
				if cap(got) <= len(got) || got[len(got)-1] == 0 {
					t.Fatalf("%s %d words: no spare capacity or untrimmed", name, words)
				}
				var b strings.Builder
				for i, g := range slices.Backward(got) {
					if i == len(got)-1 {
						fmt.Fprintf(&b, "%d", g)
					} else {
						fmt.Fprintf(&b, "%09d", g)
					}
				}
				if b.String() != text {
					t.Fatalf("%s %d words: %s, want %s", name, words, b.String(), text)
				}
			}
		}
	}
}

// TestFromRatScratchEnvelope checks the toolchain-pinned math/big scratch
// envelope (ratScratchBytes): from a cold pool, cumulative allocated bytes per
// call stay within the envelope plus the result, over a size sweep from one
// word to 2^20 bits that crosses math/big's recursive-division threshold (40
// words) on both paths.
func TestFromRatScratchEnvelope(t *testing.T) {
	if testing.Short() {
		t.Skip("allocation sweep")
	}
	for _, bitsN := range []int{64, 256, 1 << 10, 1 << 12, 1 << 14, 1 << 16, 1 << 17, 1 << 18, 1 << 20} {
		n := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), uint(bitsN)), big.NewInt(3))
		d := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), uint(bitsN/2+5)), big.NewInt(7))
		r := new(big.Rat).SetFrac(n, d)
		s, _ := readRat(r)
		for _, target := range []int64{-40, int64(bitsN / 8)} { // k ≥ 0 and k < 0 (10^(b/8) < 2^(b/2))
			p := s.plan(target)
			if p.tiny {
				continue
			}
			limbs := 1 + p.quotientBound/9
			scratch, _ := ratScratchBytes(p.operandWords)
			planned := scratch + limbs*4 + 64
			used := coldAllocatedWithin(func() {
				if _, _, err := FromRatToExponent(r, int32(target), TiesToEven); err != nil {
					t.Fatal(err)
				}
			}, planned)
			t.Logf("bits=%d t=%d words=%d allocated=%d envelope=%d", bitsN, target, p.operandWords, used, planned)
			if used > planned {
				t.Errorf("bits=%d t=%d: allocated %d bytes > planned %d", bitsN, target, used, planned)
			}
		}
	}
}

// TestRatEgressExactAndFresh checks that rational conversion is exact:
// Rat returns a fresh value in lowest terms equal to the Decimal, which
// FromRat maps back numerically.
func TestRatEgressExactAndFresh(t *testing.T) {
	rng := rand.New(rand.NewPCG(46, 7))
	for range 4000 {
		d := randomDivOperand(rng, 60)
		r, err := d.Rat(nil)
		if err != nil {
			t.Fatal(err)
		}
		if r.Cmp(divRat(t, d)) != 0 {
			t.Fatalf("%v: Rat %s", d, r.RatString())
		}
		g := new(big.Int).GCD(nil, nil, new(big.Int).Abs(r.Num()), r.Denom())
		if g.Cmp(big.NewInt(1)) != 0 && r.Num().Sign() != 0 {
			t.Fatalf("%v: %s not in lowest terms", d, r.RatString())
		}
		back, err := FromRat(r)
		if err != nil || !back.Equal(d) {
			t.Fatalf("%v: round trip %v (%v)", d, back, err)
		}
		again, _ := d.Rat(nil)
		r.Num().SetInt64(99)
		if again.Cmp(divRat(t, d)) != 0 {
			t.Fatal("Rat results share storage")
		}
	}
	if r, err := Zero().Rat(nil); err != nil || r.Sign() != 0 {
		t.Fatalf("zero: (%v, %v)", r, err)
	}
	if _, err := MustParse("1E-400").RatWithBudget(nil, Budget{MaxDigits: 400}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("denominator 10^400 under a 400-digit cap: %v", err)
	}
	if _, err := MustParse("1E-400").RatWithBudget(nil, Budget{MaxDigits: 401}); err != nil {
		t.Fatalf("denominator 10^400 under a 401-digit cap: %v", err)
	}
	if _, err := New(1, math.MaxInt32).RatWithBudget(nil, Budget{MaxDigits: 10}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("huge integral Rat under a small cap: %v", err)
	}
}

// BenchmarkFromRat is the rational seam's smoke row: context and exponent
// rounding of small non-terminating rationals, exact terminating ingress,
// and exact egress.
func BenchmarkFromRat(b *testing.B) {
	third, sevenths, fortieths := big.NewRat(1, 3), big.NewRat(22, 7), big.NewRat(3, 40)
	ctx := Decimal128Context()
	egress, _ := Parse("0.075")
	b.Run("ctx34-third", func(b *testing.B) {
		b.ReportAllocs()
		for b.Loop() {
			_, _, _ = FromRatWithContext(third, ctx)
		}
	})
	b.Run("toexp-sevenths", func(b *testing.B) {
		b.ReportAllocs()
		for b.Loop() {
			_, _, _ = FromRatToExponent(sevenths, -10, TiesToEven)
		}
	})
	b.Run("exact-fortieths", func(b *testing.B) {
		b.ReportAllocs()
		for b.Loop() {
			_, _ = FromRat(fortieths)
		}
	})
	b.Run("rat-egress", func(b *testing.B) {
		b.ReportAllocs()
		for b.Loop() {
			_, _ = egress.Rat(nil)
		}
	})
}

// coldAllocated returns the cumulative heap bytes f allocates, measured from
// a cold math/big pool with the collector off.
func coldAllocated(f func()) uint64 {
	var before, after runtime.MemStats
	runtime.GC()
	runtime.GC()
	defer debug.SetGCPercent(debug.SetGCPercent(-1))
	runtime.ReadMemStats(&before)
	f()
	runtime.ReadMemStats(&after)
	return after.TotalAlloc - before.TotalAlloc
}

// coldAllocatedWithin measures f like coldAllocated and reports the least
// reading, retrying up to three times only while a reading exceeds limit:
// TotalAlloc is process-wide, and another goroutine's allocation can only
// add to a reading.
func coldAllocatedWithin(f func(), limit uint64) uint64 {
	least := coldAllocated(f)
	for range 2 {
		if least <= limit {
			break
		}
		least = min(least, coldAllocated(f))
	}
	return least
}

// TestRationalLoopsAllocateLinearly checks that the factor-5 loops of FromRat
// and Rat reuse their quotient and remainder, and Rat takes ownership of its
// integers without SetInt, SetFrac or Set copies, so each call allocates
// within its planned envelope (ratScratchBytes for math/big's scratch plus the
// result) instead of quadratically.
func TestRationalLoopsAllocateLinearly(t *testing.T) {
	if testing.Short() {
		t.Skip("allocation sweep")
	}
	for _, k := range []int64{1000, 10000} {
		// FromRat(1/5^k): the exact path's factor-5 loop runs k times.
		r := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Exp(big.NewInt(5), big.NewInt(k), nil))
		s, _ := readRat(r)
		e := s.exactPlan()
		scratch, _ := ratScratchBytes(e.operandWords)
		planned := scratch + (1+e.quotientBound/9)*4 + 64
		used := coldAllocatedWithin(func() {
			if _, err := FromRat(r); err != nil {
				t.Fatal(err)
			}
		}, planned)
		if used > planned {
			t.Errorf("FromRat(1/5^%d): allocated %d bytes > planned %d", k, used, planned)
		}

		// Rat of 5^k·10^−k: the egress factor-5 loop runs k times.
		d := MustParse(new(big.Int).Exp(big.NewInt(5), big.NewInt(k), nil).String() + "E-" + fmt.Sprint(k))
		v := coefficientViewOf(d)
		digits, _ := arithmeticDigits(&v)
		wc := ratWords(digits*332193/100000 + 1)
		wj, _ := ratPowerWords(uint64(k))
		scratch, _ = ratScratchBytes(wc + wj)
		plannedRat := scratch + 8*(wc+wj) + 512
		used = coldAllocatedWithin(func() {
			if _, err := d.Rat(nil); err != nil {
				t.Fatal(err)
			}
		}, plannedRat)
		if used > plannedRat {
			t.Errorf("Rat(5^%d·10^−%d): allocated %d bytes > planned %d", k, k, used, plannedRat)
		}
	}
	// Rat of an integral value costs its BigInt conversion plus the Rat
	// header, not a second copy of the words.
	d := MustParse("7E+100000")
	bigInt := coldAllocated(func() { _, _ = d.BigInt(nil) })
	rat := coldAllocatedWithin(func() { _, _ = d.Rat(nil) }, bigInt+256)
	if rat > bigInt+256 {
		t.Errorf("Rat(7E+100000): allocated %d bytes, BigInt %d: the integral path copies the words", rat, bigInt)
	}
}

// TestRatPlanBoundsQuotient pins the FromRat division plan's quotient
// bounds against the actual quotient: for
// every target, the quotient n·10^k/d (k ≥ 0) or n/(d·10^j) (k = −j < 0) has
// at most the planned 64-bit words and quotientBound digits, which the
// conversion charge, the division charge and the physical admission rely
// on.
func TestRatPlanBoundsQuotient(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 7))
	for range 20000 {
		n, d := randomBits(r, 1+r.IntN(400)), randomBits(r, 1+r.IntN(400))
		if n.Sign() == 0 || d.Sign() == 0 {
			continue
		}
		x := new(big.Rat).SetFrac(n, d)
		s, _ := readRat(x)
		target := int64(r.IntN(300) - 150)
		p := s.plan(target)
		if !p.ok || p.tiny {
			continue
		}
		num, den := new(big.Int).Abs(x.Num()), new(big.Int).Set(x.Denom())
		if k := -target; k >= 0 {
			num.Mul(num, new(big.Int).Exp(big.NewInt(10), big.NewInt(k), nil))
		} else {
			den.Mul(den, new(big.Int).Exp(big.NewInt(10), big.NewInt(-k), nil))
		}
		q := new(big.Int).Quo(num, den)
		if digits := uint64(len(q.String())); q.Sign() != 0 && digits > p.quotientBound {
			t.Fatalf("%v at t=%d: quotient has %d digits > planned %d (bn=%d bd=%d)", x, target, digits, p.quotientBound, s.bn, s.bd)
		}
	}
}

// randomBits returns a random integer of exactly bitLen bits.
func randomBits(r *rand.Rand, bitLen int) *big.Int {
	v := big.NewInt(1)
	for range bitLen - 1 {
		v.Lsh(v, 1)
		v.SetBit(v, 0, uint(r.IntN(2)))
	}
	return v
}

// TestRatChargesBoundCountedWork checks the charges of the FromRat
// family's own loops, counted inside the library with the nil
// counter production passes (as divCount does for the division kernel):
// over terminating rationals with every trailing-zero count, the factor-5
// loop runs at most the charged bMax times, and the word-by-word quotient
// conversion takes at most the charged conversion steps Uc·⌈Uc/9⌉.
// math/big's own internal work is covered by the schoolbook bound and the
// measured per-unit ceiling, not by counts.
func TestRatChargesBoundCountedWork(t *testing.T) {
	r := rand.New(rand.NewPCG(51, 13))
	five := big.NewInt(5)
	checked := 0
	for range 5000 {
		a, b := r.IntN(300), r.IntN(200)
		d := new(big.Int).Lsh(new(big.Int).Exp(five, big.NewInt(int64(b)), nil), uint(a))
		x := new(big.Rat).SetFrac(randomBits(r, 1+r.IntN(300)), d)
		s, _ := readRat(x)
		if s.zero {
			continue
		}
		e := s.exactPlan()
		var count ratCount
		q, _, terminating := s.exactDigitsCounted(e, &count)
		if !terminating {
			t.Fatalf("%v: a power-of-ten denominator must terminate", x)
		}
		// d = 2^a·5^b in lowest terms keeps its fives unless the numerator
		// shares them; the loop runs once per remaining five.
		fives := uint64(0)
		for rest := new(big.Int).Set(x.Denom()); new(big.Int).Mod(rest, five).Sign() == 0; rest.Quo(rest, five) {
			fives++
		}
		// Each successful division removes at least one five; up to the
		// single-five prefix the loop is the single-five reference loop.
		if count.fives > fives || fives <= ratFivePrefix && count.fives != fives || count.fives > e.bMax {
			t.Fatalf("%v: the factor-5 loop ran %d times (fives %d, charged bMax %d)", x, count.fives, fives, e.bMax)
		}
		_, uc, _ := ratConversionCharge(ratWords(s.bn) + mustRatPowerWords(t, max(e.a, e.bMax)))
		if steps := uc * (1 + (uc-1)/9); count.limbSteps > steps {
			t.Fatalf("%v: conversion took %d limb steps > charged %d", x, count.limbSteps, steps)
		}
		if len(q) > 0 {
			checked++
		}
	}
	if checked < 4000 {
		t.Fatalf("only %d conversions counted", checked)
	}
}

// TestFromRatFactorFiveValuationBound checks that the factor-5 valuation of
// the exact rational path takes O(log b) divisions, not b, for denominators
// 2^a·5^b, and the results stay exact. Oracles: math/big rational equality,
// the hand-derived exponent −max(a, b) of a numerator coprime to 10, and the
// hand-derived Rat of 5^b·10^−b, which is 1/2^b.
func TestFromRatFactorFiveValuationBound(t *testing.T) {
	five := big.NewInt(5)
	for _, tc := range []struct{ a, b int64 }{{0, 1000}, {7, 4093}, {0, 20000}, {20001, 20000}, {3, 65537}} {
		d := new(big.Int).Lsh(new(big.Int).Exp(five, big.NewInt(tc.b), nil), uint(tc.a))
		x := new(big.Rat).SetFrac(big.NewInt(-3), d) // 3 is coprime to 10
		s, _ := readRat(x)
		e := s.exactPlan()
		var count ratCount
		_, _, terminating := s.exactDigitsCounted(e, &count)
		if !terminating {
			t.Fatalf("1/(2^%d·5^%d) must terminate", tc.a, tc.b)
		}
		if bound := 32 + 2*uint64(bits.Len64(uint64(tc.b))); count.fives > bound {
			t.Errorf("2^%d·5^%d: %d factor-5 divisions > %d", tc.a, tc.b, count.fives, bound)
		}
		got, err := FromRat(x)
		if err != nil {
			t.Fatal(err)
		}
		if want := -int32(max(tc.a, tc.b)); got.Exponent() != want {
			t.Errorf("2^%d·5^%d: exponent %d, want %d", tc.a, tc.b, got.Exponent(), want)
		}
		back, err := got.Rat(nil)
		if err != nil || back.Cmp(x) != 0 {
			t.Errorf("2^%d·5^%d: FromRat is not exact (%v)", tc.a, tc.b, err)
		}
	}
	for _, b := range []int64{40, 5000, 20000} {
		p := new(big.Int).Exp(five, big.NewInt(b), nil)
		d := MustParse(p.String() + "E-" + fmt.Sprint(b))
		r, err := d.Rat(nil)
		want := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), uint(b)))
		if err != nil || r.Cmp(want) != 0 || r.Num().Cmp(big.NewInt(1)) != 0 {
			t.Errorf("Rat(5^%d·10^−%d) is not 1/2^%d (%v)", b, b, b, err)
		}
	}
}

// singleFiveReference divides by five once per step: the reference for
// removeFives.
func singleFiveReference(x *big.Int, limit uint64) (*big.Int, uint64) {
	x = new(big.Int).Set(x)
	five, q, rem := big.NewInt(5), new(big.Int), new(big.Int)
	var v uint64
	for v < limit {
		q.QuoRem(x, five, rem)
		if rem.Sign() != 0 {
			break
		}
		x, q = q, x
		v++
	}
	return x, v
}

// TestRemoveFivesMatchesSingleFiveLoop checks that the block-ladder
// valuation returns exactly the quotient and count of the
// single-five reference loop over random and boundary operands (valuations
// around the prefix and powers of two, cofactors of one or many words,
// limits 0, 1, around the valuation and unbounded), and its successful
// divisions never exceed the reference's. The guard requires the ladder to
// serve a substantial share of the cases.
func TestRemoveFivesMatchesSingleFiveLoop(t *testing.T) {
	r := rand.New(rand.NewPCG(71, 88))
	five := big.NewInt(5)
	valuations := []uint64{0, 1, 2, 31, 32, 33, 34, 63, 64, 65, 66, 95, 96, 97, 127, 128, 129, 255, 256, 257, 1000, 1023, 1024, 1025}
	laddered, cases := 0, 0
	for i := range 3000 {
		v := valuations[i%len(valuations)]
		if i%3 == 0 {
			v = uint64(r.IntN(700))
		}
		var cofactor *big.Int
		switch i % 4 {
		case 0:
			cofactor = big.NewInt(1)
		case 1:
			cofactor = new(big.Int).SetUint64(math.MaxUint64)
		default:
			cofactor = randomBits(r, 1+r.IntN(2000))
		}
		for new(big.Int).Mod(cofactor, five).Sign() == 0 {
			cofactor.Add(cofactor, big.NewInt(1))
		}
		x := new(big.Int).Mul(cofactor, new(big.Int).Exp(five, new(big.Int).SetUint64(v), nil))
		limits := []uint64{0, 1, v, v + 1, math.MaxUint64, uint64(r.IntN(int(2*v + 2)))}
		if v > 0 {
			limits = append(limits, v-1)
		}
		if v > ratFivePrefix {
			limits = append(limits, ratFivePrefix, 2*ratFivePrefix-1, 2*ratFivePrefix)
		}
		for _, limit := range limits {
			want, wantV := singleFiveReference(x, limit)
			var count ratCount
			got, spare, gotV := removeFives(new(big.Int).Set(x), new(big.Int), new(big.Int), five, limit, &count)
			if gotV != wantV || got.Cmp(want) != 0 {
				t.Fatalf("x=5^%d·c limit %d: (%d, %v), want (%d, %v)", v, limit, gotV, got, wantV, want)
			}
			if got == spare || five.Cmp(big.NewInt(5)) != 0 {
				t.Fatal("result aliases the spare buffer or five was modified")
			}
			if count.fives > wantV || wantV <= ratFivePrefix && count.fives != wantV {
				t.Fatalf("x=5^%d·c limit %d: %d divisions for %d fives", v, limit, count.fives, wantV)
			}
			if wantV >= 2*ratFivePrefix {
				laddered++
			}
			cases++
		}
	}
	if laddered < cases/5 {
		t.Fatalf("the ladder served %d of %d cases", laddered, cases)
	}
}

func mustRatPowerWords(t *testing.T, k uint64) uint64 {
	t.Helper()
	w, ok := ratPowerWords(k)
	if !ok {
		t.Fatal("power words overflow")
	}
	return w
}

// TestFromRatZeroAllocation covers the admission rule for zero results:
// an implicit denominator must not allocate before admission or when the
// constructor's zero result has a zero-heap estimate.
func TestFromRatZeroAllocation(t *testing.T) {
	ctx := Decimal64Context()
	for _, src := range []*big.Rat{new(big.Rat), big.NewRat(0, 1)} {
		for _, tc := range []struct {
			name     string
			run      func(Budget) (Decimal, Conditions, error)
			exponent int32
		}{
			{"bare", func(b Budget) (Decimal, Conditions, error) {
				d, _, err := FromRatWithContext(src, Context{}.WithBudget(b))
				return d, 0, err
			}, 0},
			{"context", func(b Budget) (Decimal, Conditions, error) { return FromRatWithContext(src, ctx.WithBudget(b)) }, 0},
			{"unlimited context", func(b Budget) (Decimal, Conditions, error) {
				return FromRatWithContext(src, Context{}.WithBudget(b))
			}, 0},
			{"target", func(b Budget) (Decimal, Conditions, error) {
				return FromRatToExponentWithBudget(src, -7, Exact, b)
			}, -7},
		} {
			for _, work := range []uint64{0, 1, 3, 4} {
				b := Budget{MaxWork: work}
				d, c, err := tc.run(b)
				wantAllocs := float64(0)
				if work == 1 || work == 3 {
					wantAllocs = 1
					if !errors.Is(err, ErrInsufficientStorage) || c != 0 {
						t.Fatalf("%s work%d: %v %v", tc.name, work, c, err)
					}
				} else if err != nil || c != 0 || !d.IsZero() || d.Exponent() != tc.exponent {
					t.Fatalf("%s: %s %v %v", tc.name, d, c, err)
				}
				if n := testing.AllocsPerRun(20, func() { _, _, _ = tc.run(b) }); n != wantAllocs {
					t.Errorf("%s work%d: allocations %g, want %g", tc.name, work, n, wantAllocs)
				}
				if work == 4 {
					if heap := coldAllocatedWithin(func() { _, _, _ = tc.run(b) }, 0); heap != 0 {
						t.Errorf("%s zero heap %d, want0", tc.name, heap)
					}
				}
			}
		}
	}
	// Zero must not bypass source validation, including a negative unit
	// denominator for which math/big.IsInt still reports true.
	for _, den := range []int64{-1, -3} {
		r := big.NewRat(0, 1)
		r.Denom().SetInt64(den)
		if _, _, err := FromRatWithContext(r, Context{}.WithBudget(Budget{MaxWork: 1})); !errors.Is(err, ErrConversionSyntax) {
			t.Fatalf("negative denominator %d: %v", den, err)
		}
	}
}

// TestFromRatImplicitDenominatorPrecharge covers the implicit-denominator
// source shape with a nonzero numerator written through Num: denominator1 remains
// implicit, and the tiny work cap must refuse before it is materialized.
func TestFromRatImplicitDenominatorPrecharge(t *testing.T) {
	r := new(big.Rat)
	r.Num().SetInt64(7)
	for _, run := range []func() error{
		func() error { _, _, err := FromRatWithContext(r, Context{}.WithBudget(Budget{MaxWork: 1})); return err },
		func() error {
			_, _, err := FromRatWithContext(r, Decimal64Context().WithBudget(Budget{MaxWork: 1}))
			return err
		},
		func() error {
			_, _, err := FromRatToExponentWithBudget(r, -3, Exact, Budget{MaxWork: 1})
			return err
		},
	} {
		if err := run(); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatal(err)
		}
		if n := testing.AllocsPerRun(20, func() { _ = run() }); n != 1 {
			t.Errorf("implicit denominator precharge allocations %g, want1", n)
		}
	}
}

// TestFromRatImplicitDenominatorOracle covers the unit-denominator
// descriptor against independent rational rounding in every mode, including
// target and precision/guard boundaries for both signs.
func TestFromRatImplicitDenominatorOracle(t *testing.T) {
	for _, text := range []string{"-123456789012345678901234567890", "-125", "-7", "1", "7", "125", "123456789012345678901234567890"} {
		n, ok := new(big.Int).SetString(text, 10)
		if !ok {
			t.Fatal(text)
		}
		r := new(big.Rat)
		r.Num().Set(n)
		oracle := new(big.Rat).SetInt(n)
		for _, mode := range allDivModes {
			for _, target := range []int64{-12, -1, 0, 1, 3} {
				want := oracleToExponent(oracle, 0, target, mode)
				got, c, err := FromRatToExponent(r, int32(target), mode)
				checkDivOutcome(t, text, got, c, err, want, n.Sign() < 0)
			}
			for _, p := range []int64{1, 3, 40} {
				ctx, _ := NewContext(uint32(p), mode, nil, 0)
				got, c, err := FromRatWithContext(r, ctx)
				checkDivOutcome(t, text, got, c, err, oracleContext(oracle, 0, p, mode), n.Sign() < 0)
				ctx, _ = NewContext(uint32(p), mode, &ExponentGuards{Emin: -3, Emax: 3}, 0)
				got, c, err = FromRatWithContext(r, ctx)
				checkDivOutcome(t, text, got, c, err, oracleGuarded(oracle, 0, p, -3, 3, mode), n.Sign() < 0)
			}
		}
		if r.Num().Cmp(n) != 0 || !r.IsInt() {
			t.Fatal("source mutated")
		}
	}
	bad := new(big.Rat)
	bad.Num().SetInt64(1)
	bad.Num().Bits()[0] = 0
	if _, err := FromRat(bad); !errors.Is(err, ErrConversionSyntax) {
		t.Fatalf("malformed implicit numerator: %v", err)
	}
}

// removeFives is the valuation the two production sites inline: it
// divides x > 0 by 5 as often as 5 divides it, at most limit times,
// removing the first ratFivePrefix fives one at a time and the rest with
// fiveLadder, and returns the quotient, the spare buffer and v =
// min(ν5(x), limit).
func removeFives(x, quotient, rem, five *big.Int, limit uint64, count *ratCount) (*big.Int, *big.Int, uint64) {
	var v uint64
	for v < limit {
		if v == ratFivePrefix && limit-v >= ratFivePrefix {
			return fiveLadder(x, quotient, rem, five, limit, v, count)
		}
		quotient.QuoRem(x, five, rem)
		if rem.Sign() != 0 {
			break
		}
		x, quotient = quotient, x
		v++
		if count != nil {
			count.fives++
		}
	}
	return x, quotient, v
}

// TestRatInlineMatchesGeneral pins the one-word paths of FromRat,
// FromRatToExponent and Rat to the general math/big paths: terminating and
// repeating fractions, every rounding mode, zero, and operands just beyond
// one word, with the conditions and every refusal.
func TestRatInlineMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x726174, 3))
	general := Budget{MaxWork: math.MaxUint64}
	word := func() uint64 {
		switch rng.IntN(5) {
		case 0:
			return rng.Uint64()
		case 1:
			return rng.Uint64N(1_000_000)
		case 2: // only twos and fives: every quotient by it terminates
			return uint64(1) << rng.IntN(20) * pow10Words[rng.IntN(8)] * float64Fives[rng.IntN(8)]
		case 3:
			return pow10Words[rng.IntN(20)]
		}
		return rng.Uint64N(1 << 20)
	}
	var exact, repeating, toExponent, egress int
	for range 100000 {
		num, den := new(big.Int).SetUint64(word()), new(big.Int).SetUint64(word())
		if den.Sign() == 0 {
			den.SetInt64(1)
		}
		if rng.IntN(50) == 0 {
			num.Lsh(num, 64) // beyond one word: the inline path must defer
		}
		if rng.IntN(2) == 0 {
			num.Neg(num)
		}
		r := new(big.Rat).SetFrac(num, den)
		text := r.String()

		got, err := FromRat(r)
		want, _, werr := fromRatExact(r, limits{}, "FromRat")
		requireSameOutcome(t, "FromRat", text, got, 0, err, want, 0, werr)
		if err == nil {
			exact++
		} else {
			repeating++
		}

		target := int32(rng.IntN(25) - 20)
		mode := RoundingMode(rng.IntN(int(Exact) + 2)) // one invalid mode
		gotE, gc, err := FromRatToExponent(r, target, mode)
		wantE, wc, werr := fromRatToExponent(r, target, mode, limits{}, "FromRatToExponent")
		requireSameOutcome(t, "FromRatToExponent", text, gotE, gc, err, wantE, wc, werr)
		if err == nil {
			toExponent++
		}

		// Rat: a one-word coefficient at a small negative exponent.
		d := inlineDecimal(uint128{lo: word()}, int32(-rng.IntN(22)), rng.IntN(2) == 0)
		back, err := d.Rat(nil)
		reference, werr := d.ratWithBudget(nil, general, "Rat")
		if err != nil || werr != nil || back.Cmp(reference) != 0 || back.Denom().Cmp(reference.Denom()) != 0 || back.Denom().Sign() <= 0 {
			t.Fatalf("%v.Rat() = %v, %v; general %v, %v", d, back, err, reference, werr)
		}
		if roundTrip, err := FromRat(back); err != nil || roundTrip.Compare(d) != 0 {
			t.Fatalf("%v.Rat() = %v does not convert back: %v, %v", d, back, roundTrip, err)
		}
		reused := new(big.Rat).SetFrac64(7, 3)
		if again, err := d.Rat(reused); err != nil || again != reused || again.Cmp(reference) != 0 {
			t.Fatalf("%v.Rat(reused) = %v, %v", d, again, err)
		}
		egress++
	}
	if exact < 10000 || repeating < 10000 || toExponent < 50000 || egress < 100000 {
		t.Fatalf("vacuous path coverage: %d exact, %d repeating, %d to exponent, %d egress", exact, repeating, toExponent, egress)
	}
	if _, err := FromRat(nil); !errors.Is(err, ErrConversionSyntax) {
		t.Fatalf("FromRat(nil): %v", err)
	}
}

// TestFromRatDigitCapRefusesBeforeDividing checks that a digit cap the
// quotient certainly exceeds refuses before the division builds the
// quotient, and that the bound never refuses a result that fits: a cap of
// exactly the result's digits admits the call and one digit fewer refuses.
func TestFromRatDigitCapRefusesBeforeDividing(t *testing.T) {
	budget := Budget{MaxDigits: 50}
	allocated := func(call func() error) (uint64, error) {
		var before, after runtime.MemStats
		runtime.ReadMemStats(&before)
		err := call()
		runtime.ReadMemStats(&after)
		return after.TotalAlloc - before.TotalAlloc, err
	}
	huge := new(big.Rat).SetInt(new(big.Int).Lsh(big.NewInt(1), 4_000_000)) // 1,204,120 digits
	for name, call := range map[string]func() error{
		"FromRatToExponentWithBudget(1/3, -2000000)": func() error {
			_, _, err := FromRatToExponentWithBudget(big.NewRat(1, 3), -2_000_000, TiesToEven, budget)
			return err
		},
		"FromRatToExponentWithBudget(2^4000000, 0)": func() error {
			_, _, err := FromRatToExponentWithBudget(huge, 0, TiesToEven, budget)
			return err
		},
		"FromRatWithContext(2^4000000, unlimited precision)": func() error {
			_, _, err := FromRatWithContext(huge, Context{}.WithBudget(budget))
			return err
		},
	} {
		if bytes, err := allocated(call); !errors.Is(err, ErrInsufficientStorage) || bytes > 1<<16 {
			t.Errorf("%s: %v after allocating %d bytes; want the storage refusal before the division", name, err, bytes)
		}
	}

	// The Exact mode keeps its own refusal: an inexact quotient is Inexact
	// whatever the digit cap, and only an exact one can exceed it.
	_, _, err := FromRatToExponentWithBudget(big.NewRat(1, 3), -100, Exact, budget)
	var detail *Error
	if !errors.As(err, &detail) || detail.Code != 0 || detail.Condition != Inexact {
		t.Errorf("1/3 at -100 in Exact mode under a digit cap: %v; want the Inexact refusal", err)
	}
	if _, _, err := FromRatToExponentWithBudget(big.NewRat(1, 4), -100, Exact, budget); !errors.Is(err, ErrInsufficientStorage) {
		t.Errorf("1/4 at -100 in Exact mode under a digit cap: %v; want the storage refusal", err)
	}

	rng := rand.New(rand.NewPCG(0x636170, 7))
	var admitted, refused, early int
	for range 20000 {
		num := new(big.Int).SetUint64(1 + rng.Uint64N(1<<62))
		num.Lsh(num, uint(rng.IntN(300)))
		den := new(big.Int).SetUint64(1 + rng.Uint64N(1<<62))
		den.Lsh(den, uint(rng.IntN(300)))
		if rng.IntN(4) == 0 {
			den.SetInt64(1)
		}
		r := new(big.Rat).SetFrac(num, den)
		target := int32(rng.IntN(241) - 120)
		mode := RoundingMode(rng.IntN(int(Exact)))
		want, wc, err := FromRatToExponent(r, target, mode)
		if err != nil {
			t.Fatal(err)
		}
		digits := want.CoefficientDigits()
		got, gc, err := FromRatToExponentWithBudget(r, target, mode, Budget{MaxDigits: digits})
		if err != nil || !sameRepresentation(got, want) || gc != wc {
			t.Fatalf("%v at %d with a cap of its own %d digits: %v %v, %v; want %v %v", r, target, digits, got, gc, err, want, wc)
		}
		admitted++
		if s, ok := readRat(r); ok && !s.zero {
			if floor := s.quotientDigitsFloor(-int64(target)); floor > digits {
				t.Fatalf("%v at %d: the digit floor %d exceeds the result's %d digits", r, target, floor, digits)
			} else if floor > 0 && floor+2 >= digits {
				early++ // the bound is within two digits of the result
			}
		}
		if digits > 1 {
			if _, _, err := FromRatToExponentWithBudget(r, target, mode, Budget{MaxDigits: digits - 1}); !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("%v at %d with a cap one below its %d digits: %v", r, target, digits, err)
			}
			refused++
		}
	}
	if admitted < 20000 || refused < 8000 || early < 8000 {
		t.Fatalf("vacuous path coverage: %d admitted, %d refused, %d with a tight floor", admitted, refused, early)
	}
}
