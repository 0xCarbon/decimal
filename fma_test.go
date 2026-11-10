// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"strings"
	"testing"
	"time"
)

// fmaModes is every rounding mode, Exact included.
var fmaModes = []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact}

// fmaGuards is the oracle's view of optional exponent guards.
type fmaGuards struct {
	on         bool
	emin, emax int64
}

// fmaWant is an oracle outcome: a signed coefficient at an exponent with
// its Conditions, the Exact refusal, or ErrExponentRange.
type fmaWant struct {
	coefficient *big.Int // magnitude
	exponent    int64
	negative    bool
	conditions  Conditions
	refused     bool
	rangeError  bool
}

// fmaExact is x·y + z as a signed integer at the preferred exponent
// min(ex+ey, ez), computed with math/big from the operands' coefficient
// digits and exponents only.
func fmaExact(x, y, z Decimal) (*big.Int, int64) {
	product := new(big.Int).Mul(contextTestCoefficient(x), contextTestCoefficient(y))
	ep, ez := int64(x.exponent())+int64(y.exponent()), int64(z.exponent())
	ideal := min(ep, ez)
	sum := new(big.Int).Mul(product, pow10Big(ep-ideal))
	return sum.Add(sum, new(big.Int).Mul(contextTestCoefficient(z), pow10Big(ez-ideal))), ideal
}

func fmaDigits(v *big.Int) int64 { return int64(len(v.String())) }

// fmaOracle rounds the exact signed integer sum at exponent ideal once to
// p digits in mode, independently of the library: the cut is the excess
// over p digits, raised to Etiny under guards; ties compare twice the
// remainder with 10^cut; a carry to p+1 digits shifts once. Overflow above
// Emax substitutes Bmax (Exact refuses it), a result whose exact adjusted
// exponent lies below Emin is Subnormal (and Underflow when inexact), an
// exact zero keeps the ideal exponent, and an unpublishable exponent is
// ErrExponentRange. The direction bit is sign(result − exact).
func fmaOracle(exact *big.Int, ideal, p int64, mode RoundingMode, g fmaGuards) fmaWant {
	negative := exact.Sign() < 0
	magnitude := new(big.Int).Abs(exact)
	fits := func(e int64) bool { return e >= math.MinInt32 && e <= math.MaxInt32 }
	if magnitude.Sign() == 0 {
		return fmaWant{coefficient: magnitude, exponent: ideal, rangeError: !fits(ideal)}
	}
	direction := func(q *big.Int, e int64) Conditions {
		result := new(big.Rat).SetInt(q)
		result.Mul(result, pow10Rat(e-ideal))
		if negative {
			result.Neg(result)
		}
		return oracleDirection(result, new(big.Rat).SetInt(exact))
	}
	overflow := func() fmaWant {
		if mode == Exact {
			return fmaWant{refused: true}
		}
		nines := new(big.Int).Sub(pow10Big(p), big.NewInt(1))
		e := g.emax - p + 1
		return fmaWant{coefficient: nines, exponent: e, negative: negative, conditions: Overflow | Inexact | Rounded | direction(nines, e)}
	}
	length := fmaDigits(magnitude)
	adjusted := ideal + length - 1
	if g.on && adjusted > g.emax {
		return overflow()
	}
	cut := max(0, length-p)
	tiny := g.on && adjusted < g.emin
	if tiny {
		cut = max(cut, g.emin-(p-1)-ideal)
	}
	divisor := pow10Big(cut)
	q, r := new(big.Int).QuoRem(magnitude, divisor, new(big.Int))
	inexact := r.Sign() != 0
	if mode == Exact && inexact {
		return fmaWant{refused: true}
	}
	half := new(big.Int).Lsh(r, 1).Cmp(divisor)
	var up bool
	switch mode {
	case TiesToEven:
		up = half > 0 || half == 0 && q.Bit(0) == 1
	case TiesAwayFromZero:
		up = half >= 0
	case TiesTowardZero:
		up = half > 0
	case AwayFromZero:
		up = inexact
	case TowardPositiveInfinity:
		up = inexact && !negative
	case TowardNegativeInfinity:
		up = inexact && negative
	}
	exponent := ideal + cut
	if up {
		q.Add(q, big.NewInt(1))
		if fmaDigits(q) > p {
			q.Quo(q, big.NewInt(10))
			exponent++
		}
	}
	var conditions Conditions
	if cut > 0 {
		conditions |= Rounded
	}
	if inexact {
		conditions |= Inexact | direction(q, exponent)
	}
	if tiny {
		conditions |= Subnormal
		if inexact {
			conditions |= Underflow
		}
	}
	if q.Sign() == 0 {
		return fmaWant{coefficient: q, exponent: exponent, conditions: conditions, rangeError: !fits(exponent)}
	}
	if g.on && exponent+fmaDigits(q)-1 > g.emax {
		return overflow()
	}
	return fmaWant{coefficient: q, exponent: exponent, negative: negative, conditions: conditions, rangeError: !fits(exponent)}
}

// fmaCheck compares one FMAWithContext outcome with the oracle.
func fmaCheck(t *testing.T, label string, got Decimal, conditions Conditions, err error, want fmaWant) {
	t.Helper()
	switch {
	case want.refused:
		var ce *Error
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || !sameRepresentation(got, Decimal{}) || conditions != 0 {
			t.Fatalf("%s: (%v, %v, %v), want the Exact refusal", label, got, conditions, err)
		}
		return
	case want.rangeError:
		if !errors.Is(err, ErrExponentRange) || !sameRepresentation(got, Decimal{}) || conditions != 0 {
			t.Fatalf("%s: (%v, %v, %v), want ErrExponentRange", label, got, conditions, err)
		}
		return
	}
	if err != nil {
		t.Fatalf("%s: %v", label, err)
	}
	if got.negative() != want.negative || got.coefficientDigits() != want.coefficient.String() || int64(got.exponent()) != want.exponent || conditions != want.conditions {
		t.Fatalf("%s: %s%s·10^%d %v, want %v%s·10^%d %v", label, map[bool]string{true: "-"}[got.negative()], got.coefficientDigits(), got.exponent(), conditions,
			map[bool]string{true: "-"}[want.negative], want.coefficient, want.exponent, want.conditions)
	}
}

// fmaOperand draws a Decimal of up to maxDigits digits at an exponent in
// [lo, hi]: random digits, all nines (carries), trailing zeros, a zero or
// a negative zero, either sign.
func fmaOperand(r *rand.Rand, maxDigits int, lo, hi int32) Decimal {
	e := lo + int32(r.IntN(int(hi-lo)+1))
	switch r.IntN(14) {
	case 0:
		return zeroDecimal(e)
	case 1:
		return inlineDecimal(uint128{}, e, true)
	}
	c := randomDigits(r, 1+r.IntN(maxDigits))
	switch r.IntN(6) {
	case 0:
		c = new(big.Int).Sub(pow10Big(int64(1+r.IntN(maxDigits))), big.NewInt(1))
	case 1:
		c.Mul(c, pow10Big(int64(r.IntN(8))))
	}
	if r.IntN(2) == 0 {
		c.Neg(c)
	}
	return sqrtDecimal(c, int64(e))
}

// fmaTriple draws x, y, z; a third of the time z nearly cancels x·y (the
// negated product plus a small perturbation at a random position), which
// exercises borrows, exact zeros and ties on the rounding position.
func fmaTriple(r *rand.Rand, maxDigits int, lo, hi int32) (Decimal, Decimal, Decimal) {
	x, y := fmaOperand(r, maxDigits, lo, hi), fmaOperand(r, maxDigits, lo, hi)
	if r.IntN(3) != 0 || x.isZero() || y.isZero() {
		return x, y, fmaOperand(r, maxDigits, lo, hi)
	}
	product := new(big.Int).Mul(contextTestCoefficient(x), contextTestCoefficient(y))
	product.Neg(product)
	shift := int64(r.IntN(4))
	product.Mul(product, pow10Big(shift))
	switch r.IntN(4) {
	case 0:
	case 1:
		product.Add(product, pow10Big(int64(r.IntN(6))))
	case 2:
		product.Sub(product, pow10Big(int64(r.IntN(6))))
	default:
		product.Add(product, big.NewInt(int64(r.IntN(11)-5)*5))
	}
	return x, y, sqrtDecimal(product, int64(x.exponent())+int64(y.exponent())-shift)
}

// TestFMAAgainstBigOracle checks that FMAWithContext rounds once: over random operands, near-cancelling addends, zeros and
// carries, in all eight modes at random precisions with and without
// guards, FMAWithContext equals the math/big oracle of the exact x·y + z
// rounded once, in value, exponent and Conditions; the direction bit agrees
// with sign(result − exact); the budgeted twin under an unlimited budget
// and the product-term path under it (the logical full-span path) agree;
// and the directed pair encloses the exact sum on its p-digit grid.
func TestFMAAgainstBigOracle(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 60))
	cases := 4000
	if testing.Short() {
		cases = 1000
	}
	unlimited := Budget{MaxWork: math.MaxUint64}
	seen := map[Conditions]int{}
	for i := range cases {
		x, y, z := fmaTriple(r, 1+r.IntN(45), -30, 30)
		exact, ideal := fmaExact(x, y, z)
		p := int64(1 + r.IntN(40))
		var g fmaGuards
		var guards *ExponentGuards
		if r.IntN(3) == 0 {
			emin := int32(-r.IntN(50))
			g = fmaGuards{on: true, emin: int64(emin), emax: int64(emin) + int64(r.IntN(90))}
			guards = &ExponentGuards{Emin: emin, Emax: int32(g.emax)}
		}
		exactRat := new(big.Rat).Mul(new(big.Rat).SetInt(exact), pow10Rat(ideal))
		var directed [2]Decimal
		var directedConditions [2]Conditions
		for _, mode := range fmaModes {
			ctx := contextTestContext(t, uint32(p), mode, guards, 0)
			label := fmt.Sprintf("case %d: FMA(%v, %v, %v) p=%d mode=%d guards=%+v", i, x, y, z, p, mode, g)
			want := fmaOracle(exact, ideal, p, mode, g)
			got, conditions, err := x.FMAWithContext(y, z, ctx)
			fmaCheck(t, label, got, conditions, err, want)
			if err == nil {
				checkRoundingDirection(t, label, exactRat, mode, got, conditions, err)
				seen[conditions&(Inexact|Subnormal|Overflow|Increased|Decreased)]++
			}
			budgeted, budgetedConditions, budgetedErr := x.FMAWithContext(y, z, ctx.WithBudget(unlimited))
			if !sameRepresentation(got, budgeted) || conditions != budgetedConditions || (err == nil) != (budgetedErr == nil) {
				t.Fatalf("%s: unbudgeted %v %v %v, budgeted %v %v %v", label, got, conditions, err, budgeted, budgetedConditions, budgetedErr)
			}
			general, generalConditions, generalErr := x.fmaGeneral(y, z, ctx.WithBudget(unlimited))
			if !sameRepresentation(got, general) || conditions != generalConditions || (err == nil) != (generalErr == nil) {
				t.Fatalf("%s: unbudgeted %v %v %v, product-term path %v %v %v", label, got, conditions, err, general, generalConditions, generalErr)
			}
			switch mode {
			case TowardNegativeInfinity:
				directed[0], directedConditions[0] = got, conditions
			case TowardPositiveInfinity:
				directed[1], directedConditions[1] = got, conditions
			}
		}
		if exact.Sign() != 0 && !want0Range(exact, ideal, p, g) {
			quantum := directionPrecisionQuantum(exactRat, p, g.on, g.emin)
			checkDirectedEnclosure(t, fmt.Sprintf("case %d", i), exactRat, quantum, directed[0], directedConditions[0], directed[1], directedConditions[1])
		}
	}
	for _, class := range []Conditions{0, Inexact | Decreased, Inexact | Increased, Subnormal, Overflow | Decreased} {
		found := false
		for c := range seen {
			if c&class == class && (class != 0 || c == 0) {
				found = true
			}
		}
		if !found {
			t.Fatalf("vacuous sweep: no outcome with %v (%v)", class, seen)
		}
	}
}

// want0Range reports whether the oracle's TowardZero outcome is a range
// error, where no directed pair exists to enclose.
func want0Range(exact *big.Int, ideal, p int64, g fmaGuards) bool {
	return fmaOracle(exact, ideal, p, TowardZero, g).rangeError
}

// TestFMAEqualsMulThenAdd checks that the default regime is exact:
// FMAWithContext at Context{}, with and without a budget, returns exactly Mul then Add, representation
// and cohort included, over random inline and limb-held operands, zeros
// and near cancellations; the value is the math/big exact sum at
// min(ex+ey, ez). An exponent sum outside int32 is Mul's ErrExponentRange
// under FMA's own Op, for a zero operand too.
func TestFMAEqualsMulThenAdd(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 61))
	slow := 0
	for i := range 6000 {
		x, y, z := fmaTriple(r, 1+r.IntN(70), -40, 40)
		product, err := x.Mul(y)
		if err != nil {
			t.Fatal(err)
		}
		want, err := product.Add(z)
		if err != nil {
			t.Fatal(err)
		}
		exact, ideal := fmaExact(x, y, z)
		if contextTestCoefficient(want).Cmp(exact) != 0 || int64(want.exponent()) != ideal {
			t.Fatalf("case %d: Mul then Add %v is not the exact sum %s·10^%d", i, want, exact, ideal)
		}
		if want.slow != nil {
			slow++
		}
		for name, call := range map[string]func() (Decimal, error){
			"fmaExactBudget": func() (Decimal, error) {
				return x.fmaExactBudget(y, z, Budget{MaxWork: math.MaxUint64})
			},
			"fmaGeneral": func() (Decimal, error) {
				got, _, err := x.fmaGeneral(y, z, Context{}.WithBudget(Budget{MaxWork: math.MaxUint64}))
				return got, err
			},
			"FMAWithContext": func() (Decimal, error) {
				got, conditions, err := x.FMAWithContext(y, z, Context{})
				if conditions != 0 {
					t.Fatalf("Context{} reported %v", conditions)
				}
				return got, err
			},
		} {
			got, err := call()
			if err != nil || !sameRepresentation(got, want) {
				t.Fatalf("case %d: %s(%v, %v, %v) = %v, %v; Mul then Add %v", i, name, x, y, z, got, err, want)
			}
		}
	}
	if slow < 1000 {
		t.Fatalf("only %d limb-held results", slow)
	}
	for _, tc := range []struct{ x, y Decimal }{
		{New(1, math.MaxInt32), New(1, 1)},
		{New(0, math.MaxInt32), New(0, 1)},
		{New(-5, math.MinInt32), New(3, -1)},
		{zeroDecimal(math.MinInt32), zeroDecimal(-1)},
	} {
		_, mulErr := tc.x.Mul(tc.y)
		for name, err := range map[string]error{
			"fmaExactBudget": second(tc.x.fmaExactBudget(tc.y, One(), Budget{MaxWork: 1})),
			"FMAWithContext": func() error {
				_, _, err := tc.x.FMAWithContext(tc.y, One(), Context{})
				return err
			}(),
		} {
			var oe *Error
			if !errors.Is(mulErr, ErrExponentRange) || !errors.Is(err, ErrExponentRange) || !errors.As(err, &oe) || oe.Op != "FMAWithContext" {
				t.Fatalf("%s(%v, %v): %v; Mul %v", name, tc.x, tc.y, err, mulErr)
			}
		}
	}
	// The exponent sum at either int32 end is valid.
	for _, tc := range []struct{ x, y, z Decimal }{
		{New(3, math.MaxInt32-1), New(7, 1), New(1, math.MaxInt32-5)},
		{New(3, math.MinInt32+1), New(-7, -1), New(1, math.MinInt32)},
	} {
		want, _ := tc.x.Mul(tc.y)
		want, _ = want.Add(tc.z)
		if got, err := tc.x.fmaExact(tc.y, tc.z); err != nil || !sameRepresentation(got, want) {
			t.Fatalf("FMA(%v, %v, %v) = %v, %v; want %v", tc.x, tc.y, tc.z, got, err, want)
		}
	}
}

func second[T any](_ T, err error) error { return err }

// fmaExact is FMAWithContext at Context{}: the exact x·y + z. There is no
// bare FMA, so the exact regime is reached through the context form.
func (d Decimal) fmaExact(y, z Decimal) (Decimal, error) {
	result, _, err := d.FMAWithContext(y, z, Context{})
	return result, err
}

// fmaExactBudget is FMAWithContext at Context{} carrying budget.
func (d Decimal) fmaExactBudget(y, z Decimal, budget Budget) (Decimal, error) {
	result, _, err := d.FMAWithContext(y, z, Context{}.WithBudget(budget))
	return result, err
}

// fmaGeneral is FMAWithContext on the product-term path alone, the general
// path the inline paths defer to: the bare kernel's exponent check and
// fmaTerms at precision 0, and contextFMATerms otherwise, under the
// context's budget.
func (d Decimal) fmaGeneral(y, z Decimal, ctx Context) (Decimal, Conditions, error) {
	const op = "FMAWithContext"
	e := int64(d.exponent()) + int64(y.exponent())
	if ctx.precision != 0 {
		return d.contextFMATerms(y, z, e, ctx, ctx.arith, op)
	}
	if e < math.MinInt32 || e > math.MaxInt32 {
		return contextFailure(op, ErrExponentRange)
	}
	result, err := d.fmaTerms(y, z, e, ctx.arith, op)
	return result, 0, err
}

// TestFMAInlineMatchesLimbs pins the inline fast paths to the general
// product-term paths (fast paths never own semantics): for
// inline operands, the unbudgeted bare and context forms, which take
// inlineMul and the Add kernels, equal the product-term paths, in
// representation, Conditions and error. A vacuity guard requires both
// fast-path hits and products beyond 2^128.
func TestFMAInlineMatchesLimbs(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 62))
	unlimited := Budget{MaxWork: math.MaxUint64, MaxDigits: math.MaxUint64}
	var fast, wide int
	var sumInline, sumDeferred, contextExact, contextDeferred int
	for range 40000 {
		x, y, z := fmaTriple(r, 38, -25, 25)
		if x.slow != nil || y.slow != nil {
			continue
		}
		product, productInline := inlineMul(x, y)
		if productInline {
			fast++
		} else {
			wide++
		}
		got, err := x.fmaExact(y, z)
		want, _, wantErr := x.fmaGeneral(y, z, Context{}.WithBudget(unlimited))
		if !sameRepresentation(got, want) || (err == nil) != (wantErr == nil) {
			t.Fatalf("bare FMA(%v, %v, %v): fast %v %v, general %v %v", x, y, z, got, err, want, wantErr)
		}
		mode := fmaModes[r.IntN(len(fmaModes))]
		var guards *ExponentGuards
		if r.IntN(3) == 0 {
			guards = &ExponentGuards{Emin: int32(-r.IntN(40)), Emax: int32(r.IntN(40))}
		}
		ctx := contextTestContext(t, uint32(1+r.IntN(40)), mode, guards, 0)
		if productInline {
			var exact Decimal
			var ok bool
			if z.slow == nil {
				exact, ok = inlineAddSub(product, z, false)
			}
			if ok {
				sumInline++
			} else {
				sumDeferred++
			}
			if ok && contextExactFits(exact, ctx) {
				contextExact++
			} else {
				contextDeferred++
			}
		}
		gotC, events, err := x.FMAWithContext(y, z, ctx)
		wantC, wantEvents, wantErr := x.fmaGeneral(y, z, ctx.WithBudget(unlimited))
		if !sameRepresentation(gotC, wantC) || events != wantEvents || (err == nil) != (wantErr == nil) || err != nil && err.Error() != wantErr.Error() {
			t.Fatalf("context FMA(%v, %v, %v) %+v: fast %v %v %v, general %v %v %v", x, y, z, ctx, gotC, events, err, wantC, wantEvents, wantErr)
		}
	}
	if fast < 10000 || wide < 1000 {
		t.Fatalf("vacuous: %d fast-path products, %d beyond 2^128", fast, wide)
	}
	if sumInline < 100 || sumDeferred < 100 || contextExact < 100 || contextDeferred < 100 {
		t.Fatalf("vacuous FMA sum classes: inline=%d deferred=%d context-exact=%d context-deferred=%d", sumInline, sumDeferred, contextExact, contextDeferred)
	}
	t.Logf("actual FMA outcomes: products=%d wide=%d sum-inline=%d sum-deferred=%d context-exact=%d context-deferred=%d", fast, wide, sumInline, sumDeferred, contextExact, contextDeferred)
}

// TestFMAOneRoundingGDA pins GDA's fma example: at
// p=9, 888565290 × 1557.96930 − 86087.7578 is 1.38435736E+12 rounded once,
// while MulWithContext then AddWithContext rounds the product first and
// gives 1.38435735E+12. The exact value 1384357356777.83920 is checked
// with math/big, and the result is Increased over it.
func TestFMAOneRoundingGDA(t *testing.T) {
	x, y, z := MustParse("888565290"), MustParse("1557.96930"), MustParse("-86087.7578")
	exact := new(big.Rat).Add(new(big.Rat).Mul(divRat(t, x), divRat(t, y)), divRat(t, z))
	if exact.FloatString(5) != "1384357356777.83920" {
		t.Fatalf("exact x·y + z = %s", exact.FloatString(5))
	}
	for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, AwayFromZero, TowardPositiveInfinity} {
		ctx := contextTestContext(t, 9, mode, nil, 0)
		got, conditions, err := x.FMAWithContext(y, z, ctx)
		if err != nil || got.String() != "1.38435736E+12" || conditions != Inexact|Rounded|Increased {
			t.Fatalf("mode %d: FMAWithContext = %v %v %v", mode, got, conditions, err)
		}
		product, _, _ := x.MulWithContext(y, ctx)
		twice, _, _ := product.AddWithContext(z, ctx)
		if mode <= TiesTowardZero && twice.String() != "1.38435735E+12" {
			t.Fatalf("mode %d: Mul then Add = %v", mode, twice)
		}
	}
}

// TestFMAInt32Edges checks exponent edges: the internal product exponent is
// int64 and only the published exponent must fit. FMA(1E−2000000000,
// 1E−2000000000, 1) at p=34 under TiesToEven is 1 at exponent −33 with 34
// digits and Inexact|Rounded|Decreased, while FMAWithContext at Context{} refuses with Mul's
// ErrExponentRange. A product exponent above int32 overflows to Bmax under
// guards and is ErrExponentRange without them; a product far below int32
// underflows under guards; an exact zero at an ideal exponent outside
// int32 is ErrExponentRange; a zero product below int32 keeps the ideal
// exponent's cohort. The budgeted form agrees under a budget of 2^20
// units: the context reduction, over int64 exponents, makes a gap of
// billions of digits cost O(p) there too.
func TestFMAInt32Edges(t *testing.T) {
	tiny := MustParse("1E-2000000000")
	huge := MustParse("1E+2000000000")
	guarded := Decimal128Context()
	half := int32(-1073741850) // two halves sum to 100 below MinInt32
	for _, tc := range []struct {
		label      string
		x, y, z    Decimal
		ctx        Context
		want       string
		exponent   int32
		conditions Conditions
		code       ErrorCode
	}{
		{"witness", tiny, tiny, One(), mustContext(t, 34, TiesToEven), "1.000000000000000000000000000000000", -33, Inexact | Rounded | Decreased, 0},
		{"witness, up", tiny, tiny, One(), mustContext(t, 34, AwayFromZero), "1.000000000000000000000000000000001", -33, Inexact | Rounded | Increased, 0},
		{"witness, negative addend", tiny, tiny, New(-1, 0), mustContext(t, 34, TowardZero), "-0.9999999999999999999999999999999999", -34, Inexact | Rounded | Increased, 0},
		{"witness, guarded", tiny, tiny, One(), guarded, "1.000000000000000000000000000000000", -33, Inexact | Rounded | Decreased, 0},
		{"huge product, guarded", huge, huge, One(), guarded, "9.999999999999999999999999999999999E+6144", 6111, Overflow | Inexact | Rounded | Decreased, 0},
		{"huge negative product, guarded", huge, huge.Neg(), One(), guarded, "-9.999999999999999999999999999999999E+6144", 6111, Overflow | Inexact | Rounded | Increased, 0},
		{"huge product, unguarded", huge, huge, One(), mustContext(t, 34, TiesToEven), "", 0, 0, ErrExponentRange},
		{"tiny product alone, unguarded", tiny, tiny, Zero(), mustContext(t, 34, TiesToEven), "", 0, 0, ErrExponentRange},
		{"tiny product alone, guarded", tiny, tiny, Zero(), guarded, "0E-6176", -6176, Subnormal | Underflow | Inexact | Rounded | Decreased, 0},
		{"tiny product alone, guarded, up", tiny, tiny, Zero(), contextTestContext(t, 34, AwayFromZero, &ExponentGuards{Emin: -6143, Emax: 6144}, 0), "1E-6176", -6176, Subnormal | Underflow | Inexact | Rounded | Increased, 0},
		{"negative tiny product alone, guarded", MustParse("3E-2000000000"), MustParse("-2E-2000000000"), Zero(), guarded, "0E-6176", -6176, Subnormal | Underflow | Inexact | Rounded | Increased, 0},
		{"zero product at an int64 exponent", zeroDecimal(-2000000000), zeroDecimal(-2000000000), Zero(), guarded, "", 0, 0, ErrExponentRange},
		{"zero product below int32, near addend", zeroDecimal(half), New(7, half), New(5, -2147483600), mustContext(t, 34, TiesToEven), "5.000000000000000000000000000000000E-2147483600", -2147483633, Rounded, 0},
	} {
		for _, budget := range []Budget{{}, {MaxWork: 1 << 20}} {
			got, conditions, err := tc.x.FMAWithContext(tc.y, tc.z, tc.ctx.WithBudget(budget))
			label := fmt.Sprintf("%s, budget %+v", tc.label, budget)
			if tc.code != 0 {
				if !errors.Is(err, tc.code) || conditions != 0 || !sameRepresentation(got, Decimal{}) {
					t.Fatalf("%s: %v %v %v, want %v", label, got, conditions, err, tc.code)
				}
				continue
			}
			if err != nil || got.String() != tc.want || got.exponent() != tc.exponent || conditions != tc.conditions {
				t.Fatalf("%s: %v (e %d) %v %v; want %s (e %d) %v", label, got, got.exponent(), conditions, err, tc.want, tc.exponent, tc.conditions)
			}
		}
	}
	// An opposite-sign comparison with the product's exponent below int32
	// keeps the adjusted exponents in int64.
	rx, ry, rz := MustParse("3.8990598979E-2147483622"), MustParse("3.90693909940200990520E-17"), MustParse("-5.059E-2147483642")
	exact, ideal := fmaExact(rx, ry, rz)
	for _, mode := range fmaModes {
		ctx := contextTestContext(t, 3, mode, nil, 0)
		got, conditions, err := rx.FMAWithContext(ry, rz, ctx)
		fmaCheck(t, fmt.Sprintf("int64 adjusted exponent mode %d", mode), got, conditions, err, fmaOracle(exact, ideal, 3, mode, fmaGuards{}))
	}
	// An exact zero at exactly MinInt32 is publishable.
	for _, budget := range []Budget{{}, {MaxWork: 100}} {
		half := zeroDecimal(math.MinInt32 / 2)
		got, conditions, err := half.FMAWithContext(half, Zero(), mustContext(t, 34, TiesToEven).WithBudget(budget))
		if err != nil || !got.isZero() || got.exponent() != math.MinInt32 || conditions != 0 {
			t.Fatalf("zero at MinInt32, budget %+v: %v (e %d) %v %v", budget, got, got.exponent(), conditions, err)
		}
	}
	for _, x := range []Decimal{tiny, huge, zeroDecimal(-2000000000)} {
		if _, err := x.fmaExact(x, One()); !errors.Is(err, ErrExponentRange) {
			t.Fatalf("bare FMA of a product exponent outside int32: %v", err)
		}
	}
	if got, _, err := tiny.FMAWithContext(tiny, One(), mustContext(t, 34, TiesToEven)); err != nil || got.CoefficientDigits() != 34 {
		t.Fatalf("witness digits: %v %v", got, err)
	}
}

// TestFMAFarAddendIsSticky checks that FMA with z far from the product
// costs O(p): with the addend, or the product, wholly below
// the other's rounding position, the context form substitutes one sticky
// digit, so the result at gaps up to about 4·10⁹ digits equals the result
// at a gap of 60, which the math/big oracle checks, in every mode and sign
// arrangement. A zero product or zero addend far below the other operand
// is clamped: its result and its smallest
// admitting work cap do not depend on the gap. Every call together
// finishes in well under the time one gap-sized stream would take
// (billions of digits).
func TestFMAFarAddendIsSticky(t *testing.T) {
	x, y := MustParse("1234567890123456789012345"), MustParse("-9.87654321")
	start := time.Now()
	calls := 0
	for _, mode := range fmaModes[:7] {
		ctx := contextTestContext(t, 16, mode, nil, 0)
		for _, sign := range []int64{1, -1} {
			for _, productLarge := range []bool{true, false} {
				// shift is how far the product moves up with the gap, so every
				// exponent stays within int32 up to a gap of 4·10⁹.
				shift := func(gap int64) int64 {
					if productLarge {
						return gap / 2
					}
					return 0
				}
				place := func(gap int64) (Decimal, Decimal, Decimal) {
					if productLarge {
						// z lies gap places below the product's last digit.
						px := sqrtDecimal(contextTestCoefficient(x), int64(x.exponent())+shift(gap))
						return px, y, sqrtDecimal(big.NewInt(7*sign), int64(px.exponent())+int64(y.exponent())-gap)
					}
					// The product lies gap places below z's last digit.
					return New(3, int32(-gap/2)), New(-7*sign, int32(-gap+gap/2)), New(5, 0)
				}
				nx, ny, nz := place(60)
				exact, ideal := fmaExact(nx, ny, nz)
				want := fmaOracle(exact, ideal, 16, mode, fmaGuards{})
				for _, gap := range []int64{60, 1000, 200_000_000, 2_000_000_000, 4_000_000_000} {
					fx, fy, fz := place(gap)
					got, conditions, err := fx.FMAWithContext(fy, fz, ctx)
					calls++
					label := fmt.Sprintf("mode %d sign %d productLarge %v gap %d", mode, sign, productLarge, gap)
					if gap == 60 {
						fmaCheck(t, label, got, conditions, err, want)
						continue
					}
					if want.coefficient.String() != got.coefficientDigits() || want.exponent+shift(gap)-shift(60) != int64(got.exponent()) || want.negative != got.negative() || want.conditions != conditions || err != nil {
						t.Fatalf("%s: %v %v %v, at gap 60 %v", label, got, conditions, err, want)
					}
				}
			}
		}
	}
	// A zero product or a zero addend far below the other operand: the
	// context reduction clamps the zero, so the result, its Conditions
	// and the smallest admitting work cap are those at a gap of 60, in
	// every mode and for both signs of the nonzero operand.
	for _, mode := range fmaModes[:7] {
		ctx := contextTestContext(t, 16, mode, nil, 0)
		for _, sign := range []int64{1, -1} {
			for _, zeroProduct := range []bool{true, false} {
				shift := func(gap int64) int64 {
					if zeroProduct {
						return 0
					}
					return gap / 2
				}
				place := func(gap int64) (Decimal, Decimal, Decimal) {
					if zeroProduct {
						return zeroDecimal(int32(-gap / 2)), New(7, int32(-gap+gap/2)), New(12345*sign, 0)
					}
					px := sqrtDecimal(contextTestCoefficient(x), int64(x.exponent())+shift(gap))
					return px, New(-7*sign, 0), zeroDecimal(int32(int64(px.exponent()) - gap))
				}
				nx, ny, nz := place(60)
				exact, ideal := fmaExact(nx, ny, nz)
				want := fmaOracle(exact, ideal, 16, mode, fmaGuards{})
				var firstCap uint64
				for _, gap := range []int64{60, 1000, 200_000_000, 2_000_000_000, 4_000_000_000} {
					fx, fy, fz := place(gap)
					label := fmt.Sprintf("zero product %v mode %d sign %d gap %d", zeroProduct, mode, sign, gap)
					got, conditions, err := fx.FMAWithContext(fy, fz, ctx)
					calls++
					if want.coefficient.String() != got.coefficientDigits() || want.exponent+shift(gap)-shift(60) != int64(got.exponent()) || want.negative != got.negative() || want.conditions != conditions || err != nil {
						t.Fatalf("%s: %v %v %v, at gap 60 %v", label, got, conditions, err, want)
					}
					limit := smallestAdmitting(1<<40, func(w uint64) bool {
						_, _, err := fx.FMAWithContext(fy, fz, ctx.WithBudget(Budget{MaxWork: w}))
						return err == nil
					})
					calls += 40
					if gap == 60 {
						firstCap = limit
					} else if limit != firstCap {
						t.Fatalf("%s: smallest work cap %d, at gap 60 %d", label, limit, firstCap)
					}
				}
			}
		}
	}
	// Operands whose unreduced streams would hold billions of padded
	// zeros.
	ctx34 := mustContext(t, 34, TiesToEven)
	for _, tc := range []struct {
		x, y, z Decimal
		want    string
	}{
		{zeroDecimal(math.MinInt32), New(1, math.MinInt32), New(1, math.MaxInt32), "1.000000000000000000000000000000000E+2147483647"},
		{zeroDecimal(-2000000000), New(1, -2000000000), One(), "1.000000000000000000000000000000000"},
		{New(3, 0), New(7, 0), zeroDecimal(-2000000000), "21.00000000000000000000000000000000"},
	} {
		got, conditions, err := tc.x.FMAWithContext(tc.y, tc.z, ctx34)
		calls++
		if err != nil || got.String() != tc.want || conditions != Rounded {
			t.Fatalf("FMA(%v, %v, %v): %v %v %v; want %s with Rounded", tc.x, tc.y, tc.z, got, conditions, err, tc.want)
		}
	}
	if elapsed := time.Since(start); elapsed > 2*time.Second {
		t.Fatalf("%d far-operand FMA calls took %v", calls, elapsed)
	}
}

// TestFMAGuardsExactAndTraps covers the context form's guards, Exact mode
// and traps: an inexact sum refuses under Exact with
// zero value and Conditions, while a zero-only discard succeeds with
// Rounded; overflow publishes Bmax, and Exact refuses it; a subnormal sum
// reports Subnormal and Underflow; a trapped condition returns the finite
// result, the untrapped Conditions and an *Error naming the trap.
func TestFMAGuardsExactAndTraps(t *testing.T) {
	exactCtx := mustContext(t, 3, Exact)
	if got, conditions, err := MustParse("1.1").FMAWithContext(MustParse("1.1"), MustParse("0.001"), exactCtx); !isInexactRefusal(err) || conditions != 0 || !sameRepresentation(got, Decimal{}) {
		t.Fatalf("Exact inexact: %v %v %v", got, conditions, err)
	}
	if got, conditions, err := New(25, 0).FMAWithContext(New(40, 0), New(0, 1), exactCtx); err != nil || got.String() != "1.00E+3" || conditions != Rounded {
		t.Fatalf("Exact zero-only discard: %v %v %v", got, conditions, err)
	}
	guards := &ExponentGuards{Emin: -5, Emax: 5}
	over := contextTestContext(t, 3, TiesToEven, guards, 0)
	if got, conditions, err := New(999, 2).FMAWithContext(New(9, 1), New(1, 0), over); err != nil || got.String() != "9.99E+5" || conditions != Overflow|Inexact|Rounded|Decreased {
		t.Fatalf("overflow: %v %v %v", got, conditions, err)
	}
	if _, _, err := New(999, 2).FMAWithContext(New(9, 1), New(1, 0), contextTestContext(t, 3, Exact, guards, 0)); !isInexactRefusal(err) {
		t.Fatalf("Exact overflow: %v", err)
	}
	if got, conditions, err := New(3, -4).FMAWithContext(New(7, -4), New(6, -8), over); err != nil || got.String() != "3E-7" || conditions != Subnormal|Underflow|Inexact|Rounded|Increased {
		t.Fatalf("subnormal: %v %v %v", got, conditions, err)
	}
	trapped := contextTestContext(t, 3, TiesToEven, guards, Inexact)
	got, conditions, err := MustParse("1.1").FMAWithContext(MustParse("1.1"), MustParse("0.001"), trapped)
	var ce *Error
	if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Op != "FMAWithContext" || got.String() != "1.21" || conditions != Rounded|Decreased {
		t.Fatalf("trapped Inexact: %v %v %v", got, conditions, err)
	}
	budgeted := contextTestContext(t, 3, TiesToEven, guards, Overflow)
	got, conditions, err = New(999, 2).FMAWithContext(New(9, 1), New(1, 0), budgeted.WithBudget(Budget{MaxWork: 1 << 10}))
	if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Overflow || ce.Op != "FMAWithContext" || got.String() != "9.99E+5" || conditions != Inexact|Rounded|Decreased {
		t.Fatalf("trapped Overflow: %v %v %v", got, conditions, err)
	}
}

func isInexactRefusal(err error) bool {
	var ce *Error
	return errors.As(err, &ce) && ce.Condition == Inexact && errors.Is(err, ErrInexact)
}

// TestFMAZerosAndSigns covers FMA's zero and sign rules: a
// zero factor, including a negative zero, gives an unsigned zero product at
// ex+ey, so the result is z at min(ex+ey, ez); an exact cancellation is an
// unsigned zero at the preferred exponent, bare and in context; every sign
// arrangement of a nonzero sum is the sign of the exact value.
func TestFMAZerosAndSigns(t *testing.T) {
	negZero := inlineDecimal(uint128{}, -3, true)
	ctx := mustContext(t, 5, TiesToEven)
	for _, tc := range []struct {
		x, y, z Decimal
		want    string
		e       int32
	}{
		{negZero, New(-7, 2), New(-5, 0), "-5.0", -1},
		{negZero, New(7, 2), New(5, -6), "0.000005", -6},
		{Zero(), Zero(), negZero, "0.000", -3},
		{negZero, negZero, Zero(), "0.000000", -6},
		{New(-3, -2), New(4, -1), MustParse("0.012"), "0.000", -3},
		{New(3, -2), New(-4, -1), MustParse("0.0120"), "0.0000", -4},
	} {
		got, err := tc.x.fmaExact(tc.y, tc.z)
		if err != nil || got.String() != tc.want || got.exponent() != tc.e || got.isZero() && got.negative() {
			t.Fatalf("FMA(%v, %v, %v) = %v (e %d, negative %v), %v; want %s at %d", tc.x, tc.y, tc.z, got, got.exponent(), got.negative(), err, tc.want, tc.e)
		}
		gotC, conditions, err := tc.x.FMAWithContext(tc.y, tc.z, ctx)
		if err != nil || !sameRepresentation(gotC, got) || conditions != 0 {
			t.Fatalf("FMAWithContext(%v, %v, %v) = %v, %v, %v; want %v", tc.x, tc.y, tc.z, gotC, conditions, err, got)
		}
	}
	for _, sx := range []int64{1, -1} {
		for _, sy := range []int64{1, -1} {
			for _, sz := range []int64{1, -1} {
				for _, z := range []int64{2, 30} {
					x, y, zz := New(3*sx, 0), New(4*sy, 0), New(z*sz, 0)
					got, err := x.fmaExact(y, zz)
					want := 12*sx*sy + z*sz
					if err != nil || got.String() != New(want, 0).String() {
						t.Fatalf("FMA(%v, %v, %v) = %v, %v; want %d", x, y, zz, got, err, want)
					}
				}
			}
		}
	}
}

// fmaTile is t(d) = 1+(d−1)/9.
func fmaTile(d uint64) uint64 { return 1 + (d-1)/9 }

// fmaClosedCharge is the documented FMA tariff, derived by hand
// from the shapes: Mul's charge t(dx)·t(dy)+dx+dy (1 for a zero factor)
// plus the Add/Sub charge with the product as a (dx+dy)-digit operand at
// ex+ey: L = the larger aligned span; same signs dP+dz+L+1, opposite signs
// 2(dP+dz)+L (only dP+dz when they cancel), one zero L, both zero 1. It
// returns that base B and L.
func fmaClosedCharge(x, y, z Decimal, cancel bool) (uint64, uint64) {
	dx, dy, dz := x.CoefficientDigits(), y.CoefficientDigits(), z.CoefficientDigits()
	productZero := x.isZero() || y.isZero()
	pre, dp := uint64(1), uint64(1)
	if !productZero {
		pre, dp = fmaTile(dx)*fmaTile(dy)+dx+dy, dx+dy
	}
	ep, ez := int64(x.exponent())+int64(y.exponent()), int64(z.exponent())
	e := min(ep, ez)
	spanP, spanZ := dp+uint64(ep-e), dz+uint64(ez-e)
	switch {
	case productZero && z.isZero():
		return pre + 1, 1
	case productZero:
		return pre + spanZ, spanZ
	case z.isZero():
		return pre + spanP, spanP
	}
	L := max(spanP, spanZ)
	if (x.negative() != y.negative()) == z.negative() {
		return pre + dp + dz + L + 1, L
	}
	if cancel {
		return pre + dp + dz, L
	}
	return pre + 2*(dp+dz) + L, L
}

// fmaContextCharge is the context tariff's base B, derived by hand from
// the documented rules rather than from the planner: the product is a span
// of dx+dy−1 or dx+dy digits at ex+ey (int64) and z its own span; the
// context reduction's rule (b) clamps a zero to
// max(e_zero, min(e_nz, pos−1)) with pos = e_nz+d−p (the least d), raised
// to Etiny under guards; rule (a) replaces a nonzero operand whose greatest
// adjusted exponent lies below P = min(e_large, adj_large−p−1)−1 (the
// large operand's least adjusted exponent) by one digit at P. B is Mul's
// charge plus the Add/Sub charge over the reduced operands, planned at dx+dy.
func fmaContextCharge(x, y, z Decimal, ctx Context, cancel bool) uint64 {
	type span struct {
		lo, hi uint64
		e      int64
		neg    bool
	}
	dx, dy := x.CoefficientDigits(), y.CoefficientDigits()
	pre := uint64(1)
	prod := span{e: int64(x.exponent()) + int64(y.exponent()), neg: x.negative() != y.negative()}
	if !x.isZero() && !y.isZero() {
		pre = fmaTile(dx)*fmaTile(dy) + dx + dy
		prod.lo, prod.hi = dx+dy-1, dx+dy
	}
	add := span{e: int64(z.exponent()), neg: z.negative()}
	if !z.isZero() {
		add.lo, add.hi = z.CoefficientDigits(), z.CoefficientDigits()
	}
	p := int64(ctx.precision)
	clamp := func(zero *span, nz span) {
		pos := nz.e + int64(nz.lo) - p
		if ctx.guarded {
			pos = max(pos, int64(ctx.guards.Emin)-p+1)
		}
		zero.e = max(zero.e, min(nz.e, pos-1))
	}
	switch {
	case prod.hi == 0 && add.hi == 0:
		return pre + 1
	case prod.hi == 0:
		clamp(&prod, add)
		return pre + add.hi + uint64(add.e-min(add.e, prod.e))
	case add.hi == 0:
		clamp(&add, prod)
		return pre + prod.hi + uint64(prod.e-min(prod.e, add.e))
	}
	adjLo := func(s span) int64 { return s.e + int64(s.lo) - 1 }
	adjHi := func(s span) int64 { return s.e + int64(s.hi) - 1 }
	for _, pair := range [][2]*span{{&prod, &add}, {&add, &prod}} {
		large, small := pair[0], pair[1]
		if adjLo(*large) > adjHi(*small) {
			if position := min(large.e, adjLo(*large)-p-1) - 1; adjHi(*small) < position {
				*small = span{lo: 1, hi: 1, e: position, neg: small.neg}
			}
		}
	}
	e := min(prod.e, add.e)
	L := max(prod.hi+uint64(prod.e-e), add.hi+uint64(add.e-e))
	inputs := prod.hi + add.hi
	switch {
	case prod.neg == add.neg:
		return pre + inputs + L + 1
	case cancel:
		return pre + inputs
	}
	return pre + 2*inputs + L
}

// TestFMABudgetCharges counts the charges of the FMA tariff: over random shapes, signs, zeros, cancellations and
// exponent gaps, the smallest work cap FMAWithContext at Context{} admits is the closed
// form B, and that of FMAWithContext at a finite precision is B + 2N + 1 for its N-digit
// result; the smallest digit cap is Add's over the (dx+dy)-digit product
// (L or L+1 by the exact carry for same signs, L otherwise) bare, and N in
// context; one unit or digit less refuses. The context base is over the
// operands as the context planner reduces them (fmaContextCharge).
func TestFMABudgetCharges(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 63))
	counted := 0
	for i := range 1500 {
		x, y, z := fmaTriple(r, 1+r.IntN(60), -20, 20)
		exact, _ := fmaExact(x, y, z)
		cancel := exact.Sign() == 0 && !x.isZero() && !y.isZero() && !z.isZero()
		B, L := fmaClosedCharge(x, y, z, cancel)
		label := fmt.Sprintf("case %d: FMA(%v, %v, %v)", i, x, y, z)
		bare := func(b Budget) error { _, err := x.fmaExactBudget(y, z, b); return err }
		if w := smallestAdmitting(1<<40, func(w uint64) bool { return bare(Budget{MaxWork: w}) == nil }); w != B {
			t.Fatalf("%s: smallest work cap %d, closed form %d", label, w, B)
		}
		want, _ := x.fmaExact(y, z)
		digits := L
		switch {
		case cancel:
			digits = 1
		case !x.isZero() && !y.isZero() && !z.isZero() && (x.negative() != y.negative()) == z.negative() && want.CoefficientDigits() > L:
			digits = L + 1
		}
		if n := smallestAdmitting(1<<40, func(n uint64) bool { return bare(Budget{MaxDigits: n}) == nil }); n != digits {
			t.Fatalf("%s: smallest digit cap %d, want %d", label, n, digits)
		}
		ctx := contextTestContext(t, uint32(1+r.IntN(40)), fmaModes[r.IntN(7)], nil, 0)
		got, _, err := x.FMAWithContext(y, z, ctx)
		if err != nil {
			t.Fatal(err)
		}
		run := func(b Budget) error { _, _, err := x.FMAWithContext(y, z, ctx.WithBudget(b)); return err }
		N := got.CoefficientDigits()
		BC := fmaContextCharge(x, y, z, ctx, cancel)
		if w := smallestAdmitting(1<<40, func(w uint64) bool { return run(Budget{MaxWork: w}) == nil }); w != BC+2*N+1 {
			t.Fatalf("%s p=%d: smallest context work cap %d, closed form %d", label, ctx.precision, w, BC+2*N+1)
		}
		if n := smallestAdmitting(1<<40, func(n uint64) bool { return run(Budget{MaxDigits: n}) == nil }); n != N {
			t.Fatalf("%s p=%d: smallest context digit cap %d, want %d", label, ctx.precision, n, N)
		}
		counted++
	}
	if counted < 1500 {
		t.Fatalf("counted %d", counted)
	}
}

// TestFMARefusesBeforeAllocating checks that FMA budgets refuse before allocating:
// with a product of 223 limbs, beyond the stack scratch, every refusal the
// shapes decide (a work cap below the same-sign charge or below the
// opposite-sign comparison precharge, a digit cap below L, bare and in
// context) comes before the product's scratch; an opposite-sign cap
// between the precharge and the full charge builds the product for the
// comparison and refuses before the result.
func TestFMARefusesBeforeAllocating(t *testing.T) {
	x, y := MustParse(strings.Repeat("7", 1000)), MustParse(strings.Repeat("3", 1000)+"E-5")
	scratch := uint64(4 * 223)
	ctx := mustContext(t, 34, TiesToEven)
	for _, z := range []Decimal{MustParse("12345"), MustParse("-12345")} {
		B, L := fmaClosedCharge(x, y, z, false)
		type refusal struct {
			name   string
			budget Budget
			limit  uint64
		}
		after := scratch + scratch/4 + 16 + 256
		cases := []refusal{
			{"work", Budget{MaxWork: B - 1}, 256},
			{"digits", Budget{MaxDigits: L - 1}, 256},
		}
		if z.negative() {
			// Opposite signs: only the comparison precharge is shape-decided;
			// the full charge and the digit cap follow the comparison, as
			// for Add, since an exact cancellation needs neither.
			pre := fmaTile(1000)*fmaTile(1000) + 2000
			cases = []refusal{
				{"precharge", Budget{MaxWork: pre + 2005 - 1}, 256},
				{"after comparison", Budget{MaxWork: B - 1}, after},
				{"digits after comparison", Budget{MaxDigits: L - 1}, after},
			}
		}
		for _, tc := range cases {
			for _, form := range []struct {
				name string
				call func() error
			}{
				{"bare", func() error { _, err := x.fmaExactBudget(y, z, tc.budget); return err }},
				{"context", func() error { _, _, err := x.FMAWithContext(y, z, ctx.WithBudget(tc.budget)); return err }},
			} {
				if form.name == "context" && strings.HasPrefix(tc.name, "digits") {
					continue // the context digit cap binds the published result
				}
				if err := form.call(); !errors.Is(err, ErrInsufficientStorage) {
					t.Fatalf("z=%v %s %s: %v", z, form.name, tc.name, err)
				}
				heap := coldAllocatedWithin(func() { _ = form.call() }, tc.limit)
				if heap > tc.limit {
					t.Fatalf("z=%v %s %s: refusal allocated %d bytes, limit %d", z, form.name, tc.name, heap, tc.limit)
				}
				if tc.limit == after && heap < scratch {
					t.Fatalf("z=%v %s: %d bytes, the comparison needs the product", z, form.name, heap)
				}
			}
		}
	}
}

// TestFMAAllocations covers FMA's allocation class: inline results allocate nothing, bare and in context; a result of at
// most 81 digits allocates only its fused holder; a product beyond the
// 48-limb stack scratch adds one scratch allocation (a 48-limb product
// stays on the stack); a heap product that is the whole sum is handed
// over without a copy; a zero product returns a limb-held addend without
// copying it; and FMA never
// allocates more than Mul then Add, which publishes the product.
func TestFMAAllocations(t *testing.T) {
	x19, y19, z19 := MustParse("4123456789012345678"), MustParse("1234567890123456789"), MustParse("-9876543210987654321")
	x40, y40 := MustParse(strings.Repeat("7", 40)), MustParse(strings.Repeat("3", 40)+"E-2")
	x250, y250 := MustParse(strings.Repeat("8", 250)), MustParse(strings.Repeat("6", 250))
	x200, y200 := MustParse(strings.Repeat("8", 216)), MustParse(strings.Repeat("6", 216))
	// A 67-limb product that is the whole sum is handed over without a
	// copy: its buffer and holder, as Mul publishes it.
	x7, y3 := MustParse(strings.Repeat("7", 300)), MustParse(strings.Repeat("3", 300))
	ctx34, ctx81 := Decimal128Context(), mustContext(t, 81, TiesToEven)
	for _, tc := range []struct {
		name         string
		fma, mulAdd  func()
		allow, extra float64
	}{
		{"bare inline", func() { _, _ = x19.fmaExact(y19, z19) }, func() { p, _ := x19.Mul(y19); _, _ = p.Add(z19) }, 0, 0},
		{"bare 80 digits", func() { _, _ = x40.fmaExact(y40, z19) }, func() { p, _ := x40.Mul(y40); _, _ = p.Add(z19) }, 1, 1},
		{"bare 500 digits", func() { _, _ = x250.fmaExact(y250, z19) }, func() { p, _ := x250.Mul(y250); _, _ = p.Add(z19) }, 3, 1},
		{"context inline", func() { _, _, _ = x19.FMAWithContext(y19, z19, ctx34) }, func() {
			p, _, _ := x19.MulWithContext(y19, ctx34)
			_, _, _ = p.AddWithContext(z19, ctx34)
		}, 0, 0},
		{"heap product returned as the sum", func() { _, _ = x7.fmaExact(y3, Zero()) }, func() { p, _ := x7.Mul(y3); _, _ = p.Add(Zero()) }, 2, 0},
		{"zero product returns a limb-held addend", func() { _, _ = Zero().fmaExact(New(5, 0), x40) }, func() { p, _ := Zero().Mul(New(5, 0)); _, _ = p.Add(x40) }, 0, 0},
		{"zero product of a limb-held factor returns the addend", func() { _, _ = Zero().fmaExact(x40, x40) }, func() { p, _ := Zero().Mul(x40); _, _ = p.Add(x40) }, 0, 0},
		{"context 81 digits", func() { _, _, _ = x40.FMAWithContext(y40, MustParse("1E-50"), ctx81) }, nil, 1, 0},
		{"context long operands", func() { _, _, _ = x250.FMAWithContext(y250, z19, ctx34) }, nil, 1, 0},
		{"context 48-limb product on the stack", func() { _, _, _ = x200.FMAWithContext(y200, z19, ctx34) }, nil, 0, 0},
	} {
		if n := testing.AllocsPerRun(50, tc.fma); n != tc.allow {
			t.Fatalf("%s: %v allocations, want %v", tc.name, n, tc.allow)
		}
		if tc.mulAdd != nil {
			if n := testing.AllocsPerRun(50, tc.mulAdd); n != tc.allow+tc.extra {
				t.Fatalf("%s: Mul then Add %v allocations, want %v", tc.name, n, tc.allow+tc.extra)
			}
		}
	}
}

// TestFMAReductionMatchesUnreduced pins FMA's reduction (fmaReduce: the
// context planner over the unbuilt product's digit bracket dx+dy−1..dx+dy
// and int64 exponents) to the unreduced reference path (fast paths never
// own semantics): over factors whose product often has
// dx+dy−1 digits, addends placed within a few digits of the sticky and
// clamp thresholds on both sides, zeros, all eight modes and guards,
// FMAWithContext and its budgeted twin equal the exact product added by
// contextAddSub with reduction off, in representation, Conditions and
// error. A vacuity guard requires every reduction kind to fire.
func TestFMAReductionMatchesUnreduced(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 65))
	unlimited := Budget{MaxWork: math.MaxUint64}
	fired := map[string]int{}
	for range 20000 {
		x, y := fmaOperand(r, 12, -20, 20), fmaOperand(r, 12, -20, 20)
		p := int64(1 + r.IntN(20))
		var z Decimal
		dz := 1 + r.IntN(12)
		// Place z around a threshold of the product: its last digit, or the
		// product's rounding position (adjusted − p), give or take a few.
		ep := int64(x.exponent()) + int64(y.exponent())
		adj := ep + int64(x.CoefficientDigits()+y.CoefficientDigits()) - 1
		anchor := []int64{ep, adj - p, adj + p + int64(dz), ep - int64(dz)}[r.IntN(4)]
		ez := anchor + int64(r.IntN(9)-4)
		switch r.IntN(6) {
		case 0:
			z = zeroDecimal(int32(ez))
		default:
			c := randomDigits(r, dz)
			if r.IntN(2) == 0 {
				c.Neg(c)
			}
			z = sqrtDecimal(c, ez)
		}
		var guards *ExponentGuards
		if r.IntN(3) == 0 {
			emin := int32(-r.IntN(40))
			guards = &ExponentGuards{Emin: emin, Emax: emin + int32(20+r.IntN(60))}
		}
		ctx := contextTestContext(t, uint32(p), fmaModes[r.IntN(len(fmaModes))], guards, 0)
		product, err := x.Mul(y)
		if err != nil {
			t.Fatal(err)
		}
		want, wantConditions, wantErr := product.contextAddSub(z, ctx.withLimits(unlimited.arith()), "FMAWithContext", false, false, nil)
		for _, budget := range []Budget{{}, unlimited} {
			got, conditions, err := x.FMAWithContext(y, z, ctx.WithBudget(budget))
			if !sameRepresentation(got, want) || conditions != wantConditions || (err == nil) != (wantErr == nil) {
				t.Fatalf("FMA(%v, %v, %v) %+v budget %+v: %v %v %v; unreduced %v %v %v", x, y, z, ctx, budget, got, conditions, err, want, wantConditions, wantErr)
			}
		}
		// The product-term path reduces its spans whether or not an inline
		// path would have served the call.
		got, conditions, err := x.fmaGeneral(y, z, ctx.WithBudget(unlimited))
		if !sameRepresentation(got, want) || conditions != wantConditions || (err == nil) != (wantErr == nil) {
			t.Fatalf("FMA(%v, %v, %v) %+v product-term path: %v %v %v; unreduced %v %v %v", x, y, z, ctx, got, conditions, err, want, wantConditions, wantErr)
		}
		xv, yv := coefficientViewOf(x), coefficientViewOf(y)
		a, _, _ := fmaProductTerm(&xv, &yv, ep, x.negative() != y.negative())
		var b addTerm
		b.load(z, false)
		ra, rb := a, b
		fmaReduce(&ra, &rb, ctx)
		switch {
		case ra.exponent != a.exponent && a.zero:
			fired["zero product clamped"]++
		case rb.exponent != b.exponent && b.zero:
			fired["zero addend clamped"]++
		case ra.v.count == 1 && !a.zero && a.v.count == 0:
			fired["product substituted"]++
		case rb.digits == 1 && rb.exponent != b.exponent:
			fired["addend substituted"]++
		}
	}
	for _, kind := range []string{"zero product clamped", "zero addend clamped", "product substituted", "addend substituted"} {
		if fired[kind] < 100 {
			t.Fatalf("vacuous: %v", fired)
		}
	}
}

// TestFMAReductionBelowInt32 checks a reduction below int32: the unpublished
// product may lie below int32 while the large addend is at MinInt32.
// Hand-derived: x*y is positive and far below Etiny, so ties-to-even keeps
// z=1E-MinInt32, with a downward inexact subnormal result and bounded work.
func TestFMAReductionBelowInt32(t *testing.T) {
	ctx := contextTestContext(t, 34, TiesToEven, &ExponentGuards{Emin: math.MinInt32 + 33, Emax: 0}, 0)
	x, y, z := New(1, -2000000000), New(1, -2000000000), New(1, math.MinInt32)
	got, conditions, err := x.FMAWithContext(y, z, ctx.WithBudget(Budget{MaxWork: 1000, MaxDigits: 34}))
	want := Inexact | Rounded | Subnormal | Underflow | Decreased
	if err != nil || got.coefficientDigits() != "1" || got.exponent() != math.MinInt32 || got.negative() || conditions != want {
		t.Fatalf("got coefficient=%s exponent=%d negative=%v conditions=%v err=%v; want 1E%d %v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, int64(math.MinInt32), want)
	}
}
