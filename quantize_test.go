// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"math"
	"math/big"
	randv1 "math/rand"
	"math/rand/v2"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
)

// quantizeWordOracle reads the independently supplied coefficient, rather than
// any rounded result. Its arbitrary-precision doubling cannot overflow.
func quantizeWordOracle(coefficient string, exponent, target int32, negative bool, mode RoundingMode) (string, bool, Conditions, bool) {
	n, ok := new(big.Int).SetString(coefficient, 10)
	if !ok {
		panic("invalid independent coefficient")
	}
	if n.Sign() == 0 {
		return "0", false, 0, false
	}
	difference := int64(exponent) - int64(target)
	power := new(big.Int).Exp(big.NewInt(10), big.NewInt(max(difference, -difference)), nil)
	if difference >= 0 {
		return n.Mul(n, power).String(), negative, 0, false
	}
	q, r := new(big.Int), new(big.Int)
	q.QuoRem(n, power, r)
	events := Rounded
	if r.Sign() != 0 {
		if mode == Exact {
			return "0", false, 0, true
		}
		events |= Inexact
	}
	half := new(big.Int).Lsh(r, 1).Cmp(power)
	up := false
	switch mode {
	case TiesToEven:
		up = half > 0 || half == 0 && q.Bit(0) == 1
	case TiesAwayFromZero:
		up = half >= 0
	case TiesTowardZero:
		up = half > 0
	case TowardZero, Exact:
	case AwayFromZero:
		up = r.Sign() != 0
	case TowardPositiveInfinity:
		up = r.Sign() != 0 && !negative
	case TowardNegativeInfinity:
		up = r.Sign() != 0 && negative
	default:
		panic("invalid oracle mode")
	}
	if up {
		q.Add(q, big.NewInt(1))
	}
	// Both integers are now expressed at the source exponent. Their comparison
	// independently supplies the sign of rounded value minus exact value.
	direction := new(big.Int).Mul(q, power).Cmp(n)
	if negative {
		direction = -direction
	}
	if direction < 0 {
		events |= Decreased
	} else if direction > 0 {
		events |= Increased
	}
	return q.String(), negative && q.Sign() != 0, events, false
}

// TestQuantizeOneWordPublicMatchesOracle checks all eight modes,
// cuts 1-20, zero/tie/sticky/parity/carry and canonical word-band boundaries.
// A positive budget forces the general path; the independent big.Int oracle
// owns the expected coefficient, cohort, sign, conditions and Exact identity.
func TestQuantizeOneWordPublicMatchesOracle(t *testing.T) {
	type fixture struct {
		coefficient string
		exponent    int32
		target      int32
	}
	var fixtures []fixture
	for cut := int32(1); cut <= 20; cut++ {
		divisor := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(cut)), nil)
		half := new(big.Int).Rsh(new(big.Int).Set(divisor), 1)
		remainders := []*big.Int{big.NewInt(0), big.NewInt(1), new(big.Int).Sub(half, big.NewInt(1)), half, new(big.Int).Add(half, big.NewInt(1)), new(big.Int).Sub(divisor, big.NewInt(1))}
		for quotient := int64(0); quotient <= 3; quotient++ {
			for _, remainder := range remainders {
				n := new(big.Int).Mul(big.NewInt(quotient), divisor)
				n.Add(n, remainder)
				fixtures = append(fixtures, fixture{n.String(), -cut, 0})
			}
		}
	}
	for _, coefficient := range []string{"0", "1", "999995", "9999999999999999999", "18446744073709551614", "18446744073709551615", "18446744073709551616", "18446744073709551617", strings.Repeat("9", 38), "340282366920938463463374607431768211455", "340282366920938463463374607431768211456", strings.Repeat("9", 40)} {
		for _, cut := range []int32{0, 1, 2, 19, 20} {
			fixtures = append(fixtures, fixture{coefficient, -cut, 0})
		}
		for _, target := range []int32{-3, -4, -19, -20} {
			fixtures = append(fixtures, fixture{coefficient, -2, target})
		}
	}
	var counts struct{ oneWord, twoWord, deferred, slow, zero, exactRefusal, carry int }
	for _, f := range fixtures {
		for _, negative := range []bool{false, true} {
			text := f.coefficient + "E" + strconv.FormatInt(int64(f.exponent), 10)
			if negative {
				text = "-" + text
			}
			d := MustParse(text)
			if d.coefficientDigits() != f.coefficient || d.exponent() != f.exponent || d.negative() != (negative && f.coefficient != "0") {
				t.Fatalf("fixture publication changed %s", text)
			}
			for mode := TiesToEven; mode <= Exact; mode++ {
				want, sign, events, refused := quantizeWordOracle(f.coefficient, f.exponent, f.target, negative, mode)
				ctx := Context{rounding: mode}
				budget := Budget{MaxWork: math.MaxUint64, MaxDigits: math.MaxUint64}
				general, generalEvents, generalErr := d.QuantizeWithContext(f.target, ctx.WithBudget(budget))
				check := func(op string, got Decimal, gotEvents Conditions, err error) {
					t.Helper()
					if refused {
						quantizeAbort(t, got, gotEvents, err, op, ErrInexact)
						return
					}
					if err != nil || !got.validRepresentation() || got.coefficientDigits() != want || got.exponent() != f.target || got.negative() != sign || gotEvents != events {
						t.Fatalf("%s(%s, %d, %v) = %s e%d sign%v %v %v; oracle %s sign%v %v", op, text, f.target, mode, got.coefficientDigits(), got.exponent(), got.negative(), gotEvents, err, want, sign, events)
					}
					if !sameRepresentation(got, general) || gotEvents != generalEvents || generalErr != nil {
						t.Fatalf("%s differs from admitted budgeted general path", op)
					}
				}
				check("QuantizeWithContext", general, generalEvents, generalErr)
				got, gotEvents, err := d.Quantize(f.target, mode)
				check("Quantize", got, gotEvents, err)
				got, gotEvents, err = d.QuantizeWithContext(f.target, ctx)
				check("QuantizeWithContext", got, gotEvents, err)
				if f.target == 0 {
					got, gotEvents, err = d.RoundToIntegral(mode)
					check("RoundToIntegral", got, gotEvents, err)
				}
				if d.isZero() {
					counts.zero++
				} else if d.slow != nil {
					counts.slow++
				} else {
					_, _, _, ok := inlineQuantize(d, f.target, mode)
					if !ok {
						counts.deferred++
					} else if d.words.hi == 0 && f.target > f.exponent {
						counts.oneWord++
					} else if d.words.hi != 0 && f.target > f.exponent {
						counts.twoWord++
					}
				}
				if refused {
					counts.exactRefusal++
				}
				if f.coefficient == "999995" && f.exponent == -2 && f.target == 0 && mode == TiesToEven {
					counts.carry++
				}
			}
		}
	}
	if counts.oneWord < 6000 || counts.twoWord < 400 || counts.deferred < 100 || counts.slow < 100 || counts.zero < 300 || counts.exactRefusal < 500 || counts.carry != 2 {
		t.Fatalf("vacuous class coverage: %+v", counts)
	}
	t.Logf("public class counts: %+v; %d independent fixtures", counts, len(fixtures))
}

// TestQuantizeOneWordBudgetAndAllocation checks the excluded context,
// positive-budget and zero cases, with independent hand-derived adjacent
// tariffs; successful default word paths retain zero allocations.
func TestQuantizeOneWordBudgetAndAllocation(t *testing.T) {
	for _, tc := range []struct {
		text   string
		target int32
		digits uint64
		work   uint64
	}{
		{"12345E-2", -1, 4, 9}, {"125E-2", -1, 2, 5},
		{"999995E-3", -2, 6, 12}, {"120E-2", -1, 2, 5},
		{"123E-2", -4, 5, 5}, {"12345E-2", -2, 5, 1},
	} {
		d := MustParse(tc.text)
		for _, budget := range []Budget{{MaxWork: tc.work - 1}, {MaxDigits: tc.digits - 1}, {MaxDigits: tc.digits, MaxWork: tc.work}, {MaxDigits: tc.digits}, {MaxWork: tc.work}} {
			got, events, err := d.QuantizeWithContext(tc.target, Context{}.WithBudget(budget))
			if budget == (Budget{}) || budget.MaxWork == tc.work || budget.MaxDigits == tc.digits && budget.MaxWork == 0 {
				quantizeAssertOracle(t, d, tc.target, TiesToEven, got, events, err)
			} else {
				quantizeAbort(t, got, events, err, "QuantizeWithContext", ErrInsufficientStorage)
			}
		}
	}
	input := MustParse("-9.99")
	for _, ctx := range []Context{
		{precision: 2}, {precision: 3, guarded: true, guards: ExponentGuards{Emin: -2, Emax: -1}},
		{traps: Inexact | Rounded}, {rounding: Exact},
	} {
		got, events, err := input.QuantizeWithContext(-1, ctx)
		want, wantEvents, wantErr := input.quantizeLimbs(-1, ctx, limits{MaxWork: math.MaxUint64}, "QuantizeWithContext")
		if !sameRepresentation(got, want) || events != wantEvents || (err == nil) != (wantErr == nil) || err != nil && err.Error() != wantErr.Error() {
			t.Fatalf("excluded context %+v changed result, conditions or error: %s %v %v; general %s %v %v", ctx, got, events, err, want, wantEvents, wantErr)
		}
	}
	for _, value := range []Decimal{New(0, math.MinInt32), New(1, math.MaxInt32)} {
		got, events, err := value.QuantizeWithContext(math.MinInt32, Context{}.WithBudget(Budget{MaxWork: 1, MaxDigits: 1}))
		if value.isZero() {
			if err != nil || events != 0 || !got.isZero() || got.exponent() != math.MinInt32 || got.negative() || !got.validRepresentation() {
				t.Fatal("budgeted zero cohort changed")
			}
		} else {
			quantizeAbort(t, got, events, err, "QuantizeWithContext", ErrInsufficientStorage)
		}
	}
	for mode := TiesToEven; mode <= Exact; mode++ {
		text := "-12345E-2"
		if mode == Exact {
			text = "-12000E-2"
		}
		d := MustParse(text)
		for _, integral := range []bool{false, true} {
			target := int32(-1)
			if integral {
				target = 0
			}
			call := func() (Decimal, Conditions, error) {
				if integral {
					return d.RoundToIntegral(mode)
				}
				return d.Quantize(target, mode)
			}
			got, events, err := call()
			quantizeAssertOracle(t, d, target, mode, got, events, err)
			allocs := testing.AllocsPerRun(100, func() {
				var callErr error
				quantizeResourceSink, _, callErr = call()
				if callErr != nil {
					panic(callErr)
				}
			})
			if allocs != 0 || !sameRepresentation(quantizeResourceSink, got) {
				t.Fatalf("word public path mode%v integral%v used %v allocations or changed result", mode, integral, allocs)
			}
		}
	}
}

func TestQuantizeEntryPointsAgree(t *testing.T) {
	got, conditions, err := MustParse("1.245").Quantize(-2, TiesToEven)
	if err != nil || got.coefficientDigits() != "124" || got.exponent() != -2 || conditions != Inexact|Rounded|Decreased {
		t.Errorf("direct tie: coefficient %s exponent %d conditions %v error %v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
	got, conditions, err = MustParse("2.5").RoundToIntegral(TowardZero)
	if err != nil || got.coefficientDigits() != "2" || got.exponent() != 0 || conditions != Inexact|Rounded|Decreased {
		t.Errorf("integral: coefficient %s exponent %d conditions %v error %v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
	ctx := Context{}
	got, conditions, err = MustParse("12E+2").QuantizeWithContext(-2, ctx.WithBudget(Budget{MaxDigits: 6, MaxWork: 5}))
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) {
		t.Errorf("growth work cap: result %+v conditions %v error %v", got, conditions, err)
	}
}

func TestQuantizeExactTargetVector(t *testing.T) {
	got, conditions, err := MustParse("1.234").Quantize(-2, TiesToEven)
	if err != nil || got.coefficientDigits() != "123" || got.exponent() != -2 || got.negative() || conditions != Inexact|Rounded|Decreased {
		t.Fatalf("1.234 at -2: coefficient %s e%d sign%v conditions %v error %v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
	}
}

func TestQuantizeAndIntegralSharedOwnership(t *testing.T) {
	value := MustParse(strings.Repeat("739182645", 5) + "E-1")
	copyValue := value
	integralGrowth := MustParse(strings.Repeat("739182645", 5) + "E+1")
	copyGrowth := integralGrowth
	if value.slow == nil || len(value.slow.limbs) == 0 || integralGrowth.slow == nil || len(integralGrowth.slow.limbs) == 0 {
		t.Fatal("ownership fixture must use a slow holder")
	}
	before, beforeGrowth := slices.Clone(value.slow.limbs), slices.Clone(integralGrowth.slow.limbs)
	ctx := quantizeTestContext(t, 0, TiesToEven, nil, 0)
	for _, tc := range []struct {
		name   string
		input  Decimal
		target int32
		call   func() (Decimal, Conditions, error)
	}{
		{"direct Quantize growth", value, -2, func() (Decimal, Conditions, error) { return value.Quantize(-2, TiesToEven) }},
		{"budgeted Quantize growth", value, -2, func() (Decimal, Conditions, error) {
			return copyValue.QuantizeWithContext(-2, ctx.WithBudget(Budget{MaxDigits: 46}))
		}},
		{"direct Quantize shrink", value, 0, func() (Decimal, Conditions, error) { return value.Quantize(0, TiesToEven) }},
		{"budgeted Quantize shrink", value, 0, func() (Decimal, Conditions, error) {
			return copyValue.QuantizeWithContext(0, ctx.WithBudget(Budget{MaxDigits: 45}))
		}},
		{"direct integral shrink", value, 0, func() (Decimal, Conditions, error) { return value.RoundToIntegral(TiesToEven) }},
		{"budgeted integral shrink", value, 0, func() (Decimal, Conditions, error) {
			return copyValue.RoundToIntegralWithContext(ctx.WithBudget(Budget{MaxDigits: 45}))
		}},
		{"direct integral growth", integralGrowth, 0, func() (Decimal, Conditions, error) { return integralGrowth.RoundToIntegral(TiesToEven) }},
		{"budgeted integral growth", integralGrowth, 0, func() (Decimal, Conditions, error) {
			return copyGrowth.RoundToIntegralWithContext(ctx.WithBudget(Budget{MaxDigits: 46}))
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			quantizeAssertOracle(t, tc.input, tc.target, TiesToEven, got, conditions, err)
			if got.slow == nil || got.slow == tc.input.slow || len(got.slow.limbs) == 0 || &got.slow.limbs[0] == &tc.input.slow.limbs[0] {
				t.Fatal("changed slow result reuses source coefficient storage")
			}
		})
	}
	for _, tc := range []struct {
		name string
		call func() (Decimal, Conditions, error)
	}{
		{"Quantize refusal", func() (Decimal, Conditions, error) {
			return copyValue.QuantizeWithContext(-2, ctx.WithBudget(Budget{MaxDigits: 1}))
		}},
		{"integral shrink refusal", func() (Decimal, Conditions, error) {
			return copyValue.RoundToIntegralWithContext(ctx.WithBudget(Budget{MaxDigits: 1}))
		}},
		{"integral growth refusal", func() (Decimal, Conditions, error) {
			return copyGrowth.RoundToIntegralWithContext(ctx.WithBudget(Budget{MaxDigits: 1}))
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("refusal published result: %+v, %v, %v", got, conditions, err)
			}
		})
	}
	if value.slow != copyValue.slow || !slices.Equal(value.slow.limbs, before) || !slices.Equal(copyValue.slow.limbs, before) {
		t.Fatal("direct or budgeted target operation changed source or shallow copy")
	}
	if integralGrowth.slow != copyGrowth.slow || !slices.Equal(integralGrowth.slow.limbs, beforeGrowth) || !slices.Equal(copyGrowth.slow.limbs, beforeGrowth) {
		t.Fatal("integral growth changed source or shallow copy")
	}
}

func TestQuantizeAndIntegralLeaveContextUnchanged(t *testing.T) {
	ctx := quantizeTestContext(t, 0, TiesAwayFromZero, nil, Rounded)
	before := ctx
	for _, tc := range []struct {
		name       string
		direct     func() (Decimal, Conditions, error)
		short      func() (Decimal, Conditions, error)
		zeroBudget func() (Decimal, Conditions, error)
		limited    func() (Decimal, Conditions, error)
		even, away string
		exponent   int32
		limitOp    string
	}{
		{"Quantize", func() (Decimal, Conditions, error) { return MustParse("1.245").Quantize(-2, TiesToEven) },
			func() (Decimal, Conditions, error) { return MustParse("1.245").QuantizeWithContext(-2, ctx) },
			func() (Decimal, Conditions, error) {
				return MustParse("1.245").QuantizeWithContext(-2, ctx.WithBudget(Budget{}))
			},
			func() (Decimal, Conditions, error) {
				return MustParse("1.245").QuantizeWithContext(-2, ctx.WithBudget(Budget{MaxWork: 3}))
			},
			"124", "125", -2, "QuantizeWithContext"},
		{"RoundToIntegral", func() (Decimal, Conditions, error) { return MustParse("2.5").RoundToIntegral(TiesToEven) },
			func() (Decimal, Conditions, error) { return MustParse("2.5").RoundToIntegralWithContext(ctx) },
			func() (Decimal, Conditions, error) {
				return MustParse("2.5").RoundToIntegralWithContext(ctx.WithBudget(Budget{}))
			},
			func() (Decimal, Conditions, error) {
				return MustParse("2.5").RoundToIntegralWithContext(ctx.WithBudget(Budget{MaxWork: 1}))
			},
			"2", "3", 0, "RoundToIntegralWithContext"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			checkDirect := func() {
				t.Helper()
				got, conditions, err := tc.direct()
				if err != nil || got.coefficientDigits() != tc.even || got.exponent() != tc.exponent || conditions != Inexact|Rounded|Decreased {
					t.Fatalf("direct policy: %s e%d conditions%v error%v", got.coefficientDigits(), got.exponent(), conditions, err)
				}
			}
			checkContext := func(call func() (Decimal, Conditions, error), method string) {
				t.Helper()
				got, conditions, err := call()
				var trapped *Error
				if got.coefficientDigits() != tc.away || got.exponent() != tc.exponent || conditions != Inexact|Increased || !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Op != method || trapped.Condition != Rounded || !errors.Is(err, ErrRounded) {
					t.Fatalf("context policy %s: %s e%d conditions%v error%v", method, got.coefficientDigits(), got.exponent(), conditions, err)
				}
			}
			checkDirect()
			checkContext(tc.short, tc.name+"WithContext")
			got, conditions, err := tc.limited()
			quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, tc.limitOp)
			checkContext(tc.zeroBudget, tc.limitOp)
			checkDirect()
			checkContext(tc.short, tc.name+"WithContext")
		})
	}
	if ctx != before {
		t.Fatal("interleaved target calls changed explicit context")
	}
}

func TestRoundToIntegralGuardFitAndNoUnderflow(t *testing.T) {
	excluded := quantizeTestContext(t, 2, TiesToEven, &ExponentGuards{Emin: 2, Emax: 5}, Underflow)
	got, conditions, err := One().RoundToIntegralWithContext(excluded)
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "RoundToIntegralWithContext")
	tooSmall := quantizeTestContext(t, 1, TiesToEven, nil, Underflow)
	got, conditions, err = MustParse("9.9").RoundToIntegralWithContext(tooSmall)
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "RoundToIntegralWithContext")
	guarded := quantizeTestContext(t, 3, TiesToEven, &ExponentGuards{Emin: 2, Emax: 3}, Underflow)
	input := MustParse("1.4")
	for _, tc := range []struct {
		name string
		call func() (Decimal, Conditions, error)
	}{
		{"Quantize", func() (Decimal, Conditions, error) { return input.QuantizeWithContext(0, guarded) }},
		{"RoundToIntegral", func() (Decimal, Conditions, error) { return input.RoundToIntegralWithContext(guarded) }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			if err != nil || got.coefficientDigits() != "1" || got.exponent() != 0 || got.negative() || conditions != Subnormal|Inexact|Rounded|Decreased || conditions&Underflow != 0 {
				t.Fatalf("inexact guarded subnormal: %s e%d sign%v conditions%v error%v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
			}
		})
	}
}

func TestQuantizeAndIntegralExactRefusal(t *testing.T) {
	for _, tc := range []struct {
		name string
		call func() (Decimal, Conditions, error)
		op   string
	}{
		{"Quantize", func() (Decimal, Conditions, error) { return MustParse("1.234").Quantize(-2, Exact) }, "Quantize"},
		{"RoundToIntegral", func() (Decimal, Conditions, error) { return MustParse("2.5").RoundToIntegral(Exact) }, "RoundToIntegral"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			quantizeCheckAbort(t, got, conditions, err, ErrInexact, tc.op)
		})
	}
}

func quantizeTestContext(t *testing.T, precision uint32, mode RoundingMode, guards *ExponentGuards, traps Conditions) Context {
	t.Helper()
	ctx, err := NewContext(precision, mode, guards, traps)
	if err != nil {
		t.Fatal(err)
	}
	return ctx
}

func quantizeCheckAbort(t *testing.T, got Decimal, conditions Conditions, err error, code ErrorCode, op string) {
	t.Helper()
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, code) {
		t.Fatalf("%s abort: result %+v conditions %v error %v; want %v", op, got, conditions, err, code)
	}
	if code == ErrInexact {
		var trapped *Error
		if !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Op != op || trapped.Condition != Inexact {
			t.Fatalf("%s Exact identity: %v", op, err)
		}
		return
	}
	if code == ErrInvalidContext {
		var configuration *Error
		if !errors.As(err, &configuration) || configuration.Op != op || configuration.Condition != InvalidContext {
			t.Fatalf("%s invalid mode identity: %v", op, err)
		}
		return
	}
	var operation *Error
	wantCondition := InsufficientStorage
	if code == ErrInvalidOperation {
		wantCondition = InvalidOperation
	}
	if !errors.As(err, &operation) || operation.Op != op || operation.Condition != wantCondition {
		t.Fatalf("%s operation identity: %v", op, err)
	}
}

func TestQuantizeFormsAgree(t *testing.T) {
	ctx := quantizeTestContext(t, 0, TiesToEven, nil, 0)
	input := MustParse("1.245")
	for _, call := range []func() (Decimal, Conditions, error){
		func() (Decimal, Conditions, error) { return input.Quantize(-2, TiesToEven) },
		func() (Decimal, Conditions, error) { return input.QuantizeWithContext(-2, ctx) },
		func() (Decimal, Conditions, error) {
			return input.QuantizeWithContext(-2, ctx.WithBudget(Budget{}))
		},
	} {
		got, conditions, err := call()
		quantizeAssertOracle(t, input, -2, TiesToEven, got, conditions, err)
	}
	for _, call := range []func() (Decimal, Conditions, error){
		func() (Decimal, Conditions, error) { return input.RoundToIntegral(TiesToEven) },
		func() (Decimal, Conditions, error) { return input.RoundToIntegralWithContext(ctx) },
		func() (Decimal, Conditions, error) {
			return input.RoundToIntegralWithContext(ctx.WithBudget(Budget{}))
		},
	} {
		got, conditions, err := call()
		quantizeAssertOracle(t, input, 0, TiesToEven, got, conditions, err)
	}
	for _, tc := range []struct {
		op   string
		call func() (Decimal, Conditions, error)
	}{
		{"Quantize", func() (Decimal, Conditions, error) { return input.Quantize(-2, RoundingMode(255)) }},
		{"RoundToIntegral", func() (Decimal, Conditions, error) { return input.RoundToIntegral(RoundingMode(255)) }},
	} {
		got, conditions, err := tc.call()
		quantizeCheckAbort(t, got, conditions, err, ErrInvalidContext, tc.op)
	}
	trapping := quantizeTestContext(t, 0, TiesToEven, nil, Rounded)
	for _, tc := range []struct {
		op   string
		call func() (Decimal, Conditions, error)
	}{
		{"RoundToIntegralWithContext", func() (Decimal, Conditions, error) { return MustParse("2.5").RoundToIntegralWithContext(trapping) }},
		{"RoundToIntegralWithContext", func() (Decimal, Conditions, error) {
			return MustParse("2.5").RoundToIntegralWithContext(trapping.WithBudget(Budget{MaxDigits: 1, MaxWork: 3}))
		}},
	} {
		got, conditions, err := tc.call()
		var trapped *Error
		if got.coefficientDigits() != "2" || got.exponent() != 0 || conditions != Inexact|Decreased || !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Op != tc.op || trapped.Condition != Rounded || !errors.Is(err, ErrRounded) {
			t.Fatalf("%s trap: %s e%d conditions%v err%v", tc.op, got.coefficientDigits(), got.exponent(), conditions, err)
		}
	}
	got, conditions, err := MustParse("2.5").RoundToIntegral(Exact)
	quantizeCheckAbort(t, got, conditions, err, ErrInexact, "RoundToIntegral")
}

func TestQuantizeExactZeroOnly(t *testing.T) {
	for _, tc := range []struct {
		input  string
		target int32
		want   string
	}{
		{"1.000", -1, "10"},
		{"99.90", -1, "999"},
	} {
		got, conditions, err := MustParse(tc.input).Quantize(tc.target, Exact)
		if err != nil || got.coefficientDigits() != tc.want || got.exponent() != tc.target || conditions != Rounded {
			t.Fatalf("zero-only %s to %d: %s e%d conditions%v err%v", tc.input, tc.target, got.coefficientDigits(), got.exponent(), conditions, err)
		}
	}
	got, conditions, err := MustParse("1.001").Quantize(-1, Exact)
	quantizeCheckAbort(t, got, conditions, err, ErrInexact, "Quantize")
	got, conditions, err = MustParse("-0.000").Quantize(6, Exact)
	if err != nil || conditions != 0 || !got.isZero() || got.exponent() != 6 || got.negative() {
		t.Fatalf("signed input zero: %+v conditions%v err%v", got, conditions, err)
	}
	got, conditions, err = MustParse("-0.5").Quantize(0, TiesToEven)
	if err != nil || conditions != Inexact|Rounded|Increased || !got.isZero() || got.exponent() != 0 || got.negative() {
		t.Fatalf("negative tiny-to-zero: %+v conditions%v err%v", got, conditions, err)
	}
}

func TestQuantizeFullDiscardDigitBoundary(t *testing.T) {
	for _, tc := range []struct {
		input       string
		target      int32
		mode        RoundingMode
		coefficient string
		negative    bool
		direction   Conditions
	}{
		{"5", 1, TiesToEven, "0", false, Decreased},
		{"5", 1, TiesAwayFromZero, "1", false, Increased},
		{"-5", 1, TiesAwayFromZero, "1", true, Decreased},
		{"5", 2, TiesToEven, "0", false, Decreased},
		{"5", 2, AwayFromZero, "1", false, Increased},
	} {
		input := MustParse(tc.input)
		got, conditions, err := input.Quantize(tc.target, tc.mode)
		if err != nil || got.coefficientDigits() != tc.coefficient || got.exponent() != tc.target || got.negative() != tc.negative || conditions != Inexact|Rounded|tc.direction {
			t.Fatalf("full discard %s to %d mode%d: %s sign%v conditions%v err%v", tc.input, tc.target, tc.mode, got.coefficientDigits(), got.negative(), conditions, err)
		}
	}
	got, conditions, err := New(5, 0).Quantize(1, Exact)
	quantizeCheckAbort(t, got, conditions, err, ErrInexact, "Quantize")
}

func TestQuantizeCandidateFit(t *testing.T) {
	toward := quantizeTestContext(t, 2, TowardZero, nil, 0)
	got, conditions, err := MustParse("9.99").QuantizeWithContext(-1, toward)
	if err != nil || got.coefficientDigits() != "99" || got.exponent() != -1 || conditions != Inexact|Rounded|Decreased {
		t.Fatalf("valid target fit: %s e%d %v %v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
	for _, tc := range []struct {
		name string
		ctx  Context
	}{
		{"rounded coefficient", quantizeTestContext(t, 2, TiesToEven, nil, 0)},
		{"rounded adjusted exponent", quantizeTestContext(t, 3, TiesToEven, &ExponentGuards{Emin: -2, Emax: 0}, 0)},
		{"both", quantizeTestContext(t, 2, TiesToEven, &ExponentGuards{Emin: -1, Emax: 0}, 0)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := MustParse("9.99").QuantizeWithContext(-1, tc.ctx)
			quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
		})
	}
	ctx := quantizeTestContext(t, 2, TiesToEven, &ExponentGuards{Emin: 2, Emax: 5}, 0)
	got, conditions, err = One().RoundToIntegralWithContext(ctx)
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "RoundToIntegralWithContext")
	ctx = quantizeTestContext(t, 1, TiesToEven, nil, 0)
	got, conditions, err = MustParse("9.9").RoundToIntegralWithContext(ctx)
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "RoundToIntegralWithContext")
	ctx = quantizeTestContext(t, 3, TiesToEven, &ExponentGuards{Emin: -2, Emax: 2}, Subnormal|Rounded)
	got, conditions, err = New(0, 100).QuantizeWithContext(-4, ctx)
	if err != nil || conditions != 0 || !got.isZero() || got.exponent() != -4 || got.negative() {
		t.Fatalf("guarded valid target zero cohort: %+v conditions%v err%v", got, conditions, err)
	}
}

func TestQuantizeExactBeforeHypotheticalFit(t *testing.T) {
	input := MustParse("9.99")
	for _, ctx := range []Context{
		quantizeTestContext(t, 2, Exact, nil, 0),
		quantizeTestContext(t, 3, Exact, &ExponentGuards{Emin: -2, Emax: 0}, 0),
		quantizeTestContext(t, 2, Exact, &ExponentGuards{Emin: -1, Emax: 0}, 0),
	} {
		for _, cap := range []uint64{2, 3} {
			got, conditions, err := input.QuantizeWithContext(-1, ctx.WithBudget(Budget{MaxWork: cap}))
			want := ErrInsufficientStorage
			if cap == 3 {
				want = ErrInexact
			}
			quantizeCheckAbort(t, got, conditions, err, want, "QuantizeWithContext")
		}
	}
	ctx := quantizeTestContext(t, 2, Exact, nil, 0)
	for _, tc := range []struct {
		input  string
		target int32
	}{{"9.99", -2}, {"99.90", -1}} {
		got, conditions, err := MustParse(tc.input).QuantizeWithContext(tc.target, ctx)
		quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
	}
}

func TestQuantizeModeIsolation(t *testing.T) {
	input := MustParse("1.245")
	direct, directConditions, directErr := input.Quantize(-2, TiesToEven)
	ctx := quantizeTestContext(t, 0, TiesAwayFromZero, nil, 0)
	contextual, contextualConditions, contextualErr := input.QuantizeWithContext(-2, ctx)
	if directErr != nil || contextualErr != nil || direct.coefficientDigits() != "124" || contextual.coefficientDigits() != "125" || directConditions != Inexact|Rounded|Decreased || contextualConditions != Inexact|Rounded|Increased {
		t.Fatalf("mode isolation: %s/%v/%v versus %s/%v/%v", direct.coefficientDigits(), directConditions, directErr, contextual.coefficientDigits(), contextualConditions, contextualErr)
	}
	for _, tc := range []struct {
		input     string
		mode      RoundingMode
		want      string
		negative  bool
		direction Conditions
	}{{"2.5", TowardZero, "2", false, Decreased}, {"-2.5", TowardNegativeInfinity, "3", true, Decreased}} {
		value := MustParse(tc.input)
		got, conditions, err := value.RoundToIntegral(tc.mode)
		if err != nil || got.coefficientDigits() != tc.want || got.exponent() != 0 || got.negative() != tc.negative || conditions != Inexact|Rounded|tc.direction {
			t.Fatalf("integral mode %s: %s sign%v cond%v err%v", tc.input, got.coefficientDigits(), got.negative(), conditions, err)
		}
	}
}

func TestQuantizeSourceQualifiedGDA(t *testing.T) {
	// GDA extended/quantize.decTest SHA-256
	// bf320e26d5dc7596a669c606389e2227520390b4ce7daddf73593431f366900c.
	// The finite-only API replaces GDA NaN with an InvalidOperation error and
	// normalizes signed zero; the listed numeric and condition cases match.
	ctx := quantizeTestContext(t, 7, TiesAwayFromZero, &ExponentGuards{Emin: -999, Emax: 999}, 0)
	for _, tc := range []struct {
		id, input   string
		target      int32
		coefficient string
		conditions  Conditions
		invalid     bool
	}{
		{"quax545", "1E-1000", -999, "0", Inexact | Rounded | Decreased, false},
		{"quax550", "1E-998", -1005, "", 0, true},
		{"quax551", "1E-999", -1005, "1000000", 0, false},
		{"quax552", "1E-1000", -1005, "100000", Subnormal, false},
		{"quax553", "1E-999", -1006, "", 0, true},
		{"quax556", "1.666666E-1000", -1005, "166667", Subnormal | Inexact | Rounded | Increased, false},
		{"quax562", "1.666666E-1006", -1005, "0", Inexact | Rounded | Decreased, false},
	} {
		t.Run(tc.id, func(t *testing.T) {
			got, conditions, err := MustParse(tc.input).QuantizeWithContext(tc.target, ctx)
			if tc.invalid {
				quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
				return
			}
			if err != nil || got.coefficientDigits() != tc.coefficient || got.exponent() != tc.target || got.negative() || conditions != tc.conditions || conditions&Underflow != 0 {
				t.Fatalf("%s: coefficient %s e%d sign%v conditions%v err%v", tc.id, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
			}
		})
	}
}

func TestQuantizeTrapPartition(t *testing.T) {
	guards := &ExponentGuards{Emin: -999, Emax: 999}
	input := MustParse("1.666666E-1000")
	ctx := quantizeTestContext(t, 7, TiesAwayFromZero, guards, Inexact|Rounded|Subnormal|Underflow)
	got, conditions, err := input.QuantizeWithContext(-1005, ctx)
	var trapped *Error
	if got.coefficientDigits() != "166667" || got.exponent() != -1005 || conditions != Increased || !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Op != "QuantizeWithContext" || trapped.Condition != Inexact|Rounded|Subnormal {
		t.Fatalf("multi trap: %s e%d conditions%v err%v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
	for _, cause := range []ErrorCode{ErrInexact, ErrRounded, ErrSubnormal} {
		if !errors.Is(err, cause) {
			t.Fatalf("missing trap cause %v", cause)
		}
	}
	if errors.Is(err, ErrUnderflow) || errors.Is(err, ErrOverflow) || trapped.Unwrap() != nil {
		t.Fatalf("unexpected trap cause: %v", err)
	}
	ctx = quantizeTestContext(t, 7, TiesAwayFromZero, guards, Underflow)
	got, conditions, err = input.QuantizeWithContext(-1005, ctx)
	if err != nil || got.coefficientDigits() != "166667" || conditions != Inexact|Rounded|Subnormal|Increased {
		t.Fatalf("Underflow-only trap fired: %s conditions%v err%v", got.coefficientDigits(), conditions, err)
	}
	got, conditions, err = MustParse("1.666666E-1006").QuantizeWithContext(-1005, ctx)
	if err != nil || got.coefficientDigits() != "0" || got.exponent() != -1005 || got.negative() || conditions != Inexact|Rounded|Decreased {
		t.Fatalf("tiny zero flags: %s e%d sign%v conditions%v err%v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
	}
}

func TestQuantizeSharedOwnership(t *testing.T) {
	value := MustParse(strings.Repeat("739182645", 112))
	copyValue := value
	before := slices.Clone(value.slow.limbs)
	for _, tc := range []struct {
		target int32
		call   func() (Decimal, Conditions, error)
	}{
		{-1, func() (Decimal, Conditions, error) { return value.Quantize(-1, TiesToEven) }},
		{1, func() (Decimal, Conditions, error) { return copyValue.Quantize(1, TiesToEven) }},
		{-1, func() (Decimal, Conditions, error) {
			return value.QuantizeWithContext(-1, Context{}.WithBudget(Budget{MaxDigits: 1009, MaxWork: 1009}))
		}},
	} {
		got, conditions, err := tc.call()
		quantizeAssertOracle(t, value, tc.target, TiesToEven, got, conditions, err)
		if got.slow == value.slow {
			t.Fatal("changed result reused source slow holder")
		}
	}
	got, conditions, err := copyValue.QuantizeWithContext(-1, Context{}.WithBudget(Budget{MaxDigits: 1}))
	quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
	if value.slow != copyValue.slow || !slices.Equal(value.slow.limbs, before) || !slices.Equal(copyValue.slow.limbs, before) {
		t.Fatal("Quantize changed a source slow holder or shallow copy")
	}
}

func TestQuantizeUsesOnlyItsOwnModeAndBudget(t *testing.T) {
	value := MustParse("1.245")
	even, evenConditions, evenErr := value.Quantize(-2, TiesToEven)
	awayContext := quantizeTestContext(t, 0, TiesAwayFromZero, nil, Rounded)
	away, awayConditions, awayErr := value.QuantizeWithContext(-2, awayContext)
	refused, refusedConditions, refusedErr := value.QuantizeWithContext(-2, awayContext.WithBudget(Budget{MaxWork: 3}))
	again, againConditions, againErr := value.Quantize(-2, TiesToEven)
	if evenErr != nil || even.coefficientDigits() != "124" || evenConditions != Inexact|Rounded|Decreased || againErr != nil || again.coefficientDigits() != "124" || againConditions != evenConditions {
		t.Fatalf("direct policy changed across calls: %s/%v/%v then %s/%v/%v", even.coefficientDigits(), evenConditions, evenErr, again.coefficientDigits(), againConditions, againErr)
	}
	if away.coefficientDigits() != "125" || awayConditions != Inexact|Increased || !errors.Is(awayErr, ErrRounded) {
		t.Fatalf("context policy: %s/%v/%v", away.coefficientDigits(), awayConditions, awayErr)
	}
	quantizeCheckAbort(t, refused, refusedConditions, refusedErr, ErrInsufficientStorage, "QuantizeWithContext")
}

func TestQuantizeFivePathCharges(t *testing.T) {
	ctx := Context{}
	for _, tc := range []struct {
		name, input        string
		target             int32
		mode               RoundingMode
		base, work, digits uint64
	}{
		{"zero", "-0.000", 6, TiesToEven, 1, 1, 1},
		{"equal", "1.23", -2, TiesToEven, 1, 1, 3},
		{"growth", "12E+2", -2, TiesToEven, 1, 6, 6},
		{"existing discard", "1.234", -2, TiesToEven, 4, 7, 3},
		{"virtual gap", "5", 2, AwayFromZero, 1, 2, 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			value := MustParse(tc.input)
			modeContext := quantizeTestContext(t, 0, tc.mode, nil, 0)
			caps := []uint64{tc.base, tc.work}
			if tc.base > 1 {
				caps = append(caps, tc.base-1)
			}
			if tc.work > 1 {
				caps = append(caps, tc.work-1)
			}
			for _, cap := range caps {
				got, conditions, err := value.QuantizeWithContext(tc.target, modeContext.WithBudget(Budget{MaxWork: cap}))
				if cap < tc.work {
					quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
				} else {
					quantizeAssertOracle(t, value, tc.target, tc.mode, got, conditions, err)
				}
			}
			if tc.digits > 1 {
				got, conditions, err := value.QuantizeWithContext(tc.target, modeContext.WithBudget(Budget{MaxDigits: tc.digits - 1, MaxWork: tc.work}))
				quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
			}
			got, conditions, err := value.QuantizeWithContext(tc.target, modeContext.WithBudget(Budget{MaxDigits: tc.digits, MaxWork: tc.work}))
			quantizeAssertOracle(t, value, tc.target, tc.mode, got, conditions, err)
			got, conditions, err = value.QuantizeWithContext(tc.target, modeContext.WithBudget(Budget{}))
			quantizeAssertOracle(t, value, tc.target, tc.mode, got, conditions, err)
			if tc.mode == TiesToEven {
				got, conditions, err = value.QuantizeWithContext(tc.target, ctx)
				quantizeAssertOracle(t, value, tc.target, tc.mode, got, conditions, err)
			}
		})
	}
}

func TestQuantizePrecedenceAndOneBuffer(t *testing.T) {
	guarded := quantizeTestContext(t, 3, TiesToEven, &ExponentGuards{Emin: -2, Emax: 0}, Inexact|Rounded)
	got, conditions, err := MustParse("9.99").QuantizeWithContext(-5, guarded.WithBudget(Budget{MaxWork: 1}))
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
	got, conditions, err = New(0, -100).QuantizeWithContext(-5, guarded.WithBudget(Budget{MaxWork: 1}))
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
	got, conditions, err = MustParse("9.99").QuantizeWithContext(-1, guarded.WithBudget(Budget{MaxDigits: 1, MaxWork: 3}))
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
	ctx := quantizeTestContext(t, 0, TiesToEven, nil, Inexact|Rounded)
	value := MustParse("1.234")
	got, conditions, err = value.QuantizeWithContext(-2, ctx.WithBudget(Budget{MaxDigits: 2, MaxWork: 7}))
	quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
	got, conditions, err = value.QuantizeWithContext(-2, ctx.WithBudget(Budget{MaxDigits: 3, MaxWork: 6}))
	quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
	got, conditions, err = value.QuantizeWithContext(-2, ctx.WithBudget(Budget{MaxDigits: 3, MaxWork: 7}))
	var trapped *Error
	if got.coefficientDigits() != "123" || got.exponent() != -2 || conditions != Decreased || !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Condition != Inexact|Rounded {
		t.Fatalf("finite trap after quotas: %s e%d conditions%v err%v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
	near := quantizeCount{hi: 1}
	if quantizeAdmitted(math.MaxUint64, near) || !quantizeAdmitted(0, near) {
		t.Fatal("wide logical count imposed a hidden uint64 cap")
	}
	_, err = quantizePhysicalCount(quantizeCount{hi: 9}, "QuantizeWithContext")
	if !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("oversize physical count: %v", err)
	}
	_, err = quantizePhysicalCount(near, "QuantizeWithContext")
	if strconv.IntSize == 32 && !errors.Is(err, ErrInsufficientStorage) || strconv.IntSize == 64 && err != nil {
		t.Fatalf("architecture physical count: %v", err)
	}
}

func TestQuantizeExactCapCollision(t *testing.T) {
	for _, ctx := range []Context{
		quantizeTestContext(t, 2, Exact, nil, 0),
		quantizeTestContext(t, 3, Exact, &ExponentGuards{Emin: -2, Emax: 0}, 0),
	} {
		for _, cap := range []uint64{2, 3} {
			got, conditions, err := MustParse("9.99").QuantizeWithContext(-1, ctx.WithBudget(Budget{MaxWork: cap}))
			want := ErrInsufficientStorage
			if cap == 3 {
				want = ErrInexact
			}
			quantizeCheckAbort(t, got, conditions, err, want, "QuantizeWithContext")
		}
	}
}

func TestQuantizeTypedAborts(t *testing.T) {
	got, conditions, err := One().RoundToIntegral(RoundingMode(255))
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidContext, "RoundToIntegral")
	ctx := quantizeTestContext(t, 2, TiesToEven, &ExponentGuards{Emin: 2, Emax: 3}, 0)
	got, conditions, err = One().RoundToIntegralWithContext(ctx)
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "RoundToIntegralWithContext")
	got, conditions, err = MustParse("1.234").QuantizeWithContext(-2, Context{}.WithBudget(Budget{MaxWork: 3}))
	quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
	got, conditions, err = MustParse("1.234").Quantize(-2, Exact)
	quantizeCheckAbort(t, got, conditions, err, ErrInexact, "Quantize")
	_, err = quantizePhysicalCount(quantizeCount{hi: 9}, "QuantizeWithContext")
	var operation *Error
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != "QuantizeWithContext" || operation.Condition != InsufficientStorage {
		t.Fatalf("physical refusal identity: %v", err)
	}
}

func TestQuantizeTrapVersusDomain(t *testing.T) {
	ctx := quantizeTestContext(t, 7, TiesAwayFromZero, &ExponentGuards{Emin: -999, Emax: 999}, Inexact|Rounded)
	value := MustParse("1.666666E-1000")
	got, conditions, err := value.QuantizeWithContext(-1005, ctx)
	var trapped *Error
	if got.coefficientDigits() != "166667" || got.exponent() != -1005 || conditions != Subnormal|Increased || !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Condition != Inexact|Rounded {
		t.Fatalf("finite trap: %s e%d conditions%v err%v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
	got, conditions, err = value.QuantizeWithContext(-1006, ctx)
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
}

func TestQuantizeBoundaryLengthsAndExtremeGaps(t *testing.T) {
	for _, width := range []int{38, 39, 40, 1000, 10000} {
		value := MustParse(strings.Repeat("739182645", width/9) + strings.Repeat("7", width%9))
		for _, target := range []int32{-1, 1} {
			got, conditions, err := value.Quantize(target, TiesToEven)
			quantizeAssertOracle(t, value, target, TiesToEven, got, conditions, err)
		}
	}
	for _, tc := range []struct {
		input       Decimal
		target      int32
		mode        RoundingMode
		coefficient string
		negative    bool
		direction   Conditions
	}{
		{New(5, math.MinInt32), math.MaxInt32, TiesToEven, "0", false, Decreased},
		{New(5, math.MinInt32), math.MaxInt32, AwayFromZero, "1", false, Increased},
		{New(-5, math.MinInt32), math.MaxInt32, TowardNegativeInfinity, "1", true, Decreased},
	} {
		got, conditions, err := tc.input.Quantize(tc.target, tc.mode)
		if err != nil || got.coefficientDigits() != tc.coefficient || got.exponent() != tc.target || got.negative() != tc.negative || conditions != Inexact|Rounded|tc.direction {
			t.Fatalf("full int32 gap: %s e%d sign%v conditions%v err%v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
		}
	}
	got, conditions, err := New(12, math.MaxInt32).QuantizeWithContext(math.MinInt32, Context{}.WithBudget(Budget{MaxDigits: 1, MaxWork: 1}))
	quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
	got, conditions, err = New(0, math.MinInt32).Quantize(math.MaxInt32, TiesToEven)
	if err != nil || conditions != 0 || !got.isZero() || got.exponent() != math.MaxInt32 || got.negative() {
		t.Fatalf("zero extreme cohort: %+v conditions%v err%v", got, conditions, err)
	}
}

func TestQuantizeCarrierBoundaryGrowthShrink(t *testing.T) {
	for _, width := range []int{38, 39, 40, 1000, 10000} {
		for _, sign := range []string{"", "-"} {
			input := MustParse(sign + "1" + strings.Repeat("0", width-1))
			copyInput := input
			var before []uint32
			if input.slow != nil {
				before = slices.Clone(input.slow.limbs)
			}
			for _, tc := range []struct {
				name, coefficient string
				target            int32
				n, base, work     uint64
				conditions        Conditions
			}{
				{"growth", "1" + strings.Repeat("0", width), -1, uint64(width + 1), 1, uint64(width + 1), 0},
				{"shrink", "1" + strings.Repeat("0", width-2), 1, uint64(width - 1), uint64(width), uint64(2*width - 1), Rounded},
			} {
				t.Run(strconv.Itoa(width)+"/"+sign+tc.name, func(t *testing.T) {
					for _, budget := range []Budget{
						{MaxDigits: tc.n - 1, MaxWork: tc.work},
						{MaxDigits: tc.n, MaxWork: tc.work - 1},
					} {
						got, conditions, err := input.QuantizeWithContext(tc.target, Context{}.WithBudget(budget))
						quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
					}
					if tc.base > 1 {
						got, conditions, err := input.QuantizeWithContext(tc.target, Context{}.WithBudget(Budget{MaxDigits: tc.n, MaxWork: tc.base - 1}))
						quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
					}
					got, conditions, err := input.QuantizeWithContext(tc.target, Context{}.WithBudget(Budget{MaxDigits: tc.n, MaxWork: tc.work}))
					quantizeAssertOracle(t, input, tc.target, TiesToEven, got, conditions, err)
					if got.coefficientDigits() != tc.coefficient || conditions != tc.conditions || got.negative() != input.negative() {
						t.Fatalf("boundary cohort: %s sign%v conditions%v, want %s sign%v conditions%v", got.coefficientDigits(), got.negative(), conditions, tc.coefficient, input.negative(), tc.conditions)
					}
					from := quantizeOracleRat(input.coefficientDigits(), input.exponent(), input.negative())
					to := quantizeOracleRat(got.coefficientDigits(), got.exponent(), got.negative())
					if from.Cmp(to) != 0 {
						t.Fatalf("exact boundary value changed: %s to %s", from, to)
					}
					if got.slow != nil && input.slow != nil && got.slow == input.slow {
						t.Fatal("changed result reused source slow holder")
					}
				})
			}
			if input.slow != copyInput.slow || input.coefficientDigits() != copyInput.coefficientDigits() || input.negative() != copyInput.negative() || input.exponent() != copyInput.exponent() {
				t.Fatal("boundary call changed input or shallow copy")
			}
			if input.slow != nil && !slices.Equal(input.slow.limbs, before) {
				t.Fatal("boundary call changed source limbs")
			}
		}
	}
}

func TestQuantizeExtremeVirtualGap(t *testing.T) {
	for _, negative := range []bool{false, true} {
		value := New(5, math.MinInt32)
		if negative {
			value = New(-5, math.MinInt32)
		}
		for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity} {
			up := mode == AwayFromZero || mode == TowardPositiveInfinity && !negative || mode == TowardNegativeInfinity && negative
			want := "0"
			if up {
				want = "1"
			}
			// A zero result lies on the opposite side of the exact
			// value from its sign; a one-quantum result lies beyond it.
			direction := Decreased
			if up {
				direction = Increased
				if negative {
					direction = Decreased
				}
			} else if negative {
				direction = Increased
			}
			ctx := quantizeTestContext(t, 0, mode, nil, 0)
			for _, cap := range []uint64{0, 1, 2} {
				got, conditions, err := value.QuantizeWithContext(math.MaxInt32, ctx.WithBudget(Budget{MaxDigits: 1, MaxWork: cap}))
				if cap == 1 {
					quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
					continue
				}
				if err != nil || got.coefficientDigits() != want || got.exponent() != math.MaxInt32 || got.negative() != (negative && up) || conditions != Inexact|Rounded|direction {
					t.Fatalf("extreme gap mode%d neg%v cap%d: %s e%d sign%v conditions%v err%v", mode, negative, cap, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
				}
			}
		}
		ctx := quantizeTestContext(t, 0, Exact, nil, 0)
		for _, cap := range []uint64{0, 1} {
			got, conditions, err := value.QuantizeWithContext(math.MaxInt32, ctx.WithBudget(Budget{MaxWork: cap}))
			quantizeCheckAbort(t, got, conditions, err, ErrInexact, "QuantizeWithContext")
		}
	}
}

func TestQuantizeExtremeGrowthQuota(t *testing.T) {
	for _, tc := range []struct {
		value  Decimal
		target int32
		n      uint64
	}{
		{New(5, math.MaxInt32), math.MinInt32, 4_294_967_296},
		{New(7, 1_000_000_000), 0, 1_000_000_001},
	} {
		for _, budget := range []Budget{
			{MaxDigits: 10_000},
			{MaxWork: 10_000},
			{MaxDigits: 10_000, MaxWork: 10_000},
		} {
			var got Decimal
			var conditions Conditions
			var err error
			allocs := testing.AllocsPerRun(100, func() {
				got, conditions, err = tc.value.QuantizeWithContext(tc.target, Context{}.WithBudget(budget))
			})
			quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
			if allocs > 1 {
				t.Fatalf("extreme growth N%d quota %+v allocated %.0f times", tc.n, budget, allocs)
			}
		}
	}
}

func TestQuantizeCarryAcrossLimb(t *testing.T) {
	for _, retained := range []int{8, 9, 18, 37, 38, 39, 1000, 10000} {
		input := MustParse(strings.Repeat("9", retained) + "5E-1")
		got, conditions, err := input.Quantize(0, TiesAwayFromZero)
		quantizeAssertOracle(t, input, 0, TiesAwayFromZero, got, conditions, err)
		if got.coefficientDigits() != "1"+strings.Repeat("0", retained) || got.exponent() != 0 {
			t.Fatalf("all-nines carry %d: coefficient length %d exponent %d", retained, len(got.coefficientDigits()), got.exponent())
		}
	}
}

func TestQuantizeRefusalAllocation(t *testing.T) {
	value := MustParse(strings.Repeat("739182645", 1111) + "7")
	if value.slow == nil || len(value.coefficientDigits()) != 10000 {
		t.Fatal("allocation fixture needs a 10,000-digit slow coefficient")
	}
	for _, tc := range []struct {
		name   string
		target int32
		budget Budget
	}{
		{"precharge", 1, Budget{MaxWork: 9999}},
		{"final digits", -1, Budget{MaxDigits: 10000}},
		{"final work", -1, Budget{MaxDigits: 10001, MaxWork: 10000}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var got Decimal
			var conditions Conditions
			var err error
			allocs := testing.AllocsPerRun(100, func() {
				got, conditions, err = value.QuantizeWithContext(tc.target, Context{}.WithBudget(tc.budget))
			})
			quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
			if allocs > 1 {
				t.Fatalf("%s allocated %.0f times per refusal; want only the typed error", tc.name, allocs)
			}
		})
	}
}

var quantizeResultSink Decimal

func TestQuantizeOneBufferGrowthAllocation(t *testing.T) {
	value := MustParse(strings.Repeat("739182645", 1111) + "7")
	allocs := testing.AllocsPerRun(100, func() {
		var conditions Conditions
		var err error
		quantizeResultSink, conditions, err = value.Quantize(-1, TiesToEven)
		if err != nil || conditions != 0 {
			panic("unexpected admitted growth outcome")
		}
	})
	if allocs > 2 {
		t.Fatalf("admitted slow growth allocated %.0f times; want one limb slice and holder", allocs)
	}
	if len(quantizeResultSink.coefficientDigits()) != 10001 || quantizeResultSink.exponent() != -1 {
		t.Fatalf("growth sink cohort: %d digits e%d", len(quantizeResultSink.coefficientDigits()), quantizeResultSink.exponent())
	}
}

func TestQuantizeConcurrentReaders(t *testing.T) {
	value := MustParse(strings.Repeat("123456789", 5) + "E-4")
	copyValue := value
	ctx := quantizeTestContext(t, 0, TiesToEven, nil, Inexact|Rounded)
	budget := Budget{MaxDigits: 46, MaxWork: 100}
	before, ctxBefore := slices.Clone(value.slow.limbs), ctx
	type operation struct {
		name, method        string
		target              int32
		contextual, refuse  bool
		call                func() (Decimal, Conditions, error)
		coefficient         string
		negative            bool
		conditions, trapped Conditions
	}
	ops := []operation{
		{name: "direct growth", method: "Quantize", target: -5, call: func() (Decimal, Conditions, error) { return value.Quantize(-5, TiesToEven) }},
		{name: "context shrink", method: "QuantizeWithContext", target: -3, contextual: true, call: func() (Decimal, Conditions, error) { return copyValue.QuantizeWithContext(-3, ctx) }},
		{name: "budgeted growth", method: "QuantizeWithContext", target: -5, contextual: true, call: func() (Decimal, Conditions, error) { return copyValue.QuantizeWithContext(-5, ctx.WithBudget(budget)) }},
		{name: "budgeted refusal", method: "QuantizeWithContext", target: -5, contextual: true, refuse: true, call: func() (Decimal, Conditions, error) {
			return copyValue.QuantizeWithContext(-5, ctx.WithBudget(Budget{MaxDigits: 1}))
		}},
		{name: "direct integral", method: "RoundToIntegral", target: 0, call: func() (Decimal, Conditions, error) { return value.RoundToIntegral(TiesToEven) }},
		{name: "context integral", method: "RoundToIntegralWithContext", target: 0, contextual: true, call: func() (Decimal, Conditions, error) { return copyValue.RoundToIntegralWithContext(ctx) }},
		{name: "budgeted integral", method: "RoundToIntegralWithContext", target: 0, contextual: true, call: func() (Decimal, Conditions, error) {
			return copyValue.RoundToIntegralWithContext(ctx.WithBudget(budget))
		}},
	}
	for i := range ops {
		entry := &ops[i]
		entry.coefficient, entry.negative, entry.conditions = quantizeOracle(value, entry.target, TiesToEven)
		if entry.contextual {
			entry.trapped = entry.conditions & ctx.traps
			entry.conditions &^= ctx.traps
		}
	}
	start := make(chan struct{})
	var group sync.WaitGroup
	for range 12 {
		group.Go(func() {
			<-start
			for range 50 {
				for _, tc := range ops {
					got, conditions, err := tc.call()
					if tc.refuse {
						var operation *Error
						if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != tc.method {
							t.Errorf("%s: result %+v conditions %v error %v", tc.name, got, conditions, err)
							return
						}
						continue
					}
					if got.coefficientDigits() != tc.coefficient || got.exponent() != tc.target || got.negative() != tc.negative || conditions != tc.conditions {
						t.Errorf("%s: coefficient %s e%d sign%v conditions%v", tc.name, got.coefficientDigits(), got.exponent(), got.negative(), conditions)
						return
					}
					var condition *Error
					if tc.trapped == 0 && err != nil || tc.trapped != 0 && (!errors.As(err, &condition) || condition.Code != 0 || condition.Op != tc.method || condition.Condition != tc.trapped || !errors.Is(err, ErrInexact)) {
						t.Errorf("%s: error %v, trapped %v", tc.name, err, tc.trapped)
						return
					}
				}
			}
		})
	}
	close(start)
	group.Wait()
	if value.slow != copyValue.slow || !slices.Equal(value.slow.limbs, before) || ctx != ctxBefore {
		t.Fatal("concurrent Quantize changed source or context")
	}
}

// quantizeOracle uses only test-side arbitrary-precision integer arithmetic.
// It reads the fixture input, never a coefficient produced by Quantize. The
// direction bit is the sign of the oracle's own rounded value minus
// the exact input, decided by math/big.Rat comparison.
func quantizeOracle(input Decimal, target int32, mode RoundingMode) (string, bool, Conditions) {
	magnitude, ok := new(big.Int).SetString(input.coefficientDigits(), 10)
	if !ok {
		panic("invalid fixture coefficient")
	}
	if magnitude.Sign() == 0 {
		return "0", false, 0
	}
	negative := input.negative()
	difference := int64(input.exponent()) - int64(target)
	if difference >= 0 {
		power := new(big.Int).Exp(big.NewInt(10), big.NewInt(difference), nil)
		return magnitude.Mul(magnitude, power).String(), negative, 0
	}
	divisor := new(big.Int).Exp(big.NewInt(10), big.NewInt(-difference), nil)
	quotient, remainder := new(big.Int), new(big.Int)
	quotient.QuoRem(magnitude, divisor, remainder)
	events := Rounded
	if remainder.Sign() != 0 {
		events |= Inexact
	}
	double := new(big.Int).Lsh(remainder, 1)
	half := double.Cmp(divisor)
	up := false
	switch mode {
	case TiesToEven:
		up = half > 0 || half == 0 && quotient.Bit(0) == 1
	case TiesAwayFromZero:
		up = half >= 0
	case TiesTowardZero:
		up = half > 0
	case TowardZero, Exact:
	case AwayFromZero:
		up = remainder.Sign() != 0
	case TowardPositiveInfinity:
		up = remainder.Sign() != 0 && !negative
	case TowardNegativeInfinity:
		up = remainder.Sign() != 0 && negative
	}
	if up {
		quotient.Add(quotient, big.NewInt(1))
	}
	if quotient.Sign() == 0 {
		negative = false
	}
	if events&Inexact != 0 {
		rounded := quantizeOracleRat(quotient.String(), target, negative)
		events |= oracleDirection(rounded, quantizeOracleRat(input.coefficientDigits(), input.exponent(), input.negative()))
	}
	return quotient.String(), negative, events
}

func quantizeOracleRat(coefficient string, exponent int32, negative bool) *big.Rat {
	numerator, ok := new(big.Int).SetString(coefficient, 10)
	if !ok {
		panic("invalid coefficient")
	}
	if negative {
		numerator.Neg(numerator)
	}
	if exponent >= 0 {
		numerator.Mul(numerator, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(exponent)), nil))
		return new(big.Rat).SetInt(numerator)
	}
	denominator := new(big.Int).Exp(big.NewInt(10), big.NewInt(-int64(exponent)), nil)
	return new(big.Rat).SetFrac(numerator, denominator)
}

func quantizeAssertOracle(t *testing.T, input Decimal, target int32, mode RoundingMode, got Decimal, conditions Conditions, err error) {
	t.Helper()
	wantDigits, wantNegative, wantConditions := quantizeOracle(input, target, mode)
	if err != nil || got.coefficientDigits() != wantDigits || got.exponent() != target || got.negative() != wantNegative || conditions != wantConditions {
		t.Fatalf("input %s target %d mode %d: got %s e%d sign%v conditions%v err%v; want %s e%d sign%v conditions%v", input, target, mode, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, wantDigits, target, wantNegative, wantConditions)
	}
	gotRat := quantizeOracleRat(got.coefficientDigits(), got.exponent(), got.negative())
	wantRat := quantizeOracleRat(wantDigits, target, wantNegative)
	if gotRat.Cmp(wantRat) != 0 {
		t.Fatalf("input %s target %d: rational value %s, want %s", input, target, gotRat, wantRat)
	}
	sourceRat := quantizeOracleRat(input.coefficientDigits(), input.exponent(), input.negative())
	distance := new(big.Rat).Sub(gotRat, sourceRat)
	if distance.Sign() < 0 {
		distance.Neg(distance)
	}
	if wantConditions&Inexact == 0 {
		if distance.Sign() != 0 {
			t.Fatalf("input %s target %d: exact target changed rational value", input, target)
		}
	} else if distance.Cmp(quantizeOracleRat("1", target, false)) >= 0 {
		t.Fatalf("input %s target %d: rounded result is not an adjacent target quantum", input, target)
	}
}

func TestQuantizeAllModesSignsAndCutClasses(t *testing.T) {
	modes := [...]RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact}
	classes := [...]struct {
		name, input string
	}{
		{"below-half", "1.241"},
		{"clean-even-tie", "1.245"},
		{"clean-odd-tie", "1.255"},
		{"sticky-tie", "1.2451"},
		{"above-half", "1.246"},
	}
	for _, mode := range modes {
		ctx, err := NewContext(0, mode, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		for _, sign := range []string{"", "-"} {
			for _, class := range classes {
				t.Run(strconv.Itoa(int(mode))+"/"+sign+class.name, func(t *testing.T) {
					input := MustParse(sign + class.input)
					direct, directConditions, directErr := input.Quantize(-2, mode)
					contextual, contextualConditions, contextualErr := input.QuantizeWithContext(-2, ctx)
					budgeted, budgetedConditions, budgetedErr := input.QuantizeWithContext(-2, ctx.WithBudget(Budget{MaxDigits: 3, MaxWork: 100}))
					if mode == Exact {
						quantizeCheckAbort(t, direct, directConditions, directErr, ErrInexact, "Quantize")
						quantizeCheckAbort(t, contextual, contextualConditions, contextualErr, ErrInexact, "QuantizeWithContext")
						quantizeCheckAbort(t, budgeted, budgetedConditions, budgetedErr, ErrInexact, "QuantizeWithContext")
						return
					}
					quantizeAssertOracle(t, input, -2, mode, direct, directConditions, directErr)
					quantizeAssertOracle(t, input, -2, mode, contextual, contextualConditions, contextualErr)
					quantizeAssertOracle(t, input, -2, mode, budgeted, budgetedConditions, budgetedErr)
				})
			}
		}
	}
}

func TestQuantizeDeterministicBigOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x717a, 0x9245))
	modes := [...]RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity}
	for i := range 800 {
		width := 1 + rng.IntN(90)
		digits := make([]byte, width)
		for j := range digits {
			digits[j] = byte('0' + rng.IntN(10))
		}
		digits[0] = byte('1' + rng.IntN(9))
		sign := ""
		if rng.IntN(2) == 0 {
			sign = "-"
		}
		source := int32(rng.IntN(71) - 35)
		target := int32(rng.IntN(71) - 35)
		input := MustParse(sign + string(digits) + "E" + strconv.Itoa(int(source)))
		mode := modes[i%len(modes)]
		got, conditions, err := input.Quantize(target, mode)
		quantizeAssertOracle(t, input, target, mode, got, conditions, err)
	}
	for _, input := range []string{"1" + strings.Repeat("0", 38), strings.Repeat("9", 39), strings.Repeat("7", 40)} {
		value := MustParse(input)
		for _, target := range []int32{-3, 0, 3} {
			got, conditions, err := value.Quantize(target, TiesToEven)
			quantizeAssertOracle(t, value, target, TiesToEven, got, conditions, err)
		}
	}
}

// TestQuantizeFiveTargetPaths pins the public B/W/N charge for every
// target path, with separate unlimited axes and the integral target-zero alias.
func TestQuantizeFiveTargetPaths(t *testing.T) {
	for _, tc := range []struct {
		name, input   string
		target        int32
		mode          RoundingMode
		base, work, n uint64
	}{
		{"zero", "-0.000", 6, TiesToEven, 1, 1, 1},
		{"equal", "1.23", -2, TiesToEven, 1, 1, 3},
		{"append", "12E+2", -2, TiesToEven, 1, 6, 6},
		{"existing discard", "1.234", -2, TiesToEven, 4, 7, 3},
		{"virtual gap", "5", 2, AwayFromZero, 1, 2, 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			input := MustParse(tc.input)
			ctx := quantizeTestContext(t, 0, tc.mode, nil, 0)
			call := func(budget Budget) (Decimal, Conditions, error) {
				return input.QuantizeWithContext(tc.target, ctx.WithBudget(budget))
			}
			checkSuccess := func(budget Budget) {
				t.Helper()
				got, conditions, err := call(budget)
				quantizeAssertOracle(t, input, tc.target, tc.mode, got, conditions, err)
				if uint64(len(got.coefficientDigits())) != tc.n {
					t.Fatalf("logical result digits = %d, want %d", len(got.coefficientDigits()), tc.n)
				}
			}
			checkRefusal := func(budget Budget) {
				t.Helper()
				got, conditions, err := call(budget)
				quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
			}
			if tc.base > 1 { // A zero limit means unlimited, not B-1 refusal.
				checkRefusal(Budget{MaxWork: tc.base - 1})
			}
			if tc.base < tc.work {
				checkRefusal(Budget{MaxWork: tc.base})
			}
			if tc.work > 1 {
				checkRefusal(Budget{MaxWork: tc.work - 1})
			}
			checkSuccess(Budget{MaxWork: tc.work})
			if tc.n > 1 { // N-1 is a positive refusal cap only in this case.
				checkRefusal(Budget{MaxDigits: tc.n - 1, MaxWork: tc.work})
			}
			checkSuccess(Budget{MaxDigits: tc.n, MaxWork: tc.work})
			checkSuccess(Budget{MaxDigits: 0, MaxWork: tc.work})
			checkSuccess(Budget{MaxDigits: tc.n, MaxWork: 0})
			checkSuccess(Budget{})
		})
	}

	ctx := quantizeTestContext(t, 0, TiesToEven, nil, 0)
	for _, tc := range []struct {
		name, input   string
		base, work, n uint64
	}{
		{"integral append", "12E+2", 1, 4, 4},
		{"integral discard", "12.34", 4, 6, 2},
	} {
		t.Run(tc.name, func(t *testing.T) {
			input := MustParse(tc.input)
			call := func(budget Budget) (Decimal, Conditions, error) {
				return input.RoundToIntegralWithContext(ctx.WithBudget(budget))
			}
			if tc.base > 1 {
				got, conditions, err := call(Budget{MaxWork: tc.base - 1})
				quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "RoundToIntegralWithContext")
			}
			got, conditions, err := call(Budget{MaxWork: tc.work - 1})
			quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "RoundToIntegralWithContext")
			got, conditions, err = call(Budget{MaxDigits: tc.n - 1, MaxWork: tc.work})
			quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "RoundToIntegralWithContext")
			for _, budget := range []Budget{
				{MaxDigits: tc.n, MaxWork: tc.work},
				{MaxDigits: 0, MaxWork: tc.work},
				{MaxDigits: tc.n, MaxWork: 0},
				{},
			} {
				got, conditions, err = call(budget)
				quantizeAssertOracle(t, input, 0, TiesToEven, got, conditions, err)
				if uint64(len(got.coefficientDigits())) != tc.n {
					t.Fatalf("integral digits = %d, want %d", len(got.coefficientDigits()), tc.n)
				}
			}
		})
	}
}

var quantizeResourceSink Decimal

// TestQuantizeRefusalOrderAndOneBuffer collides domain, precharge,
// Exact, final quotas and traps, then checks allocation on slow coefficients.
func TestQuantizeRefusalOrderAndOneBuffer(t *testing.T) {
	guarded := quantizeTestContext(t, 3, TiesToEven, &ExponentGuards{Emin: -2, Emax: 0}, Inexact|Rounded)
	for _, input := range []Decimal{MustParse("9.99"), New(0, -100)} {
		got, conditions, err := input.QuantizeWithContext(-5, guarded.WithBudget(Budget{MaxDigits: 1, MaxWork: 1}))
		quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
	}
	exact := quantizeTestContext(t, 2, Exact, nil, Inexact)
	for _, tc := range []struct {
		cap  uint64
		code ErrorCode
	}{{2, ErrInsufficientStorage}, {3, ErrInexact}} {
		got, conditions, err := MustParse("9.99").QuantizeWithContext(-1, exact.WithBudget(Budget{MaxWork: tc.cap}))
		quantizeCheckAbort(t, got, conditions, err, tc.code, "QuantizeWithContext")
	}
	got, conditions, err := MustParse("9.99").QuantizeWithContext(-1, guarded.WithBudget(Budget{MaxDigits: 1, MaxWork: 3}))
	quantizeCheckAbort(t, got, conditions, err, ErrInvalidOperation, "QuantizeWithContext")
	value := MustParse("1.234")
	trapping := quantizeTestContext(t, 0, TiesToEven, nil, Inexact|Rounded)
	for _, budget := range []Budget{
		{MaxDigits: 2, MaxWork: 7},
		{MaxDigits: 3, MaxWork: 6},
	} {
		got, conditions, err = value.QuantizeWithContext(-2, trapping.WithBudget(budget))
		quantizeCheckAbort(t, got, conditions, err, ErrInsufficientStorage, "QuantizeWithContext")
	}
	got, conditions, err = value.QuantizeWithContext(-2, trapping.WithBudget(Budget{MaxDigits: 3, MaxWork: 7}))
	var trapped *Error
	wantDigits, wantNegative, wantEvents := quantizeOracle(value, -2, TiesToEven)
	if got.coefficientDigits() != wantDigits || got.exponent() != -2 || got.negative() != wantNegative || conditions != Decreased || wantEvents != Inexact|Rounded|Decreased || !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Op != "QuantizeWithContext" || trapped.Condition != Inexact|Rounded || !errors.Is(err, ErrInexact) || !errors.Is(err, ErrRounded) {
		t.Fatalf("finite trap after quotas: %s e%d sign%v conditions%v err%v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
	}
	_, err = quantizePhysicalCount(quantizeCount{hi: 9}, "QuantizeWithContext")
	var physical *Error
	if !errors.As(err, &physical) || physical.Op != "QuantizeWithContext" || physical.Code != ErrInsufficientStorage || physical.Condition != InsufficientStorage {
		t.Fatalf("synthetic physical refusal identity: %v", err)
	}

	wide := MustParse(strings.Repeat("739182645", 112)) // 1,008 digits; slow holder.
	before := wide.coefficientDigits()
	allocs := testing.AllocsPerRun(30, func() {
		var c Conditions
		var callErr error
		quantizeResourceSink, c, callErr = wide.QuantizeWithContext(-1, Context{}.WithBudget(Budget{MaxDigits: 1009, MaxWork: 1009}))
		if callErr != nil || c != 0 {
			panic("admitted growth failed")
		}
	})
	if allocs > 2 || len(quantizeResourceSink.coefficientDigits()) != 1009 || quantizeResourceSink.exponent() != -1 || quantizeResourceSink.slow == wide.slow {
		t.Fatalf("admitted growth used %.0f allocations; result %d digits e%d", allocs, len(quantizeResourceSink.coefficientDigits()), quantizeResourceSink.exponent())
	}
	for _, budget := range []Budget{{MaxDigits: 1008}, {MaxWork: 1008}} {
		var refused Decimal
		var refusedConditions Conditions
		var refusedErr error
		allocs = testing.AllocsPerRun(30, func() {
			refused, refusedConditions, refusedErr = wide.QuantizeWithContext(-1, Context{}.WithBudget(budget))
		})
		quantizeCheckAbort(t, refused, refusedConditions, refusedErr, ErrInsufficientStorage, "QuantizeWithContext")
		if allocs > 1 {
			t.Fatalf("refusal %+v used %.0f allocations; want typed error only", budget, allocs)
		}
	}
	if wide.coefficientDigits() != before {
		t.Fatal("target calls mutated their shared input")
	}
}

func quantizeAbort(t *testing.T, got Decimal, conditions Conditions, err error, op string, code ErrorCode) {
	t.Helper()
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, code) || errors.Is(err, ErrExponentRange) {
		t.Fatalf("%s abort: coefficient %s exponent %d sign %v conditions %v error %v; want %v without exponent-range identity", op, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, code)
	}
	switch code {
	case ErrInvalidContext:
		typed, ok := err.(*Error)
		if !ok || typed.Op != op || typed.Code != code || typed.Condition != InvalidContext {
			t.Fatalf("%s Error identity: %v", op, err)
		}
	case ErrInvalidOperation, ErrInsufficientStorage:
		typed, ok := err.(*Error)
		wantCondition := InvalidOperation
		if code == ErrInsufficientStorage {
			wantCondition = InsufficientStorage
		}
		if !ok || typed.Op != op || typed.Code != code || typed.Condition != wantCondition {
			t.Fatalf("%s Error identity: %v", op, err)
		}
	case ErrInexact:
		typed, ok := err.(*Error)
		if !ok || typed.Op != op || typed.Condition != Inexact || errors.Is(err, ErrRounded) {
			t.Fatalf("%s Error identity: %v", op, err)
		}
	default:
		t.Fatalf("unsupported test cause %v", code)
	}
}

// TestQuantizeAbortIdentity checks the exact outer type, wrapped cause,
// operation name and zero return for each publicly reachable abort class.
func TestQuantizeAbortIdentity(t *testing.T) {
	guarded := quantizeTestContext(t, 2, TiesToEven, &ExponentGuards{Emin: 2, Emax: 3}, 0)
	fit := quantizeTestContext(t, 2, TiesToEven, nil, 0)
	for _, tc := range []struct {
		name, op string
		code     ErrorCode
		call     func() (Decimal, Conditions, error)
	}{
		{"unknown Quantize mode", "Quantize", ErrInvalidContext, func() (Decimal, Conditions, error) { return One().Quantize(0, RoundingMode(255)) }},
		{"unknown integral mode", "RoundToIntegral", ErrInvalidContext, func() (Decimal, Conditions, error) { return One().RoundToIntegral(RoundingMode(255)) }},
		{"guarded target", "QuantizeWithContext", ErrInvalidOperation, func() (Decimal, Conditions, error) {
			return One().QuantizeWithContext(0, guarded.WithBudget(Budget{MaxWork: 1}))
		}},
		{"integral guarded target", "RoundToIntegralWithContext", ErrInvalidOperation, func() (Decimal, Conditions, error) { return One().RoundToIntegralWithContext(guarded) }},
		{"rounded candidate fit", "QuantizeWithContext", ErrInvalidOperation, func() (Decimal, Conditions, error) { return MustParse("9.99").QuantizeWithContext(-1, fit) }},
		{"work refusal", "QuantizeWithContext", ErrInsufficientStorage, func() (Decimal, Conditions, error) {
			return MustParse("1.234").QuantizeWithContext(-2, Context{}.WithBudget(Budget{MaxWork: 3}))
		}},
		{"integral digit refusal", "RoundToIntegralWithContext", ErrInsufficientStorage, func() (Decimal, Conditions, error) {
			return MustParse("12.34").RoundToIntegralWithContext(Context{}.WithBudget(Budget{MaxDigits: 1}))
		}},
		{"Exact Quantize", "Quantize", ErrInexact, func() (Decimal, Conditions, error) { return MustParse("1.234").Quantize(-2, Exact) }},
		{"Exact integral", "RoundToIntegral", ErrInexact, func() (Decimal, Conditions, error) { return MustParse("2.5").RoundToIntegral(Exact) }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			quantizeAbort(t, got, conditions, err, tc.op, tc.code)
		})
	}
	_, err := quantizePhysicalCount(quantizeCount{hi: 9}, "QuantizeWithContext")
	physical, ok := err.(*Error)
	if !errors.Is(err, ErrInsufficientStorage) || !ok || physical.Op != "QuantizeWithContext" || physical.Code != ErrInsufficientStorage || physical.Condition != InsufficientStorage || errors.Is(err, ErrExponentRange) {
		t.Fatalf("physical preflight typed identity: %v", err)
	}
}

var quantizeBenchmarkResult Decimal
var quantizeBenchmarkConditions Conditions
var quantizeBenchmarkError error

// BenchmarkQuantizeDirected exercises distinct fixed target-rounding paths.
// Inputs and independent expected coefficients are prepared outside the timer.
func BenchmarkQuantizeDirected(b *testing.B) {
	for _, tc := range []struct {
		name, input string
		target      int32
		integral    bool
	}{
		{"equal-inline", "123.45", -2, false},
		{"shrink-inline-tie", "123.455", -2, false},
		{"shrink-slow-1000", strings.Repeat("7", 1000) + ".55", 0, false},
		{"growth-slow-1000", strings.Repeat("4", 1000), -3, false},
		{"integral-slow-1000", strings.Repeat("6", 1000) + ".51", 0, true},
	} {
		b.Run(tc.name, func(b *testing.B) {
			input := MustParse(tc.input)
			wantDigits, wantNegative, wantConditions := quantizeOracle(input, tc.target, TiesToEven)
			run := func() (Decimal, Conditions, error) {
				if tc.integral {
					return input.RoundToIntegral(TiesToEven)
				}
				return input.Quantize(tc.target, TiesToEven)
			}
			got, conditions, err := run()
			if err != nil || got.coefficientDigits() != wantDigits || got.exponent() != tc.target || got.negative() != wantNegative || conditions != wantConditions {
				b.Fatalf("oracle mismatch: got %s e%d sign%v conditions%v err%v; want %s e%d sign%v conditions%v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, wantDigits, tc.target, wantNegative, wantConditions)
			}
			b.ReportAllocs()
			b.ResetTimer()
			for b.Loop() {
				quantizeBenchmarkResult, quantizeBenchmarkConditions, quantizeBenchmarkError = run()
				if quantizeBenchmarkError != nil {
					b.Fatal(quantizeBenchmarkError)
				}
			}
		})
	}
}

// quantizeDirectionInput draws a signed decimal of up to 40 digits whose
// runs of nines provoke carries across the target quantum.
func quantizeDirectionInput(rng *rand.Rand) Decimal {
	digits := make([]byte, 1+rng.IntN(40))
	for i := range digits {
		digits[i] = byte('0' + rng.IntN(10))
		if rng.IntN(3) == 0 {
			digits[i] = '9'
		}
	}
	digits[0] = byte('1' + rng.IntN(9))
	sign := ""
	if rng.IntN(2) == 0 {
		sign = "-"
	}
	return MustParse(sign + string(digits) + "E" + strconv.Itoa(rng.IntN(41)-30))
}

// TestQuantizeDirectionAgainstRationalOracle checks the direction
// against a rational oracle for Quantize and RoundToIntegral in direct and
// context forms: in every mode the direction bit equals sign(result −
// exact) by math/big.Rat comparison and accompanies Inexact exactly. Named
// rows pin negative values rounded to the unsigned zero (Increased), the
// Etiny quantum under guards, zero-only discards (Rounded, no direction),
// Exact refusals and resource refusals (no value, no direction).
func TestQuantizeDirectionAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(0xdec045, 3))
	modes := [...]RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact}
	counts := map[Conditions]int{}
	for i := range 20_000 {
		input := quantizeDirectionInput(rng)
		exact := directionValueRat(input)
		target := input.exponent() + int32(rng.IntN(45)-5)
		mode := modes[rng.IntN(len(modes))]
		label := input.String() + " t" + strconv.Itoa(int(target)) + " mode" + strconv.Itoa(int(mode))
		var got Decimal
		var conditions Conditions
		var err error
		switch i % 4 {
		case 0:
			got, conditions, err = input.Quantize(target, mode)
		case 1:
			got, conditions, err = input.RoundToIntegral(mode)
		case 2:
			emin := int32(rng.IntN(41) - 40)
			ctx := quantizeTestContext(t, uint32(1+rng.IntN(45)), mode, &ExponentGuards{Emin: emin, Emax: emin + 40}, 0)
			got, conditions, err = input.QuantizeWithContext(target, ctx)
		default:
			got, conditions, err = input.RoundToIntegralWithContext(quantizeTestContext(t, 0, mode, nil, 0).WithBudget(Budget{MaxWork: 1 << 20}))
		}
		if checkRoundingDirection(t, label, exact, mode, got, conditions, err) {
			counts[conditions&(Increased|Decreased|Subnormal)]++
		} else if conditions != 0 {
			t.Fatalf("%s: refusal returned %v", label, conditions)
		}
	}
	for _, want := range []Conditions{Increased, Decreased, Increased | Subnormal, Decreased | Subnormal} {
		if counts[want] < 20 {
			t.Fatalf("Quantize direction corpus reached %v only %d times: %v", want, counts[want], counts)
		}
	}

	etiny := quantizeTestContext(t, 7, TiesAwayFromZero, &ExponentGuards{Emin: -999, Emax: 999}, 0)
	for _, tc := range []struct {
		name       string
		call       func() (Decimal, Conditions, error)
		input      string
		want       string
		conditions Conditions
	}{
		{"negative to zero TowardZero", func() (Decimal, Conditions, error) { return MustParse("-0.4").Quantize(0, TowardZero) }, "-0.4", "0", Inexact | Rounded | Increased},
		{"negative third to zero", func() (Decimal, Conditions, error) { return MustParse("-0.333").Quantize(0, TowardZero) }, "-0.333", "0", Inexact | Rounded | Increased},
		{"negative tie to zero", func() (Decimal, Conditions, error) { return MustParse("-0.5").RoundToIntegral(TiesToEven) }, "-0.5", "0", Inexact | Rounded | Increased},
		{"negative to zero TowardPositive", func() (Decimal, Conditions, error) { return MustParse("-0.999").Quantize(0, TowardPositiveInfinity) }, "-0.999", "0", Inexact | Rounded | Increased},
		{"positive to zero TowardNegative", func() (Decimal, Conditions, error) { return MustParse("0.999").Quantize(0, TowardNegativeInfinity) }, "0.999", "0", Inexact | Rounded | Decreased},
		{"negative away TowardNegative", func() (Decimal, Conditions, error) { return MustParse("-0.001").Quantize(0, TowardNegativeInfinity) }, "-0.001", "-1", Inexact | Rounded | Decreased},
		{"Etiny subnormal up", func() (Decimal, Conditions, error) {
			return MustParse("1.666666E-1000").QuantizeWithContext(-1005, etiny)
		}, "1.666666E-1000", "1.66667E-1000", Subnormal | Inexact | Rounded | Increased},
		{"Etiny negative to zero", func() (Decimal, Conditions, error) {
			return MustParse("-1.666666E-1006").QuantizeWithContext(-1005, etiny)
		}, "-1.666666E-1006", "0E-1005", Inexact | Rounded | Increased},
		{"Etiny negative subnormal", func() (Decimal, Conditions, error) {
			return MustParse("-1.666664E-1000").QuantizeWithContext(-1005, etiny)
		}, "-1.666664E-1000", "-1.66666E-1000", Subnormal | Inexact | Rounded | Increased},
		{"zero-only discard", func() (Decimal, Conditions, error) { return MustParse("1.000").Quantize(-1, TowardPositiveInfinity) }, "1.000", "1.0", Rounded},
		{"zero-only discard Exact", func() (Decimal, Conditions, error) { return MustParse("-99.90").Quantize(-1, Exact) }, "-99.90", "-99.9", Rounded},
		{"zero-only integral", func() (Decimal, Conditions, error) { return MustParse("-7.00").RoundToIntegral(TowardZero) }, "-7.00", "-7", Rounded},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			if err != nil || got.String() != tc.want || conditions != tc.conditions {
				t.Fatalf("%s: %v %v %v; want %s %v", tc.name, got, conditions, err, tc.want, tc.conditions)
			}
			checkRoundingDirection(t, tc.name, directionValueRat(MustParse(tc.input)), TiesToEven, got, conditions, err)
		})
	}
	for _, tc := range []struct {
		name string
		op   string
		code ErrorCode
		call func() (Decimal, Conditions, error)
	}{
		{"Exact Quantize", "Quantize", ErrInexact, func() (Decimal, Conditions, error) { return MustParse("-1.234").Quantize(-2, Exact) }},
		{"Exact integral", "RoundToIntegralWithContext", ErrInexact, func() (Decimal, Conditions, error) {
			return MustParse("-0.4").RoundToIntegralWithContext(quantizeTestContext(t, 0, Exact, nil, 0))
		}},
		{"resource Quantize", "QuantizeWithContext", ErrInsufficientStorage, func() (Decimal, Conditions, error) {
			return MustParse("1.234").QuantizeWithContext(-2, quantizeTestContext(t, 0, TowardPositiveInfinity, nil, 0).WithBudget(Budget{MaxWork: 3}))
		}},
		{"resource integral", "RoundToIntegralWithContext", ErrInsufficientStorage, func() (Decimal, Conditions, error) {
			return MustParse("-12.34").RoundToIntegralWithContext(quantizeTestContext(t, 0, TowardNegativeInfinity, nil, 0).WithBudget(Budget{MaxDigits: 1}))
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			quantizeCheckAbort(t, got, conditions, err, tc.code, tc.op)
		})
	}
}

// TestQuantizeDirectedEnclosure checks the enclosure and tightness
// property for Quantize and RoundToIntegral: TowardNegativeInfinity and
// TowardPositiveInfinity return the floor and ceiling of the exact value on
// the target exponent's grid (exponent 0 for RoundToIntegral), so they
// bracket it and no multiple of the target quantum lies strictly between,
// including carries such as 9.995 to 10.00 and guarded subnormal targets.
func TestQuantizeDirectedEnclosure(t *testing.T) {
	rng := rand.New(rand.NewPCG(0xdec045, 4))
	checked, inexact := 0, 0
	guarded := func(mode RoundingMode) Context {
		return quantizeTestContext(t, 7, mode, &ExponentGuards{Emin: -999, Emax: 999}, 0)
	}
	type sample struct {
		input   Decimal
		target  int32
		context bool
	}
	samples := []sample{
		{MustParse("9.995"), -2, false},
		{MustParse("-9.995"), -2, false},
		{MustParse("99.5"), 0, false},
		{MustParse("1.666666E-1000"), -1005, true},
		{MustParse("-1.666666E-1006"), -1005, true},
		{New(5, math.MinInt32), math.MaxInt32, false},
		{New(-5, math.MinInt32), math.MaxInt32, false},
	}
	for range 10_000 {
		input := quantizeDirectionInput(rng)
		samples = append(samples, sample{input, input.exponent() + int32(rng.IntN(45)-5), rng.IntN(2) == 0})
	}
	for i, s := range samples {
		var lo, hi Decimal
		var loConditions, hiConditions Conditions
		var loErr, hiErr error
		if s.context {
			lo, loConditions, loErr = s.input.QuantizeWithContext(s.target, guarded(TowardNegativeInfinity))
			hi, hiConditions, hiErr = s.input.QuantizeWithContext(s.target, guarded(TowardPositiveInfinity))
			if loErr != nil || hiErr != nil {
				if !errors.Is(loErr, ErrInvalidOperation) || !errors.Is(hiErr, ErrInvalidOperation) || loConditions != 0 || hiConditions != 0 {
					t.Fatalf("sample %d: guarded refusals %v %v / %v %v", i, loConditions, loErr, hiConditions, hiErr)
				}
				continue
			}
		} else {
			lo, loConditions, loErr = s.input.Quantize(s.target, TowardNegativeInfinity)
			hi, hiConditions, hiErr = s.input.Quantize(s.target, TowardPositiveInfinity)
		}
		if loErr != nil || hiErr != nil {
			t.Fatalf("sample %d %v t%d: errors %v / %v", i, s.input, s.target, loErr, hiErr)
		}
		label := "sample " + strconv.Itoa(i) + " " + s.input.String() + " t" + strconv.Itoa(int(s.target))
		if s.target == math.MaxInt32 {
			// The grid at 10^MaxInt32 is not materialized: pin the one-quantum
			// and zero results by sign instead.
			wantLo, wantHi := Decreased, Increased
			if lo.isZero() == s.input.negative() || hi.isZero() == !s.input.negative() || loConditions&(Increased|Decreased) != wantLo || hiConditions&(Increased|Decreased) != wantHi {
				t.Fatalf("%s: lo %v %v hi %v %v", label, lo, loConditions, hi, hiConditions)
			}
			continue
		}
		exact := directionValueRat(s.input)
		if !checkDirectedEnclosure(t, label, exact, int64(s.target), lo, loConditions, hi, hiConditions) {
			t.Fatalf("%s: Quantize reported Overflow", label)
		}
		checked++
		if loConditions&Inexact != 0 {
			inexact++
		}
		integralLo, integralLoConditions, _ := s.input.RoundToIntegral(TowardNegativeInfinity)
		integralHi, integralHiConditions, _ := s.input.RoundToIntegral(TowardPositiveInfinity)
		checkDirectedEnclosure(t, label+" integral", exact, 0, integralLo, integralLoConditions, integralHi, integralHiConditions)
	}
	if checked < 7_000 || inexact < 3_000 {
		t.Fatalf("enclosure checked %d pairs, %d inexact", checked, inexact)
	}
}

// quantizeCallResult renders one quantize call as "value exponent
// conditions error".
func quantizeCallResult(d Decimal, c Conditions, err error) string {
	e := "<nil>"
	if err != nil {
		e = err.Error()
	}
	return d.String() + " " + strconv.Itoa(int(d.exponent())) + " " + c.String() + " " + e
}

// TestQuantizeTargetOverridesContextPrecision checks that a per-operation
// target wins: an explicit Quantize target rounds at that
// exponent under a finite-precision context rather than at the context's
// working precision. Hand-derived: 1.2345 at 10^-3 under p=10 is 1.234
// (tie to even), at 10^-1 under p=3 is 1.2, and 1.2 at 10^-3 under p=10 is
// 1.200 with no condition, while the same p=3 context rounds 1.2345+0 to
// its working precision, 1.23.
func TestQuantizeTargetOverridesContextPrecision(t *testing.T) {
	p10, err := NewContext(10, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	p3, err := NewContext(3, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		in     string
		target int32
		ctx    Context
		want   string
	}{
		{"1.2345", -3, p10, "1.234 -3 Inexact|Rounded|Decreased <nil>"},
		{"1.2345", -1, p3, "1.2 -1 Inexact|Rounded|Decreased <nil>"},
		{"1.2", -3, p10, "1.200 -3 0 <nil>"},
		{"98.76", 0, p10, "99 0 Inexact|Rounded|Increased <nil>"},
	} {
		if got := quantizeCallResult(MustParse(tc.in).QuantizeWithContext(tc.target, tc.ctx)); got != tc.want {
			t.Errorf("QuantizeWithContext(%s, %d, p=%d) = %q, want %q", tc.in, tc.target, tc.ctx.Precision(), got, tc.want)
		}
	}
	if got, want := quantizeCallResult(MustParse("1.2345").AddWithContext(Zero(), p3)), "1.23 -2 Inexact|Rounded|Decreased <nil>"; got != want {
		t.Errorf("AddWithContext(1.2345, 0, p=3) = %q, want %q", got, want)
	}
}

// TestQuantizeOneDecimalTieGroundTruth checks negative ties at one
// decimal place and tie-to-even on a positive operand against the GDA
// table: -2.35 quantized to 10^-1 is -2.4
// under TiesToEven, TiesAwayFromZero, AwayFromZero and
// TowardNegativeInfinity (Decreased) and -2.3 under TiesTowardZero,
// TowardZero and TowardPositiveInfinity (Increased), always Inexact and
// Rounded; Exact refuses with Inexact; 2.25 under TiesToEven is 2.2.
func TestQuantizeOneDecimalTieGroundTruth(t *testing.T) {
	neg := MustParse("-2.35")
	for _, tc := range []struct {
		mode RoundingMode
		want string
	}{
		{TiesToEven, "-2.4 -1 Inexact|Rounded|Decreased <nil>"},
		{TiesAwayFromZero, "-2.4 -1 Inexact|Rounded|Decreased <nil>"},
		{TiesTowardZero, "-2.3 -1 Inexact|Rounded|Increased <nil>"},
		{TowardZero, "-2.3 -1 Inexact|Rounded|Increased <nil>"},
		{AwayFromZero, "-2.4 -1 Inexact|Rounded|Decreased <nil>"},
		{TowardPositiveInfinity, "-2.3 -1 Inexact|Rounded|Increased <nil>"},
		{TowardNegativeInfinity, "-2.4 -1 Inexact|Rounded|Decreased <nil>"},
	} {
		if got := quantizeCallResult(neg.Quantize(-1, tc.mode)); got != tc.want {
			t.Errorf("-2.35 at 10^-1 under %v = %q, want %q", tc.mode, got, tc.want)
		}
	}
	if d, c, err := neg.Quantize(-1, Exact); !errors.Is(err, ErrInexact) || !reflect.DeepEqual(d, Decimal{}) || c != 0 {
		t.Errorf("-2.35 at 10^-1 under Exact = %s, %v, %v; want Decimal{} and an Inexact refusal", d, c, err)
	}
	if got, want := quantizeCallResult(MustParse("2.25").Quantize(-1, TiesToEven)), "2.2 -1 Inexact|Rounded|Decreased <nil>"; got != want {
		t.Errorf("2.25 at 10^-1 under TiesToEven = %q, want %q", got, want)
	}
}

// TestQuantizeGuardedTargetOutsideLattice checks a guarded target
// outside the exponent lattice: under p=3, Emin -2,
// Emax 2 (Etiny -4) with Overflow and Underflow trapped, Quantize to a
// target below Etiny or above Emax returns Decimal{}, zero conditions and an
// unconditional InvalidOperation Error, never a boundary value,
// Overflow or a trap error; targets on the lattice's edges succeed with the
// hand-derived results. RoundToIntegral's target 0 above Emax -1 is refused
// the same way.
func TestQuantizeGuardedTargetOutsideLattice(t *testing.T) {
	ctx, err := NewContext(3, TiesToEven, &ExponentGuards{Emin: -2, Emax: 2}, Overflow|Underflow)
	if err != nil {
		t.Fatal(err)
	}
	refused := func(name string, d Decimal, c Conditions, err error) {
		t.Helper()
		var opErr *Error
		if !reflect.DeepEqual(d, Decimal{}) || c != 0 || !errors.Is(err, ErrInvalidOperation) || !errors.As(err, &opErr) ||
			opErr.Condition != InvalidOperation || errors.Is(err, ErrOverflow) || opErr.Code == 0 {
			t.Errorf("%s = %s, %v, %v; want Decimal{}, 0 and an unconditional InvalidOperation", name, d, c, err)
		}
	}
	for _, in := range []Decimal{One(), Zero(), MustParse("1E-4"), MustParse("-9.99")} {
		for _, target := range []int32{-5, 3, math.MaxInt32, math.MinInt32} {
			d, c, err := in.QuantizeWithContext(target, ctx)
			refused("QuantizeWithContext("+in.String()+", "+strconv.Itoa(int(target))+")", d, c, err)
		}
	}
	for _, tc := range []struct {
		in     string
		target int32
		want   string
	}{
		{"0", -4, "0.0000 -4 0 <nil>"},
		{"1E-4", -4, "0.0001 -4 Subnormal <nil>"},
		{"1E+2", 2, "1E+2 2 0 <nil>"},
		{"1", 2, "0E+2 2 Inexact|Rounded|Decreased <nil>"},
	} {
		if got := quantizeCallResult(MustParse(tc.in).QuantizeWithContext(tc.target, ctx)); got != tc.want {
			t.Errorf("QuantizeWithContext(%s, %d) = %q, want %q", tc.in, tc.target, got, tc.want)
		}
	}
	below, err := NewContext(3, TiesToEven, &ExponentGuards{Emin: -5, Emax: -1}, 0)
	if err != nil {
		t.Fatal(err)
	}
	d, c, err := MustParse("0.5").RoundToIntegralWithContext(below)
	refused("RoundToIntegralWithContext(0.5, Emax -1)", d, c, err)
}

// TestInlineQuantizeMatchesLimbPath pins direct Quantize, RoundToIntegral and
// unguarded context Quantize to the general target-rounding path in all
// eight modes, including Exact refusal, traps and zero results.
func TestInlineQuantizeMatchesLimbPath(t *testing.T) {
	r := randv1.New(randv1.NewSource(20261002))
	fast := 0
	for range 200_000 {
		d := inlineSample(r, 0)
		if d.isZero() {
			continue
		}
		target := d.exponent() + int32(r.Intn(51)-25)
		ctx := Context{rounding: RoundingMode(r.Intn(int(Exact) + 1))}
		if r.Intn(4) == 0 {
			ctx.traps = Conditions(r.Intn(int(trappableConditions) + 1))
		}
		want, wantEvents, wantErr := d.quantizeLimbs(target, ctx, limits{}, "QuantizeWithContext")
		got, events, err := d.quantize(target, ctx, limits{}, "QuantizeWithContext")
		if _, _, _, ok := inlineQuantize(d, target, ctx.rounding); ok {
			fast++
		}
		if !sameRepresentation(got, want) || events != wantEvents || (err == nil) != (wantErr == nil) ||
			err != nil && err.Error() != wantErr.Error() {
			t.Fatalf("Quantize(%#v, %d, %+v) = %#v, %b, %v; limb path %#v, %b, %v", d, target, ctx, got, events, err, want, wantEvents, wantErr)
		}
	}
	if fast < 100_000 {
		t.Fatalf("inline quantize exercised only %d times", fast)
	}
}
