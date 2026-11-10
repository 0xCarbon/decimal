// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"math"
	"math/big"
	"math/rand/v2"
	"path/filepath"
	"reflect"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
)

func TestContextPublicSignatureShapes(t *testing.T) {
	var construct func(uint32, RoundingMode, *ExponentGuards, Conditions) (Context, error) = NewContext
	var precision func(Context) uint32 = Context.Precision
	var rounding func(Context) RoundingMode = Context.Rounding
	var guards func(Context) (ExponentGuards, bool) = Context.ExponentGuards
	var traps func(Context) Conditions = Context.Traps
	var derive func(Context, Conditions) (Context, error) = Context.WithTraps
	var p32, p64, p128 func() Context = Decimal32Context, Decimal64Context, Decimal128Context
	if construct == nil || precision == nil || rounding == nil || guards == nil || traps == nil || derive == nil || p32 == nil || p64 == nil || p128 == nil {
		t.Fatal("missing context entry point")
	}
}

func TestContextZeroAndCopiedGuard(t *testing.T) {
	var zero Context
	if zero.Precision() != 0 || zero.Rounding() != TiesToEven || zero.Traps() != 0 {
		t.Fatalf("zero context = %+v", zero)
	}
	if guard, enabled := zero.ExponentGuards(); enabled || guard != (ExponentGuards{}) {
		t.Fatalf("zero guards = %+v, %v", guard, enabled)
	}

	input := ExponentGuards{Emin: 0, Emax: 0}
	got, err := NewContext(1, TiesToEven, &input, Clamped)
	if err != nil {
		t.Fatal(err)
	}
	input.Emin, input.Emax = -100, 100
	copyOfGetter, enabled := got.ExponentGuards()
	if !enabled || copyOfGetter != (ExponentGuards{}) || got.Precision() != 1 || got.Traps() != Clamped {
		t.Fatalf("guarded [0,0] = %+v, %+v, enabled=%v", got, copyOfGetter, enabled)
	}
	copyOfGetter.Emin = 77
	if guard, _ := got.ExponentGuards(); guard != (ExponentGuards{}) {
		t.Fatalf("getter modified context guard: %+v", guard)
	}
	unbounded, err := NewContext(1, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	if _, enabled := unbounded.ExponentGuards(); enabled || got == unbounded {
		t.Fatal("nil guard and [0,0] guard collapsed")
	}
	derived, err := got.WithTraps(Inexact)
	if err != nil || derived.Traps() != Inexact || got.Traps() != Clamped {
		t.Fatalf("derivation = %+v, %v; original = %+v", derived, err, got)
	}
	if g, e := derived.ExponentGuards(); !e || g != (ExponentGuards{}) || derived.Precision() != got.Precision() || derived.Rounding() != got.Rounding() {
		t.Fatalf("derivation lost configuration: %+v", derived)
	}
}

func TestContextInvalidIdentityAndBounds(t *testing.T) {
	allModes := [...]RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact}
	for _, mode := range allModes {
		if _, err := NewContext(0, mode, nil, 0); err != nil {
			t.Fatalf("valid mode %d: %v", mode, err)
		}
	}
	for _, tc := range []struct {
		name      string
		precision uint32
		mode      RoundingMode
		guard     *ExponentGuards
		traps     Conditions
	}{
		{"unlimited guarded", 0, TiesToEven, &ExponentGuards{}, 0},
		{"reversed endpoints", 1, TiesToEven, &ExponentGuards{Emin: 2, Emax: 1}, 0},
		{"etiny below int32", 2, TiesToEven, &ExponentGuards{Emin: math.MinInt32, Emax: math.MinInt32}, 0},
		{"unknown mode 8", 1, 8, nil, 0},
		{"unknown mode 255", 1, 255, nil, 0},
		{"Increased direction attribute trap", 1, TiesToEven, nil, Increased},
		{"Decreased direction attribute trap", 1, TiesToEven, nil, Decreased},
		{"highest undeclared trap bit", 1, TiesToEven, nil, 1 << 15},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := NewContext(tc.precision, tc.mode, tc.guard, tc.traps)
			assertInvalidContext(t, got, err, "NewContext")
		})
	}
	for _, tc := range []struct {
		guard ExponentGuards
		p     uint32
	}{
		{ExponentGuards{Emin: math.MinInt32, Emax: math.MinInt32}, 1},
		{ExponentGuards{Emin: math.MinInt32 + 1, Emax: math.MinInt32 + 1}, 2},
		{ExponentGuards{Emin: math.MaxInt32, Emax: math.MaxInt32}, 1},
	} {
		got, err := NewContext(tc.p, Exact, &tc.guard, Underflow)
		if err != nil || got.Precision() != tc.p || got.Rounding() != Exact || got.Traps() != Underflow {
			t.Fatalf("boundary %+v p=%d: %+v, %v", tc.guard, tc.p, got, err)
		}
		if guard, enabled := got.ExponentGuards(); !enabled || guard != tc.guard {
			t.Fatalf("boundary getter %+v, %v", guard, enabled)
		}
	}
	if got, err := NewContext(math.MaxUint32, TiesToEven, nil, 0); err != nil || got.Precision() != math.MaxUint32 {
		t.Fatalf("unbounded maximum precision: %+v, %v", got, err)
	}
}

func TestContextInvalidGuardTrapIndependence(t *testing.T) {
	reversed := ExponentGuards{Emin: 2, Emax: 1}
	for _, traps := range [...]Conditions{0, InvalidContext} {
		got, err := NewContext(3, TiesToEven, &reversed, traps)
		assertInvalidContext(t, got, err, "NewContext")
	}
}

func TestContextTrapDerivationAndErrorTotality(t *testing.T) {
	allKnown := Conditions((Underflow << 1) - 1)
	base, err := NewContext(3, TiesAwayFromZero, &ExponentGuards{Emin: -2, Emax: 2}, allKnown)
	if err != nil || base.Traps() != allKnown {
		t.Fatalf("declared trap bits: %+v, %v", base, err)
	}
	derived, err := base.WithTraps(Clamped | Inexact)
	if err != nil || derived.Traps() != Clamped|Inexact || base.Traps() != allKnown {
		t.Fatalf("known trap derivation: %+v, %v", derived, err)
	}
	for _, unknown := range [...]Conditions{Increased, Decreased, 1 << 15} {
		got, err := base.WithTraps(unknown)
		assertInvalidContext(t, got, err, "Context.WithTraps")
		got, err = (Context{}).WithTraps(unknown)
		assertInvalidContext(t, got, err, "Context.WithTraps")
	}
	fromZero, err := (Context{}).WithTraps(Clamped)
	if err != nil || fromZero.Precision() != 0 || fromZero.Rounding() != TiesToEven || fromZero.Traps() != Clamped {
		t.Fatalf("zero-context derivation = %+v, %v", fromZero, err)
	}
	if _, enabled := fromZero.ExponentGuards(); enabled {
		t.Fatal("zero-context derivation gained guards")
	}
	var zero Error
	if zero.Error() != "decimal: error" || zero.Unwrap() != nil {
		t.Fatalf("zero Error = %q, %v", zero.Error(), zero.Unwrap())
	}
	var nilErr *Error
	if nilErr.Error() != "decimal: error" || nilErr.Unwrap() != nil {
		t.Fatalf("nil Error = %q, %v", nilErr.Error(), nilErr.Unwrap())
	}
	bareCause := Error{Code: ErrInvalidContext}
	if bareCause.Error() != "decimal: invalid context" || !errors.Is(&bareCause, ErrInvalidContext) {
		t.Fatalf("zero-Op Error = %q, %v", bareCause.Error(), bareCause.Unwrap())
	}
	if ErrInvalidContext.Error() != "decimal: invalid context" {
		t.Fatalf("sentinel diagnostic = %q", ErrInvalidContext.Error())
	}
}

func assertInvalidContext(t *testing.T, got Context, err error, op string) {
	t.Helper()
	var contextErr *Error
	if got != (Context{}) || !errors.Is(err, ErrInvalidContext) || !errors.As(err, &contextErr) || contextErr.Op != op || contextErr.Code != ErrInvalidContext || contextErr.Condition != InvalidContext {
		t.Fatalf("invalid context = %+v, %v; want %s/ErrInvalidContext/InvalidContext", got, err, op)
	}
	if contextErr.Error() == "" || contextErr.Unwrap() != ErrInvalidContext {
		t.Fatalf("invalid context diagnostic/wrap = %q, %v", contextErr.Error(), contextErr.Unwrap())
	}
}

func TestContextTupleValidationIndependentBigIntOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(0xdec17, 0x71ec))
	precisions := []uint32{0, 1, 2, 7, 34, math.MaxUint32}
	endpoints := []int32{math.MinInt32, math.MinInt32 + 1, -100, -1, 0, 1, 100, math.MaxInt32 - 1, math.MaxInt32}
	for _, p := range precisions {
		for _, emin := range endpoints {
			for _, emax := range endpoints {
				checkContextTupleOracle(t, p, emin, emax)
			}
		}
	}
	for range 2000 {
		checkContextTupleOracle(t, rng.Uint32(), int32(rng.Uint32()), int32(rng.Uint32()))
	}
}

func checkContextTupleOracle(t *testing.T, p uint32, emin, emax int32) {
	t.Helper()
	guards := ExponentGuards{Emin: emin, Emax: emax}
	etiny := big.NewInt(int64(emin))
	if p > 0 {
		etiny.Sub(etiny, new(big.Int).SetUint64(uint64(p-1)))
	}
	valid := p > 0 && emin <= emax && etiny.IsInt64() && etiny.Int64() >= math.MinInt32 && etiny.Int64() <= math.MaxInt32
	got, err := NewContext(p, TiesToEven, &guards, 0)
	if valid {
		if err != nil || got.Precision() != p {
			t.Fatalf("oracle valid tuple p=%d [%d,%d], Etiny=%s: %+v, %v", p, emin, emax, etiny, got, err)
		}
		if g, enabled := got.ExponentGuards(); !enabled || g != guards {
			t.Fatalf("oracle valid tuple getter p=%d [%d,%d]: %+v, %v", p, emin, emax, g, enabled)
		}
	} else {
		assertInvalidContext(t, got, err, "NewContext")
	}
}

func TestContextNumericalPresets(t *testing.T) {
	for _, tc := range []struct {
		name  string
		make  func() Context
		p     uint32
		emin  int32
		emax  int32
		etiny int32
	}{
		{"decimal32", Decimal32Context, 7, -95, 96, -101},
		{"decimal64", Decimal64Context, 16, -383, 384, -398},
		{"decimal128", Decimal128Context, 34, -6143, 6144, -6176},
	} {
		t.Run(tc.name, func(t *testing.T) {
			first, second := tc.make(), tc.make()
			assertPreset := func(label string, c Context, wantTraps Conditions) {
				t.Helper()
				g, enabled := c.ExponentGuards()
				if c.Precision() != tc.p || c.Rounding() != TiesToEven || c.Traps() != wantTraps || !enabled || g != (ExponentGuards{Emin: tc.emin, Emax: tc.emax}) || int64(g.Emin)-int64(tc.p-1) != int64(tc.etiny) {
					t.Fatalf("%s preset = %+v, guard %+v enabled=%v; want traps %v", label, c, g, enabled, wantTraps)
				}
			}
			assertPreset("first before derivation", first, 0)
			assertPreset("second before derivation", second, 0)
			derived, err := first.WithTraps(Inexact)
			if err != nil {
				t.Fatalf("preset derivation: %v", err)
			}
			assertPreset("first after derivation", first, 0)
			assertPreset("second after derivation", second, 0)
			assertPreset("derived", derived, Inexact)
		})
	}
}

func TestContextSharedConcurrentUse(t *testing.T) {
	input := ExponentGuards{Emin: -383, Emax: 384}
	shared, err := NewContext(16, TiesToEven, &input, Inexact)
	if err != nil {
		t.Fatal(err)
	}
	input = ExponentGuards{Emin: 99, Emax: 100}
	var wg sync.WaitGroup
	wrong := make(chan struct{}, 32)
	for range 32 {
		wg.Go(func() {
			for range 200 {
				g, enabled := shared.ExponentGuards()
				derived, deriveErr := shared.WithTraps(Rounded)
				if !enabled || g != (ExponentGuards{Emin: -383, Emax: 384}) || shared.Precision() != 16 || shared.Rounding() != TiesToEven || shared.Traps() != Inexact || deriveErr != nil || derived.Traps() != Rounded || derived.Precision() != 16 {
					wrong <- struct{}{}
					return
				}
			}
		})
	}
	wg.Wait()
	close(wrong)
	if len(wrong) != 0 {
		t.Fatal("shared context changed during concurrent reads and derivations")
	}
}

func TestContextArithmeticZeroPrecision(t *testing.T) {
	a, b := MustParse("1.10"), MustParse("-2.5")
	for _, tc := range []struct {
		name    string
		bare    func(Decimal, Decimal) (Decimal, error)
		context func(Decimal, Decimal, Context) (Decimal, Conditions, error)
		budget  func(Decimal, Decimal, Context, Budget) (Decimal, Conditions, error)
	}{
		{"add", Decimal.Add, Decimal.AddWithContext, addWithContextAndBudget},
		{"sub", Decimal.Sub, Decimal.SubWithContext, subWithContextAndBudget},
		{"mul", Decimal.Mul, Decimal.MulWithContext, mulWithContextAndBudget},
	} {
		t.Run(tc.name, func(t *testing.T) {
			want, wantErr := tc.bare(a, b)
			for _, call := range []func() (Decimal, Conditions, error){
				func() (Decimal, Conditions, error) { return tc.context(a, b, Context{}) },
				func() (Decimal, Conditions, error) { return tc.budget(a, b, Context{}, Budget{}) },
			} {
				got, cond, err := call()
				if wantErr != nil || err != nil || cond != 0 || got.coefficientDigits() != want.coefficientDigits() || got.exponent() != want.exponent() || got.negative() != want.negative() {
					t.Fatalf("zero context: coefficient %s e%d sign %v conditions %v error %v; want %s e%d sign %v error %v", got.coefficientDigits(), got.exponent(), got.negative(), cond, err, want.coefficientDigits(), want.exponent(), want.negative(), wantErr)
				}
			}
		})
	}
	got, cond, err := New(1, math.MaxInt32).MulWithContext(New(1, 1), Context{})
	var operation *Error
	if !reflect.DeepEqual(got, Decimal{}) || cond != 0 || !errors.Is(err, ErrExponentRange) || !errors.As(err, &operation) || operation.Op != "MulWithContext" || operation.Condition != 0 {
		t.Fatalf("short method range identity: %+v, %v, %v", got, cond, err)
	}
	got, cond, err = One().AddWithContext(One(), Context{}.WithBudget(Budget{MaxWork: 3}))
	if !reflect.DeepEqual(got, Decimal{}) || cond != 0 || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != "AddWithContext" || operation.Condition != InsufficientStorage {
		t.Fatalf("budget method resource identity: %+v, %v, %v", got, cond, err)
	}
}

func TestConditionErrorTotalAndMultiCause(t *testing.T) {
	var nilError *Error
	if nilError.Error() == "" || nilError.Unwrap() != nil {
		t.Fatal("nil Error is not total")
	}
	var zero Error
	if zero.Error() == "" || zero.Unwrap() != nil {
		t.Fatal("zero Error is not total")
	}
	err := &Error{Op: "MulWithContext", Condition: Inexact | Rounded | Overflow}
	if !errors.Is(err, ErrInexact) || !errors.Is(err, ErrRounded) || !errors.Is(err, ErrOverflow) || errors.Is(err, ErrUnderflow) {
		t.Fatalf("multi-cause identity: %v", err.Unwrap())
	}
	if err.Unwrap() != nil {
		t.Fatalf("trapped set unwraps to %v; want nil (Is matches each code)", err.Unwrap())
	}
}

func TestContextArithmeticZeroPrecisionPositiveBudgetParity(t *testing.T) {
	cases := []struct {
		name, operation string
		a, b            Decimal
		budget          Budget
		coefficient     string // Empty means checked resource refusal.
		exponent        int32
		negative        bool
	}{
		{"add both zero", "add", New(0, -3), New(0, 2), Budget{MaxDigits: 1, MaxWork: 1}, "0", -3, false},
		{"add one nonzero work below", "add", New(12, 2), Zero(), Budget{MaxDigits: 4, MaxWork: 3}, "", 0, false},
		{"add one nonzero digit below", "add", New(12, 2), Zero(), Budget{MaxDigits: 3, MaxWork: 4}, "", 0, false},
		{"add one nonzero admitted", "add", New(12, 2), Zero(), Budget{MaxDigits: 4, MaxWork: 4}, "1200", 0, false},
		{"add no carry work below", "add", One(), One(), Budget{MaxDigits: 1, MaxWork: 3}, "", 0, false},
		{"add no carry admitted", "add", One(), One(), Budget{MaxDigits: 1, MaxWork: 4}, "2", 0, false},
		{"add carry work below", "add", New(9, 0), One(), Budget{MaxDigits: 2, MaxWork: 3}, "", 0, false},
		{"add carry digit below", "add", New(9, 0), One(), Budget{MaxDigits: 1, MaxWork: 4}, "", 0, false},
		{"add carry admitted", "add", New(9, 0), One(), Budget{MaxDigits: 2, MaxWork: 4}, "10", 0, false},
		{"sub cancellation work below", "sub", New(100, -2), New(100, -2), Budget{MaxDigits: 1, MaxWork: 5}, "", 0, false},
		{"sub cancellation admitted", "sub", New(100, -2), New(100, -2), Budget{MaxDigits: 1, MaxWork: 6}, "0", -2, false},
		{"sub unequal work below", "sub", New(2, -1), New(7, -1), Budget{MaxDigits: 1, MaxWork: 4}, "", 0, false},
		{"sub unequal admitted", "sub", New(2, -1), New(7, -1), Budget{MaxDigits: 1, MaxWork: 5}, "5", -1, true},
		{"sub effective same sign carry digit below", "sub", New(9, 0), New(-1, 0), Budget{MaxDigits: 1, MaxWork: 4}, "", 0, false},
		{"sub effective same sign carry admitted", "sub", New(9, 0), New(-1, 0), Budget{MaxDigits: 2, MaxWork: 4}, "10", 0, false},
		{"mul zero admitted", "mul", New(0, -3), New(123, 2), Budget{MaxDigits: 1, MaxWork: 1}, "0", -1, false},
		{"mul tiles work below", "mul", MustParse(strings.Repeat("9", 19)), MustParse(strings.Repeat("9", 19)), Budget{MaxDigits: 38, MaxWork: 46}, "", 0, false},
		{"mul tiles digit below", "mul", MustParse(strings.Repeat("9", 19)), MustParse(strings.Repeat("9", 19)), Budget{MaxDigits: 37, MaxWork: 47}, "", 0, false},
		{"mul tiles admitted", "mul", MustParse(strings.Repeat("9", 19)), MustParse(strings.Repeat("9", 19)), Budget{MaxDigits: 38, MaxWork: 47}, "", 0, false},
	}
	// The 19-by-19 product has 38 digits; compute its content independently of
	// either the bare or the context method before checking the exact preferred cohort.
	product, _, _, _ := contextOracle(MustParse(strings.Repeat("9", 19)), MustParse(strings.Repeat("9", 19)), "mul", 38, TiesToEven)
	cases[len(cases)-1].coefficient = product
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			var bare Decimal
			var bareErr error
			var got Decimal
			var conditions Conditions
			var err error
			var bareOp, contextOp string
			switch tc.operation {
			case "add":
				bare, bareErr = tc.a.addSub(tc.b, tc.budget.arith(), "AddWithContext", false)
				got, conditions, err = tc.a.AddWithContext(tc.b, Context{}.WithBudget(tc.budget))
				bareOp, contextOp = "AddWithContext", "AddWithContext"
			case "sub":
				bare, bareErr = tc.a.addSub(tc.b, tc.budget.arith(), "SubWithContext", true)
				got, conditions, err = tc.a.SubWithContext(tc.b, Context{}.WithBudget(tc.budget))
				bareOp, contextOp = "SubWithContext", "SubWithContext"
			case "mul":
				bare, bareErr = tc.a.multiply(tc.b, tc.budget.arith(), "MulWithContext")
				got, conditions, err = tc.a.MulWithContext(tc.b, Context{}.WithBudget(tc.budget))
				bareOp, contextOp = "MulWithContext", "MulWithContext"
			}
			if conditions != 0 {
				t.Fatalf("p=0 returned conditions %v", conditions)
			}
			if tc.coefficient == "" {
				for _, pair := range []struct {
					value Decimal
					err   error
					op    string
				}{{bare, bareErr, bareOp}, {got, err, contextOp}} {
					var operation *Error
					if !reflect.DeepEqual(pair.value, Decimal{}) || !errors.Is(pair.err, ErrInsufficientStorage) || !errors.As(pair.err, &operation) || operation.Op != pair.op || operation.Condition != InsufficientStorage {
						t.Fatalf("%s refusal: value %+v error %v", pair.op, pair.value, pair.err)
					}
				}
				return
			}
			if bareErr != nil || err != nil {
				t.Fatalf("admission: bare error %v, context error %v", bareErr, err)
			}
			for _, value := range []Decimal{bare, got} {
				if value.coefficientDigits() != tc.coefficient || value.exponent() != tc.exponent || value.negative() != tc.negative {
					t.Fatalf("admission: coefficient %s exponent %d sign %v; want %s e%d sign %v", value.coefficientDigits(), value.exponent(), value.negative(), tc.coefficient, tc.exponent, tc.negative)
				}
			}
		})
	}
}

func TestContextArithmeticConcurrentSharedOperandsAndContext(t *testing.T) {
	a := MustParse("1" + strings.Repeat("0", 39) + "1")
	b := MustParse(strings.Repeat("9", 40))
	if a.slow == nil || b.slow == nil {
		t.Fatal("concurrent test needs shared slow coefficients")
	}
	guardInput := &ExponentGuards{Emin: -100, Emax: 100}
	ctx, err := NewContext(41, TiesToEven, guardInput, Inexact)
	if err != nil {
		t.Fatal(err)
	}
	budget := Budget{MaxDigits: 41, MaxWork: 206}
	aBefore, bBefore, ctxBefore := a, b, ctx
	aLimbs, bLimbs := slices.Clone(a.slow.limbs), slices.Clone(b.slow.limbs)
	type operation struct {
		name, kind  string
		call        func() (Decimal, Conditions, error)
		coefficient string
		exponent    int64
		negative    bool
		conditions  Conditions
		trapped     Conditions
		held        Decimal
	}
	ops := []operation{
		{name: "AddWithContext", kind: "add", call: func() (Decimal, Conditions, error) { return a.AddWithContext(b, ctx) }},
		{name: "SubWithContext", kind: "sub", call: func() (Decimal, Conditions, error) { return a.SubWithContext(b, ctx) }},
		{name: "MulWithContext", kind: "mul", call: func() (Decimal, Conditions, error) { return a.MulWithContext(b, ctx) }},
		{name: "AddWithContext", kind: "add", call: func() (Decimal, Conditions, error) { return a.AddWithContext(b, ctx.WithBudget(budget)) }},
		{name: "SubWithContext", kind: "sub", call: func() (Decimal, Conditions, error) { return a.SubWithContext(b, ctx.WithBudget(budget)) }},
		{name: "MulWithContext", kind: "mul", call: func() (Decimal, Conditions, error) { return a.MulWithContext(b, ctx.WithBudget(budget)) }},
	}
	for i := range ops {
		entry := &ops[i]
		entry.coefficient, entry.exponent, entry.negative, entry.conditions = contextOracle(a, b, entry.kind, 41, TiesToEven)
		entry.trapped = entry.conditions & Inexact
		entry.conditions &^= Inexact
		if entry.kind == "mul" && (entry.trapped != Inexact || entry.conditions != Rounded|Increased) || entry.kind != "mul" && (entry.trapped != 0 || entry.conditions != 0) {
			t.Fatalf("independent operation conditions for %s: returned %v, trapped %v", entry.name, entry.conditions, entry.trapped)
		}
		entry.held, _, _ = entry.call()
	}
	check := func(entry operation) bool {
		got, conditions, err := entry.call()
		if got.coefficientDigits() != entry.coefficient || int64(got.exponent()) != entry.exponent || got.negative() != entry.negative || conditions != entry.conditions {
			t.Errorf("shared %s: coefficient %s exponent %d sign %v conditions %v", entry.name, got.coefficientDigits(), got.exponent(), got.negative(), conditions)
			return false
		}
		if entry.trapped == 0 {
			if err != nil {
				t.Errorf("shared %s: unexpected error %v", entry.name, err)
				return false
			}
			return true
		}
		var condition *Error
		if !errors.As(err, &condition) || condition.Code != 0 || condition.Op != entry.name || condition.Condition != entry.trapped || !errors.Is(err, ErrInexact) || errors.Is(err, ErrRounded) {
			t.Errorf("shared %s: trap %v", entry.name, err)
			return false
		}
		return true
	}
	const workers, repetitions = 12, 50
	start := make(chan struct{})
	begun, resume := make(chan struct{}), make(chan struct{})
	var begunOnce sync.Once
	var group sync.WaitGroup
	for range workers {
		group.Go(func() {
			<-start
			for range repetitions {
				for _, entry := range ops {
					ok := check(entry)
					begunOnce.Do(func() {
						close(begun)
						<-resume
					})
					if !ok {
						return
					}
				}
			}
		})
	}
	close(start)
	<-begun
	// Context owns a copy of the caller's guards even while many goroutines
	// use the same context. Derivation must also leave that value unchanged.
	guardInput.Emin, guardInput.Emax = 50, 50
	derived, deriveErr := ctx.WithTraps(Rounded)
	pair, guarded := ctx.ExponentGuards()
	close(resume)
	group.Wait()
	if deriveErr != nil || derived.Traps() != Rounded || ctx.Traps() != Inexact {
		t.Fatalf("shared context derivation: derived traps %v, original traps %v, error %v", derived.Traps(), ctx.Traps(), deriveErr)
	}
	if !guarded || pair != ctxBefore.guards {
		t.Fatalf("shared context guard input leaked: %+v guarded %v", pair, guarded)
	}
	if !reflect.DeepEqual(a, aBefore) || !reflect.DeepEqual(b, bBefore) || !slices.Equal(a.slow.limbs, aLimbs) || !slices.Equal(b.slow.limbs, bLimbs) || ctx != ctxBefore {
		t.Fatal("shared operand or context changed")
	}
	for _, entry := range ops {
		if entry.held.coefficientDigits() != entry.coefficient || int64(entry.held.exponent()) != entry.exponent || entry.held.negative() != entry.negative {
			t.Fatalf("held result of %s changed after concurrent calls", entry.name)
		}
	}
}

func TestContextArithmeticRoundsOnce(t *testing.T) {
	ctx, err := NewContext(2, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name            string
		call            func() (Decimal, Conditions, error)
		wantCoefficient string
		wantExponent    int32
		direction       Conditions // 1.2 < 1.234; 410 > 408.
	}{
		{"add", func() (Decimal, Conditions, error) { return MustParse("1.234").AddWithContext(Zero(), ctx) }, "12", -1, Decreased},
		{"sub", func() (Decimal, Conditions, error) { return MustParse("1.234").SubWithContext(Zero(), ctx) }, "12", -1, Decreased},
		{"mul", func() (Decimal, Conditions, error) {
			return New(12, 0).MulWithContext(New(34, 0), ctx.WithBudget(Budget{MaxDigits: 2, MaxWork: 10}))
		}, "41", 1, Increased},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			if err != nil || got.coefficientDigits() != tc.wantCoefficient || got.exponent() != tc.wantExponent || conditions != Inexact|Rounded|tc.direction {
				t.Fatalf("got coefficient %s exponent %d conditions %v error %v; want %s e%d %v", got.coefficientDigits(), got.exponent(), conditions, err, tc.wantCoefficient, tc.wantExponent, Inexact|Rounded|tc.direction)
			}
		})
	}
}

func TestContextPreferredScaleBareAndZeroContext(t *testing.T) {
	for _, tc := range []struct {
		name, left, right, want, coefficient string
		exponent                             int32
		bare                                 func(Decimal, Decimal) (Decimal, error)
		context                              func(Decimal, Decimal, Context) (Decimal, Conditions, error)
	}{
		{"add 1.10 plus zero", "1.10", "0", "1.10", "110", -2, Decimal.Add, Decimal.AddWithContext},
		{"mul 1.10 times 2.5", "1.10", "2.5", "2.750", "2750", -3, Decimal.Mul, Decimal.MulWithContext},
	} {
		t.Run(tc.name, func(t *testing.T) {
			a, b := MustParse(tc.left), MustParse(tc.right)
			bare, err := tc.bare(a, b)
			if err != nil {
				t.Fatal(err)
			}
			got, conditions, err := tc.context(a, b, Context{})
			if err != nil || conditions != 0 {
				t.Fatalf("unrounded context: conditions %v, error %v", conditions, err)
			}
			for _, result := range []Decimal{bare, got} {
				if result.coefficientDigits() != tc.coefficient || result.exponent() != tc.exponent || result.negative() {
					t.Fatalf("preferred cohort: coefficient %s e%d sign%v; want %s e%d", result.coefficientDigits(), result.exponent(), result.negative(), tc.coefficient, tc.exponent)
				}
				text, err := result.Text(0)
				if err != nil || text != tc.want {
					t.Fatalf("preferred cohort: %q, %v; want %q", text, err, tc.want)
				}
			}
		})
	}
}

func TestContextMulTileCharge(t *testing.T) {
	a, b := New(12, 0), New(34, 0)
	product := "408" // Independent small integer multiplication: 12 * 34.
	for _, tc := range []struct {
		name    string
		context Context
		base    uint64
		final   uint64
		want    string
		exp     int32
		flags   Conditions
	}{
		{"p0", Context{}, 5, 5, product, 0, 0},
		{"p2", contextTestContext(t, 2, TiesToEven, nil, 0), 5, 10, "41", 1, Inexact | Rounded | Increased},
	} {
		t.Run(tc.name, func(t *testing.T) {
			for cap := uint64(4); cap <= tc.final; cap++ {
				budget := Budget{MaxWork: cap}
				if tc.name == "p0" {
					bare, _, err := a.MulWithContext(b, Context{}.WithBudget(budget))
					if cap < tc.final {
						var operation *Error
						if !reflect.DeepEqual(bare, Decimal{}) || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != "MulWithContext" || operation.Condition != InsufficientStorage {
							t.Fatalf("bare cap %d: value %+v, error %v", cap, bare, err)
						}
					} else if err != nil || bare.coefficientDigits() != product || bare.exponent() != 0 || bare.negative() {
						t.Fatalf("bare cap %d: coefficient %s e%d sign%v err%v", cap, bare.coefficientDigits(), bare.exponent(), bare.negative(), err)
					}
				}
				got, conditions, err := a.MulWithContext(b, tc.context.WithBudget(budget))
				if cap < tc.final {
					var operation *Error
					if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != "MulWithContext" || operation.Condition != InsufficientStorage {
						t.Fatalf("context %s cap %d: value %+v, conditions %v, error %v", tc.name, cap, got, conditions, err)
					}
				} else if err != nil || got.coefficientDigits() != tc.want || got.exponent() != tc.exp || got.negative() || conditions != tc.flags {
					t.Fatalf("context %s cap %d: coefficient %s e%d sign%v conditions %v err%v", tc.name, cap, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
				}
			}
		})
	}
	// A large low-work refusal must not materialize a coefficient-sized
	// product before the documented B precharge is admitted.
	large := MustParse(strings.Repeat("9", 10_000))
	ctx := contextTestContext(t, 2, TiesToEven, nil, 0)
	var result Decimal
	var conditions Conditions
	var err error
	allocs := testing.AllocsPerRun(20, func() {
		result, conditions, err = large.MulWithContext(large, ctx.WithBudget(Budget{MaxWork: 4}))
	})
	if !reflect.DeepEqual(result, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("large precharge: value %+v, conditions %v, error %v", result, conditions, err)
	}
	if allocs > 1 {
		t.Fatalf("low-work Mul allocated %.0f times per call; want at most typed error", allocs)
	}
}

func TestContextConditionAndTrapIsolation(t *testing.T) {
	ctx := contextTestContext(t, 2, TiesToEven, nil, 0)
	trapped, err := ctx.WithTraps(Inexact)
	if err != nil || ctx.Traps() != 0 || trapped.Traps() != Inexact {
		t.Fatalf("trap derivation changed original: original %v, derived %v, error %v", ctx.Traps(), trapped.Traps(), err)
	}
	source := MustParse("1.234")
	checkFinite := func(label string, context Context, want Conditions, trappedInexact bool) {
		t.Helper()
		got, conditions, err := source.AddWithContext(Zero(), context)
		if got.coefficientDigits() != "12" || got.exponent() != -1 || got.negative() || conditions != want {
			t.Fatalf("%s: coefficient %s e%d sign%v conditions %v, want %v", label, got.coefficientDigits(), got.exponent(), got.negative(), conditions, want)
		}
		var condition *Error
		if trappedInexact {
			if !errors.As(err, &condition) || condition.Code != 0 || condition.Op != "AddWithContext" || condition.Condition != Inexact || !errors.Is(err, ErrInexact) || errors.Is(err, ErrRounded) {
				t.Fatalf("%s: trapped identity %v", label, err)
			}
		} else if err != nil {
			t.Fatalf("%s: unexpected trap %v", label, err)
		}
	}
	// 1.2 < 1.234, and a trapped Inexact keeps the direction bit.
	checkFinite("untrapped first", ctx, Inexact|Rounded|Decreased, false)
	checkFinite("trapped", trapped, Rounded|Decreased, true)
	zeroOnly, conditions, err := MustParse("1.00").AddWithContext(Zero(), ctx)
	if err != nil || zeroOnly.coefficientDigits() != "10" || zeroOnly.exponent() != -1 || conditions != Rounded {
		t.Fatalf("zero-only: coefficient %s e%d conditions %v error %v", zeroOnly.coefficientDigits(), zeroOnly.exponent(), conditions, err)
	}
	exact, conditions, err := One().AddWithContext(Zero(), ctx)
	if err != nil || exact.coefficientDigits() != "1" || exact.exponent() != 0 || conditions != 0 {
		t.Fatalf("following exact call: coefficient %s e%d conditions %v error %v", exact.coefficientDigits(), exact.exponent(), conditions, err)
	}
	checkFinite("untrapped again", ctx, Inexact|Rounded|Decreased, false)
	guarded := contextTestContext(t, 3, TiesToEven, &ExponentGuards{Emin: -2, Emax: 2}, 0)
	boundary, conditions, err := MustParse("1000").MulWithContext(One(), guarded)
	if err != nil || boundary.coefficientDigits() != "999" || boundary.exponent() != 0 || boundary.negative() || conditions != Overflow|Inexact|Rounded|Decreased {
		t.Fatalf("untrapped boundary: coefficient %s e%d sign%v conditions %v error %v", boundary.coefficientDigits(), boundary.exponent(), boundary.negative(), conditions, err)
	}
	guardedTrap, err := guarded.WithTraps(Overflow)
	if err != nil || guarded.Traps() != 0 {
		t.Fatalf("guarded trap derivation: original %v, error %v", guarded.Traps(), err)
	}
	trappedBoundary, conditions, err := MustParse("1000").MulWithContext(One(), guardedTrap)
	var boundaryError *Error
	if trappedBoundary.coefficientDigits() != "999" || trappedBoundary.exponent() != 0 || trappedBoundary.negative() || conditions != Inexact|Rounded|Decreased || !errors.As(err, &boundaryError) || boundaryError.Op != "MulWithContext" || boundaryError.Condition != Overflow || !errors.Is(err, ErrOverflow) {
		t.Fatalf("trapped boundary: coefficient %s e%d sign%v conditions %v error %v", trappedBoundary.coefficientDigits(), trappedBoundary.exponent(), trappedBoundary.negative(), conditions, err)
	}
}

func TestContextGuardedBoundaries(t *testing.T) {
	guards := &ExponentGuards{Emin: -2, Emax: 2}
	for _, tc := range []struct {
		name, input, want string
		mode              RoundingMode
		conditions        Conditions
	}{
		{"round first", "999.1", "999", TiesToEven, Inexact | Rounded | Decreased},
		{"then overflow", "999.1", "999", TowardPositiveInfinity, Overflow | Inexact | Rounded | Decreased},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx := contextTestContext(t, 3, tc.mode, guards, 0)
			got, conditions, err := MustParse(tc.input).MulWithContext(One(), ctx)
			if err != nil || got.coefficientDigits() != tc.want || got.exponent() != 0 || got.negative() || conditions != tc.conditions {
				t.Fatalf("%s: coefficient %s e%d sign%v conditions %v error %v", tc.name, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
			}
		})
	}
	for _, tc := range []struct {
		name, want string
		mode       RoundingMode
		direction  Conditions
	}{
		{"negative toward positive", "-0.0012", TowardPositiveInfinity, Increased},
		{"negative toward negative", "-0.0013", TowardNegativeInfinity, Decreased},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx := contextTestContext(t, 3, tc.mode, guards, 0)
			got, conditions, err := MustParse("-0.00123").MulWithContext(One(), ctx)
			text, textErr := got.Text(0)
			if err != nil || textErr != nil || text != tc.want || conditions != Subnormal|Underflow|Inexact|Rounded|tc.direction {
				t.Fatalf("%s: text %s conditions %v errors %v/%v", tc.name, text, conditions, err, textErr)
			}
		})
	}
	for _, negative := range []bool{false, true} {
		input := New(1, -5)
		if negative {
			input = New(-1, -5)
		}
		for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity} {
			ctx := contextTestContext(t, 3, mode, guards, 0)
			got, conditions, err := input.MulWithContext(One(), ctx)
			away := mode == AwayFromZero || mode == TowardPositiveInfinity && !negative || mode == TowardNegativeInfinity && negative
			wantDigits := "0"
			if away {
				wantDigits = "1"
			}
			direction := oracleDirection(quantizeOracleRat(wantDigits, -4, away && negative), quantizeOracleRat("1", -5, negative))
			if err != nil || got.coefficientDigits() != wantDigits || got.exponent() != -4 || got.negative() != (away && negative) || conditions != Subnormal|Underflow|Inexact|Rounded|direction {
				t.Fatalf("tiny sign%v mode%d: coefficient %s e%d sign%v conditions %v error %v", negative, mode, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
			}
		}
	}
}

func TestBareArithmeticHasNoGuardEvents(t *testing.T) {
	// These exact operands lie above the guarded p=3/Emax=2 Bmax used in the
	// context tests. Bare methods have neither a guard argument nor a
	// condition channel, so they retain the exact value and ideal cohort.
	for _, tc := range []struct {
		name string
		call func() (Decimal, error)
	}{
		{"Add", func() (Decimal, error) { return MustParse("1000").Add(Zero()) }},
		{"Sub", func() (Decimal, error) { return MustParse("1000").Sub(Zero()) }},
		{"Mul", func() (Decimal, error) { return MustParse("1000").Mul(One()) }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := tc.call()
			if err != nil || got.coefficientDigits() != "1000" || got.exponent() != 0 || got.negative() {
				t.Fatalf("bare guard leakage: coefficient %s e%d sign%v error %v", got.coefficientDigits(), got.exponent(), got.negative(), err)
			}
		})
	}
}

func TestExactZeroPreferredExponentAcrossBareAndContext(t *testing.T) {
	guarded := contextTestContext(t, 3, TiesToEven, &ExponentGuards{Emin: -2, Emax: 2}, 0)
	for _, tc := range []struct {
		name     string
		bare     func() (Decimal, error)
		context  func(Context) (Decimal, Conditions, error)
		exponent int32
	}{
		{"Add differing exponents", func() (Decimal, error) { return New(1, -9).Add(New(-10, -10)) }, func(c Context) (Decimal, Conditions, error) { return New(1, -9).AddWithContext(New(-10, -10), c) }, -10},
		{"Sub differing exponents", func() (Decimal, error) { return New(1, -9).Sub(New(10, -10)) }, func(c Context) (Decimal, Conditions, error) { return New(1, -9).SubWithContext(New(10, -10), c) }, -10},
		{"Mul zero", func() (Decimal, error) { return New(0, -7).Mul(New(-3, -3)) }, func(c Context) (Decimal, Conditions, error) { return New(0, -7).MulWithContext(New(-3, -3), c) }, -10},
	} {
		t.Run(tc.name, func(t *testing.T) {
			bare, err := tc.bare()
			if err != nil || !bare.isZero() || bare.exponent() != tc.exponent || bare.negative() {
				t.Fatalf("bare exact zero: %+v, %v", bare, err)
			}
			for _, c := range []Context{{}, guarded} {
				got, conditions, err := tc.context(c)
				if err != nil || conditions != 0 || !got.isZero() || got.exponent() != tc.exponent || got.negative() {
					t.Fatalf("context exact zero: %+v, conditions %v, error %v", got, conditions, err)
				}
			}
		})
	}
	tiny, conditions, err := New(1, -5).MulWithContext(One(), guarded)
	if err != nil || !tiny.isZero() || tiny.exponent() != -4 || tiny.negative() || conditions != Subnormal|Underflow|Inexact|Rounded|Decreased {
		t.Fatalf("rounded tiny zero uses Etiny: %+v, conditions %v, error %v", tiny, conditions, err)
	}
}

func contextTestContext(t *testing.T, precision uint32, mode RoundingMode, guards *ExponentGuards, traps Conditions) Context {
	t.Helper()
	ctx, err := NewContext(precision, mode, guards, traps)
	if err != nil {
		t.Fatal(err)
	}
	return ctx
}

func contextTestCoefficient(d Decimal) *big.Int {
	value, ok := new(big.Int).SetString(d.coefficientDigits(), 10)
	if !ok {
		panic("invalid test coefficient")
	}
	if d.negative() {
		value.Neg(value)
	}
	return value
}

// contextOracle uses only math/big decimal integer arithmetic; it does not
// inspect the production stream, coefficient limbs or rounding helpers.
func contextOracle(a, b Decimal, operation string, precision uint32, mode RoundingMode) (string, int64, bool, Conditions) {
	var exact *big.Int
	var exponent int64
	if operation == "mul" {
		exact = new(big.Int).Mul(contextTestCoefficient(a), contextTestCoefficient(b))
		exponent = int64(a.exponent()) + int64(b.exponent())
	} else {
		exponent = int64(min(a.exponent(), b.exponent()))
		powerA := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(a.exponent())-exponent), nil)
		powerB := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(b.exponent())-exponent), nil)
		left := new(big.Int).Mul(contextTestCoefficient(a), powerA)
		right := new(big.Int).Mul(contextTestCoefficient(b), powerB)
		if operation == "sub" {
			exact = new(big.Int).Sub(left, right)
		} else {
			exact = new(big.Int).Add(left, right)
		}
	}
	negative := exact.Sign() < 0
	if negative {
		exact.Abs(exact)
	}
	if exact.Sign() == 0 {
		return "0", exponent, false, 0
	}
	digits := len(exact.String())
	if digits <= int(precision) {
		return exact.String(), exponent, negative, 0
	}
	cut := digits - int(precision)
	divisor := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(cut)), nil)
	quotient, remainder := new(big.Int), new(big.Int)
	quotient.QuoRem(exact, divisor, remainder)
	conditions := Rounded
	if remainder.Sign() != 0 {
		conditions |= Inexact
	}
	double := new(big.Int).Lsh(remainder, 1)
	comparison := double.Cmp(divisor)
	up := false
	switch mode {
	case TiesToEven:
		up = comparison > 0 || comparison == 0 && quotient.Bit(0) == 1
	case TiesAwayFromZero:
		up = comparison >= 0
	case TiesTowardZero:
		up = comparison > 0
	case TowardZero:
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
	sourceExponent := exponent
	exponent += int64(cut)
	if len(quotient.String()) > int(precision) {
		quotient.Quo(quotient, big.NewInt(10))
		exponent++
	}
	if conditions&Inexact != 0 {
		// Compare the oracle's rounded value with the exact result, both
		// scaled to the exact result's exponent.
		scale := new(big.Int).Exp(big.NewInt(10), big.NewInt(exponent-sourceExponent), nil)
		rounded := new(big.Int).Mul(quotient, scale)
		signedExact := new(big.Int).Set(exact)
		if negative {
			rounded.Neg(rounded)
			signedExact.Neg(signedExact)
		}
		conditions |= oracleDirection(new(big.Rat).SetInt(rounded), new(big.Rat).SetInt(signedExact))
	}
	return quotient.String(), exponent, negative, conditions
}

func TestContextArithmeticUngardedModesBigOracle(t *testing.T) {
	for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity} {
		ctx := contextTestContext(t, 2, mode, nil, 0)
		for _, operation := range []string{"add", "sub", "mul"} {
			for _, source := range []string{"1.25", "1.251", "1.24", "1.26", "-1.25", "-1.251", "-1.24", "-1.26", "9.99", "-9.99"} {
				a, b := MustParse(source), Zero()
				if operation == "mul" {
					b = One()
				}
				var got Decimal
				var conditions Conditions
				var err error
				switch operation {
				case "add":
					got, conditions, err = a.AddWithContext(b, ctx)
				case "sub":
					got, conditions, err = a.SubWithContext(b, ctx)
				case "mul":
					got, conditions, err = a.MulWithContext(b, ctx)
				}
				wantDigits, wantExponent, wantNegative, wantConditions := contextOracle(a, b, operation, 2, mode)
				if err != nil || got.coefficientDigits() != wantDigits || int64(got.exponent()) != wantExponent || got.negative() != wantNegative || conditions != wantConditions {
					t.Fatalf("%s %s mode %d: got %s e%d sign %v conditions %v err %v; want %s e%d sign %v conditions %v", operation, source, mode, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, wantDigits, wantExponent, wantNegative, wantConditions)
				}
			}
		}
	}
	// Exact is the eighth mode. A nonzero precision cut has no
	// numerical-mode rounded candidate, while removing only zeros is exact
	// and still reports Rounded. Check both signs across all three methods.
	exact := contextTestContext(t, 2, Exact, nil, 0)
	call := func(a, b Decimal, operation string) (Decimal, Conditions, error) {
		switch operation {
		case "add":
			return a.AddWithContext(b, exact)
		case "sub":
			return a.SubWithContext(b, exact)
		case "mul":
			return a.MulWithContext(b, exact)
		}
		t.Fatalf("unknown operation %q", operation)
		return Decimal{}, 0, nil
	}
	for _, operation := range []string{"add", "sub", "mul"} {
		for _, source := range []string{"1.25", "1.251", "1.24", "1.26", "-1.25", "-1.251", "-1.24", "-1.26"} {
			a, b := MustParse(source), Zero()
			if operation == "mul" {
				b = One()
			}
			got, conditions, err := call(a, b, operation)
			var refusal *Error
			if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.As(err, &refusal) || refusal.Condition != Inexact || !errors.Is(err, ErrInexact) || errors.Is(err, ErrRounded) {
				t.Fatalf("Exact %s %s: value %+v conditions %v error %v", operation, source, got, conditions, err)
			}
		}
		for _, source := range []string{"1.200", "-1.200"} {
			a, b := MustParse(source), Zero()
			if operation == "mul" {
				b = One()
			}
			got, conditions, err := call(a, b, operation)
			if err != nil || got.coefficientDigits() != "12" || got.exponent() != -1 || got.negative() != strings.HasPrefix(source, "-") || conditions != Rounded {
				t.Fatalf("Exact zero-only %s %s: coefficient %s e%d sign%v conditions %v error %v", operation, source, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
			}
		}
	}
}

func TestContextMulLargeConvolutionBigOracle(t *testing.T) {
	a := MustParse(strings.Repeat("739182645", 1111) + "7")
	b := MustParse(strings.Repeat("845291736", 1111) + "8")
	for _, precision := range []uint32{34, 20000} {
		ctx := contextTestContext(t, precision, TiesToEven, nil, 0)
		got, conditions, err := a.MulWithContext(b, ctx)
		wantDigits, wantExponent, wantNegative, wantConditions := contextOracle(a, b, "mul", precision, TiesToEven)
		gotDigits := got.coefficientDigits()
		if err != nil || gotDigits != wantDigits || int64(got.exponent()) != wantExponent || got.negative() != wantNegative || conditions != wantConditions {
			t.Fatalf("large Mul p%d: digit lengths %d/%d equal %t, exponent %d/%d, sign %v/%v, conditions %v/%v, err %v", precision, len(gotDigits), len(wantDigits), gotDigits == wantDigits, got.exponent(), wantExponent, got.negative(), wantNegative, conditions, wantConditions, err)
		}
	}
}

func TestContextArithmeticMixedSignBigOracle(t *testing.T) {
	pairs := [][2]string{
		{"123.45", "0.00678"},
		{"-123.45", "0.00678"},
		{"999999999999999999.99", "0.01"},
		{"100000000000000000.00", "-0.01"},
		{"7.0000", "-6.9999"},
		{"-7.0000", "6.9999"},
		{"1E+12", "1E-7"},
		{"-5E-15", "11E+5"},
		{strings.Repeat("9", 38), strings.Repeat("7", 39)},
	}
	for _, precision := range []uint32{1, 3, 7, 16, 34} {
		for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity} {
			ctx := contextTestContext(t, precision, mode, nil, 0)
			for _, texts := range pairs {
				a, b := MustParse(texts[0]), MustParse(texts[1])
				for _, operation := range []string{"add", "sub", "mul"} {
					var got Decimal
					var conditions Conditions
					var err error
					switch operation {
					case "add":
						got, conditions, err = a.AddWithContext(b, ctx)
					case "sub":
						got, conditions, err = a.SubWithContext(b, ctx)
					case "mul":
						got, conditions, err = a.MulWithContext(b, ctx)
					}
					wantDigits, wantExponent, wantNegative, wantConditions := contextOracle(a, b, operation, precision, mode)
					if err != nil || got.coefficientDigits() != wantDigits || int64(got.exponent()) != wantExponent || got.negative() != wantNegative || conditions != wantConditions {
						t.Fatalf("%s %s %s p%d mode%d: got %s e%d sign%v cond%v err%v; want %s e%d sign%v cond%v", operation, texts[0], texts[1], precision, mode, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, wantDigits, wantExponent, wantNegative, wantConditions)
					}
				}
			}
		}
	}
}

func TestContextArithmeticDeterministicBigOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x74120, 0xc9117))
	modes := [...]RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity}
	operand := func() Decimal {
		if rng.IntN(13) == 0 {
			return New(0, int32(rng.IntN(41)-20))
		}
		digits := make([]byte, 1+rng.IntN(50))
		for i := range digits {
			digits[i] = byte('0' + rng.IntN(10))
		}
		digits[0] = byte('1' + rng.IntN(9))
		sign := ""
		if rng.IntN(2) == 0 {
			sign = "-"
		}
		return MustParse(sign + string(digits) + "E" + strconv.Itoa(rng.IntN(41)-20))
	}
	for i := range 800 {
		a, b := operand(), operand()
		precision := uint32(1 + rng.IntN(34))
		mode := modes[i%len(modes)]
		ctx := contextTestContext(t, precision, mode, nil, 0)
		for _, operation := range []string{"add", "sub", "mul"} {
			var got Decimal
			var conditions Conditions
			var err error
			switch operation {
			case "add":
				got, conditions, err = a.AddWithContext(b, ctx)
			case "sub":
				got, conditions, err = a.SubWithContext(b, ctx)
			case "mul":
				got, conditions, err = a.MulWithContext(b, ctx)
			}
			wantDigits, wantExponent, wantNegative, wantConditions := contextOracle(a, b, operation, precision, mode)
			if err != nil || got.coefficientDigits() != wantDigits || int64(got.exponent()) != wantExponent || got.negative() != wantNegative || conditions != wantConditions {
				t.Fatalf("case%d %s p%d mode%d a=%s b=%s: got %s e%d sign%v conditions%v err%v; want %s e%d sign%v conditions%v", i, operation, precision, mode, a, b, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, wantDigits, wantExponent, wantNegative, wantConditions)
			}
		}
	}
}

func TestContextArithmeticFiniteWorkPathCaps(t *testing.T) {
	ctx := contextTestContext(t, 3, TiesToEven, nil, 0)
	for _, tc := range []struct {
		name  string
		call  func(Budget) (Decimal, Conditions, error)
		base  uint64
		final uint64
	}{
		{"add both zero", func(b Budget) (Decimal, Conditions, error) {
			return Zero().AddWithContext(Zero(), ctx.WithBudget(b))
		}, 1, 4},
		{"add one nonzero", func(b Budget) (Decimal, Conditions, error) {
			return New(12, 0).AddWithContext(Zero(), ctx.WithBudget(b))
		}, 2, 7},
		{"add same sign", func(b Budget) (Decimal, Conditions, error) {
			return One().AddWithContext(One(), ctx.WithBudget(b))
		}, 4, 7},
		{"add same sign carry", func(b Budget) (Decimal, Conditions, error) {
			return New(9, 0).AddWithContext(One(), ctx.WithBudget(b))
		}, 4, 9},
		{"sub cancellation", func(b Budget) (Decimal, Conditions, error) {
			return One().SubWithContext(One(), ctx.WithBudget(b))
		}, 2, 5},
		{"sub unequal", func(b Budget) (Decimal, Conditions, error) {
			return New(7, 0).SubWithContext(New(2, 0), ctx.WithBudget(b))
		}, 5, 8},
		{"mul zero", func(b Budget) (Decimal, Conditions, error) {
			return Zero().MulWithContext(One(), ctx.WithBudget(b))
		}, 1, 4},
		{"mul nonzero", func(b Budget) (Decimal, Conditions, error) {
			return New(12, 0).MulWithContext(New(34, 0), ctx.WithBudget(b))
		}, 5, 12},
	} {
		t.Run(tc.name, func(t *testing.T) {
			for _, cap := range []uint64{tc.base - 1, tc.base, tc.final - 1, tc.final} {
				if cap == 0 {
					continue // Zero means unlimited, not a positive B-1 cap.
				}
				got, conditions, err := tc.call(Budget{MaxWork: cap})
				if cap < tc.final {
					if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) {
						t.Fatalf("cap %d: got %+v, %v, %v; want resource refusal", cap, got, conditions, err)
					}
				} else if err != nil {
					t.Fatalf("cap %d: %v", cap, err)
				}
			}
		})
	}
}

func TestContextArithmeticGuardsAndCollision(t *testing.T) {
	guard := &ExponentGuards{Emin: -2, Emax: 2}
	ctx := contextTestContext(t, 3, TiesToEven, guard, 0)
	for _, tc := range []struct {
		name        string
		input       Decimal
		coefficient string
		exponent    int32
		conditions  Conditions
	}{
		{"exact subnormal", New(1, -3), "1", -3, Subnormal},
		{"inexact subnormal", New(12, -5), "1", -4, Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"tiny to zero", New(1, -5), "0", -4, Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"postround overflow", MustParse("999.9"), "999", 0, Overflow | Inexact | Rounded | Decreased},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.input.MulWithContext(One(), ctx)
			if err != nil || got.coefficientDigits() != tc.coefficient || got.exponent() != tc.exponent || conditions != tc.conditions || got.negative() {
				t.Fatalf("got %s e%d sign %v cond %v err %v; want %s e%d cond %v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, tc.coefficient, tc.exponent, tc.conditions)
			}
		})
	}
	zero, conditions, err := New(1, -10).AddWithContext(New(-1, -10), ctx)
	if err != nil || conditions != 0 || !zero.isZero() || zero.exponent() != -10 || zero.negative() {
		t.Fatalf("guarded exact zero: %+v, %v, %v", zero, conditions, err)
	}
	ctx = contextTestContext(t, 1, TiesToEven, &ExponentGuards{Emin: 0, Emax: math.MaxInt32}, Overflow)
	got, conditions, err := New(99, math.MaxInt32).MulWithContext(One(), ctx)
	var trapped *Error
	if got.coefficientDigits() != "9" || got.exponent() != math.MaxInt32 || conditions != Inexact|Rounded|Decreased || !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Condition != Overflow || !errors.Is(err, ErrOverflow) {
		t.Fatalf("guarded range/overflow collision: %s e%d cond %v err %v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
	ctx = contextTestContext(t, 2, TiesToEven, &ExponentGuards{Emin: 0, Emax: math.MaxInt32}, Overflow)
	got, conditions, err = New(999, math.MaxInt32).MulWithContext(One(), ctx.WithBudget(Budget{MaxDigits: 1}))
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("Bmax digit cap before trap: %+v, %v, %v", got, conditions, err)
	}
	got, conditions, err = New(999, math.MaxInt32).MulWithContext(One(), ctx.WithBudget(Budget{MaxDigits: 2}))
	if got.coefficientDigits() != "99" || got.exponent() != math.MaxInt32-1 || conditions != Inexact|Rounded|Decreased || !errors.Is(err, ErrOverflow) {
		t.Fatalf("Bmax admitted trap: %s e%d, %v, %v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
}

func TestContextArithmeticAllModeGuardOverflow(t *testing.T) {
	guards := &ExponentGuards{Emin: -2, Emax: 2}
	for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity} {
		ctx := contextTestContext(t, 3, mode, guards, 0)
		for _, input := range []string{"999.9", "-999.9", "1000", "-1000"} {
			got, conditions, err := MustParse(input).MulWithContext(One(), ctx)
			negative := strings.HasPrefix(input, "-")
			overflow := strings.Contains(input, "1000") || mode == AwayFromZero || mode <= TiesTowardZero || mode == TowardPositiveInfinity && !negative || mode == TowardNegativeInfinity && negative
			wantConditions := Inexact | Rounded
			if overflow {
				wantConditions |= Overflow
			}
			// ±999 is nearer zero than every exact input, whether it is the
			// truncated value or the Bmax substitution.
			if negative {
				wantConditions |= Increased
			} else {
				wantConditions |= Decreased
			}
			if err != nil || got.coefficientDigits() != "999" || got.exponent() != 0 || got.negative() != negative || conditions != wantConditions {
				t.Fatalf("overflow mode%d input%s: coefficient %s e%d sign%v conditions%v err%v", mode, input, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
			}
		}
	}
}

func TestContextArithmeticPreferredCohorts(t *testing.T) {
	ctx := contextTestContext(t, 4, TiesToEven, nil, 0)
	for _, tc := range []struct {
		name        string
		call        func() (Decimal, Conditions, error)
		coefficient string
		exponent    int32
	}{
		{"add with zero", func() (Decimal, Conditions, error) { return MustParse("1.10").AddWithContext(Zero(), ctx) }, "110", -2},
		{"mul exact", func() (Decimal, Conditions, error) { return MustParse("1.10").MulWithContext(MustParse("2.5"), ctx) }, "2750", -3},
		{"signed cancellation", func() (Decimal, Conditions, error) {
			return MustParse("1.100").AddWithContext(MustParse("-1.100"), ctx)
		}, "0", -3},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			if err != nil || conditions != 0 || got.coefficientDigits() != tc.coefficient || got.exponent() != tc.exponent || got.negative() {
				t.Fatalf("cohort: coefficient %s e%d sign%v conditions%v err%v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
			}
		})
	}
}

func TestContextArithmeticExactRangeTrapAndBudgetOrder(t *testing.T) {
	ctx := contextTestContext(t, 2, TiesToEven, nil, 0)
	for _, cap := range []uint64{4, 5, 9, 10} {
		got, conditions, err := New(12, 0).MulWithContext(New(34, 0), ctx.WithBudget(Budget{MaxDigits: 2, MaxWork: cap}))
		if cap < 10 {
			if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("Mul cap %d refusal: %+v, %v, %v", cap, got, conditions, err)
			}
		} else if err != nil || got.coefficientDigits() != "41" || got.exponent() != 1 || conditions != Inexact|Rounded|Increased {
			t.Fatalf("Mul cap 10 admission: %s e%d, %v, %v", got.coefficientDigits(), got.exponent(), conditions, err)
		}
	}
	exact := contextTestContext(t, 2, Exact, nil, 0)
	got, conditions, err := New(12, 0).MulWithContext(New(34, 0), exact.WithBudget(Budget{MaxWork: 5}))
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInexact) {
		t.Fatalf("Exact after admitted B: %+v, %v, %v", got, conditions, err)
	}
	for _, mode := range []RoundingMode{TiesToEven, TowardZero, Exact} {
		ctx = contextTestContext(t, 1, mode, nil, 0)
		got, conditions, err = New(99, math.MaxInt32).MulWithContext(One(), ctx)
		want := ErrExponentRange
		if mode == Exact {
			want = ErrInexact
		}
		if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, want) {
			t.Fatalf("postround exponent mode %d: %+v, %v, %v; want %v", mode, got, conditions, err, want)
		}
	}
	for _, mode := range []RoundingMode{TiesToEven, Exact} {
		ctx = contextTestContext(t, 1, mode, nil, 0)
		for _, cap := range []uint64{3, 4} {
			got, conditions, err = New(99, math.MaxInt32).MulWithContext(One(), ctx.WithBudget(Budget{MaxWork: cap}))
			want := ErrInsufficientStorage
			if cap == 4 {
				want = ErrExponentRange
				if mode == Exact {
					want = ErrInexact
				}
			}
			if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, want) {
				t.Fatalf("postround collision mode%d cap%d: %+v, %v, %v; want %v", mode, cap, got, conditions, err, want)
			}
		}
	}
	ctx = contextTestContext(t, 2, TowardZero, nil, 0)
	got, conditions, err = New(999, math.MaxInt32).MulWithContext(One(), ctx.WithBudget(Budget{MaxDigits: 1}))
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrExponentRange) {
		t.Fatalf("postround range before digit cap: %+v, %v, %v", got, conditions, err)
	}
	ctx = contextTestContext(t, 1, Exact, nil, Rounded)
	got, conditions, err = MustParse("1.00").AddWithContext(Zero(), ctx)
	if got.coefficientDigits() != "1" || got.exponent() != 0 || conditions != 0 || !errors.Is(err, ErrRounded) {
		t.Fatalf("zero-only Exact with Rounded trap: %s e%d, %v, %v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
}

// TestContextArithmeticHugeAlignmentAndFinalDigits covers the context (p > 0)
// charges over the reduced operands: the remote 1 in 1E+1000000 + 1 at p=1 is
// charged as one sticky digit three places below the top (L=4, B=7, W=10),
// and the zero in 12E+1000000 + 0 at p=2 is charged one place below the
// rounding position (L=3, B=3, W=8). The unreduced full-span charges
// (B=1,000,004 and W=1,000,007) survive only through the reference seam.
func TestContextArithmeticHugeAlignmentAndFinalDigits(t *testing.T) {
	type call func(Budget) (Decimal, Conditions, error)
	refuses := func(label string, run call, budget Budget) {
		t.Helper()
		got, conditions, err := run(budget)
		if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("%s %+v: %+v, %v, %v", label, budget, got, conditions, err)
		}
	}
	admits := func(label string, run call, budget Budget, digits string, exponent int32, want Conditions) {
		t.Helper()
		got, conditions, err := run(budget)
		if err != nil || got.coefficientDigits() != digits || got.exponent() != exponent || conditions != want {
			t.Fatalf("%s %+v: %s e%d, %v, %v", label, budget, got.coefficientDigits(), got.exponent(), conditions, err)
		}
	}
	ctx := contextTestContext(t, 1, TiesToEven, nil, 0)
	left := New(1, 1_000_000)
	reduced := func(b Budget) (Decimal, Conditions, error) {
		return left.AddWithContext(One(), ctx.WithBudget(b))
	}
	reference := func(b Budget) (Decimal, Conditions, error) {
		return contextReferenceCall(left, One(), "add", ctx, b)
	}
	refuses("huge aligned B-1", reduced, Budget{MaxDigits: 1, MaxWork: 6})
	refuses("huge aligned W-1", reduced, Budget{MaxDigits: 1, MaxWork: 9})
	admits("huge aligned rounded", reduced, Budget{MaxDigits: 1, MaxWork: 10}, "1", 1_000_000, Inexact|Rounded|Decreased)
	base := uint64(1_000_004)
	refuses("reference huge aligned B-1", reference, Budget{MaxDigits: 1, MaxWork: base - 1})
	refuses("reference huge aligned W-1", reference, Budget{MaxDigits: 1, MaxWork: base + 2})
	admits("reference huge aligned rounded", reference, Budget{MaxDigits: 1, MaxWork: base + 3}, "1", 1_000_000, Inexact|Rounded|Decreased)

	ctx = contextTestContext(t, 2, TiesToEven, nil, 0)
	left = New(12, 1_000_000)
	reduced = func(b Budget) (Decimal, Conditions, error) {
		return left.AddWithContext(New(0, 0), ctx.WithBudget(b))
	}
	reference = func(b Budget) (Decimal, Conditions, error) {
		return contextReferenceCall(left, New(0, 0), "add", ctx, b)
	}
	refuses("huge aligned final digit cap", reduced, Budget{MaxDigits: 1, MaxWork: 8})
	refuses("huge aligned zero B-1", reduced, Budget{MaxWork: 2})
	refuses("huge aligned zero W-1", reduced, Budget{MaxDigits: 2, MaxWork: 7})
	admits("huge aligned zero-only discard", reduced, Budget{MaxDigits: 2, MaxWork: 8}, "12", 1_000_000, Rounded)
	refuses("reference huge aligned final digit cap", reference, Budget{MaxDigits: 1, MaxWork: 1_000_007})
	refuses("reference huge aligned zero W-1", reference, Budget{MaxDigits: 2, MaxWork: 1_000_006})
	admits("reference huge aligned zero-only discard", reference, Budget{MaxDigits: 2, MaxWork: 1_000_007}, "12", 1_000_000, Rounded)
}

func TestContextArithmeticGuardedSignsAndMultiTrap(t *testing.T) {
	guard := &ExponentGuards{Emin: -2, Emax: 2}
	for _, tc := range []struct {
		mode            RoundingMode
		input           int64
		wantCoefficient string
		wantNegative    bool
		direction       Conditions // sign of result − (±1E-5).
	}{
		{TiesToEven, 1, "0", false, Decreased},
		{TiesToEven, -1, "0", false, Increased},
		{TowardPositiveInfinity, 1, "1", false, Increased},
		{TowardPositiveInfinity, -1, "0", false, Increased},
		{TowardNegativeInfinity, 1, "0", false, Decreased},
		{TowardNegativeInfinity, -1, "1", true, Decreased},
		{AwayFromZero, -1, "1", true, Decreased},
	} {
		ctx := contextTestContext(t, 3, tc.mode, guard, 0)
		got, conditions, err := New(tc.input, -5).MulWithContext(One(), ctx)
		if err != nil || got.coefficientDigits() != tc.wantCoefficient || got.exponent() != -4 || got.negative() != tc.wantNegative || conditions != Subnormal|Underflow|Inexact|Rounded|tc.direction {
			t.Fatalf("tiny mode%d input%d: %s e%d sign%v cond%v err%v", tc.mode, tc.input, got.coefficientDigits(), got.exponent(), got.negative(), conditions, err)
		}
	}
	ctx := contextTestContext(t, 3, TiesToEven, guard, Inexact|Rounded|Subnormal|Underflow)
	got, conditions, err := New(12, -5).MulWithContext(One(), ctx)
	var trapped *Error
	if got.coefficientDigits() != "1" || got.exponent() != -4 || conditions != Decreased || !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Op != "MulWithContext" || trapped.Condition != Inexact|Rounded|Subnormal|Underflow {
		t.Fatalf("multibit trap: %s e%d, %v, %v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
	for _, cause := range []ErrorCode{ErrInexact, ErrRounded, ErrSubnormal, ErrUnderflow} {
		if !errors.Is(err, cause) {
			t.Fatalf("missing trapped cause %v", cause)
		}
	}
	ctx = contextTestContext(t, 3, Exact, guard, 0)
	got, conditions, err = New(12, -5).MulWithContext(One(), ctx)
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInexact) {
		t.Fatalf("Exact tiny refusal: %+v, %v, %v", got, conditions, err)
	}
	ctx = contextTestContext(t, 3, Exact, guard, Rounded)
	got, conditions, err = New(100, -5).MulWithContext(One(), ctx)
	if got.coefficientDigits() != "10" || got.exponent() != -4 || conditions != Subnormal || !errors.Is(err, ErrRounded) || errors.Is(err, ErrUnderflow) {
		t.Fatalf("Exact zero-only tiny: %s e%d, %v, %v", got.coefficientDigits(), got.exponent(), conditions, err)
	}
}

func TestContextArithmeticRangeAndPresets(t *testing.T) {
	for _, mode := range []RoundingMode{TiesToEven, TowardZero, Exact} {
		ctx := contextTestContext(t, 1, mode, nil, 0)
		for _, operation := range []string{"add", "sub"} {
			a, b := New(99, math.MaxInt32), New(0, math.MaxInt32)
			var got Decimal
			var conditions Conditions
			var err error
			if operation == "add" {
				got, conditions, err = a.AddWithContext(b, ctx)
			} else {
				got, conditions, err = a.SubWithContext(b, ctx)
			}
			want := ErrExponentRange
			if mode == Exact {
				want = ErrInexact
			}
			if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, want) {
				t.Fatalf("%s postround range mode%d: %+v, %v, %v", operation, mode, got, conditions, err)
			}
		}
	}
	ctx := contextTestContext(t, 2, TiesToEven, &ExponentGuards{Emin: -1, Emax: 1}, Overflow)
	got, conditions, err := New(0, math.MaxInt32).MulWithContext(New(1, 1), ctx.WithBudget(Budget{MaxWork: 1}))
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrExponentRange) {
		t.Fatalf("ideal Mul range before zero/budget/guard: %+v, %v, %v", got, conditions, err)
	}
	for _, preset := range []Context{Decimal32Context(), Decimal64Context(), Decimal128Context()} {
		a, b := MustParse(strings.Repeat("7", 40)), One()
		got, conditions, err := a.MulWithContext(b, preset)
		wantDigits, wantExponent, wantNegative, wantConditions := contextOracle(a, b, "mul", preset.Precision(), preset.Rounding())
		if err != nil || got.coefficientDigits() != wantDigits || int64(got.exponent()) != wantExponent || got.negative() != wantNegative || conditions != wantConditions {
			t.Fatalf("preset p%d: %s e%d sign%v cond%v err%v; want %s e%d sign%v cond%v", preset.Precision(), got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, wantDigits, wantExponent, wantNegative, wantConditions)
		}
	}
}

func TestContextArithmeticSlowOperandImmutability(t *testing.T) {
	a := MustParse(strings.Repeat("739182645", 100))
	b := MustParse(strings.Repeat("845291736", 100))
	aCopy, bCopy := a, b
	aBefore, bBefore := slices.Clone(a.slow.limbs), slices.Clone(b.slow.limbs)
	ctx := contextTestContext(t, 34, TiesToEven, nil, 0)
	for _, call := range []func() (Decimal, Conditions, error){
		func() (Decimal, Conditions, error) { return a.AddWithContext(b, ctx) },
		func() (Decimal, Conditions, error) { return a.SubWithContext(b, ctx) },
		func() (Decimal, Conditions, error) { return a.MulWithContext(b, ctx) },
	} {
		if _, _, err := call(); err != nil {
			t.Fatal(err)
		}
	}
	if !slices.Equal(a.slow.limbs, aBefore) || !slices.Equal(b.slow.limbs, bBefore) || a.slow != aCopy.slow || b.slow != bCopy.slow {
		t.Fatal("shared slow operand changed")
	}
}

func TestContextMulPrechargeRefusesBeforeResultAllocation(t *testing.T) {
	a := MustParse(strings.Repeat("739182645", 1111) + "7")
	b := MustParse(strings.Repeat("845291736", 1111) + "8")
	ctx := contextTestContext(t, 34, TiesToEven, nil, 0)
	budget := Budget{MaxWork: 1_256_543}
	var got Decimal
	var conditions Conditions
	var err error
	allocs := testing.AllocsPerRun(100, func() {
		got, conditions, err = a.MulWithContext(b, ctx.WithBudget(budget))
	})
	var operation *Error
	if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != "MulWithContext" || operation.Condition != InsufficientStorage {
		t.Fatalf("context Mul B-1 identity: exact zero %v, conditions %v, error %v", reflect.DeepEqual(got, Decimal{}), conditions, err)
	}
	if allocs > 1 {
		t.Fatalf("context Mul B-1 allocated %.0f times per call; want at most the typed error", allocs)
	}
}

func TestContextMulFinalQuotaRefusesBeforeResultAllocation(t *testing.T) {
	a := MustParse(strings.Repeat("739182645", 111) + "7")
	b := MustParse(strings.Repeat("845291736", 111) + "8")
	ctx := contextTestContext(t, 2000, TiesToEven, nil, 0)
	base := uint64(112*112 + 2000)
	for _, budget := range []Budget{
		{MaxDigits: 1999, MaxWork: base + 4001},
		{MaxDigits: 2000, MaxWork: base + 4000},
	} {
		var got Decimal
		var conditions Conditions
		var err error
		allocs := testing.AllocsPerRun(20, func() {
			got, conditions, err = a.MulWithContext(b, ctx.WithBudget(budget))
		})
		if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInsufficientStorage) || allocs > 1 {
			t.Fatalf("final quota %+v: result %+v conditions %v err %v allocations %.0f", budget, got, conditions, err, allocs)
		}
	}
}

// contextDirectionCall runs one context arithmetic operation and returns
// the exact rational result from the operands' own digits.
// contextReduceOperands applies contextReduceShapes to two operands as the
// kernel does (reducedOperand), for tests that inspect the reduction.
func contextReduceOperands(x, y Decimal, ctx Context) (Decimal, Decimal) {
	sx, sy := x.Shape(), y.Shape()
	rx, ry := contextReduceShapes(sx, sy, ctx)
	return reducedOperand(x, sx, rx), reducedOperand(y, sy, ry)
}

// contextReferenceCall is the unreduced reference seam: context Add or Sub
// over the full aligned span, under the public budgeted operation name so
// error identities compare equal.
func contextReferenceCall(a, b Decimal, operation string, ctx Context, budget Budget) (Decimal, Conditions, error) {
	if operation == "sub" {
		return a.contextAddSub(b, ctx.withLimits(budget.arith()), "SubWithContext", true, false, nil)
	}
	return a.contextAddSub(b, ctx.withLimits(budget.arith()), "AddWithContext", false, false, nil)
}

func contextDirectionCall(a, b Decimal, operation string, ctx Context, budget Budget) (Decimal, Conditions, error, *big.Rat) {
	x, y := directionValueRat(a), directionValueRat(b)
	switch operation {
	case "add":
		got, conditions, err := a.AddWithContext(b, ctx.WithBudget(budget))
		return got, conditions, err, new(big.Rat).Add(x, y)
	case "sub":
		got, conditions, err := a.SubWithContext(b, ctx.WithBudget(budget))
		return got, conditions, err, new(big.Rat).Sub(x, y)
	default:
		got, conditions, err := a.MulWithContext(b, ctx.WithBudget(budget))
		return got, conditions, err, new(big.Rat).Mul(x, y)
	}
}

// contextDirectionOperand draws a small signed decimal whose runs of nines
// provoke carries into a new decade.
func contextDirectionOperand(rng *rand.Rand) Decimal {
	if rng.IntN(15) == 0 {
		return New(0, int32(rng.IntN(21)-10))
	}
	digits := make([]byte, 1+rng.IntN(12))
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
	return MustParse(sign + string(digits) + "E" + strconv.Itoa(rng.IntN(21)-14))
}

// TestContextArithmeticDirectionAgainstRationalOracle checks the result
// direction against an exact oracle for context Add, Sub and Mul: in every
// mode, guarded and unguarded, the direction bit equals sign(result − exact)
// by math/big.Rat comparison, accompanies Inexact exactly, and respects the
// directed-mode side unless Overflow is reported. Named rows pin negative
// values rounded to the unsigned zero at the Etiny quantum (Increased),
// subnormal results, zero-only discards (Rounded, no direction), Exact
// refusals and resource refusals (no value, no direction).
func TestContextArithmeticDirectionAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(0xdec045, 1))
	modes := [...]RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact}
	counts := map[Conditions]int{}
	for i := range 30_000 {
		a, b := contextDirectionOperand(rng), contextDirectionOperand(rng)
		p := uint32(1 + rng.IntN(10))
		mode := modes[rng.IntN(len(modes))]
		var guards *ExponentGuards
		if rng.IntN(3) != 0 {
			emin := int32(-rng.IntN(12))
			guards = &ExponentGuards{Emin: emin, Emax: emin + 2 + int32(rng.IntN(14))}
		}
		ctx := contextTestContext(t, p, mode, guards, 0)
		operation := [...]string{"add", "sub", "mul"}[i%3]
		got, conditions, err, exact := contextDirectionCall(a, b, operation, ctx, Budget{})
		label := operation + " " + a.String() + " " + b.String() + " p" + strconv.Itoa(int(p)) + " mode" + strconv.Itoa(int(mode))
		if checkRoundingDirection(t, label, exact, mode, got, conditions, err) {
			counts[conditions&(Increased|Decreased|Overflow|Subnormal)]++
		} else if mode != Exact {
			t.Fatalf("%s: unexpected refusal %v", label, err)
		}
	}
	for _, want := range []Conditions{Increased, Decreased, Increased | Subnormal, Decreased | Subnormal, Increased | Overflow, Decreased | Overflow} {
		if counts[want] < 20 {
			t.Fatalf("direction corpus reached %v only %d times: %v", want, counts[want], counts)
		}
	}

	guards := &ExponentGuards{Emin: -2, Emax: 2} // p=3: Etiny -4, Bmax 999
	for _, tc := range []struct {
		name, operation, a, b string
		mode                  RoundingMode
		want                  string
		conditions            Conditions
	}{
		{"negative tiny to zero", "mul", "-1E-5", "1", TowardZero, "0.0000", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"negative tiny to zero by add", "add", "-0.00001", "0.000004", TiesToEven, "0.0000", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"positive tiny to zero", "sub", "0.00003", "0.00002", TowardNegativeInfinity, "0.0000", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"negative tiny away", "mul", "-0.00001", "1", TowardNegativeInfinity, "-0.0001", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"subnormal at Etiny", "mul", "0.0123", "0.01", TowardPositiveInfinity, "0.0002", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"subnormal carry", "add", "0.00999", "0", TiesToEven, "0.0100", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"zero-only discard", "add", "1.00", "0.000", TowardPositiveInfinity, "1.00", Rounded},
		{"zero-only discard mul", "mul", "12.0", "10", TowardZero, "120", Rounded},
		{"exact subnormal", "mul", "0.001", "1", TowardZero, "0.001", Subnormal},
	} {
		t.Run(tc.name, func(t *testing.T) {
			a, b := MustParse(tc.a), MustParse(tc.b)
			got, conditions, err, exact := contextDirectionCall(a, b, tc.operation, contextTestContext(t, 3, tc.mode, guards, 0), Budget{})
			text, _ := got.Text(0)
			if err != nil || text != tc.want || conditions != tc.conditions {
				t.Fatalf("%s %s %s: %s %v %v; want %s %v", tc.operation, tc.a, tc.b, text, conditions, err, tc.want, tc.conditions)
			}
			checkRoundingDirection(t, tc.name, exact, tc.mode, got, conditions, err)
		})
	}
	for _, tc := range []struct {
		name, operation, a, b string
		mode                  RoundingMode
		budget                Budget
		code                  ErrorCode
	}{
		{"Exact refusal add", "add", "1.234", "0", Exact, Budget{}, ErrInexact},
		{"Exact refusal mul", "mul", "-1.5", "0.25", Exact, Budget{}, ErrInexact},
		{"Exact refusal sub", "sub", "0.001", "1", Exact, Budget{}, ErrInexact},
		{"resource refusal mul", "mul", "12", "34", TiesToEven, Budget{MaxWork: 4}, ErrInsufficientStorage},
		{"resource refusal sub", "sub", "1.2345", "-0.0001", TowardPositiveInfinity, Budget{MaxDigits: 1}, ErrInsufficientStorage},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx := contextTestContext(t, 2, tc.mode, nil, 0)
			got, conditions, err, _ := contextDirectionCall(MustParse(tc.a), MustParse(tc.b), tc.operation, ctx, tc.budget)
			if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, tc.code) {
				t.Fatalf("%s: %+v %v %v; want no value, no conditions, %v", tc.name, got, conditions, err, tc.code)
			}
		})
	}
}

// TestContextArithmeticDirectedEnclosure covers the directed-rounding
// enclosure and tightness property for context Add, Sub and Mul: for random
// exact values, whenever neither directed result reports Overflow,
// TowardNegativeInfinity and TowardPositiveInfinity return the floor and
// ceiling of the exact value on the p-digit grid of its decade (the Etiny
// quantum when tiny), so they bracket it and no representable value lies
// strictly between; a carry into a new decade (9.995 to 10.0 at p=3) is
// covered by named rows.
func TestContextArithmeticDirectedEnclosure(t *testing.T) {
	rng := rand.New(rand.NewPCG(0xdec045, 2))
	checked, inexact := 0, 0
	type sample struct {
		operation string
		a, b      Decimal
		p         uint32
		guards    *ExponentGuards
	}
	samples := []sample{
		{"add", MustParse("9.99"), MustParse("0.005"), 3, nil},
		{"sub", MustParse("-9.99"), MustParse("0.005"), 3, nil},
		{"mul", MustParse("1.999"), MustParse("5"), 3, nil},
		{"add", MustParse("999.9"), MustParse("0.09"), 4, &ExponentGuards{Emin: -2, Emax: 3}},
		{"add", MustParse("0.00999"), Zero(), 3, &ExponentGuards{Emin: -2, Emax: 5}},
		{"sub", MustParse("-0.00999"), Zero(), 3, &ExponentGuards{Emin: -2, Emax: 5}},
		{"mul", MustParse("-1E-5"), One(), 3, &ExponentGuards{Emin: -2, Emax: 2}},
		{"sub", MustParse("1E+20"), MustParse("1E-20"), 5, nil},
	}
	for range 20_000 {
		var guards *ExponentGuards
		if rng.IntN(2) == 0 {
			emin := int32(-rng.IntN(12))
			guards = &ExponentGuards{Emin: emin, Emax: emin + 2 + int32(rng.IntN(14))}
		}
		samples = append(samples, sample{[...]string{"add", "sub", "mul"}[rng.IntN(3)], contextDirectionOperand(rng), contextDirectionOperand(rng), uint32(1 + rng.IntN(10)), guards})
	}
	for i, s := range samples {
		lo, loConditions, loErr, exact := contextDirectionCall(s.a, s.b, s.operation, contextTestContext(t, s.p, TowardNegativeInfinity, s.guards, 0), Budget{})
		hi, hiConditions, hiErr, _ := contextDirectionCall(s.a, s.b, s.operation, contextTestContext(t, s.p, TowardPositiveInfinity, s.guards, 0), Budget{})
		if loErr != nil || hiErr != nil {
			t.Fatalf("sample %d %s %v %v: errors %v / %v", i, s.operation, s.a, s.b, loErr, hiErr)
		}
		emin := int64(0)
		if s.guards != nil {
			emin = int64(s.guards.Emin)
		}
		quantum := directionPrecisionQuantum(exact, int64(s.p), s.guards != nil, emin)
		label := "sample " + strconv.Itoa(i) + " " + s.operation + " " + s.a.String() + " " + s.b.String() + " p" + strconv.Itoa(int(s.p))
		if checkDirectedEnclosure(t, label, exact, quantum, lo, loConditions, hi, hiConditions) {
			checked++
			if loConditions&Inexact != 0 {
				inexact++
			}
		}
		if i < 3 && lo.coefficientDigits() != "100" && hi.coefficientDigits() != "100" {
			t.Fatalf("carry row %d did not reach the new decade: lo %v hi %v", i, lo, hi)
		}
	}
	if checked < 12_000 || inexact < 5_000 {
		t.Fatalf("enclosure checked %d pairs, %d inexact", checked, inexact)
	}
}

// TestContextArithmeticOverflowDirectionVectors covers overflow directions
// for context Add, Sub and Mul in every mode and sign at p=3, Emax=2: an
// exact value past Bmax, an exact 1000, and 999.5 and 999.9, whose rounding
// carries past Bmax only in modes that round the magnitude up. Every
// substitution to ±999 reports Decreased for a positive and Increased for a
// negative exact value; the non-overflowing ±999 results report the same
// direction because they truncate toward zero; Exact refuses with no
// direction.
func TestContextArithmeticOverflowDirectionVectors(t *testing.T) {
	guards := &ExponentGuards{Emin: -2, Emax: 2}
	modes := [...]RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact}
	for _, magnitude := range []string{"1000.1", "1000", "999.9", "999.5"} {
		exactMagnitude, _ := new(big.Rat).SetString(magnitude)
		for _, negative := range []bool{false, true} {
			exact := new(big.Rat).Set(exactMagnitude)
			if negative {
				exact.Neg(exact)
			}
			// Operands whose exact sum, difference or product is exact.
			one := big.NewRat(1, 1)
			operands := map[string][2]*big.Rat{
				"add": {new(big.Rat).Sub(exact, one), one},
				"sub": {new(big.Rat).Add(exact, one), one},
				"mul": {new(big.Rat).Mul(exact, big.NewRat(2, 1)), big.NewRat(1, 2)},
			}
			for _, mode := range modes {
				// Hand-derived: 999.9 and 999.5 carry past 999 when the
				// magnitude rounds up (999 is odd, so TiesToEven rounds the
				// tie up; TiesTowardZero keeps it).
				up := false
				switch mode {
				case TiesToEven, TiesAwayFromZero, AwayFromZero:
					up = true
				case TiesTowardZero:
					up = magnitude != "999.5"
				case TowardPositiveInfinity:
					up = !negative
				case TowardNegativeInfinity:
					up = negative
				}
				overflow := magnitude == "1000.1" || magnitude == "1000" || up
				want := Inexact | Rounded | Decreased
				if negative {
					want = Inexact | Rounded | Increased
				}
				if overflow {
					want |= Overflow
				}
				for _, operation := range []string{"add", "sub", "mul"} {
					a := MustParse(operands[operation][0].FloatString(2))
					b := MustParse(operands[operation][1].FloatString(1))
					got, conditions, err, computed := contextDirectionCall(a, b, operation, contextTestContext(t, 3, mode, guards, 0), Budget{})
					label := operation + " " + a.String() + " " + b.String() + " mode" + strconv.Itoa(int(mode))
					if computed.Cmp(exact) != 0 {
						t.Fatalf("%s: operands give %s, want %s", label, computed.RatString(), exact.RatString())
					}
					if mode == Exact {
						if !reflect.DeepEqual(got, Decimal{}) || conditions != 0 || !errors.Is(err, ErrInexact) {
							t.Fatalf("%s: Exact overflow %+v %v %v", label, got, conditions, err)
						}
						continue
					}
					if err != nil || got.coefficientDigits() != "999" || got.exponent() != 0 || got.negative() != negative || conditions != want {
						t.Fatalf("%s: %v %v %v; want %s999 %v", label, got, conditions, err, map[bool]string{true: "-"}[negative], want)
					}
					checkRoundingDirection(t, label, exact, mode, got, conditions, err)
				}
			}
		}
	}
}

// TestContextRemoteOperandKeepsDirection covers remote operands: a context
// Add or Sub whose small operand lies wholly below the rounding position
// takes the sticky substitute (budgeted or not), and must return the value,
// exponent and conditions, including the direction bit, of the unreduced
// reference seam (contextAddSub with reduce=false), which keeps the logical
// full-width path. The direction is also checked against the exact rational
// sum, including borrows in Sub and negative operands.
func TestContextRemoteOperandKeepsDirection(t *testing.T) {
	budget := Budget{MaxDigits: 1 << 20, MaxWork: 1 << 30}
	seen := map[Conditions]int{}
	for _, texts := range [][2]string{
		{"1E+60", "1E-60"},
		{"1E+60", "-1E-60"},
		{"-1E+60", "1E-60"},
		{"-1E+60", "-1E-60"},
		{"1E-60", "1E+60"},
		{"-3E-50", "9.99999E+40"},
		{"123456789E+30", "4E-40"},
		{"1000000", "1E-80"},
		{"-1000000", "5E-80"},
	} {
		a, b := MustParse(texts[0]), MustParse(texts[1])
		for _, p := range []uint32{1, 5, 16} {
			if x, y := contextReduceOperands(a, b, contextTestContext(t, p, TiesToEven, nil, 0)); sameRepresentation(x, a) && sameRepresentation(y, b) {
				t.Fatalf("%s %s p%d: fixture does not take the remote-operand substitute", texts[0], texts[1], p)
			}
			for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity} {
				ctx := contextTestContext(t, p, mode, nil, 0)
				for _, operation := range []string{"add", "sub"} {
					want, wantConditions, wantErr := contextReferenceCall(a, b, operation, ctx, Budget{})
					for _, b2 := range []Budget{{}, budget} {
						got, conditions, err, exact := contextDirectionCall(a, b, operation, ctx, b2)
						label := operation + " " + texts[0] + " " + texts[1] + " p" + strconv.Itoa(int(p)) + " mode" + strconv.Itoa(int(mode))
						if err != nil || wantErr != nil || !sameRepresentation(got, want) || conditions != wantConditions {
							t.Fatalf("%s budget %+v: reduced %v %v %v; reference %v %v %v", label, b2, got, conditions, err, want, wantConditions, wantErr)
						}
						checkRoundingDirection(t, label, exact, mode, got, conditions, err)
						seen[conditions&(Increased|Decreased)]++
					}
				}
			}
		}
	}
	// Borrow: 1E+60 − 1E-60 at p=5 truncates to 9.9999E+59 below the
	// exact value and rounds to nearest back up to 1.0000E+60 above it.
	for _, tc := range []struct {
		mode       RoundingMode
		want       string
		conditions Conditions
	}{
		{TowardZero, "9.9999E+59", Inexact | Rounded | Decreased},
		{TiesToEven, "1.0000E+60", Inexact | Rounded | Increased},
		{TowardPositiveInfinity, "1.0000E+60", Inexact | Rounded | Increased},
	} {
		ctx := contextTestContext(t, 5, tc.mode, nil, 0)
		for _, b := range []Budget{{}, budget} {
			got, conditions, err := MustParse("1E+60").SubWithContext(MustParse("1E-60"), ctx.WithBudget(b))
			if err != nil || got.String() != tc.want || conditions != tc.conditions {
				t.Fatalf("borrow mode%d budget %+v: %v %v %v; want %s %v", tc.mode, b, got, conditions, err, tc.want, tc.conditions)
			}
		}
	}
	if seen[Increased] == 0 || seen[Decreased] == 0 {
		t.Fatalf("remote-operand corpus lacks a direction: %v", seen)
	}
}

// TestContextRejectsDirectionTraps checks that the result-direction
// attributes are declared but not trappable, so NewContext and WithTraps
// reject them, alone or beside GDA bits, with ErrInvalidContext, while the
// full GDA inventory stays valid.
func TestContextRejectsDirectionTraps(t *testing.T) {
	gda := Conditions((Underflow << 1) - 1)
	if _, err := NewContext(3, TiesToEven, nil, gda); err != nil {
		t.Fatalf("GDA inventory as traps: %v", err)
	}
	base := contextTestContext(t, 3, TiesToEven, nil, Inexact)
	for _, traps := range []Conditions{Increased, Decreased, Increased | Decreased, Inexact | Increased, gda | Decreased, Inexact | Rounded | Decreased} {
		got, err := NewContext(3, TiesToEven, nil, traps)
		assertInvalidContext(t, got, err, "NewContext")
		got, err = base.WithTraps(traps)
		assertInvalidContext(t, got, err, "Context.WithTraps")
		if base.Traps() != Inexact {
			t.Fatalf("rejected derivation changed the receiver: %v", base.Traps())
		}
	}
	// A returned set becomes a valid trap set once the direction is masked.
	_, returned, err := MustParse("1.234").AddWithContext(Zero(), contextTestContext(t, 2, TiesToEven, nil, 0))
	if err != nil || returned != Inexact|Rounded|Decreased {
		t.Fatalf("returned set %v, %v", returned, err)
	}
	if _, err := base.WithTraps(returned); !errors.Is(err, ErrInvalidContext) {
		t.Fatalf("unmasked returned set accepted as traps: %v", err)
	}
	if derived, err := base.WithTraps(returned &^ (Increased | Decreased)); err != nil || derived.Traps() != Inexact|Rounded {
		t.Fatalf("masked returned set: %v, %v", derived.Traps(), err)
	}
}

// TestContextInexactTrapKeepsDirection checks, for every context emitter,
// that an Inexact trap still fires as Error{Condition: Inexact}, the finite
// result is returned, and its untrapped conditions keep the direction bit;
// Error.Condition never carries a direction bit.
func TestContextInexactTrapKeepsDirection(t *testing.T) {
	for _, mode := range []RoundingMode{TowardNegativeInfinity, TowardPositiveInfinity} {
		direction := Decreased
		if mode == TowardPositiveInfinity {
			direction = Increased
		}
		ctx := contextTestContext(t, 3, mode, nil, Inexact)
		allTraps := contextTestContext(t, 3, mode, &ExponentGuards{Emin: -2, Emax: 2}, Conditions((Underflow<<1)-1))
		for _, tc := range []struct {
			op   string
			call func(Context) (Decimal, Conditions, error)
		}{
			{"AddWithContext", func(c Context) (Decimal, Conditions, error) { return MustParse("1.2345").AddWithContext(Zero(), c) }},
			{"SubWithContext", func(c Context) (Decimal, Conditions, error) { return MustParse("1.2345").SubWithContext(Zero(), c) }},
			{"MulWithContext", func(c Context) (Decimal, Conditions, error) { return MustParse("1.2345").MulWithContext(One(), c) }},
			{"QuantizeWithContext", func(c Context) (Decimal, Conditions, error) { return MustParse("1.2345").QuantizeWithContext(-2, c) }},
			{"RoundToIntegralWithContext", func(c Context) (Decimal, Conditions, error) { return MustParse("1.2345").RoundToIntegralWithContext(c) }},
			{"DivWithContext", func(c Context) (Decimal, Conditions, error) { return One().DivWithContext(MustParse("0.81"), c) }},
		} {
			got, conditions, err := tc.call(ctx)
			var trapped *Error
			if !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Op != tc.op || trapped.Condition != Inexact || !errors.Is(err, ErrInexact) || conditions != Rounded|direction || got.isZero() {
				t.Fatalf("%s mode%d: %v %v %v; want Rounded|%v and the Inexact trap", tc.op, mode, got, conditions, err, direction)
			}
			if trapped.Condition&(Increased|Decreased) != 0 {
				t.Fatalf("%s: Trapped carries direction %v", tc.op, trapped.Condition)
			}
			got, conditions, err = tc.call(allTraps)
			if !errors.As(err, &trapped) || trapped.Code != 0 || trapped.Condition&(Increased|Decreased) != 0 || trapped.Condition&Inexact == 0 || conditions != direction || got.isZero() {
				t.Fatalf("%s all traps: %v %v %v; want only %v returned", tc.op, got, conditions, err, direction)
			}
		}
	}
	for _, err := range []error{
		func() error { _, _, err := MustParse("1.25").Quantize(-1, Exact); return err }(),
		func() error { _, err := One().Div(MustParse("3")); return err }(),
		func() error {
			_, _, err := MustParse("12").MulWithContext(MustParse("34"), contextTestContext(t, 2, TiesToEven, nil, 0).WithBudget(Budget{MaxWork: 4}))
			return err
		}(),
		func() error { _, _, err := One().DivToExponent(Zero(), 0, TowardZero); return err }(),
		func() error { _, err := NewContext(1, TiesToEven, nil, Increased); return err }(),
		func() error { _, err := Parse("1.2.3"); return err }(),
	} {
		var condition *Error
		var operation *Error
		var contextErr *Error
		var parse *Error
		switch {
		case errors.As(err, &condition) && condition.Code == 0:
			if condition.Condition&(Increased|Decreased) != 0 || condition.Condition == 0 {
				t.Fatalf("Error %v carries %v", err, condition.Condition)
			}
		case errors.As(err, &operation):
			if operation.Condition&(Increased|Decreased) != 0 || operation.Condition == 0 {
				t.Fatalf("Error %v carries %v", err, operation.Condition)
			}
		case errors.As(err, &contextErr):
			if contextErr.Condition != InvalidContext {
				t.Fatalf("Error %v carries %v", err, contextErr.Condition)
			}
		case errors.As(err, &parse):
			if parse.Condition&(Increased|Decreased) != 0 || parse.Condition == 0 {
				t.Fatalf("Error %v carries %v", err, parse.Condition)
			}
		default:
			t.Fatalf("untyped error %v", err)
		}
	}
}

// checkContextWorkIndependentOfGap checks gap-independent work for one family
// of pairs (x, y) drawn at exponent gaps 40 .. 10^7, in Add and Sub at p=34:
// the smallest admitting work cap of the budgeted call, and the base charge B
// the unbudgeted call computes (reported through contextAddSub's charge seam,
// never timed), stay within four units of their values at gap 40; the
// admitted result, exponent and conditions equal the unbudgeted call's and,
// for gaps up to 10^5, the unreduced reference seam's.
func checkContextWorkIndependentOfGap(t *testing.T, name string, pair func(gap string) (Decimal, Decimal)) {
	t.Helper()
	ctx, err := NewContext(34, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	firstWork, firstCharge := map[string]uint64{}, map[string]uint64{}
	for _, gap := range []int{40, 1000, 100000, 10000000} {
		x, y := pair(strconv.Itoa(gap))
		for _, operation := range []string{"add", "sub"} {
			d := reductionDraw{a: x, b: y, ctx: ctx, sub: operation == "sub"}
			label := name + " " + operation + " g=" + strconv.Itoa(gap)
			public := "AddWithContext"
			if d.sub {
				public = "SubWithContext"
			}
			var charge uint64
			want, wantConditions, err := x.contextAddSub(y, ctx.withLimits(limits{}), public, d.sub, true, &charge)
			if err != nil || charge == 0 {
				t.Fatalf("%s: unbudgeted %v %v, charge %d", label, want, err, charge)
			}
			work := smallestAdmitting(1<<40, func(w uint64) bool {
				_, _, err := d.call(Budget{MaxWork: w})
				return err == nil
			})
			got, conditions, err := d.call(Budget{MaxWork: work})
			if err != nil || !sameRepresentation(got, want) || conditions != wantConditions {
				t.Fatalf("%s: budgeted (%v, %v, %v), unbudgeted (%v, %v)", label, got, conditions, err, want, wantConditions)
			}
			// The unbudgeted charge is the budgeted base: W = B + 2N + 1.
			if n := got.CoefficientDigits(); work != charge+2*n+1 {
				t.Fatalf("%s: unbudgeted base charge %d, but the budgeted call admits at W=%d with N=%d", label, charge, work, n)
			}
			if gap <= 100000 {
				reference, referenceConditions, referenceErr := contextReferenceCall(x, y, operation, ctx, Budget{})
				if referenceErr != nil || !sameRepresentation(got, reference) || conditions != referenceConditions {
					t.Fatalf("%s: reduced (%v, %v), reference seam (%v, %v, %v)", label, got, conditions, reference, referenceConditions, referenceErr)
				}
			}
			if firstWork[operation] == 0 {
				firstWork[operation], firstCharge[operation] = work, charge
			}
			if work > firstWork[operation]+4 {
				t.Errorf("%s: smallest admitting work %d, at gap 40 it was %d", label, work, firstWork[operation])
			}
			if charge > firstCharge[operation]+4 {
				t.Errorf("%s: unbudgeted base charge %d, at gap 40 it was %d", label, charge, firstCharge[operation])
			}
		}
	}
}

// TestContextAddBudgetIndependentOfGap checks that a budgeted context Add
// with a remote operand costs O(p): context Add and Sub of 1E+g and 1 or
// −7.25, budgeted or not, reduce the operand lying below the rounding
// position to its sticky digit before charging, so the work does not depend
// on the gap g, and the result equals the unbudgeted call's and the unreduced
// reference seam's (checkContextWorkIndependentOfGap).
func TestContextAddBudgetIndependentOfGap(t *testing.T) {
	for _, small := range []string{"1", "-7.25"} {
		checkContextWorkIndependentOfGap(t, "1E+g, "+small, func(g string) (Decimal, Decimal) {
			return MustParse("1E+" + g), MustParse(small)
		})
	}
}

// TestContextAddZeroOperandIndependentOfGap checks the same O(p) cost for a
// zero operand: a zero whose exponent lies far below the rounding position of
// the nonzero operand (1 + 0E−g), or a nonzero operand far above a zero at
// exponent 0 (1E+g + 0), is charged and streamed as if the zero sat one place
// below that position, budgeted or not, so the work does not depend on g
// (checkContextWorkIndependentOfGap).
func TestContextAddZeroOperandIndependentOfGap(t *testing.T) {
	checkContextWorkIndependentOfGap(t, "1, 0E-g", func(g string) (Decimal, Decimal) { return MustParse("1"), MustParse("0E-" + g) })
	checkContextWorkIndependentOfGap(t, "0E-g, 1", func(g string) (Decimal, Decimal) { return MustParse("0E-" + g), MustParse("1") })
	checkContextWorkIndependentOfGap(t, "1E+g, 0", func(g string) (Decimal, Decimal) { return MustParse("1E+" + g), MustParse("0") })
}

// TestContextMayReduceIsNecessary covers the contextMayReduce pre-filter:
// wherever contextReduceShapes changes a shape, contextMayReduce (fed exact
// digit counts, 0 for zero) reports true, and for a zero operand it reports
// exactly when the clamp moves the zero. It runs over drawReduction's corpus
// (inline and slow coefficients, both reductions, guards, int32 limits) and
// exponent gaps swept around both firing thresholds. A guard requires it to
// skip the planner in most draws.
func TestContextMayReduceIsNecessary(t *testing.T) {
	r := rand.New(rand.NewPCG(62, 3))
	skipped, fired := 0, 0
	check := func(x, y Decimal, ctx Context) {
		sx, sy := x.Shape(), y.Shape()
		rx, ry := contextReduceShapes(sx, sy, ctx)
		reduces := rx != sx || ry != sy
		may := contextMayReduce(sx.Digits, sx.Exponent, sy.Digits, sy.Exponent, int64(ctx.precision), contextFloor(ctx))
		if reduces && !may || may && !reduces && (sx.Digits == 0) != (sy.Digits == 0) {
			t.Fatalf("%v %v %+v: planner reduces %v (%+v, %+v), contextMayReduce %v", x, y, ctx, reduces, rx, ry, may)
		}
		if may {
			fired++
		} else {
			skipped++
		}
	}
	for range 200_000 {
		d := drawReduction(r, 3000)
		check(d.a, d.b, d.ctx)
	}
	for _, p := range []uint32{1, 5, 16, 34, 40} {
		ctx, _ := NewContext(p, TiesToEven, nil, 0)
		guarded, _ := NewContext(p, TiesToEven, &ExponentGuards{Emin: -30, Emax: 30}, 0)
		for _, dx := range []uint64{1, 9, 19, 20, 38, 39, 45, 90} {
			for _, dy := range []uint64{1, 2, 18, 38, 39, 82} {
				x := shapedDecimal(nil, dx, 0, false, '9')
				for gap := int32(0); gap <= int32(dx+dy)+int32(p)+6; gap++ {
					y := shapedDecimal(nil, dy, -gap, true, '1')
					check(x, y, ctx)
					check(y, x, guarded)
					check(x, New(0, -gap), ctx)
					check(New(0, -gap-40), y, guarded)
				}
			}
		}
	}
	if skipped < 100_000 || fired < 50_000 {
		t.Fatalf("contextMayReduce coverage: skipped %d, fired %d", skipped, fired)
	}
}

// reductionDraw is one context Add/Sub call of the reduction differential
// corpus, with which reduction (if any) contextReduceShapes applies.
type reductionDraw struct {
	a, b          Decimal
	ctx           Context
	sub           bool
	sticky, clamp bool
}

// clampInt32 clamps v into the int32 exponent range.
func clampInt32(v int64) int32 {
	return int32(min(max(v, math.MinInt32), math.MaxInt32))
}

// drawReduction draws a context Add or Sub around the reduction boundaries: a
// nonzero operand on both sides of the sticky position P = min(e, adj−p−1)−1
// (near or up to maxGap places below), a zero on both sides of pos = adj−p+1
// (or Etiny under guards) and above the nonzero's exponent, overlapping
// operands of all-nine and power-of-ten coefficients for carries and borrows,
// guards placing Etiny or Emax next to the result, random traps, every mode
// including Exact, and exponents next to both int32 limits.
func drawReduction(r *rand.Rand, maxGap int64) reductionDraw {
	precisions := []uint32{1, 2, 3, 5, 7, 16, 34}
	p := precisions[r.IntN(len(precisions))]
	if r.IntN(3) == 0 {
		p = uint32(1 + r.IntN(40))
	}
	operand := func(digits uint64, e int32, negative bool) Decimal {
		b := make([]byte, 0, digits+16)
		if negative {
			b = append(b, '-')
		}
		kind := r.IntN(6)
		for i := range digits {
			switch {
			case kind < 2:
				b = append(b, '9')
			case kind == 2:
				b = append(b, "10"[min(i, 1)])
			case i == 0:
				b = append(b, byte('1'+r.IntN(9)))
			default:
				b = append(b, byte('0'+r.IntN(10)))
			}
		}
		b = append(b, 'E')
		b = strconv.AppendInt(b, int64(e), 10)
		return MustParse(string(b))
	}
	dx := uint64(1 + r.IntN(40))
	ex := int64(r.IntN(400) - 200)
	switch r.IntN(8) {
	case 0:
		ex = math.MaxInt32 - int64(r.IntN(80))
	case 1:
		ex = math.MinInt32 + int64(r.IntN(80))
	}
	x := operand(dx, int32(ex), r.IntN(2) == 0)
	adjX := ex + int64(dx) - 1
	var y Decimal
	switch r.IntN(5) {
	case 0, 1: // a nonzero on either side of P
		position := min(ex, adjX-int64(p)-1) - 1
		adjY := position + int64(r.IntN(7)-3)
		if r.IntN(4) == 0 {
			adjY = position - 1 - r.Int64N(maxGap)
		}
		dy := uint64(1 + r.IntN(20))
		y = operand(dy, clampInt32(adjY-int64(dy)+1), r.IntN(2) == 0)
	case 2: // a zero on either side of pos, or above the nonzero's exponent
		pos := adjX - int64(p) + 1
		ez := pos + int64(r.IntN(7)-3)
		switch r.IntN(4) {
		case 0:
			ez = pos - 1 - r.Int64N(maxGap)
		case 1:
			ez = ex + int64(r.IntN(6))
		}
		y = New(0, clampInt32(ez))
	case 3: // overlapping operands: carries and borrows at the rounding position
		dy := uint64(1 + r.IntN(40))
		y = operand(dy, clampInt32(ex+int64(r.IntN(81)-40)), r.IntN(2) == 0)
	default: // both zero, or a zero beside a near operand
		y = New(0, clampInt32(ex+int64(r.IntN(81)-40)))
		if r.IntN(3) == 0 {
			x = New(0, int32(ex))
		}
	}
	if r.IntN(2) == 0 {
		x, y = y, x
	}
	var guards *ExponentGuards
	if r.IntN(2) == 0 {
		adj := max(int64(x.exponent())+int64(x.CoefficientDigits())-1, int64(y.exponent())+int64(y.CoefficientDigits())-1)
		emin := adj + int64(r.IntN(9)-4) // Etiny near pos
		if r.IntN(2) == 0 {
			emin = adj - int64(p) - int64(r.IntN(60))
		}
		emax := max(emin, adj+int64(r.IntN(9)-4)) // Emax near the result
		if r.IntN(2) == 0 {
			emax = max(emin, adj+int64(r.IntN(60)))
		}
		guards = &ExponentGuards{Emin: clampInt32(emin), Emax: clampInt32(emax)}
	}
	var traps Conditions
	if r.IntN(4) == 0 {
		traps = Conditions(r.IntN(int(trappableConditions) + 1))
	}
	ctx, err := NewContext(p, RoundingMode(r.IntN(int(Exact)+1)), guards, traps)
	if err != nil {
		ctx, _ = NewContext(p, RoundingMode(r.IntN(int(Exact)+1)), nil, traps)
	}
	d := reductionDraw{a: x, b: y, ctx: ctx, sub: r.IntN(2) == 0}
	sx, sy := x.Shape(), y.Shape()
	rx, ry := contextReduceShapes(sx, sy, ctx)
	for _, pair := range [][2]Shape{{sx, rx}, {sy, ry}} {
		if pair[0] != pair[1] {
			if pair[0].Digits == 0 {
				d.clamp = true
			} else {
				d.sticky = true
			}
		}
	}
	return d
}

// call runs the draw through the public budgeted entry point.
func (d reductionDraw) call(budget Budget) (Decimal, Conditions, error) {
	if d.sub {
		return d.a.SubWithContext(d.b, d.ctx.WithBudget(budget))
	}
	return d.a.AddWithContext(d.b, d.ctx.WithBudget(budget))
}

func (d reductionDraw) operation() string {
	if d.sub {
		return "sub"
	}
	return "add"
}

// sameContextOutcome compares two context results on value, exponent,
// Conditions (including the direction bits), error identity and text, and
// the trapped set.
func sameContextOutcome(got Decimal, conditions Conditions, err error, want Decimal, wantConditions Conditions, wantErr error) bool {
	if !sameRepresentation(got, want) || conditions != wantConditions || (err == nil) != (wantErr == nil) {
		return false
	}
	if err == nil {
		return true
	}
	var trapped, wantTrapped *Error
	isTrap := errors.As(err, &trapped) && trapped.Code == 0
	wantTrap := errors.As(wantErr, &wantTrapped) && wantTrapped.Code == 0
	if isTrap != wantTrap || isTrap && trapped.Condition != wantTrapped.Condition {
		return false
	}
	for _, code := range []ErrorCode{ErrInsufficientStorage, ErrExponentRange, ErrInexact, ErrRounded, ErrSubnormal, ErrUnderflow, ErrOverflow} {
		if errors.Is(err, code) != errors.Is(wantErr, code) {
			return false
		}
	}
	return err.Error() == wantErr.Error()
}

// TestContextReductionMatchesReference pins the fast path to the general
// path: context Add/Sub over the reduced operands (public entry points,
// unbudgeted and budgeted) returns what the unreduced reference seam returns
// over the full aligned span, on result, exponent, Conditions with the
// direction bit, error identity and trapped set, over drawReduction's corpus.
// Directions and, for unguarded non-Exact draws, values are also checked
// against math/big. A vacuity guard requires both reductions, and the
// conditions around them, to fire.
func TestContextReductionMatchesReference(t *testing.T) {
	r := rand.New(rand.NewPCG(62, 1))
	draws := 200_000
	if testing.Short() {
		draws = 30_000
	}
	seen := map[string]int{}
	for i := range draws {
		d := drawReduction(r, 3000)
		op := d.operation()
		want, wantConditions, wantErr := contextReferenceCall(d.a, d.b, op, d.ctx, Budget{MaxWork: math.MaxUint64})
		for _, budget := range []Budget{{}, {MaxWork: 1 << 40, MaxDigits: 1 << 20}} {
			got, conditions, err := d.call(budget)
			if !sameContextOutcome(got, conditions, err, want, wantConditions, wantErr) {
				t.Fatalf("draw %d %s %v %v %+v budget %+v: reduced %v %v %v; reference %v %v %v", i, op, d.a, d.b, d.ctx, budget, got, conditions, err, want, wantConditions, wantErr)
			}
			if budget != (Budget{}) || max(abs64(int64(d.a.exponent())), abs64(int64(d.b.exponent()))) > 4000 {
				continue
			}
			_, _, _, exact := contextDirectionCall(d.a, d.b, op, d.ctx, budget)
			label := "draw " + strconv.Itoa(i) + " " + op + " " + d.a.String() + " " + d.b.String()
			// A trapped result keeps its value; its trapped bits return to
			// the set for the check. Exact's refusal carries no value.
			all, valueErr := conditions, err
			if trapped := (*Error)(nil); errors.As(err, &trapped) && trapped.Code == 0 && !(d.ctx.rounding == Exact && trapped.Condition&Inexact != 0) {
				all, valueErr = conditions|trapped.Condition, nil
			}
			if checkRoundingDirection(t, label, exact, d.ctx.rounding, got, all, valueErr) {
				seen["oracle direction"]++
			}
			if !d.ctx.guarded && d.ctx.rounding != Exact && err == nil && got.isZero() == false {
				digits, exponent, negative, oracleConditions := contextOracle(d.a, d.b, op, d.ctx.precision, d.ctx.rounding)
				if got.coefficientDigits() != digits || int64(got.exponent()) != exponent || got.negative() != negative || conditions != oracleConditions {
					t.Fatalf("%s %+v: %s e%d %v; math/big %s e%d %v", label, d.ctx, got.coefficientDigits(), got.exponent(), conditions, digits, exponent, oracleConditions)
				}
				seen["oracle value"]++
			}
		}
		if !d.sticky && !d.clamp {
			seen["unreduced"]++
			continue
		}
		kind := "clamp"
		if d.sticky {
			kind = "sticky"
		}
		seen[kind]++
		var trapped *Error
		switch {
		case errors.As(wantErr, &trapped) && trapped.Code == 0 && d.ctx.rounding == Exact && trapped.Condition == Inexact && want.isZero() && !want.negative():
			seen[kind+" Exact refusal"]++
		case trapped != nil && trapped.Code == 0:
			seen[kind+" trapped"]++
		case errors.Is(wantErr, ErrExponentRange):
			seen[kind+" exponent range"]++
		}
		for name, bit := range map[string]Conditions{"Rounded": Rounded, "Inexact": Inexact, "Increased": Increased, "Decreased": Decreased, "Subnormal": Subnormal, "Overflow": Overflow} {
			if wantConditions&bit != 0 {
				seen[kind+" "+name]++
			}
		}
		if wantErr == nil && wantConditions&Rounded != 0 && wantConditions&Inexact == 0 {
			seen[kind+" zero-only discard"]++
		}
		if extreme := max(abs64(int64(d.a.exponent())), abs64(int64(d.b.exponent()))); extreme > math.MaxInt32-200 {
			seen[kind+" int32 limit"]++
		}
		if d.a.negative() != (d.b.negative() != d.sub) && !d.a.isZero() && !d.b.isZero() {
			seen[kind+" opposite signs (borrow)"]++
		}
		nines := func(x Decimal) bool { return strings.Trim(x.coefficientDigits(), "9") == "" && !x.isZero() }
		if wantErr == nil && wantConditions&Rounded != 0 && strings.TrimRight(want.coefficientDigits(), "0") == "1" && (nines(d.a) || nines(d.b)) {
			seen[kind+" carry"]++
		}
		if max(abs64(int64(d.a.exponent())), abs64(int64(d.b.exponent()))) <= 4000 {
			seen[kind+" math/big checked"]++
		}
	}
	t.Logf("reduction differential over %d draws: %v", draws, seen)
	minimum := draws / 2000
	for _, key := range []string{
		"sticky", "clamp", "sticky Rounded", "clamp Rounded", "sticky Inexact", "clamp Inexact",
		"sticky Increased", "sticky Decreased", "clamp Increased", "clamp Decreased",
		"sticky Subnormal", "clamp Subnormal", "sticky Overflow", "clamp Overflow",
		"clamp zero-only discard", "sticky Exact refusal", "clamp Exact refusal",
		"sticky trapped", "clamp trapped", "sticky int32 limit", "clamp int32 limit",
		"sticky exponent range", "clamp exponent range", "sticky opposite signs (borrow)",
		"sticky carry", "clamp carry", "sticky math/big checked", "clamp math/big checked",
		"oracle direction", "oracle value", "unreduced",
	} {
		if seen[key] < minimum {
			t.Fatalf("vacuous differential: %q fired %d times (< %d): %v", key, seen[key], minimum, seen)
		}
	}
	if seen["sticky"] < draws/5 || seen["clamp"] < draws/10 {
		t.Fatalf("reductions fired too rarely: %v", seen)
	}
}

func abs64(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

// TestContextReductionMonotoneCharges checks that the reduction never raises
// a charge. Over drawReduction's corpus, the smallest work cap the reduced
// path admits (B for a refusal reached after the precharge, W = B+2N+1 for a
// result) is at most the reference seam's, strictly less where a reduction
// fired, and the reduced path admits every work and digit cap the reference
// admits.
func TestContextReductionMonotoneCharges(t *testing.T) {
	r := rand.New(rand.NewPCG(62, 2))
	draws := 4000
	if testing.Short() {
		draws = 800
	}
	reduced := 0
	for i := range draws {
		d := drawReduction(r, 2000)
		op := d.operation()
		admitted := func(err error) bool { return !errors.Is(err, ErrInsufficientStorage) }
		refWork := smallestAdmitting(1<<40, func(w uint64) bool {
			_, _, err := contextReferenceCall(d.a, d.b, op, d.ctx, Budget{MaxWork: w})
			return admitted(err)
		})
		gotWork := smallestAdmitting(1<<40, func(w uint64) bool {
			_, _, err := d.call(Budget{MaxWork: w})
			return admitted(err)
		})
		label := "draw " + strconv.Itoa(i) + " " + op + " " + d.a.String() + " " + d.b.String()
		if gotWork > refWork || (d.sticky || d.clamp) && gotWork >= refWork {
			t.Fatalf("%s %+v: reduced smallest work %d, reference %d (sticky %v clamp %v)", label, d.ctx, gotWork, refWork, d.sticky, d.clamp)
		}
		if _, _, err := d.call(Budget{MaxWork: refWork}); !admitted(err) {
			t.Fatalf("%s: reference admits work %d, reduced refuses", label, refWork)
		}
		refDigits := smallestAdmitting(1<<20, func(n uint64) bool {
			_, _, err := contextReferenceCall(d.a, d.b, op, d.ctx, Budget{MaxDigits: n})
			return admitted(err)
		})
		if _, _, err := d.call(Budget{MaxDigits: refDigits}); !admitted(err) {
			t.Fatalf("%s: reference admits digit cap %d, reduced refuses", label, refDigits)
		}
		if d.sticky || d.clamp {
			reduced++
		}
	}
	if reduced < draws/4 {
		t.Fatalf("monotonicity corpus reduced only %d of %d draws", reduced, draws)
	}
}

// contextCallResult renders one context call as "value exponent conditions
// error" for comparison against hand-derived expectations.
func contextCallResult(d Decimal, c Conditions, err error) string {
	return d.String() + " " + strconv.Itoa(int(d.exponent())) + " " + c.String() + " " + fmt.Sprint(err)
}

// TestContextZeroValueIsExactTiesToEvenUnguardedUntrapped checks the zero
// Context: Context{} has unlimited precision (a 40-by-40-digit product equals
// the math/big product with no condition), rounds ties to even (2.5 -> 2, 3.5
// -> 4, -2.5 -> -2, 2.25 at 0.1 -> 2.2), applies no exponent guard at either
// int32 endpoint and traps nothing (inexact results return nil errors). A
// constructed context whose mode field is the zero RoundingMode also rounds
// 2.25 to 2.2 at p=2, where a silent half-up would give 2.3.
func TestContextZeroValueIsExactTiesToEvenUnguardedUntrapped(t *testing.T) {
	var zero Context
	if _, guarded := zero.ExponentGuards(); zero.Precision() != 0 || zero.Rounding() != TiesToEven || guarded || zero.Traps() != 0 {
		t.Fatalf("Context{} = precision %d, mode %v, guarded %v, traps %v", zero.Precision(), zero.Rounding(), guarded, zero.Traps())
	}
	for _, tc := range []struct {
		in   string
		want string
	}{
		{"2.5", "2 0 Inexact|Rounded|Decreased <nil>"},
		{"3.5", "4 0 Inexact|Rounded|Increased <nil>"},
		{"-2.5", "-2 0 Inexact|Rounded|Increased <nil>"},
		{"2.4999", "2 0 Inexact|Rounded|Decreased <nil>"},
	} {
		if got := contextCallResult(MustParse(tc.in).RoundToIntegralWithContext(zero)); got != tc.want {
			t.Errorf("RoundToIntegralWithContext(%s, Context{}) = %q, want %q", tc.in, got, tc.want)
		}
	}
	if got, want := contextCallResult(MustParse("2.25").QuantizeWithContext(-1, zero)), "2.2 -1 Inexact|Rounded|Decreased <nil>"; got != want {
		t.Errorf("QuantizeWithContext(2.25, -1, Context{}) = %q, want %q", got, want)
	}
	a := strings.Repeat("9", 40)
	b := "1234567890123456789012345678901234567891"
	x, _ := new(big.Int).SetString(a, 10)
	y, _ := new(big.Int).SetString(b, 10)
	want := new(big.Int).Mul(x, y).String() + " 0 0 <nil>"
	if got := contextCallResult(MustParse(a).MulWithContext(MustParse(b), zero)); got != want {
		t.Errorf("unlimited-precision product = %q, want %q", got, want)
	}
	for _, tc := range []struct {
		d    Decimal
		want string
	}{
		{New(1, math.MaxInt32), "1E+2147483647 2147483647 0 <nil>"},
		{New(1, math.MinInt32), "1E-2147483648 -2147483648 0 <nil>"},
		{New(-123, math.MinInt32), "-1.23E-2147483646 -2147483648 0 <nil>"},
	} {
		if got := contextCallResult(tc.d.MulWithContext(One(), zero)); got != tc.want {
			t.Errorf("unguarded endpoint %s = %q, want %q", tc.d, got, tc.want)
		}
	}
	zeroMode, err := NewContext(2, RoundingMode(0), nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct{ in, want string }{
		{"2.25", "2.2 -1 Inexact|Rounded|Decreased <nil>"},
		{"2.35", "2.4 -1 Inexact|Rounded|Increased <nil>"},
		{"-2.25", "-2.2 -1 Inexact|Rounded|Increased <nil>"},
	} {
		if got := contextCallResult(MustParse(tc.in).AddWithContext(Zero(), zeroMode)); got != tc.want {
			t.Errorf("zero-mode p=2 context rounds %s to %q, want %q (TiesToEven)", tc.in, got, tc.want)
		}
	}
}

// TestPresetsNeverClampExponent checks that no preset clamps: under
// Decimal32/64/128, a one-digit coefficient at the adjusted exponent Emax
// stays coefficient 1 at exponent Emax through context multiplication and
// precision rounding, with no condition. A GDA clamp=1 context would pad it
// to exponent Emax-(p-1) with p-1 trailing zeros and report Clamped.
func TestPresetsNeverClampExponent(t *testing.T) {
	for _, tc := range []struct {
		name string
		ctx  Context
		emax int32
		want string
	}{
		{"Decimal32", Decimal32Context(), 96, "1E+96"},
		{"Decimal64", Decimal64Context(), 384, "1E+384"},
		{"Decimal128", Decimal128Context(), 6144, "1E+6144"},
	} {
		for op, run := range map[string]func() (Decimal, Conditions, error){
			"MulWithContext":              func() (Decimal, Conditions, error) { return New(1, tc.emax).MulWithContext(One(), tc.ctx) },
			"RoundToPrecisionWithContext": func() (Decimal, Conditions, error) { return New(1, tc.emax).RoundToPrecisionWithContext(tc.ctx) },
			"QuantizeWithContext":         func() (Decimal, Conditions, error) { return New(1, tc.emax).QuantizeWithContext(tc.emax, tc.ctx) },
		} {
			d, c, err := run()
			if err != nil || c != 0 || d.String() != tc.want || d.exponent() != tc.emax || d.CoefficientDigits() != 1 {
				t.Errorf("%s %s(1E+%d) = %s at exponent %d, %d digits, %v, %v; want %s unclamped", tc.name, op, tc.emax, d, d.exponent(), d.CoefficientDigits(), c, err, tc.want)
			}
		}
	}
}

// TestRoundingCatalogHasExactlyEightModes checks that excluded modes stay
// out: the parsed RoundingMode constant block is exactly the eight
// names with values 0..7, an out-of-catalog value names itself
// RoundingMode(8), and no exported identifier of the library names a 05up or
// half-odd mode. The exclusion pattern is checked on hand-written samples
// first.
func TestRoundingCatalogHasExactlyEightModes(t *testing.T) {
	excluded := regexp.MustCompile(`(?i)05up|half[-_ ]?odd|roundup05|zerofiveup`)
	for name, want := range map[string]bool{
		"Round05Up": true, "HalfOdd": true, "TiesToOdd": false, "ROUND_05UP": true, "RoundHalf_Odd": true,
		"TiesToEven": false, "AwayFromZero": false,
	} {
		if excluded.MatchString(name) != want {
			t.Fatalf("exclusion pattern on %s = %v, want %v", name, !want, want)
		}
	}
	wantModes := []string{"TiesToEven", "TiesAwayFromZero", "TiesTowardZero", "TowardZero",
		"AwayFromZero", "TowardPositiveInfinity", "TowardNegativeInfinity", "Exact"}
	fset := token.NewFileSet()
	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	var modes []string
	exported := 0
	for _, file := range files {
		if strings.HasSuffix(file, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(fset, file, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatal(err)
		}
		ast.Inspect(f, func(n ast.Node) bool {
			ident, ok := n.(*ast.Ident)
			if ok && ident.IsExported() {
				exported++
				if excluded.MatchString(ident.Name) {
					t.Errorf("%s: exported identifier %s names an excluded mode", fset.Position(ident.Pos()), ident.Name)
				}
			}
			return true
		})
		for _, decl := range f.Decls {
			gen, ok := decl.(*ast.GenDecl)
			if !ok || gen.Tok != token.CONST {
				continue
			}
			inBlock := false
			for i, spec := range gen.Specs {
				vs := spec.(*ast.ValueSpec)
				if i == 0 {
					ident, ok := vs.Type.(*ast.Ident)
					inBlock = ok && ident.Name == "RoundingMode"
				} else if vs.Type != nil {
					inBlock = false
				}
				if inBlock {
					for _, n := range vs.Names {
						modes = append(modes, n.Name)
					}
				}
			}
		}
	}
	if !slices.Equal(modes, wantModes) {
		t.Fatalf("RoundingMode constants = %v, want exactly %v", modes, wantModes)
	}
	if exported < 500 {
		t.Fatalf("scanned only %d exported identifier uses", exported)
	}
	for i, name := range wantModes {
		if got := RoundingMode(i).String(); got != name {
			t.Errorf("RoundingMode(%d) = %s, want %s", i, got, name)
		}
	}
	if got := RoundingMode(8).String(); got != "RoundingMode(8)" {
		t.Errorf("RoundingMode(8) = %s, want RoundingMode(8)", got)
	}
	if _, err := NewContext(1, RoundingMode(8), nil, 0); !errors.Is(err, ErrInvalidContext) {
		t.Errorf("NewContext with mode 8 error = %v, want ErrInvalidContext", err)
	}
}

// TestUnguardedArithmeticEmitsNoGuardConditions checks that guard conditions
// cannot arise unguarded: under Context{} and an unguarded p=1 context that
// traps Overflow, Underflow and Subnormal, results at both int32 exponent
// endpoints are exact, rounded or a range-family error with condition 0, and
// an exact-regime budget excess is an InsufficientStorage Error; none emits
// Overflow, Underflow or Subnormal, even with those three trapped. Vectors
// are hand-derived.
func TestUnguardedArithmeticEmitsNoGuardConditions(t *testing.T) {
	trapping, err := NewContext(1, TiesToEven, nil, Overflow|Underflow|Subnormal)
	if err != nil {
		t.Fatal(err)
	}
	maxNine, tinyOne := New(9, math.MaxInt32), New(1, math.MinInt32)
	tiny15 := New(15, math.MinInt32)
	three := New(3, 0)
	type result struct {
		want    string // exact result text, or "" for an error
		wantErr error
		cond    Conditions
	}
	cases := []struct {
		name string
		run  func(Context) (Decimal, Conditions, error)
		zero result
		p1   result
	}{
		{"9E+MaxInt32 + 9E+MaxInt32", func(c Context) (Decimal, Conditions, error) { return maxNine.AddWithContext(maxNine, c) },
			result{"1.8E+2147483648", nil, 0}, result{"", ErrExponentRange, 0}},
		{"1E+MinInt32 x 1E-1", func(c Context) (Decimal, Conditions, error) { return tinyOne.MulWithContext(New(1, -1), c) },
			result{"", ErrExponentRange, 0}, result{"", ErrExponentRange, 0}},
		{"15E+MinInt32 + 0", func(c Context) (Decimal, Conditions, error) { return tiny15.AddWithContext(Zero(), c) },
			result{"1.5E-2147483647", nil, 0}, result{"2E-2147483647", nil, Inexact | Rounded | Increased}},
		{"1E+MinInt32 / 3", func(c Context) (Decimal, Conditions, error) { return tinyOne.DivWithContext(three, c) },
			result{"", ErrInexact, 0}, result{"", ErrExponentRange, 0}},
		{"budgeted 40x40 digits", func(c Context) (Decimal, Conditions, error) {
			v := MustParse(strings.Repeat("7", 40))
			return v.MulWithContext(v, c.WithBudget(Budget{MaxDigits: 10}))
		}, result{"", ErrInsufficientStorage, 0}, result{"6E+79", nil, Inexact | Rounded | Decreased}},
	}
	for _, tc := range cases {
		for _, run := range []struct {
			ctx  Context
			want result
		}{{Context{}, tc.zero}, {trapping, tc.p1}} {
			d, c, err := tc.run(run.ctx)
			var condErr *Error
			if c&(Overflow|Underflow|Subnormal) != 0 || errors.As(err, &condErr) && condErr.Condition&(Overflow|Underflow|Subnormal) != 0 {
				t.Errorf("%s (precision %d) emitted a guard condition: %v, %v", tc.name, run.ctx.Precision(), c, err)
			}
			if run.want.want == "" {
				var opErr *Error
				if !errors.Is(err, run.want.wantErr) || c != 0 || !reflect.DeepEqual(d, Decimal{}) {
					t.Errorf("%s (precision %d) = %s, %v, %v; want Decimal{}, 0, %v", tc.name, run.ctx.Precision(), d, c, err, run.want.wantErr)
				}
				if run.want.wantErr != ErrInexact && (!errors.As(err, &opErr) || opErr.Condition&(Overflow|Underflow|Subnormal) != 0) {
					t.Errorf("%s (precision %d) error %v is not a guard-free Error", tc.name, run.ctx.Precision(), err)
				}
				continue
			}
			if err != nil || c != run.want.cond || d.String() != run.want.want {
				t.Errorf("%s (precision %d) = %s, %v, %v; want %s, %v", tc.name, run.ctx.Precision(), d, c, err, run.want.want, run.want.cond)
			}
		}
	}
}

// reduceTestShape draws a Shape for the planner differentials: zero one
// time in five, and exponents placed around the other shape's reduction
// thresholds (its last digit, its rounding position, Etiny), so both the
// sticky substitution and the zero clamp fire on either side.
func reduceTestShape(r *rand.Rand, other Shape, p int64) Shape {
	s := Shape{Digits: uint64(1 + r.IntN(40)), Negative: r.IntN(2) == 0}
	if r.IntN(5) == 0 {
		s.Digits, s.Negative = 0, false
	}
	adj := int64(other.Exponent) + int64(max(other.Digits, 1)) - 1
	anchor := []int64{int64(other.Exponent), adj - p, adj - p - int64(s.Digits), int64(other.Exponent) - int64(s.Digits)}[r.IntN(4)]
	s.Exponent = int32(max(min(anchor+int64(r.IntN(9)-4), math.MaxInt32), math.MinInt32))
	return s
}

// TestReduceSpansMatchShapes pins FMA's span planner (contextReduceSpans) to
// the Shape planner, which Add and Sub keep: over shape pairs placed around
// every reduction threshold, zeros, both signs, precisions 1..40, guards and
// exponents at the int32 ends, the span planner with exact digit brackets (lo
// = hi) returns exactly the Shape planner's reduction. A vacuity guard
// requires the unchanged case, both sticky substitutions and both zero
// clamps.
func TestReduceSpansMatchShapes(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 67))
	seen := map[string]int{}
	for i := range 200000 {
		p := int64(1 + r.IntN(40))
		var guards *ExponentGuards
		if r.IntN(3) == 0 {
			emin := int32(-r.IntN(60))
			guards = &ExponentGuards{Emin: emin, Emax: emin + int32(r.IntN(120))}
		}
		ctx := contextTestContext(t, uint32(p), TiesToEven, guards, 0)
		x := Shape{Digits: uint64(1 + r.IntN(40)), Exponent: int32(r.IntN(81) - 40), Negative: r.IntN(2) == 0}
		switch {
		case i%50 == 0:
			x.Exponent = math.MaxInt32 - int32(r.IntN(40))
		case i%50 == 1:
			x.Exponent = math.MinInt32 + int32(r.IntN(40))
		}
		y := reduceTestShape(r, x, p)
		if r.IntN(2) == 0 {
			x, y = y, x
		}
		rx, ry := contextReduceShapes(x, y, ctx)
		sx, sy := contextReduceSpans(spanOf(x), spanOf(y), ctx)
		if sx != spanOf(rx) || sy != spanOf(ry) {
			t.Fatalf("%+v %+v %+v: spans %+v %+v, shapes %+v %+v", x, y, ctx, sx, sy, rx, ry)
		}
		switch {
		case rx == x && ry == y:
			seen["unchanged"]++
		case x.Digits == 0 && rx.Exponent != x.Exponent:
			seen["zero x clamped"]++
		case y.Digits == 0 && ry.Exponent != y.Exponent:
			seen["zero y clamped"]++
		case rx != x:
			seen["x substituted"]++
		default:
			seen["y substituted"]++
		}
	}
	for _, kind := range []string{"unchanged", "zero x clamped", "zero y clamped", "x substituted", "y substituted"} {
		if seen[kind] < 1000 {
			t.Fatalf("vacuous: %v", seen)
		}
	}
}

// contextAddSubStaged runs FMA's term-form context plan over Decimal
// operands as FMA runs it with no prior work: terms, the span planner,
// admission and the finisher.
func contextAddSubStaged(d, other Decimal, ctx Context, budget Budget, subtract bool) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		result, err := d.addSub(other, budget.arith(), "AddWithContext", subtract)
		return result, 0, err
	}
	var a, b addTerm
	if !a.load(d, false) || !b.load(other, subtract) {
		return contextFailure("AddWithContext", ErrInsufficientStorage)
	}
	sa := reduceSpan{exponent: a.exponent, negative: a.negative}
	if !a.zero {
		sa.lo, sa.hi = a.digits, a.digits
	}
	sb := reduceSpan{exponent: b.exponent, negative: b.negative}
	if !b.zero {
		sb.lo, sb.hi = b.digits, b.digits
	}
	ra, rb := contextReduceSpans(sa, sb, ctx)
	a.reduce(sa, ra)
	b.reduce(sb, rb)
	var p contextAddSubPlan
	if err := p.admit(&a, &b, budget.arith(), 0, "AddWithContext"); err != nil {
		return Decimal{}, 0, err
	}
	return p.finish(&a, &b, ctx, budget.arith(), "AddWithContext")
}

// TestContextAddSubPlanMatchesKernel pins FMA's term-form context plan
// (contextAddSubPlan with the span planner) to the Decimal kernel
// contextAddSub in charges and refusals, not only in results: over operand
// pairs around the reduction thresholds, zeros, cancellations, all eight
// modes and guards, the smallest admitting work and digit caps are equal, and
// at each cap, one below it and one above it the two return the same
// representation, Conditions and error. A vacuity guard requires refusals,
// reductions and every path.
func TestContextAddSubPlanMatchesKernel(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 69))
	seen := map[string]int{}
	const op = "AddWithContext"
	for range 6000 {
		p := int64(1 + r.IntN(30))
		var guards *ExponentGuards
		if r.IntN(3) == 0 {
			emin := int32(-r.IntN(50))
			guards = &ExponentGuards{Emin: emin, Emax: emin + int32(r.IntN(100))}
		}
		ctx := contextTestContext(t, uint32(p), fmaModes[r.IntN(len(fmaModes))], guards, 0)
		x := fmaOperand(r, 45, -30, 30)
		ys := reduceTestShape(r, x.Shape(), p)
		var y Decimal
		switch {
		case r.IntN(6) == 0:
			y = x.Neg()
		case ys.Digits == 0:
			y = zeroDecimal(ys.Exponent)
		default:
			c := randomDigits(r, int(ys.Digits))
			if ys.Negative {
				c.Neg(c)
			}
			y = sqrtDecimal(c, int64(ys.Exponent))
		}
		subtract := r.IntN(2) == 0
		kernel := func(b Budget) (Decimal, Conditions, error) {
			return x.contextAddSub(y, ctx.withLimits(b.arith()), op, subtract, true, nil)
		}
		staged := func(b Budget) (Decimal, Conditions, error) {
			return contextAddSubStaged(x, y, ctx, b, subtract)
		}
		admits := func(f func(Budget) (Decimal, Conditions, error), b Budget) bool {
			_, _, err := f(b)
			return !errors.Is(err, ErrInsufficientStorage)
		}
		work := smallestAdmitting(1<<40, func(w uint64) bool { return admits(kernel, Budget{MaxWork: w}) })
		digits := smallestAdmitting(1<<40, func(n uint64) bool { return admits(kernel, Budget{MaxDigits: n}) })
		label := fmt.Sprintf("%v %v sub=%v %+v", x, y, subtract, ctx)
		if w := smallestAdmitting(1<<40, func(w uint64) bool { return admits(staged, Budget{MaxWork: w}) }); w != work {
			t.Fatalf("%s: plan work cap %d, kernel %d", label, w, work)
		}
		if n := smallestAdmitting(1<<40, func(n uint64) bool { return admits(staged, Budget{MaxDigits: n}) }); n != digits {
			t.Fatalf("%s: plan digit cap %d, kernel %d", label, n, digits)
		}
		for _, b := range []Budget{{MaxWork: work}, {MaxWork: work - 1}, {MaxWork: work + 1}, {MaxDigits: digits}, {MaxDigits: digits - 1}} {
			want, wantConditions, wantErr := kernel(b)
			got, conditions, err := staged(b)
			if !sameRepresentation(got, want) || conditions != wantConditions || (err == nil) != (wantErr == nil) || err != nil && err.Error() != wantErr.Error() {
				t.Fatalf("%s budget %+v: plan %v %v %v, kernel %v %v %v", label, b, got, conditions, err, want, wantConditions, wantErr)
			}
			if errors.Is(err, ErrInsufficientStorage) {
				seen["refused"]++
			}
		}
		sx, sy := x.Shape(), y.Shape()
		sy.Negative = sy.Negative != subtract && sy.Digits != 0
		rx, ry := contextReduceShapes(sx, sy, ctx)
		switch {
		case rx != sx || ry != sy:
			seen["reduced"]++
		case x.isZero() || y.isZero():
			seen["zero"]++
		case x.negative() != (y.negative() != subtract):
			seen["opposite"]++
		default:
			seen["same"]++
		}
	}
	for _, kind := range []string{"refused", "reduced", "zero", "opposite", "same"} {
		if seen[kind] < 100 {
			t.Fatalf("vacuous: %v", seen)
		}
	}
}

// TestContextNegativeResidueBelowNmin covers a decFinalize-style Nmin hazard.
// The exact magnitude 0.01 - 0.0000001 = 0.0099999 is below Nmin=0.01. At
// p=3, Emin=-2, Etiny=-4 it rounds to 0.0099 or 0.0100; both outcomes retain
// the pre-round Subnormal/Underflow events. This is a signed cancellation
// witness, independent of RemNear semantics.
func TestContextNegativeResidueBelowNmin(t *testing.T) {
	for _, negative := range []bool{false, true} {
		for mode := TiesToEven; mode <= Exact; mode++ {
			for _, operation := range []string{"add", "sub"} {
				t.Run(fmt.Sprintf("negative=%v/mode=%d/%s", negative, mode, operation), func(t *testing.T) {
					a, b := New(1, -2), New(1, -7)
					if negative {
						a, b = a.Neg(), b.Neg()
					}
					if operation == "add" {
						b = b.Neg()
					}
					ctx := contextTestContext(t, 3, mode, &ExponentGuards{Emin: -2, Emax: 2}, 0)
					got, conditions, err, exact := contextDirectionCall(a, b, operation, ctx, Budget{})
					if mode == Exact {
						if !errors.Is(err, ErrInexact) || conditions != 0 || !reflect.DeepEqual(got, Decimal{}) {
							t.Fatalf("Nmin Exact refusal: got %+v, %v, %v", got, conditions, err)
						}
						return
					}
					up := mode == TiesToEven || mode == TiesAwayFromZero || mode == TiesTowardZero || mode == AwayFromZero || mode == TowardPositiveInfinity && !negative || mode == TowardNegativeInfinity && negative
					coefficient := "99"
					direction := Decreased
					if up {
						coefficient = "100"
					}
					if up != negative {
						direction = Increased
					}
					wantConditions := Inexact | Rounded | Subnormal | Underflow | direction
					if err != nil || got.coefficientDigits() != coefficient || got.exponent() != -4 || got.negative() != negative || conditions != wantConditions {
						t.Fatalf("Nmin residue: got %s e%d negative=%v conditions=%v error=%v; want %s e-4 negative=%v conditions=%v", got.coefficientDigits(), got.exponent(), got.negative(), conditions, err, coefficient, negative, wantConditions)
					}
					checkRoundingDirection(t, "Nmin residue", exact, mode, got, conditions, err)
				})
			}
		}
	}
}

// roundTenthsOracle rounds a two-decimal operand, written as n hundredths,
// to tenths under mode by the mode's defining rule on the integer quotient
// and remainder, independent of the library's rounding kernel. ok is false
// when Exact must refuse.
func roundTenthsOracle(n int64, mode RoundingMode) (tenths int64, ok bool) {
	q, r := n/10, n%10 // truncation toward zero
	if r < 0 {
		r = -r
	}
	sign := int64(1)
	if n < 0 {
		sign = -1
	}
	away := func(up bool) int64 {
		if up {
			return q + sign
		}
		return q
	}
	switch mode {
	case TiesToEven:
		return away(r > 5 || r == 5 && q%2 != 0), true
	case TiesAwayFromZero:
		return away(r >= 5), true
	case TiesTowardZero:
		return away(r > 5), true
	case TowardZero:
		return q, true
	case AwayFromZero:
		return away(r != 0), true
	case TowardPositiveInfinity:
		return away(r != 0 && sign > 0), true
	case TowardNegativeInfinity:
		return away(r != 0 && sign < 0), true
	default: // Exact
		return q, r == 0
	}
}

// TestRoundingModeWorkedTable checks the worked rounding tables, including
// negative ties: the RoundingMode reference documentation carries a worked
// table with a row for every mode and negative tie operands (−2.35 and −2.45
// to one decimal place), and every constant's own documentation shows a
// negative tie. Each table cell and each "a → b" example in a constant's
// documentation equals both an integer oracle of the mode's defining rule and
// the library's Quantize(-1, mode), with Exact's refusals reported as
// ErrInexact.
func TestRoundingModeWorkedTable(t *testing.T) {
	for _, tc := range []struct {
		n    int64
		mode RoundingMode
		want int64
	}{{-235, TiesToEven, -24}, {-245, TiesToEven, -24}, {-245, TiesAwayFromZero, -25}, {-236, TowardZero, -23}, {-234, TowardNegativeInfinity, -24}} {
		if got, _ := roundTenthsOracle(tc.n, tc.mode); got != tc.want {
			t.Fatalf("oracle %d under %s = %d, want %d", tc.n, tc.mode, got, tc.want)
		}
	}
	check := func(where, operand, shown string, mode RoundingMode) {
		t.Helper()
		n, err := strconv.ParseInt(strings.Replace(operand, ".", "", 1), 10, 64)
		if err != nil || !regexp.MustCompile(`^-?\d\.\d\d$`).MatchString(operand) {
			t.Fatalf("%s: operand %q is not a two-decimal value", where, operand)
		}
		got, _, qerr := MustParse(operand).Quantize(-1, mode)
		want, ok := roundTenthsOracle(n, mode)
		if !ok {
			if shown != "refused" || !errors.Is(qerr, ErrInexact) {
				t.Errorf("%s: %s under %s shows %q, library err %v; want refused", where, operand, mode, shown, qerr)
			}
			return
		}
		wantText := strconv.FormatFloat(float64(want)/10, 'f', 1, 64)
		if shown != wantText || qerr != nil || got.String() != wantText {
			t.Errorf("%s: %s under %s shows %q, library %s (%v), oracle %s", where, operand, mode, shown, got, qerr, wantText)
		}
	}

	f, err := parser.ParseFile(token.NewFileSet(), "context.go", nil, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		t.Fatal(err)
	}
	var typeDoc *ast.CommentGroup
	constDocs := map[string]string{}
	for _, decl := range f.Decls {
		gd, ok := decl.(*ast.GenDecl)
		if !ok {
			continue
		}
		for _, spec := range gd.Specs {
			switch spec := spec.(type) {
			case *ast.TypeSpec:
				if spec.Name.Name == "RoundingMode" {
					typeDoc = gd.Doc
				}
			case *ast.ValueSpec:
				if gd.Tok == token.CONST && spec.Doc != nil {
					constDocs[spec.Names[0].Name] = spec.Doc.Text()
				}
			}
		}
	}
	if typeDoc == nil {
		t.Fatal("RoundingMode has no documentation")
	}
	var header []string
	rows := map[string]bool{}
	for _, c := range typeDoc.List {
		line, ok := strings.CutPrefix(c.Text, "//\t")
		if !ok {
			continue
		}
		fields := strings.Fields(line)
		if fields[0] == "mode" {
			header = fields[1:]
			continue
		}
		if len(header) == 0 || len(fields) != len(header)+1 {
			t.Fatalf("worked-table row %q does not match header %q", line, header)
		}
		rows[fields[0]] = true
		mode := slices.IndexFunc(roundingModeNames[:], func(name string) bool { return name == fields[0] })
		if mode < 0 {
			t.Fatalf("worked table names unknown mode %q", fields[0])
		}
		for i, operand := range header {
			check("RoundingMode table", operand, fields[i+1], RoundingMode(mode))
		}
	}
	if len(rows) != len(roundingModeNames) {
		t.Fatalf("worked table has rows %v, want every mode", rows)
	}
	if !slices.Contains(header, "-2.35") || !slices.Contains(header, "-2.45") {
		t.Fatalf("worked table operands %q lack the negative ties -2.35 and -2.45", header)
	}

	arrow := regexp.MustCompile(`(−?\d\.\d\d) → (−?\d\.\d)`)
	for _, name := range roundingModeNames {
		d := constDocs[name]
		examples := arrow.FindAllStringSubmatch(d, -1)
		negativeTie := regexp.MustCompile(`−2\.[34]5\b`).MatchString(d)
		if !negativeTie {
			t.Errorf("%s documentation has no negative tie example: %q", name, d)
		}
		mode := RoundingMode(slices.Index(roundingModeNames[:], name))
		for _, m := range examples {
			check(name+" doc", strings.ReplaceAll(m[1], "−", "-"), strings.ReplaceAll(m[2], "−", "-"), mode)
		}
		if name == "Exact" {
			check("Exact doc", "-2.35", "refused", Exact)
			if !strings.Contains(d, "−2.35 are refused") {
				t.Errorf("Exact documentation does not show the refused negative tie: %q", d)
			}
		} else if len(examples) < 3 {
			t.Errorf("%s documentation has %d worked examples, want at least 3", name, len(examples))
		}
	}
}

// Budgeted-call adapters: tests table these shapes as function values; the
// public form carries the budget in the Context.
func addWithBudget(d, o Decimal, b Budget) (Decimal, error) {
	r, _, err := d.AddWithContext(o, Context{}.WithBudget(b))
	return r, err
}

func subWithBudget(d, o Decimal, b Budget) (Decimal, error) {
	r, _, err := d.SubWithContext(o, Context{}.WithBudget(b))
	return r, err
}

func mulWithBudget(d, o Decimal, b Budget) (Decimal, error) {
	r, _, err := d.MulWithContext(o, Context{}.WithBudget(b))
	return r, err
}

func addWithContextAndBudget(d, o Decimal, ctx Context, b Budget) (Decimal, Conditions, error) {
	return d.AddWithContext(o, ctx.WithBudget(b))
}

func subWithContextAndBudget(d, o Decimal, ctx Context, b Budget) (Decimal, Conditions, error) {
	return d.SubWithContext(o, ctx.WithBudget(b))
}

func mulWithContextAndBudget(d, o Decimal, ctx Context, b Budget) (Decimal, Conditions, error) {
	return d.MulWithContext(o, ctx.WithBudget(b))
}

func quantizeWithContextAndBudget(d Decimal, e int32, ctx Context, b Budget) (Decimal, Conditions, error) {
	return d.QuantizeWithContext(e, ctx.WithBudget(b))
}

func roundToIntegralWithContextAndBudget(d Decimal, ctx Context, b Budget) (Decimal, Conditions, error) {
	return d.RoundToIntegralWithContext(ctx.WithBudget(b))
}

func fromRatWithContextAndBudget(r *big.Rat, ctx Context, b Budget) (Decimal, Conditions, error) {
	return FromRatWithContext(r, ctx.WithBudget(b))
}

// TestContextDerivations checks that WithPrecision, WithRounding, WithGuards
// and WithoutGuards change exactly one component, keep the budget, validate
// as NewContext validates (hand-derived invalid cases), never mutate the
// receiver, and fail with Context{} and an ErrInvalidContext error naming the
// method.
func TestContextDerivations(t *testing.T) {
	budget := Budget{MaxDigits: 40, MaxWork: 900}
	base := Decimal64Context().WithBudget(budget)
	frozen := base
	p, err := base.WithPrecision(7)
	if err != nil || p.Precision() != 7 || p.Rounding() != base.Rounding() || p.Budget() != budget || p.Traps() != base.Traps() {
		t.Fatalf("WithPrecision = %+v, %v", p, err)
	}
	if g, ok := p.ExponentGuards(); !ok || g != (ExponentGuards{Emin: -383, Emax: 384}) {
		t.Fatalf("WithPrecision lost guards: %+v %v", g, ok)
	}
	r, err := base.WithRounding(TiesAwayFromZero)
	if err != nil || r.Rounding() != TiesAwayFromZero || r.Precision() != 16 || r.Budget() != budget {
		t.Fatalf("WithRounding = %+v, %v", r, err)
	}
	g, err := base.WithGuards(ExponentGuards{Emin: -10, Emax: 10})
	if got, ok := g.ExponentGuards(); err != nil || !ok || got != (ExponentGuards{Emin: -10, Emax: 10}) || g.Budget() != budget {
		t.Fatalf("WithGuards = %+v, %v", g, err)
	}
	if _, ok := base.WithoutGuards().ExponentGuards(); ok || base.WithoutGuards().Budget() != budget {
		t.Fatal("WithoutGuards kept the guards or lost the budget")
	}
	if base != frozen {
		t.Fatal("a derivation mutated the receiver")
	}
	// Precision 0 is unlimited and cannot carry guards; Emin above Emax and
	// an unknown mode are invalid, exactly as NewContext rules.
	_, err = base.WithPrecision(0)
	assertInvalidContextOp(t, err, "Context.WithPrecision")
	if c, err := base.WithoutGuards().WithPrecision(0); err != nil || c.Precision() != 0 {
		t.Fatalf("unguarded precision 0: %+v, %v", c, err)
	}
	_, err = base.WithRounding(RoundingMode(99))
	assertInvalidContextOp(t, err, "Context.WithRounding")
	_, err = base.WithGuards(ExponentGuards{Emin: 5, Emax: 4})
	assertInvalidContextOp(t, err, "Context.WithGuards")
	if c, err := base.WithGuards(ExponentGuards{Emin: 5, Emax: 4}); c != (Context{}) || err == nil {
		t.Fatalf("failed derivation returned %+v", c)
	}
}

func assertInvalidContextOp(t *testing.T, err error, op string) {
	t.Helper()
	var e *Error
	if !errors.As(err, &e) || e.Op != op || e.Code != ErrInvalidContext || e.Condition != InvalidContext {
		t.Fatalf("%s: %v; want an ErrInvalidContext error", op, err)
	}
}

// farProductOracle is fmaOracle for an exact product whose exponent may lie
// billions of decades from the guards, where fmaOracle would build the
// power of ten between them. Far above Emax the outcome is the overflow
// substitution; a tiny product more than a digit below the Etiny quantum
// keeps no digit, so only the directed modes that round away from the
// discarded part publish one unit. Both are decided without that power.
func farProductOracle(exact *big.Int, ideal, p int64, mode RoundingMode, g fmaGuards) fmaWant {
	if !g.on || exact.Sign() == 0 {
		return fmaOracle(exact, ideal, p, mode, g)
	}
	negative := exact.Sign() < 0
	toward, away := Decreased, Increased // the result's magnitude is below or above the exact one
	if negative {
		toward, away = Increased, Decreased
	}
	length := fmaDigits(new(big.Int).Abs(exact))
	etiny := g.emin - (p - 1)
	switch adjusted := ideal + length - 1; {
	case adjusted > g.emax:
		if mode == Exact {
			return fmaWant{refused: true}
		}
		nines := new(big.Int).Sub(pow10Big(p), big.NewInt(1))
		return fmaWant{coefficient: nines, exponent: g.emax - p + 1, negative: negative, conditions: Overflow | Inexact | Rounded | toward}
	case etiny-ideal > length+1:
		if mode == Exact {
			return fmaWant{refused: true}
		}
		conditions := Rounded | Inexact | Subnormal | Underflow
		if mode == AwayFromZero || mode == TowardPositiveInfinity && !negative || mode == TowardNegativeInfinity && negative {
			return fmaWant{coefficient: big.NewInt(1), exponent: etiny, negative: negative, conditions: conditions | away}
		}
		return fmaWant{coefficient: new(big.Int), exponent: etiny, conditions: conditions | toward}
	}
	return fmaOracle(exact, ideal, p, mode, g)
}

// TestMulWithContextRoundsBeforeExponentRange pins MulWithContext to the
// math/big oracle where the exponent sum leaves int32: the product is
// rounded once, guards report Overflow or Underflow, and ErrExponentRange
// is returned only for a result whose own exponent cannot be stored.
func TestMulWithContextRoundsBeforeExponentRange(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x6d756c, 31))
	type bounds struct{ lo, hi int32 }
	high, low, middle := bounds{math.MaxInt32 - 60, math.MaxInt32}, bounds{math.MinInt32, math.MinInt32 + 60}, bounds{-40, 40}
	pairs := [][2]bounds{{high, high}, {low, low}, {high, middle}, {low, middle}, {high, low}}
	var beyond, published, refused, flagged int
	for i := range 60000 {
		pair := pairs[i%len(pairs)]
		x := fmaOperand(rng, 45, pair[0].lo, pair[0].hi)
		y := fmaOperand(rng, 45, pair[1].lo, pair[1].hi)
		p := []int64{1, 3, 7, 16, 34}[rng.IntN(5)]
		mode := RoundingMode(rng.IntN(int(Exact) + 1))
		g := fmaGuards{}
		var guards *ExponentGuards
		if rng.IntN(2) == 0 {
			g = fmaGuards{on: true, emin: -383, emax: 384}
			guards = &ExponentGuards{Emin: -383, Emax: 384}
		}
		ctx, err := NewContext(uint32(p), mode, guards, 0)
		if err != nil {
			t.Fatal(err)
		}
		exact := new(big.Int).Mul(contextTestCoefficient(x), contextTestCoefficient(y))
		ideal := int64(x.exponent()) + int64(y.exponent())
		want := farProductOracle(exact, ideal, p, mode, g)
		got, conditions, err := x.MulWithContext(y, ctx)
		fmaCheck(t, fmt.Sprintf("%v × %v at precision %d, %v, guards %t", x, y, p, mode, g.on), got, conditions, err, want)
		if ideal < math.MinInt32 || ideal > math.MaxInt32 {
			beyond++
			switch {
			case want.rangeError:
				refused++
			case !want.refused:
				published++
				if want.conditions&(Overflow|Underflow) != 0 {
					flagged++
				}
			}
		}
		// The estimate admits whatever the operation does.
		if cost, cerr := EstimateMul(x.Shape(), y.Shape(), ctx); cerr != nil {
			t.Fatalf("EstimateMul(%v, %v): %v", x, y, cerr)
		} else if err == nil {
			if _, _, berr := x.MulWithContext(y, ctx.WithBudget(Budget{MaxDigits: cost.Digits, MaxWork: cost.WorkUnits})); berr != nil {
				t.Fatalf("%v × %v refused its own estimate %+v: %v", x, y, cost, berr)
			}
		}
	}
	if beyond < 20000 || published < 5000 || refused < 5000 || flagged < 2000 {
		t.Fatalf("vacuous path coverage: %d sums beyond int32, %d published, %d refused, %d overflowed or underflowed", beyond, published, refused, flagged)
	}
}

// TestContextInlineRoundingMatchesGeneral pins the inline rounding of an
// exact 128-bit sum or product to the general context path, which a
// never-binding budget selects: every precision that can round an inline
// value, every mode, guards tight enough to make results tiny or overflow,
// traps, operands of one and two words at ordinary and extreme exponents,
// and the all-nines sums and products that carry into a new digit.
func TestContextInlineRoundingMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x696e6c, 11))
	general := Budget{MaxWork: math.MaxUint64}
	operand := func() Decimal {
		var w uint128
		switch rng.IntN(7) {
		case 0:
			w.lo = rng.Uint64()
		case 1:
			w.lo = rng.Uint64N(100_000_000)
		case 2: // all nines
			w.lo = pow10Words[1+rng.IntN(19)] - 1
		case 3: // a power of ten, or one beside it
			w.lo = pow10Words[rng.IntN(20)] + uint64(rng.IntN(3)) - 1
		case 4: // a half beyond some digit
			w.lo = uint64(1+rng.IntN(999))*pow10Words[1+rng.IntN(15)] + 5*pow10Words[rng.IntN(15)]
		case 5: // two words
			w = uint128{rng.Uint64(), rng.Uint64N(1 << uint(1+rng.IntN(60)))}
			if rng.IntN(4) == 0 { // a power of ten beyond one word, or one beside it
				w = pow10Wide[20+rng.IntN(19)]
				w.lo += uint64(rng.IntN(3)) - 1
			}
		default:
			w.lo = rng.Uint64N(1 << uint(1+rng.IntN(63)))
		}
		exponent := int32(rng.IntN(41) - 20)
		switch rng.IntN(40) {
		case 0:
			exponent = math.MaxInt32 - int32(rng.IntN(30))
		case 1:
			exponent = math.MinInt32 + int32(rng.IntN(30))
		}
		return inlineDecimal(w, exponent, rng.IntN(2) == 0)
	}
	var rounded, carried, refused, trapped, cancelled int
	for range 300000 {
		x, y := operand(), operand()
		if rng.IntN(8) == 0 {
			// Near cancellation across an exponent gap of g: x·10^g lies
			// just above 2^128 and y just below it, so the aligned operand
			// leaves 128 bits and the exact difference is short.
			g := 1 + rng.IntN(12)
			quotient, _ := new(big.Int).SetString("340282366920938463463374607431768211456", 10) // 2^128
			quotient.Quo(quotient, pow10Big(int64(g))).Add(quotient, big.NewInt(1+int64(rng.IntN(3))))
			exponent := int32(rng.IntN(41) - 20)
			x = inlineDecimal(uint128{quotient.Uint64(), new(big.Int).Rsh(quotient, 64).Uint64()}, exponent, rng.IntN(2) == 0)
			y = inlineDecimal(uint128{^uint64(0) - rng.Uint64N(1<<uint(rng.IntN(40))), ^uint64(0)}, exponent-int32(g), !x.negative())
			cancelled++
		}
		var guards *ExponentGuards
		if rng.IntN(3) == 0 {
			guards = &ExponentGuards{Emin: int32(-rng.IntN(30)), Emax: int32(rng.IntN(40))}
		}
		traps := Conditions(0)
		if rng.IntN(4) == 0 {
			traps = []Conditions{Inexact, Rounded, Inexact | Rounded, Overflow | Underflow | Subnormal}[rng.IntN(4)]
		}
		ctx, err := NewContext(uint32(1+rng.IntN(38)), RoundingMode(rng.IntN(int(Exact)+1)), guards, traps)
		if err != nil {
			t.Fatal(err)
		}
		slow := ctx.WithBudget(general)
		for name, op := range map[string]func(Context) (Decimal, Conditions, error){
			"Add":   func(c Context) (Decimal, Conditions, error) { return x.AddWithContext(y, c) },
			"Sub":   func(c Context) (Decimal, Conditions, error) { return x.SubWithContext(y, c) },
			"Mul":   func(c Context) (Decimal, Conditions, error) { return x.MulWithContext(y, c) },
			"Round": func(c Context) (Decimal, Conditions, error) { return x.RoundToPrecisionWithContext(c) },
		} {
			got, gc, gerr := op(ctx)
			want, wc, werr := op(slow)
			if (gerr == nil) != (werr == nil) || gerr != nil && gerr.Error() != werr.Error() || gc != wc || !sameRepresentation(got, want) {
				t.Fatalf("%s(%v, %v) at precision %d, %v, guards %v, traps %v: %v %v %v; general %v %v %v",
					name, x, y, ctx.Precision(), ctx.Rounding(), guards, traps, got, gc, gerr, want, wc, werr)
			}
			switch {
			case gerr != nil && gc == 0 && errors.Is(gerr, ErrInexact) && traps == 0:
				refused++
			case gerr != nil:
				trapped++
			case gc&Rounded != 0:
				rounded++
				if got.coefficientDigits() == "1"+strings.Repeat("0", int(ctx.Precision())-1) && gc&Increased != 0 == !got.negative() {
					carried++
				}
			}
		}
	}
	if rounded < 200000 || carried < 500 || refused < 20000 || trapped < 20000 || cancelled < 5000 {
		t.Fatalf("vacuous path coverage: %d rounded, %d carried, %d refused, %d trapped, %d near cancellations", rounded, carried, refused, trapped, cancelled)
	}
}

// TestContextProductMatchesStream pins the stack product of MulWithContext
// to the streamed product: operands from one digit to beyond the stack
// bound, every precision class, every mode, guards, traps and budgets on
// both sides of each refusal, with the conditions and the error text.
func TestContextProductMatchesStream(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x70726f64, 5))
	var product, streamed, refused, flagged int
	for i := range 40000 {
		limit := []int{40, 100, 500, 1200}[i%4]
		x := fmaOperand(rng, 1+rng.IntN(limit), -60, 60)
		y := fmaOperand(rng, 1+rng.IntN(limit), -60, 60)
		var guards *ExponentGuards
		if rng.IntN(3) == 0 {
			guards = &ExponentGuards{Emin: int32(-rng.IntN(200)), Emax: int32(rng.IntN(300))}
		}
		traps := Conditions(0)
		if rng.IntN(5) == 0 {
			traps = []Conditions{Inexact, Rounded, Overflow | Underflow | Subnormal}[rng.IntN(3)]
		}
		precision := uint32(1 + rng.IntN(60))
		if rng.IntN(4) == 0 {
			precision = uint32(1 + rng.IntN(1300))
		}
		ctx, err := NewContext(precision, RoundingMode(rng.IntN(int(Exact)+1)), guards, traps)
		if err != nil {
			t.Fatal(err)
		}
		budget := limits{}
		if rng.IntN(3) == 0 {
			budget = limits{MaxDigits: uint64(rng.IntN(80)), MaxWork: uint64(rng.IntN(4000))}
		}
		got, gc, gerr := x.contextMul(y, ctx, budget, "MulWithContext")
		want, wc, werr := x.contextMulPath(y, ctx, budget, "MulWithContext", true)
		if (gerr == nil) != (werr == nil) || gerr != nil && gerr.Error() != werr.Error() || gc != wc || !sameRepresentation(got, want) {
			t.Fatalf("%v × %v at precision %d, %v, guards %v, traps %v, budget %+v: %v %v %v; streamed %v %v %v",
				x, y, precision, ctx.Rounding(), guards, traps, budget, got, gc, gerr, want, wc, werr)
		}
		xv, yv := coefficientViewOf(x), coefficientViewOf(y)
		switch {
		case xv.count+yv.count > contextProductLimbs:
			streamed++
		case xv.count > 0 && yv.count > 0:
			product++
		}
		if gerr != nil {
			refused++
		} else if gc&(Overflow|Underflow|Subnormal) != 0 {
			flagged++
		}
	}
	if product < 20000 || streamed < 500 || refused < 5000 || flagged < 1000 {
		t.Fatalf("vacuous path coverage: %d stack products, %d streamed, %d refused, %d overflowed or underflowed", product, streamed, refused, flagged)
	}
}
