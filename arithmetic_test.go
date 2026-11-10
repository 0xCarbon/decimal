// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"math"
	"math/big"
	"math/rand"
	randv2 "math/rand/v2"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
)

var arithmeticResultSink Decimal

// TestMulOneWordBoundaries covers the exact one-word product with an
// independent math/big oracle, nonvacuous high-word carries, zero cohorts,
// exponent validation before zero, and adjacent positive-budget tariffs.
func TestMulOneWordBoundaries(t *testing.T) {
	texts := []string{"0", "1", "2", "9", "10", "9999999999", "1000000000000000000", "18446744073709551614", "18446744073709551615", "18446744073709551616", "340282366920938463463374607431768211455"}
	var oneWord, highCarry, wideFit, deferred, zero int
	for _, left := range texts {
		for _, right := range texts {
			for _, negativeA := range []bool{false, true} {
				for _, negativeB := range []bool{false, true} {
					aText, bText := left+"E-2", right+"E+1"
					if negativeA {
						aText = "-" + aText
					}
					if negativeB {
						bText = "-" + bText
					}
					a, b := MustParse(aText), MustParse(bText)
					ai, _ := new(big.Int).SetString(left, 10)
					bi, _ := new(big.Int).SetString(right, 10)
					want := new(big.Int).Mul(ai, bi)
					got, err := a.Mul(b)
					general, _, generalErr := a.MulWithContext(b, Context{}.WithBudget(Budget{MaxWork: math.MaxUint64, MaxDigits: math.MaxUint64}))
					if err != nil || generalErr != nil || !got.validRepresentation() || !sameRepresentation(got, general) || got.coefficientDigits() != want.String() || got.exponent() != -1 || got.negative() != (want.Sign() != 0 && negativeA != negativeB) {
						t.Fatalf("%s * %s = %s e%d sign%v %v; big.Int %s; general %s %v", aText, bText, got.coefficientDigits(), got.exponent(), got.negative(), err, want, general, generalErr)
					}
					fast, ok := inlineMul(a, b)
					if ok != (want.BitLen() <= 128) || ok && !sameRepresentation(fast, got) {
						t.Fatal("inline product eligibility or representation changed")
					}
					if want.Sign() == 0 {
						zero++
					} else if a.words.hi == 0 && b.words.hi == 0 {
						oneWord++
						if want.BitLen() > 64 {
							highCarry++
						}
					} else if ok {
						wideFit++
					} else {
						deferred++
					}
				}
			}
		}
	}
	if oneWord != 256 || highCarry < 50 || wideFit < 20 || deferred < 20 || zero != 84 {
		t.Fatalf("vacuous product classes: word%d carry%d wide%d defer%d zero%d", oneWord, highCarry, wideFit, deferred, zero)
	}
	for _, edge := range []int32{math.MinInt32, math.MaxInt32} {
		step := int32(1)
		if edge < 0 {
			step = -1
		}
		for _, zeroFirst := range []bool{false, true} {
			for _, over := range []bool{false, true} {
				a, b := New(0, edge), New(-1, 0)
				if over {
					b = New(-1, step)
				}
				if !zeroFirst {
					a, b = b, a
				}
				got, err := a.Mul(b)
				if over {
					var op *Error
					if !sameRepresentation(got, Decimal{}) || !errors.Is(err, ErrExponentRange) || !errors.As(err, &op) || op.Op != "Mul" || op.Condition != 0 {
						t.Fatalf("zero bypassed exponent validation: %s %v", got, err)
					}
				} else if err != nil || !got.isZero() || got.exponent() != edge || got.negative() || !got.validRepresentation() {
					t.Fatal("edge zero product changed cohort or sign")
				}
			}
		}
	}
	for _, pair := range [][2]string{{"12", "34"}, {"18446744073709551615", "18446744073709551615"}} {
		a, b := MustParse(pair[0]), MustParse(pair[1])
		digits := uint64(len(pair[0]) + len(pair[1]))
		work := (1+(uint64(len(pair[0]))-1)/9)*(1+(uint64(len(pair[1]))-1)/9) + digits
		for _, budget := range []Budget{{MaxDigits: digits - 1}, {MaxWork: work - 1}, {MaxDigits: digits, MaxWork: work}, {MaxDigits: digits}, {MaxWork: work}} {
			got, _, err := a.MulWithContext(b, Context{}.WithBudget(budget))
			if budget.MaxDigits == digits || budget.MaxWork == work {
				want, _ := a.Mul(b)
				if err != nil || !sameRepresentation(got, want) {
					t.Fatal("adjacent Mul tariff did not admit")
				}
			} else {
				var op *Error
				if !sameRepresentation(got, Decimal{}) || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &op) || op.Op != "MulWithContext" || op.Condition != InsufficientStorage {
					t.Fatal("positive Mul budget bypassed general admission")
				}
			}
		}
		got, err := a.Mul(b)
		if err != nil {
			t.Fatal(err)
		}
		allocs := testing.AllocsPerRun(100, func() {
			var callErr error
			arithmeticResultSink, callErr = a.Mul(b)
			if callErr != nil {
				panic(callErr)
			}
		})
		if allocs != 0 || !sameRepresentation(arithmeticResultSink, got) {
			t.Fatalf("one-word Mul used %v allocations or changed retained product", allocs)
		}
	}
	t.Logf("product classes: word%d carry%d wide%d defer%d zero%d", oneWord, highCarry, wideFit, deferred, zero)
}

func TestArithmeticPublicSignatureShapes(t *testing.T) {
	var add func(Decimal, Decimal) (Decimal, error) = Decimal.Add
	var sub func(Decimal, Decimal) (Decimal, error) = Decimal.Sub
	var mul func(Decimal, Decimal) (Decimal, error) = Decimal.Mul
	var addBudget func(Decimal, Decimal, Budget) (Decimal, error) = addWithBudget
	var subBudget func(Decimal, Decimal, Budget) (Decimal, error) = subWithBudget
	var mulBudget func(Decimal, Decimal, Budget) (Decimal, error) = mulWithBudget
	if add == nil || sub == nil || mul == nil || addBudget == nil || subBudget == nil || mulBudget == nil {
		t.Fatal("a required arithmetic method signature is absent")
	}
}

func TestOperationErrorZeroValueTotal(t *testing.T) {
	var zero Error
	if got := zero.Error(); got != "decimal: error" {
		t.Fatalf("zero-value Error() = %q", got)
	}
	if zero.Unwrap() != nil {
		t.Fatal("zero-value Unwrap() is not nil")
	}
	var nilError *Error
	if got := nilError.Error(); got != "decimal: error" || nilError.Unwrap() != nil {
		t.Fatalf("nil receiver Error()/Unwrap() = %q/%v", got, nilError.Unwrap())
	}
}

func TestArithmeticBareZeroBudgetParity(t *testing.T) {
	a, b := MustParse("12.30"), MustParse("-2.5")
	for _, tc := range []struct {
		name    string
		bare    func(Decimal, Decimal) (Decimal, error)
		bounded func(Decimal, Decimal, Budget) (Decimal, error)
	}{
		{"add", Decimal.Add, addWithBudget},
		{"sub", Decimal.Sub, subWithBudget},
		{"mul", Decimal.Mul, mulWithBudget},
	} {
		t.Run(tc.name, func(t *testing.T) {
			plain, plainErr := tc.bare(a, b)
			budgeted, budgetErr := tc.bounded(a, b, Budget{})
			if plainErr != nil || budgetErr != nil || plain.coefficientDigits() != budgeted.coefficientDigits() || plain.exponent() != budgeted.exponent() || plain.negative() != budgeted.negative() {
				t.Fatalf("bare = %s e%d neg %v, %v; zero budget = %s e%d neg %v, %v", plain.coefficientDigits(), plain.exponent(), plain.negative(), plainErr, budgeted.coefficientDigits(), budgeted.exponent(), budgeted.negative(), budgetErr)
			}
		})
	}
}

// TestArithmeticInlineDispatchPreservesBudget checks that, under either
// positive quota axis, inline dispatch retains the exact tariff, refusal
// identity and preferred cohort, including slow carriers whose inline words
// cannot supply the value.
func TestArithmeticInlineDispatchPreservesBudget(t *testing.T) {
	var refusals, admitted, slow int
	for _, literals := range [][2]string{
		{"0E+3", "0E-2"}, {"0E+19", "-12E-2"}, {"12E+1", "0"},
		{"1", "1"}, {"9", "1"}, {"7", "-2"}, {"123E-2", "123E-2"},
		{"1E+19", "1"}, {"18446744073709551615E+1", "1"},
		{"340282366920938463463374607431768211455", "1"},
		{strings.Repeat("9", 40), "1"}, {"1", "-" + strings.Repeat("9", 40)},
		{strings.Repeat("9", 40), "-" + strings.Repeat("9", 40)},
		{strings.Repeat("9", 40) + "E+1", "0"}, {"0", "-" + strings.Repeat("9", 40)},
	} {
		a, b := MustParse(literals[0]), MustParse(literals[1])
		parts := func(literal string) (*big.Int, int32) {
			text, exponentText, hasExponent := strings.Cut(literal, "E")
			n, ok := new(big.Int).SetString(text, 10)
			if !ok {
				t.Fatalf("invalid oracle fixture %q", literal)
			}
			var exponent int64
			if hasExponent {
				var err error
				exponent, err = strconv.ParseInt(exponentText, 10, 32)
				if err != nil {
					t.Fatalf("invalid oracle exponent %q: %v", literal, err)
				}
			}
			return n, int32(exponent)
		}
		ai, ae := parts(literals[0])
		bi, be := parts(literals[1])
		for _, operation := range []struct {
			name string
			call func(Decimal, Decimal, Budget) (Decimal, error)
		}{
			{"AddWithContext", addWithBudget}, {"SubWithContext", subWithBudget},
		} {
			op := "add"
			if operation.name == "SubWithContext" {
				op = "sub"
			}
			want, exponent := oracleParts(ai, ae, bi, be, op)
			alignedWidth := func(n *big.Int, e int32) uint64 {
				if n.Sign() == 0 {
					return 0
				}
				return uint64(len(new(big.Int).Abs(n).String())) + uint64(int64(e)-int64(exponent))
			}
			length := max(alignedWidth(ai, ae), alignedWidth(bi, be))
			da, db := uint64(len(new(big.Int).Abs(ai).String())), uint64(len(new(big.Int).Abs(bi).String()))
			digits, work := uint64(1), uint64(1)
			switch {
			case ai.Sign() == 0 && bi.Sign() == 0:
			case ai.Sign() == 0 || bi.Sign() == 0:
				digits, work = length, length
			case (ai.Sign() < 0) == ((bi.Sign() < 0) != (op == "sub")):
				digits = uint64(len(new(big.Int).Abs(want).String()))
				work = da + db + length + 1
			case want.Sign() == 0:
				work = da + db
			default:
				digits, work = length, 2*(da+db)+length
			}
			quotas := []Budget{{}, {MaxDigits: digits}, {MaxWork: work}, {MaxDigits: digits, MaxWork: work}, {MaxDigits: digits + 1, MaxWork: work + 1}}
			if digits > 1 {
				quotas = append(quotas, Budget{MaxDigits: digits - 1})
			}
			if work > 1 {
				quotas = append(quotas, Budget{MaxWork: work - 1})
			}
			carriers := [][2]Decimal{{a, b}}
			for _, pair := range carriers {
				for _, budget := range quotas {
					got, err := operation.call(pair[0], pair[1], budget)
					refuse := budget.MaxDigits > 0 && budget.MaxDigits < digits || budget.MaxWork > 0 && budget.MaxWork < work
					if refuse {
						var operationError *Error
						if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operationError) || operationError.Op != operation.name || operationError.Condition != InsufficientStorage || !sameRepresentation(got, Decimal{}) {
							t.Fatalf("%s(%v, budget=%+v): refusal %#v, %v", operation.name, literals, budget, got, err)
						}
						refusals++
						continue
					}
					if err != nil || !got.validRepresentation() {
						t.Fatalf("%s(%v, budget=%+v): %#v, %v", operation.name, literals, budget, got, err)
					}
					assertOracleParts(t, got, want, exponent)
					admitted++
					if pair[0].slow != nil || pair[1].slow != nil {
						slow++
					}
				}
			}
		}
	}
	if refusals < 35 || admitted < 100 || slow < 50 {
		t.Fatalf("vacuous dispatch classes: refused=%d admitted=%d slow=%d", refusals, admitted, slow)
	}
	t.Logf("actual dispatch outcomes: refused=%d admitted=%d slow=%d", refusals, admitted, slow)
}

func TestArithmeticCancellationPrecharge(t *testing.T) {
	x := MustParse(strings.Repeat("9", 10_000) + "E-5000")
	got, _, err := x.SubWithContext(x, Context{}.WithBudget(Budget{MaxWork: 1}))
	var oe *Error
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &oe) || oe.Op != "SubWithContext" || oe.Condition != InsufficientStorage || !got.isZero() || got.exponent() != 0 {
		t.Fatalf("precharge refusal: %+v, %v", got, err)
	}
}

func TestArithmeticSubMulResourceIdentity(t *testing.T) {
	for _, tc := range []struct {
		name, op string
		call     func() (Decimal, error)
	}{
		{"sub", "SubWithContext", func() (Decimal, error) {
			res, _, resErr := New(12, 0).SubWithContext(Zero(), Context{}.WithBudget(Budget{MaxDigits: 1}))
			return res, resErr
		}},
		{"mul", "MulWithContext", func() (Decimal, error) {
			res, _, resErr := New(12, 0).MulWithContext(New(34, 0), Context{}.WithBudget(Budget{MaxDigits: 3}))
			return res, resErr
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := tc.call()
			var oe *Error
			if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &oe) || oe.Op != tc.op || oe.Condition != InsufficientStorage || !got.isZero() || got.exponent() != 0 || got.negative() {
				t.Fatalf("got %+v, %v", got, err)
			}
		})
	}
}

func TestArithmeticExactPreferredCohorts(t *testing.T) {
	tests := []struct {
		name        string
		left, right string
		call        func(Decimal, Decimal) (Decimal, error)
		want        string
	}{
		{"add keeps scale", "1.10", "0", Decimal.Add, "1.10"},
		{"subtract keeps scale", "1.10", "0", Decimal.Sub, "1.10"},
		{"multiply sums exponents", "1.10", "2.5", Decimal.Mul, "2.750"},
		{"cancellation keeps minimum exponent", "1.20", "1.2", Decimal.Sub, "0.00"},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			a, b := MustParse(tc.left), MustParse(tc.right)
			got, err := tc.call(a, b)
			if err != nil {
				t.Fatalf("operation error: %v", err)
			}
			text, err := got.Text(0)
			if err != nil || text != tc.want {
				t.Fatalf("got %q, %v; want %q", text, err, tc.want)
			}
		})
	}
}

func TestArithmeticBudgetPaths(t *testing.T) {
	tests := []struct {
		name      string
		call      func(Budget) (Decimal, error)
		bad, good Budget
		want      string
	}{
		{"both zero work", func(b Budget) (Decimal, error) {
			res, _, resErr := New(0, 3).AddWithContext(New(0, -2), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxWork: 0}, Budget{MaxWork: 1}, "0.00"},
		{"one zero work", func(b Budget) (Decimal, error) {
			res, _, resErr := New(12, 1).AddWithContext(Zero(), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxWork: 2}, Budget{MaxWork: 3}, "120"},
		{"one zero digits", func(b Budget) (Decimal, error) {
			res, _, resErr := New(12, 1).SubWithContext(Zero(), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxDigits: 2}, Budget{MaxDigits: 3}, "120"},
		{"same sign work", func(b Budget) (Decimal, error) {
			res, _, resErr := One().AddWithContext(One(), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxWork: 3}, Budget{MaxWork: 4}, "2"},
		{"same sign actual carry", func(b Budget) (Decimal, error) {
			res, _, resErr := New(9, 0).AddWithContext(One(), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxDigits: 1}, Budget{MaxDigits: 2}, "10"},
		{"opposite sign work", func(b Budget) (Decimal, error) {
			res, _, resErr := New(7, 0).AddWithContext(New(-2, 0), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxWork: 4}, Budget{MaxWork: 5}, "5"},
		{"cancellation comparison", func(b Budget) (Decimal, error) {
			res, _, resErr := New(2, -2).AddWithContext(New(-2, -2), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxWork: 1}, Budget{MaxWork: 2}, "0.00"},
		{"multiply work", func(b Budget) (Decimal, error) {
			res, _, resErr := New(12, 0).MulWithContext(New(34, 0), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxWork: 4}, Budget{MaxWork: 5}, "408"},
		{"multiply digit envelope", func(b Budget) (Decimal, error) {
			res, _, resErr := New(12, 0).MulWithContext(New(34, 0), Context{}.WithBudget(b))
			return res, resErr
		}, Budget{MaxDigits: 3}, Budget{MaxDigits: 4}, "408"},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			if tc.bad != (Budget{}) {
				got, err := tc.call(tc.bad)
				if !errors.Is(err, ErrInsufficientStorage) || !got.isZero() || got.exponent() != 0 {
					t.Fatalf("bad limit: got %+v, %v", got, err)
				}
			}
			got, err := tc.call(tc.good)
			if err != nil {
				t.Fatalf("good limit: %v", err)
			}
			text, err := got.Text(0)
			if err != nil || text != tc.want {
				t.Fatalf("good limit: got %q, %v; want %q", text, err, tc.want)
			}
		})
	}
	if _, _, err := One().AddWithContext(Zero(), Context{}.WithBudget(Budget{MaxDigits: 1})); err != nil {
		t.Fatalf("1+0 with one digit: %v", err)
	}
	if _, _, err := One().SubWithContext(Zero(), Context{}.WithBudget(Budget{MaxDigits: 1})); err != nil {
		t.Fatalf("1-0 with one digit: %v", err)
	}
	if _, _, err := New(2, 0).AddWithContext(New(-1, 0), Context{}.WithBudget(Budget{MaxDigits: 1})); err != nil {
		t.Fatalf("no-carry magnitude subtraction with one digit: %v", err)
	}
}

func TestArithmeticRangeIdentityAndZero(t *testing.T) {
	for _, tc := range []struct {
		name string
		a, b Decimal
	}{
		{"positive", New(1, math.MaxInt32), New(1, 1)},
		{"negative", New(1, math.MinInt32), New(1, -1)},
		{"zero still checked", New(0, math.MaxInt32), New(1, 1)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, _, err := tc.a.MulWithContext(tc.b, Context{}.WithBudget(Budget{MaxDigits: 1, MaxWork: 1}))
			var oe *Error
			if !errors.Is(err, ErrExponentRange) || !errors.As(err, &oe) || oe.Condition != 0 || oe.Op != "MulWithContext" || !got.isZero() || got.exponent() != 0 || got.negative() {
				t.Fatalf("got %+v, %v", got, err)
			}
		})
	}
	zero, err := New(0, 2).Mul(New(-3, -3))
	if err != nil || !zero.isZero() || zero.exponent() != -1 || zero.negative() {
		t.Fatalf("zero product: %+v, %v", zero, err)
	}
	zero, err = New(0, 5).Sub(New(0, -2))
	if err != nil || !zero.isZero() || zero.exponent() != -2 || zero.negative() {
		t.Fatalf("zero difference: %+v, %v", zero, err)
	}
	_, _, err = New(1, math.MaxInt32).AddWithContext(New(1, math.MinInt32), Context{}.WithBudget(Budget{MaxDigits: 100}))
	if !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("extreme alignment budget: %v", err)
	}
	result, _, err := New(9, 0).AddWithContext(One(), Context{}.WithBudget(Budget{MaxDigits: 1}))
	var resource *Error
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &resource) || resource.Op != "AddWithContext" || resource.Condition != InsufficientStorage || !result.isZero() || result.exponent() != 0 || result.negative() {
		t.Fatalf("resource identity/result: %+v, %v", result, err)
	}
	_, err = New(1, math.MaxInt32).Mul(New(1, 1))
	var bare *Error
	if !errors.As(err, &bare) || bare.Op != "Mul" {
		t.Fatalf("bare method name: %v", err)
	}
	valid, err := New(1, math.MaxInt32).Mul(One())
	if err != nil || valid.exponent() != math.MaxInt32 {
		t.Fatalf("in-domain maximum exponent: %+v, %v", valid, err)
	}
}

func TestArithmeticLogicalResultQuotaOnReuse(t *testing.T) {
	x := MustParse(strings.Repeat("7", 1000))
	if _, _, err := x.AddWithContext(Zero(), Context{}.WithBudget(Budget{MaxDigits: 999})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("999-digit cap on reusable x: %v", err)
	}
	got, _, err := x.AddWithContext(Zero(), Context{}.WithBudget(Budget{MaxDigits: 1000, MaxWork: 1000}))
	if err != nil || !got.Equal(x) || got.slow != x.slow {
		t.Fatalf("1000-digit cap on reusable x: %+v, %v", got, err)
	}
}

func TestArithmeticPhysicalAddressabilityPreflight(t *testing.T) {
	// On 386 this is a synthetic plan just beyond the maximum addressable
	// uint32 slice byte count; no allocation is attempted. On 64-bit the
	// corresponding digit count exceeds uint64 and cannot be represented.
	maxLimbs := uint64(math.MaxInt) / 4
	assertResource := func(op string, err error) {
		t.Helper()
		var oe *Error
		if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &oe) || oe.Op != op || oe.Condition != InsufficientStorage {
			t.Fatalf("%s physical preflight identity: %v", op, err)
		}
	}
	if maxLimbs <= math.MaxUint64/9 {
		digits := maxLimbs*9 + 1
		for _, op := range []string{"AddWithContext", "SubWithContext"} {
			_, err := arithmeticLimbCount(digits, op)
			assertResource(op, err)
		}
	}
	_, err := arithmeticPhysicalLimbCount(maxLimbs+1, "MulWithContext")
	assertResource("MulWithContext", err)
	if _, err := arithmeticPhysicalLimbCount(maxLimbs, "MulWithContext"); err != nil {
		t.Fatalf("last addressable limb count refused: %v", err)
	}
	if _, ok := arithmeticAdd(math.MaxUint64, 1); ok {
		t.Fatal("digit span addition wrapped")
	}
	if _, ok := arithmeticMul(math.MaxUint64, 2); ok {
		t.Fatal("work product wrapped")
	}
}

func TestArithmeticSharedSlowOperandsConcurrent(t *testing.T) {
	a := MustParse(strings.Repeat("9", 80) + "E-40")
	b := MustParse(strings.Repeat("1234567890", 6) + "E-20")
	if a.slow == nil || b.slow == nil {
		t.Fatal("shared-operand test requires two slow coefficients")
	}
	aLimbs := slices.Clone(a.slow.limbs)
	bLimbs := slices.Clone(b.slow.limbs)
	aBefore, bBefore := a.coefficientDigits(), b.coefficientDigits()
	ai, _ := new(big.Int).SetString(aBefore, 10)
	bi, _ := new(big.Int).SetString(bBefore, 10)
	type operation struct {
		name        string
		call        func(Decimal, Decimal) (Decimal, error)
		coefficient string
		exponent    int32
	}
	ops := make([]operation, 0, 3)
	for _, tc := range []struct {
		name string
		call func(Decimal, Decimal) (Decimal, error)
	}{
		{"add", Decimal.Add}, {"sub", Decimal.Sub}, {"mul", Decimal.Mul},
	} {
		want, exponent := oracleParts(ai, a.exponent(), bi, b.exponent(), tc.name)
		ops = append(ops, operation{tc.name, tc.call, new(big.Int).Abs(want).String(), exponent})
	}
	var wg sync.WaitGroup
	for range 12 {
		wg.Go(func() {
			for range 50 {
				for _, op := range ops {
					got, err := op.call(a, b)
					if err != nil || got.coefficientDigits() != op.coefficient || got.exponent() != op.exponent || got.negative() {
						t.Errorf("shared %s: got %s e%d negative %v, %v; want %s e%d", op.name, got.coefficientDigits(), got.exponent(), got.negative(), err, op.coefficient, op.exponent)
						return
					}
				}
			}
		})
	}
	wg.Wait()
	if !slices.Equal(a.slow.limbs, aLimbs) || !slices.Equal(b.slow.limbs, bLimbs) || a.coefficientDigits() != aBefore || b.coefficientDigits() != bBefore {
		t.Fatal("published slow operand changed")
	}
}

func TestArithmeticInlineAllocation(t *testing.T) {
	wide := MustParse(strings.Repeat("9", 37))
	for _, tc := range []struct {
		name string
		call func() (Decimal, error)
	}{
		{"add same scale", func() (Decimal, error) { return New(12345, -2).Add(New(6789, -2)) }},
		{"add mixed scale", func() (Decimal, error) { return New(12345, -2).Add(New(6789, -3)) }},
		{"subtract", func() (Decimal, error) { return New(12345, -2).Sub(New(6789, -2)) }},
		{"multiply", func() (Decimal, error) { return New(12345, -2).Mul(New(6789, -2)) }},
		{"multiply six stack limbs", func() (Decimal, error) { return New(9, 0).Mul(wide) }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			allocs := testing.AllocsPerRun(1000, func() {
				got, err := tc.call()
				if err != nil {
					panic(err)
				}
				arithmeticResultSink = got
			})
			t.Logf("inline allocation probe: %.0f allocs/op", allocs)
			if allocs != 0 {
				t.Fatalf("inline result allocated: %.0f allocs/op", allocs)
			}
		})
	}
}

func TestArithmeticSameSignExactDigitBudget(t *testing.T) {
	wide := strings.Repeat("9", 1000)
	for _, tc := range []struct {
		name, left, right string
		call              func(Decimal, Decimal, Budget) (Decimal, error)
		cap               uint64
		want              string
		refuse            bool
	}{
		{"one plus one", "1", "1", addWithBudget, 1, "2", false},
		{"sub reverses sign", "1", "-1", subWithBudget, 1, "2", false},
		{"carry refused", "9", "1", addWithBudget, 1, "", true},
		{"carry admitted", "9", "1", addWithBudget, 2, "10", false},
		{"all nines no carry", "888888888", "111111111", addWithBudget, 9, "999999999", false},
		{"full width no carry", strings.Repeat("8", 1000), strings.Repeat("1", 1000), addWithBudget, 1000, wide, false},
		{"full width carry refused", wide, "1", addWithBudget, 1000, "", true},
		{"full width carry admitted", wide, "1", addWithBudget, 1001, "1" + strings.Repeat("0", 1000), false},
		{"aligned gap no carry", "1E+18", "1", addWithBudget, 19, "1000000000000000001", false},
		{"preferred cohort", "1.0", "1.0", addWithBudget, 2, "2.0", false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := tc.call(MustParse(tc.left), MustParse(tc.right), Budget{MaxDigits: tc.cap})
			if tc.refuse {
				var oe *Error
				if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &oe) || oe.Condition != InsufficientStorage || !got.isZero() || got.exponent() != 0 {
					t.Fatalf("refusal = %+v, %v", got, err)
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			text, err := got.Text(0)
			if err != nil || text != tc.want {
				t.Fatalf("result = %q, %v; want %q", text, err, tc.want)
			}
		})
	}

	for _, work := range []struct {
		limit  uint64
		refuse bool
	}{{3, true}, {4, false}} {
		got, _, err := One().AddWithContext(One(), Context{}.WithBudget(Budget{MaxDigits: 1, MaxWork: work.limit}))
		if work.refuse {
			if !errors.Is(err, ErrInsufficientStorage) || !got.isZero() {
				t.Fatalf("work %d should refuse: %+v, %v", work.limit, got, err)
			}
		} else if err != nil || got.coefficientDigits() != "2" {
			t.Fatalf("work %d should admit: %+v, %v", work.limit, got, err)
		}
	}
}

func TestArithmeticSameSignDigitBudgetBigIntOracle(t *testing.T) {
	rng := rand.New(rand.NewSource(20260923017))
	for i := range 360 {
		coefficient := func() string {
			n := 1 + rng.Intn(90)
			var text strings.Builder
			text.WriteByte(byte('1' + rng.Intn(9)))
			for range n - 1 {
				text.WriteByte(byte('0' + rng.Intn(10)))
			}
			return text.String()
		}
		ac, bc := coefficient(), coefficient()
		ae, be := int32(rng.Intn(41)-20), int32(rng.Intn(41)-20)
		subtract := i%2 != 0
		negativeA := i%3 == 0
		negativeB := negativeA != subtract // effective signs must match
		input := func(coeff string, exponent int32, negative bool) Decimal {
			literal := coeff + "E" + strconv.FormatInt(int64(exponent), 10)
			if negative {
				literal = "-" + literal
			}
			return MustParse(literal)
		}
		a, b := input(ac, ae, negativeA), input(bc, be, negativeB)
		ai, _ := new(big.Int).SetString(ac, 10)
		bi, _ := new(big.Int).SetString(bc, 10)
		if negativeA {
			ai.Neg(ai)
		}
		if negativeB {
			bi.Neg(bi)
		}
		op := "add"
		call := addWithBudget
		if subtract {
			op, call = "sub", subWithBudget
		}
		want, exponent := oracleParts(ai, ae, bi, be, op)
		shiftA, shiftB := uint64(int64(ae)-int64(exponent)), uint64(int64(be)-int64(exponent))
		L := max(uint64(len(ac))+shiftA, uint64(len(bc))+shiftB)
		actualDigits := uint64(len(new(big.Int).Abs(want).String()))
		if actualDigits != L && actualDigits != L+1 {
			t.Fatalf("case %d: oracle has %d digits outside L=%d envelope", i, actualDigits, L)
		}
		got, err := call(a, b, Budget{MaxDigits: L})
		if actualDigits == L+1 {
			var oe *Error
			if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &oe) || oe.Condition != InsufficientStorage || !got.isZero() || got.exponent() != 0 {
				t.Fatalf("case %d: expected carry refusal, got %+v, %v", i, got, err)
			}
		} else {
			if err != nil {
				t.Fatalf("case %d: false refusal: %v", i, err)
			}
			assertOracleParts(t, got, want, exponent)
		}
	}
}

func carryBig(t *testing.T, digits string) *big.Int {
	t.Helper()
	n, ok := new(big.Int).SetString(digits, 10)
	if !ok {
		t.Fatalf("invalid oracle integer %q", digits)
	}
	return n
}

func assertCarryRefusal(t testing.TB, got Decimal, err error, op string) {
	t.Helper()
	var operation *Error
	if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != op || operation.Condition != InsufficientStorage || got.slow != nil || got.words != (uint128{}) || got.exponent() != 0 || got.negative() {
		t.Fatalf("%s refusal = coefficient %s exponent %d negative %v, error %v", op, got.coefficientDigits(), got.exponent(), got.negative(), err)
	}
}

func TestArithmeticTightCarrySharedSlowOwnership(t *testing.T) {
	for _, tc := range []struct {
		name, digits, operation string
		carry                   bool
	}{
		{"add_no_carry", strings.Repeat("4", 80), "add", false},
		{"sub_no_carry", strings.Repeat("4", 80), "sub", false},
		{"add_carry", strings.Repeat("9", 80), "add", true},
		{"sub_carry", strings.Repeat("9", 80), "sub", true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			left := MustParse(tc.digits + "E-7")
			right := left // deliberately share the same slow holder
			if tc.operation == "sub" {
				right = right.withNegative(true) // effective signs still match
			}
			if left.slow == nil || right.slow != left.slow {
				t.Fatal("test did not construct a shared slow holder")
			}
			before := slices.Clone(left.slow.limbs)
			var got Decimal
			var err error
			if tc.operation == "add" {
				got, _, err = left.AddWithContext(right, Context{}.WithBudget(Budget{MaxDigits: 80}))
			} else {
				got, _, err = left.SubWithContext(right, Context{}.WithBudget(Budget{MaxDigits: 80}))
			}
			if tc.carry {
				assertCarryRefusal(t, got, err, map[string]string{"add": "AddWithContext", "sub": "SubWithContext"}[tc.operation])
			} else {
				if err != nil {
					t.Fatal(err)
				}
				a, b := carryBig(t, tc.digits), carryBig(t, tc.digits)
				if tc.operation == "sub" {
					b.Neg(b)
				}
				want, exponent := oracleParts(a, -7, b, -7, tc.operation)
				assertOracleParts(t, got, want, exponent)
				if got.slow == nil || got.slow == left.slow {
					t.Fatal("successful result must own an independent slow holder")
				}
				got.slow.limbs[0] ^= 1 // test-only alias challenge
			}
			if !slices.Equal(left.slow.limbs, before) || !slices.Equal(right.slow.limbs, before) || left.coefficientDigits() != tc.digits || right.coefficientDigits() != tc.digits || left.negative() || right.negative() != (tc.operation == "sub") {
				t.Fatal("shared slow operand changed")
			}
		})
	}
}

func TestArithmeticCarryAdmissionCallLocal(t *testing.T) {
	for round := range 20 {
		for _, tc := range []struct {
			name  string
			left  int64
			carry bool
		}{
			{"no_carry", 1, false},
			{"carry", 9, true},
		} {
			a, b := New(tc.left, 0), One()
			want := new(big.Int).Add(big.NewInt(tc.left), big.NewInt(1))
			for _, cap := range []uint64{0, 2, 1, 2, 0, 1} {
				bare, bareErr := a.Add(b)
				if bareErr != nil {
					t.Fatalf("round %d %s bare: %+v, %v", round, tc.name, bare, bareErr)
				}
				assertOracleParts(t, bare, want, 0)
				got, _, err := a.AddWithContext(b, Context{}.WithBudget(Budget{MaxDigits: cap}))
				if cap == 1 && tc.carry {
					assertCarryRefusal(t, got, err, "AddWithContext")
				} else if err != nil || !got.Equal(bare) {
					t.Fatalf("round %d %s cap %d: %+v, %v", round, tc.name, cap, got, err)
				} else {
					assertOracleParts(t, got, want, 0)
				}
				if unrelated, unrelatedErr := New(7, 0).Mul(New(8, 0)); unrelatedErr != nil || unrelated.coefficientDigits() != "56" {
					t.Fatalf("interleaved operation: %+v, %v", unrelated, unrelatedErr)
				}
			}
		}
	}
}

func TestArithmeticCarryPlanBareUnlimitedLooseTight(t *testing.T) {
	for _, tc := range []struct {
		name, left, right, leftCoefficient, operation string
		carry                                         bool
	}{
		{"add_no_carry", "1.0", "1.0", "10", "add", false},
		{"add_carry", "9.0", "1.0", "90", "add", true},
		{"sub_no_carry", "1.0", "-1.0", "10", "sub", false},
		{"sub_carry", "9.0", "-1.0", "90", "sub", true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			a, b := MustParse(tc.left), MustParse(tc.right)
			ai, bi := carryBig(t, tc.leftCoefficient), carryBig(t, "10")
			if b.negative() {
				bi.Neg(bi)
			}
			want, exponent := oracleParts(ai, a.exponent(), bi, b.exponent(), tc.operation)
			bare := Decimal.Add
			bounded := addWithBudget
			op := "AddWithContext"
			if tc.operation == "sub" {
				bare, bounded, op = Decimal.Sub, subWithBudget, "SubWithContext"
			}
			for _, mode := range []struct {
				name   string
				budget Budget
				plain  bool
			}{
				{"bare", Budget{}, true},
				{"unlimited", Budget{}, false},
				{"loose", Budget{MaxDigits: 3}, false},
				{"tight", Budget{MaxDigits: 2}, false},
			} {
				t.Run(mode.name, func(t *testing.T) {
					var got Decimal
					var err error
					if mode.plain {
						got, err = bare(a, b)
					} else {
						got, err = bounded(a, b, mode.budget)
					}
					if mode.name == "tight" && tc.carry {
						assertCarryRefusal(t, got, err, op)
						return
					}
					if err != nil {
						t.Fatal(err)
					}
					assertOracleParts(t, got, want, exponent)
				})
			}
		})
	}
}

func TestArithmeticCarryRefusalPreallocationAndOwnership(t *testing.T) {
	for _, width := range []int{1, 1000} {
		digits := strings.Repeat("9", width)
		a, b := MustParse(digits), One()
		var before []uint32
		if a.slow != nil {
			before = slices.Clone(a.slow.limbs)
		}
		got, _, err := a.AddWithContext(b, Context{}.WithBudget(Budget{MaxDigits: uint64(width)}))
		assertCarryRefusal(t, got, err, "AddWithContext")
		if a.coefficientDigits() != digits || b.coefficientDigits() != "1" || (a.slow != nil && !slices.Equal(a.slow.limbs, before)) {
			t.Fatal("refusal mutated an operand")
		}
		admitted, _, admitErr := a.AddWithContext(b, Context{}.WithBudget(Budget{MaxDigits: uint64(width + 1)}))
		if admitErr != nil {
			t.Fatal(admitErr)
		}
		want := new(big.Int).Add(carryBig(t, digits), big.NewInt(1))
		assertOracleParts(t, admitted, want, 0)
	}

	wide := MustParse(strings.Repeat("9", 1000))
	baseline := testing.AllocsPerRun(100, func() {
		got, _, err := wide.AddWithContext(One(), Context{}.WithBudget(Budget{MaxDigits: 999}))
		if !errors.Is(err, ErrInsufficientStorage) || !got.isZero() {
			panic("early refusal changed")
		}
	})
	carried := testing.AllocsPerRun(100, func() {
		got, _, err := wide.AddWithContext(One(), Context{}.WithBudget(Budget{MaxDigits: 1000}))
		if !errors.Is(err, ErrInsufficientStorage) || !got.isZero() {
			panic("carry refusal changed")
		}
	})
	if carried != baseline {
		t.Fatalf("carry refusal allocs/run %.0f, early resource refusal %.0f: result coefficient may have been allocated", carried, baseline)
	}
	t.Logf("early refusal %.0f allocs/run; carry refusal %.0f allocs/run", baseline, carried)
}

func TestArithmeticCarryWorkPrecedesScan(t *testing.T) {
	for _, tc := range []struct {
		name   string
		budget Budget
		refuse bool
	}{
		{"small_work_refuse", Budget{MaxDigits: 1, MaxWork: 3}, true},
		{"small_work_admit", Budget{MaxDigits: 1, MaxWork: 4}, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, _, err := One().AddWithContext(One(), Context{}.WithBudget(tc.budget))
			if tc.refuse {
				assertCarryRefusal(t, got, err, "AddWithContext")
			} else if err != nil || got.coefficientDigits() != "2" {
				t.Fatalf("work admission: %+v, %v", got, err)
			}
		})
	}
	left, right := MustParse(strings.Repeat("8", 1000)), MustParse(strings.Repeat("1", 1000))
	for _, tc := range []struct {
		name   string
		budget Budget
		refuse bool
	}{
		{"long_work_refuse", Budget{MaxDigits: 1000, MaxWork: 3000}, true},
		{"below_L_refuse_without_scan", Budget{MaxDigits: 999, MaxWork: 3001}, true},
		{"long_work_admit", Budget{MaxDigits: 1000, MaxWork: 3001}, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, _, err := left.AddWithContext(right, Context{}.WithBudget(tc.budget))
			if tc.refuse {
				assertCarryRefusal(t, got, err, "AddWithContext")
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			want := new(big.Int).Add(carryBig(t, strings.Repeat("8", 1000)), carryBig(t, strings.Repeat("1", 1000)))
			assertOracleParts(t, got, want, 0)
		})
	}
}

func TestArithmeticTightCarryWidthBoundaries(t *testing.T) {
	for _, width := range []int{19, 38, 39, 1000} {
		digits := strings.Repeat("4", width)
		a, b := MustParse(digits+"E-3"), MustParse(digits+"E-3")
		if (width >= 39) != (a.slow != nil && b.slow != nil) {
			t.Fatalf("width %d did not cross the expected inline/slow boundary", width)
		}
		want, exponent := oracleParts(carryBig(t, digits), -3, carryBig(t, digits), -3, "add")
		for _, tc := range []struct {
			name   string
			budget Budget
			bare   bool
		}{
			{"bare", Budget{}, true},
			{"tight", Budget{MaxDigits: uint64(width)}, false},
			{"loose", Budget{MaxDigits: uint64(width + 1)}, false},
		} {
			t.Run(strconv.Itoa(width)+"/"+tc.name, func(t *testing.T) {
				var got Decimal
				var err error
				if tc.bare {
					got, err = a.Add(b)
				} else {
					got, _, err = a.AddWithContext(b, Context{}.WithBudget(tc.budget))
				}
				if err != nil {
					t.Fatal(err)
				}
				assertOracleParts(t, got, want, exponent)
			})
		}
	}
	for _, tc := range []struct {
		name, left, right string
		bare              func(Decimal, Decimal) (Decimal, error)
		call              func(Decimal, Decimal, Budget) (Decimal, error)
		cap               uint64
		want              string
	}{
		{"one_plus_one", "1", "1", Decimal.Add, addWithBudget, 1, "2"},
		{"one_minus_negative_one", "1", "-1", Decimal.Sub, subWithBudget, 1, "2"},
		{"aligned_gap", "1E+18", "1", Decimal.Add, addWithBudget, 19, "1000000000000000001"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			a, b := MustParse(tc.left), MustParse(tc.right)
			want := carryBig(t, tc.want)
			for _, mode := range []struct {
				name string
				cap  uint64
			}{
				{"bare", 0}, {"tight", tc.cap}, {"loose", tc.cap + 1},
			} {
				t.Run(mode.name, func(t *testing.T) {
					var got Decimal
					var err error
					if mode.name == "bare" {
						got, err = tc.bare(a, b)
					} else {
						got, err = tc.call(a, b, Budget{MaxDigits: mode.cap})
					}
					if err != nil {
						t.Fatal(err)
					}
					assertOracleParts(t, got, want, 0)
				})
			}
		})
	}
}

func TestArithmeticCarryRefusalOperationIdentity(t *testing.T) {
	for _, tc := range []struct {
		name, right, operation string
		call                   func(Decimal, Decimal, Budget) (Decimal, error)
	}{
		{"add", "1", "AddWithContext", addWithBudget},
		{"sub", "-1", "SubWithContext", subWithBudget},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := tc.call(New(9, 0), MustParse(tc.right), Budget{MaxDigits: 1})
			assertCarryRefusal(t, got, err, tc.operation)
		})
	}
}

func TestArithmeticGroupedCarrySparseExtremeGap(t *testing.T) {
	const highExponent int32 = 1<<31 - 1
	const lowExponent int32 = -1 << 31
	high := New(9, highExponent)
	low := New(1, lowExponent)
	a, b := coefficientViewOf(high), coefficientViewOf(low)
	shift := uint64(int64(highExponent) - int64(lowExponent))
	if additionNeedsCarry(&a, shift, &b, 0, shift+1) {
		t.Fatal("sparse extreme exponent gap has no final carry")
	}
}

// TestArithmeticVirtualLimbAlignment is a result-level guard for the
// virtual base-10^9 Add/Sub writer. The independent oracle constructs
// signed integer coefficients and applies the exponent shifts with math/big.
func TestArithmeticVirtualLimbAlignment(t *testing.T) {
	for _, tc := range []struct {
		name, ac, bc string
		ae, be       int32
		an, bn       bool
	}{
		{"zero shift", "1234567890123456789", "9876543210987654321", 0, 0, false, false},
		{"one digit shift", "1234567890123456789", "9876543210987654321", 1, 0, false, false},
		{"eight digit shift", strings.Repeat("9", 40), strings.Repeat("1", 39), 8, 0, false, false},
		{"nine digit shift", strings.Repeat("8", 38), strings.Repeat("7", 38), 9, 0, false, false},
		{"seventeen digit shift", strings.Repeat("1", 75), strings.Repeat("9", 74), 17, 0, false, true},
		{"long borrow", "1" + strings.Repeat("0", 999), "1", 0, 0, false, false},
		{"shifted cross limb borrow", "1", "1", 18, 0, false, false},
		{"long carry", strings.Repeat("9", 1000), "1", 0, 0, false, false},
		{"negative operands", strings.Repeat("9", 90), strings.Repeat("8", 91), 7, 0, true, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			makeInput := func(coeff string, exponent int32, negative bool) Decimal {
				literal := coeff + "E" + strconv.FormatInt(int64(exponent), 10)
				if negative {
					literal = "-" + literal
				}
				return MustParse(literal)
			}
			a := makeInput(tc.ac, tc.ae, tc.an)
			b := makeInput(tc.bc, tc.be, tc.bn)
			ai, _ := new(big.Int).SetString(tc.ac, 10)
			bi, _ := new(big.Int).SetString(tc.bc, 10)
			if tc.an {
				ai.Neg(ai)
			}
			if tc.bn {
				bi.Neg(bi)
			}
			for _, op := range []struct {
				name string
				call func(Decimal, Decimal) (Decimal, error)
			}{
				{"add", Decimal.Add},
				{"sub", Decimal.Sub},
			} {
				t.Run(op.name, func(t *testing.T) {
					got, err := op.call(a, b)
					if err != nil {
						t.Fatal(err)
					}
					want, exponent := oracleParts(ai, tc.ae, bi, tc.be, op.name)
					assertOracleParts(t, got, want, exponent)
				})
			}
		})
	}
}

func mulChargeDigits(n int) string {
	const pattern = "739182645"
	return strings.Repeat(pattern, (n+len(pattern)-1)/len(pattern))[:n]
}

func TestMulWorkChargeCheckedBoundary(t *testing.T) {
	const twoTo32 = uint64(1) << 32
	for _, tc := range []struct {
		name string
		d    uint64
		want uint64
		ok   bool
	}{
		{"2x2", 2, 5, true},
		{"near uint64 maximum", 9 * (twoTo32 - 10), 18446744065119616944, true},
		{"final addition overflows", 9 * (twoTo32 - 1), 0, false},
		{"tile product overflows", 9 * twoTo32, 0, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, ok := mulWorkCharge(tc.d, tc.d, 2*tc.d)
			if ok != tc.ok || ok && got != tc.want {
				t.Fatalf("d1=d2=%d: charge=%d, valid=%v; want charge=%d, valid=%v", tc.d, got, ok, tc.want, tc.ok)
			}
		})
	}
}

func TestMulTileChargeRefusalAllocation(t *testing.T) {
	left := MustParse(mulChargeDigits(10000))
	right := MustParse(mulChargeDigits(10000))
	budget := Budget{MaxWork: 1256543}
	var got Decimal
	var err error
	allocs := testing.AllocsPerRun(100, func() {
		got, _, err = left.MulWithContext(right, Context{}.WithBudget(budget))
	})
	var operation *Error
	if !reflect.DeepEqual(got, Decimal{}) || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != "MulWithContext" || operation.Condition != InsufficientStorage {
		t.Fatalf("B-1 refusal: exact zero result %v, err %v", reflect.DeepEqual(got, Decimal{}), err)
	}
	if allocs > 1 {
		t.Fatalf("B-1 refusal allocated %.0f times per call; want at most the typed error allocation", allocs)
	}
}

func TestMulTileChargeAdjacentCapsAndOracle(t *testing.T) {
	for _, tc := range []struct {
		name          string
		left, right   int
		work          uint64
		negativeRight bool
	}{
		{"2x2", 2, 2, 5, true},
		{"F6_mulsmall_19x1", 19, 1, 23, false},
		{"19x19", 19, 19, 47, false},
		{"38x38", 38, 38, 101, false},
		{"38x39", 38, 39, 102, false},
		{"39x39", 39, 39, 103, false},
		{"208x208", 208, 208, 992, false},
		{"1x1000", 1, 1000, 1113, false},
		{"1000x1000", 1000, 1000, 14544, false},
		{"10000x10000", 10000, 10000, 1256544, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			leftText, rightText := mulChargeDigits(tc.left), mulChargeDigits(tc.right)
			if tc.negativeRight {
				rightText = "-" + rightText
			}
			left := MustParse(leftText + "E-2")
			right := MustParse(rightText + "E+3")
			li, ok := new(big.Int).SetString(leftText, 10)
			if !ok {
				t.Fatal("left oracle input")
			}
			ri, ok := new(big.Int).SetString(rightText, 10)
			if !ok {
				t.Fatal("right oracle input")
			}
			want := new(big.Int).Mul(li, ri)
			wantNegative := want.Sign() < 0
			wantDigits := new(big.Int).Abs(want).String()
			budget := Budget{MaxDigits: uint64(tc.left + tc.right), MaxWork: tc.work}
			got, _, err := left.MulWithContext(right, Context{}.WithBudget(budget))
			if err != nil || got.coefficientDigits() != wantDigits || got.exponent() != 1 || got.negative() != wantNegative {
				t.Fatalf("at cap %d: got %d coefficient digits, exponent %d, negative %v, err %v; want %d coefficient digits, exponent 1, negative %v", tc.work, len(got.coefficientDigits()), got.exponent(), got.negative(), err, len(wantDigits), wantNegative)
			}
			budget.MaxWork--
			got, _, err = left.MulWithContext(right, Context{}.WithBudget(budget))
			var operation *Error
			if !reflect.DeepEqual(got, Decimal{}) || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &operation) || operation.Op != "MulWithContext" || operation.Condition != InsufficientStorage {
				t.Fatalf("one below cap %d: exact zero result %v, err %v", budget.MaxWork, reflect.DeepEqual(got, Decimal{}), err)
			}
			budget.MaxWork = 0
			unbounded, _, err := left.MulWithContext(right, Context{}.WithBudget(budget))
			if err != nil || unbounded.coefficientDigits() != wantDigits || unbounded.exponent() != 1 || unbounded.negative() != wantNegative {
				t.Fatalf("zero work quota: got coefficient %s exponent %d negative %v, err %v", unbounded.coefficientDigits(), unbounded.exponent(), unbounded.negative(), err)
			}
		})
	}
}

func TestArithmeticGroupedCarryTopWidthBoundaries(t *testing.T) {
	for _, width := range []int{8, 9, 17, 18, 38, 39} {
		for _, tc := range []struct {
			name, left, right string
			carry             bool
		}{
			{"no_carry", strings.Repeat("4", width), strings.Repeat("5", width), false},
			{"carry", strings.Repeat("9", width), "1", true},
		} {
			t.Run(tc.name+"_width_"+strconv.Itoa(width), func(t *testing.T) {
				left, right := MustParse(tc.left), MustParse(tc.right)
				li, _ := new(big.Int).SetString(tc.left, 10)
				ri, _ := new(big.Int).SetString(tc.right, 10)
				want := new(big.Int).Add(li, ri)
				if got := len(want.String()) > width; got != tc.carry {
					t.Fatal("independent carry expectation changed")
				}
				for _, sub := range []bool{false, true} {
					operand := right
					if sub {
						operand = MustParse("-" + tc.right)
					}
					for _, cap := range []uint64{uint64(width), uint64(width + 1)} {
						budget := Budget{MaxDigits: cap}
						var got Decimal
						var err error
						op := "AddWithContext"
						if sub {
							got, _, err = left.SubWithContext(operand, Context{}.WithBudget(budget))
							op = "SubWithContext"
						} else {
							got, _, err = left.AddWithContext(operand, Context{}.WithBudget(budget))
						}
						if tc.carry && cap == uint64(width) {
							assertCarryRefusal(t, got, err, op)
							continue
						}
						if err != nil {
							t.Fatal(err)
						}
						assertOracleParts(t, got, want, 0)
					}
				}
			})
		}
	}
}

func TestArithmeticGroupedCarryConcurrentSharedReaders(t *testing.T) {
	leftText, rightText := strings.Repeat("4", 1000), strings.Repeat("5", 1000)
	left, right := MustParse(leftText), MustParse(rightText)
	negativeRight := MustParse("-" + rightText)
	want := strings.Repeat("9", 1000)
	budget := Budget{MaxDigits: 1000}
	const workers, iterations = 8, 50
	start := make(chan struct{})
	var group sync.WaitGroup
	for range workers {
		group.Go(func() {
			<-start
			for range iterations {
				add, _, addErr := left.AddWithContext(right, Context{}.WithBudget(budget))
				sub, _, subErr := left.SubWithContext(negativeRight, Context{}.WithBudget(budget))
				if addErr != nil || subErr != nil || add.String() != want || sub.String() != want {
					t.Errorf("shared grouped scan: add=%v sub=%v", addErr, subErr)
					return
				}
			}
		})
	}
	close(start)
	group.Wait()
	if left.String() != leftText || right.String() != rightText || negativeRight.String() != "-"+rightText {
		t.Fatal("concurrent grouped scan changed a shared operand")
	}
}

// oracleParts uses math/big only in tests and keeps the preferred exponent
// separate from the independently computed signed integer coefficient.
func oracleParts(a *big.Int, ae int32, b *big.Int, be int32, op string) (*big.Int, int32) {
	if op == "mul" {
		return new(big.Int).Mul(a, b), ae + be
	}
	e := min(ae, be)
	x := new(big.Int).Mul(a, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(ae-e)), nil))
	y := new(big.Int).Mul(b, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(be-e)), nil))
	if op == "sub" {
		return x.Sub(x, y), e
	}
	return x.Add(x, y), e
}

func assertOracleParts(t testing.TB, got Decimal, want *big.Int, exponent int32) {
	t.Helper()
	negative := want.Sign() < 0
	magnitude := new(big.Int).Abs(want).String()
	if got.coefficientDigits() != magnitude || got.exponent() != exponent || got.negative() != negative {
		t.Fatalf("got coefficient %s e%d negative %v, want %s e%d negative %v", got.coefficientDigits(), got.exponent(), got.negative(), magnitude, exponent, negative)
	}
}

func TestArithmeticIndependentBigIntOracle(t *testing.T) {
	rng := rand.New(rand.NewSource(20260923))
	for i := range 360 {
		coeff := func() string {
			n := 1 + rng.Intn(75)
			var s strings.Builder
			s.Grow(n)
			s.WriteByte(byte('1' + rng.Intn(9)))
			for range n - 1 {
				s.WriteByte(byte('0' + rng.Intn(10)))
			}
			return s.String()
		}
		as, bs := coeff(), coeff()
		ae, be := int32(rng.Intn(41)-20), int32(rng.Intn(41)-20)
		if i%13 == 0 {
			bs = as
			be = ae
		}
		if i%17 == 0 {
			as = "0"
		}
		if i%19 == 0 {
			bs = "0"
		}
		an, bn := i%2 == 0, i%3 == 0
		makeInput := func(s string, exponent int32, negative bool) Decimal {
			literal := s + "E" + strconv.FormatInt(int64(exponent), 10)
			if negative {
				literal = "-" + literal
			}
			return MustParse(literal)
		}
		a, b := makeInput(as, ae, an), makeInput(bs, be, bn)
		ai, _ := new(big.Int).SetString(as, 10)
		bi, _ := new(big.Int).SetString(bs, 10)
		if an {
			ai.Neg(ai)
		}
		if bn {
			bi.Neg(bi)
		}
		beforeA, beforeB := a.coefficientDigits(), b.coefficientDigits()
		for _, tc := range []struct {
			name string
			call func(Decimal, Decimal) (Decimal, error)
		}{
			{"add", Decimal.Add}, {"sub", Decimal.Sub}, {"mul", Decimal.Mul},
		} {
			got, err := tc.call(a, b)
			if err != nil {
				t.Fatalf("case %d %s: %v", i, tc.name, err)
			}
			want, exponent := oracleParts(ai, ae, bi, be, tc.name)
			assertOracleParts(t, got, want, exponent)
			if a.coefficientDigits() != beforeA || b.coefficientDigits() != beforeB {
				t.Fatalf("case %d %s mutated input", i, tc.name)
			}
		}
	}
}

func TestArithmeticInlineBoundaryAndLimbCarries(t *testing.T) {
	max128 := MustParse("340282366920938463463374607431768211455")
	got, err := max128.Add(One())
	if err != nil {
		t.Fatal(err)
	}
	want, _ := new(big.Int).SetString("340282366920938463463374607431768211455", 10)
	want.Add(want, big.NewInt(1))
	assertOracleParts(t, got, want, 0)
	if got.slow == nil {
		t.Fatal("2^128 result did not promote to slow coefficient")
	}
	// One digit times 37 digits has a 38-digit logical envelope but a
	// six-limb n+m multiplication buffer. It must still publish inline.
	wide := MustParse(strings.Repeat("9", 37))
	got, err = New(9, 0).Mul(wide)
	if err != nil {
		t.Fatal(err)
	}
	wi, _ := new(big.Int).SetString(strings.Repeat("9", 37), 10)
	assertOracleParts(t, got, wi.Mul(wi, big.NewInt(9)), 0)
	if got.slow != nil {
		t.Fatal("38-digit six-buffer-limb product did not publish inline")
	}

	a, b := MustParse(strings.Repeat("9", 90)), MustParse(strings.Repeat("9", 90))
	for _, tc := range []struct {
		name string
		call func(Decimal, Decimal) (Decimal, error)
	}{
		{"add", Decimal.Add}, {"sub", Decimal.Sub}, {"mul", Decimal.Mul},
	} {
		got, err := tc.call(a, b)
		if err != nil {
			t.Fatal(err)
		}
		ai, _ := new(big.Int).SetString(strings.Repeat("9", 90), 10)
		want, e := oracleParts(ai, 0, ai, 0, tc.name)
		assertOracleParts(t, got, want, e)
	}
}

var carryGroupBenchmarkResult Decimal
var carryGroupBenchmarkError error

// BenchmarkCarryGroupPreflight measures public tight and loose Add admission.
// Every named workload checks an independent integer result or typed refusal
// before timing. The loose treatment skips the carry scan.
func BenchmarkCarryGroupPreflight(b *testing.B) {
	for _, tc := range []struct {
		name, left, right string
	}{
		{"one_no_carry", "1", "1"},
		{"width19_no_carry", "4123456789012345678", "1234567890123456789"},
		{"slow1000_short_no_carry", "4" + strings.Repeat("0", 999), "1"},
		{"slow1000_full_no_carry", strings.Repeat("4", 1000), strings.Repeat("5", 1000)},
		{"slow1000_full_carry", strings.Repeat("9", 1000), "1"},
	} {
		a, rhs := MustParse(tc.left), MustParse(tc.right)
		left, leftOK := new(big.Int).SetString(tc.left, 10)
		right, rightOK := new(big.Int).SetString(tc.right, 10)
		if !leftOK || !rightOK {
			b.Fatal("invalid independent benchmark input")
		}
		want, exponent := oracleParts(left, 0, right, 0, "add")
		span := uint64(max(len(tc.left), len(tc.right)))
		carry := uint64(len(want.String())) > span
		b.Run(tc.name, func(b *testing.B) {
			for _, quota := range []struct {
				name string
				cap  uint64
			}{
				{"tight", span}, {"loose", span + 1},
			} {
				b.Run(quota.name, func(b *testing.B) {
					budget := Budget{MaxDigits: quota.cap}
					refuse := quota.name == "tight" && carry
					got, _, err := a.AddWithContext(rhs, Context{}.WithBudget(budget))
					if refuse {
						assertCarryRefusal(b, got, err, "AddWithContext")
					} else {
						if err != nil {
							b.Fatal(err)
						}
						assertOracleParts(b, got, want, exponent)
					}
					b.ReportAllocs()
					b.ResetTimer()
					for b.Loop() {
						carryGroupBenchmarkResult, _, carryGroupBenchmarkError = a.AddWithContext(rhs, Context{}.WithBudget(budget))
						if (carryGroupBenchmarkError != nil) != refuse {
							b.Fatal("timed refusal changed")
						}
					}
				})
			}
		})
	}
}

var carryGroupSubBenchmarkResult Decimal
var carryGroupSubBenchmarkError error

// BenchmarkCarryGroupSubPreflight measures the public Sub path with a
// negative right operand, so Sub uses the same-sign grouped carry preflight.
func BenchmarkCarryGroupSubPreflight(b *testing.B) {
	for _, tc := range []struct {
		name, left, right string
	}{
		{"full_no_carry", strings.Repeat("4", 1000), "-" + strings.Repeat("5", 1000)},
		{"full_carry", strings.Repeat("9", 1000), "-1"},
	} {
		left, right := MustParse(tc.left), MustParse(tc.right)
		li, leftOK := new(big.Int).SetString(tc.left, 10)
		ri, rightOK := new(big.Int).SetString(tc.right, 10)
		if !leftOK || !rightOK {
			b.Fatal("invalid independent benchmark input")
		}
		want, exponent := oracleParts(li, 0, ri, 0, "sub")
		span := uint64(len(tc.left))
		carry := uint64(len(want.String())) > span
		b.Run(tc.name, func(b *testing.B) {
			for _, quota := range []struct {
				name string
				cap  uint64
			}{
				{"tight", span}, {"loose", span + 1}, {"unbounded", 0},
			} {
				b.Run(quota.name, func(b *testing.B) {
					budget := Budget{MaxDigits: quota.cap}
					refuse := quota.name == "tight" && carry
					got, _, err := left.SubWithContext(right, Context{}.WithBudget(budget))
					if refuse {
						assertCarryRefusal(b, got, err, "SubWithContext")
					} else {
						if err != nil {
							b.Fatal(err)
						}
						assertOracleParts(b, got, want, exponent)
					}
					b.ReportAllocs()
					b.ResetTimer()
					for b.Loop() {
						carryGroupSubBenchmarkResult, _, carryGroupSubBenchmarkError = left.SubWithContext(right, Context{}.WithBudget(budget))
						if (carryGroupSubBenchmarkError != nil) != refuse {
							b.Fatal("timed refusal changed")
						}
					}
				})
			}
		})
	}
}

// TestAddExactAtPreferredScale checks that addition is always exact at
// the preferred scale: 1.10 + 0 by bare Add and by Context{} Add is 1.10
// at exponent −2 with no conditions, and random bare Add equals the
// math/big sum at min(ex, ey), with Context{} Add identical.
func TestAddExactAtPreferredScale(t *testing.T) {
	x, zero := MustParse("1.10"), MustParse("0")
	bare, err := x.Add(zero)
	if err != nil || bare.String() != "1.10" || bare.exponent() != -2 {
		t.Fatalf("1.10 + 0 = %s, %v", bare, err)
	}
	unrounded, conditions, err := x.AddWithContext(zero, Context{})
	if err != nil || conditions != 0 || !unrounded.Equal(bare) || unrounded.exponent() != -2 {
		t.Fatalf("Context{} 1.10 + 0 = %s, %v, %v", unrounded, conditions, err)
	}
	r := randv2.New(randv2.NewPCG(53, 14))
	for range 5000 {
		a, b := sumOperands(r, 2, 60)[0], sumOperands(r, 2, 60)[1]
		got, err := a.Add(b)
		if err != nil {
			t.Fatal(err)
		}
		want := new(big.Rat).Add(divRat(t, a), divRat(t, b))
		if divRat(t, got).Cmp(want) != 0 || got.exponent() != min(a.exponent(), b.exponent()) {
			t.Fatalf("%s + %s = %s, want %s at %d", a, b, got, want.RatString(), min(a.exponent(), b.exponent()))
		}
		context, conditions, err := a.AddWithContext(b, Context{})
		if err != nil || conditions != 0 || !context.Equal(got) || context.exponent() != got.exponent() || context.negative() != got.negative() {
			t.Fatalf("Context{} %s + %s = %s, %v, %v; bare %s", a, b, context, conditions, err, got)
		}
	}
}

// TestOperationsDoNotMutateAliasedOperands checks that operations never
// mutate receivers or operands: a slow-band and an inline value, each used
// as receiver and operand of the same call, keep their text, exponent and
// coefficient storage through every arithmetic, selection, rounding and
// context family, and each exact result equals the math/big.Rat value of
// the operation on the literal. Context results equal the same call on
// freshly parsed, unaliased operands.
func TestOperationsDoNotMutateAliasedOperands(t *testing.T) {
	ctx := Decimal128Context()
	for _, literal := range []string{strings.Repeat("9", 80) + "E-40", "1234.50"} {
		x := MustParse(literal)
		text, exponent := x.String(), x.exponent()
		var limbs []uint32
		if x.slow != nil {
			limbs = slices.Clone(x.slow.limbs)
		}
		r, ok := new(big.Rat).SetString(literal)
		if !ok {
			t.Fatal(literal)
		}
		sq := new(big.Rat).Mul(r, r)
		exact := func(name string, got Decimal, err error, want *big.Rat) {
			t.Helper()
			if err != nil {
				t.Fatalf("%s(%s): %v", name, literal, err)
			}
			g, ok := new(big.Rat).SetString(got.String())
			if !ok || g.Cmp(want) != 0 {
				t.Errorf("%s(%s) = %s, want %s", name, literal, got, want.RatString())
			}
		}
		fresh := func() Decimal { return MustParse(literal) }
		checkUnchanged := func(name string) {
			t.Helper()
			if x.String() != text || x.exponent() != exponent || (limbs != nil && !slices.Equal(x.slow.limbs, limbs)) {
				t.Fatalf("%s mutated its aliased receiver/operand %s", name, literal)
			}
		}
		sum, err := x.Add(x)
		exact("Add", sum, err, new(big.Rat).Add(r, r))
		checkUnchanged("Add")
		diff, err := x.Sub(x)
		exact("Sub", diff, err, new(big.Rat))
		checkUnchanged("Sub")
		prod, err := x.Mul(x)
		exact("Mul", prod, err, sq)
		checkUnchanged("Mul")
		quo, err := x.Div(x)
		exact("Div", quo, err, big.NewRat(1, 1))
		checkUnchanged("Div")
		pow, err := x.Pow(2)
		exact("Pow", pow, err, sq)
		checkUnchanged("Pow")
		total, err := Sum(x, x, x)
		exact("Sum", total, err, new(big.Rat).Mul(r, big.NewRat(3, 1)))
		checkUnchanged("Sum")
		multiple, _, err := x.RoundToMultiple(x, TiesToEven)
		exact("RoundToMultiple", multiple, err, r)
		checkUnchanged("RoundToMultiple")
		exact("Min", x.Min(x), nil, r)
		exact("Max", x.Max(x), nil, r)
		exact("Neg", x.Neg().Neg(), nil, r)
		exact("Reduce", x.Reduce(), nil, r)
		checkUnchanged("selection")
		for name, op := range map[string]func(a, b Decimal, c Context) (Decimal, Conditions, error){
			"AddWithContext": Decimal.AddWithContext,
			"SubWithContext": Decimal.SubWithContext,
			"MulWithContext": Decimal.MulWithContext,
			"DivWithContext": Decimal.DivWithContext,
		} {
			got, gotC, gotErr := op(x, x, ctx)
			want, wantC, wantErr := op(fresh(), fresh(), ctx)
			if got.String() != want.String() || got.exponent() != want.exponent() || gotC != wantC || (gotErr == nil) != (wantErr == nil) {
				t.Errorf("%s aliased = %s %v %v, unaliased %s %v %v", name, got, gotC, gotErr, want, wantC, wantErr)
			}
			checkUnchanged(name)
		}
	}
}

// TestDefaultRegimeIsExactUntilLimits checks that the default regime is
// exact until limits: with no context, a
// 2000-nines square has no global coefficient cap and equals the math/big
// product; a product whose ideal exponent leaves int32 in either direction
// returns Decimal{} and an ErrExponentRange Error with condition 0;
// and growth under a caller budget is a checked InsufficientStorage refusal
// one digit below the 4000-digit result, admitted at 4000.
func TestDefaultRegimeIsExactUntilLimits(t *testing.T) {
	nines := strings.Repeat("9", 2000)
	x := MustParse(nines)
	got, err := x.Mul(x)
	n, _ := new(big.Int).SetString(nines, 10)
	if want := new(big.Int).Mul(n, n).String(); err != nil || got.String() != want || got.CoefficientDigits() != 4000 {
		t.Fatalf("(10^2000-1)^2 = %d digits, %v; want the math/big product", got.CoefficientDigits(), err)
	}
	for _, tc := range []struct{ a, b Decimal }{
		{New(1, math.MaxInt32), New(1, 1)},
		{New(1, math.MinInt32), New(1, -1)},
		{New(0, math.MaxInt32), New(7, 1)},
	} {
		d, err := tc.a.Mul(tc.b)
		var opErr *Error
		if !reflect.DeepEqual(d, Decimal{}) || !errors.Is(err, ErrExponentRange) || !errors.As(err, &opErr) || opErr.Condition != 0 || opErr.Op != "Mul" {
			t.Errorf("%s x %s = %s, %v; want Decimal{} and Mul ErrExponentRange with condition 0", tc.a, tc.b, d, err)
		}
	}
	d, _, err := x.MulWithContext(x, Context{}.WithBudget(Budget{MaxDigits: 3999}))
	var opErr *Error
	if !reflect.DeepEqual(d, Decimal{}) || !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &opErr) || opErr.Op != "MulWithContext" {
		t.Errorf("4000-digit product under a 3999-digit budget = %v; want a MulWithContext InsufficientStorage refusal", err)
	}
	if d, _, err := x.MulWithContext(x, Context{}.WithBudget(Budget{MaxDigits: 4000})); err != nil || d.String() != got.String() {
		t.Errorf("4000-digit product under a 4000-digit budget: %v", err)
	}
}

// addSubStaged runs the term-form plan (addSubAdmit, addSubPlan.unchanged,
// addSubFinish) as FMA runs it, with no prior work, over Decimal operands.
func addSubStaged(d, other Decimal, budget Budget, subtract bool) (Decimal, error) {
	var a, b addTerm
	if !a.load(d, false) || !b.load(other, subtract) {
		return arithmeticFailure("Add", ErrInsufficientStorage)
	}
	p, err := addSubAdmit(&a, &b, budget.arith(), 0, "Add")
	if err != nil {
		return Decimal{}, err
	}
	switch p.unchanged(&a, &b) {
	case addSelfA:
		return d, nil
	case addSelfB:
		other = other.withNegative(b.negative)
		return other, nil
	}
	return addSubFinish(&p, &a, &b, budget.arith(), "Add")
}

// TestAddSubStagesMatchAddKernel pins FMA's term-form Add/Sub plan to the
// Decimal kernel it restates:
// over operands inline and limb-held, zeros and negative zeros, carries,
// cancellations and exponent gaps, and budgets at, just below and just
// above each operand pair's own work and digit charges, addSubAdmit and
// addSubFinish return exactly addSubLimbs's result (representation
// included) or its refusal. A vacuity guard requires refusals, carries
// and every path.
func TestAddSubStagesMatchAddKernel(t *testing.T) {
	r := randv2.New(randv2.NewPCG(53, 66))
	seen := map[string]int{}
	for range 30000 {
		x, y := fmaOperand(r, 50, -30, 30), fmaOperand(r, 50, -30, 30)
		if r.IntN(4) == 0 {
			y = x.Neg()
		}
		subtract := r.IntN(2) == 0
		work := smallestAdmitting(1<<40, func(w uint64) bool {
			_, err := x.addSubLimbs(y, limits{MaxWork: w}, "Add", subtract)
			return err == nil
		})
		digits := smallestAdmitting(1<<40, func(n uint64) bool {
			_, err := x.addSubLimbs(y, limits{MaxDigits: n}, "Add", subtract)
			return err == nil
		})
		for _, budget := range []Budget{{}, {MaxWork: work}, {MaxWork: work - 1}, {MaxDigits: digits}, {MaxDigits: digits - 1}, {MaxDigits: digits + 1, MaxWork: work + 1}} {
			want, wantErr := x.addSubLimbs(y, budget.arith(), "Add", subtract)
			got, err := addSubStaged(x, y, budget, subtract)
			if !sameRepresentation(got, want) || (err == nil) != (wantErr == nil) || err != nil && err.Error() != wantErr.Error() {
				t.Fatalf("%v %v sub=%v %+v: staged %v %v, kernel %v %v", x, y, subtract, budget, got, err, want, wantErr)
			}
			switch {
			case err != nil:
				seen["refused"]++
			case want.isZero():
				seen["zero"]++
			case want.CoefficientDigits() > max(x.CoefficientDigits(), y.CoefficientDigits()):
				seen["carry"]++
			default:
				seen["other"]++
			}
		}
	}
	for _, kind := range []string{"refused", "zero", "carry", "other"} {
		if seen[kind] < 1000 {
			t.Fatalf("vacuous: %v", seen)
		}
	}
}

// TestMulIdealExponentOverflowIsExactOrError checks that Mul is exact or
// returns an error with a condition identity: for in-domain operands whose
// ideal exponent s1+s2 leaves int32 in either direction, bare Mul returns
// Decimal{} and an *Error for "Mul" whose cause is ErrExponentRange under
// errors.Is and whose GDA Condition is zero, for inline, two-word and limb-held
// coefficients in both operand orders. The rows include products with trailing
// zeros (10·10 and 10^20·10^20), whose value a coefficient rebase could store
// at MaxInt32, so a rebase or a clamped boundary value cannot pass; a panic
// fails the test. Each overflowing pair has an in-domain neighbour one exponent
// step back that multiplies exactly to the math/big product at the int32 edge.
func TestMulIdealExponentOverflowIsExactOrError(t *testing.T) {
	coefficients := []string{"1", "10", "7", "18446744073709551615", "100000000000000000000", strings.Repeat("9", 100), "1" + strings.Repeat("0", 90)}
	var refused, exact int
	for _, ca := range coefficients {
		for _, cb := range coefficients {
			for _, edge := range []int64{math.MaxInt32, math.MinInt32} {
				step := int64(1)
				if edge < 0 {
					step = -1
				}
				for _, over := range []bool{true, false} {
					ea := edge - 3*step
					eb := 3 * step
					if over {
						eb += step
					}
					a := MustParse(ca + "E" + strconv.FormatInt(ea, 10))
					b := MustParse(cb + "E" + strconv.FormatInt(eb, 10))
					for _, pair := range [][2]Decimal{{a, b}, {b, a}} {
						got, err := pair[0].Mul(pair[1])
						if over {
							refused++
							var oe *Error
							if !reflect.DeepEqual(got, Decimal{}) || !errors.Is(err, ErrExponentRange) || !errors.As(err, &oe) || oe.Op != "Mul" || oe.Condition != 0 {
								t.Errorf("%sE%d x %sE%d = %+v, %v; want Decimal{} and a Mul ErrExponentRange error with Condition 0", ca, ea, cb, eb, got, err)
							}
							continue
						}
						exact++
						x, _ := new(big.Int).SetString(ca, 10)
						y, _ := new(big.Int).SetString(cb, 10)
						if want := new(big.Int).Mul(x, y).String(); err != nil || got.coefficientDigits() != want || int64(got.exponent()) != edge {
							t.Errorf("%sE%d x %sE%d = %s e%d, %v; want %s at exponent %d", ca, ea, cb, eb, got.coefficientDigits(), got.exponent(), err, want, edge)
						}
					}
				}
			}
		}
	}
	if refused != 196 || exact != 196 {
		t.Fatalf("checked %d refusals and %d exact products; want 196 each", refused, exact)
	}
}

// TestAddExtremeExponentGapRefusedBeforeAllocation checks that arithmetic
// growth is refused before allocation: adding 1E+2147483647 to
// 1E-2147483648 needs a 2^32-digit aligned coefficient. Under an explicit
// digit budget, AddWithContext and SubWithContext at Context{} in both
// operand orders, with inline and slow operands, return Decimal{} and an
// *Error with ErrInsufficientStorage, allocating at
// most the error object and never the expanded coefficient, and leave both
// operands unchanged. The oracle is the aligned span computed with math/big
// (exponent gap plus the larger operand length); a 41-digit control at the
// same budget shape admits its exact sum, so the refusal is not vacuous.
func TestAddExtremeExponentGapRefusedBeforeAllocation(t *testing.T) {
	high := New(1, math.MaxInt32)
	low := New(1, math.MinInt32)
	slowHigh, err := Parse(strings.Repeat("9", 1000) + "E+2147482647")
	if err != nil || slowHigh.slow == nil {
		t.Fatalf("slow fixture: %+v, %v", slowHigh, err)
	}
	span := new(big.Int).Sub(big.NewInt(math.MaxInt32), big.NewInt(math.MinInt32))
	span.Add(span, big.NewInt(1)) // aligned digits of 1E+2147483647 + 1E-2147483648
	if span.Cmp(new(big.Int).Lsh(big.NewInt(1), 32)) != 0 {
		t.Fatalf("oracle span %s, want 2^32", span)
	}
	budget := Budget{MaxDigits: 1 << 20}
	type call struct {
		name string
		op   string
		run  func(a, b Decimal) (Decimal, error)
	}
	calls := []call{
		{"add", "AddWithContext", func(a, b Decimal) (Decimal, error) {
			res, _, resErr := a.AddWithContext(b, Context{}.WithBudget(budget))
			return res, resErr
		}},
		{"sub", "SubWithContext", func(a, b Decimal) (Decimal, error) {
			res, _, resErr := a.SubWithContext(b, Context{}.WithBudget(budget))
			return res, resErr
		}},
	}
	for _, c := range calls {
		for _, pair := range []struct {
			name string
			a, b Decimal
		}{
			{"high+low", high, low},
			{"low+high", low, high},
			{"slow-high+low", slowHigh, low},
			{"low+slow-high", low, slowHigh},
		} {
			t.Run(c.name+"/"+pair.name, func(t *testing.T) {
				a, b := pair.a, pair.b
				aText, bText := a.String(), b.String()
				aSlow, bSlow := a.slow, b.slow
				var aLimbs, bLimbs []uint32
				if aSlow != nil {
					aLimbs = slices.Clone(aSlow.limbs)
				}
				if bSlow != nil {
					bLimbs = slices.Clone(bSlow.limbs)
				}
				got, err := c.run(a, b)
				var oe *Error
				if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &oe) || oe.Op != c.op ||
					oe.Condition != InsufficientStorage || !got.isZero() || got.exponent() != 0 || got.negative() || got.slow != nil {
					t.Fatalf("got (%+v, %v), want Decimal{} and %s/ErrInsufficientStorage", got, err, c.op)
				}
				allocs := testing.AllocsPerRun(20, func() { arithmeticResultSink, _ = c.run(a, b) })
				if allocs > 1 {
					t.Fatalf("refusal allocations=%g, want at most the error", allocs)
				}
				if bytes := coldAllocatedWithin(func() { arithmeticResultSink, _ = c.run(a, b) }, 256); bytes > 256 {
					t.Fatalf("refusal allocated %d bytes, want only the error object", bytes)
				}
				if a.String() != aText || b.String() != bText || a.slow != aSlow || b.slow != bSlow ||
					aSlow != nil && !slices.Equal(aSlow.limbs, aLimbs) || bSlow != nil && !slices.Equal(bSlow.limbs, bLimbs) {
					t.Fatal("refusal changed an operand")
				}
			})
		}
	}
	// Non-vacuity: 1E+20 + 1E-20 spans 41 digits; cap 40 refuses and 41
	// admits the math/big sum 10^40 + 1 at exponent -20.
	a, b := New(1, 20), New(1, -20)
	if _, _, err := a.AddWithContext(b, Context{}.WithBudget(Budget{MaxDigits: 40})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("41-digit span at cap 40: %v", err)
	}
	got, _, err := a.AddWithContext(b, Context{}.WithBudget(Budget{MaxDigits: 41}))
	want := new(big.Int).Add(new(big.Int).Exp(big.NewInt(10), big.NewInt(40), nil), big.NewInt(1))
	if err != nil || got.exponent() != -20 || !got.Equal(MustParse(want.String()+"E-20")) {
		t.Fatalf("41-digit span at cap 41: %s, %v; want %sE-20", got, err, want)
	}
}

// dispatchSample draws a canonical operand near base with its signed
// coefficient: zero, one, small and tie-shaped values, the one-word and
// two-word boundaries, random two-word values, and limb values of 39 to
// 60 digits.
func dispatchSample(r *rand.Rand, base int32) (Decimal, *big.Int) {
	two64 := new(big.Int).Lsh(big.NewInt(1), 64)
	two128 := new(big.Int).Lsh(big.NewInt(1), 128)
	c := new(big.Int)
	switch r.Intn(12) {
	case 0:
	case 1:
		c.SetInt64(1)
	case 2:
		c.SetInt64(r.Int63n(1_000_000))
	case 3:
		c.SetInt64(r.Int63n(100_000)*10 + 5) // a tie at one dropped digit
	case 4:
		c.Sub(two64, big.NewInt(int64(1+r.Intn(2)))) // 2^64-2, 2^64-1
	case 5:
		c.Add(two64, big.NewInt(int64(r.Intn(2)))) // 2^64, 2^64+1
	case 6:
		c.Sub(two128, big.NewInt(int64(1+r.Intn(2)))) // 2^128-2, 2^128-1
	case 7:
		c.SetUint64(r.Uint64())
		c.Lsh(c, uint(r.Intn(64))).Or(c, new(big.Int).SetUint64(r.Uint64()))
	case 8:
		c.Exp(big.NewInt(10), big.NewInt(int64(r.Intn(39))), nil)
		c.Sub(c, big.NewInt(int64(r.Intn(2))))
	case 9:
		digits := 39 + r.Intn(22)
		c.Exp(big.NewInt(10), big.NewInt(int64(digits-1)), nil)
		c.Add(c, new(big.Int).Rand(r, c))
	default:
		c.SetUint64(r.Uint64() >> r.Intn(64))
	}
	exponent := int64(base) + int64(r.Intn(41)-20)
	exponent = max(math.MinInt32, min(math.MaxInt32, exponent))
	negative := c.Sign() != 0 && r.Intn(2) == 0
	var limbs []uint32
	billion := new(big.Int).SetUint64(decimalLimbBase)
	for q, m := new(big.Int).Set(c), new(big.Int); q.Sign() != 0; {
		q.DivMod(q, billion, m)
		limbs = append(limbs, uint32(m.Uint64()))
	}
	d := publishOwned(limbs, int32(exponent), negative)
	if negative {
		c.Neg(c)
	}
	return d, c
}

// dispatchBase is a random operand band: near zero or within 20 of an
// int32 exponent limit.
func dispatchBase(r *rand.Rand) int32 {
	switch r.Intn(6) {
	case 0:
		return math.MinInt32 + 20
	case 1:
		return math.MaxInt32 - 20
	}
	return int32(r.Intn(61) - 30)
}

// TestExactDispatchMatchesGeneralPath pins the lean dispatchers to
// the general limb paths and to math/big. The bare Add, Sub and Mul, the
// inline-only addSubExact and mulExact, the budgeted addSub and multiply,
// and the context entry points must return the representation, cohort,
// conditions and error of the general path, over signs, zeros, the
// one-word and two-word boundaries, carries out of 128 bits, exponent
// bands at the int32 limits, admitting and refusing budgets, and every
// rounding mode at exact ties. Vacuity guards require the inline paths to
// serve a substantial share of the cases and to decline others.
func TestExactDispatchMatchesGeneralPath(t *testing.T) {
	r := rand.New(rand.NewSource(20261030))
	ten := big.NewInt(10)
	pow10 := func(k int64) *big.Int { return new(big.Int).Exp(ten, big.NewInt(k), nil) }
	unlimited := Budget{MaxDigits: math.MaxUint64, MaxWork: math.MaxUint64}
	same := func(label string, a, b Decimal, got Decimal, gotErr error, want Decimal, wantErr error) {
		t.Helper()
		if !reflect.DeepEqual(gotErr, wantErr) || gotErr == nil && !sameRepresentation(got, want) {
			t.Fatalf("%s(%#v, %#v) = %#v, %v; general path %#v, %v", label, a, b, got, gotErr, want, wantErr)
		}
	}
	var fastAdd, declinedAdd, fastMul, declinedMul, refused, admittedBudget, contextCases int
	const trials = 60_000
	for range trials {
		base := dispatchBase(r)
		a, ca := dispatchSample(r, base)
		b, cb := dispatchSample(r, base)
		for _, subtract := range []bool{false, true} {
			op := "Add"
			mode := exactLimbs
			if subtract {
				op, mode = "Sub", exactLimbs|exactSubtract
			}
			var got Decimal
			var err error
			if subtract {
				got, err = a.Sub(b)
			} else {
				got, err = a.Add(b)
			}
			want, wantErr := a.addSubLimbs(b, limits{}, op, subtract)
			same(op, a, b, got, err, want, wantErr)
			e := min(a.exponent(), b.exponent())
			x := new(big.Int).Mul(ca, pow10(int64(a.exponent())-int64(e)))
			y := new(big.Int).Mul(cb, pow10(int64(b.exponent())-int64(e)))
			if subtract {
				y.Neg(y)
			}
			if err != nil {
				t.Fatalf("%s(%#v, %#v): %v", op, a, b, err)
			}
			assertOracleParts(t, got, x.Add(x, y), e)
			inline, ok, inlineErr := a.addSubExact(b, mode&^exactLimbs)
			if ok {
				fastAdd++
				same(op+" inline", a, b, inline, inlineErr, want, wantErr)
			} else {
				declinedAdd++
				if inlineErr != nil || !sameRepresentation(inline, Decimal{}) {
					t.Fatalf("declined %s inline sum returned %#v, %v", op, inline, inlineErr)
				}
			}
			budget := limits{MaxDigits: uint64(r.Intn(48)), MaxWork: uint64(r.Intn(320))}
			got, err = a.addSub(b, budget, op, subtract)
			want, wantErr = a.addSubLimbs(b, budget, op, subtract)
			same(op+" budgeted", a, b, got, err, want, wantErr)
			if wantErr != nil {
				refused++
			} else if budget != (limits{}) {
				admittedBudget++
			}
		}
		// Mul draws its second operand from an independent band so that
		// exponent sums leave int32 at both limits.
		mb, cmb := dispatchSample(r, dispatchBase(r))
		got, err := a.Mul(mb)
		e := int64(a.exponent()) + int64(mb.exponent())
		general := func(budget limits) (Decimal, error) {
			if e < math.MinInt32 || e > math.MaxInt32 {
				return arithmeticFailure("Mul", ErrExponentRange)
			}
			return a.multiplyLimbs(mb, budget, "Mul", int32(e))
		}
		want, wantErr := general(limits{})
		same("Mul", a, mb, got, err, want, wantErr)
		if err == nil {
			assertOracleParts(t, got, new(big.Int).Mul(ca, cmb), int32(e))
		} else if !errors.Is(err, ErrExponentRange) {
			t.Fatalf("Mul(%#v, %#v): %v", a, mb, err)
		}
		if inline, ok, inlineErr := a.mulExact(mb, 0); ok {
			fastMul++
			same("Mul inline", a, mb, inline, inlineErr, want, wantErr)
		} else {
			declinedMul++
		}
		budget := limits{MaxDigits: uint64(r.Intn(90)), MaxWork: uint64(r.Intn(400))}
		got, err = a.multiply(mb, budget, "Mul")
		want, wantErr = general(budget)
		same("Mul budgeted", a, mb, got, err, want, wantErr)
		// The context entry points against their unlimited-budget form,
		// which bypasses the inline paths.
		if r.Intn(4) == 0 {
			var guards *ExponentGuards
			if r.Intn(3) == 0 {
				guards = &ExponentGuards{Emin: -40, Emax: 40}
			}
			ctx, cerr := NewContext(uint32(1+r.Intn(45)), RoundingMode(r.Intn(int(Exact)+1)), guards, 0)
			if cerr != nil {
				t.Fatal(cerr)
			}
			dispatchContextAgrees(t, a, b, mb, ctx, ctx.WithBudget(unlimited))
			contextCases++
		}
	}
	// Exact ties at one dropped digit, for every rounding mode and sign.
	var ties int
	for mode := TiesToEven; mode <= Exact; mode++ {
		for _, digits := range []int64{2, 5, 19, 20, 38} {
			for _, negative := range []bool{false, true} {
				c := new(big.Int).Mul(big.NewInt(int64(1+r.Intn(9))), pow10(digits-1))
				c.Add(c, big.NewInt(5)) // ...05 rounds at one dropped digit
				if digits == 38 {
					c.Sub(pow10(38), big.NewInt(5)) // 99...95 carries out
				}
				tie := MustParse(c.String() + "E-3")
				if negative {
					tie = tie.negated()
				}
				ctx, cerr := NewContext(uint32(digits-1), mode, nil, 0)
				if cerr != nil {
					t.Fatal(cerr)
				}
				dispatchContextAgrees(t, tie, New(0, -3), One(), ctx, ctx.WithBudget(unlimited))
				ties++
			}
		}
	}
	if fastAdd < trials/2 || declinedAdd < trials/20 || fastMul < trials/4 || declinedMul < trials/20 || refused < trials/10 || admittedBudget < trials/10 || contextCases < trials/8 || ties == 0 {
		t.Fatalf("vacuous dispatch classes: add %d/%d mul %d/%d budget refused %d admitted %d context %d ties %d", fastAdd, declinedAdd, fastMul, declinedMul, refused, admittedBudget, contextCases, ties)
	}
	t.Logf("inline add %d declined %d; inline mul %d declined %d; budget refused %d admitted %d; context %d; ties %d", fastAdd, declinedAdd, fastMul, declinedMul, refused, admittedBudget, contextCases, ties)
}

// dispatchContextAgrees checks AddWithContext, SubWithContext and
// MulWithContext under ctx against general, the same context with an
// unlimited budget, which never takes an inline path.
func dispatchContextAgrees(t *testing.T, a, b, m Decimal, ctx, general Context) {
	t.Helper()
	check := func(label string, x, y Decimal, run func(Decimal, Decimal, Context) (Decimal, Conditions, error)) {
		t.Helper()
		got, gotC, gotErr := run(x, y, ctx)
		want, wantC, wantErr := run(x, y, general)
		if gotC != wantC || !reflect.DeepEqual(gotErr, wantErr) || gotErr == nil && !sameRepresentation(got, want) {
			t.Fatalf("%s(%#v, %#v, %+v) = %#v %v %v; general %#v %v %v", label, x, y, ctx, got, gotC, gotErr, want, wantC, wantErr)
		}
	}
	check("AddWithContext", a, b, Decimal.AddWithContext)
	check("SubWithContext", a, b, Decimal.SubWithContext)
	check("MulWithContext", a, m, Decimal.MulWithContext)
}
