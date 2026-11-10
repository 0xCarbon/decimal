// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"math/big"
	"testing"
)

// oracleDirection is the result-direction bit of an oracle's rounded
// value relative to the exact result: the sign of result − exact, decided by
// exact math/big.Rat comparison and never read from the implementation.
func oracleDirection(result, exact *big.Rat) Conditions {
	switch result.Cmp(exact) {
	case 1:
		return Increased
	case -1:
		return Decreased
	}
	return 0
}

// directionValueRat is the exact rational value of a returned Decimal, read
// from its coefficient digits, exponent and sign with math/big.
func directionValueRat(d Decimal) *big.Rat {
	return quantizeOracleRat(d.coefficientDigits(), d.exponent(), d.negative())
}

// directionAdjusted is floor(log10 |v|) for a nonzero rational.
func directionAdjusted(v *big.Rat) int64 {
	magnitude := new(big.Rat).Abs(v)
	a := int64(len(magnitude.Num().String())) - int64(len(magnitude.Denom().String()))
	for magnitude.Cmp(pow10Rat(a)) < 0 {
		a--
	}
	for magnitude.Cmp(pow10Rat(a+1)) >= 0 {
		a++
	}
	return a
}

// directionGrid returns the greatest and least multiples of 10^quantum that
// enclose exact: the only results a tight directed rounding may return.
func directionGrid(exact *big.Rat, quantum int64) (floor, ceil *big.Rat) {
	scaled := new(big.Rat).Mul(exact, pow10Rat(-quantum))
	// Rat denominators are positive, so Euclidean division is floor division.
	low := new(big.Int).Div(scaled.Num(), scaled.Denom())
	high := new(big.Int).Set(low)
	if !scaled.IsInt() {
		high.Add(high, big.NewInt(1))
	}
	floor = new(big.Rat).Mul(new(big.Rat).SetInt(low), pow10Rat(quantum))
	ceil = new(big.Rat).Mul(new(big.Rat).SetInt(high), pow10Rat(quantum))
	return floor, ceil
}

// directionPrecisionQuantum is the exponent of the rounding grid a finite
// precision p uses for exact: the p-digit quantum of exact's decade, never
// below Etiny under guards. A carry into the next decade (9.995 to 10.0 at
// p=3) lands on a multiple of this finer quantum.
func directionPrecisionQuantum(exact *big.Rat, p int64, guarded bool, emin int64) int64 {
	if exact.Sign() == 0 {
		return 0
	}
	quantum := directionAdjusted(exact) - p + 1
	if guarded {
		quantum = max(quantum, emin-p+1)
	}
	return quantum
}

// checkRoundingDirection checks the direction contract of one returned result
// against its exact value: the direction bit is sign(result − exact) by
// math/big.Rat comparison, at most one bit is set, a bit accompanies Inexact
// exactly, and the directed modes keep their side unless Overflow is
// reported. A call that returned an error without a value carries no bit.
// It reports whether a value was checked.
func checkRoundingDirection(t *testing.T, label string, exact *big.Rat, mode RoundingMode, got Decimal, conditions Conditions, err error) bool {
	t.Helper()
	if conditions&(Increased|Decreased) == Increased|Decreased {
		t.Fatalf("%s: both direction bits in %v", label, conditions)
	}
	if err != nil {
		if conditions&(Increased|Decreased) != 0 {
			t.Fatalf("%s: refusal %v carried direction %v", label, err, conditions)
		}
		return false
	}
	want := oracleDirection(directionValueRat(got), exact)
	if conditions&(Increased|Decreased) != want {
		t.Fatalf("%s: result %v exact %s conditions %v; want direction %v", label, got, exact.RatString(), conditions, want)
	}
	if (conditions&Inexact != 0) != (want != 0) {
		t.Fatalf("%s: Inexact and direction disagree in %v", label, conditions)
	}
	if conditions&Overflow != 0 {
		return true
	}
	switch mode {
	case TowardNegativeInfinity:
		if want == Increased {
			t.Fatalf("%s: TowardNegativeInfinity reported Increased without Overflow", label)
		}
	case TowardPositiveInfinity:
		if want == Decreased {
			t.Fatalf("%s: TowardPositiveInfinity reported Decreased without Overflow", label)
		}
	case TowardZero:
		if want == Decreased && exact.Sign() < 0 || want == Increased && exact.Sign() > 0 {
			t.Fatalf("%s: TowardZero moved away from zero (%v)", label, conditions)
		}
	}
	return true
}

// checkDirectedEnclosure checks the enclosure and tightness property
// for one pair of TowardNegativeInfinity/TowardPositiveInfinity results of
// the same exact value: unless either reports Overflow, lo and hi are the
// floor and ceiling of exact on the rounding grid 10^quantum, so lo ≤ exact
// ≤ hi and no grid value lies strictly between exact and either result; lo
// reports Decreased and hi Increased exactly when they differ from exact.
// It reports whether the pair was checked.
func checkDirectedEnclosure(t *testing.T, label string, exact *big.Rat, quantum int64, lo Decimal, loConditions Conditions, hi Decimal, hiConditions Conditions) bool {
	t.Helper()
	if (loConditions|hiConditions)&Overflow != 0 {
		return false
	}
	floor, ceil := directionGrid(exact, quantum)
	loValue, hiValue := directionValueRat(lo), directionValueRat(hi)
	if loValue.Cmp(floor) != 0 || hiValue.Cmp(ceil) != 0 {
		t.Fatalf("%s: exact %s grid 1E%d: lo %v hi %v; want %s and %s", label, exact.RatString(), quantum, lo, hi, floor.RatString(), ceil.RatString())
	}
	wantLo, wantHi := Conditions(0), Conditions(0)
	if floor.Cmp(exact) != 0 {
		wantLo = Decreased
	}
	if ceil.Cmp(exact) != 0 {
		wantHi = Increased
	}
	if loConditions&(Increased|Decreased) != wantLo || hiConditions&(Increased|Decreased) != wantHi {
		t.Fatalf("%s: exact %s: lo %v %v, hi %v %v", label, exact.RatString(), lo, loConditions, hi, hiConditions)
	}
	return true
}

// TestConditionsDirectionAccessor checks that Direction is
// +1 for Increased, −1 for Decreased and 0 for the empty set, for sets
// without a direction and for a caller-built set with both bits, which no
// operation emits.
func TestConditionsDirectionAccessor(t *testing.T) {
	for _, tc := range []struct {
		conditions Conditions
		want       int
	}{
		{0, 0},
		{Increased, 1},
		{Decreased, -1},
		{Inexact | Rounded | Increased, 1},
		{Overflow | Inexact | Rounded | Decreased, -1},
		{Inexact | Rounded, 0},
		{Rounded, 0},
		{Increased | Decreased, 0},
		{Inexact | Increased | Decreased, 0},
	} {
		if got := tc.conditions.Direction(); got != tc.want {
			t.Errorf("(%v).Direction() = %d, want %d", tc.conditions, got, tc.want)
		}
	}
}

// TestConditionsStringNamesDirection checks that the two
// result-direction attributes follow Underflow, keep every earlier bit
// value, and String names them in ascending bit order; bits beyond them are
// still undeclared.
func TestConditionsStringNamesDirection(t *testing.T) {
	if Increased != Underflow<<1 || Decreased != Underflow<<2 || Clamped != 1 || Underflow != 1<<12 {
		t.Fatalf("condition bit values moved: Clamped %#x Underflow %#x Increased %#x Decreased %#x", uint32(Clamped), uint32(Underflow), uint32(Increased), uint32(Decreased))
	}
	for _, tc := range []struct {
		conditions Conditions
		want       string
	}{
		{Increased, "Increased"},
		{Decreased, "Decreased"},
		{Inexact | Rounded | Decreased, "Inexact|Rounded|Decreased"},
		{Overflow | Inexact | Rounded | Increased, "Inexact|Overflow|Rounded|Increased"},
		{Subnormal | Underflow | Inexact | Rounded | Increased, "Inexact|Rounded|Subnormal|Underflow|Increased"},
		{Increased | Decreased, "Increased|Decreased"},
		{Decreased << 1, "Conditions(0x8000)"},
		{Decreased | Decreased<<1, "Decreased|Conditions(0x8000)"},
	} {
		if got := tc.conditions.String(); got != tc.want {
			t.Errorf("String(%#x) = %q, want %q", uint32(tc.conditions), got, tc.want)
		}
	}
}

// TestEvaluationErrorIdentities checks the supplied-limit versus physical
// refusal distinction and the one-outer-object error envelope.
func TestEvaluationErrorIdentities(t *testing.T) {
	for _, axis := range []EvaluationResource{EvaluationUnits, EvaluationCoefficientDigits} {
		err := evaluationFailure("PowDecimalWithContext", evaluationStatus{code: ErrInsufficientStorage, resource: axis, limit: 19})
		var limit *Error
		if !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &limit) || limit.Resource == 0 || limit.Op != "PowDecimalWithContext" || limit.Condition != InsufficientStorage || limit.Resource != axis || limit.Limit != 19 {
			t.Fatalf("wrong quota identity: %#v", err)
		}
		if errors.Is(err, ErrInexact) || err.Error() == "" {
			t.Fatalf("invalid quota text/condition: %v", err)
		}
	}
	err := evaluationFailure("LnWithContext", evaluationStatus{code: ErrInsufficientStorage})
	var op *Error
	if !errors.As(err, &op) || op.Resource != 0 || !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("physical refusal mislabeled: %v", err)
	}
	if evaluationFailure("Exp", evaluationStatus{}) != nil {
		t.Fatal("success status became error")
	}
	var sink error
	if n := testing.AllocsPerRun(100, func() {
		sink = evaluationFailure("ExpWithContext", evaluationStatus{code: ErrInsufficientStorage, resource: EvaluationUnits, limit: 1})
	}); n != 1 {
		t.Fatalf("outer quota error objects=%g", n)
	}
	if sink == nil {
		t.Fatal("missing failure")
	}
	for _, e := range []ErrorCode{ErrEvaluationBudgetRequired, ErrEvaluationBoundOverflow, 0} {
		if e.Error() == "" {
			t.Fatal("empty bound error text")
		}
	}
	var nilLimit *Error
	if nilLimit.Error() == "" || nilLimit.Unwrap() != nil {
		t.Fatal("nil limit error not safe")
	}
}
