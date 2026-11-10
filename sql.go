// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"database/sql/driver"
	"fmt"
	"math/big"
	"reflect"
)

// decimalDecomposer is the database/sql decimal decompose convention.
type decimalDecomposer interface {
	Decompose(buf []byte) (form byte, negative bool, coefficient []byte, exponent int32)
}

// Scan implements sql.Scanner. It accepts exactly: string and []byte text
// in the one decimal grammar, keeping the written scale (1.10 stays 1.10);
// every int and uint type (not uintptr), uint64 included, at exponent 0; float64 and
// float32 as their exact binary expansion (0.1 scans as
// 0.1000000000000000055511151231257827021181583404541015625: upstream
// float loss is reflected, not repaired); and any value with a Decompose
// method, whose coefficient and exponent transfer exactly. big.Int and
// *big.Int sources are exact at exponent 0. big.Rat and *big.Rat sources
// must terminate in decimal and use the largest exponent not above 0;
// they carry no column scale (11/10 becomes 1.1). Non-terminating rationals
// return an *Error that unwraps to ErrInexact: scan into a *big.Rat
// variable or any and use FromRatWithContext or FromRatToExponent instead.
// big.Float and *big.Float are refused by kind as an unsupported source with a
// remedy, including typed nils: choose the driver's decimal text mode or
// convert explicitly. Typed-nil integer and rational pointers are conversion
// syntax errors. Accepted sources are never retained or mutated and must
// not be mutated concurrently. Driver-specific types without Decompose need
// a caller-side wrapper; see ExampleNullDecimal_driverDecimal. SQL NULL is
// refused, because Decimal has no NULL state; scan nullable columns into
// NullDecimal. Non-finite text or forms, a nil-pointer decompose source
// (refused before it is called) and every other source kind are errors
// that unwrap to ErrConversionSyntax; text whose exponent leaves the int32
// domain unwraps to ErrExponentRange. The receiver changes only on success.
func (d *Decimal) Scan(src any) error {
	return d.scan(src, Budget{}, "Scan")
}

// ScanWithBudget is Scan with a Budget, for direct calls.
func (d *Decimal) ScanWithBudget(src any, budget Budget) error {
	return d.scan(src, budget, "ScanWithBudget")
}

func (d *Decimal) scan(src any, budget Budget, op string) error {
	if d == nil || src == nil {
		// A nil receiver, or SQL NULL into a value without a NULL state:
		// both are invalid operations on the destination.
		return newError(op, ErrInvalidOperation)
	}
	v, err := scanValue(src, budget, op)
	if err != nil {
		return err
	}
	*d = v
	return nil
}

// NullDecimal carries SQL NULL beside a Decimal. Scan of NULL sets Valid to
// false and clears Decimal; Value returns nil for an invalid value and the
// canonical text otherwise. NullDecimal deliberately has no Decompose or
// Compose method: a NULL is never encoded as a finite zero. To bind a
// nullable value through the decompose convention, pass SQLDecimal{d} when
// valid and nil otherwise.
type NullDecimal struct {
	// Decimal is the value when Valid is true, and Decimal{} otherwise.
	Decimal Decimal
	// Valid is false for SQL NULL.
	Valid bool
}

// Scan implements sql.Scanner with Decimal.Scan's source rules, plus SQL
// NULL. On error both fields are unchanged.
func (n *NullDecimal) Scan(src any) error {
	return n.scan(src, Budget{}, "Scan")
}

// ScanWithBudget is Scan with a Budget, for direct calls.
func (n *NullDecimal) ScanWithBudget(src any, budget Budget) error {
	return n.scan(src, budget, "ScanWithBudget")
}

func (n *NullDecimal) scan(src any, budget Budget, op string) error {
	if n == nil {
		return newError(op, ErrInvalidOperation)
	}
	if src == nil {
		*n = NullDecimal{}
		return nil
	}
	v, err := scanValue(src, budget, op)
	if err != nil {
		return err
	}
	*n = NullDecimal{Decimal: v, Valid: true}
	return nil
}

// Value implements driver.Valuer: nil when invalid, otherwise the
// Decimal's canonical text.
func (n NullDecimal) Value() (driver.Value, error) {
	if !n.Valid {
		return nil, nil
	}
	return n.Decimal.Value()
}

// scanValue classifies the source by its exact dynamic type and converts
// it under the budget.
func scanValue(src any, budget Budget, op string) (Decimal, error) {
	switch s := src.(type) {
	case big.Float:
		return scanBigFloatRefusal(op, false)
	case *big.Float:
		return scanBigFloatRefusal(op, true)
	case big.Int:
		return scanBigInt(&s, budget, op)
	case *big.Int:
		return scanBigInt(s, budget, op)
	case big.Rat:
		return scanBigRat(&s, budget, op)
	case *big.Rat:
		return scanBigRat(s, budget, op)
	case string:
		return scanText(s, budget, op)
	case []byte:
		return scanText(s, budget, op)
	case int64:
		return scanInteger(s < 0, int64Magnitude(s), budget, op)
	case float64:
		return scanFloat64(s, budget, op)
	case float32:
		return scanFloat64(float64(s), budget, op)
	case decimalDecomposer:
		return scanDecomposer(s, budget, op)
	default:
		if negative, magnitude, ok := integerSource(src); ok {
			return scanInteger(negative, magnitude, budget, op)
		}
		return Decimal{}, unsupportedSource(op, fmt.Sprintf("%T", src))
	}
}

// scanText charges the byte and work caps before scanning: a refusal keeps
// a string as its Input, which is immutable, and leaves Input empty for a
// []byte instead of copying it.
func scanText[T Literal](s T, budget Budget, op string) (Decimal, error) {
	n := uint64(len(s))
	if budget.MaxInputBytes != 0 && n > budget.MaxInputBytes || budget.MaxWork != 0 && n > budget.MaxWork {
		if text, ok := any(s).(string); ok {
			return Decimal{}, &Error{Op: op, Input: text, Code: ErrInsufficientStorage, Condition: InsufficientStorage}
		}
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	return parseWithBudget(s, textLimits{MaxDigits: budget.MaxDigits}, op)
}

// integerSource returns the sign and magnitude of a source of any Go
// integer kind; drivers deliver uint64 for unsigned BIGINT columns.
func integerSource(src any) (negative bool, magnitude uint64, ok bool) {
	var v int64
	switch s := src.(type) {
	case int64:
		v = s
	case int:
		v = int64(s)
	case int32:
		v = int64(s)
	case int16:
		v = int64(s)
	case int8:
		v = int64(s)
	case uint64:
		return false, s, true
	case uint:
		return false, uint64(s), true
	case uint32:
		return false, uint64(s), true
	case uint16:
		return false, uint64(s), true
	case uint8:
		return false, uint64(s), true
	default:
		return false, 0, false
	}
	return v < 0, int64Magnitude(v), true
}

// int64Magnitude is |v|, exact for MinInt64.
func int64Magnitude(v int64) uint64 {
	if v < 0 {
		return -uint64(v)
	}
	return uint64(v)
}

func scanInteger(negative bool, magnitude uint64, budget Budget, op string) (Decimal, error) {
	if !admitted(budget.MaxDigits, uint64(wordDigits(magnitude)), true) || !admitted(budget.MaxWork, 1, true) {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	return inlineDecimal(uint128{lo: magnitude}, 0, negative), nil
}

// scanFloat64 converts the exact binary expansion, charging the
// expansion's P·87 work before expanding and the expansion's exact digit
// count before publication allocates.
func scanFloat64(f float64, budget Budget, op string) (Decimal, error) {
	if float64Nonfinite(f) {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	negative, m, e := binary64Parts(f)
	if m == 0 {
		return Decimal{}, nil
	}
	if !admitted(budget.MaxWork, binary64Passes(e)*binary64Limbs, true) {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	var buf [binary64Limbs]uint32
	limbs, exponent := expandDyadic(&buf, m, e)
	if !admitted(budget.MaxDigits, limbsDigits(limbs), true) {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	return divPublish(divOutcome{r: limbs, exponent: exponent}, negative, 0, limits{}, op)
}

// scanDecomposer refuses a nil-pointer source before calling it, then
// decodes the tuple with Compose's engine under the byte, digit (the raw
// envelope U) and work (Compose's W) caps. The coefficient is never
// retained.
func scanDecomposer(s decimalDecomposer, budget Budget, op string) (Decimal, error) {
	if rv := reflect.ValueOf(s); rv.Kind() == reflect.Pointer && rv.IsNil() {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	form, negative, coefficient, exponent := s.Decompose(nil)
	if form != 0 {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	if !admitted(budget.MaxInputBytes, uint64(len(coefficient)), true) {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	var v Decimal
	limit := Budget{MaxInputDigits: budget.MaxDigits, MaxDigits: budget.MaxDigits, MaxWork: budget.MaxWork}
	if err := v.compose(form, negative, coefficient, exponent, limit, op); err != nil {
		return Decimal{}, err
	}
	return v, nil
}

// Binary floating-point conversion stays an explicit caller choice.
const scanBigFloatRemedy = "big.Float is binary floating point, not a decimal: read the column as decimal text (the driver's string mode; for gosnowflake, query without WithHigherPrecision), or scan into an any and convert the big.Float explicitly, for example with r, _ := f.Rat(nil); FromRatToExponent(r, -scale, mode)"
const scanRatRemedy = "non-terminating rational: Scan converts only exact values; scan into a *big.Rat variable (var r *big.Rat; rows.Scan(&r)) or an any, and round it with FromRatWithContext or FromRatToExponent"

func scanBigFloatRefusal(op string, pointer bool) (Decimal, error) {
	text := "unsupported source big.Float: " + scanBigFloatRemedy
	if pointer {
		text = "unsupported source *big.Float: " + scanBigFloatRemedy
	}
	return Decimal{}, &Error{Op: op, Code: ErrConversionSyntax, Condition: ConversionSyntax, Remedy: text}
}

// unsupportedSource refuses a Scan source kind outside the accepted union by
// its dynamic type; the value itself is never formatted.
func unsupportedSource(op, kind string) *Error {
	return &Error{Op: op, Code: ErrConversionSyntax, Condition: ConversionSyntax, Remedy: "unsupported source " + kind}
}

// scanBigIntBits validates metadata before the byte cap, distinguishing
// malformed top words from an unaddressable bit length.
func scanBigIntBits(x *big.Int) (uint64, ErrorCode) {
	if x == nil {
		return 0, ErrConversionSyntax
	}
	words := x.Bits()
	if len(words) != 0 && words[len(words)-1] == 0 {
		return 0, ErrConversionSyntax
	}
	n, ok := checkedBitLength(x)
	if !ok {
		return 0, ErrInsufficientStorage
	}
	return n, 0
}

func scanBigRatBits(r *big.Rat) (bn, bd uint64, code ErrorCode) {
	if r == nil || r.Denom().Sign() <= 0 {
		return 0, 0, ErrConversionSyntax
	}
	bn, cn := scanBigIntBits(r.Num())
	bd, cd := scanBigIntBits(r.Denom())
	// Classification of either component precedes physical admission.
	if cn == ErrConversionSyntax || cd == ErrConversionSyntax {
		return 0, 0, ErrConversionSyntax
	}
	if cn != 0 {
		return 0, 0, cn
	}
	return bn, bd, cd
}

func scanBigInt(x *big.Int, budget Budget, op string) (Decimal, error) {
	n, code := scanBigIntBits(x)
	if code != 0 {
		return Decimal{}, newError(op, code)
	}
	if !admitted(budget.MaxInputBytes, (n+7)/8, true) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	return fromBigInt(x, Budget{MaxInputDigits: budget.MaxDigits, MaxDigits: budget.MaxDigits, MaxWork: budget.MaxWork}, op)
}

func scanBigRat(r *big.Rat, budget Budget, op string) (Decimal, error) {
	bn, bd, code := scanBigRatBits(r)
	if code != 0 {
		return Decimal{}, newError(op, code)
	}
	if !admitted(budget.MaxInputBytes, (bn+7)/8+(bd+7)/8, true) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	ab := limits{MaxDigits: budget.MaxDigits, MaxWork: budget.MaxWork}
	v, _, err := fromRatContext(r, Context{}, ab, op) // precision 0: the exact quotient
	if e, ok := err.(*Error); ok && e.Code == 0 && e.Condition == Inexact {
		e.Remedy = scanRatRemedy
	}
	return v, err
}
