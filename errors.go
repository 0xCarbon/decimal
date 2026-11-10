// SPDX-License-Identifier: Apache-2.0

package decimal

import "strconv"

// Conditions is the set of GDA-named conditions returned by an operation,
// plus the two result-direction attributes Increased and Decreased, which
// are not exceptional and cannot be trapped. Mask them with
// c &^ (Increased|Decreased) before reusing a returned set as traps.
type Conditions uint16

// The GDA conditions, in the bit order Conditions.String uses.
const (
	// Clamped is reserved: it can be selected as a trap, but no operation
	// reports it, because the library never clamps an exponent.
	Clamped Conditions = 1 << iota
	// ConversionSyntax identifies text or a source that is not a decimal
	// literal; it is the Condition of an error wrapping ErrConversionSyntax.
	ConversionSyntax
	// DivisionByZero identifies a nonzero dividend divided by zero, or the
	// logarithm of zero; it is the Condition of an ErrDivisionByZero error.
	DivisionByZero
	// DivisionImpossible identifies an integer quotient longer than a finite
	// context precision; it is the Condition of an ErrDivisionImpossible
	// error.
	DivisionImpossible
	// DivisionUndefined identifies 0/0; it is the Condition of an
	// ErrDivisionUndefined error.
	DivisionUndefined
	// Inexact reports that a rounding discarded digits that were not all
	// zero, so the result differs from the exact value. Exactly one of
	// Increased and Decreased accompanies it.
	Inexact
	// InsufficientStorage identifies a refusal for resources: a budget or
	// an addressability limit; it is the Condition of an
	// ErrInsufficientStorage error.
	InsufficientStorage
	// InvalidContext identifies an invalid Context configuration; it is the
	// Condition of an *Error.
	InvalidContext
	// InvalidOperation identifies an operand outside an operation's domain,
	// such as the square root of a negative value; it is the Condition of
	// an ErrInvalidOperation error.
	InvalidOperation
	// Overflow reports a result above the context's Emax, replaced by the
	// context's largest finite value. Binary64 conversion reports it for a
	// magnitude beyond MaxFloat64, replaced by MaxFloat64 or an infinity
	// according to the rounding mode.
	Overflow
	// Rounded reports that a rounding discarded digits, possibly all zero.
	Rounded
	// Subnormal reports a nonzero result below the context's Emin, rounded
	// at the subnormal quantum; binary64 conversion reports it for a
	// nonzero result below 2^-1022.
	Subnormal
	// Underflow reports a Subnormal result that is also Inexact, in context
	// arithmetic and in binary64 conversion alike.
	Underflow
	// Increased and Decreased are result-direction attributes, not
	// exceptional conditions: exactly one accompanies an emitted
	// Inexact and reports whether the returned value is greater or less than
	// the exact result. They are never trappable and never appear in an
	// error's Condition field. TowardNegativeInfinity never
	// reports Increased and TowardPositiveInfinity never reports Decreased
	// unless Overflow is also reported: guarded overflow substitutes the
	// finite largest value in every mode, which is then no finite bound.
	Increased
	// Decreased reports that the returned value is less than the exact
	// result; see Increased.
	Decreased
)

var conditionNames = [...]string{
	"Clamped", "ConversionSyntax", "DivisionByZero", "DivisionImpossible",
	"DivisionUndefined", "Inexact", "InsufficientStorage", "InvalidContext",
	"InvalidOperation", "Overflow", "Rounded", "Subnormal", "Underflow",
	"Increased", "Decreased",
}

// Direction returns +1 when the set reports Increased, −1 when it reports
// Decreased and 0 otherwise, including for a set with both bits, which no
// operation emits: the sign of the returned value minus the exact result.
func (c Conditions) Direction() int {
	switch c & (Increased | Decreased) {
	case Increased:
		return 1
	case Decreased:
		return -1
	}
	return 0
}

// roundingDirection is the value direction of an inexact rounding that did
// (up) or did not increase the magnitude of a value with the given sign.
func roundingDirection(up, negative bool) Conditions {
	if up != negative {
		return Increased
	}
	return Decreased
}

// String names the set conditions in ascending bit order, joined by "|".
// The empty set is "0"; undeclared bits are shown in hexadecimal.
func (c Conditions) String() string {
	if c == 0 {
		return "0"
	}
	var b []byte
	for i, name := range conditionNames {
		if c&(1<<i) != 0 {
			if len(b) > 0 {
				b = append(b, '|')
			}
			b = append(b, name...)
		}
	}
	if unknown := c &^ declaredConditions; unknown != 0 {
		if len(b) > 0 {
			b = append(b, '|')
		}
		b = append(b, "Conditions(0x"...)
		b = strconv.AppendUint(b, uint64(unknown), 16)
		b = append(b, ')')
	}
	return string(b)
}

// ErrorCode identifies a decimal failure without mutable package sentinels.
type ErrorCode uint8

// The error codes. An *Error wraps one for errors.Is; a trapped condition
// set matches the code of each trapped condition through Error.Is.
const (
	// ErrConversionSyntax: input that is not a decimal literal, or a source
	// that cannot be converted.
	ErrConversionSyntax ErrorCode = iota + 1
	// ErrExponentRange: a result or literal whose exponent does not fit
	// int32.
	ErrExponentRange
	// ErrInsufficientStorage: work refused by a budget or by an
	// addressability limit, before allocating.
	ErrInsufficientStorage
	// ErrInvalidContext: an invalid Context configuration.
	ErrInvalidContext
	// ErrInexact: a trapped Inexact condition, an Exact-mode or
	// non-terminating refusal, or a display or conversion that cannot be
	// exact.
	ErrInexact
	// ErrRounded: a trapped Rounded condition.
	ErrRounded
	// ErrSubnormal: a trapped Subnormal condition.
	ErrSubnormal
	// ErrOverflow: a trapped Overflow condition.
	ErrOverflow
	// ErrUnderflow: a trapped Underflow condition.
	ErrUnderflow
	// ErrInvalidOperation: an operand or argument outside the operation's
	// domain.
	ErrInvalidOperation
	// ErrNonIntegral: an integer conversion of a value with a nonzero
	// fraction.
	ErrNonIntegral
	// ErrIntegerRange: an integer conversion whose value does not fit the
	// target type or width.
	ErrIntegerRange
	// ErrDivisionByZero: a nonzero value divided by zero, or the logarithm
	// of zero.
	ErrDivisionByZero
	// ErrDivisionUndefined: zero divided by zero.
	ErrDivisionUndefined
	// ErrDivisionImpossible: an integer quotient longer than a finite
	// context precision.
	ErrDivisionImpossible
	// ErrEvaluationBudgetRequired: BoundEvaluation received no finite
	// positive unit quota. Bound-query failures are returned bare and do not
	// wrap ErrInsufficientStorage.
	ErrEvaluationBudgetRequired
	// ErrEvaluationBoundOverflow: the permitted-attempt bound cannot fit
	// uint64. The budget remains valid and may admit an easy call.
	ErrEvaluationBoundOverflow
)

// Error returns the code's message, prefixed "decimal: ".
func (c ErrorCode) Error() string { return "decimal: " + c.text() }

func (c ErrorCode) text() string {
	switch c {
	case ErrConversionSyntax:
		return "conversion syntax"
	case ErrExponentRange:
		return "exponent out of range"
	case ErrInsufficientStorage:
		return "insufficient storage"
	case ErrInvalidContext:
		return "invalid context"
	case ErrInexact:
		return "inexact"
	case ErrRounded:
		return "rounded"
	case ErrSubnormal:
		return "subnormal"
	case ErrOverflow:
		return "overflow"
	case ErrUnderflow:
		return "underflow"
	case ErrInvalidOperation:
		return "invalid operation"
	case ErrNonIntegral:
		return "nonintegral value"
	case ErrIntegerRange:
		return "integer out of range"
	case ErrDivisionByZero:
		return "division by zero"
	case ErrDivisionUndefined:
		return "division undefined"
	case ErrDivisionImpossible:
		return "division impossible"
	case ErrEvaluationBudgetRequired:
		return "evaluation bound requires a finite positive unit budget"
	case ErrEvaluationBoundOverflow:
		return "evaluation bound overflows uint64"
	default:
		return "unknown error code"
	}
}

// condition is the GDA condition a code's refusal reports.
func (c ErrorCode) condition() Conditions {
	switch c {
	case ErrConversionSyntax:
		return ConversionSyntax
	case ErrInsufficientStorage:
		return InsufficientStorage
	case ErrInvalidContext:
		return InvalidContext
	case ErrInvalidOperation:
		return InvalidOperation
	case ErrDivisionByZero:
		return DivisionByZero
	case ErrDivisionUndefined:
		return DivisionUndefined
	case ErrDivisionImpossible:
		return DivisionImpossible
	}
	return 0
}

// Error is every error an operation returns; the Estimate functions and
// BoundEvaluation return a bare ErrorCode instead. errors.Is matches its Code, or for a trapped
// condition set the code of each trapped condition, without allocating;
// errors.As(&e) with e *Error reads the details. The owning function defines its result on
// failure.
type Error struct {
	// Op names the exported function or method that failed. The text
	// encoders (MarshalText, AppendText, MarshalJSON and Value) report
	// the Text operation they share.
	Op string
	// Input is the complete input text of a parse failure, else empty.
	Input string
	// Remedy names the instruction or source that avoids the refusal, such
	// as a rounding target for a non-terminating quotient or the dynamic
	// type of an unsupported Scan source. It affects only the message.
	Remedy string
	// Limit is the supplied cap of the exhausted Resource.
	Limit uint64
	// Code is the cause; it is zero for a trapped condition set.
	Code ErrorCode
	// Resource names the exhausted quota of an elementary function; it is
	// zero otherwise.
	Resource EvaluationResource
	// Condition is the GDA condition of the cause, or the trapped set, or
	// Inexact for an Exact-mode or non-terminating refusal.
	Condition Conditions
}

// Error returns "decimal: Op: cause", followed by the remedy and the input
// when they are set. A trapped set reads "condition Inexact|Rounded".
func (e *Error) Error() string {
	if e == nil || e.Code == 0 && e.Condition == 0 {
		return "decimal: error"
	}
	text := "decimal: "
	if e.Op != "" {
		text += e.Op + ": "
	}
	if e.Code != 0 {
		text += e.Code.text()
	} else {
		text += "condition " + e.Condition.String()
	}
	if e.Remedy != "" {
		text += ": " + e.Remedy
	}
	if e.Input != "" {
		text += ": " + e.Input
	}
	return text
}

// Unwrap returns Code, or nil for a trapped condition set.
func (e *Error) Unwrap() error {
	if e == nil || e.Code == 0 {
		return nil
	}
	return e.Code
}

// trappedCodes maps the trappable result conditions to their codes.
var trappedCodes = [...]struct {
	condition Conditions
	code      ErrorCode
}{
	{Inexact, ErrInexact},
	{Overflow, ErrOverflow},
	{Rounded, ErrRounded},
	{Subnormal, ErrSubnormal},
	{Underflow, ErrUnderflow},
}

// Is reports whether a trapped condition set includes the condition of the
// ErrorCode target, so errors.Is matches each trapped condition's code
// (Inexact, Overflow, Rounded, Subnormal, Underflow) without allocating.
func (e *Error) Is(target error) bool {
	c, ok := target.(ErrorCode)
	if e == nil || !ok || e.Code != 0 {
		return false
	}
	for _, bit := range trappedCodes {
		if bit.code == c {
			return e.Condition&bit.condition != 0
		}
	}
	return false
}

// newError returns an *Error for code with the code's condition.
func newError(op string, code ErrorCode) *Error {
	return &Error{Op: op, Code: code, Condition: code.condition()}
}

// conditionError returns the *Error of a trapped condition set.
func conditionError(op string, trapped Conditions, remedy string) *Error {
	return &Error{Op: op, Condition: trapped, Remedy: remedy}
}

// EvaluationResource identifies the supplied quota exhausted by an adaptive
// call. It is not a numerical condition or a physical addressability limit.
type EvaluationResource uint8

const (
	// EvaluationUnits is the evaluation-unit quota, Budget.MaxWork.
	EvaluationUnits EvaluationResource = iota + 1
	// EvaluationCoefficientDigits is the result-digit quota,
	// Budget.MaxDigits.
	EvaluationCoefficientDigits
)
