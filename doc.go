// SPDX-License-Identifier: Apache-2.0

// Package decimal provides exact, immutable, finite decimal numbers with
// arbitrary-size coefficients and int32 base-ten exponents, implemented in
// pure Go with no dependencies outside the standard library.
//
// A [Decimal] is a coefficient and an exponent: 1.10 is 110×10⁻² and stays
// distinct from 1.1 (11×10⁻¹) in text and accessors, while [Decimal.Equal],
// [Decimal.Compare] and [Hasher] use numeric equality across such cohorts.
// Values below 2¹²⁸ are stored inline without allocation; larger
// coefficients use immutable base-10⁹ limbs that copies share safely. An
// operation whose operands and result are inline allocates nothing; one
// whose operands and result stay within 81 digits (every product or sum of
// two 38-digit values) allocates at most once, and a longer result at least
// twice (division beyond 48 limbs also allocates its working buffer). The
// zero value is 0. The value space is finite: there are no NaNs,
// infinities or negative zero.
//
// # Construction and text
//
// [Parse], [MustParse], [New], [FromInt64], [FromUint64] and [FromBigInt]
// preserve the constructed coefficient and exponent. [Decimal.Text] and
// [Decimal.String] emit canonical text for that cohort, [Decimal.AppendText]
// appends it without allocating, and [Decimal.Reduce] makes normalization
// explicit. [Decimal.Exponent] and [Decimal.CoefficientDigits] report the
// stored scale.
//
// # Arithmetic
//
// [Decimal.Add], [Decimal.Sub] and [Decimal.Mul] are exact and never round:
// they return the exact result at the ideal exponent or an error.
// Rounding is always explicit, through a [Context] (precision, a
// [RoundingMode], optional exponent guards and traps) in the WithContext
// forms, or through [Decimal.Quantize] and [Decimal.RoundToIntegral]. Every
// context operation reports the GDA [Conditions] it raised; trapped
// conditions return an [*Error]. Every inexact rounding also reports
// [Increased] or [Decreased], the side of the exact value its result lies
// on ([Conditions.Direction]); these two are never trappable. The zero
// RoundingMode is [TiesToEven], and [Exact] refuses any value-changing round.
// Monetary code should name its mode, usually [TiesAwayFromZero]; the
// [RoundingMode] documentation has a worked table of every mode, and
// docs/cookbook.md collects the recipes.
//
// [TowardNegativeInfinity] never reports Increased and
// [TowardPositiveInfinity] never reports Decreased, so the two bracket the
// exact value, unless Overflow is also reported: a guarded overflow
// substitutes the finite largest value in every mode (for example
// TowardPositiveInfinity can return it with Decreased|Overflow), and such a
// result is no finite bound.
//
// [Decimal.Div] returns a terminating quotient exactly (1/4 is 0.25) and
// refuses a non-terminating one such as 1/3 with a remedy instead of
// choosing a scale. [Decimal.DivWithContext] rounds the quotient once to the
// context precision; [Decimal.DivToExponent] rounds it once to a fixed
// exponent, the shape of SQL DECIMAL division and AVG. A zero divisor
// returns [ErrDivisionByZero], or [ErrDivisionUndefined] for 0/0.
//
// [Decimal.Quo] returns the truncated integer quotient at exponent 0, and
// [Decimal.Rem] and [Decimal.RemNear] the exact remainders x − q·y and
// x − n·y (n nearest, ties to even) at the smaller operand exponent: 10.5
// Rem 3 is 1.5 and 3 Rem 0.29 is 0.10. They never round; a finite context
// precision refuses a quotient longer than p with [ErrDivisionImpossible].
// A remainder never materializes the quotient, so 1E+2147483647 Rem 7 costs
// a few hundred limb operations.
//
// Rationals follow the same policy. [FromRat] converts a terminating
// *big.Rat exactly (3/40 is 0.075) and refuses 1/3 with the same remedy;
// [FromRatWithContext] and [FromRatToExponent] round it once, and
// [Decimal.Rat] returns the value as an exact *big.Rat in lowest terms.
//
// Doubles are exact binary rationals. [FromFloat64Exact] expands one exactly
// (0.1 is 0.1000000000000000055511151231257827021181583404541015625), while
// [FromFloat64] keeps strconv's shortest round-trip digits (0.1).
// [FromFloat64ToExponent] and [FromFloat64WithContext] round the exact value
// once from a stack expansion, without heap allocation. [Decimal.Float64] and
// [Decimal.Float64Rounded] return the double selected by a mode, together
// with Conditions that report exactness, direction, and IEEE 754 overflow
// and underflow, so the floor and ceiling bracket the decimal.
// [Decimal.CompareFloat64] orders a decimal against a double without
// converting either one. Their work does not grow with the exponent: at
// most one exact comparison, and only when a rounding boundary lies within
// 2^−59 of the value, relative to it.
//
// Rounding has two explicit targets and never happens implicitly.
// [Decimal.Quantize] rounds to a stored exponent and [Decimal.RoundToPrecision]
// to a number of significant digits, each once under a supplied mode.
// [Decimal.RoundToMultiple] rounds to a multiple such as a cash increment
// (2.525 to 0.05 is 2.50 under TiesToEven), deciding on the exact quotient so
// it never double-rounds.
//
// [Decimal.FMAWithContext] rounds the exact x·y + z once, so it can differ
// from MulWithContext then AddWithContext, which round twice; with Context{}
// it returns the exact sum, as Mul then Add would.
//
// [Decimal.Sqrt] returns an exact root or refuses, as Div does for a
// non-terminating quotient; [Decimal.SqrtWithContext] rounds the root once,
// correctly in every mode, deciding ties from the exact remainder
// (docs/reference/correct-rounding.md).
//
// [Decimal.Pow] takes an int32 exponent and returns the exact power, the
// repeated-multiplication cohort (1.10² is 1.2100), or refuses a
// non-terminating reciprocal; [Decimal.PowWithContext] rounds x^n once,
// correctly in every mode (docs/reference/correct-rounding.md). 0⁰ is 1,
// the empty product, where GDA's power gives NaN (a documented deviation).
//
// [Decimal.Exp], [Decimal.Ln], [Decimal.Log10] and [Decimal.PowDecimal]
// (a Decimal exponent) are correctly rounded: their context forms
// round once, correctly in every mode (docs/reference/correct-rounding.md):
// the value is enclosed between certified directed bounds at a working
// precision that doubles until the bounds prove the rounding, with no
// guard-digit guess or iteration cap.
// Mathematical exactness alone decides Inexact: Exp(0) is 1, Ln(1) is 0,
// Log10(1000) is 3 and 4^0.5 is exactly 2, and an exact tie such as
// 2.25 = (81/16)^0.5 at two digits rounds as a tie. The bare forms return
// exact values or refuse as Div does. A negative Ln or Log10 operand, and
// a negative base with a noninteger exponent, are invalid; zero is
// ErrDivisionByZero. Their [Budget] bounds a whole attempt,
// success or refusal, and [BoundEvaluation] turns it into a heap bound.
//
// The trigonometric and hyperbolic functions ([Decimal.Sin], [Decimal.Cos],
// [Decimal.Tan], [Decimal.Asin], [Decimal.Acos], [Decimal.Atan],
// [Decimal.Atan2], [Decimal.Sinh], [Decimal.Cosh], [Decimal.Tanh],
// [Decimal.Asinh], [Decimal.Acosh], [Decimal.Atanh]) use the same
// machinery, in radians: exact at their zero or one
// arguments, correctly rounded in every mode otherwise
// (docs/reference/correct-rounding.md). Reducing a huge argument modulo π/2
// needs π to about as many digits as the argument's exponent; that work is
// charged, so a finite budget refuses it first.
//
// Each correctly rounded operation's argument, the test that checks its
// reduction or enclosure, and its validating named cases are listed in
// docs/reference/correct-rounding.md.
//
// [ParseToExponent] and [ParseWithContext] round a literal once while
// parsing it, the shape of SQL CAST(text AS DECIMAL(p,s)): only the
// result's digits are stored, so a long literal rounded to a short result
// allocates nothing, and an exponent far below int32 rounds by value
// (1e-99999999999 at exponent −2 is 0.00). The parse family is generic, so
// a string or a []byte is parsed in place.
//
// # Resource budgets
//
// Decimal coefficients can grow without bound, so every operation whose
// cost depends on its inputs takes a [Budget]. An operation that rounds to a
// precision reads it from its [Context] ([Context.WithBudget]; with
// Context{} the computation stays exact), and an operation with an explicit
// target or no rounding takes it as a parameter ([Decimal.DivToExponentWithBudget],
// [ParseJSONWithBudget], [Decimal.FixedWithOptions] and so on). A budget
// only refuses work before allocating; it never changes a result. Zero
// fields mean no caller limit.
//
// To charge its own meter before calling, a caller asks an estimator:
// [EstimateMul], [EstimateDiv], [EstimateFromRat],
// [EstimateParse] and their peers take operand [Shape] values (from
// [Decimal.Shape]) or sizes and return a [Cost]: the work units, digits,
// bytes and heap allocation the call can consume, without allocating. A
// budget built from a Cost (for example [Cost.Budget]) always
// admits the call, and within a family time is affine in charged units, so
// a work cap bounds latency. The adaptive functions have no completion
// estimate: their Budget caps evaluation units shared by every
// phase of one attempt, and [BoundEvaluation] bounds its cumulative heap.
//
// # Display and interoperation
//
// [Decimal.Fixed], [Decimal.Scientific] and [Decimal.Engineering] render
// with explicit digits and rounding; [Decimal.Format] supports the %v, %s,
// %f and %e verbs; %+v is %v and %#v is decimal.MustParse("text"). Decimal implements [encoding.TextMarshaler],
// [encoding.TextUnmarshaler], [encoding.TextAppender], [json.Marshaler],
// [json.Unmarshaler] and [driver.Valuer]. [NewInt128],
// [Decimal.CoefficientInt128], [NewTwosComplement] and
// [Decimal.AppendTwosComplement] exchange the exact coefficient with
// 128-bit storage lanes and Parquet or Arrow two's-complement bytes, the
// exponent carried separately. With database/sql, a Decimal binds as
// canonical text and [Decimal.Scan] reads text, every int and uint type,
// float64 and float32 (as their exact binary value) and any engine's exact decimal through the decompose
// convention; [NullDecimal] carries SQL NULL. [SQLDecimal] opts a value
// into decompose binding for drivers that type parameters by value. JSON
// emits bare numbers and accepts numbers or strings. [Decimal.Int64],
// [Decimal.Uint64] and [Decimal.BigInt] convert exactly or fail;
// [FromBigIntWithBudget] and [Decimal.BigIntWithBudget] bound the work with
// a [Budget].
//
// # Equality and keys
//
// Decimal is deliberately not comparable: == and map[Decimal]V do not
// compile, because two cohorts of one number would otherwise differ. Use
// [Decimal.Equal], a text key from d.Reduce().Text(0), or [Hasher] with a
// caller-owned [maphash.Hash] for hash tables.
//
// # Errors
//
// Every operation failure is an [*Error]: [errors.Is] matches its
// [ErrorCode], or for a trapped condition set the code of each trapped
// condition; the Estimate functions and [BoundEvaluation] return a bare
// ErrorCode. An Error's Op names the exported function (Text for every
// text encoder), Condition the GDA condition, Input the text of a
// parse failure, Remedy the instruction that avoids a refusal, and Resource
// and Limit an exhausted elementary-function quota.
// Values are immutable and safe for concurrent use.
//
// # Documentation
//
// The repository's docs directory holds the rest of the documentation set:
// docs/reference/semantics.md (the value model, cohorts, contexts,
// conditions, errors and budgets),
// docs/api-guide.md (how the API is organized and which call fits a task),
// docs/cookbook.md (recipes, including map keys that span Decimal and
// float64), docs/interop.md (database/sql, SQL DECIMAL(p,s) columns, JSON
// and binary lanes), docs/reference/correct-rounding.md (the correctly
// rounded operations and how each is verified) and docs/rationale.md (why
// the design is what it is). Their Go
// examples are the runnable examples of this package.
package decimal

import (
	"database/sql"
	"database/sql/driver"
	"encoding"
	"encoding/json"
	"hash/maphash"
)

var (
	_ encoding.TextMarshaler   = Decimal{}
	_ encoding.TextAppender    = Decimal{}
	_ encoding.TextUnmarshaler = (*Decimal)(nil)
	_ json.Marshaler           = Decimal{}
	_ json.Unmarshaler         = (*Decimal)(nil)
	_ driver.Valuer            = Decimal{}
	_ driver.Valuer            = NullDecimal{}
	_ sql.Scanner              = (*Decimal)(nil)
	_ sql.Scanner              = (*NullDecimal)(nil)
	_ maphash.Hasher[Decimal]  = Hasher{}
)
