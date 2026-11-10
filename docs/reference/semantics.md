# Semantics reference

What a `Decimal` is and what its operations promise. The package
documentation (`go doc github.com/0xCarbon/decimal`) is the per-function
reference, and the [API guide](../api-guide.md) explains how the functions
are organized. Where this page and the package documentation disagree,
one of them has a bug; please report it.

## Value model

- **Finite only.** Every value is s·c·10^e: a sign, a
  nonnegative integer coefficient c of any length and an exponent e.
  There is no NaN, no infinity and no negative zero. Division by zero,
  0/0 and non-finite input are errors, never values. `Parse("NaN")`
  fails with `ErrConversionSyntax`.
- **One zero, at any exponent.** `-0.00` parses to zero at
  exponent −2; its `Sign()` is 0. The zero value `Decimal{}` is 0 at
  exponent 0 and is ready to use.
- **Exponent domain.** e is an int32. The coefficient is bounded
  only by memory and by the budgets below. A result whose stored exponent
  would leave int32 is an error (`ErrExponentRange`), never a wrapped
  exponent.
- **Immutable values.** Every method has a value
  receiver except the decoding methods (`Scan`, `Compose`, `UnmarshalText`,
  `UnmarshalJSON` and their budgeted forms), which replace their receiver
  only on success. Values
  are safe to share between goroutines without synchronization. There is
  no package-level state that changes a result.

## Cohorts: value versus scale

A decimal number has many representations: 1.1, 1.10 and 1.100 are one
number (a cohort) with exponents −1, −2 and −3. Decimal keeps the member
you constructed:

- **Construction preserves the scale.** `Parse("1.10")` stores 110×10⁻²;
  `Exponent()` returns −2 and `CoefficientDigits()` returns 3. Text keeps
  it: `String()` is `1.10`.
- **Arithmetic picks the ideal exponent.** An
  exact result is returned at its ideal exponent: the smaller operand
  exponent for `Add` and `Sub` (1.10 + 2.2 is 3.30), the sum of the
  exponents for `Mul` (1.10 × 2.0 is 2.200), and the dividend's minus the
  divisor's for `Div`, or the nearest exponent below it that holds the
  exact quotient (6.0 / 2 is 3.0, 1.00 / 4 is 0.25). Trailing zeros are
  neither added nor stripped silently.
- **Normalization is explicit.** `Reduce` returns the canonical
  member: trailing zeros stripped while the exponent stays in int32, zero
  at exponent 0. `Parse("1.2300").Reduce()` is 1.23 and `Parse("100")`
  reduces to 1E+2.
- **Equality ignores the scale.** `Equal`, `Compare` and
  `Hasher` compare numeric values: 1.10 equals 1.1 and `Compare` returns 0.
  `Compare` is a total order consistent with `Equal`.
- **Not comparable with `==`.** `Decimal` is
  deliberately non-comparable: `==` and `map[Decimal]V` do not compile,
  because two members of one cohort would otherwise be different keys. The
  [cookbook](../cookbook.md#keys-for-maps) shows the key recipes.

## Operations and exactness

Operations fall into four signature families, by how they
treat a result that is not exact:

| Family | Shape | Examples | Rounds? |
| --- | --- | --- | --- |
| Exact-or-error | `(Decimal, error)` | `Add`, `Sub`, `Mul`, `Div`, `Quo`, `Rem`, `Sqrt`, `Pow`, `Exp`, `FromRat` | never; an inexact result is refused |
| Instructed | `(Decimal, Conditions, error)` | `Quantize`, `RoundToPrecision`, `RoundToIntegral`, `RoundToMultiple`, `DivToExponent`, `ParseToExponent`, `FromFloat64ToExponent` | once, to the target and mode you pass |
| Context | `(Decimal, Conditions, error)` | every `…WithContext` method | once, under the `Context` you pass |
| Selection | `Decimal` | `Neg`, `Abs`, `Min`, `Max`, `Reduce` | never; no error is possible |

- **Nothing rounds implicitly.** `Add`, `Sub` and `Mul`
  return the exact result or a resource error. `Div` returns a
  terminating quotient exactly and refuses 1/3 with an `*Error`
  (trapped `Inexact`) whose message names the two remedies:
  `DivWithContext` or `DivToExponent`.
- **One rounding per call.** An instructed or context
  operation rounds the exact mathematical result once. `DivToExponent` is
  not `DivWithContext` followed by `Quantize`, which could round twice;
  `FMAWithContext` rounds x·y + z once.
- **Correctly rounded functions.**
  `SqrtWithContext`, `PowWithContext` and the elementary and
  trigonometric functions return the correctly rounded result in every
  mode. [Correct rounding](correct-rounding.md) lists each claim's
  argument and the tests that check it.
- **Documented deviation.** 0⁰ is 1 (the empty product); GDA's power
  returns NaN there.

## Rounding modes

`RoundingMode` has seven modes and `Exact`: `TiesToEven`,
`TiesAwayFromZero`, `TiesTowardZero`, `TowardZero`, `AwayFromZero`,
`TowardPositiveInfinity` and `TowardNegativeInfinity`. `Exact` refuses any
rounding that changes the value.

- **The zero mode is `TiesToEven`.** `Context{}`, every preset
  and a `Quantize` given an unset mode round a tie to the even digit.
  Monetary code names its mode, usually `TiesAwayFromZero`; see the
  [cookbook](../cookbook.md#rounding-money). The `RoundingMode`
  documentation has a table of every mode on positive and negative ties.
- **Names say what happens to ties.** Each mode name states its
  tie rule; names whose tie rule differs between libraries are not used.
- **Where to round is the application's decision.** The library
  never picks a rounding point for you.

## Contexts

A `Context` is an immutable value with five slots: precision,
rounding mode, optional exponent guards, a trap set and a resource
`Budget`. It is passed to each call; nothing global exists.
`WithPrecision`, `WithRounding`, `WithGuards`, `WithoutGuards`,
`WithTraps` and `WithBudget` derive a new context and keep the other
slots; the budget never changes a numeric result.

- **Precision.** Zero means exact, unlimited precision: `Context{}` makes
  `AddWithContext` behave as `Add`, and `DivWithContext` refuses 1/3 as
  `Div` does. A precision p > 0 rounds a result with more than p
  significant digits to p digits under the context's mode.
- **Guards.** `ExponentGuards{Emin, Emax}` bounds the adjusted
  exponent (e + digits − 1). Guards need a finite precision: `NewContext`
  rejects guards with precision 0 (`ErrInvalidContext`). A result above
  Emax reports `Overflow` and publishes the largest finite value of the
  context, a finite number in every mode, so the result stays in the value
  space. A nonzero result below Emin is rounded once at
  the quantum 10^Etiny, Etiny = Emin − (p − 1), and reports `Subnormal`
  (and `Underflow` when inexact): 0.00123 at p = 3, Emin = −2 is 0.0012.
- **Presets.** `Decimal32Context`, `Decimal64Context` and
  `Decimal128Context` return p = 7, 16 and 34 with the IEEE 754 exponent
  bounds (Emin −95, −383, −6143; Emax 96, 384, 6144), `TiesToEven` and no
  traps. They add no encoding, clamping or special values.
- **Traps.** `WithTraps` derives a context whose selected
  conditions become an error: a trapped condition returns an `*Error`
  whose `Condition` holds the trapped set and whose `Is` method makes
  `errors.Is` match the `ErrorCode` of each trapped condition (its
  `Unwrap` returns nil). The finite result of a trapped context operation remains available
  beside the error. `Increased` and `Decreased` cannot be trapped.

## Conditions

Instructed and context operations return a `Conditions` set: the GDA
condition names that apply, plus a direction. Conditions
are returned by each call; there is no flag register to clear.

- `Rounded`: digits were discarded (possibly zeros: 1.000 + 0 at p = 3 is
  1.00 with `Rounded` alone).
- `Inexact`: the discarded digits were not all zero, so the result differs
  from the exact value.
- `Increased` or `Decreased` accompanies every `Inexact`: the returned
  value is above or below the exact result.
  `Conditions.Direction()` returns +1 or −1. `TowardNegativeInfinity`
  never reports `Increased` and `TowardPositiveInfinity` never reports
  `Decreased`, except together with `Overflow`, whose substituted largest
  finite value is no bound.
- `Overflow`, `Underflow`, `Subnormal`: guard events (above).
- `ConversionSyntax`, `DivisionByZero`, `DivisionImpossible`,
  `DivisionUndefined`, `InsufficientStorage`, `InvalidContext`,
  `InvalidOperation`: the GDA names that identify refusals, carried in the
  `Condition` field of the error values below.
- `Clamped` is reserved: it can be selected as a trap but no operation
  reports it.

`Conditions.String()` joins the names with `|` in bit order, and the empty
set prints as `0`.

## Errors

Every failure is a returned error; only `MustParse` panics. Every
operation failure is one type, `*Error`, which wraps an `ErrorCode`
constant for `errors.Is`; the `Estimate` functions and
`BoundEvaluation` return a bare `ErrorCode` instead. Its message is
`decimal: Op: cause[: remedy][: input]`, and its fields are:

| Field | Holds |
| --- | --- |
| `Op` | the exported function or method that failed |
| `Input` | the complete input text of a parse failure, else empty |
| `Remedy` | the instruction that avoids the refusal (`DivWithContext` or `DivToExponent` for 1/3), or the dynamic type of an unsupported `Scan` source |
| `Limit` | the supplied cap of the exhausted `Resource` |
| `Code` | the `ErrorCode` cause that `Unwrap` returns; zero for a trapped condition set |
| `Resource` | the exhausted quota of an adaptive function, else zero |
| `Condition` | the GDA condition of the cause, the trapped set, or `Inexact` for an `Exact`-mode or non-terminating refusal |

An unsupported `Scan` source is `ErrConversionSyntax` with the source type
in `Remedy`. A trapped condition set has no single cause: its `Unwrap`
returns nil, and its `Is` method matches the code of each trapped
condition, so `errors.Is` never allocates.

The `ErrorCode` constants are `ErrConversionSyntax`, `ErrExponentRange`,
`ErrInsufficientStorage`, `ErrInvalidContext`, `ErrInexact`,
`ErrRounded`, `ErrSubnormal`, `ErrOverflow`, `ErrUnderflow`,
`ErrInvalidOperation`, `ErrNonIntegral`, `ErrIntegerRange`,
`ErrDivisionByZero`, `ErrDivisionUndefined`, `ErrDivisionImpossible`,
and the two `BoundEvaluation` codes `ErrEvaluationBudgetRequired` and
`ErrEvaluationBoundOverflow`.
Match with `errors.Is(err, decimal.ErrInexact)` and inspect with
`errors.As`. A domain error is never silent: a negative `Sqrt`
or `Ln` operand is `ErrInvalidOperation`, `Ln(0)` and a zero divisor are
`ErrDivisionByZero`, and 0/0 is `ErrDivisionUndefined`.

## Budgets

A coefficient can be arbitrarily long, so the work of most operations
depends on the input. Every such operation has a budgeted form. One `Budget` type has the axes
`MaxInputBytes`, `MaxInputDigits`, `MaxDigits`, `MaxOutputBytes` and
`MaxWork`; each family reads its own axes and ignores the rest. An
operation that rounds to a precision reads the budget from its context
(`Context.WithBudget`, which keeps `MaxInputBytes`, `MaxDigits` and
`MaxWork`; `Context{}.WithBudget(b)` is a budgeted exact call), and an
operation with a fixed target or no rounding takes it as a parameter:

| Family | Axes read | Budgeted entry points |
| --- | --- | --- |
| parsing | `MaxInputBytes`, `MaxDigits` | `ParseWithContext`, `ParseToExponentWithBudget`, `ParseJSONWithBudget` |
| arithmetic and rounding | `MaxDigits`, `MaxWork` | the context forms (`AddWithContext`, `QuantizeWithContext` …), `SumWithBudget`, `DivToExponentWithBudget`, `RoundToMultipleWithBudget`, `FromRatToExponentWithBudget`, `FromFloat64ToExponentWithBudget` |
| display | `MaxOutputBytes`, `MaxWork` | `FixedWithOptions`, `ScientificWithOptions` (budget in `DisplayOptions`), `EngineeringWithBudget`, the `Append` forms; `Text` takes a byte limit |
| scan | `MaxInputBytes`, `MaxDigits`, `MaxWork` | `ScanWithBudget` |
| integer conversion | `MaxInputDigits`, `MaxDigits`, `MaxWork` | `FromBigIntWithBudget`, `BigIntWithBudget`, `RatWithBudget`, `ComposeWithBudget`, `NewTwosComplementWithBudget` |
| adaptive functions | `MaxDigits`, `MaxWork` (evaluation units of a whole attempt) | the context forms (`ExpWithContext` …) |

- **A budget refuses before allocating and never changes a result.** A
  zero field means no caller limit on that axis. A refusal is an error
  with `ErrInsufficientStorage` identity.
- **Estimate before calling.** `EstimateAdd`, `EstimateMul`,
  `EstimateParse` and their peers take operand `Shape` values
  (`Decimal.Shape()`) or sizes and return a `Cost`: work units, digits,
  bytes and heap bytes. A rounding operation's estimator takes the
  `Context` it will run under (`EstimateAdd(x, y, ctx)`; precision 0 is
  the exact form). The budget `Cost.Budget()` builds always admits the
  call. The `Budget` documentation states each family's tariff.
- **Adaptive functions.** The context's `Budget` caps every phase of
  one `Exp`, `Ln`, `Log10`, `PowDecimal` or trigonometric attempt;
  `BoundEvaluation` turns it into a heap bound. There is no completion
  estimate, because the refinement a correctly rounded result needs is not
  known in advance ([correct rounding](correct-rounding.md)).
- **No cancellation.** Decimal does not take a `context.Context`; budgets
  bound work before a call instead.

## Text

- **One grammar.** Parsing accepts an optional sign, digits
  with at most one `.` (`5`, `5.`, `.5`) and an optional exponent `e` or
  `E`. Whitespace, `_`, commas and non-finite words are syntax errors. The
  same grammar serves `Parse`, `UnmarshalText`, `UnmarshalJSON` (numbers
  or strings) and `Scan` of text.
- **Canonical text.** `Text`, `String`, `MarshalText`,
  `MarshalJSON` and `Value` emit one canonical string per value and
  scale, GDA to-scientific-string: plain when the exponent is ≤ 0 and the
  adjusted exponent is ≥ −6 (`1.10`, `-0.005`), otherwise exponent form
  with an uppercase `E` and a signed exponent (`1.2E+4`, `1E-7`). Parsing
  the canonical text returns the same value and scale.
- **Display is separate.** `Fixed`, `Scientific`,
  `Engineering` and the `%v %s %f %e` verbs render for people, with
  explicit digits and rounding.

## Conversions

- **Integers and math/big.** `FromInt64`,
  `FromUint64`, `New` and `FromBigInt` are exact. `Int64`, `Uint64` and
  `BigInt` are exact or fail (`ErrNonIntegral`, `ErrIntegerRange`).
  `FromRat` is exact for a terminating rational and refuses 1/3;
  `FromRatWithContext` and `FromRatToExponent` round it once. `Rat` is
  exact.
- **float64.** A double is an exact binary
  rational. `FromFloat64Exact(0.1)` is
  0.1000000000000000055511151231257827021181583404541015625;
  `FromFloat64(0.1)` is 0.1, strconv's shortest round-trip digits.
  `FromFloat64ToExponent` and `FromFloat64WithContext` round the exact
  value once. `Float64` and `Float64Rounded` report exactness and
  direction, and `CompareFloat64` orders a decimal against a double
  without converting either one.
- **Integer minor units.** `New(1999, -2)` is 19.99; the
  [API guide](../api-guide.md#integer-minor-units) converts back.

The [interop guide](../interop.md) covers database/sql, SQL `DECIMAL(p,s)`
columns, JSON and binary coefficient lanes.
