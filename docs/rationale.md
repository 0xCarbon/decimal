# Design rationale

Why Decimal is built the way it is. Each section states a choice and the
alternatives it beat. What the library promises is in the
[semantics reference](reference/semantics.md); how to call it is in the
[API guide](api-guide.md).

## A finite value space

Every value is a sign, an unbounded integer coefficient and an int32
exponent. There is no NaN, no infinity and no negative zero: division by
zero, 0/0 and non-finite text are errors, never values.

- **Why not the GDA/IEEE specials.** They need a second exceptional channel
  beside error returns, and a NaN that flows onward hides the failure that
  made it. They also cannot be checked by the `math/big` rational oracle
  that anchors the test suite.
- **Why not a fixed-width decimal128.** A 34-digit ceiling is a semantic
  wall, and dropping the cohort would lose the scale that money and SQL
  columns carry.
- **Scale is part of the value's state.** `1.10` keeps exponent −2; nothing
  normalizes silently, and `Reduce` is the explicit way to drop trailing
  zeros.
- **Guards stay finite.** A context may set exponent guards; a result
  above the upper guard is the largest finite value of the context, and a
  result below the lower guard is rounded once at the Etiny quantum. Both
  are ordinary finite values.

## Representation: two bands, one value

`Decimal` holds the coefficient inline in two 64-bit words when it is
below 2^128, and otherwise in an immutable holder of base-10⁹ limbs. The
boundary is invisible: every operation has one meaning on both sides.

- **Why not a `math/big` carrier.** It allocates per operation, and
  pointer `==` splits equal values into different map keys. `math/big` is
  used at the boundaries (`big.Int`, `big.Rat`) and as the test oracle.
- **Why not a fixed 96-bit decimal (.NET, rust_decimal).** A hard
  coefficient wall of 28–29 digits turns ordinary growth into an error.
- **Why not DPD or BID.** The IEEE interchange encodings are a separable
  codec layer, not a carrier.
- **Non-comparable by construction.** `Decimal` cannot be used with `==`
  or as a map key: two members of one cohort would otherwise be different
  keys. Equality, ordering and hashing are methods (`Equal`, `Compare`,
  `Hasher`), and the [cookbook](cookbook.md#keys-for-maps) shows the key
  recipes.
- **Allocation follows size.** An operation on inline operands with an
  inline result allocates nothing; a larger result allocates its holder,
  and its limbs too beyond the holder's built-in ones. The benchmark suite
  pins every allocation class, including the operand-bound and
  `math/big`-bound ones.
- **Safe Go only.** No `unsafe`, no assembly, no cgo. A portable-SIMD digit
  scanner is built with `GOEXPERIMENT=simd`; its scalar twin (a plain
  build) defines the semantics, and both profiles pass the same suite with
  bit-identical results.

## Precision model: exact until told otherwise

Arithmetic is exact by default. `Add`, `Sub` and `Mul` return the exact
result; `Div` returns it when the quotient terminates and refuses
otherwise. A result that needs rounding needs an instruction: a target
exponent, a number of significant digits, or a `Context`.

- **Why not precision by default (GDA, decNumber, libmpdec, apd).** A
  default precision rounds silently, and callers inherit defaults they
  never chose, which differ between implementations of the same model.
- **Why not per-value SQL precision and scale.** The engines disagree, so
  there is no single SQL decimal semantics to adopt; SQL `DECIMAL(p,s)` is
  composed from a `Context` and `Quantize` instead (see the
  [interop guide](interop.md)).
- **Contexts are explicit, immutable values.** A context carries
  precision, rounding mode, optional exponent guards, traps and a budget.
  There is no package-level context and no global state that changes a
  result. The zero `Context{}` is exact.
- **The scale of an exact result is predictable.** Each operation has a
  ideal exponent: the smaller one for addition, the sum for
  multiplication, the difference for division. Addition and
  multiplication return the exact result at it; exact division returns
  the quotient at the exponent closest to it that holds the exact value,
  so 1/4 is 0.25. Trailing zeros are neither padded nor stripped past the
  ideal.

## A named rounding catalog

Seven rounding modes plus `Exact`: `TiesToEven` (the zero value and the
default), `TiesAwayFromZero`, `TiesTowardZero`, `TowardZero`,
`AwayFromZero`, `TowardPositiveInfinity` and `TowardNegativeInfinity`.
`Exact` refuses any rounding that would change the value; dropping only
zeros is allowed and reported as `Rounded`.

- **Names say what happens at a tie.** The two traditional names that
  pair "half" with "up" or "down" are ambiguous, notably for negative
  operands, so no identifier uses them and no document uses them
  unqualified. Money that must round ties away from zero selects
  `TiesAwayFromZero` explicitly; the cookbook shows it.
- **Two targets, no third.** A rounding names either an exponent or a
  number of significant digits. Rounding to a multiple, such as a cash
  increment, is an operation (`RoundToMultiple`), not a mode.
- **Placement is the application's.** Whether to round per line or per
  invoice is policy; the library has no placement API.
- **Every rounding reports its direction.** The returned `Conditions`
  carry `Inexact` and `Rounded`, and say whether the result is above or
  below the exact value.

## Errors and conditions

No library operation panics on any input; `MustParse`, for literals, is
the named exception. Failures are typed errors that wrap an `ErrorCode`
for `errors.Is`. Events that do not abort, such as `Inexact` and
`Rounded`, are returned with the result; nothing accumulates in a flag
register or in package state. A context's traps turn a chosen condition
into an error, and domain violations are never silent.

- **Why not panics.** One missed input class crashes a service. Several
  existing Go decimal libraries panic on inputs such as a zero divisor or
  an oversized exponent.
- **Why not GDA status flags.** Sticky flags need mutable shared state,
  which contradicts immutable values and concurrent use.

## Budgets: refuse before allocating

Operations whose result or working storage can outgrow their inputs
have budgeted forms (for text, `Text` with a byte limit beside `String`).
A budget caps the digits and work units a call may use; size arithmetic,
addressability and the budget are checked before anything is allocated,
and a refusal returns `ErrInsufficientStorage`. A zero budget field
means no caller quota, not a global cap.

- **Why budgets are per call.** A global cap would be hidden state. The
  budget travels in the call's `Context` for operations that round to a
  precision, because `Context{}` already means exact and a second budgeted
  form per operation would only default an argument; it never changes a
  numeric result. Operations with a fixed target or no rounding take it as
  a parameter.
- **One budget type.** `Budget` names the axes of `Cost`
  (`MaxInputBytes`, `MaxInputDigits`, `MaxDigits`, `MaxOutputBytes`,
  `MaxWork`); each family reads its own axes and ignores the rest, and
  `Cost.Budget()` builds one that admits the estimated call.
- **Why the budget is predictable.** `Shape` and the `Estimate` functions
  compute a call's `Cost` from operand shapes before the call, and a
  budget built from that cost always admits it.
- **Why finite-precision calls stay bounded.** Their work does not grow
  with quantities the result does not need: context `Add` and `Sub`
  reduce an operand that lies wholly below the rounding position to one
  sticky digit, so neither the work nor the budget charge depends on the
  exponent gap.
- **Adaptive evaluation charges its own units.** The adaptive functions
  (`Exp`, `Ln`, `Log10`, `PowDecimal` and the trigonometric and hyperbolic
  functions) read `MaxDigits` and `MaxWork` from the context's
  `Budget` in evaluation units charged before each stage.

## Correct rounding through certified enclosures

`Decimal.Sqrt`, `Decimal.Pow`, `Decimal.Exp`, `Decimal.Ln`,
`Decimal.Log10`, `Decimal.PowDecimal` and the trigonometric and hyperbolic
functions are correctly rounded in every mode under a finite context: the
exact result, rounded once. A square root is decided exactly from the
integer root and its remainder. An integer power is bracketed between
powers truncated down and up at a working width that doubles until the
bracket decides the rounding; at the bracket's bound the exact path
decides. The other functions compute directed lower and upper bounds with
analytic tails, raise the working precision until the bounds decide the
rounding, and decide exact results separately. Each claim, with its
argument, checker test and named oracle cases, is listed in the
[correct-rounding reference](reference/correct-rounding.md).

- **Why not an error bound.** A result that may be off by a unit in the
  last place makes the rounding mode meaningless, so no function takes
  that license.
- **Why not a maximum working precision.** It bounds neither the
  preparatory work nor the constants, reductions and retries. A separate
  quota, the evaluation budget, bounds the attempt honestly: the call
  succeeds or refuses within it.
- **Why the bare forms refuse.** Without a context there is no precision
  to round to, so `Exp`, `Sqrt` and the rest return the exact value or an
  error.

## API shape

- **Immutable values with value receivers.** Every arithmetic method
  returns a new value, and values are safe to share between goroutines.
  The decoding methods (`Scan`, `UnmarshalText` and peers) replace their
  receiver only on success.
- **The signature tells you whether a call can round.** Operations fall
  into four families: selections that cannot grow or fail (`Neg`,
  `Max`), exact-or-error operations that return `(Decimal, error)`
  (`Add`, `Div`), and instructed and context operations that return
  `(Decimal, Conditions, error)` (`Quantize`; `AddWithContext`). No bare
  form rounds silently: bare arithmetic returns the exact result or an
  error, and the bare conversions that must round (`Float64`, the `Fixed`
  display) document the rounding, `Float64` also reporting it.
- **Budgets travel with the call.** A rounding operation has two forms,
  the bare exact `X` and `XWithContext`, whose context carries the budget
  (`Context{}.WithBudget(b)` is the budgeted exact call); target-exponent
  and non-rounding operations have one `…WithBudget` form. Text takes a
  byte limit (`Text`), display takes its budget in options, and JSON input
  has `ParseJSONWithBudget`.
- **A usable zero value.** `var d decimal.Decimal` is 0.
- **Why not a pointer carrier with a separate context (apd) or `math/big`
  style receivers.** Mutable receivers bring aliasing hazards back.
- **No iterators.** The API has no `iter.Seq` surfaces: a single-pass
  sequence cannot keep `SumWithBudget`'s refusal before allocation.

## Interoperation at the boundary

`Value` sends canonical text to `database/sql`; `Scan` accepts text,
integers, the exact value of a `float64` and exact `math/big` sources; JSON
is a bare number on output and a number or string on input, never through
a `float64`. Engine-specific rules (division scale, assignment rounding)
stay with the caller, composed from `Context` and `Quantize`; there are no
engine profiles. The [interop guide](interop.md) has the driver matrix.

## Scope and compatibility

One package, `github.com/0xCarbon/decimal`, importing only the standard
library and building with `CGO_ENABLED=0` on every target. Money logic,
rational or symbolic computation, binary floating-point emulation, locale
services and GPU work are non-goals.

Version 1 is feature-complete: later releases fix bugs and improve
performance. Patch releases keep the observable contract (values,
cohorts, conditions, error identities, budget charges and the
serializations) except for security fixes, conformance bug fixes,
clarifications of the specification and previously unspecified behavior,
each with a failing test and a labeled entry in the
[changelog](../CHANGELOG.md). A fix that needs a new exported identifier
ships as a minor release, and a fix that would need an incompatible API
is declined and documented.

There is no migration guide from other decimal libraries; the
documentation describes only Decimal's own semantics.

## How the claims are checked

Correctness comes from sources independent of the code under test: a
`math/big` rational differential (`tools/oracle`), the General Decimal
Arithmetic decTest corpus with a manifest that classifies every excluded
case (`make conformance`), property laws, fuzz targets with committed
seed corpora, and hand-derived vectors. Performance changes are measured
with interleaved A/B runs at public entry points, compared with
`tools/benchcmp`; CI timings are not used. See
[CONTRIBUTING.md](../CONTRIBUTING.md).
