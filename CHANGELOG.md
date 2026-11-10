# Changelog

All notable changes to this project are documented here. The format is
based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the
project follows [Semantic Versioning](https://semver.org/).

## [Unreleased]

## [1.0.0] - 2026-11-10

Initial public release.

### Added

- `Decimal`: immutable, finite decimal values with an arbitrary-size
  coefficient and an int32 exponent, stored inline below 2^128. Values keep
  their scale (cohort); `Equal`, `Compare` and `Hasher` compare numerically.
- Exact arithmetic: `Add`, `Sub`, `Mul`, `Sum`, `Div` (exact or refused),
  `Quo`, `Rem`, `RemNear`, `Neg`, `Abs`, `Min`, `Max`, `Reduce`.
- Contexts with precision, seven rounding modes plus `Exact`, exponent
  guards, traps and a resource budget; `Decimal32Context`,
  `Decimal64Context` and `Decimal128Context`. Every rounding operation has
  a `…WithContext` form that rounds once and returns `Conditions`
  including the rounding direction.
- Instructed rounding: `Quantize`, `RoundToPrecision`, `RoundToIntegral`,
  `RoundToMultiple`, `DivToExponent`, `ParseToExponent`,
  `FromRatToExponent`, `FromFloat64ToExponent`; `FMAWithContext`.
- Correctly rounded `Sqrt`, `Pow`, `Exp`, `Ln`, `Log10`, `PowDecimal` and
  the trigonometric and hyperbolic functions, by certified enclosures.
- Resource budgets (`Budget`) for every input-size-dependent operation,
  checked before allocating, with `Shape`, `Cost` and `Estimate…`
  functions and `BoundEvaluation`.
- Text: one parse grammar for `string` and `[]byte`, canonical text that
  round-trips, `Fixed`, `Scientific`, `Engineering` and `fmt` verbs.
- Interoperation: `encoding.TextMarshaler`/`TextUnmarshaler`/
  `TextAppender`, JSON, `database/sql` (`Value`, `Scan`, `NullDecimal`,
  `SQLDecimal`), `int64`/`uint64`, `big.Int`, `big.Rat`, 128-bit and
  two's-complement coefficients, and exact `float64` conversion and
  comparison.
- One error type, `*Error`, with `ErrorCode` causes for `errors.Is`.

[Unreleased]: https://github.com/0xCarbon/decimal/compare/v1.0.0...HEAD
[1.0.0]: https://github.com/0xCarbon/decimal/releases/tag/v1.0.0
