# Decimal

[![CI](https://github.com/0xCarbon/decimal/actions/workflows/ci.yml/badge.svg)](https://github.com/0xCarbon/decimal/actions/workflows/ci.yml)
[![Go Reference](https://pkg.go.dev/badge/github.com/0xCarbon/decimal.svg)](https://pkg.go.dev/github.com/0xCarbon/decimal)

Exact, arbitrary-precision decimal arithmetic for Go, in pure Go with no
dependencies outside the standard library.

Go has no decimal type. Binary floating point cannot represent `0.1`, and
the systems Go programs talk to (SQL `DECIMAL` columns, JSON, financial
protocols) are decimal. `decimal` provides immutable, finite decimal values
whose semantics follow the General Decimal Arithmetic model and IEEE 754
decimal rounding:

- **Exact by default.** `Add`, `Sub` and `Mul` never round; `Div` returns a
  terminating quotient exactly and otherwise refuses. Rounding happens
  only where the code asks for it, once, under a named mode, and every
  rounding reports what it did.
- **No panics on input.** Every failure is a returned `*Error`; only
  `MustParse`, meant for literals, panics.
- **Resource-bounded.** Coefficients are unbounded, so every operation
  whose work depends on input size has a budgeted form that refuses before
  allocating. Untrusted text, JSON and database values cannot make a call
  do unbounded work.
- **Allocation-disciplined.** Values below 2^128 are stored inline:
  arithmetic, parsing and formatting into a caller's buffer (`AppendText`,
  `AppendFixed`, …) allocate nothing on them; the string-returning forms
  allocate only their result.
- **Portable.** `CGO_ENABLED=0`, no `unsafe`, no assembly. Building with
  `GOEXPERIMENT=simd` adds a portable-SIMD digit scanner for `[]byte`
  input; both builds pass the same suite, and results are bit-identical on
  every platform, including 386, arm64 and js/wasm.

## Install

```sh
go get github.com/0xCarbon/decimal
```

Requires Go 1.27.1 or newer.

## Quick start

```go
package main

import (
	"fmt"

	"github.com/0xCarbon/decimal"
)

func main() {
	price := decimal.MustParse("19.99")
	quantity := decimal.FromInt64(3)
	subtotal, err := price.Mul(quantity) // exact: 59.97
	if err != nil {
		panic(err)
	}
	rate := decimal.MustParse("0.0825")
	tax, err := subtotal.Mul(rate) // exact: 4.947525
	if err != nil {
		panic(err)
	}
	tax, _, err = tax.Quantize(-2, decimal.TiesAwayFromZero) // round to cents
	if err != nil {
		panic(err)
	}
	total, err := subtotal.Add(tax)
	if err != nil {
		panic(err)
	}
	fmt.Println(subtotal, tax, total) // 59.97 4.95 64.92
}
```

Rounding with a context, and reading what the rounding did:

```go
ctx := decimal.Decimal64Context() // 16 digits, TiesToEven
q, conditions, err := decimal.MustParse("1").DivWithContext(decimal.MustParse("3"), ctx)
fmt.Println(q, conditions, err) // 0.3333333333333333 Inexact|Rounded|Decreased <nil>

_, err = decimal.MustParse("1").Div(decimal.MustParse("3"))
fmt.Println(errors.Is(err, decimal.ErrInexact)) // true: 1/3 does not terminate
```

More runnable examples are in [example_test.go](example_test.go) and on
[pkg.go.dev](https://pkg.go.dev/github.com/0xCarbon/decimal).

## Features

- **Values keep their scale.** A `Decimal` is a coefficient and an int32
  exponent. `1.10` and `1.1` are equal numbers (`Equal`, `Compare`,
  `Hasher`) but keep their own text and `Exponent()`. `Reduce` normalizes
  explicitly. `Decimal` is deliberately not comparable with `==`, so two
  spellings of one number can never become two map keys by accident.
- **Seven rounding modes plus `Exact`.** `TiesToEven` (the zero value),
  `TiesAwayFromZero`, `TiesTowardZero`, `TowardZero`, `AwayFromZero`,
  `TowardPositiveInfinity` and `TowardNegativeInfinity`; `Exact` refuses
  any rounding that changes the value. Each rounding returns `Conditions`
  (`Inexact`, `Rounded`, guard events) and its direction.
- **Contexts.** A `Context` carries precision, rounding mode, optional
  exponent guards, traps and a resource budget. It is an immutable value
  passed to each call; there is no global state. `Decimal32Context`,
  `Decimal64Context` and `Decimal128Context` give the IEEE 754 precisions.
- **Rounding to a target.** `Quantize`, `RoundToPrecision`,
  `RoundToIntegral`, `RoundToMultiple` (cash increments), `DivToExponent`
  and `ParseToExponent` (SQL `CAST(text AS DECIMAL(p,s))`) round exactly
  once.
- **Integer division and fused multiply-add.** `Quo`, `Rem` and `RemNear`
  are exact; `FMAWithContext` rounds x·y + z once.
- **Correctly rounded functions.** `Sqrt`, `Pow`, `Exp`, `Ln`, `Log10`,
  `PowDecimal`, `Sin`, `Cos`, `Tan`, `Asin`, `Acos`, `Atan`, `Atan2`,
  `Sinh`, `Cosh`, `Tanh`, `Asinh`, `Acosh` and `Atanh` are correctly
  rounded in every mode under a context: the exact result, rounded once.
  The bare forms return the exact value or refuse. The argument and the
  tests behind each claim are in
  [docs/reference/correct-rounding.md](docs/reference/correct-rounding.md).
- **Display.** `Text`/`String` (canonical, round-trips), `Fixed`,
  `Scientific`, `Engineering`, `Append…` forms and the `fmt` verbs
  `%v %s %f %e` with width and precision.
- **Interoperation.** `encoding.TextMarshaler`/`TextUnmarshaler`/
  `TextAppender`; JSON as a bare number out and a number or string in,
  never through `float64`; `database/sql` `Valuer` and `Scanner`,
  `NullDecimal` and the decompose-based `SQLDecimal`; exact conversion to
  and from `int64`, `uint64`, `big.Int`, `big.Rat` and 128-bit or
  two's-complement coefficients (Parquet, Arrow); `float64` conversion
  that treats a double as the exact binary rational it is, with
  `FromFloat64` for shortest digits and `CompareFloat64` for ordering
  without conversion.

## API overview

Operations that may round come in two forms:

| Form | Returns | Meaning |
| --- | --- | --- |
| `x.Add(y)` | `(Decimal, error)` | the exact result, or an error |
| `x.AddWithContext(y, ctx)` | `(Decimal, Conditions, error)` | rounded once under `ctx`, with the conditions it raised |

`Context{}` is exact, so `AddWithContext(y, Context{}.WithBudget(b))` is
the budgeted exact sum. Operations that round to a fixed target or never
round take a `Budget` in one `…WithBudget` form (`DivToExponentWithBudget`,
`SumWithBudget`, `ParseJSONWithBudget`, `ScanWithBudget`).

- **`Budget`** caps input bytes, digits, output bytes and work units. A
  zero field means no limit on that axis; a refusal is an error matching
  `ErrInsufficientStorage`, raised before anything is allocated. A budget
  never changes a result.
- **Estimators.** `EstimateAdd`, `EstimateParse`, `EstimateFixed` and their
  peers compute a call's `Cost` from operand `Shape`s before the call;
  `Cost.Budget()` builds a budget that admits it. `BoundEvaluation` turns
  the budget of an adaptive function (`Exp`, `Ln`, `Log10`, `PowDecimal`
  and the trigonometric and hyperbolic functions, whose working precision
  grows until the rounding is proved) into a heap bound.
- **`Error`.** Every operation failure is an `*Error` with the operation,
  an `ErrorCode` cause for `errors.Is` (`ErrInexact`, `ErrDivisionByZero`,
  `ErrConversionSyntax`, `ErrInsufficientStorage`, …), and the condition,
  remedy, input or exhausted quota where they apply.

For untrusted input, parse with a budget:

```go
ctx := decimal.Context{}.WithBudget(decimal.Budget{MaxInputBytes: 64, MaxDigits: 40})
d, _, err := decimal.ParseWithContext(input, ctx)
```

## Documentation

- [Semantics reference](docs/reference/semantics.md) (`docs/reference/semantics.md`):
  value model, cohorts, contexts, conditions, errors and budgets
- [API guide](docs/api-guide.md) (`docs/api-guide.md`): naming, choosing a
  call, handling results
- [Cookbook](docs/cookbook.md) (`docs/cookbook.md`): money rounding and
  map keys
- [Interop guide](docs/interop.md) (`docs/interop.md`): `database/sql` and
  a driver matrix, SQL `DECIMAL(p,s)` columns, JSON, binary coefficients
  and `float64`
- [Correct rounding](docs/reference/correct-rounding.md)
  (`docs/reference/correct-rounding.md`): the argument and tests behind
  each correctly rounded operation
- [Design rationale](docs/rationale.md) (`docs/rationale.md`): why the
  value space, precision model, rounding catalog, budgets and API are what
  they are
- [Architecture](ARCHITECTURE.md): repository layout and verification
- The package documentation: `go doc -all github.com/0xCarbon/decimal`

## Performance

The benchmark portfolio (families F1–F8: parsing, aggregation, a money
loop, formatting, map keys, tight 19-digit arithmetic, JSON and
`database/sql`) runs the same workloads through `decimal` and four other
Go decimal libraries (the incumbents): [shopspring/decimal](https://github.com/shopspring/decimal)
v1.6.0, [cockroachdb/apd](https://github.com/cockroachdb/apd) v3.2.3,
[ericlagergren/decimal](https://github.com/ericlagergren/decimal) and
[govalues/decimal](https://github.com/govalues/decimal) v0.1.36. Every row
first checks its results against a `math/big` oracle; a library that
cannot produce the oracle's result for a workload is excluded from that
row rather than timed.

The table gives medians of 10 interleaved rounds (AMD Ryzen 9 5900XT, two
pinned cores of a shared host, Go 1.27.1 linux/amd64, built with
`GOEXPERIMENT=simd`, 2026-11-11). Speedup is the fastest incumbent's time
divided by `decimal`'s time, using the medians shown (above 1.00x is
faster).

| family | workload | fastest incumbent | `decimal` time | incumbent time | speedup |
| --- | --- | --- | ---: | ---: | ---: |
| F1 parse | `"1234.56"` | govalues | 11.4 ns | 22.7 ns | 1.99x |
|  | 19-digit integer | govalues | 13.1 ns | 53.0 ns | 4.06x |
|  | 40 digits | shopspring | 61.8 ns | 342 ns | 5.54x |
|  | exponent form | shopspring | 12.7 ns | 60.5 ns | 4.75x |
| F2 aggregate | 1000 exact mixed-scale additions | govalues | 4.78 µs | 8.11 µs | 1.69x |
| F3 money loop | price × qty, round to cents, fee (256 lines) | ericlagergren | 3.51 µs | 13.1 µs | 3.74x |
| F4 format | plain | govalues | 17.9 ns | 19.5 ns | 1.09x |
|  | fixed, 2 places | govalues | 24.5 ns | 24.6 ns | 1.00x |
|  | scientific | apd | 27.3 ns | 121 ns | 4.44x |
| F5 map key | 1024 string keys | govalues | 118 µs | 147 µs | 1.25x |
| F6 tight arithmetic | add, 19 digits | ericlagergren | 4.52 ns | 21.2 ns | 4.69x |
|  | multiply, 19 digits | ericlagergren | 3.66 ns | 22.3 ns | 6.07x |
|  | divide to 2 places | shopspring | 13.9 ns | 153 ns | 11.05x |
|  | divide by 4 | shopspring | 13.3 ns | 101 ns | 7.58x |
|  | compare | shopspring | 2.78 ns | 5.58 ns | 2.01x |
| F7 JSON | encode + decode, bare number | govalues | 43.9 ns | 52.1 ns | 1.19x |
|  | encode + decode, quoted number | govalues | 39.7 ns | 52.0 ns | 1.31x |
| F8 `database/sql` | Valuer + Scan | govalues | 752 ns | 753 ns | 1.00x |
|  | `SQLDecimal` compose | apd | 585 ns | 618 ns | 1.06x |
|  | `NullDecimal` round trip | govalues | 718 ns | 716 ns | 1.00x |

The speedups of F1 to F3, F4 plain and scientific, and F5 to F7 are
significant (Mann–Whitney, p < 0.001), and in those rows `decimal`
allocates no more than the best incumbent, usually nothing. In F4 fixed and
in the F8 Valuer + Scan and `NullDecimal` rows the samples of `decimal` and
of the fastest incumbent overlap: treat those rows as ties. F8 is the one
family where `decimal` uses more memory: a `Decimal` is 32 bytes, so the
`driver.Value` round trip and the value-shaped `SQLDecimal`/`NullDecimal`
wrappers move 28–48 more bytes per row (and one more allocation in
compose, where the time is 6% shorter), which the database round trip
itself dwarfs.

To reproduce:

```sh
make bench-incumbents BENCH_COUNT=10   # writes dist/incumbents.txt
go run ./tools/benchcmp -dominance -ref decimal dist/incumbents.txt
```

See [benchmarks/incumbents/README.md](benchmarks/incumbents/README.md) for
the method and what each family measures. Absolute times vary with the
host; compare libraries only within one interleaved run on one machine.

## Development

```sh
make check        # vet, gofmt, checkdeps, checkstate, tests in both profiles
make conformance  # download the decTest corpus and run it
make fuzz-smoke   # 20 s per fuzz target
make bench        # benchmark portfolio
```

See [CONTRIBUTING.md](CONTRIBUTING.md) for the workflow and rules.

## Support and security

Questions and bug reports go to
[GitHub issues](https://github.com/0xCarbon/decimal/issues). Report
vulnerabilities privately as described in [SECURITY.md](SECURITY.md).
Participation is governed by the [code of conduct](CODE_OF_CONDUCT.md).
Release notes are in [CHANGELOG.md](CHANGELOG.md).

## License

Copyright 2026 0xCarbon. Licensed under Apache-2.0; see [LICENSE](LICENSE).
