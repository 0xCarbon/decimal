# API guide

How the package's API is organized and which call fits which job. The
package documentation (`go doc -all github.com/0xCarbon/decimal`) is the
reference for every function; the [semantics reference](reference/semantics.md)
states the rules they share. Every Go block on this page is the body of a
runnable example in [example_test.go](../example_test.go) whose output
`go test` checks, and a test keeps this page equal to it.

## A first program

<!-- example: Example -->
```go
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
fmt.Println(subtotal, tax, total)
// Output: 59.97 4.95 64.92
```

Multiplication is exact, so the tax keeps all six decimals until
`Quantize` rounds it to cents under the mode the code names.

## Naming

A rounding operation appears in two forms. The suffix says what the form
adds:

| Form | Signature shape | Adds |
| --- | --- | --- |
| `Add` | `(Decimal, error)` | exact result or refusal, no quota |
| `AddWithContext` | `(…, ctx Context) (Decimal, Conditions, error)` | rounding under a context, with conditions and the context's `Budget` |

`Context{}` is exact, so `AddWithContext(y, Context{}.WithBudget(b))` is the
budgeted exact sum. Operations that round to a fixed target or never round
take the `Budget` as a parameter in one `…WithBudget` form instead:

| Form | Signature shape | Adds |
| --- | --- | --- |
| `DivToExponent` | `(…, target int32, mode RoundingMode) (Decimal, Conditions, error)` | one rounding to a stored exponent |
| `DivToExponentWithBudget` | `(…, target int32, mode RoundingMode, budget Budget) (Decimal, Conditions, error)` | a caller limit on digits and work |
| `SumWithBudget` | `(values []Decimal, budget Budget) (Decimal, error)` | a caller limit on a non-rounding operation |

Other suffixes follow the same pattern: `ToExponent` rounds once to a
stored exponent (`DivToExponent`, `ParseToExponent`,
`FromFloat64ToExponent`, `FromRatToExponent`), `WithOptions` takes display
options (`FixedWithOptions`, `ScientificWithOptions`), `Append` writes into
a caller buffer (`AppendFixed`, `AppendScientific`, `AppendEngineering`),
and each budgeted operation has one `Estimate` function, named after it,
that returns its `Cost` before the call (`EstimateAdd(x, y, ctx)`,
`EstimateParse`, `EstimateFixed`). The adaptive functions (`Exp` …
`Atanh`) have no estimate; `BoundEvaluation` turns their context's
`Budget` into a heap bound. `MustParse` is the only function that panics;
it is meant for literals.

Values are passed and returned by value. Methods have value receivers,
except the decoders (`Scan`, `Compose`, `UnmarshalText`, `UnmarshalJSON`
and their budgeted forms), which set their pointer receiver only on
success.

## Choosing a call

| Task | Call |
| --- | --- |
| read a literal or user text | `Parse` (or `ParseWithContext(s, Context{}.WithBudget(b))` for untrusted input) |
| read text straight into a scale, SQL `CAST(text AS DECIMAL(p,s))` | `ParseToExponent` |
| exact sum, difference, product | `Add`, `Sub`, `Mul`, `Sum` |
| quotient that may not terminate | `DivWithContext` (to p digits) or `DivToExponent` (to a scale) |
| integer quotient and remainder | `Quo`, `Rem`, `RemNear` |
| x·y + z with one rounding | `FMAWithContext` |
| square root, integer power | `Sqrt`, `Pow` (exact or refused), `SqrtWithContext`, `PowWithContext` |
| round to cents or another scale | `Quantize` with an explicit mode |
| round to significant digits | `RoundToPrecision` |
| round to a cash increment such as 0.05 | `RoundToMultiple` |
| arithmetic at IEEE decimal64 precision | the `WithContext` forms with `Decimal64Context()` |
| exp, ln, log10, powers, trigonometry | `ExpWithContext`, `LnWithContext`, `PowDecimalWithContext`, `SinWithContext` … |
| compare, sort, test equality | `Compare` (with `slices.SortFunc`), `Equal` |
| map keys | `Reduce().Text(0)` or `Hasher`; see the [cookbook](cookbook.md#keys-for-maps) |
| show a number to a person | `Fixed`, `Scientific`, `Engineering`, `fmt` verbs |
| store or send a number | `Text`, `MarshalText`, `MarshalJSON`, `Value` |
| read a database column | `Scan` (or `NullDecimal` for a nullable column); see the [interop guide](interop.md) |
| exchange an unscaled coefficient | `NewInt128`, `CoefficientInt128`, `NewTwosComplement`, `AppendTwosComplement` |
| convert a float64 | `FromFloat64` (shortest digits) or `FromFloat64Exact` (exact binary value) |
| convert integers and math/big values | `FromInt64`, `Int64`, `FromBigInt`, `BigInt`, `FromRat` (exact or refused), `FromRatToExponent`, `Rat` |
| bound work before calling | the `Estimate…` function, then `Cost.Budget()` through `Context.WithBudget` or a `…WithBudget` form (`BoundEvaluation` for the adaptive functions) |

## Handling results

- `(Decimal, error)`: the error is the only signal. On error, use the
  returned value only where the method documents it.
- `(Decimal, Conditions, error)`: `Conditions` tells you what the
  rounding did (`Inexact`, `Rounded`, `Increased`, `Decreased`, guard
  events). A nil error with `Inexact` is a successful rounding. A trapped
  condition becomes an `*Error`; context arithmetic and `Quantize`
  still return their finite result beside it, while an `Exact` refusal
  returns none.
- Match errors with `errors.Is(err, decimal.ErrInexact)` and friends, and
  inspect them with `errors.As` into `*decimal.Error`, whose fields are
  listed in the [semantics reference](reference/semantics.md#errors).

## Integer minor units

Money kept as an integer count of minor units moves to and from `Decimal`
without loss: `New` places the exponent, and `Int64` returns the count
only when the value is integral.

<!-- example: ExampleNew_minorUnits -->
```go
price := decimal.New(1999, -2) // 1999 cents
total, err := price.Mul(decimal.FromInt64(3))
if err != nil {
	panic(err)
}
cents, err := total.Mul(decimal.FromInt64(100)) // exact: 5997.00
if err != nil {
	panic(err)
}
n, err := cents.Int64()
fmt.Println(price, total, n, err)

third, _, _ := total.DivToExponent(decimal.FromInt64(7), -4, decimal.TiesToEven) // 8.5671
scaled, _ := third.Mul(decimal.FromInt64(100))
_, err = scaled.Int64() // 856.7100 is not integral
fmt.Println(third, errors.Is(err, decimal.ErrNonIntegral))
// Output:
// 19.99 59.97 5997 <nil>
// 8.5671 true
```

Round to cents with `Quantize(-2, mode)` before converting a value that
may carry more decimals.

## More examples

[example_test.go](../example_test.go) holds every runnable example; `go doc`
shows each beside its function. The [cookbook](cookbook.md) collects
task recipes and the [interop guide](interop.md) covers databases, JSON
and binary lanes.
