# Interop guide

How Decimal meets databases, JSON and other carriers. The
[semantics reference](reference/semantics.md) covers the value model.
Every Go block on this page is the body of a runnable example in
[example_test.go](../example_test.go) whose output `go test` checks, and a
test keeps this page equal to it.

## database/sql

- **Binding.** A `Decimal` parameter binds as its canonical text
  (`Value` returns a string such as `19.90`), which every listed driver
  accepts; the engine parses it into the column type.
- **Scanning.** `Scan` reads text (`string`,
  `[]byte`) with its written scale, `int64`, `float64` as its exact binary
  value, `big.Int` and `*big.Int`, terminating `big.Rat` and `*big.Rat`,
  and any value with a `Decompose` method. It refuses `big.Float` with a
  remedy, a non-terminating rational with `ErrInexact`, and SQL NULL.
- **NULL.** Scan nullable columns into `NullDecimal`; its
  `Value` is nil when `Valid` is false.
- **Decompose binding.** `SQLDecimal{d}` binds through the database/sql
  decompose convention, for drivers that type parameters by value. Drivers
  without decompose support reject it; pass the `Decimal` itself to them.
- **Driver-specific types.** A driver value without `Decompose` (DuckDB's
  decimal, for example) needs a small wrapper Scanner;
  `ExampleNullDecimal_driverDecimal` in example_test.go shows one.

<!-- example: ExampleNullDecimal -->
```go
var price decimal.NullDecimal
_ = price.Scan([]byte("19.90")) // a NUMERIC column as a driver delivers it
fmt.Println(price.Decimal, price.Valid)
_ = price.Scan(nil) // SQL NULL
v, _ := price.Value()
fmt.Println(price.Valid, v)
var d decimal.Decimal
_ = d.Scan(0.1) // a float column scans as its exact binary value
fmt.Println(d)
// Output:
// 19.90 true
// false <nil>
// 0.1000000000000000055511151231257827021181583404541015625
```

### Driver matrix

What each driver delivers for a `DECIMAL`/`NUMERIC` column by default,
according to its source at the listed version or commit (read in September
2026; only the SQLite behavior was run), with the `Scan` outcome of this
library. Each driver accepts the `Value` string on bind; whether Trino,
Databricks and BigQuery coerce it server-side was not tested.

| Driver | Version | Delivers by default | `Scan` |
| --- | --- | --- | --- |
| lib/pq | 451ac10 | `[]byte` PostgreSQL text | accepted |
| jackc/pgx v5 stdlib | 794073f | `string` | accepted |
| go-sql-driver/mysql | 16b91c5 | `[]byte` text on both protocols | accepted |
| microsoft/go-mssqldb | 1f52296 | `[]byte` scaled text | accepted |
| ClickHouse/clickhouse-go/v2 (std) | v2.48.0 | `string`, trailing zeros trimmed upstream | accepted; the column scale is already lost |
| snowflakedb/gosnowflake/v2 | v2.2.0 | `string`; `big.Float` or `big.Int` with `WithHigherPrecision` | accepted; `big.Int` accepted, `big.Float` refused |
| mattn/go-sqlite3 | v1.14.52 | `int64`, `float64`, `string` or `[]byte` by storage class | accepted |
| modernc.org/sqlite | v1.59.0 | as mattn; NUMERIC affinity stores `"1.10"` as REAL 1.1 | accepted; the loss is upstream |
| ncruces/go-sqlite3 | v0.35.6 | as mattn | accepted |
| godror/godror | v0.51.5 | `godror.Number` with `Decompose` | accepted through `Decompose` |
| sijms/go-ora/v2 | v2.9.0 | `string` | accepted |
| duckdb/duckdb-go/v2 | v2.10505.0 | `duckdb.Decimal` (no `Decompose`) | refused; use a wrapper Scanner |
| googleapis/go-sql-spanner | v1.26.0 | `big.Rat` (GoogleSQL), `string` (PostgreSQL dialect) | accepted (terminating rationals) |
| trinodb/trino-go-client | v0.336.0 | `string` | accepted |
| databricks/databricks-sql-go | v1.16.0 | `string`; `float64` with `WithKernelDecimalAsFloat` | accepted |
| gorm.io/driver/bigquery, viant/bigquery | v1.2.1, v0.5.3 | `*big.Rat`, `float64` | accepted (terminating rationals; `float64` as its binary value) |

The first four drivers transport the `Value` string losslessly. Only godror implements the
decompose convention, on its own type, and no listed driver consumes a
foreign decomposer on bind, so none of them needs `SQLDecimal`.

Scale lost upstream is not restored by `Scan`: a rational source (Spanner,
BigQuery) carries no column scale and scans at the largest exponent not
above 0, so a Spanner NUMERIC 1.10 scans as 1.1; ClickHouse's std mode
trims trailing zeros; SQLite's NUMERIC affinity stores decimal text as
REAL; godror's `NumberAsFloat64` option delivers `float64`; and in
MariaDB's `sql_mode=ORACLE` a plain `NUMBER` column is a DOUBLE, not a
DECIMAL.

## SQL DECIMAL(p,s) columns

An engine's `DECIMAL(p,s)` or `NUMERIC(p,s)` column stores values with at
most p digits, s of them after the point. Decimal has no column type and no
engine profile: the library keeps
exact values and their scale, and the caller applies the column rule with
a `Context` and `Quantize`.

- `QuantizeWithContext(-s, ctx)` with `ctx` of precision p rounds to the
  column's scale once and refuses, with `ErrInvalidOperation`, a value
  whose result needs more than p digits, which is the
  assignment rule of engines that raise an error on precision overflow.
- The rounding mode is the engine's rule, named by the caller.
  PostgreSQL's `numeric` and MySQL's `DECIMAL` assignment round ties away
  from zero.
- Arithmetic stays exact until the assignment, so a product is rounded
  once. A division rounds once to the engine's result scale with
  `DivToExponent`; that scale is the engine's rule (MySQL: the dividend's
  scale plus `div_precision_increment`; PostgreSQL and SQL Server use
  other formulas, and `AVG`'s result type is implementation-defined).
  Storing the
  quotient in a narrower column rounds a second time, as the engine does.
- `ParseToExponent` is the scale half of `CAST(text AS DECIMAL(p,s))`:
  it rounds the literal once and stores only the result's digits. A
  following `QuantizeWithContext` at the same exponent is exact and adds
  the precision check.

<!-- example: ExampleContext_sqlDecimal -->
```go
// NUMERIC(5,2): five digits, two after the point, ties away from zero.
column, err := decimal.NewContext(5, decimal.TiesAwayFromZero, nil, 0)
if err != nil {
	panic(err)
}
for _, text := range []string{"123.456", "7", "-0.005", "999.995", "1234.5"} {
	stored, conditions, err := decimal.MustParse(text).QuantizeWithContext(-2, column)
	if err != nil {
		fmt.Println(text, "->", err, errors.Is(err, decimal.ErrInvalidOperation))
		continue
	}
	fmt.Println(text, "->", stored, conditions)
}

// Arithmetic is exact; the assignment rounds once.
price, quantity := decimal.MustParse("19.99"), decimal.MustParse("0.333")
line, _ := price.Mul(quantity) // exact: 6.65667
stored, conditions, _ := line.QuantizeWithContext(-2, column)
fmt.Println(line, "->", stored, conditions)

// A quotient at MySQL's division scale (the dividend's scale 2 plus
// div_precision_increment 4), then assigned to the column: two roundings,
// as the engine performs them.
sum, _ := decimal.Sum(decimal.MustParse("10.00"), decimal.MustParse("20.00"), decimal.MustParse("20.00"))
quotient, conditions, _ := sum.DivToExponent(decimal.FromInt64(3), -2-4, decimal.TiesAwayFromZero)
fmt.Println(sum, "/ 3 ->", quotient, conditions)
stored, conditions, _ = quotient.QuantizeWithContext(-2, column)
fmt.Println(quotient, "->", stored, conditions)
// Output:
// 123.456 -> 123.46 Inexact|Rounded|Increased
// 7 -> 7.00 0
// -0.005 -> -0.01 Inexact|Rounded|Decreased
// 999.995 -> decimal: QuantizeWithContext: invalid operation true
// 1234.5 -> decimal: QuantizeWithContext: invalid operation true
// 6.65667 -> 6.66 Inexact|Rounded|Increased
// 50.00 / 3 -> 16.666667 Inexact|Rounded|Increased
// 16.666667 -> 16.67 Inexact|Rounded|Increased
```

999.995 rounds to 1000.00, six digits, so `NUMERIC(5,2)` refuses it, as
it refuses 1234.5. Engine result-type rules compose from the same calls;
`TestEngineRulesComposeFromCoreOperations` builds a SQL Server
`decimal(38,6)` quotient from `DivWithContext` at precision 38 and
`Quantize(-6, …)`, and MySQL's division scale (the dividend's scale plus
`div_precision_increment`) from `DivToExponent`.

## JSON and text formats

- **JSON.** `MarshalJSON` emits a bare canonical number, never a
  string and never through `float64`; `UnmarshalJSON` accepts a number or
  a string and keeps the written scale.
- **Text formats.** YAML and other text encoders use
  `MarshalText` and `UnmarshalText`; non-finite spellings such as `.nan`
  are rejected.

<!-- example: ExampleDecimal_MarshalJSON -->
```go
var order struct {
	Amount decimal.Decimal `json:"amount"`
	Fee    decimal.Decimal `json:"fee"`
}
if err := json.Unmarshal([]byte(`{"amount": 10.50, "fee": "0.25"}`), &order); err != nil {
	panic(err)
}
out, _ := json.Marshal(order)
fmt.Println(string(out))
// Output: {"amount":10.50,"fee":0.25}
```

## Binary coefficient lanes

A lane is a fixed-width binary column that holds the unscaled coefficient.

`NewInt128` and `CoefficientInt128` exchange the coefficient with 128-bit
storage words, and `NewTwosComplement` and `AppendTwosComplement` with
Parquet or Arrow two's-complement bytes of any width; the exponent (the
negated column scale) travels separately.

<!-- example: ExampleNewTwosComplement -->
```go
// A Parquet FIXED_LEN_BYTE_ARRAY(16) DECIMAL(38,2) value: big-endian
// two's complement coefficient, scale out of band.
lane := []byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfb, 0x2e}
d, _ := decimal.NewTwosComplement(lane, binary.BigEndian, -2)
fmt.Println(d)
out, _ := d.AppendTwosComplement(nil, 4, binary.LittleEndian)
fmt.Printf("% x\n", out)
// Output:
// -12.34
// 2e fb ff ff
```

## math/big

`FromBigInt` and `BigInt` convert a `*big.Int` exactly; `BigInt` refuses a
value with a nonzero fraction (`ErrNonIntegral`). `Rat` returns the value
as an exact `*big.Rat` in lowest terms. `FromRat` converts a terminating
rational exactly and refuses one such as 1/3 with a remedy;
`FromRatWithContext` and `FromRatToExponent` round it once, as
`DivWithContext` and `DivToExponent` do. `BigInt` and `Rat` fill a
caller's destination (`d.BigInt(z)`, `d.Rat(z)`; nil allocates). Each
conversion is bounded by a `Budget`: the context forms read it from
`Context.WithBudget`, the others take it in a `…WithBudget` form
(`FromBigIntWithBudget`, `BigIntWithBudget`, `RatWithBudget`,
`FromRatToExponentWithBudget`), and a `big.Float` is never converted
implicitly.

## Binary floating point

A `float64` is an exact binary rational, so `0.1` as a double is not the
decimal 0.1. `FromFloat64` keeps strconv's shortest digits, and
`FromFloat64Exact` the exact value; `FromFloat64ToExponent` rounds the
exact value once to a scale.
`Float64Rounded` returns the double below or above the decimal, and
`CompareFloat64` orders the two without converting. For a map key
that a decimal and a double share exactly when they are equal, see the
[cookbook](cookbook.md#keys-that-span-decimal-and-float64).

<!-- example: ExampleDecimal_Float64Rounded -->
```go
d := decimal.MustParse("0.1")
lo, lc, _ := d.Float64Rounded(decimal.TowardNegativeInfinity)
hi, hc, _ := d.Float64Rounded(decimal.TowardPositiveInfinity)
fmt.Println(lo, lc)
fmt.Println(hi, hc)
cmp, _ := d.CompareFloat64(0.1)
fmt.Println(cmp)
exact, _ := decimal.FromFloat64Exact(0.1)
cast, _, _ := decimal.FromFloat64ToExponent(2.675, -2, decimal.TiesToEven)
fmt.Println(exact, cast)
// Output:
// 0.09999999999999999 Inexact|Rounded|Decreased
// 0.1 Inexact|Rounded|Increased
// -1
// 0.1000000000000000055511151231257827021181583404541015625 2.67
```
