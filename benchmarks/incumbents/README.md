# Incumbent comparison

This module runs the decimal benchmark portfolio (families F1–F8) against
four other Go decimal libraries in the same test binary:

| Library | Version |
| --- | --- |
| [github.com/shopspring/decimal](https://github.com/shopspring/decimal) | v1.6.0 |
| [github.com/cockroachdb/apd/v3](https://github.com/cockroachdb/apd) | v3.2.3 |
| [github.com/ericlagergren/decimal](https://github.com/ericlagergren/decimal) | v0.0.0-20240411145413-00de7ca16731 |
| [github.com/govalues/decimal](https://github.com/govalues/decimal) | v0.1.36 |

It is a separate module (`replace github.com/0xCarbon/decimal => ../..`)
so that the library and its own benchmarks keep no third-party
dependencies. Nothing imports it.

## Running

```sh
cd benchmarks/incumbents
go test -run . -bench . -benchtime 1x ./...           # smoke: every check and one iteration of every row
go test -v -run TestIncumbentMatchedAccuracy ./...    # the matched-accuracy table
go test -run '^$' -bench . -benchmem -count 10 . > run.txt
go run ../../tools/benchcmp -dominance -ref decimal run.txt
```

`make bench-incumbents` from the repository root runs the last two
commands (`BENCH_COUNT`, `BENCH_TIME` and `BENCH` adjust them) and writes
`dist/incumbents.txt`.

Sub-benchmarks are named `Family/library/variant`, for example
`BenchmarkF6TightArith/apd/mul19`. The `decimal` rows of each family run
first, then each incumbent's matching rows.

## Matched accuracy

Every row runs on the portfolio's committed-seed corpus and must produce
the same result as an independent `math/big` oracle before it is timed:

- every row: every value equals the oracle's value;
- F4 display rows: the text equals the oracle's text byte for byte;
- F7 JSON and F8 database rows: the value round-trips exactly; an
  emitter that differs only in presentation (quoted JSON numbers, dropped
  trailing zeros) is timed and labeled "value-matched".

A row whose check fails, or whose library has no API for the variant, is
never timed; `TestIncumbentMatchedAccuracy` prints it as `EXCLUDED` with
the first mismatch or the missing capability. Every timed loop calls the
library's methods directly and does the same class of work as the
matching `decimal` row; conversions to text and accuracy checks run
before timing.

## Families

| Family | Variants | Measures |
| --- | --- | --- |
| F1Parse | money6, int19, big40, expform | parsing text: 6-digit money values, 19-digit integers, 40-digit values, exponent form |
| F2Aggregate | mixed1000 | 1000 exact additions of mixed-scale operands |
| F3MoneyLoop | price-qty-round-fee | price × quantity, round to cents with ties away from zero, accumulate, apply a fee rate, net |
| F4Format | plain, fixed2dp, scientific | canonical text, two-decimal fixed display, scientific display with a digit count |
| F5MapKey | string1024, hasher1024 | inserting and looking up 1024 numerically equal keys of differing scale, through a canonical string key or a hashing recipe |
| F6TightArith | add19, mul19, mulsmall, div2dp, divby4, cmp19 | 19-digit add, multiply, multiply by a small integer, divide rounding to two decimals, exact division by 4, compare |
| F7JSON | plain, quoted | JSON encode and decode of a bare and of a quoted number |
| F8Database | valuer-scan, sqldecimal-compose, null-roundtrip | a `database/sql` round trip through an in-memory fake driver: `Value`/`Scan`, the decompose convention, and a nullable wrapper |

## Comparing

`benchcmp -dominance -ref decimal` groups rows by family and variant and
compares `decimal` with every incumbent that ran the same variant, unit
by unit (ns/op, B/op, allocs/op). A row is reported as dominated only when
`decimal`'s raw samples lie wholly below every incumbent's; an incumbent
whose samples lie wholly below `decimal`'s is printed as a SHORTFALL; any
overlap is "unseparated", and fewer than `-min-samples` (default 10)
observations per side is "insufficient".

For numbers you intend to publish:

- use a quiet machine: no other load, a fixed CPU frequency where
  possible, and the benchmark pinned to cores nothing else uses;
- run at least 10 rounds; to interleave rounds, build the test binary once
  (`go test -c -o incumbents.test .`) and run it repeatedly with
  `-test.count 1`, appending to one file, so drift affects every library
  alike;
- report the CPU, OS, Go version and build profile (the Makefile's default
  is `GOEXPERIMENT=simd`) with the raw output.

## Refreshing the portfolio copies

The `decimal_*_test.go` files are generated copies of `../*_test.go`.
`sync.sh` (run by `go generate ./...` here, or `make generate` at the
root) copies them into this package and renames each family that
`incumbents_test.go` re-declares from `BenchmarkF<n><Name>` to
`decimalF<n><Name>`; every other benchmark and test of the portfolio
becomes unexported, so `go test` here runs only the comparison and
`TestIncumbentMatchedAccuracy`. CI fails when the copies are stale.
