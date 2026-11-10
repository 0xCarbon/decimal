# Contributing to Decimal

Thank you for helping. Decimal v1 is feature-complete: contributions are
bug fixes, conformance fixes, performance improvements, documentation and
tests. A change to the exported API or to observable behavior (values,
cohorts, conditions, error identities, budget charges, serializations)
needs an issue first; see [Compatibility](docs/rationale.md#scope-and-compatibility).

## Setup

You need Go 1.27.1 or newer. Every build uses `CGO_ENABLED=0`; the
Makefile sets it, and builds with `GOEXPERIMENT=simd` unless told
otherwise.

```sh
make check        # vet and gofmt, checkdeps, checkstate, go test in both profiles
make conformance  # download the decTest corpus (once) and run it
make fuzz-smoke   # fuzz each target for 20 s (FUZZ_TIME=1m for longer)
```

CI runs the same checks on Linux (amd64, arm64, 386), macOS, Windows and
js/wasm, so a pull request should pass `make check` locally first.
For a change that touches only Markdown files or `LICENSE`, CI runs the
test suite once (Linux, `simd`), which holds the documentation tests; the
other jobs pass without running.

## Rules

- **Standard library only.** The library and its tools import nothing
  outside `std`; `make checkdeps` enforces it. Third-party decimal
  libraries appear only in the separate `benchmarks/incumbents` module.
- **No `unsafe`, cgo or assembly.** Portable SIMD uses only the standard
  `simd` package, in `goexperiment.simd` files with a scalar twin; never
  import `simd/archsimd` directly.
- **Both build profiles.** `GOEXPERIMENT=simd` (the Makefile's default)
  and the scalar profile `GOEXPERIMENT=` (what a plain `go build` selects)
  must build and pass the same suite, with identical results.
- **No panics, no package state.** Operations return errors; only
  `Must…` functions panic. Package-level variables are never written
  (`make checkstate`).
- **Budgets refuse before allocating.** Every operation whose work depends
  on input size has a budgeted form, and the budget is checked before any
  allocation. Finite-precision operations must not do work proportional
  to quantities the result does not need, such as an exponent gap.
- **Fast paths never own semantics.** An optimized path returns only when
  its result is provably what the general path returns, and otherwise
  defers to it. Add a differential test that pins the fast path to the
  general path over randomized and boundary inputs, with a guard that the
  fast path was actually taken. A fast path that serves budgeted calls
  gates on a derived bound of the general charge (`limits.admits` and the
  constants in `cost.go`, each attained in a test on its dearest shape) or
  on the general path's own pricing of the call; the general path owns
  every refusal.
- **Independent oracles.** Tests check results against `math/big`,
  `strconv`, `encoding/json` or hand-derived vectors, never against the
  code under test.

## Tests

- A bug fix starts with a test that fails on the current code for the
  intended reason (a wrong value, cohort, condition, error identity or
  allocation count).
- Tests of `foo.go` go in `foo_test.go`. Public-API tests that need the
  external package go in `api_test.go`, runnable examples in
  `example_test.go`, and fuzz targets in `fuzz_test.go` unless they belong
  beside one subject's tests (`FuzzEqualityScaleInvariant`,
  `FuzzScanDecimal`). Every fuzz target is listed in the Makefile's
  `FUZZ_TARGETS`, which a test enforces.
- Every Go block in `docs/` is the body of an example in `example_test.go`,
  named by a `<!-- example: ExampleName -->` line before it; a test keeps
  them equal.
- A fuzz crasher is committed under `testdata/fuzz/<Target>/` with a named
  regression test; see [testdata/fuzz/README.md](testdata/fuzz/README.md).
- A documentation claim that an operation is correctly rounded cites
  [docs/reference/correct-rounding.md](docs/reference/correct-rounding.md),
  which names its checker and oracle cases.

## Conformance corpus

`make conformance` downloads the General Decimal Arithmetic decTest suites
into `.cache/dectest` (gitignored; the corpus is not redistributed),
verifies each file's SHA-256 against `testdata/dectest/downloads.txt`, and
runs every adopted case. `testdata/dectest/manifest.json` classifies every
case: adopted, excluded with a reason (non-finite values, clamping,
signed zero, …) or re-derived with provenance, and
`testdata/dectest/classification.txt` lists the per-case result. A change
to the rules or the library that moves a case shows up as drift and must
be reviewed in the manifest.

## Benchmarks

`benchmarks/` holds the F1–F8 portfolio; every timed row checks its
results against an oracle before timing. A performance change needs an
interleaved A/B comparison on a quiet machine:

```sh
git stash; go test -c -o old.test ./benchmarks; git stash pop
go test -c -o new.test ./benchmarks
for i in $(seq 10); do
	./old.test -test.run '^$' -test.bench . -test.benchmem -test.count 1 >> old.txt
	./new.test -test.run '^$' -test.bench . -test.benchmem -test.count 1 >> new.txt
done
go run ./tools/benchcmp old.txt new.txt
```

Use at least 10 rounds per side; `benchcmp` reports a change only at
p ≤ 0.05 (Mann-Whitney U). Include the command, Go version, CPU, OS and the
raw output in the pull request. Rows the change cannot reach should show
no significant change; if they do, the host is noisy. A change to the
library's speed should be shown at a public entry point, not only by an
isolated kernel timing.

The comparison with other libraries lives in
[benchmarks/incumbents](benchmarks/incumbents/README.md). After changing
`benchmarks/*_test.go`, run `make generate` to refresh its copies.

## Generated files

`float64_table.go` is generated by `tools/float64table`; `make generate`
rewrites it, and a test fails when it is stale.

## Pull requests

Keep a pull request to one concern, describe the behavior it changes,
and add an entry under "Unreleased" in [CHANGELOG.md](CHANGELOG.md) for
anything users can observe. By contributing you agree that your
contribution is licensed under the [Apache License 2.0](LICENSE).
Participation is governed by the [code of conduct](CODE_OF_CONDUCT.md).
