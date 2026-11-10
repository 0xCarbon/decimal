# Fuzz seed corpora and crasher promotion

Each subdirectory `Fuzz<Target>/` is the committed seed corpus for one
target, in the native format (`go test fuzz v1` header; one argument per
line as a Go call expression). `f.Add` seeds inside `fuzz_test.go` and these
files both run on every plain `go test`, so every committed seed is a
regression test.

`make fuzz-smoke` fuzzes every target for 20 seconds (`FUZZ_TIME` changes
it); CI runs it on every push. For a longer run of one target:

```sh
go test -run '^$' -fuzz '^FuzzParse$' -fuzztime 10m .
```

## Promoting a crasher

Every crasher found by fuzzing is kept as a regression test:

1. **Reproduce.** `go test -run '^Fuzz<Target>$' .` re-runs the committed
   corpus; the crasher file the fuzzer wrote under this directory must fail
   the target deterministically.
2. **Commit the seed.** Keep the crasher file in this directory under its
   name with the prefix `crasher-`, tracked in Git, so every later
   `go test` re-executes it.
3. **Add a named regression test.** Add `TestRegression<short-id>` beside
   the target (in the same test file), invoking the same property on the
   exact input and naming the file as a `"<Target>/crasher-<id>"` string
   literal.
4. **Fix the defect.** The seed and the named test stay after the fix.

`TestFuzzCorpusPromotion` enforces these rules on every plain `go test`: a
file the engine wrote (a 16-hex-digit name) fails until it is promoted,
every `crasher-` file needs its `TestRegression` test, every regression
test names a committed crasher, and every fuzz target of the package is in
the Makefile's `FUZZ_TARGETS`.
