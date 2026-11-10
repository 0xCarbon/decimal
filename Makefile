# SPDX-License-Identifier: Apache-2.0
#
# Development targets for github.com/0xCarbon/decimal. Every target builds
# with CGO_ENABLED=0. The default build profile is GOEXPERIMENT=simd; the
# scalar profile (GOEXPERIMENT=) must build and pass the same suite.

export CGO_ENABLED := 0
GOEXPERIMENT ?= simd
export GOEXPERIMENT
GO ?= go

# The decTest corpus is downloaded here, never committed (see testdata/dectest).
DECTEST_DIR := $(CURDIR)/.cache/dectest

# Every fuzz target of the library package; TestFuzzCorpusPromotion keeps
# this list complete.
FUZZ_TARGETS := FuzzScanDecimal FuzzParse FuzzRoundtrip FuzzArithmetic FuzzDivision FuzzFromRat FuzzFloat64Egress FuzzCompareFloat64 FuzzFromFloat64 FuzzParseToExponent FuzzScan FuzzTwosComplement FuzzQuoRem FuzzQuantize FuzzJSON FuzzEqualityScaleInvariant
FUZZ_TIME ?= 20s

BENCH ?= .
BENCH_COUNT ?= 10
BENCH_TIME ?= 1s

.PHONY: all help check test test-simd test-scalar vet fmt fmt-check lint bench-compare checkdeps checkstate \
	conformance fuzz-smoke bench bench-incumbents generate clean

all: check

help:
	@echo "make check             vet, fmt-check, checkdeps, checkstate and test (both profiles)"
	@echo "make test              go test ./... in the simd and the scalar profile"
	@echo "make vet               go vet ./... in both profiles"
	@echo "make fmt-check         fail on gofmt differences"
	@echo "make lint              vet and fmt-check, plus 'go fix -diff' modernizations"
	@echo "make checkdeps         dependency, unsafe and assembly policy of every module"
	@echo "make checkstate        no mutable package state, no init, panic only in Must*"
	@echo "make conformance       download the decTest corpus and run it"
	@echo "make fuzz-smoke        run every fuzz target for FUZZ_TIME (default 20s)"
	@echo "make bench             run the benchmark portfolio and summarize it"
	@echo "make bench-incumbents  run the portfolio against other Go decimal libraries"
	@echo "make bench-compare     A/B statistics: OLD=old.txt NEW=new.txt (go test -bench output)"
	@echo "make generate          regenerate float64_table.go and the incumbent copies"

check: vet fmt-check checkdeps checkstate test

test: test-simd test-scalar

test-simd:
	GOEXPERIMENT=simd $(GO) test -count=1 ./...

test-scalar:
	GOEXPERIMENT= $(GO) test -count=1 ./...

vet:
	GOEXPERIMENT=simd $(GO) vet ./...
	GOEXPERIMENT= $(GO) vet ./...

fmt:
	gofmt -s -w .

fmt-check:
	@out=$$(gofmt -s -l .); if [ -n "$$out" ]; then echo "gofmt -s differences (run make fmt):"; echo "$$out"; exit 1; fi

lint: vet fmt-check
	@out="$$($(GO) fix -diff ./... 2>&1)"; if [ -n "$$out" ]; then echo "$$out"; echo "go fix suggests modernizations"; exit 1; fi

checkdeps:
	$(GO) run ./tools/checkdeps

checkstate:
	$(GO) run ./tools/checkstate .

# Provisioning downloads the corpus once and verifies every file's size and
# SHA-256; a missing or altered corpus fails, it is never skipped.
conformance:
	$(GO) run ./tools/dectestconv -provision -downloads testdata/dectest/downloads.txt -dir $(DECTEST_DIR)
	DECIMAL_DECTEST_DIR=$(DECTEST_DIR) $(GO) test -count=1 -run '^(TestDecTestCorpus|TestDecTestFixtures)$$' ./tools/dectestconv

fuzz-smoke:
	@for t in $(FUZZ_TARGETS); do \
		echo "==> $$t ($(FUZZ_TIME))"; \
		$(GO) test -run '^$$' -fuzz "^$$t$$" -fuzztime $(FUZZ_TIME) . || exit 1; \
	done

bench:
	@mkdir -p dist
	$(GO) test -run '^$$' -bench '$(BENCH)' -benchtime $(BENCH_TIME) -count $(BENCH_COUNT) -benchmem ./benchmarks | tee dist/bench.txt
	$(GO) run ./tools/benchcmp -summary dist/bench.txt

bench-compare:
	@test -n "$(OLD)" && test -n "$(NEW)" || { echo "usage: make bench-compare OLD=old.txt NEW=new.txt"; exit 2; }
	$(GO) run ./tools/benchcmp $(OLD) $(NEW)

bench-incumbents:
	@mkdir -p dist
	cd benchmarks/incumbents && $(GO) test -run '^$$' -bench '$(BENCH)' -benchtime $(BENCH_TIME) -count $(BENCH_COUNT) -benchmem . | tee $(CURDIR)/dist/incumbents.txt
	$(GO) run ./tools/benchcmp -dominance -ref decimal dist/incumbents.txt

generate:
	$(GO) run ./tools/float64table > float64_table.go.tmp && mv float64_table.go.tmp float64_table.go
	cd benchmarks/incumbents && $(GO) generate ./...

clean:
	rm -rf dist
