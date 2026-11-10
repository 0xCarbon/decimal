// SPDX-License-Identifier: Apache-2.0

// Package benchmarks holds the F1–F8 benchmark portfolio for
// github.com/0xCarbon/decimal and its supplemental families (value
// operations, display extras, the Catalogue and Conversion families, the
// multiply family and others). It uses only the public API; every timed
// variant first checks its results against an independent oracle
// (math/big, strconv, encoding/json or the input text itself), so a fast but
// wrong implementation fails before it is measured.
//
// Inputs derive from the committed seed 20260918 and sub-benchmark names are
// stable (Family/library/variant), so runs on two commits compare directly:
//
//	go test -run '^$' -bench . -count 10 ./benchmarks > new.txt
//	go run ./tools/benchcmp old.txt new.txt
//
// make bench aggregates one run with benchcmp -summary. The incumbent
// comparison lives in the separate module benchmarks/incumbents, so this
// module and the library stay free of third-party dependencies; benchcmp
// -dominance compares each family with the incumbents on a run that holds
// their rows.
package benchmarks
