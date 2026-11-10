// SPDX-License-Identifier: Apache-2.0

// Package incumbents compares github.com/0xCarbon/decimal with other Go
// decimal libraries on the F1–F8 benchmark portfolio. It is a separate
// module so that the library and its own benchmarks stay free of
// third-party dependencies; nothing imports it.
//
// The decimal_*_test.go files are generated copies of ../*_test.go; see
// sync.sh and README.md.
package incumbents

//go:generate sh sync.sh
