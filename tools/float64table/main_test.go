// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"os"
	"testing"
)

// TestGeneratedTableIsCurrent keeps float64_table.go equal to this
// generator's output.
func TestGeneratedTableIsCurrent(t *testing.T) {
	committed, err := os.ReadFile("../../float64_table.go")
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(committed, generate()) {
		t.Fatal("float64_table.go is stale: go run ./tools/float64table > float64_table.go")
	}
}
