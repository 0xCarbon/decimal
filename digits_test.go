// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"fmt"
	"math"
	"math/rand/v2"
	"runtime"
	"strings"
	"testing"
)

// digitSpanBytewise is the one-byte-at-a-time oracle for digitSpan.
func digitSpanBytewise(s string) int {
	for i := range len(s) {
		if s[i] < '0' || s[i] > '9' {
			return i
		}
	}
	return len(s)
}

// TestDigitPredicate places every byte value at every position of every
// length through two full SWAR words plus a tail, checking both the span and
// the whole-string predicate.
func TestDigitPredicate(t *testing.T) {
	t.Logf("runtime=%s %s/%s", runtime.Version(), runtime.GOOS, runtime.GOARCH)
	for n := 0; n <= 129; n++ {
		data := []byte(strings.Repeat("9", n))
		if got := digitSpan(string(data)); got != n || !validDigits(string(data)) {
			t.Fatalf("valid length %d: span %d", n, got)
		}
		for pos := range data {
			for b := range 256 {
				data[pos] = byte(b)
				isDigit := byte(b) >= '0' && byte(b) <= '9'
				wantSpan := n
				if !isDigit {
					wantSpan = pos
				}
				if got := digitSpan(string(data)); got != wantSpan {
					t.Fatalf("length=%d position=%d byte=%d span=%d want=%d", n, pos, b, got, wantSpan)
				}
				if got := validDigits(string(data)); got != isDigit {
					t.Fatalf("length=%d position=%d byte=%d valid=%v want=%v", n, pos, b, got, isDigit)
				}
			}
			data[pos] = '9'
		}
	}
}

// TestZeroSpan checks the SWAR zero run against every byte at every
// position through two words plus a tail.
func TestZeroSpan(t *testing.T) {
	for n := 0; n <= 40; n++ {
		data := []byte(strings.Repeat("0", n))
		if got := zeroSpan(string(data)); got != n {
			t.Fatalf("all-zero length %d: span %d", n, got)
		}
		for pos := range data {
			for b := range 256 {
				data[pos] = byte(b)
				want := n
				if byte(b) != '0' {
					want = pos
				}
				if got := zeroSpan(string(data)); got != want {
					t.Fatalf("length=%d position=%d byte=%d span=%d want=%d", n, pos, b, got, want)
				}
			}
			data[pos] = '0'
		}
	}
}

func TestRandomDigits(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260922, 1))
	for i := range 10000 {
		n := rng.IntN(4097)
		data := make([]byte, n)
		for j := range data {
			data[j] = byte('0' + rng.IntN(10))
		}
		if i%2 == 0 && n > 0 {
			data[rng.IntN(n)] = byte(rng.IntN(256))
		}
		s := string(data)
		if got, want := digitSpan(s), digitSpanBytewise(s); got != want {
			t.Fatalf("case=%d length=%d got=%v want=%v", i, n, got, want)
		}
	}
}

// TestDigitSpanBytesMatchesScalarTwin checks the portable SIMD digit
// kernel against its scalar twin: seeded []byte
// inputs, the only carrier digitSpan dispatches to vectorDigitSpanBytes,
// run through the dispatched kernel and must equal both the SWAR scalar
// twin and the bytewise oracle, with one byte planted at a random position
// in three of every four inputs; the planted bytes cycle through all 256
// values, and the test asserts each was planted at least once. In the simd
// profile on a non-emulated target at least 1000 inputs reach the vector
// kernel; the scalar profile runs the same differential through the SWAR
// twin.
func TestDigitSpanBytesMatchesScalarTwin(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260929, 3))
	vector := 0
	var seen [256]bool
	planted := 0
	for i := range 4000 {
		n := rng.IntN(4097)
		data := make([]byte, n)
		for j := range data {
			data[j] = byte('0' + rng.IntN(10))
		}
		if i%4 != 0 && n > 0 {
			b := byte(planted % 256)
			planted++
			data[rng.IntN(n)] = b
			seen[b] = true
		}
		want := digitSpanBytewise(string(data))
		if got, swar := digitSpan(data), swarDigitSpan(data); got != want || swar != want {
			t.Fatalf("case=%d length=%d dispatched=%d swar=%d want=%d", i, n, got, swar, want)
		}
		if n >= vectorSpanMin {
			vector++
		}
	}
	var unseen []int
	for b, ok := range seen {
		if !ok {
			unseen = append(unseen, b)
		}
	}
	if len(unseen) > 0 {
		t.Fatalf("%d byte values never planted: %#x", len(unseen), unseen)
	}
	if vectorSpanMin < math.MaxInt && vector < 1000 {
		t.Fatalf("only %d inputs reached the vector dispatch threshold %d", vector, vectorSpanMin)
	}
	t.Logf("vector-eligible inputs: %d (threshold %d)", vector, vectorSpanMin)
}

func TestDigitAllocations(t *testing.T) {
	for _, n := range []int{19, 38, 128, 1024, 1000000} {
		s := strings.Repeat("9", n)
		allocs := testing.AllocsPerRun(100, func() { digitSpan(s) })
		if allocs != 0 {
			t.Errorf("length=%d allocations=%v want=0", n, allocs)
		}
	}
}

var spanResult int

// BenchmarkDigitSpan compares the SWAR kernel with the bytewise oracle.
func BenchmarkDigitSpan(b *testing.B) {
	for _, n := range []int{8, 19, 38, 128, 1024, 1000000} {
		for _, valid := range []bool{true, false} {
			s := strings.Repeat("9", n)
			if !valid {
				s = s[:len(s)-1] + ":"
			}
			want := digitSpanBytewise(s)
			raw := []byte(s)
			// bytewise: oracle; swar: string input; bytes: []byte input,
			// which takes the portable SIMD kernel in goexperiment.simd builds.
			for _, kernel := range []string{"bytewise", "swar", "bytes"} {
				span := digitSpan[string]
				switch kernel {
				case "bytewise":
					span = digitSpanBytewise
				case "bytes":
					span = func(string) int { return digitSpan(raw) }
				}
				b.Run(fmt.Sprintf("%s/n%d/valid%v", kernel, n, valid), func(b *testing.B) {
					if span(s) != want {
						b.Fatal("matched-accuracy check failed")
					}
					b.ReportAllocs()
					b.SetBytes(int64(n))
					for b.Loop() {
						spanResult = span(s)
					}
				})
			}
		}
	}
}
