// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"fmt"
	"io"
	"math"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"
)

// TestRegressionMode rejects adverse changes and incomplete input.
// Expected outcomes use separated hand-derived samples, not the comparator.
func TestRegressionMode(t *testing.T) {
	for _, tc := range []struct {
		name     string
		old, cur string
		count    int
		want     int
	}{
		{"same", "100", "100", 8, 0},
		{"faster", "100", "90", 8, 0},
		{"slower_even_inside_old_band", "100", "101", 8, 1},
		{"insufficient", "100", "90", 7, 1},
		{"not_finite", "100", "NaN", 8, 1},
		{"negative", "100", "-1", 8, 1},
		{"zero_time", "100", "0", 8, 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			paths := []string{filepath.Join(dir, "a.txt"), filepath.Join(dir, "b.txt")}
			for i, v := range []string{tc.old, tc.cur} {
				if err := os.WriteFile(paths[i], []byte(strings.Repeat("BenchmarkX-1 100 "+v+" ns/op 0 B/op 0 allocs/op\n", tc.count)), 0o644); err != nil {
					t.Fatal(err)
				}
			}
			var out, errs bytes.Buffer
			if got := run(append([]string{"-regression"}, paths...), &out, &errs); got != tc.want {
				t.Fatalf("exit=%d want=%d; %s %s", got, tc.want, &out, &errs)
			}
		})
	}
	for _, mutation := range []string{"missing_row", "missing_unit", "extra_row", "allocation", "bytes", "failure", "allocation_distribution"} {
		t.Run(mutation, func(t *testing.T) {
			dir := t.TempDir()
			a := strings.Repeat("BenchmarkX-1 100 100 ns/op 0 B/op 0 allocs/op\n", 8)
			b := a
			switch mutation {
			case "missing_row":
				b = strings.ReplaceAll(b, "BenchmarkX", "BenchmarkY")
			case "missing_unit":
				b = strings.ReplaceAll(b, " 0 B/op", "")
			case "extra_row":
				b += strings.ReplaceAll(a, "BenchmarkX", "BenchmarkY")
			case "allocation":
				b = strings.Replace(b, "0 allocs/op", "1 allocs/op", 1)
			case "bytes":
				b = strings.Replace(b, "0 B/op", "1 B/op", 1)
			case "failure":
				b += "FAIL\n"
			case "allocation_distribution":
				a = strings.Replace(a, "0 allocs/op", "1 allocs/op", 1)
				b = strings.ReplaceAll(b, "0 allocs/op", "1 allocs/op")
			}
			paths := []string{filepath.Join(dir, "a"), filepath.Join(dir, "b")}
			for i, data := range []string{a, b} {
				if err := os.WriteFile(paths[i], []byte(data), 0o644); err != nil {
					t.Fatal(err)
				}
			}
			var out, errs bytes.Buffer
			if got := run(append([]string{"-regression"}, paths...), &out, &errs); got != 1 {
				t.Fatalf("exit=%d; %s %s", got, &out, &errs)
			}
		})
	}
}

func TestParseStripsProcsAndCollectsUnits(t *testing.T) {
	input := `goos: linux
BenchmarkX/a-4   	 100	  12.5 ns/op	  8 B/op	  1 allocs/op
BenchmarkX/a-4   	 100	  13.5 ns/op	  8 B/op	  1 allocs/op
BenchmarkY-16    	  10	  99 ns/op
PASS
`
	s, err := parse(strings.NewReader(input))
	if err != nil {
		t.Fatal(err)
	}
	if got := strings.Join(s.order, ","); got != "BenchmarkX/a,BenchmarkY" {
		t.Fatalf("order = %s", got)
	}
	if got := s.units["BenchmarkX/a"]["ns/op"]; len(got) != 2 || got[0] != 12.5 || got[1] != 13.5 {
		t.Fatalf("ns/op samples = %v", got)
	}
	if got := s.units["BenchmarkX/a"]["allocs/op"]; len(got) != 2 {
		t.Fatalf("allocs/op samples = %v", got)
	}
}

func TestMannWhitneyExactAndApproximate(t *testing.T) {
	// Completely separated samples of 5 and 5: exact two-sided p = 2/C(10,5).
	low := []float64{1, 2, 3, 4, 5}
	high := []float64{6, 7, 8, 9, 10}
	if got, want := mannWhitney(low, high), 2.0/252; math.Abs(got-want) > 1e-12 {
		t.Fatalf("exact p = %v, want %v", got, want)
	}
	// Identical distributions are never significant.
	if got := mannWhitney([]float64{1, 1, 1}, []float64{1, 1, 1}); got != 1 {
		t.Fatalf("all-tied p = %v, want 1", got)
	}
	// Interleaved samples are not significant.
	if got := mannWhitney([]float64{1, 3, 5, 7, 9}, []float64{2, 4, 6, 8, 10}); got < 0.5 {
		t.Fatalf("interleaved p = %v, want >= 0.5", got)
	}
	// Ties use the normal approximation and still detect clear separation.
	if got := mannWhitney([]float64{1, 1, 2, 2, 3, 3}, []float64{7, 7, 8, 8, 9, 9}); got > 0.01 {
		t.Fatalf("tied separated p = %v, want <= 0.01", got)
	}
}

func TestRunReportsOnlySignificantChanges(t *testing.T) {
	dir := t.TempDir()
	write := func(name string, values ...string) string {
		var b strings.Builder
		for _, v := range values {
			b.WriteString("BenchmarkFast-4 100 " + v + " ns/op\n")
			b.WriteString("BenchmarkSame-4 100 50 ns/op\n")
		}
		path := filepath.Join(dir, name)
		if err := os.WriteFile(path, []byte(b.String()), 0o644); err != nil {
			t.Fatal(err)
		}
		return path
	}
	old := write("old.txt", "100", "101", "102", "103", "104", "105")
	cur := write("new.txt", "50", "51", "52", "53", "54", "55")
	var stdout, stderr bytes.Buffer
	if code := run([]string{old, cur}, &stdout, &stderr); code != 0 {
		t.Fatalf("exit %d: %s", code, stderr.String())
	}
	out := stdout.String()
	if !strings.Contains(out, "BenchmarkFast") || !strings.Contains(out, "-48.8%") {
		t.Fatalf("missing significant speedup:\n%s", out)
	}
	for line := range strings.SplitSeq(out, "\n") {
		if strings.HasPrefix(line, "BenchmarkSame") && !strings.Contains(line, " ~ ") {
			t.Fatalf("unchanged benchmark reported as a change: %q", line)
		}
	}
	if code := run([]string{old}, &stdout, &stderr); code != 2 {
		t.Fatalf("missing argument exit = %d, want 2", code)
	}
	empty := filepath.Join(dir, "empty.txt")
	if err := os.WriteFile(empty, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	if code := run([]string{old, empty}, &stdout, &stderr); code != 1 {
		t.Fatalf("empty input exit = %d, want 1", code)
	}
}

// writeRun writes one benchmark run; each row is a name and its samples.
func writeRun(t *testing.T, rows map[string][]string, extra string) string {
	t.Helper()
	var b strings.Builder
	names := make([]string, 0, len(rows))
	for name := range rows {
		names = append(names, name)
	}
	slices.Sort(names)
	for _, name := range names {
		for _, sample := range rows[name] {
			b.WriteString(name + "-32 1000 " + sample + "\n")
		}
	}
	b.WriteString(extra)
	path := filepath.Join(t.TempDir(), "run.txt")
	if err := os.WriteFile(path, []byte(b.String()), 0o644); err != nil {
		t.Fatal(err)
	}
	return path
}

func tenSamples(from, step int, allocs string) []string {
	out := make([]string, 10)
	for i := range out {
		out[i] = strconv.Itoa(from+i*step) + " ns/op " + allocs
	}
	return out
}

func runOut(t *testing.T, args ...string) (string, int) {
	t.Helper()
	var stdout, stderr bytes.Buffer
	code := run(args, &stdout, &stderr)
	return stdout.String() + stderr.String(), code
}

func lineOf(t *testing.T, out, prefix, unit string) string {
	t.Helper()
	for line := range strings.SplitSeq(out, "\n") {
		if f := strings.Fields(line); len(f) > 1 && f[0] == prefix && f[1] == unit {
			return line
		}
	}
	t.Fatalf("no %s %s row in:\n%s", prefix, unit, out)
	return ""
}

// TestRunRefusesFailedRuns: a run holding a failed benchmark (a
// matched-accuracy b.Fatal) is void in every mode.
func TestRunRefusesFailedRuns(t *testing.T) {
	good := writeRun(t, map[string][]string{"BenchmarkF/decimal/v": tenSamples(10, 1, "")}, "")
	bad := writeRun(t, map[string][]string{"BenchmarkF/decimal/v": tenSamples(10, 1, "")},
		"--- FAIL: BenchmarkF/decimal/w\n    families_test.go:1: matched-accuracy mismatch\nFAIL\n")
	for _, args := range [][]string{{good, bad}, {bad, good}, {"-summary", bad}, {"-dominance", bad}} {
		out, code := runOut(t, args...)
		if code != 1 || !strings.Contains(out, "run is void") {
			t.Fatalf("%v: exit %d, output %q; want a refused void run", args, code, out)
		}
	}
	if out, code := runOut(t, "-summary", good); code != 0 {
		t.Fatalf("clean run refused: %s", out)
	}
}

// TestSummaryAggregatesOneRun pins the `make bench` aggregation of one run.
func TestSummaryAggregatesOneRun(t *testing.T) {
	path := writeRun(t, map[string][]string{"BenchmarkF/decimal/v": {"10 ns/op 0 allocs/op", "30 ns/op 0 allocs/op", "20 ns/op 0 allocs/op"}}, "")
	out, code := runOut(t, "-summary", path)
	if code != 0 {
		t.Fatalf("exit %d: %s", code, out)
	}
	if got := strings.Fields(lineOf(t, out, "BenchmarkF/decimal/v", "ns/op")); strings.Join(got[2:], " ") != "3 20.0 10.0 30.0 100.0%" {
		t.Fatalf("ns/op summary = %v", got)
	}
	if got := strings.Fields(lineOf(t, out, "BenchmarkF/decimal/v", "allocs/op")); strings.Join(got[2:], " ") != "3 0 0 0 0%" {
		t.Fatalf("allocs/op summary = %v", got)
	}
	if _, code := runOut(t, "-summary", "-dominance", path); code != 2 {
		t.Fatalf("two modes exit = %d, want 2", code)
	}
}

// TestDominanceRequiresNonOverlap: a dominance claim needs the reference's
// raw samples wholly below every incumbent's; a lower median with
// overlapping samples supports no claim.
func TestDominanceRequiresNonOverlap(t *testing.T) {
	path := writeRun(t, map[string][]string{
		"BenchmarkF1Parse/decimal/money6":     tenSamples(10, 1, "0 allocs/op"), // 10..19
		"BenchmarkF1Parse/apd/money6":         tenSamples(20, 1, "1 allocs/op"), // 20..29: separated
		"BenchmarkF1Parse/shop/money6":        tenSamples(19, 1, "0 allocs/op"), // 19..28: overlaps at 19
		"BenchmarkF6TightArith/decimal/add19": tenSamples(10, 1, "0 allocs/op"),
		"BenchmarkF6TightArith/apd/add19":     tenSamples(40, 1, "3 allocs/op"),
		"BenchmarkSolo/decimal/only":          tenSamples(1, 1, ""),
	}, "")
	out, code := runOut(t, "-dominance", path)
	if code != 0 {
		t.Fatalf("exit %d: %s", code, out)
	}
	if line := lineOf(t, out, "BenchmarkF1Parse/money6", "ns/op"); !strings.HasSuffix(line, "unseparated vs shop") || !strings.Contains(line, " shop ") {
		t.Fatalf("overlapping incumbent must block the claim: %q", line)
	}
	if line := lineOf(t, out, "BenchmarkF1Parse/money6", "allocs/op"); !strings.HasSuffix(line, "dominates, matches shop") {
		t.Fatalf("allocs verdict: %q", line)
	}
	if line := lineOf(t, out, "BenchmarkF6TightArith/add19", "ns/op"); !strings.HasSuffix(line, "  dominates") || !strings.Contains(line, "0.33x") {
		t.Fatalf("separated win: %q", line)
	}
	if strings.Contains(out, "BenchmarkSolo") {
		t.Fatalf("a family without incumbents was evaluated:\n%s", out)
	}
	short := writeRun(t, map[string][]string{
		"BenchmarkF/decimal/v": tenSamples(1, 1, "")[:9],
		"BenchmarkF/apd/v":     tenSamples(50, 1, ""),
	}, "")
	out, _ = runOut(t, "-dominance", short)
	if line := lineOf(t, out, "BenchmarkF/v", "ns/op"); !strings.HasSuffix(line, "insufficient (<10 samples)") {
		t.Fatalf("nine samples must not qualify: %q", line)
	}
}

// TestDominanceReportsShortfall: an incumbent whose samples lie wholly below
// the reference's is printed as a visible SHORTFALL, never omitted.
func TestDominanceReportsShortfall(t *testing.T) {
	path := writeRun(t, map[string][]string{
		"BenchmarkF6TightArith/decimal/div2dp":    tenSamples(200, 1, "0 allocs/op"),
		"BenchmarkF6TightArith/shopspring/div2dp": tenSamples(100, 1, "4 allocs/op"),
		"BenchmarkF6TightArith/apd/div2dp":        tenSamples(300, 1, "5 allocs/op"),
	}, "")
	out, code := runOut(t, "-dominance", path)
	if code != 0 {
		t.Fatalf("exit %d: %s", code, out)
	}
	line := lineOf(t, out, "BenchmarkF6TightArith/div2dp", "ns/op")
	if !strings.HasSuffix(line, "SHORTFALL vs shopspring") || !strings.Contains(line, "1.96x") {
		t.Fatalf("shortfall row = %q", line)
	}
	if line := lineOf(t, out, "BenchmarkF6TightArith/div2dp", "allocs/op"); !strings.HasSuffix(line, "  dominates") {
		t.Fatalf("allocation axis = %q", line)
	}
}

// writeLayouts writes one side of a layout-randomized A/B: for each layout,
// a "# layout" line and its rounds. rows maps a benchmark to one value list
// per layout (each value one round, as "N unit ..." pairs).
func writeLayouts(t *testing.T, rows map[string][][]string) string {
	t.Helper()
	names := make([]string, 0, len(rows))
	layouts := 0
	for name, ls := range rows {
		names = append(names, name)
		layouts = max(layouts, len(ls))
	}
	slices.Sort(names)
	var b strings.Builder
	for k := range layouts {
		b.WriteString("# layout " + strconv.Itoa(k+1) + "\n")
		for _, name := range names {
			if k >= len(rows[name]) {
				continue
			}
			for _, sample := range rows[name][k] {
				b.WriteString(name + "-32 1000 " + sample + "\n")
			}
		}
	}
	path := filepath.Join(t.TempDir(), "layouts.txt")
	if err := os.WriteFile(path, []byte(b.String()), 0o644); err != nil {
		t.Fatal(err)
	}
	return path
}

// layoutsOf builds per-layout rounds: layout k's value is base+k*step and
// each is repeated rounds times.
func layoutsOf(n int, base, step float64, rounds int, unit string) [][]string {
	out := make([][]string, n)
	for k := range out {
		v := strconv.FormatFloat(base+float64(k)*step, 'f', -1, 64) + " " + unit
		for range rounds {
			out[k] = append(out[k], v)
		}
	}
	return out
}

// TestLayoutsUseTheLayoutAsTheUnit: rounds of one
// layout are pseudo-replicates. Two sides whose layout means interleave
// are "~" in -layouts mode, although counting each round as a sample
// makes the same data significant; the reported n is the layout count.
func TestLayoutsUseTheLayoutAsTheUnit(t *testing.T) {
	a := writeLayouts(t, map[string][][]string{"BenchmarkF6/decimal/add19": layoutsOf(8, 100, 2, 10, "ns/op")}) // 100..114
	b := writeLayouts(t, map[string][][]string{"BenchmarkF6/decimal/add19": layoutsOf(8, 103, 2, 10, "ns/op")}) // 103..117
	out, code := runOut(t, "-layouts", a, b)
	if code != 0 {
		t.Fatalf("exit %d: %s", code, out)
	}
	line := lineOf(t, out, "BenchmarkF6/decimal/add19", "ns/op")
	if !strings.Contains(line, " 8+8 ") || !strings.HasSuffix(line, " ~") {
		t.Fatalf("interleaved layout means must be ~ over 8+8 layouts: %q", line)
	}
	perSample, _ := runOut(t, a, b)
	if l := lineOf(t, perSample, "BenchmarkF6/decimal/add19", "ns/op"); strings.Contains(l, " ~ ") || !strings.Contains(l, "80+80") {
		t.Fatalf("control: the per-sample test should (wrongly) separate the pseudo-replicates: %q", l)
	}
}

// TestLayoutsBandAndExactUnits: a significant time change inside
// the ±16% placement band is no claim, one outside it is; an exact unit
// (allocs/op, B/op) claims only a separated change; fewer than eight
// layouts per side is insufficient whatever the p; a result line outside
// any layout is refused.
func TestLayoutsBandAndExactUnits(t *testing.T) {
	a := writeLayouts(t, map[string][][]string{
		"BenchmarkIn":    layoutsOf(10, 100, 0.5, 2, "ns/op 64 B/op 2 allocs/op"),
		"BenchmarkOut":   layoutsOf(10, 100, 0.5, 2, "ns/op"),
		"BenchmarkBytes": layoutsOf(10, 100, 1, 2, "B/op"),
		"BenchmarkFew":   layoutsOf(7, 100, 0.5, 2, "ns/op"),
	})
	b := writeLayouts(t, map[string][][]string{
		"BenchmarkIn":    layoutsOf(10, 110, 0.5, 2, "ns/op 48 B/op 1 allocs/op"), // +10%, fewer allocations
		"BenchmarkOut":   layoutsOf(10, 70, 0.5, 2, "ns/op"),                      // -30%
		"BenchmarkBytes": layoutsOf(10, 105, 1, 2, "B/op"),                        // shifted, overlapping
		"BenchmarkFew":   layoutsOf(7, 50, 0.5, 2, "ns/op"),
	})
	out, code := runOut(t, "-layouts", a, b)
	if code != 0 {
		t.Fatalf("exit %d: %s", code, out)
	}
	for _, c := range []struct{ name, unit, verdict string }{
		{"BenchmarkIn", "ns/op", "inside band (no claim)"},
		{"BenchmarkIn", "allocs/op", "claim"},
		{"BenchmarkIn", "B/op", "claim"},
		{"BenchmarkOut", "ns/op", "claim"},
		{"BenchmarkBytes", "B/op", "significant, overlapping (no claim)"},
		{"BenchmarkFew", "ns/op", "insufficient (<8 layouts)"},
	} {
		if line := lineOf(t, out, c.name, c.unit); !strings.HasSuffix(line, " "+c.verdict) {
			t.Errorf("%s %s: %q, want verdict %q", c.name, c.unit, line, c.verdict)
		}
	}
	if !strings.Contains(out, "3 claim(s)") {
		t.Errorf("claim count:\n%s", out)
	}
	bare := writeRun(t, map[string][]string{"BenchmarkIn": {"1 ns/op"}}, "")
	if out, code := runOut(t, "-layouts", bare, b); code != 1 || !strings.Contains(out, "layout") {
		t.Fatalf("unlabeled input: exit %d %q", code, out)
	}
}

// TestLayoutsNullControlRefusesToClaim guards against an A=B dry run that
// reports a significant row: with -null a row significant outside
// the band is an instrument failure, printed as such, never as a claim,
// and the command exits 3; a clean null control passes with exit 0.
func TestLayoutsNullControlRefusesToClaim(t *testing.T) {
	a := writeLayouts(t, map[string][][]string{
		"BenchmarkX": layoutsOf(10, 100, 0.5, 2, "ns/op"),
		"BenchmarkY": layoutsOf(10, 100, 0.5, 2, "ns/op"),
	})
	b := writeLayouts(t, map[string][][]string{
		"BenchmarkX": layoutsOf(10, 60, 0.5, 2, "ns/op"),    // -40%: impossible between builds of one tree
		"BenchmarkY": layoutsOf(10, 100.2, 0.5, 2, "ns/op"), // interleaved
	})
	out, code := runOut(t, "-layouts", "-null", a, b)
	claimed := false
	for line := range strings.SplitSeq(out, "\n") {
		claimed = claimed || strings.HasPrefix(line, "Benchmark") && strings.HasSuffix(line, " claim")
	}
	if code != 3 || claimed || !strings.Contains(out, "NULL CONTROL FAILED: 1 row(s)") {
		t.Fatalf("exit %d, want 3 and no claim:\n%s", code, out)
	}
	if line := lineOf(t, out, "BenchmarkX", "ns/op"); !strings.HasSuffix(line, "NULL-CONTROL FAILURE") {
		t.Fatalf("row X: %q", line)
	}
	clean := writeLayouts(t, map[string][][]string{"BenchmarkX": layoutsOf(10, 100, 0.5, 2, "ns/op"), "BenchmarkY": layoutsOf(10, 100.2, 0.5, 2, "ns/op")})
	out, code = runOut(t, "-layouts", "-null", a, clean)
	if code != 0 || !strings.Contains(out, "null control passed") {
		t.Fatalf("clean null control: exit %d\n%s", code, out)
	}
	if _, code := runOut(t, "-null", a, b); code != 2 {
		t.Fatalf("-null without -layouts: exit %d, want 2", code)
	}
}

// TestLayoutsRefuseIncompleteInput: an
// omitted row or metric, invalid number, or underpowered null control cannot
// qualify the instrument. Ordinary historical comparison remains unchanged.
func TestLayoutsRefuseIncompleteInput(t *testing.T) {
	complete := writeLayouts(t, map[string][][]string{
		"BenchmarkX": layoutsOf(8, 100, 0, 1, "ns/op 0 B/op"),
		"BenchmarkY": layoutsOf(8, 100, 0, 1, "ns/op"),
	})
	for _, tc := range []struct {
		name string
		rows map[string][][]string
	}{
		{"missing row", map[string][][]string{"BenchmarkX": layoutsOf(8, 100, 0, 1, "ns/op 0 B/op")}},
		{"missing metric", map[string][][]string{"BenchmarkX": layoutsOf(8, 100, 0, 1, "ns/op"), "BenchmarkY": layoutsOf(8, 100, 0, 1, "ns/op")}},
		{"few constant layouts", map[string][][]string{"BenchmarkX": layoutsOf(7, 100, 0, 1, "ns/op 0 B/op"), "BenchmarkY": layoutsOf(7, 100, 0, 1, "ns/op")}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			b := writeLayouts(t, tc.rows)
			out, code := runOut(t, "-layouts", "-null", complete, b)
			if code != 1 || strings.Contains(out, "null control passed") {
				t.Fatalf("invalid input accepted: exit %d: %s", code, out)
			}
		})
	}
	for _, v := range []string{"NaN", "+Inf", "-1"} {
		t.Run(v, func(t *testing.T) {
			b := writeLayouts(t, map[string][][]string{"BenchmarkX": layoutsOf(8, 100, 0, 1, "ns/op 0 B/op"), "BenchmarkY": layoutsOf(8, 100, 0, 1, "ns/op")})
			data, err := os.ReadFile(b)
			if err != nil {
				t.Fatal(err)
			}
			data = bytes.ReplaceAll(data, []byte("100 ns/op"), []byte(v+" ns/op"))
			// Replace the independently constructed result value.
			if !bytes.Contains(data, []byte(v+" ns/op")) {
				t.Fatalf("fixture has no replaced value: %s", data)
			}
			if err := os.WriteFile(b, data, 0600); err != nil {
				t.Fatal(err)
			}
			out, code := runOut(t, "-layouts", "-null", complete, b)
			if code != 1 || strings.Contains(out, "null control passed") {
				t.Fatalf("invalid value accepted: exit %d: %s", code, out)
			}
		})
	}
	for _, args := range [][]string{{"-min-layouts", "7"}, {"-band", "NaN"}, {"-alpha", "NaN"}} {
		call := append([]string{"-layouts", "-null"}, args...)
		call = append(call, complete, complete)
		if out, code := runOut(t, call...); code != 2 {
			t.Fatalf("invalid protocol options %v: exit %d: %s", args, code, out)
		}
	}
}

// TestLayoutsRefuseMalformedResultLines:
// zero iterations, duplicate metrics and truncated metric pairs are not samples.
func TestLayoutsRefuseMalformedResultLines(t *testing.T) {
	valid := writeLayouts(t, map[string][][]string{"BenchmarkX": layoutsOf(8, 100, 0, 1, "ns/op")})
	for _, result := range []string{"BenchmarkX 0 100 ns/op", "BenchmarkX 1 100 ns/op 100 ns/op", "BenchmarkX 1 100 ns/op 123", "BenchmarkX 1 100", "BenchmarkX invalid 100 ns/op"} {
		t.Run(result, func(t *testing.T) {
			bad := filepath.Join(t.TempDir(), "bad.txt")
			var raw strings.Builder
			for i := range 8 {
				fmt.Fprintf(&raw, "# layout %d\n%s\n", i, result)
			}
			if err := os.WriteFile(bad, []byte(raw.String()), 0600); err != nil {
				t.Fatal(err)
			}
			out, code := runOut(t, "-layouts", "-null", valid, bad)
			if code != 1 || strings.Contains(out, "null control passed") {
				t.Fatalf("malformed samples accepted: exit%d: %s", code, out)
			}
		})
	}
}

// TestLayoutsZeroBaselineIsOutsideBand:
// hand-derived zero-to-positive time has unbounded relative change.
func TestLayoutsZeroBaselineIsOutsideBand(t *testing.T) {
	a := writeLayouts(t, map[string][][]string{"BenchmarkX": layoutsOf(8, 0, 0, 1, "ns/op")})
	b := writeLayouts(t, map[string][][]string{"BenchmarkX": layoutsOf(8, 100, 0, 1, "ns/op")})
	out, code := runOut(t, "-layouts", "-null", a, b)
	if code != 3 || !strings.Contains(out, "NULL CONTROL FAILED") {
		t.Fatalf("zero baseline hid instrument failure: exit%d: %s", code, out)
	}
}

// TestSlowerPExactWithTies pins slowerP to hand-derived permutation
// counts: a completely separated 8+8 slowdown has p = 1/C(16,8) = 1/12870
// with or without ties, the 2+2 split {1,2} versus {3,4} has p = 1/6,
// all-equal samples have p = 1, and a faster candidate has p = 1.
func TestSlowerPExactWithTies(t *testing.T) {
	for _, tc := range []struct {
		name string
		x, y []float64
		want float64
	}{
		{"separated", floats([]int{100, 101, 102, 103, 104, 105, 106, 107}), floats([]int{200, 201, 202, 203, 204, 205, 206, 207}), 1.0 / 12870},
		{"separated_with_ties", floats([]int{100, 100, 100, 101, 101, 102, 102, 102}), floats([]int{200, 200, 201, 201, 201, 201, 202, 202}), 1.0 / 12870},
		{"two_by_two", []float64{1, 2}, []float64{3, 4}, 1.0 / 6},
		{"all_equal", floats([]int{5, 5, 5, 5}), floats([]int{5, 5, 5, 5}), 1},
		{"faster", floats([]int{200, 201, 202, 203, 204, 205, 206, 207}), floats([]int{100, 101, 102, 103, 104, 105, 106, 107}), 1},
	} {
		if got := slowerP(tc.x, tc.y); math.Abs(got-tc.want) > 1e-12 {
			t.Errorf("%s: slowerP = %v, want %v", tc.name, got, tc.want)
		}
	}
}

// TestRegressionModeControlsFamilywiseError pins the regression check's
// multiple-comparison control: a portfolio run compares
// a few hundred ns/op rows, so a per-row test at alpha 0.05 fails noise-only
// runs. Holm–Bonferroni over the exact one-sided p keeps one moderate row
// among 226 from failing, while a completely separated slowdown fails with
// or without tied samples and names its row, and a separated speedup passes.
func TestRegressionModeControlsFamilywiseError(t *testing.T) {
	row := func(name string, values []int) string {
		var b strings.Builder
		for _, v := range values {
			fmt.Fprintf(&b, "%s-1 100 %d ns/op 0 B/op 0 allocs/op\n", name, v)
		}
		return b.String()
	}
	steady := []int{100, 101, 102, 103, 104, 105, 106, 107}
	base := []int{100, 102, 104, 106, 108, 110, 112, 114}
	moderate := []int{105, 107, 109, 111, 113, 115, 117, 119}
	if p := slowerP(floats(base), floats(moderate)); p > 0.05 || p <= 0.05/226 {
		t.Fatalf("fixture p = %v, want a per-row-significant but family-insignificant row", p)
	}
	for _, tc := range []struct {
		name      string
		old, cur  []int
		want      int
		failedRow bool
	}{
		{"moderate_row_among_226", base, moderate, 0, false},
		{"separated_row_among_226", base, []int{200, 201, 202, 203, 204, 205, 206, 207}, 1, true},
		{"separated_tied_row_among_226", base, []int{200, 200, 200, 201, 201, 201, 202, 202}, 1, true},
		{"separated_faster_row_among_226", []int{200, 201, 202, 203, 204, 205, 206, 207}, base, 0, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var a, b strings.Builder
			for i := range 225 {
				a.WriteString(row(fmt.Sprintf("BenchmarkRow%d", i), steady))
				b.WriteString(row(fmt.Sprintf("BenchmarkRow%d", i), steady))
			}
			a.WriteString(row("BenchmarkWorst", tc.old))
			b.WriteString(row("BenchmarkWorst", tc.cur))
			dir := t.TempDir()
			paths := []string{filepath.Join(dir, "a"), filepath.Join(dir, "b")}
			for i, data := range []string{a.String(), b.String()} {
				if err := os.WriteFile(paths[i], []byte(data), 0o644); err != nil {
					t.Fatal(err)
				}
			}
			var out, errs bytes.Buffer
			got := run(append([]string{"-regression"}, paths...), &out, &errs)
			if got != tc.want || tc.failedRow != strings.Contains(errs.String(), "BenchmarkWorst ns/op") || strings.Contains(errs.String(), "BenchmarkRow") {
				t.Fatalf("exit=%d want=%d; %s", got, tc.want, &errs)
			}
		})
	}
}

func floats(values []int) []float64 {
	out := make([]float64, len(values))
	for i, v := range values {
		out[i] = float64(v)
	}
	return out
}

func parse(r io.Reader) (samples, error) { return parseResults(r, false) }
