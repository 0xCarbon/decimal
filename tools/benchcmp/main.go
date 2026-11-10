// SPDX-License-Identifier: Apache-2.0

// Command benchcmp compares and aggregates `go test -bench` results using
// only the standard library. It is the repository's dependency-compliant
// stand-in for benchstat.
//
// Comparison (two files): for every benchmark and unit present in both inputs
// it reports the old and new medians, the relative change and a two-sided
// Mann-Whitney U p-value. A change whose p-value exceeds alpha is reported as
// "~" (no significant difference), never as a speedup or slowdown. Rows whose
// old and new observations are all identical (typically 0 allocs/op) are
// omitted.
//
// Summary (-summary, one file): the per-benchmark aggregation of one run,
// with the sample count, median, minimum, maximum and spread of each unit.
//
// Dominance (-dominance, one file): the per-family comparison against
// competing libraries. Names of
// the form Family/library/variant are grouped by family and variant; the
// reference library (-ref, default decimal) is compared on every unit with
// each incumbent that ran the same variant. The reference dominates only
// when its raw samples lie wholly below every incumbent's (non-overlapping
// distributions); an incumbent whose samples lie wholly below the
// reference's is a SHORTFALL, printed as a visible exception; any
// overlap is "unseparated", which supports neither claim. Fewer than
// -min-samples observations on either side is "insufficient".
//
// Layouts (-layouts, two files): a layout-randomized comparison of two
// source trees, which separates a code change from the effect of code
// placement (function and loop alignment) on timing. Each input holds
// several link layouts of one tree (test binaries built with
// -ldflags=-randlayout=<seed>), every result line after a "# layout ID"
// line belonging to layout ID. The statistical unit is the layout: each layout's samples are
// averaged (they are pseudo-replicates of one placement) and the two sets
// of layout means are compared with the Mann-Whitney U test; the delta is
// the change of the median layout mean. A row with fewer than -min-layouts
// layouts on either side is "insufficient" and never a claim. Every row
// gets a verdict: a time unit (ns/op) is a "claim" only when p <= alpha
// and the delta lies outside the placement band (-band, percent, default
// 16), and "inside band" when significant within it; an
// exact unit (B/op, allocs/op), which placement does not move, is a claim
// only when p <= alpha and the two sides' layout means are separated
// (no overlap). -null marks a null control (both inputs built from one
// tree): a claim is then a NULL-CONTROL FAILURE of the instrument, never a
// claim, and the command exits 3.
//
// A run containing a failed benchmark (a matched-accuracy check calls
// b.Fatal before timing) is void and refused in every mode.
//
// Usage:
//
//	go run ./tools/benchcmp [-alpha 0.05] old.txt new.txt
//	go run ./tools/benchcmp -layouts [-band 16] [-min-layouts 8] [-null] a.txt b.txt
//	go run ./tools/benchcmp -summary run.txt
//	go run ./tools/benchcmp -dominance [-ref decimal] [-min-samples 10] run.txt
//	go run ./tools/benchcmp -regression old.txt new.txt
//
// Regression (-regression, two files): fails on a significant slowdown, any
// allocation increase, or fewer than eight samples per side.
//
// Run each side at least 10 times, interleaved, so the test has enough
// power; with too few samples every row reports "~".
package main

import (
	"bufio"
	"cmp"
	"flag"
	"fmt"
	"io"
	"math"
	"os"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
)

// samples maps benchmark name -> unit -> observations, in first-seen order;
// labels holds the layout of each observation ("" before any "# layout"
// line).
type samples struct {
	order  []string
	units  map[string]map[string][]float64
	labels map[string]map[string][]string
}

var procSuffix = regexp.MustCompile(`-\d+$`)

func parseResults(r io.Reader, strict bool) (samples, error) {
	s := samples{units: map[string]map[string][]float64{}, labels: map[string]map[string][]string{}}
	scanner := bufio.NewScanner(r)
	scanner.Buffer(make([]byte, 1<<20), 1<<20)
	layout := ""
	for scanner.Scan() {
		line := scanner.Text()
		if id, ok := strings.CutPrefix(line, "# layout "); ok {
			if layout = strings.TrimSpace(id); layout == "" {
				return s, fmt.Errorf("empty layout label")
			}
			continue
		}
		if failed := strings.TrimSpace(line); strings.HasPrefix(failed, "--- FAIL") || strings.HasPrefix(failed, "FAIL") {
			return s, fmt.Errorf("run is void: %q (a failed benchmark's timing never counts)", failed)
		}
		fields := strings.Fields(line)
		if len(fields) == 0 || !strings.HasPrefix(fields[0], "Benchmark") {
			continue
		}
		if len(fields) < 4 || strict && len(fields)%2 != 0 {
			if strict {
				return s, fmt.Errorf("malformed benchmark result %q", line)
			}
			continue
		}
		iterations, err := strconv.ParseUint(fields[1], 10, 64)
		if err != nil || strict && iterations == 0 {
			if strict {
				return s, fmt.Errorf("invalid iteration count %q", fields[1])
			}
			continue // not a result line
		}
		name := procSuffix.ReplaceAllString(fields[0], "")
		byUnit, ok := s.units[name]
		if !ok {
			byUnit = map[string][]float64{}
			s.units[name] = byUnit
			s.labels[name] = map[string][]string{}
			s.order = append(s.order, name)
		}
		seenUnits := map[string]bool{}
		for i := 2; i+1 < len(fields); i += 2 {
			if strict && seenUnits[fields[i+1]] {
				return s, fmt.Errorf("%s: duplicate unit %q", name, fields[i+1])
			}
			seenUnits[fields[i+1]] = true
			v, err := strconv.ParseFloat(fields[i], 64)
			if err != nil {
				return s, fmt.Errorf("benchmark %s: value %q: %w", name, fields[i], err)
			}
			byUnit[fields[i+1]] = append(byUnit[fields[i+1]], v)
			s.labels[name][fields[i+1]] = append(s.labels[name][fields[i+1]], layout)
		}
	}
	return s, scanner.Err()
}

func median(xs []float64) float64 {
	sorted := slices.Clone(xs)
	slices.Sort(sorted)
	n := len(sorted)
	if n%2 == 1 {
		return sorted[n/2]
	}
	return (sorted[n/2-1] + sorted[n/2]) / 2
}

// mannWhitney returns the two-sided p-value for the null hypothesis that x
// and y come from the same distribution. Without ties it uses the exact U
// distribution; with ties it uses the tie-corrected normal approximation.
func mannWhitney(x, y []float64) float64 {
	n1, n2 := len(x), len(y)
	if n1 == 0 || n2 == 0 {
		return 1
	}
	type obs struct {
		v     float64
		fromX bool
	}
	all := make([]obs, 0, n1+n2)
	for _, v := range x {
		all = append(all, obs{v, true})
	}
	for _, v := range y {
		all = append(all, obs{v, false})
	}
	sort.Slice(all, func(i, j int) bool { return all[i].v < all[j].v })
	var rankX, tieTerm float64
	ties := false
	for i := 0; i < len(all); {
		j := i
		for j < len(all) && all[j].v == all[i].v {
			j++
		}
		rank := float64(i+j+1) / 2 // average of 1-based ranks i+1..j
		if t := float64(j - i); t > 1 {
			ties = true
			tieTerm += t*t*t - t
		}
		for k := i; k < j; k++ {
			if all[k].fromX {
				rankX += rank
			}
		}
		i = j
	}
	u := rankX - float64(n1*(n1+1))/2
	if !ties && n1*n2 <= 400 {
		return exactU(u, n1, n2)
	}
	n := float64(n1 + n2)
	mean := float64(n1*n2) / 2
	variance := float64(n1*n2) / 12 * ((n + 1) - tieTerm/(n*(n-1)))
	if variance <= 0 {
		return 1
	}
	z := (math.Abs(u-mean) - 0.5) / math.Sqrt(variance)
	if z < 0 {
		z = 0
	}
	return math.Min(1, math.Erfc(z/math.Sqrt2))
}

// slowerP is the exact one-sided permutation p-value that y is slower than
// x: the share of the C(n1+n2, n2) ways to label the pooled samples whose y
// rank sum is at least the observed one, with tied values sharing their
// midrank. It conditions on the ties, so a completely separated slowdown has
// p = 1/C(n1+n2, n2) whatever the ties, which the normal approximation
// cannot reach. The distribution is a subset-sum count over doubled
// midranks: O((n1+n2)·n2·Σrank) for the sample sizes used here.
func slowerP(x, y []float64) float64 {
	n1, n2 := len(x), len(y)
	if n1 == 0 || n2 == 0 {
		return 1
	}
	type obs struct {
		v     float64
		fromY bool
	}
	all := make([]obs, 0, n1+n2)
	for _, v := range x {
		all = append(all, obs{v, false})
	}
	for _, v := range y {
		all = append(all, obs{v, true})
	}
	sort.Slice(all, func(i, j int) bool { return all[i].v < all[j].v })
	ranks := make([]int, len(all)) // doubled midranks: i+j+1 for ranks i+1..j
	observed, total := 0, 0
	for i := 0; i < len(all); {
		j := i
		for j < len(all) && all[j].v == all[i].v {
			j++
		}
		for k := i; k < j; k++ {
			ranks[k] = i + j + 1
			if all[k].fromY {
				observed += i + j + 1
			}
		}
		total += (i + j + 1) * (j - i)
		i = j
	}
	// ways[k][s]: subsets of size k with doubled rank sum s.
	ways := make([][]float64, n2+1)
	for k := range ways {
		ways[k] = make([]float64, total+1)
	}
	ways[0][0] = 1
	for _, r := range ranks {
		for k := n2; k >= 1; k-- {
			for sum := total; sum >= r; sum-- {
				ways[k][sum] += ways[k-1][sum-r]
			}
		}
	}
	var tail, all2 float64
	for sum, w := range ways[n2] {
		all2 += w
		if sum >= observed {
			tail += w
		}
	}
	return tail / all2
}

// exactU counts the arrangements with a U at least as extreme as observed.
func exactU(u float64, n1, n2 int) float64 {
	// counts[i][j][k]: ways for i x-items and j y-items to reach U=k.
	maxU := n1 * n2
	prev := make([][]float64, n2+1)
	for j := range prev {
		prev[j] = make([]float64, maxU+1)
		prev[j][0] = 1
	}
	for i := 1; i <= n1; i++ {
		cur := make([][]float64, n2+1)
		for j := range cur {
			cur[j] = make([]float64, maxU+1)
			for k := 0; k <= maxU; k++ {
				// Largest item is x (contributes j) or y (contributes 0).
				if k >= j {
					cur[j][k] += prev[j][k-j]
				}
				if j > 0 {
					cur[j][k] += cur[j-1][k]
				}
			}
		}
		prev = cur
	}
	dist := prev[n2]
	var total, tail float64
	mean := float64(maxU) / 2
	deviation := math.Abs(u - mean)
	for k, ways := range dist {
		total += ways
		if math.Abs(float64(k)-mean) >= deviation-1e-9 {
			tail += ways
		}
	}
	return tail / total
}

func constant(x, y []float64) bool {
	for _, v := range slices.Concat(x, y) {
		if v != x[0] {
			return false
		}
	}
	return true
}

func format(v float64) string {
	switch a := math.Abs(v); {
	case a == 0:
		return "0"
	case a >= 100:
		return strconv.FormatFloat(v, 'f', 0, 64)
	case a >= 10:
		return strconv.FormatFloat(v, 'f', 1, 64)
	default:
		return strconv.FormatFloat(v, 'f', 2, 64)
	}
}

func compare(w io.Writer, old, cur samples, alpha float64) {
	fmt.Fprintf(w, "%-64s %-10s %12s %12s %9s %8s %s\n", "benchmark", "unit", "old", "new", "delta", "p", "n")
	for _, name := range old.order {
		newUnits, ok := cur.units[name]
		if !ok {
			continue
		}
		for _, unit := range sharedUnits(old.units[name], newUnits) {
			x, y := old.units[name][unit], newUnits[unit]
			if constant(x, y) {
				continue // identical observations carry no comparison
			}
			mo, mn := median(x), median(y)
			p := mannWhitney(x, y)
			delta := "~"
			if p <= alpha && mo != mn {
				delta = percent(mo, mn)
			}
			fmt.Fprintf(w, "%-64s %-10s %12s %12s %9s %8.3f %d+%d\n", name, unit, format(mo), format(mn), delta, p, len(x), len(y))
		}
	}
}

func sharedUnits(a, b map[string][]float64) []string {
	units := make([]string, 0, len(a))
	for unit := range a {
		if _, ok := b[unit]; ok {
			units = append(units, unit)
		}
	}
	slices.Sort(units)
	return units
}

func percent(from, to float64) string {
	if from == 0 {
		return "+inf%"
	}
	return fmt.Sprintf("%+.1f%%", (to-from)/from*100)
}

// layoutMeans averages the observations of each layout, in first-seen
// layout order; an observation outside any layout is an error.
func layoutMeans(xs []float64, labels []string) ([]float64, error) {
	var order []string
	sums, counts := map[string]float64{}, map[string]int{}
	for i, v := range xs {
		if math.IsNaN(v) || math.IsInf(v, 0) || v < 0 {
			return nil, fmt.Errorf("invalid benchmark value %v", v)
		}
		l := labels[i]
		if l == "" {
			return nil, fmt.Errorf("a result line precedes every \"# layout\" line")
		}
		if counts[l] == 0 {
			order = append(order, l)
		}
		sums[l] += v
		if math.IsInf(sums[l], 0) {
			return nil, fmt.Errorf("layout %q sum overflow", l)
		}
		counts[l]++
	}
	out := make([]float64, len(order))
	for i, l := range order {
		out[i] = sums[l] / float64(counts[l])
	}
	return out, nil
}

// exactUnit reports a unit that code placement cannot move.
func exactUnit(unit string) bool { return unit == "B/op" || unit == "allocs/op" }

// layoutOptions configures the layout-unit comparison.
type layoutOptions struct {
	alpha      float64
	band       float64 // percent; 0 disables the band
	minLayouts int
	null       bool
}

// compareLayouts is the tree A/B comparison with the layout as the
// unit; it returns the number of claims (null-control failures with -null).
func compareLayouts(w io.Writer, a, b samples, o layoutOptions) (int, error) {
	// Refuse incomplete input before printing a result or a null pass.
	if len(a.units) == 0 || len(a.units) != len(b.units) {
		return 0, fmt.Errorf("layout comparison requires identical nonempty benchmark rows")
	}
	for _, name := range a.order {
		bu, ok := b.units[name]
		if !ok || !slices.Equal(sortedUnits(a.units[name]), sortedUnits(bu)) {
			return 0, fmt.Errorf("%s: benchmark rows and units differ", name)
		}
		for _, side := range []samples{a, b} {
			for _, unit := range sortedUnits(side.units[name]) {
				means, err := layoutMeans(side.units[name][unit], side.labels[name][unit])
				if err != nil {
					return 0, fmt.Errorf("%s %s: %w", name, unit, err)
				}
				if o.null && len(means) < o.minLayouts {
					return 0, fmt.Errorf("%s %s: null control requires at least %d layouts per side", name, unit, o.minLayouts)
				}
			}
		}
	}
	if o.null {
		fmt.Fprintln(w, "NULL CONTROL: both sides are one tree; a claim below is a failure of the instrument, never a claim")
	}
	fmt.Fprintf(w, "unit: the layout (samples averaged per layout); Mann-Whitney U over layout means; alpha %.2f; time band ±%.0f%%; exact units need separation; at least %d layouts per side\n", o.alpha, o.band, o.minLayouts)
	fmt.Fprintf(w, "%-64s %-10s %12s %12s %9s %8s %-7s %s\n", "benchmark", "unit", "A", "B", "delta", "p", "layouts", "verdict")
	claims := 0
	for _, name := range a.order {
		bUnits, ok := b.units[name]
		if !ok {
			continue
		}
		for _, unit := range sharedUnits(a.units[name], bUnits) {
			x, err := layoutMeans(a.units[name][unit], a.labels[name][unit])
			if err != nil {
				return claims, fmt.Errorf("A %s: %w", name, err)
			}
			y, err := layoutMeans(bUnits[unit], b.labels[name][unit])
			if err != nil {
				return claims, fmt.Errorf("B %s: %w", name, err)
			}
			if len(x) >= o.minLayouts && len(y) >= o.minLayouts && constant(x, y) {
				continue
			}
			mx, my := median(x), median(y)
			p := mannWhitney(x, y)
			delta := percent(mx, my)
			verdict := "~"
			change := 0.0
			if mx != 0 {
				change = math.Abs((my - mx) / mx * 100)
			} else if my != 0 {
				change = math.Inf(1)
			}
			significant := p <= o.alpha && mx != my
			switch {
			case len(x) < o.minLayouts || len(y) < o.minLayouts:
				verdict = fmt.Sprintf("insufficient (<%d layouts)", o.minLayouts)
			case !significant:
			case exactUnit(unit) && separation(x, y) != 0,
				!exactUnit(unit) && change > o.band:
				verdict = "claim"
				if o.null {
					verdict = "NULL-CONTROL FAILURE"
				}
				claims++
			case exactUnit(unit):
				verdict = "significant, overlapping (no claim)"
			default:
				verdict = "inside band (no claim)"
				if o.null {
					verdict = "inside band (placement residual)"
				}
			}
			fmt.Fprintf(w, "%-64s %-10s %12s %12s %9s %8.4f %-7s %s\n", name, unit, format(mx), format(my), delta, p, fmt.Sprintf("%d+%d", len(x), len(y)), verdict)
		}
	}
	switch {
	case o.null && claims > 0:
		fmt.Fprintf(w, "NULL CONTROL FAILED: %d row(s) significant outside the band between two builds of one tree\n", claims)
	case o.null:
		fmt.Fprintln(w, "null control passed: no row significant outside the band")
	default:
		fmt.Fprintf(w, "%d claim(s)\n", claims)
	}
	return claims, nil
}

func run(args []string, stdout, stderr io.Writer) int {
	flags := flag.NewFlagSet("benchcmp", flag.ContinueOnError)
	flags.SetOutput(stderr)
	alpha := flags.Float64("alpha", 0.05, "significance level for reporting a change")
	summaryMode := flags.Bool("summary", false, "aggregate one run: n, median, min, max and spread per benchmark and unit")
	dominanceMode := flags.Bool("dominance", false, "compare each family with the other libraries on one run")
	ref := flags.String("ref", "decimal", "reference library for -dominance")
	minSamples := flags.Int("min-samples", 10, "samples per side below which -dominance reports insufficient")
	layoutsMode := flags.Bool("layouts", false, "compare two layout-randomized trees with the layout as the unit")
	band := flags.Float64("band", 16, "-layouts: placement band in percent; a significant time change within it is no claim")
	minLayouts := flags.Int("min-layouts", 8, "-layouts: layouts per side below which a row is insufficient")
	null := flags.Bool("null", false, "-layouts: a null control (one tree on both sides): a claim is an instrument failure, exit 3")
	regression := flags.Bool("regression", false, "fail on significant slowdown, any allocation increase, or incomplete 8+8 samples")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	want := 2
	if *summaryMode || *dominanceMode {
		want = 1
	}
	modes := 0
	for _, m := range []bool{*summaryMode, *dominanceMode, *layoutsMode, *regression} {
		if m {
			modes++
		}
	}
	if flags.NArg() != want || modes > 1 || *null && !*layoutsMode || math.IsNaN(*alpha) || math.IsInf(*alpha, 0) || *alpha <= 0 || *alpha > 1 || (*layoutsMode || *regression) && *alpha > 0.05 || math.IsNaN(*band) || math.IsInf(*band, 0) || *band < 0 || *layoutsMode && *minLayouts < 8 {
		fmt.Fprintln(stderr, "usage: benchcmp [-alpha 0.05] old.txt new.txt | -layouts [-band 16] [-min-layouts 8] [-null] a.txt b.txt | -summary run.txt | -dominance [-ref decimal] [-min-samples 10] run.txt")
		return 2
	}
	sets := make([]samples, want)
	for i, path := range flags.Args() {
		f, err := os.Open(path)
		if err != nil {
			fmt.Fprintln(stderr, "benchcmp:", err)
			return 1
		}
		sets[i], err = parseResults(f, *layoutsMode || *regression)
		_ = f.Close()
		if err != nil {
			fmt.Fprintf(stderr, "benchcmp: %s: %v\n", path, err)
			return 1
		}
		if len(sets[i].order) == 0 {
			fmt.Fprintf(stderr, "benchcmp: %s: no benchmark result lines\n", path)
			return 1
		}
	}
	switch {
	case *regression:
		if err := regressionCheck(stdout, sets[0], sets[1], *alpha); err != nil {
			fmt.Fprintln(stderr, "benchcmp:", err)
			return 1
		}
	case *summaryMode:
		summarize(stdout, sets[0])
	case *dominanceMode:
		dominance(stdout, sets[0], *ref, *minSamples)
	case *layoutsMode:
		claims, err := compareLayouts(stdout, sets[0], sets[1], layoutOptions{alpha: *alpha, band: *band, minLayouts: *minLayouts, null: *null})
		if err != nil {
			fmt.Fprintln(stderr, "benchcmp:", err)
			return 1
		}
		if *null && claims > 0 {
			return 3
		}
	default:
		compare(stdout, sets[0], sets[1], *alpha)
	}
	return 0
}

// regressionCheck is a non-regression check, not a performance claim.
// Both runs must cover the same rows with at least eight valid samples per arm.
// B/op and allocs/op are exact: any increase in their sorted samples fails.
// Timings compare many rows at once, so a slower median fails only when the
// exact one-sided rank-sum p that the candidate is slower (slowerP)
// survives Holm–Bonferroni over every ns/op row at alpha; a per-row test
// would fail noise-only runs of a large portfolio. Callers comparing several
// families (profiles, baselines) divide alpha among them.
func regressionCheck(w io.Writer, a, b samples, alpha float64) error {
	if len(a.units) == 0 || len(a.units) != len(b.units) {
		return fmt.Errorf("regression: identical nonempty rows required")
	}
	type timing struct {
		name   string
		p      float64
		slower bool
	}
	var failures []string
	var timings []timing
	for _, name := range a.order {
		bu, ok := b.units[name]
		if !ok || !slices.Equal(sortedUnits(a.units[name]), sortedUnits(bu)) {
			return fmt.Errorf("regression: %s rows/units differ", name)
		}
		for _, unit := range []string{"ns/op", "B/op", "allocs/op"} {
			x, y := a.units[name][unit], bu[unit]
			if len(x) < 8 || len(x) != len(y) {
				return fmt.Errorf("regression: %s %s needs equal 8+8 or more samples", name, unit)
			}
			for _, values := range [][]float64{x, y} {
				for _, v := range values {
					if math.IsNaN(v) || math.IsInf(v, 0) || v < 0 || unit == "ns/op" && v == 0 {
						return fmt.Errorf("regression: %s %s invalid value", name, unit)
					}
				}
			}
			if unit == "ns/op" {
				timings = append(timings, timing{name, slowerP(x, y), median(y) > median(x)})
				continue
			}
			p := mannWhitney(x, y)
			bad := false
			sx, sy := slices.Clone(x), slices.Clone(y)
			slices.Sort(sx)
			slices.Sort(sy)
			for i := range sx {
				if sy[i] > sx[i] {
					bad = true
				}
			}
			fmt.Fprintf(w, "%s %s A=%g B=%g p=%g regression=%t\n", name, unit, median(x), median(y), p, bad)
			if bad {
				failures = append(failures, name+" "+unit)
			}
		}
	}
	// Holm–Bonferroni: walk the p-values in ascending order, rejecting
	// p(i) <= alpha/(m-i) until the first one that is not rejected.
	order := make([]int, len(timings))
	for i := range order {
		order[i] = i
	}
	slices.SortStableFunc(order, func(i, j int) int { return cmp.Compare(timings[i].p, timings[j].p) })
	rejected := make([]bool, len(timings))
	for k, i := range order {
		if timings[i].p > alpha/float64(len(timings)-k) {
			break
		}
		rejected[i] = true
	}
	for i, t := range timings {
		x, y := a.units[t.name]["ns/op"], b.units[t.name]["ns/op"]
		bad := rejected[i] && t.slower
		fmt.Fprintf(w, "%s ns/op A=%g B=%g p=%g holm=%t regression=%t\n", t.name, median(x), median(y), t.p, rejected[i], bad)
		if bad {
			failures = append(failures, t.name+" ns/op")
		}
	}
	if len(failures) > 0 {
		return fmt.Errorf("regressions: %s", strings.Join(failures, ", "))
	}
	return nil
}

func sortedUnits(byUnit map[string][]float64) []string {
	units := make([]string, 0, len(byUnit))
	for unit := range byUnit {
		units = append(units, unit)
	}
	slices.Sort(units)
	return units
}

// summarize prints one run's per-benchmark aggregation (the `make bench`
// output): the sample count, median, extremes and spread, (max-min)/median.
func summarize(w io.Writer, s samples) {
	fmt.Fprintf(w, "%-64s %-10s %4s %12s %12s %12s %8s\n", "benchmark", "unit", "n", "median", "min", "max", "spread")
	for _, name := range s.order {
		for _, unit := range sortedUnits(s.units[name]) {
			xs := s.units[name][unit]
			m := median(xs)
			spread := "0%"
			if m != 0 {
				spread = fmt.Sprintf("%.1f%%", (slices.Max(xs)-slices.Min(xs))/m*100)
			}
			fmt.Fprintf(w, "%-64s %-10s %4d %12s %12s %12s %8s\n", name, unit, len(xs), format(m), format(slices.Min(xs)), format(slices.Max(xs)), spread)
		}
	}
}

// separation classifies the reference sample set against one incumbent's:
// -1 when every reference sample is below every incumbent sample, +1 when
// every incumbent sample is below every reference sample, 0 on overlap. The
// caller reports two constant, equal sets (typically allocs/op) as a match.
func separation(ref, inc []float64) int {
	switch {
	case slices.Max(ref) < slices.Min(inc):
		return -1
	case slices.Max(inc) < slices.Min(ref):
		return 1
	}
	return 0
}

// dominance evaluates the dominance bar on one run. Benchmarks named
// Family/library/variant are grouped by family and variant; the reference
// is compared unit by unit with every incumbent that ran the same variant.
func dominance(w io.Writer, s samples, ref string, minSamples int) {
	type group struct {
		key  string
		libs map[string]string // library -> benchmark name
		seen []string
	}
	var groups []*group
	index := map[string]*group{}
	for _, name := range s.order {
		parts := strings.SplitN(name, "/", 3)
		if len(parts) < 3 {
			continue
		}
		key := parts[0] + "/" + parts[2]
		g, ok := index[key]
		if !ok {
			g = &group{key: key, libs: map[string]string{}}
			index[key] = g
			groups = append(groups, g)
		}
		if _, dup := g.libs[parts[1]]; !dup {
			g.seen = append(g.seen, parts[1])
		}
		g.libs[parts[1]] = name
	}
	fmt.Fprintf(w, "%-56s %-10s %12s %-14s %12s %8s %8s  %s\n", "family/variant", "unit", ref, "best incumbent", "median", "ratio", "p", "verdict")
	for _, g := range groups {
		refName, ok := g.libs[ref]
		if !ok || len(g.libs) < 2 {
			continue
		}
		for _, unit := range sortedUnits(s.units[refName]) {
			x := s.units[refName][unit]
			best, bestMedian := "", math.Inf(1)
			var shortfall, unseparated, matched []string
			insufficient := len(x) < minSamples
			compared := 0
			for _, lib := range g.seen {
				if lib == ref {
					continue
				}
				y, ok := s.units[g.libs[lib]][unit]
				if !ok {
					continue
				}
				compared++
				if m := median(y); m < bestMedian {
					best, bestMedian = lib, m
				}
				if len(y) < minSamples {
					insufficient = true
					continue
				}
				switch separation(x, y) {
				case 0:
					if constant(x, y) {
						matched = append(matched, lib)
					} else {
						unseparated = append(unseparated, lib)
					}
				case 1:
					shortfall = append(shortfall, lib)
				}
			}
			if compared == 0 {
				continue
			}
			verdict := "dominates"
			switch {
			case insufficient:
				verdict = fmt.Sprintf("insufficient (<%d samples)", minSamples)
			case len(shortfall) > 0:
				verdict = "SHORTFALL vs " + strings.Join(shortfall, ",")
			case len(unseparated) > 0:
				verdict = "unseparated vs " + strings.Join(unseparated, ",")
			case len(matched) == compared:
				verdict = "matches"
			case len(matched) > 0:
				verdict = "dominates, matches " + strings.Join(matched, ",")
			}
			ratio := "-"
			if bestMedian != 0 {
				ratio = fmt.Sprintf("%.2fx", median(x)/bestMedian)
			}
			p := mannWhitney(x, s.units[g.libs[best]][unit])
			fmt.Fprintf(w, "%-56s %-10s %12s %-14s %12s %8s %8.3f  %s\n", g.key, unit, format(median(x)), best, format(bestMedian), ratio, p, verdict)
		}
	}
}

func main() { os.Exit(run(os.Args[1:], os.Stdout, os.Stderr)) }
