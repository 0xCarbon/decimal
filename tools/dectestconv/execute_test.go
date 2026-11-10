// SPDX-License-Identifier: Apache-2.0

package main

import (
	"errors"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/0xCarbon/decimal"
)

// corpusDirEnv names the provisioned corpus directory. make conformance
// sets it after provisioning; a plain go test leaves it unset and the corpus
// test skips.
const corpusDirEnv = "DECIMAL_DECTEST_DIR"

func loadRepoManifest(t *testing.T) *corpusManifest {
	t.Helper()
	m, err := loadCorpusManifest(repoPath(t, "testdata", "dectest", "manifest.json"))
	if err != nil {
		t.Fatalf("loading manifest: %v", err)
	}
	return m
}

// runCase executes one case and fails the test on a harness error or a
// disagreement with want.
func runCase(t *testing.T, tc testCase, want expectation) {
	t.Helper()
	got, err := execute(tc)
	if err != nil {
		t.Fatalf("harness: %v", err)
	}
	msg, err := check(got, want)
	if err != nil {
		t.Fatalf("harness: %v", err)
	}
	if msg != "" {
		t.Errorf("%s %s %q %v: %s", tc.ID, tc.Op, tc.Operands, tc.Directives, msg)
	}
}

// TestDecTestCorpus classifies the provisioned corpus against the manifest
// (any drift fails the manifest subtest) and runs every adopted and
// re-derived case as the subtest <suite>/<case id>.
func TestDecTestCorpus(t *testing.T) {
	dir := os.Getenv(corpusDirEnv)
	if dir == "" {
		t.Skip(corpusDirEnv + " is unset: the corpus runs under make conformance")
	}
	m := loadRepoManifest(t)
	byFile, computed, drift, err := classifyCorpus(dir, m)
	t.Run("manifest", func(t *testing.T) {
		if err != nil {
			t.Fatalf("classification: %v", err)
		}
		drift = append(drift, compareClassificationList(repoPath(t, filepath.FromSlash(m.ClassificationList)), classificationList(byFile, computed))...)
		for _, d := range drift {
			t.Error(d)
		}
		if len(computed) != len(m.Categories) {
			t.Errorf("classified %d suite files, the manifest has %d", len(computed), len(m.Categories))
		}
	})
	if err != nil || len(drift) > 0 {
		t.FailNow()
	}
	for _, cat := range m.Categories {
		if cat.Executed == 0 {
			continue
		}
		t.Run(strings.TrimSuffix(cat.File, ".decTest"), func(t *testing.T) {
			for _, c := range byFile[cat.Archive+"/"+cat.File] {
				if !executes(c.Class) {
					continue
				}
				t.Run(c.ID, func(t *testing.T) { runCase(t, c.testCase, c.Want) })
			}
		})
	}
}

// TestDecTestFixtures runs every committed manifest fixture (original
// constructions: converter samples and the replacement error-path and
// condition-emission vectors) as the subtest <fixture id>, after checking
// its content hash. It needs no corpus, so it runs in every plain go test.
func TestDecTestFixtures(t *testing.T) {
	fixtures, err := loadFixtures(loadRepoManifest(t), repoPath(t), t.Name())
	if err != nil {
		t.Fatalf("fixtures: %v", err)
	}
	for _, id := range slices.Sorted(maps.Keys(fixtures)) {
		tc := fixtures[id]
		t.Run(id, func(t *testing.T) {
			runCase(t, tc, expectation{Expected: tc.Expected, Conditions: tc.Conditions})
		})
	}
}

// TestExecutorDirectiveMapping pins the directive mapping on hand-derived
// cases, one per operation and mode (original constructions), and a
// deliberate disagreement per comparison leg so check cannot pass vacuously.
func TestExecutorDirectiveMapping(t *testing.T) {
	guarded := map[string]string{"precision": "3", "rounding": "half_even", "maxexponent": "9", "minexponent": "-9"}
	with := func(kv ...string) map[string]string {
		d := map[string]string{}
		maps.Copy(d, guarded)
		for i := 0; i < len(kv); i += 2 {
			d[kv[i]] = kv[i+1]
		}
		return d
	}
	cases := []struct {
		op       string
		d        map[string]string
		operands []string
		want     expectation
	}{
		{"add", guarded, []string{"1.25", "1.00"}, expectation{"2.25", nil}},
		{"add", guarded, []string{"1.235", "1"}, expectation{"2.24", []string{"Inexact", "Rounded"}}},
		{"add", with("rounding", "half_up"), []string{"-1.235", "-1"}, expectation{"-2.24", []string{"Inexact", "Rounded"}}},
		{"add", with("rounding", "half_down"), []string{"1.235", "1"}, expectation{"2.23", []string{"Inexact", "Rounded"}}},
		{"subtract", with("rounding", "down"), []string{"1", "0.0001"}, expectation{"0.999", []string{"Inexact", "Rounded"}}},
		{"fma", guarded, []string{"1.01", "1.01", "-1.02"}, expectation{"0.0001", nil}},
		{"fma", guarded, []string{"1.0", "2.0", "3.00"}, expectation{"5.00", nil}},
		{"fma", guarded, []string{"1.25", "1.01", "0.001"}, expectation{"1.26", []string{"Inexact", "Rounded"}}},
		{"multiply", with("rounding", "up"), []string{"1.01", "1.01"}, expectation{"1.03", []string{"Inexact", "Rounded"}}},
		{"divide", with("rounding", "ceiling"), []string{"-2", "3"}, expectation{"-0.666", []string{"Inexact", "Rounded"}}},
		{"divide", with("rounding", "floor"), []string{"-2", "3"}, expectation{"-0.667", []string{"Inexact", "Rounded"}}},
		{"divide", guarded, []string{"1", "0"}, expectation{refusedExpectation, []string{"Division_by_zero"}}},
		{"divideint", guarded, []string{"7", "2"}, expectation{"3", nil}},
		{"remainder", guarded, []string{"7.0", "2"}, expectation{"1.0", nil}},
		{"remaindernear", guarded, []string{"7", "2"}, expectation{"-1", nil}},
		{"divideint", guarded, []string{"1000", "1"}, expectation{refusedExpectation, []string{"Division_impossible"}}},
		{"remainder", guarded, []string{"1", "0"}, expectation{refusedExpectation, []string{"Division_by_zero"}}},
		{"quantize", guarded, []string{"2.5", "1E+0"}, expectation{"2", []string{"Inexact", "Rounded"}}},
		{"rescale", guarded, []string{"2.5", "0"}, expectation{"2", []string{"Inexact", "Rounded"}}},
		{"tointegral", guarded, []string{"2.5"}, expectation{"2", nil}},
		{"tointegralx", guarded, []string{"2.5"}, expectation{"2", []string{"Inexact", "Rounded"}}},
		{"squareroot", guarded, []string{"2"}, expectation{"1.41", []string{"Inexact", "Rounded"}}},
		{"power", guarded, []string{"2", "10"}, expectation{"1.02E+3", []string{"Inexact", "Rounded"}}},
		{"plus", guarded, []string{"1.2345"}, expectation{"1.23", []string{"Inexact", "Rounded"}}},
		{"minus", guarded, []string{"1.2"}, expectation{"-1.2", nil}},
		{"abs", guarded, []string{"-1.2"}, expectation{"1.2", nil}},
		{"reduce", guarded, []string{"1.200"}, expectation{"1.2", []string{"Rounded"}}},
		{"max", guarded, []string{"1.0", "1"}, expectation{"1", nil}},
		{"min", guarded, []string{"1.0", "1"}, expectation{"1.0", nil}},
		{"compare", guarded, []string{"1.0", "2"}, expectation{"-1", nil}},
		{"tosci", guarded, []string{"1.2345"}, expectation{"1.23", []string{"Inexact", "Rounded"}}},
		{"apply", guarded, []string{"12E+5"}, expectation{"1.2E+6", nil}},
		{"copy", guarded, []string{"-1.2345"}, expectation{"-1.2345", nil}},
		{"copyabs", guarded, []string{"-1.2345"}, expectation{"1.2345", nil}},
		{"copynegate", guarded, []string{"1.2345"}, expectation{"-1.2345", nil}},
		{"add", with("rounding", "exact"), []string{"1.235", "1"}, expectation{refusedExpectation, []string{"Inexact"}}},
		{"add", with("precision", "3", "maxexponent", "2", "minexponent", "-2"), []string{"999", "1"}, expectation{"999", []string{"Inexact", "Overflow", "Rounded"}}},
		{"add", with("minexponent", "-2"), []string{"0.00123", "0"}, expectation{"0.0012", []string{"Inexact", "Rounded", "Subnormal", "Underflow"}}},
		{"add", map[string]string{"precision": "9", "rounding": "half_even"}, []string{"1E+30", "1"}, expectation{"1.00000000E+30", []string{"Inexact", "Rounded"}}},
	}
	for _, c := range cases {
		tc := testCase{ID: "map", Op: c.op, Directives: c.d, Operands: c.operands}
		got, err := execute(tc)
		if err != nil {
			t.Fatalf("%s %v: harness: %v", c.op, c.operands, err)
		}
		msg, err := check(got, c.want)
		if err != nil || msg != "" {
			t.Errorf("%s %v %v: %s %v", c.op, c.operands, c.d, msg, err)
		}
		// Each leg of check must be able to fail.
		for _, wrong := range []expectation{
			{c.want.Expected + "1", c.want.Conditions},
			{c.want.Expected, append(slices.Clone(c.want.Conditions), "Clamped")},
		} {
			if msg, _ := check(got, wrong); msg == "" {
				t.Errorf("%s %v: check accepted the wrong expectation %v", c.op, c.operands, wrong)
			}
		}
	}
}

// TestExecutorHarnessErrors pins that a harness problem is never read as a
// library outcome: an unmapped operation, a wrong operand count, an
// unparsable operand, a mode without an adopted counterpart and an unknown
// condition name are harness errors.
func TestExecutorHarnessErrors(t *testing.T) {
	d := map[string]string{"precision": "9", "rounding": "half_even"}
	for _, tc := range []testCase{
		{Op: "logb", Directives: d, Operands: []string{"1"}},
		{Op: "add", Directives: d, Operands: []string{"1"}},
		{Op: "add", Directives: d, Operands: []string{"1", "x"}},
		{Op: "add", Directives: map[string]string{"precision": "9", "rounding": "05up"}, Operands: []string{"1", "1"}},
		{Op: "add", Directives: map[string]string{"precision": "9", "rounding": "half_even", "maxexponent": "9"}, Operands: []string{"1", "1"}},
		{Op: "scaleb", Directives: d, Operands: []string{"2", "1"}},
	} {
		if _, err := execute(tc); err == nil {
			t.Errorf("%s %v %v: harness error not reported", tc.Op, tc.Operands, tc.Directives)
		}
	}
	if _, err := check(outcome{Text: "1"}, expectation{"1", []string{"Lost_digits"}}); err == nil {
		t.Error("unknown condition name accepted")
	}
	if c := errorConditions(&decimal.Error{Condition: decimal.Inexact}); c != decimal.Inexact {
		t.Errorf("Error conditions %v", c)
	}
}

// TestReplacementVectorsCoverExcludedFamilies pins the replacement
// coverage: the committed fixtures hold a refusal vector per condition class
// the finite-only space turns into an error (including the Exact
// rounding-refused class), condition-emission vectors for Overflow,
// Underflow and Subnormal, and a vector for each excluded divergence family.
// TestDecTestFixtures executes them.
func TestReplacementVectorsCoverExcludedFamilies(t *testing.T) {
	m := loadRepoManifest(t)
	refused := map[string]bool{}
	emitted := map[string]bool{}
	ops := map[string]bool{}
	overflowModes := map[string]bool{}
	fixtures, err := loadFixtures(m, repoPath(t), "TestDecTestFixtures")
	if err != nil {
		t.Fatal(err)
	}
	sources := map[string]string{}
	for _, fx := range m.Fixtures {
		sources[fx.ID] = fx.Source
	}
	for id, tc := range fixtures {
		if !strings.Contains(sources[id], "replacement") {
			continue
		}
		ops[tc.Op+":"+tc.Directives["rounding"]] = true
		if slices.Contains(tc.Conditions, "Overflow") {
			overflowModes[tc.Directives["rounding"]] = true
		}
		for _, c := range tc.Conditions {
			if tc.Expected == refusedExpectation {
				refused[c] = true
			} else {
				emitted[c] = true
			}
		}
		switch {
		case strings.HasPrefix(tc.Operands[0], "-0") && tc.Expected != refusedExpectation:
			emitted["signed-zero"] = true
		case tc.Op == "power" && strings.Trim(tc.Operands[0], "-0.E+") == "" && !strings.HasPrefix(tc.Operands[1], "-"):
			emitted["zero-power"] = true
		case strings.HasPrefix(tc.Op, "tointegral") && strings.Contains(tc.Operands[0], "E+"):
			emitted["integral-exponent-zero"] = true
		case tc.Expected != refusedExpectation && strings.HasPrefix(tc.Expected, "0E"):
			emitted["unclamped-zero"] = true
		}
	}
	for _, c := range []string{"Conversion_syntax", "Division_by_zero", "Division_undefined", "Invalid_operation", "Invalid_context", "Inexact"} {
		if !refused[c] {
			t.Errorf("no refusal vector for %s", c)
		}
	}
	for _, c := range []string{"Overflow", "Underflow", "Subnormal", "signed-zero", "zero-power", "integral-exponent-zero", "unclamped-zero"} {
		if !emitted[c] {
			t.Errorf("no emission vector for %s", c)
		}
	}
	for _, m := range []string{"half_even", "half_up", "half_down", "down", "up", "ceiling", "floor"} {
		if !overflowModes[m] {
			t.Errorf("no Overflow vector under %s", m)
		}
	}
	if !ops["add:exact"] || !ops["divide:exact"] {
		t.Error("the Exact rounding-refused class needs arithmetic vectors")
	}
}

// The executor is the decTest directive mapping: it runs one
// adopted decTest case through the library's public entry points and
// compares text and conditions exactly. It never classifies: corpus.go does,
// from the case text alone.
//
// Directive mapping:
//   - precision → context precision; rounding → mode names (half_even
//     TiesToEven, half_up TiesAwayFromZero, half_down TiesTowardZero, down
//     TowardZero, up AwayFromZero, ceiling TowardPositiveInfinity, floor
//     TowardNegativeInfinity); exact → Exact (repository constructions only;
//     decTest has no such mode); maxexponent/minexponent → exponent guards
//     (absent together means unguarded); no traps.
//   - Operands are exact (extended: 1 never rounds an operand); results are
//     compared by canonical text, which is GDA to-scientific-string, and
//     conditions by set equality with Increased and Decreased masked.
//
// Operation mapping (GDA name → library):
//
//	add, subtract, multiply, divide  → {Add,Sub,Mul,Div}WithContext
//	fma                              → FMAWithContext (one rounding)
//	divideint, remainder, remaindernear → {Quo,Rem,RemNear}WithContext
//	quantize                         → QuantizeWithContext(rhs exponent)
//	rescale                          → QuantizeWithContext(rhs value)
//	tointegralx                      → RoundToIntegralWithContext
//	tointegral                       → RoundToIntegralWithContext, Inexact and
//	                                   Rounded not signalled (GDA round-to-integral-value)
//	squareroot                       → SqrtWithContext
//	power (integral rhs in int32)    → PowWithContext
//	power (any other rhs)            → PowDecimalWithContext
//	exp, ln, log10                   → {Exp,Ln,Log10}WithContext with the
//	                                   mode forced to TiesToEven: GDA rounds
//	                                   these half-even whatever the context
//	                                   says
//	plus                             → RoundToPrecisionWithContext
//	minus, abs                       → Neg / Abs, then RoundToPrecisionWithContext
//	reduce                           → RoundToPrecisionWithContext, then Reduce
//	max, min                         → Max / Min, then RoundToPrecisionWithContext
//	compare                          → Compare as -1, 0 or 1
//	tosci, apply                     → ParseWithContext, then canonical text
//	copy, copyabs, copynegate        → the operand, Abs, Neg (exact; no context)
//
// A repository construction may expect "refused": the operation must fail,
// and the listed conditions are the error's condition set (error-path
// vectors).

var operandCounts = map[string]int{
	"add": 2, "subtract": 2, "multiply": 2, "divide": 2, "quantize": 2,
	"fma": 3, "divideint": 2, "remainder": 2, "remaindernear": 2,
	"rescale": 2, "power": 2, "max": 2, "min": 2, "compare": 2,
}

var roundingModes = map[string]decimal.RoundingMode{
	"half_even": decimal.TiesToEven, "half_up": decimal.TiesAwayFromZero,
	"half_down": decimal.TiesTowardZero, "down": decimal.TowardZero,
	"up": decimal.AwayFromZero, "ceiling": decimal.TowardPositiveInfinity,
	"floor": decimal.TowardNegativeInfinity, "exact": decimal.Exact,
}

var conditionBits = map[string]decimal.Conditions{
	"clamped": decimal.Clamped, "conversion_syntax": decimal.ConversionSyntax,
	"division_by_zero": decimal.DivisionByZero, "division_impossible": decimal.DivisionImpossible,
	"division_undefined": decimal.DivisionUndefined, "inexact": decimal.Inexact,
	"insufficient_storage": decimal.InsufficientStorage, "invalid_context": decimal.InvalidContext,
	"invalid_operation": decimal.InvalidOperation, "overflow": decimal.Overflow,
	"rounded": decimal.Rounded, "subnormal": decimal.Subnormal, "underflow": decimal.Underflow,
}

const directionBits = decimal.Increased | decimal.Decreased

// outcome is what one execution produced.
type outcome struct {
	Text       string
	Conditions decimal.Conditions
	Err        error
}

// contextFor maps a case's directives to a library context.
func contextFor(d map[string]string) (decimal.Context, error) {
	p, err := strconv.ParseUint(d["precision"], 10, 32)
	if err != nil {
		return decimal.Context{}, fmt.Errorf("precision %q: %w", d["precision"], err)
	}
	mode, ok := roundingModes[d["rounding"]]
	if !ok {
		return decimal.Context{}, fmt.Errorf("rounding %q has no adopted mode", d["rounding"])
	}
	maxText, hasMax := d["maxexponent"]
	minText, hasMin := d["minexponent"]
	if hasMax != hasMin {
		return decimal.Context{}, errors.New("maxexponent and minexponent must be given together")
	}
	var guards *decimal.ExponentGuards
	if hasMax {
		emax, err := strconv.ParseInt(maxText, 10, 32)
		if err != nil {
			return decimal.Context{}, fmt.Errorf("maxexponent %q: %w", maxText, err)
		}
		emin, err := strconv.ParseInt(minText, 10, 32)
		if err != nil {
			return decimal.Context{}, fmt.Errorf("minexponent %q: %w", minText, err)
		}
		guards = &decimal.ExponentGuards{Emin: int32(emin), Emax: int32(emax)}
	}
	return decimal.NewContext(uint32(p), mode, guards, 0)
}

// execute runs one case through the mapped entry point. A harness problem
// (unmapped operation, wrong operand count, unparsable operand) is an error
// of the harness, returned separately from the library's outcome.
func execute(tc testCase) (outcome, error) {
	op := strings.ToLower(tc.Op)
	if !executedOps[op] {
		return outcome{}, fmt.Errorf("operation %s is not mapped", tc.Op)
	}
	want := operandCounts[op]
	if want == 0 {
		want = 1
	}
	if len(tc.Operands) != want {
		return outcome{}, fmt.Errorf("operation %s takes %d operands, case has %d", tc.Op, want, len(tc.Operands))
	}
	ctx, err := contextFor(tc.Directives)
	if err != nil {
		if _, ok := errors.AsType[*decimal.Error](err); ok {
			return outcome{Err: err}, nil
		}
		return outcome{}, err
	}
	if op == "tosci" || op == "apply" {
		v, c, err := decimal.ParseWithContext(tc.Operands[0], ctx)
		return result(v, c, err), nil
	}
	ops := make([]decimal.Decimal, len(tc.Operands))
	for i, text := range tc.Operands {
		v, err := decimal.Parse(text)
		if err != nil {
			return outcome{}, fmt.Errorf("operand %d %q: %w", i+1, text, err)
		}
		ops[i] = v
	}
	x := ops[0]
	var (
		v decimal.Decimal
		c decimal.Conditions
	)
	switch op {
	case "add":
		v, c, err = x.AddWithContext(ops[1], ctx)
	case "subtract":
		v, c, err = x.SubWithContext(ops[1], ctx)
	case "fma":
		v, c, err = x.FMAWithContext(ops[1], ops[2], ctx)
	case "multiply":
		v, c, err = x.MulWithContext(ops[1], ctx)
	case "divide":
		v, c, err = x.DivWithContext(ops[1], ctx)
	case "divideint":
		v, c, err = x.QuoWithContext(ops[1], ctx)
	case "remainder":
		v, c, err = x.RemWithContext(ops[1], ctx)
	case "remaindernear":
		v, c, err = x.RemNearWithContext(ops[1], ctx)
	case "quantize":
		v, c, err = x.QuantizeWithContext(ops[1].Exponent(), ctx)
	case "rescale":
		n, nerr := int32Value(ops[1])
		if nerr != nil {
			return outcome{}, nerr
		}
		v, c, err = x.QuantizeWithContext(n, ctx)
	case "tointegral", "tointegralx":
		v, c, err = x.RoundToIntegralWithContext(ctx)
		if op == "tointegral" {
			c &^= decimal.Inexact | decimal.Rounded
		}
	case "squareroot":
		v, c, err = x.SqrtWithContext(ctx)
	case "power":
		if n, nerr := int32Value(ops[1]); nerr == nil {
			v, c, err = x.PowWithContext(n, ctx)
		} else {
			v, c, err = x.PowDecimalWithContext(ops[1], ctx)
		}
	case "exp", "ln", "log10":
		if ctx.Rounding() != decimal.TiesToEven {
			d := maps.Clone(tc.Directives)
			d["rounding"] = "half_even"
			if ctx, err = contextFor(d); err != nil {
				return outcome{}, err
			}
		}
		switch op {
		case "exp":
			v, c, err = x.ExpWithContext(ctx)
		case "ln":
			v, c, err = x.LnWithContext(ctx)
		default:
			v, c, err = x.Log10WithContext(ctx)
		}
	case "plus":
		v, c, err = x.RoundToPrecisionWithContext(ctx)
	case "minus":
		v, c, err = x.Neg().RoundToPrecisionWithContext(ctx)
	case "abs":
		v, c, err = x.Abs().RoundToPrecisionWithContext(ctx)
	case "reduce":
		v, c, err = x.RoundToPrecisionWithContext(ctx)
		v = v.Reduce()
	case "max":
		v, c, err = x.Max(ops[1]).RoundToPrecisionWithContext(ctx)
	case "min":
		v, c, err = x.Min(ops[1]).RoundToPrecisionWithContext(ctx)
	case "compare":
		return outcome{Text: strconv.Itoa(x.Compare(ops[1]))}, nil
	case "copy":
		v = x
	case "copyabs":
		v = x.Abs()
	case "copynegate":
		v = x.Neg()
	}
	return result(v, c, err), nil
}

func result(v decimal.Decimal, c decimal.Conditions, err error) outcome {
	if err != nil {
		return outcome{Err: err}
	}
	return outcome{Text: v.String(), Conditions: c}
}

// int32Value reads an integral operand that selects an exponent or a power.
func int32Value(d decimal.Decimal) (int32, error) {
	n, err := d.Int64()
	if err != nil || n != int64(int32(n)) {
		return 0, fmt.Errorf("operand %s is not an int32 integer", d)
	}
	return int32(n), nil
}

// errorConditions is the condition set an error reports.
func errorConditions(err error) decimal.Conditions {
	if e, ok := errors.AsType[*decimal.Error](err); ok {
		return e.Condition
	}
	if e, ok := errors.AsType[*decimal.Error](err); ok {
		return e.Condition
	}
	if e, ok := errors.AsType[*decimal.Error](err); ok {
		return e.Condition
	}
	if e, ok := errors.AsType[*decimal.Error](err); ok {
		return e.Condition
	}
	return 0
}

// wantConditions maps decTest condition names to the library's bits.
func wantConditions(names []string) (decimal.Conditions, error) {
	var c decimal.Conditions
	for _, name := range names {
		bit, ok := conditionBits[strings.ToLower(name)]
		if !ok {
			return 0, fmt.Errorf("condition %q has no library counterpart", name)
		}
		c |= bit
	}
	return c, nil
}

// check compares an outcome with an expectation and describes a mismatch;
// the empty string is agreement.
func check(got outcome, want expectation) (string, error) {
	wantC, err := wantConditions(want.Conditions)
	if err != nil {
		return "", err
	}
	if want.Expected == refusedExpectation {
		switch {
		case got.Err == nil:
			return fmt.Sprintf("got %s [%v], want a refusal [%v]", got.Text, got.Conditions, wantC), nil
		case errorConditions(got.Err) != wantC:
			return fmt.Sprintf("refused with [%v] (%v), want [%v]", errorConditions(got.Err), got.Err, wantC), nil
		}
		return "", nil
	}
	if got.Err != nil {
		return fmt.Sprintf("refused: %v [%v], want %s [%v]", got.Err, errorConditions(got.Err), want.Expected, wantC), nil
	}
	if gotC := got.Conditions &^ directionBits; got.Text != want.Expected || gotC != wantC {
		return fmt.Sprintf("got %s [%v], want %s [%v]", got.Text, gotC, want.Expected, wantC), nil
	}
	return "", nil
}
