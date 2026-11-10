// SPDX-License-Identifier: Apache-2.0

package main

import (
	"archive/zip"
	"encoding/json"
	"maps"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// TestClassifyCaseRules pins every per-case rule on original constructions
// (exceptional-value cases are exclusions of the finite-only value space,
// never skipped silently; each divergence family has its own reason code).
func TestClassifyCaseRules(t *testing.T) {
	base := map[string]string{"precision": "9", "rounding": "half_even", "maxexponent": "999", "minexponent": "-999", "extended": "1"}
	with := func(k, v string) map[string]string {
		d := map[string]string{}
		maps.Copy(d, base)
		d[k] = v
		return d
	}
	override := map[string]caseOverride{"ov1": {Adoption: classRederived, Reason: "zero-power-one"}}
	cases := []struct {
		id, op   string
		d        map[string]string
		operands []string
		expected string
		conds    []string
		class    string
		reason   string
	}{
		{"a1", "add", base, []string{"1", "2"}, "3", nil, classAdopted, "directive-mapped"},
		{"ov1", "power", base, []string{"0", "0"}, "NaN", []string{"Invalid_operation"}, classRederived, "zero-power-one"},
		{"c1", "add", with("clamp", "1"), []string{"1", "2"}, "3", nil, classExclusion, "clamp"},
		{"s2", "add", base, []string{"1", "2"}, "3", []string{"Lost_digits"}, classExclusion, "subset"},
		{"m1", "add", with("rounding", "05up"), []string{"1", "2"}, "3", nil, classExclusion, "mode-05up"},
		{"t1", "exp", base, []string{"1"}, "2.71828183", []string{"Inexact", "Rounded"}, classAdopted, "directive-mapped"},
		{"t2", "power", base, []string{"4", "0.5"}, "2.00000000", []string{"Inexact", "Rounded"}, classAdopted, "directive-mapped"},
		{"p1", "divideint", base, []string{"7", "2"}, "3", nil, classAdopted, "directive-mapped"},
		{"p2", "fma", base, []string{"1", "2", "3"}, "5", nil, classAdopted, "directive-mapped"},
		{"d1", "toEng", base, []string{"1E+3"}, "1E+3", nil, classExclusion, "display-format"},
		{"n1", "samequantum", base, []string{"1", "2"}, "1", nil, classExclusion, "not-in-catalogue"},
		{"e1", "add", base, []string{"#", "1"}, "3", nil, classExclusion, "encoding-operand"},
		{"e2", "quantize", base, []string{"64#1", "1"}, "1", nil, classExclusion, "encoding-operand"},
		{"x1", "add", base, []string{"Inf", "1"}, "Infinity", nil, classExclusion, "non-finite"},
		{"x2", "divide", base, []string{"Inf", "0"}, "Infinity", nil, classExclusion, "non-finite"},
		{"x3", "add", base, []string{"sNaN12", "1"}, "NaN12", []string{"Invalid_operation"}, classExclusion, "non-finite"},
		{"x4", "tosci", base, []string{"-nan"}, "-NaN", nil, classExclusion, "non-finite"},
		{"x5", "max", base, []string{"NaN", "1"}, "1", nil, classExclusion, "non-finite"},
		{"k1", "add", base, []string{"0E-1100", "0"}, "0E-1007", []string{"Clamped"}, classExclusion, "clamped"},
		{"z1", "add", base, []string{"-0", "-0"}, "-0", nil, classExclusion, "signed-zero"},
		{"z2", "max", base, []string{"-0E+2", "0E1"}, "0E+1", nil, classExclusion, "signed-zero"},
		{"z3", "add", base, []string{"-0", "1"}, "1", nil, classAdopted, "directive-mapped"},
		{"i1", "tointegralx", base, []string{"12E+3"}, "1.2E+4", nil, classExclusion, "integral-exponent-zero"},
		{"i3", "tointegral", base, []string{"56E+1"}, "5.6E+2", nil, classExclusion, "integral-exponent-zero"},
		{"i4", "tointegral", base, []string{"560E+0"}, "560", nil, classAdopted, "directive-mapped"},
		{"i2", "tointegral", base, []string{"1.5"}, "2", nil, classAdopted, "directive-mapped"},
		{"w1", "power", base, []string{"1", "2147483648"}, "1", nil, classAdopted, "directive-mapped"},
		{"w2", "power", base, []string{"2", "2.00"}, "4", nil, classAdopted, "directive-mapped"},
		{"w3", "power", base, []string{"1", "-2147483648"}, "1", nil, classAdopted, "directive-mapped"},
		{"y1", "add", base, []string{"1E+2147483648", "1"}, "1E+2147483648", []string{"Rounded", "Inexact"}, classExclusion, "exponent-domain"},
		{"r1", "divide", base, []string{"1", "0"}, "Infinity", []string{"Division_by_zero"}, classAdopted, "exceptional-refusal"},
		{"r2", "divide", base, []string{"0", "0"}, "NaN", []string{"Division_undefined"}, classAdopted, "exceptional-refusal"},
		{"r3", "squareroot", base, []string{"-1"}, "NaN", []string{"Invalid_operation"}, classAdopted, "exceptional-refusal"},
		{"r4", "tosci", base, []string{"1..2"}, "NaN", []string{"Conversion_syntax"}, classAdopted, "exceptional-refusal"},
		{"r5", "add", base, []string{"9E+999", "9E+999"}, "Infinity", []string{"Overflow", "Inexact", "Rounded"}, classExclusion, "non-finite"},
		{"r6", "quantize", base, []string{"1", "1E+2147483648"}, "NaN", []string{"Invalid_operation"}, classExclusion, "exponent-domain"},
		{"q1", "rescale", base, []string{"1", "2.5"}, "NaN", []string{"Invalid_operation"}, classExclusion, "rescale-exponent-domain"},
		{"q2", "rescale", base, []string{"1", "3000000000"}, "NaN", []string{"Invalid_operation"}, classExclusion, "rescale-exponent-domain"},
		{"q3", "rescale", base, []string{"1.25", "-1.0"}, "1.2", []string{"Inexact", "Rounded"}, classAdopted, "directive-mapped"},
		{"s3", "add", with("extended", "0"), []string{"1", "2"}, "3", nil, classAdopted, "subset-coincident"},
		{"s4", "add", with("extended", "0"), []string{"1", "2"}, "4", nil, classExclusion, "subset"},
		{"s5", "samequantum", with("extended", "0"), []string{"1", "2"}, "1", nil, classExclusion, "not-in-catalogue"},
		{"s6", "add", map[string]string{"precision": "9", "rounding": "half_even", "maxexponent": "99", "minexponent": "-99", "extended": "0"}, []string{"1", "2"}, "3", nil, classExclusion, "subset"},
	}
	twins := map[string]verdict{}
	for _, tw := range []testCase{
		{Op: "add", Directives: base, Operands: []string{"1", "2"}, Expected: "3"},
		{Op: "samequantum", Directives: base, Operands: []string{"1", "2"}, Expected: "1"},
	} {
		class, reason := classifyCase(tw, nil, nil)
		twins[coincidenceKey(tw)] = verdict{class, reason}
	}
	for _, c := range cases {
		tc := testCase{ID: c.id, Op: c.op, Directives: c.d, Operands: c.operands, Expected: c.expected, Conditions: c.conds}
		class, reason := classifyCase(tc, override, twins)
		if class != c.class || reason != c.reason {
			t.Errorf("%s %s %v -> %s: got %s/%s, want %s/%s", c.id, c.op, c.operands, c.expected, class, reason, c.class, c.reason)
		}
	}
}

// TestClassificationListShowsRuleChanges pins the committed per-case list:
// an unchanged list is no drift; a moved id is named.
func TestClassificationListShowsRuleChanges(t *testing.T) {
	dir, m := syntheticCorpus(t)
	byFile, computed, _, err := classifyCorpus(dir, m)
	if err != nil {
		t.Fatal(err)
	}
	list := classificationList(byFile, computed)
	path := filepath.Join(t.TempDir(), "list.txt")
	if err := os.WriteFile(path, []byte(list), 0o644); err != nil {
		t.Fatal(err)
	}
	if d := compareClassificationList(path, list); d != nil {
		t.Fatalf("unchanged list reported drift: %v", d)
	}
	if !strings.Contains(list, "corpus.zip/alpha.decTest\tintentional-exclusion\tsigned-zero\tal002\n") {
		t.Fatalf("list does not group ids by reason:\n%s", list)
	}
	moved := strings.Replace(list, "signed-zero", "non-finite", 1)
	if d := compareClassificationList(path, moved); len(d) == 0 || !strings.Contains(strings.Join(d, "\n"), "al002") {
		t.Fatalf("moved id not named: %v", d)
	}
}

// TestNumericTextHelpers pins the independent numeric-string readers the
// rules use (they never call the library under test).
func TestNumericTextHelpers(t *testing.T) {
	for _, c := range []struct {
		s    string
		exp  int64
		ok   bool
		zero bool
	}{
		{"1.23E+5", 3, true, false}, {"-0.00", -2, true, true}, {"-0E-7", -7, true, true},
		{".5", -1, true, false}, {"5.", 0, true, false}, {"1e-2", -2, true, false},
		{"1..2", 0, false, false}, {"E5", 0, false, false}, {"1E", 0, false, false}, {"1E+-2", 0, false, false},
	} {
		e, ok := storedExponent(c.s)
		if ok != c.ok || (ok && e != c.exp) {
			t.Errorf("storedExponent(%q) = %d, %v; want %d, %v", c.s, e, ok, c.exp, c.ok)
		}
		if got := negativeZero(c.s); got != (c.zero && strings.HasPrefix(c.s, "-")) {
			t.Errorf("negativeZero(%q) = %v", c.s, got)
		}
	}
	if e, ok := storedExponent("1E+99999999999999999999999"); !ok || e <= 1<<62 {
		t.Errorf("huge exponent not saturated: %d %v", e, ok)
	}
	for _, c := range []struct {
		s        string
		n        int64
		integral bool
	}{
		{"3", 3, true}, {"-3.000", -3, true}, {"2.5", 0, false}, {"1E+3", 1000, true},
		{"0.5E+1", 5, true}, {"-0E-9", 0, true}, {"1E-400", 0, false}, {"1E+400", 1 << 62, true},
	} {
		n, integral, ok := integralValue(c.s)
		if !ok || integral != c.integral || (integral && n != c.n) {
			t.Errorf("integralValue(%q) = %d, %v, %v; want %d, %v", c.s, n, integral, ok, c.n, c.integral)
		}
	}
}

// syntheticCorpus writes an archive of original-construction suites and a
// manifest whose category rows are computed from it, so the drift checks
// run without the downloaded corpus.
func syntheticCorpus(t *testing.T) (dir string, m *corpusManifest) {
	t.Helper()
	dir = t.TempDir()
	files := map[string]string{
		"alpha.decTest": "precision: 9\nrounding: half_even\nmaxexponent: 99\nminexponent: -99\n" +
			"al001 add 1 2 -> 3\nal002 add -0 -0 -> -0\nal003 add NaN 1 -> NaN\nal004 divideint 7 2 -> 3\n",
		"beta.decTest": "precision: 9\nrounding: half_even\nbe001 exp 1 -> 2.71828183 Inexact Rounded\n",
		"gamma0.decTest": "extended: 0\nprecision: 9\nrounding: half_even\nmaxexponent: 99\nminexponent: -99\n" +
			"ga001 add 1 2 -> 3\nga002 add 1.23456789012 0 -> 1.23456789 Inexact Rounded Lost_digits\n",
	}
	f, err := os.Create(filepath.Join(dir, "corpus.zip"))
	if err != nil {
		t.Fatal(err)
	}
	zw := zip.NewWriter(f)
	for _, name := range []string{"alpha.decTest", "beta.decTest", "gamma0.decTest"} {
		w, err := zw.Create(name)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := w.Write([]byte(files[name])); err != nil {
			t.Fatal(err)
		}
	}
	if err := zw.Close(); err != nil {
		t.Fatal(err)
	}
	if err := f.Close(); err != nil {
		t.Fatal(err)
	}
	repo := loadRepoManifest(t)
	m = &corpusManifest{SchemaVersion: 2, Reasons: repo.Reasons, Runner: repo.Runner, Categories: []category{
		{Archive: "corpus.zip", File: "alpha.decTest", Adoption: "adopted", Cites: "test"},
		{Archive: "corpus.zip", File: "beta.decTest", Adoption: "excluded", Reason: "not-in-catalogue", Cites: "test"},
		{Archive: "corpus.zip", File: "gamma0.decTest", Adoption: "adopted", Cites: "test"},
	}}
	_, computed, _, err := classifyCorpus(dir, m)
	if err != nil {
		t.Fatal(err)
	}
	m.Categories = computed
	return dir, m
}

// TestClassifyCorpusDetectsDrift is the manifest-integrity control: a clean synthetic corpus has no drift; a missing
// archive is a loud rejection; an edited case, an extra or missing suite, a
// changed count and a stale override each produce drift.
func TestClassifyCorpusDetectsDrift(t *testing.T) {
	dir, m := syntheticCorpus(t)
	if _, _, drift, err := classifyCorpus(dir, m); err != nil || len(drift) != 0 {
		t.Fatalf("clean corpus: %v %v", err, drift)
	}
	alpha := m.Categories[0]
	if alpha.Cases != 4 || alpha.Executed != 2 || alpha.Classes[classExclusion] != 2 ||
		alpha.Reasons["signed-zero"] != 1 || alpha.Reasons["non-finite"] != 1 || alpha.Reasons["directive-mapped"] != 2 || alpha.Reasons["operation-pending"] != 0 {
		t.Fatalf("synthetic classification: %+v", alpha)
	}
	if gamma := m.Categories[2]; gamma.Reasons["subset-coincident"] != 1 || gamma.Reasons["subset"] != 1 || gamma.Executed != 1 {
		t.Fatalf("subset coincidence: %+v", gamma)
	}
	t.Run("missing archive", func(t *testing.T) {
		_, _, _, err := classifyCorpus(t.TempDir(), m)
		if err == nil || !isRejection(err) || !strings.Contains(err.Error(), "never a skip") {
			t.Fatalf("missing corpus not rejected loudly: %v", err)
		}
	})
	mutations := map[string]func(m *corpusManifest){
		"changed count":     func(m *corpusManifest) { m.Categories[0].Executed++ },
		"changed digest":    func(m *corpusManifest) { m.Categories[0].Classification = strings.Repeat("0", 64) },
		"changed file hash": func(m *corpusManifest) { m.Categories[1].SHA256 = strings.Repeat("0", 64) },
		"missing category":  func(m *corpusManifest) { m.Categories = m.Categories[:1] },
		"stale category": func(m *corpusManifest) {
			m.Categories = append(m.Categories, category{Archive: "corpus.zip", File: "gamma.decTest"})
		},
		"reclassified reason": func(m *corpusManifest) { m.Categories[1].Reasons = map[string]int{"display-format": 1} },
	}
	for name, mutate := range mutations {
		t.Run(name, func(t *testing.T) {
			mm := *m
			mm.Categories = append([]category(nil), m.Categories...)
			mutate(&mm)
			if _, _, drift, err := classifyCorpus(dir, &mm); err == nil && len(drift) == 0 {
				t.Fatal("drift not detected")
			}
		})
	}
	t.Run("stale override", func(t *testing.T) {
		mm := *m
		mm.Cases = []caseOverride{{ID: "al999", Archive: "corpus.zip", File: "alpha.decTest", Adoption: classRederived, Reason: "zero-power-one"}}
		if _, _, drift, err := classifyCorpus(dir, &mm); err == nil && len(drift) == 0 {
			t.Fatal("override of an absent case accepted")
		}
	})
	t.Run("override original", func(t *testing.T) {
		byFile, _, _, err := classifyCorpus(dir, m)
		if err != nil {
			t.Fatal(err)
		}
		mm := *m
		mm.Cases = []caseOverride{{ID: "al001", Archive: "corpus.zip", File: "alpha.decTest", SHA256: byFile["corpus.zip/alpha.decTest"][0].ContentSHA,
			Adoption: classRederived, Reason: "zero-power-one", Original: expectation{Expected: "4"}}}
		if _, _, _, err := classifyCorpus(dir, &mm); err == nil || !strings.Contains(err.Error(), "preserved original") {
			t.Fatalf("override with an edited original accepted: %v", err)
		}
	})
	t.Run("override applies the re-derived expectation", func(t *testing.T) {
		byFile, _, _, err := classifyCorpus(dir, m)
		if err != nil {
			t.Fatal(err)
		}
		src := byFile["corpus.zip/alpha.decTest"][1]
		mm := *m
		mm.Cases = []caseOverride{{ID: src.ID, Archive: "corpus.zip", File: "alpha.decTest", SHA256: src.ContentSHA, Adoption: classRederived, Reason: "zero-power-one",
			Original: expectation{Expected: src.Expected, Conditions: src.Conditions}, Rederived: &expectation{Expected: "0"}}}
		got, _, _, err := classifyCorpus(dir, &mm)
		if err != nil {
			t.Fatal(err)
		}
		c := got["corpus.zip/alpha.decTest"][1]
		if c.Class != classRederived || c.Want.Expected != "0" || c.Expected != "-0" {
			t.Fatalf("re-derived case %s: class %s, want %+v, corpus expectation %q", c.ID, c.Class, c.Want, c.Expected)
		}
	})
	t.Run("override hash", func(t *testing.T) {
		mm := *m
		mm.Cases = []caseOverride{{ID: "al001", Archive: "corpus.zip", File: "alpha.decTest", SHA256: strings.Repeat("0", 64), Adoption: classRederived, Reason: "zero-power-one"}}
		if _, _, _, err := classifyCorpus(dir, &mm); err == nil || !strings.Contains(err.Error(), "corpus drift") {
			t.Fatalf("override content drift accepted: %v", err)
		}
	})
}

// TestLoadFixturesChecksContent pins that a committed fixture runs only
// with the content hash the manifest records and only when present.
func TestLoadFixturesChecksContent(t *testing.T) {
	m := loadRepoManifest(t)
	if _, err := loadFixtures(m, repoPath(t), "TestDecTestFixtures"); err != nil {
		t.Fatalf("committed fixtures: %v", err)
	}
	for name, mutate := range map[string]func(fx *manifestFixture){
		"hash":    func(fx *manifestFixture) { fx.SHA256 = strings.Repeat("0", 64) },
		"absent":  func(fx *manifestFixture) { fx.ID = "zz999" },
		"no test": func(fx *manifestFixture) { fx.Test = "TestNothing" },
	} {
		t.Run(name, func(t *testing.T) {
			mm := *m
			mm.Fixtures = []manifestFixture{m.Fixtures[0]}
			mutate(&mm.Fixtures[0])
			if _, err := loadFixtures(&mm, repoPath(t), "TestDecTestFixtures"); err == nil {
				t.Fatal("mutated fixture accepted")
			}
		})
	}
}

// TestCorpusManifestValidation pins the schema-2 manifest rules on the
// committed manifest and on single-field mutations of it.
func TestCorpusManifestValidation(t *testing.T) {
	path := repoPath(t, "testdata", "dectest", "manifest.json")
	if _, err := loadCorpusManifest(path); err != nil {
		t.Fatalf("committed manifest rejected: %v", err)
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	mutate := func(fn func(m map[string]any)) string {
		var m map[string]any
		if err := json.Unmarshal(raw, &m); err != nil {
			t.Fatal(err)
		}
		fn(m)
		blob, _ := json.Marshal(m)
		p := filepath.Join(t.TempDir(), "m.json")
		if err := os.WriteFile(p, blob, 0o644); err != nil {
			t.Fatal(err)
		}
		return p
	}
	first := func(m map[string]any, key string) map[string]any { return m[key].([]any)[0].(map[string]any) }
	for name, fn := range map[string]func(m map[string]any){
		"schema 1":                  func(m map[string]any) { m["schema_version"] = 1 },
		"unknown field":             func(m map[string]any) { m["extra"] = true },
		"reason without citation":   func(m map[string]any) { m["reasons"].(map[string]any)["clamp"].(map[string]any)["cites"] = "" },
		"reason with unknown class": func(m map[string]any) { m["reasons"].(map[string]any)["clamp"].(map[string]any)["class"] = "wholesale" },
		"excluded without reason": func(m map[string]any) {
			first(m, "categories")["adoption"] = "excluded"
			delete(first(m, "categories"), "reason")
		},
		"adoption vocabulary":       func(m map[string]any) { first(m, "categories")["adoption"] = "vendored" },
		"category without citation": func(m map[string]any) { first(m, "categories")["cites"] = "" },
		"override class mismatch":   func(m map[string]any) { first(m, "cases")["adoption"] = "corpus-beta" },
		"override lost original": func(m map[string]any) {
			first(m, "cases")["original"] = map[string]any{"expected": "", "conditions": []any{}}
		},
		"override lost generator": func(m map[string]any) { first(m, "cases")["provenance"] = map[string]any{"command": "x"} },
		"fixture excluded":        func(m map[string]any) { first(m, "fixtures")["adoption"] = "intentional-exclusion" },
		"fixture without test":    func(m map[string]any) { first(m, "fixtures")["test"] = "" },
		"runner without test":     func(m map[string]any) { m["runner"].(map[string]any)["test"] = "" },
	} {
		t.Run(name, func(t *testing.T) {
			if _, err := loadCorpusManifest(mutate(fn)); err == nil {
				t.Fatal("mutated manifest accepted")
			}
		})
	}
}

// TestCorpusBytesStayLocal pins the licensing posture: the manifest
// provisions into the gitignored .cache/ tree, every committed .decTest
// file is an original construction that says so, and the manifest carries
// no operand text of any corpus case (only ids, hashes, counts and the
// preserved expectations of re-derived cases).
func TestCorpusBytesStayLocal(t *testing.T) {
	m := loadRepoManifest(t)
	if m.Sources.LocalDir != ".cache/dectest" {
		t.Fatalf("corpus directory %q is not under .cache/", m.Sources.LocalDir)
	}
	ignore, err := os.ReadFile(repoPath(t, ".gitignore"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(ignore), "\n/.cache/\n") {
		t.Fatal(".gitignore does not ignore /.cache/")
	}
	err = filepath.WalkDir(repoPath(t, "testdata"), func(path string, d os.DirEntry, err error) error {
		if err != nil || d.IsDir() || !strings.HasSuffix(path, ".decTest") {
			return err
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		head := string(data[:min(len(data), 600)])
		if !strings.Contains(head, "original construction") || !strings.Contains(head, "NOT copied") {
			t.Errorf("%s does not declare itself an original construction", path)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	for _, o := range m.Cases {
		if o.Provenance["generator"] == "" || strings.Contains(o.Provenance["command"], ".cache/") {
			t.Errorf("override %s: provenance %v", o.ID, o.Provenance)
		}
	}
}

// versioned matches a generator identity that carries a version number.
var versioned = regexp.MustCompile(`\b[0-9]+\.[0-9]+`)

// TestRederivedCasesPreserveOriginal pins the provenance of re-derived
// cases: every one keeps decTest's original expectation beside the
// re-derived value with its versioned generator and command, and the power
// suite's 0^0 cases are re-derived to 1 under reason zero-power-one, whose
// justification states 0^0 = 1.
func TestRederivedCasesPreserveOriginal(t *testing.T) {
	m := loadRepoManifest(t)
	zeroZero := map[string]bool{"powx001": true, "powx560": true, "powx561": true, "powx562": true, "powx563": true, "powx2093": true}
	seen := 0
	for _, o := range m.Cases {
		if o.Adoption != classRederived || o.Rederived == nil || o.Original.Expected == "" ||
			!versioned.MatchString(o.Provenance["generator"]) || o.Provenance["command"] == "" {
			t.Errorf("override %s lacks the original, the re-derived value, a versioned generator or the command", o.ID)
		}
		if !zeroZero[o.ID] {
			continue
		}
		seen++
		if o.File != "power.decTest" || o.Reason != "zero-power-one" || o.Rederived.Expected != "1" ||
			len(o.Rederived.Conditions) != 0 || o.Original.Expected != "NaN" ||
			!strings.Contains(o.Provenance["cites"], "0^0 = 1") || !strings.Contains(m.Reasons[o.Reason].Cites, "0^0 = 1") {
			t.Errorf("0^0 case %s is not the 0^0 = 1 re-derivation: %+v", o.ID, o)
		}
	}
	if seen != len(zeroZero) {
		t.Errorf("found %d of the %d power-suite 0^0 cases", seen, len(zeroZero))
	}
}

// loadFixtures parses the committed fixture sources under root and returns
// the fixtures run by test, keyed by id, refusing a fixture that is absent
// from its source or whose content hash differs from the manifest.
func loadFixtures(m *corpusManifest, root, test string) (map[string]testCase, error) {
	parsed := map[string]map[string]testCase{}
	out := map[string]testCase{}
	for _, fx := range m.Fixtures {
		if fx.Test != test {
			continue
		}
		if parsed[fx.Source] == nil {
			data, err := os.ReadFile(filepath.Join(root, filepath.FromSlash(fx.Source)))
			if err != nil {
				return nil, err
			}
			cases, err := parseDecTest(fx.Source, data)
			if err != nil {
				return nil, err
			}
			parsed[fx.Source] = map[string]testCase{}
			for _, tc := range cases {
				parsed[fx.Source][tc.ID] = tc
			}
		}
		tc, ok := parsed[fx.Source][fx.ID]
		switch {
		case !ok:
			return nil, reject("fixture %s is absent from %s", fx.ID, fx.Source)
		case tc.ContentSHA != fx.SHA256:
			return nil, reject("fixture %s content hash %s, manifest %s", fx.ID, tc.ContentSHA, fx.SHA256)
		}
		out[fx.ID] = tc
	}
	if len(out) == 0 {
		return nil, reject("the manifest has no fixtures for %s", test)
	}
	return out, nil
}
