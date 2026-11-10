// SPDX-License-Identifier: Apache-2.0

package main

import (
	"archive/zip"
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"maps"
	"math"
	"math/big"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
)

// The corpus side of the decTest workflow. Every case of the listed archives
// maps to exactly one
// deviation class through the hand-maintained category table and reason
// table of the manifest plus the fixed rules of classifyCase. The rules read
// only the case text and directives, never the library, so a library defect
// cannot reclassify a case. The manifest pins, per suite file, the file hash,
// the per-class and per-reason counts and a digest over every case's
// (id, content hash, class, reason); any corpus, rule or table drift fails.

// Adoption classes.
const (
	classAdopted   = "adopted"
	classExclusion = "intentional-exclusion"
	classRederived = "divergence-re-derived"
	classBeta      = "corpus-beta"
	classDefect    = "defect"
)

// corpusManifest is schema 2 of testdata/dectest/manifest.json.
type corpusManifest struct {
	SchemaVersion int             `json:"schema_version"`
	Suite         string          `json:"suite"`
	Sources       manifestSources `json:"sources"`
	Runner        manifestRunner  `json:"runner"`
	// ClassificationList is the committed per-case list, relative to the
	// repository root.
	ClassificationList string                `json:"classification_list"`
	Reasons            map[string]reasonInfo `json:"reasons"`
	Categories         []category            `json:"categories"`
	Cases              []caseOverride        `json:"cases"`
	Fixtures           []manifestFixture     `json:"fixtures"`
}

type manifestRunner struct {
	Package string `json:"package"`
	Test    string `json:"test"`
}

// reasonInfo is one reason code: the class it assigns and its justification.
type reasonInfo struct {
	Class       string `json:"class"`
	Cites       string `json:"cites"`
	Description string `json:"description"`
}

// category is one suite file of a listed archive. Adoption "adopted"
// applies the per-case rules; "excluded" assigns Reason to every case.
type category struct {
	Archive        string         `json:"archive"`
	File           string         `json:"file"`
	SHA256         string         `json:"sha256"`
	Adoption       string         `json:"adoption"`
	Reason         string         `json:"reason,omitempty"`
	Cites          string         `json:"cites"`
	Cases          int            `json:"cases"`
	Classes        map[string]int `json:"classes"`
	Reasons        map[string]int `json:"reasons"`
	Executed       int            `json:"executed"`
	ExecutedSHA256 string         `json:"executed_ids_sha256"`
	Classification string         `json:"classification_sha256"`
}

// caseOverride classifies one corpus case explicitly: a re-derived
// expectation, a corpus-beta case or a recorded defect. The original
// expectation stays alongside for audit.
type caseOverride struct {
	ID         string            `json:"id"`
	Archive    string            `json:"archive"`
	File       string            `json:"file"`
	SHA256     string            `json:"sha256"`
	Adoption   string            `json:"adoption"`
	Reason     string            `json:"reason"`
	Original   expectation       `json:"original"`
	Rederived  *expectation      `json:"rederived,omitempty"`
	Provenance map[string]string `json:"provenance"`
}

type expectation struct {
	Expected   string   `json:"expected"`
	Conditions []string `json:"conditions"`
}

// classified is one corpus case with its deviation class.
type classified struct {
	testCase
	Class  string
	Reason string
	// Want is the expectation the runner checks: the corpus expectation for
	// adopted cases, the re-derived one for divergence-re-derived cases.
	Want expectation
}

// suiteFile is one decTest file read from a listed archive.
type suiteFile struct {
	Archive string
	Name    string
	Data    []byte
}

// readArchive returns every .decTest member of a zip archive in name order.
// Any other member is an error: the category table must see the whole
// archive.
func readArchive(path string) ([]suiteFile, error) {
	r, err := zip.OpenReader(path)
	if err != nil {
		return nil, reject("corpus archive %s is not readable: %v (run 'make conformance'; a missing corpus is a failure, never a skip)", path, err)
	}
	defer r.Close()
	var files []suiteFile
	for _, f := range r.File {
		if f.FileInfo().IsDir() {
			continue
		}
		if !strings.HasSuffix(f.Name, ".decTest") || strings.ContainsAny(f.Name, `/\`) {
			return nil, reject("archive %s holds an unexpected member %q", path, f.Name)
		}
		if f.UncompressedSize64 > maxCorpusFileSize {
			return nil, reject("archive member %s is too large", f.Name)
		}
		rc, err := f.Open()
		if err != nil {
			return nil, err
		}
		data, err := io.ReadAll(io.LimitReader(rc, maxCorpusFileSize+1))
		closeErr := rc.Close()
		if err != nil {
			return nil, err
		}
		if closeErr != nil {
			return nil, closeErr
		}
		files = append(files, suiteFile{Archive: filepath.Base(path), Name: f.Name, Data: data})
	}
	slices.SortFunc(files, func(a, b suiteFile) int { return strings.Compare(a.Name, b.Name) })
	return files, nil
}

// loadCorpusManifest decodes and validates a schema-2 manifest: every
// category, override and fixture names a known class and reason, and each
// reason's class agrees with where it is used.
func loadCorpusManifest(path string) (*corpusManifest, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	dec := json.NewDecoder(bytes.NewReader(data))
	dec.DisallowUnknownFields()
	var m corpusManifest
	if err := dec.Decode(&m); err != nil {
		return nil, fmt.Errorf("malformed manifest %s: %w", path, err)
	}
	if m.SchemaVersion != 2 {
		return nil, fmt.Errorf("unsupported manifest schema_version %d in %s", m.SchemaVersion, path)
	}
	if m.ClassificationList == "" {
		return nil, fmt.Errorf("manifest %s names no classification_list", path)
	}
	if m.Runner.Package == "" || !strings.HasPrefix(m.Runner.Test, "Test") {
		return nil, fmt.Errorf("manifest %s: runner package and test are required", path)
	}
	for code, r := range m.Reasons {
		if !adoptions[r.Class] || r.Cites == "" || r.Description == "" {
			return nil, fmt.Errorf("reason %s: known class, citation and description are required", code)
		}
	}
	seenFile := map[string]bool{}
	for _, c := range m.Categories {
		key := c.Archive + "/" + c.File
		switch {
		case seenFile[key]:
			return nil, fmt.Errorf("duplicate category %s", key)
		case c.Cites == "":
			return nil, fmt.Errorf("category %s cites no justification", key)
		case c.Adoption == "adopted" && c.Reason != "":
			return nil, fmt.Errorf("adopted category %s carries a reason", key)
		case c.Adoption == "excluded":
			if r, ok := m.Reasons[c.Reason]; !ok || r.Class != classExclusion {
				return nil, fmt.Errorf("excluded category %s needs an intentional-exclusion reason, got %q", key, c.Reason)
			}
		case c.Adoption != "adopted":
			return nil, fmt.Errorf("category %s: adoption must be adopted or excluded, got %q", key, c.Adoption)
		}
		seenFile[key] = true
	}
	seenCase := map[string]bool{}
	for _, o := range m.Cases {
		r, ok := m.Reasons[o.Reason]
		switch {
		case o.Archive == "" || o.File == "":
			return nil, fmt.Errorf("case override %s must name its archive and file", o.ID)
		case seenCase[o.Archive+"/"+o.File+"/"+o.ID]:
			return nil, fmt.Errorf("duplicate case override %s", o.ID)
		case !ok || r.Class != o.Adoption:
			return nil, fmt.Errorf("case override %s: reason %q does not assign class %q", o.ID, o.Reason, o.Adoption)
		case o.Adoption == classAdopted || o.Adoption == classExclusion:
			return nil, fmt.Errorf("case override %s: overrides record only re-derived, corpus-beta or defect cases", o.ID)
		case o.Adoption == classRederived && (o.Rederived == nil || o.Provenance["generator"] == "" || o.Provenance["command"] == ""):
			return nil, fmt.Errorf("re-derived case %s needs the re-derived value and its generator and command", o.ID)
		case o.Original.Expected == "":
			return nil, fmt.Errorf("case override %s must preserve the original expectation", o.ID)
		}
		seenCase[o.Archive+"/"+o.File+"/"+o.ID] = true
	}
	seenFixture := map[string]bool{}
	for i, fx := range m.Fixtures {
		switch {
		case fx.ID == "" || fx.Source == "" || fx.SHA256 == "" || fx.Package == "" || fx.Test == "":
			return nil, fmt.Errorf("manifest fixture %d lacks id, source, sha256, package or test", i+1)
		case seenFixture[fx.ID]:
			return nil, fmt.Errorf("duplicate manifest fixture id %s", fx.ID)
		case !adoptions[fx.Adoption]:
			return nil, fmt.Errorf("fixture %s: unknown adoption class %q (taxonomy: adopted, intentional-exclusion, divergence-re-derived, corpus-beta, defect)",
				fx.ID, fx.Adoption)
		case fx.Adoption != classAdopted:
			return nil, fmt.Errorf("fixture %s: committed fixtures are original constructions and must be adopted", fx.ID)
		case fx.Reason == "":
			return nil, fmt.Errorf("fixture %s: reason code is required", fx.ID)
		}
		seenFixture[fx.ID] = true
	}
	return &m, nil
}

// Operations the executor maps to the library (execute.go owns the
// mapping), and the reason every other decTest operation is excluded.
var displayOps = map[string]bool{"toeng": true}

var (
	specialRe  = regexp.MustCompile(`(?i)^[+-]?(s?nan[0-9]*|inf|infinity)$`)
	encodingRe = regexp.MustCompile(`^[0-9]+#`)
)

// verdict is one case's class and reason.
type verdict struct{ class, reason string }

// coincidenceKey identifies a case's content apart from its id and the
// extended directive: operation, operands, every other directive, the
// expectation and the condition set. An X3.274 subset case whose key
// equals an extended case's key coincides with it.
func coincidenceKey(tc testCase) string {
	var dirs []string
	for _, k := range directiveOrder {
		if v, ok := tc.Directives[k]; ok && k != "extended" && k != "version" {
			dirs = append(dirs, k+"="+strings.ToLower(v))
		}
	}
	conds := make([]string, len(tc.Conditions))
	for i, c := range tc.Conditions {
		conds[i] = strings.ToLower(c)
	}
	slices.Sort(conds)
	return strings.Join([]string{strings.ToLower(tc.Op), strings.Join(tc.Operands, "\x1e"), strings.Join(dirs, ","), tc.Expected, strings.Join(conds, ",")}, "\x1f")
}

// refusalConditions are the conditions whose GDA exceptional result the
// finite-only space turns into a refusal carrying the same condition: the
// expectation is checked as "refused".
var refusalConditions = map[string]bool{"division_impossible": true, "division_by_zero": true, "conversion_syntax": true, "division_undefined": true, "invalid_operation": true}

// exceptionalRefusal reports a case with only finite operands whose GDA
// result is NaN or Infinity with a nonempty set of refusal conditions.
func exceptionalRefusal(tc testCase) bool {
	if !specialRe.MatchString(tc.Expected) || strings.Contains(strings.ToLower(tc.Expected), "snan") || len(tc.Conditions) == 0 ||
		slices.ContainsFunc(tc.Operands, specialRe.MatchString) {
		return false
	}
	for _, c := range tc.Conditions {
		if !refusalConditions[strings.ToLower(c)] {
			return false
		}
	}
	return true
}

// wantFor is the expectation the runner checks for an executed case that
// carries no re-derived override: the corpus expectation, or a refusal
// with its conditions for an exceptional-refusal case.
func wantFor(tc testCase) expectation {
	if exceptionalRefusal(tc) {
		return expectation{Expected: refusedExpectation, Conditions: tc.Conditions}
	}
	return expectation{Expected: tc.Expected, Conditions: tc.Conditions}
}

// classifyCase applies the fixed per-case rules of an adopted category, in
// order; the first rule that matches decides. Overrides come first; a
// subset case takes its coincident extended twin's verdict from twins.
func classifyCase(tc testCase, overrides map[string]caseOverride, twins map[string]verdict) (class, reason string) {
	if o, ok := overrides[tc.ID]; ok {
		return o.Adoption, o.Reason
	}
	d := tc.Directives
	op := strings.ToLower(tc.Op)
	if d["extended"] == "0" {
		t, ok := twins[coincidenceKey(tc)]
		switch {
		case !ok || t.class == classRederived:
			return classExclusion, "subset"
		case t.class == classAdopted:
			return classAdopted, "subset-coincident"
		}
		return t.class, t.reason
	}
	switch {
	case d["clamp"] == "1":
		return classExclusion, "clamp"
	case d["rounding"] == "05up":
		return classExclusion, "mode-05up"
	case displayOps[op]:
		return classExclusion, "display-format"
	case !executedOps[op]:
		return classExclusion, "not-in-catalogue"
	}
	for _, o := range tc.Operands {
		if o == "#" || encodingRe.MatchString(o) {
			return classExclusion, "encoding-operand"
		}
	}
	if tc.Expected == "#" || encodingRe.MatchString(tc.Expected) {
		return classExclusion, "encoding-operand"
	}
	if slices.ContainsFunc(tc.Operands, specialRe.MatchString) {
		return classExclusion, "non-finite"
	}
	for _, c := range tc.Conditions {
		switch strings.ToLower(c) {
		case "lost_digits":
			return classExclusion, "subset"
		case "clamped":
			return classExclusion, "clamped"
		}
	}
	if negativeZero(tc.Expected) {
		return classExclusion, "signed-zero"
	}
	if (op == "max" || op == "min") && slices.ContainsFunc(tc.Operands, negativeZero) {
		return classExclusion, "signed-zero"
	}
	for _, o := range tc.Operands {
		if e, ok := storedExponent(o); ok && (e < math.MinInt32 || e > math.MaxInt32) {
			return classExclusion, "exponent-domain"
		}
	}
	switch op {
	case "tointegral", "tointegralx":
		if e, ok := storedExponent(tc.Operands[0]); ok && e > 0 {
			return classExclusion, "integral-exponent-zero"
		}
	case "rescale":
		if n, integral, ok := integralValue(tc.Operands[1]); !ok || !integral || n < math.MinInt32 || n > math.MaxInt32 {
			return classExclusion, "rescale-exponent-domain"
		}
	}
	switch {
	case exceptionalRefusal(tc):
		return classAdopted, "exceptional-refusal"
	case specialRe.MatchString(tc.Expected):
		return classExclusion, "non-finite"
	}
	return classAdopted, "directive-mapped"
}

// negativeZero reports a numeric string that denotes a negative zero.
func negativeZero(s string) bool {
	if !strings.HasPrefix(s, "-") {
		return false
	}
	coeff, _, ok := numericParts(s)
	return ok && strings.Trim(coeff, "0") == ""
}

// numericParts splits a GDA numeric string (sign, digits with at most one
// point, optional exponent) into its coefficient digits and stored
// exponent. It is independent of the library under test.
func numericParts(s string) (coeff string, exp *big.Int, ok bool) {
	s = strings.TrimLeft(s, "+-")
	mant, expText, hasExp := strings.Cut(strings.ToLower(s), "e")
	intPart, frac, _ := strings.Cut(mant, ".")
	digits := intPart + frac
	if digits == "" || strings.Count(mant, ".") > 1 || strings.Trim(digits, "0123456789") != "" {
		return "", nil, false
	}
	e := new(big.Int)
	if hasExp {
		t := strings.TrimPrefix(strings.TrimPrefix(expText, "+"), "-")
		if t == "" || strings.Trim(t, "0123456789") != "" {
			return "", nil, false
		}
		if _, ok := e.SetString(expText, 10); !ok {
			return "", nil, false
		}
	}
	e.Sub(e, big.NewInt(int64(len(frac))))
	return digits, e, true
}

// storedExponent returns a numeric string's exponent, saturated to int64.
func storedExponent(s string) (int64, bool) {
	_, e, ok := numericParts(s)
	if !ok {
		return 0, false
	}
	if !e.IsInt64() {
		if e.Sign() < 0 {
			return math.MinInt64, true
		}
		return math.MaxInt64, true
	}
	return e.Int64(), true
}

// integralValue reports whether a numeric string denotes an integer and, if
// its magnitude fits, the integer (saturated to ±2^62 otherwise).
func integralValue(s string) (n int64, integral, ok bool) {
	coeff, e, ok := numericParts(s)
	if !ok {
		return 0, false, false
	}
	coeff = strings.TrimLeft(coeff, "0")
	if coeff == "" {
		return 0, true, true
	}
	if e.Sign() < 0 {
		if !e.IsInt64() || -e.Int64() > int64(len(coeff)) {
			return 0, false, true
		}
		k := int(-e.Int64())
		if strings.Trim(coeff[len(coeff)-k:], "0") != "" {
			return 0, false, true
		}
		coeff, e = coeff[:len(coeff)-k], new(big.Int)
		if coeff == "" {
			return 0, true, true
		}
	}
	const saturated = int64(1) << 62
	v, _ := new(big.Int).SetString(coeff, 10)
	if !e.IsInt64() || e.Int64() > 20 || len(coeff)+int(e.Int64()) > 20 {
		n = saturated
	} else {
		v.Mul(v, new(big.Int).Exp(big.NewInt(10), e, nil))
		n = saturated
		if v.IsInt64() && v.Int64() < saturated {
			n = v.Int64()
		}
	}
	if strings.HasPrefix(s, "-") {
		n = -n
	}
	return n, true, true
}

// parsedFile is one suite file with its parsed cases.
type parsedFile struct {
	suiteFile
	cases []testCase
}

// classifyFile classifies every case of one parsed suite file under its
// category and returns the category's computed summary. Overrides are
// keyed by case id within this file; twins by coincidence key.
func classifyFile(pf parsedFile, cat category, reasons map[string]reasonInfo, overrides map[string]caseOverride, twins map[string]verdict) ([]classified, category, error) {
	sum := sha256.Sum256(pf.Data)
	got := category{
		Archive: pf.Archive, File: pf.Name, SHA256: hex.EncodeToString(sum[:]),
		Adoption: cat.Adoption, Reason: cat.Reason, Cites: cat.Cites,
		Cases: len(pf.cases), Classes: map[string]int{}, Reasons: map[string]int{},
	}
	out := make([]classified, 0, len(pf.cases))
	digest := sha256.New()
	var executed []string
	seen := map[string]bool{}
	for _, tc := range pf.cases {
		if seen[tc.ID] {
			return nil, category{}, reject("%s: duplicate case id %s", pf.Name, tc.ID)
		}
		seen[tc.ID] = true
		class, reason := classExclusion, cat.Reason
		if cat.Adoption == "adopted" {
			class, reason = classifyCase(tc, overrides, twins)
		}
		info, ok := reasons[reason]
		if !ok || info.Class != class {
			return nil, category{}, reject("%s %s: rule reason %q is not in the manifest reason table with class %s", pf.Name, tc.ID, reason, class)
		}
		c := classified{testCase: tc, Class: class, Reason: reason, Want: wantFor(tc)}
		if o, ok := overrides[tc.ID]; ok {
			if o.SHA256 != tc.ContentSHA {
				return nil, category{}, reject("case override %s: content hash %s, corpus %s (corpus drift)", tc.ID, o.SHA256, tc.ContentSHA)
			}
			if o.Original.Expected != tc.Expected || !slices.Equal(o.Original.Conditions, tc.Conditions) {
				return nil, category{}, reject("case override %s: preserved original expectation differs from the corpus", tc.ID)
			}
			if o.Rederived != nil {
				c.Want = *o.Rederived
			}
		}
		got.Classes[class]++
		got.Reasons[reason]++
		fmt.Fprintf(digest, "%s\t%s\t%s\t%s\n", tc.ID, tc.ContentSHA, class, reason)
		if executes(class) {
			executed = append(executed, tc.ID)
		}
		out = append(out, c)
	}
	got.Classification = hex.EncodeToString(digest.Sum(nil))
	got.Executed = len(executed)
	got.ExecutedSHA256 = executedDigest(executed)
	return out, got, nil
}

// executes reports whether a class is run by the corpus test: adopted and
// re-derived cases are required subtests; a defect case runs and must fail
// until it is fixed or re-classified, so it is never a passing subtest.
func executes(class string) bool {
	return class == classAdopted || class == classRederived
}

// executedDigest is the digest of the executed cases:
// sha256 over the sorted executed case ids, one per line.
func executedDigest(ids []string) string {
	sorted := slices.Clone(ids)
	slices.Sort(sorted)
	h := sha256.New()
	for _, id := range sorted {
		fmt.Fprintf(h, "%s\n", id)
	}
	return hex.EncodeToString(h.Sum(nil))
}

// classifyCorpus reads every listed archive under dir and classifies it
// against the manifest. It returns the cases keyed by "archive/file", the
// computed category rows in archive and file order, and drift messages
// (file hash, counts, digests, missing or extra categories). Extended
// cases are classified first so the subset cases can find their twins.
func classifyCorpus(dir string, m *corpusManifest) (map[string][]classified, []category, []string, error) {
	cats := map[string]category{}
	archives := map[string]bool{}
	for _, c := range m.Categories {
		cats[c.Archive+"/"+c.File] = c
		archives[c.Archive] = true
	}
	overrides := map[string]map[string]caseOverride{}
	for _, o := range m.Cases {
		key := o.Archive + "/" + o.File
		if overrides[key] == nil {
			overrides[key] = map[string]caseOverride{}
		}
		overrides[key][o.ID] = o
	}
	var files []parsedFile
	var drift []string
	seen := map[string]bool{}
	for _, archive := range slices.Sorted(maps.Keys(archives)) {
		sfs, err := readArchive(filepath.Join(dir, archive))
		if err != nil {
			return nil, nil, nil, err
		}
		for _, sf := range sfs {
			key := archive + "/" + sf.Name
			if _, ok := cats[key]; !ok {
				drift = append(drift, fmt.Sprintf("%s is in the archive but not in the category table (adopt or exclude it; never convert silently)", key))
				continue
			}
			seen[key] = true
			cases, err := parseDecTest(sf.Name, sf.Data)
			if err != nil {
				return nil, nil, nil, err
			}
			files = append(files, parsedFile{suiteFile: sf, cases: cases})
		}
	}
	subset := func(pf parsedFile) bool {
		return len(pf.cases) > 0 && pf.cases[0].Directives["extended"] == "0"
	}
	twins := map[string]verdict{}
	byFile := map[string][]classified{}
	rows := map[string]category{}
	for pass := range 2 {
		for _, pf := range files {
			if subset(pf) != (pass == 1) {
				continue
			}
			key := pf.Archive + "/" + pf.Name
			cases, got, err := classifyFile(pf, cats[key], m.Reasons, overrides[key], twins)
			if err != nil {
				return nil, nil, nil, err
			}
			for _, c := range cases {
				if (c.Directives["extended"] == "0") != (pass == 1) {
					return nil, nil, nil, reject("%s mixes subset and extended cases", key)
				}
				if _, dup := twins[coincidenceKey(c.testCase)]; !dup && pass == 0 {
					twins[coincidenceKey(c.testCase)] = verdict{c.Class, c.Reason}
				}
			}
			byFile[key] = cases
			rows[key] = got
			drift = append(drift, compareCategory(cats[key], got)...)
		}
	}
	var computed []category
	for _, pf := range files {
		computed = append(computed, rows[pf.Archive+"/"+pf.Name])
	}
	for _, key := range slices.Sorted(maps.Keys(cats)) {
		if !seen[key] {
			drift = append(drift, fmt.Sprintf("category %s is absent from the corpus (manifest drift)", key))
		}
	}
	for _, o := range m.Cases {
		if !slices.ContainsFunc(byFile[o.Archive+"/"+o.File], func(c classified) bool { return c.ID == o.ID }) {
			drift = append(drift, fmt.Sprintf("case override %s/%s/%s is absent from the corpus", o.Archive, o.File, o.ID))
		}
	}
	return byFile, computed, drift, nil
}

func compareCategory(want, got category) []string {
	var msgs []string
	key := want.Archive + "/" + want.File
	check := func(field, w, g string) {
		if w != g {
			msgs = append(msgs, fmt.Sprintf("%s: %s is %s, manifest says %s", key, field, g, w))
		}
	}
	check("sha256", want.SHA256, got.SHA256)
	check("cases", fmt.Sprint(want.Cases), fmt.Sprint(got.Cases))
	check("classes", fmt.Sprint(want.Classes), fmt.Sprint(got.Classes))
	check("reasons", fmt.Sprint(want.Reasons), fmt.Sprint(got.Reasons))
	check("executed", fmt.Sprint(want.Executed), fmt.Sprint(got.Executed))
	check("executed_ids_sha256", want.ExecutedSHA256, got.ExecutedSHA256)
	check("classification_sha256", want.Classification, got.Classification)
	return msgs
}

// classificationList renders the per-case classification without corpus
// text: one line per suite file, class and reason, listing the case ids in
// file order. It is committed beside the manifest (the manifest's
// classification_list), so a rule or table change shows as a reviewable
// diff of ids and reason codes.
func classificationList(byFile map[string][]classified, computed []category) string {
	var b strings.Builder
	b.WriteString("# decTest per-case classification (generated by dectestconv -classify -emit; reviewed, never hand-edited).\n")
	b.WriteString("# archive/file<TAB>class<TAB>reason<TAB>case ids in file order\n")
	for _, c := range computed {
		key := c.Archive + "/" + c.File
		groups := map[verdict][]string{}
		var order []verdict
		for _, tc := range byFile[key] {
			v := verdict{tc.Class, tc.Reason}
			if groups[v] == nil {
				order = append(order, v)
			}
			groups[v] = append(groups[v], tc.ID)
		}
		for _, v := range order {
			fmt.Fprintf(&b, "%s\t%s\t%s\t%s\n", key, v.class, v.reason, strings.Join(groups[v], " "))
		}
	}
	return b.String()
}

// compareClassificationList reports the lines of the committed list that
// differ from the computed one (at most ten), as drift.
func compareClassificationList(path, got string) []string {
	data, err := os.ReadFile(path)
	if err != nil {
		return []string{fmt.Sprintf("classification list %s: %v", path, err)}
	}
	if string(data) == got {
		return nil
	}
	want := map[string]bool{}
	for line := range strings.SplitSeq(string(data), "\n") {
		want[line] = true
	}
	have := map[string]bool{}
	var msgs []string
	for line := range strings.SplitSeq(got, "\n") {
		have[line] = true
		if !want[line] && len(msgs) < 10 {
			msgs = append(msgs, "classification list: computed line not committed: "+clip(line))
		}
	}
	for line := range strings.SplitSeq(string(data), "\n") {
		if !have[line] && len(msgs) < 20 {
			msgs = append(msgs, "classification list: committed line no longer computed: "+clip(line))
		}
	}
	if len(msgs) == 0 {
		msgs = append(msgs, "classification list: line order differs")
	}
	return msgs
}

func clip(s string) string {
	if len(s) > 160 {
		return s[:160] + "…"
	}
	return s
}

// refusedExpectation marks a repository error-path vector.
const refusedExpectation = "refused"

var executedOps = map[string]bool{
	"add": true, "subtract": true, "multiply": true, "divide": true,
	"fma": true, "divideint": true, "remainder": true, "remaindernear": true,
	"quantize": true, "rescale": true, "tointegral": true, "tointegralx": true,
	"squareroot": true, "power": true, "exp": true, "ln": true, "log10": true,
	"plus": true, "minus": true, "abs": true,
	"reduce": true, "max": true, "min": true, "compare": true, "tosci": true,
	"apply": true, "copy": true, "copyabs": true, "copynegate": true,
}
