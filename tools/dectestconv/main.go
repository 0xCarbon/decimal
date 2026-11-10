// SPDX-License-Identifier: Apache-2.0

// Command dectestconv runs the decTest corpus workflow: provisioning,
// conversion and classification of the General Decimal Arithmetic testcases.
//
// Provisioning (-provision) downloads the corpus from the speleotrove URLs
// listed in the committed download list (testdata/dectest/downloads.txt)
// into a gitignored local directory (.cache/dectest) and SHA-256-verifies
// every file against it. Download unavailability, a hash or size mismatch,
// or zero matched files is a loud failure, never a skip; already-present
// files with matching hashes are reused (idempotent local runs).
//
// Conversion (-convert) parses .decTest text into the internal fixture
// representation and validates every case against the hand-maintained
// adoption manifest (testdata/dectest/manifest.json): each committed
// case id must be present with an exactly matching content hash, and the
// manifest may not reference cases the file does not contain. Corpus bytes
// never enter the tree; committed fixtures carry provenance, and the
// five-class deviation taxonomy (adopted, intentional-exclusion,
// divergence-re-derived, corpus-beta, defect) is enforced by the manifest
// schema.
//
// The per-case content hash is defined as
//
//	sha256(join("\x1f", [id, op, directives, operands, expected, conditions]))
//
// where directives joins "key=value" pairs in the fixed order version,
// precision, rounding, maxexponent, minexponent, extended, clamp (lowercase
// keys, absent keys omitted), operands joins with "\x1e", and conditions
// join with "," in file order.
package main

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"maps"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
	"time"
)

const usage = `dectestconv — decTest corpus provisioning, conversion and classification

  dectestconv -provision -downloads testdata/dectest/downloads.txt -dir .cache/dectest [-base-url URL]
  dectestconv -convert -in testdata/dectest/samples/converter-samples.decTest \
                      -manifest testdata/dectest/manifest.json -out dist/dectest-fixtures
  dectestconv -classify -dir .cache/dectest -manifest testdata/dectest/manifest.json \
                       [-emit dist/dectest] [-list dist/dectest-cases.tsv]

-classify checks every listed archive against the manifest's category
table (file hash, per-class and per-reason counts, executed-id and
classification digests) and the committed per-case classification list,
and exits 1 on any drift. -emit writes the computed category rows
(categories.json) and list (classification.txt) into a directory, for
editing the manifest by hand; the tool never rewrites the manifest or the list.
-list writes the per-case table with content hashes (local-only).

Exit codes: 0 success, 1 corpus or manifest rejection, 2 usage error.`

const defaultBaseURL = "https://speleotrove.com/decimal/"

const (
	corpusUserAgent       = "decimal-corpus-provisioner/1 (+https://github.com/0xCarbon/decimal)"
	corpusDownloadTimeout = 60 * time.Second
	corpusAttemptTimeout  = 15 * time.Second
	corpusAttempts        = 4
	maxCorpusFileSize     = 1 << 30
	corpusDiagnosticLimit = 1024
)

// adoptions is the five-class deviation taxonomy.
var adoptions = map[string]bool{
	"adopted": true, "intentional-exclusion": true, "divergence-re-derived": true,
	"corpus-beta": true, "defect": true,
}

var directiveOrder = []string{
	"version", "precision", "rounding", "maxexponent", "minexponent", "extended", "clamp",
}

var roundingValues = map[string]bool{
	"ceiling": true, "down": true, "floor": true, "half_down": true, "half_even": true,
	"half_up": true, "up": true, "05up": true, "exact": true,
}

var (
	idRe         = regexp.MustCompile(`^[A-Za-z][A-Za-z0-9_]*$`)
	opRe         = regexp.MustCompile(`^[A-Za-z][A-Za-z0-9]*$`)
	condRe       = regexp.MustCompile(`^[A-Za-z_][A-Za-z0-9_]*$`)
	downloadLine = regexp.MustCompile(`^(\S+): (\d+) bytes sha256=([0-9a-f]{64})$`)
	directiveRe  = regexp.MustCompile(`^([A-Za-z]+):\s*(\S+)\s*(?:--.*)?$`)
)

type corpusFile struct {
	Name   string
	Size   int64
	SHA256 string
}

type manifestFixture struct {
	ID         string            `json:"id"`
	Package    string            `json:"package,omitempty"`
	Test       string            `json:"test,omitempty"`
	Source     string            `json:"source"`
	SHA256     string            `json:"sha256"`
	Adoption   string            `json:"adoption"`
	Reason     string            `json:"reason"`
	Provenance map[string]string `json:"provenance"`
}

type manifestSources struct {
	Downloads string `json:"downloads"`
	LocalDir  string `json:"local_dir"`
	Note      string `json:"note"`
}

// token is one lexical element of a test line; quoted operands carry their
// unquoted text, and the bare "#" marker records decTest's invalid-operand
// syntax (such cases are classified by the manifest, not here).
type token struct {
	text    string
	quoted  bool
	invalid bool
}

type testCase struct {
	ID         string            `json:"id"`
	Op         string            `json:"op"`
	Directives map[string]string `json:"directives"`
	Operands   []string          `json:"operands"`
	Expected   string            `json:"expected"`
	Conditions []string          `json:"conditions"`
	ContentSHA string            `json:"content_sha256"`
	Provenance map[string]string `json:"provenance"`
}

type rejectionError struct{ msg string }

func (e *rejectionError) Error() string { return e.msg }

func reject(format string, args ...any) error {
	return &rejectionError{msg: fmt.Sprintf(format, args...)}
}

func isRejection(err error) bool {
	var rej *rejectionError
	return errors.As(err, &rej)
}

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, "dectestconv:", err)
		if isRejection(err) {
			os.Exit(1)
		}
		os.Exit(2)
	}
}

func run() error {
	provision := flag.Bool("provision", false, "download and SHA-256-verify the corpus against the download list")
	convert := flag.Bool("convert", false, "convert a .decTest file to fixtures, validating the manifest")
	downloads := flag.String("downloads", "", "download list, testdata/dectest/downloads.txt (provisioning)")
	dir := flag.String("dir", "", "corpus directory (provisioning)")
	baseURL := flag.String("base-url", defaultBaseURL, "corpus base URL (provisioning)")
	in := flag.String("in", "", "input .decTest file (conversion)")
	manifestPath := flag.String("manifest", "", "adoption manifest (conversion)")
	out := flag.String("out", "", "fixture output directory (conversion)")
	classify := flag.Bool("classify", false, "classify the provisioned corpus against the manifest")
	emit := flag.String("emit", "", "write the computed category rows and list into this directory (classification)")
	list := flag.String("list", "", "write every case's file, id, content hash, class and reason here as TSV (classification)")
	flag.Usage = func() { fmt.Fprintln(os.Stderr, usage) }
	flag.Parse()
	if flag.NArg() != 0 {
		return errors.New("unexpected positional arguments")
	}
	modes := 0
	for _, on := range []bool{*provision, *convert, *classify} {
		if on {
			modes++
		}
	}
	switch {
	case modes != 1:
		return errors.New("exactly one of -provision, -convert or -classify is required")
	case *classify:
		if *dir == "" || *manifestPath == "" {
			return errors.New("-classify requires -dir and -manifest")
		}
		return classifyCommand(*dir, *manifestPath, *emit, *list)
	case *provision:
		if *downloads == "" || *dir == "" {
			return errors.New("-provision requires -downloads and -dir")
		}
		files, err := parseDownloadList(*downloads)
		if err != nil {
			return err
		}
		return provisionCorpus(*dir, files, *baseURL)
	default:
		if *in == "" || *manifestPath == "" || *out == "" {
			return errors.New("-convert requires -in, -manifest and -out")
		}
		return convertFile(*in, *manifestPath, *out)
	}
}

// parseDownloadList reads the committed download list: lines of
// "name: <n> bytes sha256=<hex>" under "#" comment lines.
func parseDownloadList(path string) ([]corpusFile, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var files []corpusFile
	for i, line := range strings.Split(string(data), "\n") {
		line = strings.TrimRight(line, "\r")
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		m := downloadLine.FindStringSubmatch(line)
		if m == nil {
			return nil, fmt.Errorf("malformed download list line %d in %s: %q", i+1, path, line)
		}
		var size int64
		if _, err := fmt.Sscanf(m[2], "%d", &size); err != nil {
			return nil, fmt.Errorf("malformed size on download list line %d in %s: %w", i+1, path, err)
		}
		files = append(files, corpusFile{Name: m[1], Size: size, SHA256: m[3]})
	}
	if len(files) == 0 {
		return nil, reject("download list %s names zero corpus files: refusing to provision nothing", path)
	}
	return files, nil
}

func provisionCorpus(dir string, files []corpusFile, baseURL string) error {
	if len(files) == 0 {
		return reject("zero corpus files: refusing to provision nothing")
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	verified, downloaded := 0, 0
	for _, cf := range files {
		wasPresent := fileExists(filepath.Join(dir, cf.Name))
		if err := ensureCorpusFile(filepath.Join(dir, cf.Name), cf, baseURL); err != nil {
			return err
		}
		dst := filepath.Join(dir, cf.Name)
		info, err := os.Stat(dst)
		if err != nil {
			return err
		}
		if info.Size() != cf.Size {
			return reject("size mismatch for %s: got %d bytes, download list says %d — refusing to continue",
				dst, info.Size(), cf.Size)
		}
		if !wasPresent {
			downloaded++
		}
		verified++
	}
	fmt.Printf("dectestconv: provisioned and verified %d/%d corpus files against the download list (%d downloaded, %d already present)\n",
		verified, len(files), downloaded, verified-downloaded)
	return nil
}

func fileExists(path string) bool {
	_, err := os.Stat(path)
	return err == nil
}

func ensureCorpusFile(dst string, cf corpusFile, baseURL string) error {
	if err := verifyOrFetch(dst, cf, baseURL); err != nil {
		return reject("corpus provisioning failed for %s: %v — a missing corpus is a failure, never a skip", cf.Name, err)
	}
	return nil
}

func verifyOrFetch(dst string, cf corpusFile, baseURL string) error {
	if cf.Size < 0 || cf.Size > maxCorpusFileSize {
		return fmt.Errorf("listed size %d for %s exceeds the supported corpus file size", cf.Size, cf.Name)
	}
	if data, err := os.ReadFile(dst); err == nil {
		if err := verifyCorpusBytes(data, cf); err != nil {
			return fmt.Errorf("present file rejected: %w", err)
		}
		return nil
	} else if !errors.Is(err, os.ErrNotExist) {
		return fmt.Errorf("reading present file %s: %w", dst, err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), corpusDownloadTimeout)
	defer cancel()
	client := &http.Client{Timeout: corpusAttemptTimeout}
	data, err := downloadCorpus(ctx, client, baseURL+cf.Name, cf)
	if err != nil {
		return err
	}
	return publishCorpusFile(dst, data)
}

// downloadCorpus retries only transient HTTP responses from the same source.
// The caller's total deadline includes every request, response read and delay;
// the client additionally bounds each attempt. Integrity failures never retry.
func downloadCorpus(ctx context.Context, client *http.Client, url string, cf corpusFile) ([]byte, error) {
	for attempt := 1; attempt <= corpusAttempts; attempt++ {
		if err := ctx.Err(); err != nil {
			return nil, fmt.Errorf("download from %s exhausted total budget: %w", url, err)
		}
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
		if err != nil {
			return nil, err
		}
		req.Header.Set("User-Agent", corpusUserAgent)
		resp, err := client.Do(req)
		if err != nil {
			return nil, fmt.Errorf("download from %s failed on attempt %d/%d: %w", url, attempt, corpusAttempts, err)
		}
		if resp.StatusCode == http.StatusOK {
			data, readErr := io.ReadAll(io.LimitReader(resp.Body, cf.Size+1))
			closeErr := resp.Body.Close()
			if readErr != nil {
				return nil, fmt.Errorf("reading %s: %w", url, readErr)
			}
			if closeErr != nil {
				return nil, fmt.Errorf("closing %s: %w", url, closeErr)
			}
			if err := verifyCorpusBytes(data, cf); err != nil {
				return nil, err
			}
			return data, nil
		}
		body, readErr := io.ReadAll(io.LimitReader(resp.Body, corpusDiagnosticLimit))
		closeErr := resp.Body.Close()
		retryAfter := resp.Header.Get("Retry-After")
		diagnostic := fmt.Errorf("download from %s returned HTTP %d on attempt %d/%d; Retry-After=%q; body=%q",
			url, resp.StatusCode, attempt, corpusAttempts, retryAfter[:min(len(retryAfter), 128)], body)
		if readErr != nil || closeErr != nil {
			diagnostic = fmt.Errorf("%w; response read/close error: %v", diagnostic, errors.Join(readErr, closeErr))
		}
		if !transientCorpusStatus(resp.StatusCode) || attempt == corpusAttempts {
			return nil, diagnostic
		}
		delay := corpusRetryDelay(retryAfter, attempt, time.Now())
		if err := waitCorpusRetry(ctx, delay); err != nil {
			return nil, fmt.Errorf("%w; retry budget exhausted: %w", diagnostic, err)
		}
	}
	panic("unreachable: bounded retry loop always returns")
}

func transientCorpusStatus(status int) bool {
	return status == http.StatusTooManyRequests || status == http.StatusInternalServerError || status == http.StatusBadGateway ||
		status == http.StatusServiceUnavailable || status == http.StatusGatewayTimeout
}

func corpusRetryDelay(retryAfter string, attempt int, now time.Time) time.Duration {
	if seconds, err := strconv.ParseInt(retryAfter, 10, 64); err == nil && seconds >= 0 {
		if seconds >= int64(corpusDownloadTimeout/time.Second) {
			return corpusDownloadTimeout
		}
		return time.Duration(seconds) * time.Second
	}
	if date, err := http.ParseTime(retryAfter); err == nil {
		return min(max(date.Sub(now), 0), corpusDownloadTimeout)
	}
	return time.Second << (attempt - 1)
}

func waitCorpusRetry(ctx context.Context, delay time.Duration) error {
	timer := time.NewTimer(delay)
	defer timer.Stop()
	select {
	case <-ctx.Done():
		return ctx.Err()
	case <-timer.C:
		return ctx.Err()
	}
}

func verifyCorpusBytes(data []byte, cf corpusFile) error {
	if int64(len(data)) != cf.Size {
		return fmt.Errorf("size mismatch for %s: got %d bytes, download list says %d — refusing to continue", cf.Name, len(data), cf.Size)
	}
	return verifyHash(data, cf)
}

// publishCorpusFile exposes only verified complete bytes. The temporary file
// is created alongside the destination so rename stays on the same filesystem.
func publishCorpusFile(dst string, data []byte) error {
	f, err := os.CreateTemp(filepath.Dir(dst), "."+filepath.Base(dst)+".tmp-*")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	if err := f.Chmod(0o644); err != nil {
		f.Close()
		return err
	}
	_, writeErr := f.Write(data)
	closeErr := f.Close()
	if err := errors.Join(writeErr, closeErr); err != nil {
		return err
	}
	return os.Rename(f.Name(), dst)
}

func verifyHash(data []byte, cf corpusFile) error {
	sum := sha256.Sum256(data)
	got := hex.EncodeToString(sum[:])
	if got != cf.SHA256 {
		return fmt.Errorf("SHA-256 mismatch: got %s, download list says %s", got, cf.SHA256)
	}
	return nil
}

// parseDecTest parses .decTest text into structured cases. Structural
// deviations (unknown directives, unterminated quotes, missing ->) are
// errors; value-level oddities (specials, "#"-marked invalid operands,
// radix-prefixed numbers) are recorded as text for the manifest to classify.
func parseDecTest(name string, data []byte) ([]testCase, error) {
	var cases []testCase
	directives := map[string]string{}
	for i, raw := range strings.Split(string(data), "\n") {
		line := strings.TrimRight(raw, "\r")
		trimmed := strings.TrimSpace(line)
		where := fmt.Sprintf("%s:%d", name, i+1)
		if trimmed == "" || strings.HasPrefix(trimmed, "--") {
			continue
		}
		if m := directiveRe.FindStringSubmatch(line); m != nil {
			key := strings.ToLower(m[1])
			if key == "dectest" {
				continue // an include directive of the testall drivers; no case content
			}
			if !knownDirective(key) {
				return nil, fmt.Errorf("%s: unknown directive %q", where, m[1])
			}
			if err := validateDirective(key, m[2]); err != nil {
				return nil, fmt.Errorf("%s: %w", where, err)
			}
			directives[key] = m[2]
			continue
		}
		tokens, err := tokenize(line)
		if err != nil {
			return nil, fmt.Errorf("%s: %w", where, err)
		}
		if len(tokens) == 0 {
			continue
		}
		tc, err := parseTestCase(tokens, directives)
		if err != nil {
			return nil, fmt.Errorf("%s: %w", where, err)
		}
		tc.Provenance = map[string]string{"source": name, "suite": "speleotrove-dectest"}
		tc.ContentSHA = contentHash(tc)
		cases = append(cases, tc)
	}
	return cases, nil
}

func knownDirective(key string) bool {
	return slices.Contains(directiveOrder, key)
}

func validateDirective(key, value string) error {
	switch key {
	case "precision":
		if !isDigits(value) {
			return fmt.Errorf("precision must be a positive integer, got %q", value)
		}
	case "rounding":
		if !roundingValues[value] {
			return fmt.Errorf("unknown rounding mode %q", value)
		}
	case "maxexponent", "minexponent":
		if !isSignedDigits(value) {
			return fmt.Errorf("%s must be an integer, got %q", key, value)
		}
	case "extended", "clamp":
		if value != "0" && value != "1" {
			return fmt.Errorf("%s must be 0 or 1, got %q", key, value)
		}
	}
	return nil
}

func isDigits(s string) bool {
	if s == "" {
		return false
	}
	for _, r := range s {
		if r < '0' || r > '9' {
			return false
		}
	}
	return true
}

func isSignedDigits(s string) bool {
	t := strings.TrimPrefix(strings.TrimPrefix(s, "+"), "-")
	return isDigits(t)
}

// quotedString reads the decTest string that starts rest: either quote
// delimits it, the other kind is an ordinary character inside it, and a
// doubled delimiter stands for one delimiter character ('1E”1' is 1E'1).
// It returns the unquoted text and the number of bytes consumed.
func quotedString(rest string) (string, int, error) {
	quote := rest[0]
	var b strings.Builder
	for i := 1; i < len(rest); i++ {
		if rest[i] != quote {
			b.WriteByte(rest[i])
			continue
		}
		if i+1 < len(rest) && rest[i+1] == quote {
			b.WriteByte(quote)
			i++
			continue
		}
		return b.String(), i + 1, nil
	}
	return "", 0, errors.New("unterminated quoted operand")
}

// tokenize splits one test line into tokens, honoring quoted operands and
// cutting the line at a trailing "--" comment.
func tokenize(line string) ([]token, error) {
	var tokens []token
	i := 0
	for i < len(line) {
		for i < len(line) && (line[i] == ' ' || line[i] == '\t') {
			i++
		}
		if i >= len(line) {
			break
		}
		rest := line[i:]
		switch {
		case rest[0] == '\'' || rest[0] == '"':
			text, n, err := quotedString(rest)
			if err != nil {
				return nil, err
			}
			tokens = append(tokens, token{text: text, quoted: true})
			i += n
		default:
			end := strings.IndexAny(rest, " \t")
			word := rest
			if end >= 0 {
				word = rest[:end]
			}
			if strings.HasPrefix(word, "--") {
				return tokens, nil // trailing comment
			}
			tokens = append(tokens, token{text: word, invalid: word == "#"})
			i += len(word)
		}
	}
	return tokens, nil
}

func parseTestCase(tokens []token, directives map[string]string) (testCase, error) {
	arrow := -1
	for i, tk := range tokens {
		if !tk.quoted && tk.text == "->" {
			arrow = i
			break
		}
	}
	if arrow < 0 {
		return testCase{}, errors.New("test line has no -> separator")
	}
	if arrow < 3 {
		return testCase{}, fmt.Errorf("test line needs id, op and at least one operand before -> (got %d tokens)", arrow)
	}
	if len(tokens) < arrow+2 {
		return testCase{}, errors.New("test line has no expected value after ->")
	}
	id, op := tokens[0], tokens[1]
	if id.quoted || !idRe.MatchString(id.text) {
		return testCase{}, fmt.Errorf("invalid test id %q", id.text)
	}
	if op.quoted || !opRe.MatchString(op.text) {
		return testCase{}, fmt.Errorf("invalid operation %q", op.text)
	}
	tc := testCase{
		ID:         id.text,
		Op:         op.text,
		Directives: map[string]string{},
		Operands:   []string{},
		Conditions: []string{},
	}
	maps.Copy(tc.Directives, directives)
	for _, tk := range tokens[2:arrow] {
		if tk.invalid {
			tc.Operands = append(tc.Operands, "#")
			continue
		}
		tc.Operands = append(tc.Operands, tk.text)
	}
	tc.Expected = tokens[arrow+1].text
	for _, tk := range tokens[arrow+2:] {
		for cond := range strings.SplitSeq(tk.text, ",") {
			if cond == "" {
				continue
			}
			if !condRe.MatchString(cond) {
				return testCase{}, fmt.Errorf("invalid condition name %q", cond)
			}
			tc.Conditions = append(tc.Conditions, cond)
		}
	}
	return tc, nil
}

func contentHash(tc testCase) string {
	directives := make([]string, 0, len(directiveOrder))
	for _, k := range directiveOrder {
		if v, ok := tc.Directives[k]; ok {
			directives = append(directives, k+"="+v)
		}
	}
	parts := []string{
		tc.ID,
		tc.Op,
		strings.Join(directives, ","),
		strings.Join(tc.Operands, "\x1e"),
		tc.Expected,
		strings.Join(tc.Conditions, ","),
	}
	sum := sha256.Sum256([]byte(strings.Join(parts, "\x1f")))
	return hex.EncodeToString(sum[:])
}

// convertFile parses the input, validates it against the manifest and writes
// one fixture file per case. Manifest entries for the source must correspond
// exactly to the cases present — unknown cases, hash mismatches and stale
// entries are all rejections.
func convertFile(in, manifestPath, out string) error {
	m, err := loadCorpusManifest(manifestPath)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(in)
	if err != nil {
		return err
	}
	cases, err := parseDecTest(in, data)
	if err != nil {
		return err
	}
	declared := map[string]string{}
	for _, fx := range m.Fixtures {
		if filepath.ToSlash(fx.Source) == filepath.ToSlash(in) {
			declared[fx.ID] = fx.SHA256
		}
	}
	if len(declared) == 0 {
		return reject("manifest declares no fixtures for source %s: refusing an unmanifested conversion", in)
	}
	present := map[string]bool{}
	for _, tc := range cases {
		want, ok := declared[tc.ID]
		if !ok {
			return reject("case %s is present in %s but not in the manifest (the manifest is hand-maintained: adopt or exclude the case, never convert silently)", tc.ID, in)
		}
		if want != tc.ContentSHA {
			return reject("case %s content hash mismatch: file %s, manifest %s (corpus drift)", tc.ID, tc.ContentSHA, want)
		}
		present[tc.ID] = true
	}
	var stale []string
	for id := range declared {
		if !present[id] {
			stale = append(stale, id)
		}
	}
	sort.Strings(stale)
	if len(stale) > 0 {
		return reject("manifest declares cases absent from %s: %v (manifest drift)", in, stale)
	}
	if err := os.MkdirAll(out, 0o755); err != nil {
		return err
	}
	for _, tc := range cases {
		blob, err := json.MarshalIndent(tc, "", "  ")
		if err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(out, tc.ID+".json"), append(blob, '\n'), 0o644); err != nil {
			return err
		}
	}
	fmt.Printf("dectestconv: converted %d cases from %s, manifest-validated (%d fixture files under %s)\n",
		len(cases), in, len(cases), out)
	return nil
}

// classifyCommand runs the classification, prints its per-class and
// per-reason totals and reports drift.
func classifyCommand(dir, manifestPath, emit, list string) error {
	m, err := loadCorpusManifest(manifestPath)
	if err != nil {
		return err
	}
	byFile, computed, drift, err := classifyCorpus(dir, m)
	if err != nil {
		return err
	}
	if list != "" {
		var b strings.Builder
		b.WriteString("file\tid\tcontent_sha256\tclass\treason\n")
		for _, c := range computed {
			for _, tc := range byFile[c.Archive+"/"+c.File] {
				fmt.Fprintf(&b, "%s\t%s\t%s\t%s\t%s\n", c.Archive+"/"+c.File, tc.ID, tc.ContentSHA, tc.Class, tc.Reason)
			}
		}
		if err := os.WriteFile(list, []byte(b.String()), 0o644); err != nil {
			return err
		}
	}
	cl := classificationList(byFile, computed)
	drift = append(drift, compareClassificationList(m.ClassificationList, cl)...)
	if emit != "" {
		blob, err := json.MarshalIndent(computed, "", "  ")
		if err != nil {
			return err
		}
		if err := os.MkdirAll(emit, 0o755); err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(emit, "categories.json"), append(blob, '\n'), 0o644); err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(emit, "classification.txt"), []byte(cl), 0o644); err != nil {
			return err
		}
	}
	classes, reasons := map[string]int{}, map[string]int{}
	total := 0
	for _, c := range computed {
		total += c.Cases
		for k, v := range c.Classes {
			classes[k] += v
		}
		for k, v := range c.Reasons {
			reasons[k] += v
		}
	}
	fmt.Printf("dectestconv: %d cases in %d suite files\n", total, len(computed))
	for _, k := range slices.Sorted(maps.Keys(classes)) {
		fmt.Printf("  class  %-24s %6d\n", k, classes[k])
	}
	for _, k := range slices.Sorted(maps.Keys(reasons)) {
		fmt.Printf("  reason %-24s %6d\n", k, reasons[k])
	}
	if len(drift) > 0 {
		for _, d := range drift {
			fmt.Fprintln(os.Stderr, "drift:", d)
		}
		return reject("%d manifest drift findings: the category table no longer describes the corpus", len(drift))
	}
	return nil
}
