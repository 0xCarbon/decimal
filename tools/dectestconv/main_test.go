// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"
)

type corpusTransport func(*http.Request) (*http.Response, error)

func (f corpusTransport) RoundTrip(req *http.Request) (*http.Response, error) { return f(req) }

type trackedBody struct {
	io.Reader
	closed bool
}

func (b *trackedBody) Close() error { b.closed = true; return nil }

func installCorpusTransport(t *testing.T, transport corpusTransport) {
	t.Helper()
	old := http.DefaultTransport
	http.DefaultTransport = transport
	t.Cleanup(func() { http.DefaultTransport = old })
}

// TestProvisionHTTP pins the corpus download's bounded recovery from
// transient HTTP failures: retries never weaken the source, integrity or
// deadline checks.
func TestProvisionHTTP(t *testing.T) {
	good := []byte("corpus bytes\n")
	cf := corpusFile{Name: "fixture.decTest", Size: int64(len(good)), SHA256: sha256Hex(good)}
	for _, status := range []int{429, 500, 502, 503, 504} {
		t.Run(fmt.Sprintf("transient_%d", status), func(t *testing.T) {
			calls := 0
			var previous *trackedBody
			installCorpusTransport(t, func(req *http.Request) (*http.Response, error) {
				if previous != nil && !previous.closed {
					t.Error("previous response body still open at retry")
				}
				if req.URL.String() != "https://corpus.invalid/fixture.decTest" {
					t.Errorf("retry changed source: %s", req.URL)
				}
				calls++
				code, body := status, []byte("temporary upstream failure")
				if calls == 2 {
					code, body = http.StatusOK, good
				}
				previous = &trackedBody{Reader: bytes.NewReader(body)}
				return &http.Response{StatusCode: code, Header: http.Header{"Retry-After": {"0"}}, Body: previous}, nil
			})
			dir := t.TempDir()
			if err := verifyOrFetch(filepath.Join(dir, cf.Name), cf, "https://corpus.invalid/"); err != nil {
				t.Fatalf("transient response rejected instead of retried: %v", err)
			}
			if calls != 2 || previous == nil || !previous.closed {
				t.Fatalf("calls=%d, final body=%+v; want two closed responses", calls, previous)
			}
			data, err := os.ReadFile(filepath.Join(dir, cf.Name))
			if err != nil || !bytes.Equal(data, good) {
				t.Fatalf("published data = %q, error %v", data, err)
			}
		})
	}
	t.Run("persistent_failure_bounded", func(t *testing.T) {
		calls := 0
		var previous *trackedBody
		installCorpusTransport(t, func(req *http.Request) (*http.Response, error) {
			if previous != nil && !previous.closed {
				t.Error("previous response body still open at retry")
			}
			calls++
			previous = &trackedBody{Reader: strings.NewReader("maintenance diagnostic")}
			return &http.Response{StatusCode: 500, Header: http.Header{"Retry-After": {"0"}}, Body: previous}, nil
		})
		dir := t.TempDir()
		err := ensureCorpusFile(filepath.Join(dir, cf.Name), cf, "https://corpus.invalid/")
		if calls != 4 || err == nil || !strings.Contains(err.Error(), "maintenance diagnostic") || !strings.Contains(err.Error(), "a missing corpus is a failure, never a skip") {
			t.Fatalf("calls=%d error=%v; want four attempts and diagnostic failure", calls, err)
		}
		if previous == nil || !previous.closed {
			t.Fatal("last response body not closed")
		}
		assertEmptyDirectory(t, dir)
	})
	t.Run("descriptive_user_agent", func(t *testing.T) {
		installCorpusTransport(t, func(req *http.Request) (*http.Response, error) {
			if !strings.Contains(req.UserAgent(), "decimal") || !strings.Contains(req.UserAgent(), "https://github.com/0xCarbon/decimal") {
				t.Errorf("missing transparent User-Agent: %q", req.UserAgent())
			}
			return &http.Response{StatusCode: 200, Body: io.NopCloser(bytes.NewReader(good))}, nil
		})
		if err := verifyOrFetch(filepath.Join(t.TempDir(), cf.Name), cf, "https://corpus.invalid/"); err != nil {
			t.Fatal(err)
		}
	})
	for _, status := range []int{400, 403, 404, 501, 505} {
		t.Run(fmt.Sprintf("permanent_%d", status), func(t *testing.T) {
			calls := 0
			body := &trackedBody{Reader: strings.NewReader("permanent rejection")}
			installCorpusTransport(t, func(req *http.Request) (*http.Response, error) {
				calls++
				return &http.Response{StatusCode: status, Body: body}, nil
			})
			dir := t.TempDir()
			if err := verifyOrFetch(filepath.Join(dir, cf.Name), cf, "https://corpus.invalid/"); err == nil || calls != 1 || !body.closed {
				t.Fatalf("calls=%d closed=%v error=%v", calls, body.closed, err)
			}
			assertEmptyDirectory(t, dir)
		})
	}
	for _, name := range []string{"hash", "size", "oversize"} {
		t.Run(name+"_rejected_before_publish", func(t *testing.T) {
			want := cf
			body := good
			switch name {
			case "hash":
				want.SHA256 = strings.Repeat("0", 64)
			case "size":
				want.Size++
			case "oversize":
				body = append(slices.Clone(good), 'x')
			}
			calls := 0
			installCorpusTransport(t, func(req *http.Request) (*http.Response, error) {
				calls++
				return &http.Response{StatusCode: 200, Body: io.NopCloser(bytes.NewReader(body))}, nil
			})
			dir := t.TempDir()
			if err := ensureCorpusFile(filepath.Join(dir, cf.Name), want, "https://corpus.invalid/"); err == nil || calls != 1 {
				t.Fatalf("calls=%d error=%v; want integrity rejection without retry", calls, err)
			}
			assertEmptyDirectory(t, dir)
		})
	}
	t.Run("accurate_counts", func(t *testing.T) {
		dir := t.TempDir()
		present := cf
		present.Name = "present.decTest"
		if err := os.WriteFile(filepath.Join(dir, present.Name), good, 0o644); err != nil {
			t.Fatal(err)
		}
		calls := 0
		installCorpusTransport(t, func(req *http.Request) (*http.Response, error) {
			calls++
			return &http.Response{StatusCode: 200, Body: io.NopCloser(bytes.NewReader(good))}, nil
		})
		out, err := captureCorpusOutput(t, func() error { return provisionCorpus(dir, []corpusFile{cf, present}, "https://corpus.invalid/") })
		if err != nil || calls != 1 || !strings.Contains(out, "1 downloaded, 1 already present") {
			t.Fatalf("calls=%d error=%v output=%q", calls, err, out)
		}
		out, err = captureCorpusOutput(t, func() error { return provisionCorpus(dir, []corpusFile{cf, present}, "https://corpus.invalid/") })
		if err != nil || calls != 1 || !strings.Contains(out, "0 downloaded, 2 already present") {
			t.Fatalf("idempotent run: calls=%d error=%v output=%q", calls, err, out)
		}
	})
}

func assertEmptyDirectory(t *testing.T, dir string) {
	t.Helper()
	entries, err := os.ReadDir(dir)
	if err != nil || len(entries) != 0 {
		t.Fatalf("failed fetch left files in %s: %v, error %v", dir, entries, err)
	}
}

func captureCorpusOutput(t *testing.T, fn func() error) (string, error) {
	t.Helper()
	reader, writer, err := os.Pipe()
	if err != nil {
		t.Fatal(err)
	}
	old := os.Stdout
	os.Stdout = writer
	defer func() { os.Stdout = old }()
	err = fn()
	if closeErr := writer.Close(); closeErr != nil {
		t.Fatal(closeErr)
	}
	data, readErr := io.ReadAll(reader)
	if readErr != nil {
		t.Fatal(readErr)
	}
	if closeErr := reader.Close(); closeErr != nil {
		t.Fatal(closeErr)
	}
	return string(data), err
}

func TestCorpusRetryBudget(t *testing.T) {
	now := time.Date(2026, time.September, 22, 12, 0, 0, 0, time.UTC)
	for _, tc := range []struct {
		name, header string
		attempt      int
		want         time.Duration
	}{
		{"initial_backoff", "", 1, time.Second},
		{"second_backoff", "", 2, 2 * time.Second},
		{"third_backoff", "", 3, 4 * time.Second},
		{"zero", "0", 1, 0},
		{"seconds", "3", 1, 3 * time.Second},
		{"bounded_seconds", "9223372036854775807", 1, corpusDownloadTimeout},
		{"date", now.Add(5 * time.Second).Format(http.TimeFormat), 1, 5 * time.Second},
		{"past_date", now.Add(-time.Second).Format(http.TimeFormat), 1, 0},
		{"bounded_date", now.Add(time.Hour).Format(http.TimeFormat), 1, corpusDownloadTimeout},
		{"invalid", "invalid", 2, 2 * time.Second},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if got := corpusRetryDelay(tc.header, tc.attempt, now); got != tc.want {
				t.Fatalf("delay=%v want=%v", got, tc.want)
			}
		})
	}
	t.Run("deadline_interrupts_retry_after", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(t.Context(), 20*time.Millisecond)
		defer cancel()
		calls := 0
		body := &trackedBody{Reader: strings.NewReader("try later")}
		client := &http.Client{Transport: corpusTransport(func(req *http.Request) (*http.Response, error) {
			calls++
			return &http.Response{StatusCode: 503, Header: http.Header{"Retry-After": {"60"}}, Body: body}, nil
		})}
		_, err := downloadCorpus(ctx, client, "https://corpus.invalid/fixture", corpusFile{})
		if !errors.Is(err, context.DeadlineExceeded) || calls != 1 || !body.closed {
			t.Fatalf("calls=%d body.closed=%v error=%v", calls, body.closed, err)
		}
	})
	t.Run("deadline_interrupts_request", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(t.Context(), 20*time.Millisecond)
		defer cancel()
		calls := 0
		client := &http.Client{Transport: corpusTransport(func(req *http.Request) (*http.Response, error) {
			calls++
			<-req.Context().Done()
			return nil, req.Context().Err()
		})}
		_, err := downloadCorpus(ctx, client, "https://corpus.invalid/fixture", corpusFile{})
		if !errors.Is(err, context.DeadlineExceeded) || calls != 1 {
			t.Fatalf("calls=%d error=%v", calls, err)
		}
	})
	t.Run("cancelled_before_request", func(t *testing.T) {
		ctx, cancel := context.WithCancel(t.Context())
		cancel()
		client := &http.Client{Transport: corpusTransport(func(req *http.Request) (*http.Response, error) {
			t.Fatal("request started after total budget expired")
			return nil, errors.New("unexpected request")
		})}
		if _, err := downloadCorpus(ctx, client, "https://corpus.invalid/fixture", corpusFile{}); !errors.Is(err, context.Canceled) {
			t.Fatalf("cancellation cause lost: %v", err)
		}
	})
	t.Run("diagnostic_read_bounded", func(t *testing.T) {
		reader := strings.NewReader(strings.Repeat("x", 10000))
		body := &trackedBody{Reader: reader}
		client := &http.Client{Transport: corpusTransport(func(req *http.Request) (*http.Response, error) {
			return &http.Response{StatusCode: 403, Body: body}, nil
		})}
		_, err := downloadCorpus(t.Context(), client, "https://corpus.invalid/fixture", corpusFile{})
		if err == nil || reader.Len() != 10000-corpusDiagnosticLimit || !body.closed || len(err.Error()) > 1500 {
			t.Fatalf("remaining=%d closed=%v error=%v", reader.Len(), body.closed, err)
		}
	})
	t.Run("read_failure_never_publishes", func(t *testing.T) {
		body := &trackedBody{Reader: errorReader{}}
		installCorpusTransport(t, func(req *http.Request) (*http.Response, error) {
			return &http.Response{StatusCode: 200, Body: body}, nil
		})
		dir := t.TempDir()
		if err := verifyOrFetch(filepath.Join(dir, "fixture"), corpusFile{Size: 10}, "https://corpus.invalid/"); err == nil || !body.closed {
			t.Fatalf("read error accepted or body leaked: %v, closed=%v", err, body.closed)
		}
		assertEmptyDirectory(t, dir)
	})
	t.Run("rename_failure_removes_temporary_file", func(t *testing.T) {
		dir := t.TempDir()
		dst := filepath.Join(dir, "directory")
		if err := os.Mkdir(dst, 0o755); err != nil {
			t.Fatal(err)
		}
		if err := publishCorpusFile(dst, []byte("verified bytes")); err == nil {
			t.Fatal("publishing over a directory unexpectedly succeeded")
		}
		entries, err := os.ReadDir(dir)
		if err != nil || len(entries) != 1 || !entries[0].IsDir() {
			t.Fatalf("partial publication or temporary file leak: %v, %v", entries, err)
		}
	})
}

type errorReader struct{}

func (errorReader) Read([]byte) (int, error) { return 0, io.ErrUnexpectedEOF }

func repoPath(t *testing.T, parts ...string) string {
	t.Helper()
	return filepath.Join(append([]string{"..", ".."}, parts...)...)
}

func TestParseSampleCases(t *testing.T) {
	data, err := os.ReadFile(repoPath(t, "testdata", "dectest", "samples", "converter-samples.decTest"))
	if err != nil {
		t.Fatalf("reading sample: %v", err)
	}
	cases, err := parseDecTest("sample", data)
	if err != nil {
		t.Fatalf("parsing sample: %v", err)
	}
	if len(cases) != 3 {
		t.Fatalf("want 3 cases, got %d", len(cases))
	}
	first := cases[0]
	if first.ID != "dec012a001" || first.Op != "add" {
		t.Fatalf("first case id/op = %s/%s", first.ID, first.Op)
	}
	if len(first.Operands) != 2 || first.Operands[0] != "1.25" || first.Operands[1] != "2.50" {
		t.Fatalf("first case operands = %v", first.Operands)
	}
	if first.Expected != "3.75" || len(first.Conditions) != 0 {
		t.Fatalf("first case expected/conditions = %q/%v", first.Expected, first.Conditions)
	}
	if first.Directives["rounding"] != "half_even" {
		t.Fatalf("first case rounding = %q", first.Directives["rounding"])
	}
	third := cases[2]
	if third.Directives["rounding"] != "half_up" {
		t.Fatalf("directive change not tracked: rounding = %q", third.Directives["rounding"])
	}
	if len(third.Conditions) != 2 || third.Conditions[0] != "Inexact" || third.Conditions[1] != "Rounded" {
		t.Fatalf("third case conditions = %v", third.Conditions)
	}
}

// TestGoldenContentHash pins the content hash against values computed by an
// independent implementation. A converter
// mutation that changes any hashed field breaks this test.
func TestGoldenContentHash(t *testing.T) {
	cases := []struct {
		id   string
		want string
	}{
		{"dec012a001", "67c77eca7032337950de5fd91cc767627423c3496444ff4d30b29d13d6db8b2c"},
		{"dec012a002", "597c1abf9026c011362d0da9ff52275523c9f0c8fc49433cb459387099dc9217"},
		{"dec012a003", "70ef34acf9d0f3cb00394d185babe2a5a1679867e6435a9d74575f4dd65e415c"},
	}
	data, err := os.ReadFile(repoPath(t, "testdata", "dectest", "samples", "converter-samples.decTest"))
	if err != nil {
		t.Fatalf("reading sample: %v", err)
	}
	parsed, err := parseDecTest("sample", data)
	if err != nil {
		t.Fatalf("parsing sample: %v", err)
	}
	got := map[string]string{}
	for _, tc := range parsed {
		got[tc.ID] = tc.ContentSHA
	}
	for _, c := range cases {
		if got[c.id] != c.want {
			t.Errorf("content hash drift for %s: got %s, golden (independent implementation) %s",
				c.id, got[c.id], c.want)
		}
	}
}

func TestParseRejections(t *testing.T) {
	cases := []struct {
		name  string
		input string
		want  string
	}{
		{"unknown directive", "bogus: 1\n", "unknown directive"},
		{"bad rounding", "rounding: spin\n", "unknown rounding mode"},
		{"bad precision", "precision: nine\n", "precision must be"},
		{"bad clamp", "clamp: 2\n", "must be 0 or 1"},
		{"unterminated quote", "t001 add '1 '2 -> '3\n", "unterminated quoted operand"},
		{"missing arrow", "t001 add '1' '2' '3'\n", "no -> separator"},
		{"no operand", "t001 add -> '1'\n", "at least one operand"},
		{"no expected", "t001 add '1' '2' ->\n", "no expected value"},
		{"bad condition", "t001 add '1' '2' -> '3' 9bad\n", "invalid condition name"},
		{"quoted id", "'t001' add '1' '2' -> '3'\n", "invalid test id"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := parseDecTest("in", []byte(c.input))
			if err == nil {
				t.Fatalf("input accepted: %q", c.input)
			}
			if !strings.Contains(err.Error(), c.want) {
				t.Fatalf("error %q does not contain %q", err.Error(), c.want)
			}
		})
	}
}

func writeTemp(t *testing.T, name, content string) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), name)
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatalf("writing %s: %v", name, err)
	}
	return path
}

func sampleManifest(t *testing.T, mutate func(m map[string]any)) string {
	t.Helper()
	raw, err := os.ReadFile("testdata/dectest/manifest.json") // callers chdir to the repo root
	if err != nil {
		t.Fatalf("reading manifest: %v", err)
	}
	var m map[string]any
	if err := json.Unmarshal(raw, &m); err != nil {
		t.Fatalf("decoding manifest: %v", err)
	}
	if mutate != nil {
		mutate(m)
	}
	path := filepath.Join(t.TempDir(), "manifest.json")
	blob, err := json.MarshalIndent(m, "", "  ")
	if err != nil {
		t.Fatalf("encoding manifest: %v", err)
	}
	if err := os.WriteFile(path, blob, 0o644); err != nil {
		t.Fatalf("writing manifest: %v", err)
	}
	return path
}

const sampleSource = "testdata/dectest/samples/converter-samples.decTest"

func TestConvertValidatesAgainstManifest(t *testing.T) {
	t.Chdir(repoPath(t))
	convert := func(t *testing.T, manifest string) error {
		t.Helper()
		return convertFile(sampleSource, manifest, filepath.Join(t.TempDir(), "out"))
	}
	t.Run("valid", func(t *testing.T) {
		if err := convert(t, "testdata/dectest/manifest.json"); err != nil {
			t.Fatalf("valid conversion rejected: %v", err)
		}
	})
	t.Run("hash mismatch", func(t *testing.T) {
		manifest := sampleManifest(t, func(m map[string]any) {
			m["fixtures"].([]any)[0].(map[string]any)["sha256"] = strings.Repeat("0", 64)
		})
		err := convert(t, manifest)
		if err == nil || !strings.Contains(err.Error(), "content hash mismatch") {
			t.Fatalf("tampered hash accepted: %v", err)
		}
	})
	t.Run("stale manifest entry", func(t *testing.T) {
		manifest := sampleManifest(t, func(m map[string]any) {
			fx := map[string]any{
				"id": "dec012a099", "source": sampleSource,
				"sha256": strings.Repeat("1", 64), "adoption": "adopted", "reason": "stale",
				"package": "github.com/0xCarbon/decimal/tools/dectestconv", "test": "TestDecTestFixtures",
			}
			m["fixtures"] = append(m["fixtures"].([]any), fx)
		})
		err := convert(t, manifest)
		if err == nil || !strings.Contains(err.Error(), "manifest drift") {
			t.Fatalf("stale entry accepted: %v", err)
		}
	})
	t.Run("unmanifested source", func(t *testing.T) {
		manifest := sampleManifest(t, func(m map[string]any) {
			for _, fx := range m["fixtures"].([]any) {
				fx.(map[string]any)["source"] = "testdata/nowhere.decTest"
			}
		})
		err := convert(t, manifest)
		if err == nil || !strings.Contains(err.Error(), "no fixtures for source") {
			t.Fatalf("unmanifested conversion accepted: %v", err)
		}
	})
	t.Run("unknown adoption class", func(t *testing.T) {
		manifest := sampleManifest(t, func(m map[string]any) {
			m["fixtures"].([]any)[0].(map[string]any)["adoption"] = "wholesale"
		})
		if _, err := loadCorpusManifest(manifest); err == nil || !strings.Contains(err.Error(), "unknown adoption class") {
			t.Fatalf("bad adoption class accepted: %v", err)
		}
	})
}

func TestConvertUnmanifestedCaseRejected(t *testing.T) {
	t.Chdir(repoPath(t))
	dir := t.TempDir()
	src := filepath.Join(dir, "extra.decTest")
	content := "precision: 9\nrounding: half_even\nzzz001 add '1' '2' -> '3'\n"
	if err := os.WriteFile(src, []byte(content), 0o644); err != nil {
		t.Fatalf("writing fixture: %v", err)
	}
	err := convertFile(src, "testdata/dectest/manifest.json", filepath.Join(dir, "out"))
	if err == nil || !strings.Contains(err.Error(), "no fixtures for source") {
		t.Fatalf("unmanifested source accepted: %v", err)
	}
}

func TestProvisionLocal(t *testing.T) {
	good := []byte("corpus bytes\n")
	sum := sha256Hex(good)
	downloadList := func(entries string) string {
		return writeTemp(t, "downloads.txt", entries)
	}
	t.Run("all present and verified", func(t *testing.T) {
		dir := t.TempDir()
		if err := os.WriteFile(filepath.Join(dir, "f1.decTest"), good, 0o644); err != nil {
			t.Fatal(err)
		}
		rec := downloadList("# fixture list\nf1.decTest: 13 bytes sha256=" + sum + "\n")
		if err := provisionCorpus(dir, []corpusFile{{Name: "f1.decTest", Size: 13, SHA256: sum}}, "http://127.0.0.1:1/"); err != nil {
			t.Fatalf("valid provisioning rejected: %v", err)
		}
		_ = rec
	})
	t.Run("hash mismatch fails loudly", func(t *testing.T) {
		dir := t.TempDir()
		if err := os.WriteFile(filepath.Join(dir, "f1.decTest"), []byte("tampered\n"), 0o644); err != nil {
			t.Fatal(err)
		}
		err := provisionCorpus(dir, []corpusFile{{Name: "f1.decTest", Size: 9, SHA256: sum}}, "http://127.0.0.1:1/")
		if err == nil || !strings.Contains(err.Error(), "SHA-256 mismatch") {
			t.Fatalf("tampered corpus accepted: %v", err)
		}
	})
	t.Run("size mismatch fails loudly", func(t *testing.T) {
		dir := t.TempDir()
		if err := os.WriteFile(filepath.Join(dir, "f1.decTest"), good, 0o644); err != nil {
			t.Fatal(err)
		}
		err := provisionCorpus(dir, []corpusFile{{Name: "f1.decTest", Size: 42, SHA256: sum}}, "http://127.0.0.1:1/")
		if err == nil || !strings.Contains(err.Error(), "size mismatch") {
			t.Fatalf("size drift accepted: %v", err)
		}
	})
	t.Run("download failure fails loudly", func(t *testing.T) {
		dir := t.TempDir()
		err := provisionCorpus(dir, []corpusFile{{Name: "absent.decTest", Size: 13, SHA256: sum}}, "http://127.0.0.1:1/")
		if err == nil || !strings.Contains(err.Error(), "a missing corpus is a failure, never a skip") {
			t.Fatalf("unreachable download accepted: %v", err)
		}
	})
	t.Run("zero-entry download list refused", func(t *testing.T) {
		rec := downloadList("# empty list\n")
		if _, err := parseDownloadList(rec); err == nil || !strings.Contains(err.Error(), "zero corpus files") {
			t.Fatalf("empty download list accepted: %v", err)
		}
	})
	t.Run("malformed download list line refused", func(t *testing.T) {
		rec := downloadList("garbage line\n")
		if _, err := parseDownloadList(rec); err == nil || !strings.Contains(err.Error(), "malformed download list") {
			t.Fatalf("garbage download list accepted: %v", err)
		}
	})
}

// TestParseDirectiveTrailingComment pins that a directive followed by a "--"
// comment still sets the directive. The corpus writes
// "precision: 10  -- note"; reading such lines as test lines without "->"
// would hide rounding.decTest, squareroot.decTest, powersqrt.decTest and
// base.decTest from any conversion.
func TestParseDirectiveTrailingComment(t *testing.T) {
	input := "precision: 9\nprecision:   5           -- for easier inspection\nrounding: down -- mode\nt001 add '1' '2' -> '3'\n"
	cases, err := parseDecTest("in", []byte(input))
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	if len(cases) != 1 || cases[0].Directives["precision"] != "5" || cases[0].Directives["rounding"] != "down" {
		t.Fatalf("directives with trailing comments not applied: %+v", cases)
	}
}

// TestParseDoubleQuotedOperands pins decTest's string forms: either quote
// delimits a string, the other kind is an ordinary character inside it, and a doubled delimiter stands for one delimiter
// character. base.decTest writes toSci "12.76" (keeping the quotes inside
// the operand would turn 159 conversion cases into syntax errors) and
// '1E”1' (which must not split into two operands).
func TestParseDoubleQuotedOperands(t *testing.T) {
	input := "t001 toSci \"12.76\" -> 12.76\nt002 toSci \"'1'\" -> NaN Conversion_syntax\nt003 toSci '\"1\"' -> NaN Conversion_syntax\n" +
		"t004 toSci '1E''1' -> NaN Conversion_syntax\nt005 toSci \"1E\"\"1\" -> NaN Conversion_syntax\nt006 toSci '' -> NaN Conversion_syntax\n" +
		"t007 toSci '''1''' -> NaN Conversion_syntax\n"
	cases, err := parseDecTest("in", []byte(input))
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	want := []string{"12.76", "'1'", "\"1\"", "1E'1", "1E\"1", "", "'1'"}
	if len(cases) != len(want) {
		t.Fatalf("parsed %d cases, want %d", len(cases), len(want))
	}
	for i, tc := range cases {
		if len(tc.Operands) != 1 || tc.Operands[0] != want[i] {
			t.Fatalf("case %s operands %q, want [%q]", tc.ID, tc.Operands, want[i])
		}
	}
	if _, err := parseDecTest("in", []byte("t004 toSci \"12 -> 12\n")); err == nil ||
		!strings.Contains(err.Error(), "unterminated quoted operand") {
		t.Fatalf("unterminated double quote accepted: %v", err)
	}
}

func sha256Hex(data []byte) string {
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:])
}
