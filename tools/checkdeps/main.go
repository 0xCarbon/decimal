// SPDX-License-Identifier: Apache-2.0

// Command checkdeps audits every module of the repository. The library
// module, which holds the tools and the benchmarks, is stdlib-only; a
// separate module under tools, should one be added, may additionally use
// official golang.org/x and 0xCarbon modules; the incumbent comparison harness under
// benchmarks/incumbents may require the third-party decimal libraries it
// measures (nothing imports it). Repository code has no unsafe, assembly,
// object files or direct simd/archsimd imports. Downloaded material under
// .cache and build output under dist are not audited.
package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"go/parser"
	"go/token"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
)

type module struct {
	Path    string
	Main    bool
	Replace *module
}

func approved(path string) bool {
	return strings.HasPrefix(path, "golang.org/x/") || strings.HasPrefix(path, "github.com/0xCarbon/")
}

// incumbents are the third-party modules the comparison harness may require:
// the four measured decimal libraries and their transitive requirements.
var incumbents = map[string]bool{
	"github.com/cockroachdb/apd/v3":    true,
	"github.com/ericlagergren/decimal": true,
	"github.com/govalues/decimal":      true,
	"github.com/shopspring/decimal":    true,
	"github.com/lib/pq":                true, // required by apd's go.mod
}

// policy is the dependency rule a module is audited under.
type policy int

const (
	stdlibOnly policy = iota // the library module
	toolPolicy               // a separate tool module: approved modules only
	comparison               // the incumbent harness: approved modules and incumbents
)

// policyFor returns the rule for the module whose go.mod is at rel.
func policyFor(rel string) policy {
	rel = filepath.ToSlash(rel)
	switch {
	case strings.HasPrefix(rel, "tools/"):
		return toolPolicy
	case strings.HasPrefix(rel, "benchmarks/incumbents/"):
		return comparison
	}
	return stdlibOnly
}

func auditGraph(data []byte, p policy) error {
	dec := json.NewDecoder(bytes.NewReader(data))
	count := 0
	for {
		var m module
		if err := dec.Decode(&m); err != nil {
			if errors.Is(err, io.EOF) {
				break
			}
			return fmt.Errorf("module graph: %w", err)
		}
		count++
		if m.Path == "" {
			return errors.New("module graph contains an empty module path")
		}
		if m.Main {
			continue
		}
		if p == comparison {
			// The harness measures this repository's library in place.
			if m.Path == "github.com/0xCarbon/decimal" && m.Replace != nil && m.Replace.Path == "../.." {
				continue
			}
			if !incumbents[m.Path] && !approved(m.Path) {
				return fmt.Errorf("prohibited dependency %s", m.Path)
			}
		} else if p != toolPolicy || !approved(m.Path) {
			return fmt.Errorf("prohibited dependency %s", m.Path)
		}
		if m.Replace != nil && !approved(m.Replace.Path) {
			return fmt.Errorf("prohibited replacement for %s: %s", m.Path, m.Replace.Path)
		}
	}
	if count == 0 {
		return errors.New("empty module graph")
	}
	return nil
}

func audit(root string) error {
	return filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			rel, err := filepath.Rel(root, path)
			if err != nil {
				return err
			}
			switch rel {
			case ".git", ".cache", "dist", "node_modules":
				return filepath.SkipDir
			}
			return nil
		}
		switch filepath.Ext(d.Name()) {
		case ".s", ".S", ".sx", ".syso":
			return fmt.Errorf("%s: project-authored assembly or object file prohibited", path)
		}
		if filepath.Ext(d.Name()) == ".go" {
			file, err := parser.ParseFile(token.NewFileSet(), path, nil, parser.ImportsOnly)
			if err != nil {
				return fmt.Errorf("%s: parse imports: %w", path, err)
			}
			for _, spec := range file.Imports {
				name, err := strconv.Unquote(spec.Path.Value)
				if err != nil {
					return fmt.Errorf("%s: import path: %w", path, err)
				}
				if name == "unsafe" {
					return fmt.Errorf("%s: project-authored unsafe import prohibited", path)
				}
				if name == "simd/archsimd" || strings.HasPrefix(name, "simd/archsimd/") {
					return fmt.Errorf("%s: direct simd/archsimd import prohibited; use the portable simd package", path)
				}
			}
			return nil
		}
		if d.Name() != "go.mod" && !strings.HasSuffix(d.Name(), ".mod") {
			return nil
		}
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		args := []string{"list", "-m", "-json"}
		dir := filepath.Dir(path)
		if d.Name() != "go.mod" {
			args = append(args, "-modfile="+path)
			dir = root
		}
		args = append(args, "all")
		cmd := exec.Command("go", args...)
		cmd.Dir = dir
		cmd.Env = append(os.Environ(), "CGO_ENABLED=0", "GOWORK=off", "GOTOOLCHAIN=local", "GOFLAGS=-mod=readonly")
		var stderr bytes.Buffer
		cmd.Stderr = &stderr
		out, err := cmd.Output()
		if err != nil {
			return fmt.Errorf("%s: go list failed: %w\n%s", rel, err, stderr.String())
		}
		if err := auditGraph(out, policyFor(rel)); err != nil {
			return fmt.Errorf("%s: %w", rel, err)
		}
		if rel == "go.mod" {
			if err := auditLibraryPackage(dir); err != nil {
				return fmt.Errorf("%s: %w", rel, err)
			}
		}
		fmt.Printf("check-deps: %s passed\n", rel)
		return nil
	})
}

// libraryConfigs lists every file selection the library ships under; the
// dependency closure is audited in each so profile- or target-gated files
// cannot hide an import.
var libraryConfigs = [][]string{
	{"GOOS=linux", "GOARCH=amd64", "GOEXPERIMENT=simd"}, {"GOOS=linux", "GOARCH=amd64", "GOEXPERIMENT="},
	{"GOOS=linux", "GOARCH=386", "GOEXPERIMENT=simd"}, {"GOOS=linux", "GOARCH=386", "GOEXPERIMENT="},
	{"GOOS=linux", "GOARCH=arm64", "GOEXPERIMENT=simd"}, {"GOOS=linux", "GOARCH=arm64", "GOEXPERIMENT="},
	{"GOOS=js", "GOARCH=wasm", "GOEXPERIMENT=simd"}, {"GOOS=js", "GOARCH=wasm", "GOEXPERIMENT="},
}

// auditLibraryPackage requires that the root package's dependency closure
// holds only standard-library packages and the package itself in
// every shipped configuration. The module graph cannot see in-module
// packages such as internal/..., so this closes the gap through go list -deps.
func auditLibraryPackage(dir string) error {
	for _, config := range libraryConfigs {
		env := append(os.Environ(), "CGO_ENABLED=0", "GOWORK=off", "GOTOOLCHAIN=local", "GOFLAGS=-mod=readonly")
		env = append(env, config...)
		run := func(args ...string) (string, error) {
			cmd := exec.Command("go", args...)
			cmd.Dir = dir
			cmd.Env = env
			var stderr bytes.Buffer
			cmd.Stderr = &stderr
			out, err := cmd.Output()
			if err != nil {
				return "", fmt.Errorf("go %s (%s) failed: %w\n%s", strings.Join(args, " "), strings.Join(config, " "), err, stderr.String())
			}
			return string(out), nil
		}
		deps, err := run("list", "-deps", "-f", "{{if not .Standard}}{{.ImportPath}}{{end}}", ".")
		if err != nil {
			return err
		}
		self, err := run("list", "-f", "{{.ImportPath}}", ".")
		if err != nil {
			return err
		}
		root := strings.TrimSpace(self)
		for line := range strings.Lines(deps) {
			if path := strings.TrimSpace(line); path != "" && path != root {
				return fmt.Errorf("library package has non-standard dependency %s under %s", path, strings.Join(config, " "))
			}
		}
	}
	return nil
}

func main() {
	root, err := os.Getwd()
	if err == nil {
		err = audit(root)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "check-deps:", err)
		os.Exit(1)
	}
}
