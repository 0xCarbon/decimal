// SPDX-License-Identifier: Apache-2.0

// Command checkstate audits the library package for hidden state and
// unplanned panics. It type-checks the
// non-test files that the current build selects in the given directory and
// requires that:
//
//   - every package-level variable is unexported and has a value type
//     (basic, or arrays and structs of value types), so it cannot be a knob
//     another package sets or a reference another value shares;
//   - no expression anywhere in the package, including package-level
//     initializers and function literals, writes such a variable: no
//     assignment, increment, range assignment, address-of, aliasing slice of
//     an array, pointer-receiver method call or copy/append/delete/clear
//     through it;
//   - there is no init function;
//   - panic appears only inside functions named Must followed by an
//     upper-case letter (MustParse, which is meant for literals).
//
// Names are resolved with go/types, so shadowing and aliasing through local
// declarations are handled exactly rather than by spelling.
package main

import (
	"fmt"
	"go/ast"
	"go/build"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"regexp"
	"sort"
)

var mustName = regexp.MustCompile(`^Must[A-Z]`)

// buildConfigs lists the file selections the library ships under: every
// supported GOOS/GOARCH class in both the SIMD and the scalar profile.
// Auditing only the host's selection would let scalar-only, 386-only or
// wasm-only files carry state unseen.
var buildConfigs = []struct {
	goos, goarch string
	simd         bool
}{
	{"linux", "amd64", true}, {"linux", "amd64", false},
	{"linux", "386", true}, {"linux", "386", false},
	{"linux", "arm64", true}, {"linux", "arm64", false},
	{"js", "wasm", true}, {"js", "wasm", false},
}

func buildContext(goos, goarch string, simd bool) build.Context {
	ctx := build.Default
	ctx.GOOS, ctx.GOARCH = goos, goarch
	ctx.CgoEnabled = false
	tags := make([]string, 0, len(ctx.ToolTags)+1)
	for _, tag := range ctx.ToolTags {
		if tag != "goexperiment.simd" {
			tags = append(tags, tag)
		}
	}
	if simd {
		tags = append(tags, "goexperiment.simd")
	}
	ctx.ToolTags = tags
	return ctx
}

// auditDir audits every build configuration and returns the union of
// findings, each once.
func auditDir(dir string) ([]string, error) {
	seen := map[string]bool{}
	var findings []string
	for _, c := range buildConfigs {
		ctx := buildContext(c.goos, c.goarch, c.simd)
		got, err := auditConfig(&ctx, dir)
		if err != nil {
			return nil, fmt.Errorf("%s/%s simd=%t: %w", c.goos, c.goarch, c.simd, err)
		}
		for _, f := range got {
			if !seen[f] {
				seen[f] = true
				findings = append(findings, f)
			}
		}
	}
	sort.Strings(findings)
	return findings, nil
}

func auditConfig(ctx *build.Context, dir string) ([]string, error) {
	bp, err := ctx.ImportDir(dir, 0)
	if err != nil {
		return nil, err
	}
	fset := token.NewFileSet()
	var files []*ast.File
	for _, name := range bp.GoFiles {
		file, err := parser.ParseFile(fset, filepath.Join(dir, name), nil, parser.SkipObjectResolution)
		if err != nil {
			return nil, err
		}
		files = append(files, file)
	}
	info := &types.Info{
		Defs:       map[*ast.Ident]types.Object{},
		Uses:       map[*ast.Ident]types.Object{},
		Selections: map[*ast.SelectorExpr]*types.Selection{},
		Types:      map[ast.Expr]types.TypeAndValue{},
	}
	// The source importer resolves standard packages through build.Default.
	// Library file selection above uses the audited GOOS/GOARCH, but the
	// standard-library API is the same on every target and some std
	// internals cannot be type-checked for a foreign architecture from
	// source, so the importer keeps the host target and only takes this
	// configuration's tool tags (for profile-gated packages such as simd).
	// The tool is single-threaded.
	saved := build.Default
	build.Default.ToolTags = ctx.ToolTags
	defer func() { build.Default = saved }()
	conf := types.Config{Importer: importer.ForCompiler(fset, "source", nil)}
	pkg, err := conf.Check(bp.ImportPath, fset, files, info)
	if err != nil {
		return nil, fmt.Errorf("type-check %s: %w", dir, err)
	}
	a := auditor{fset: fset, info: info, scope: pkg.Scope()}
	for _, name := range pkg.Scope().Names() {
		v, ok := pkg.Scope().Lookup(name).(*types.Var)
		if !ok {
			continue
		}
		if v.Exported() {
			a.report(v.Pos(), "exported package variable %s", name)
		}
		if !valueType(v.Type()) {
			a.report(v.Pos(), "package variable %s has reference type %s", name, v.Type())
		}
	}
	for _, file := range files {
		a.file(file)
	}
	return a.findings, nil
}

// valueType reports whether copies of t share no storage.
func valueType(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return true
	case *types.Array:
		return valueType(u.Elem())
	case *types.Struct:
		for field := range u.Fields() {
			if !valueType(field.Type()) {
				return false
			}
		}
		return true
	default:
		return false
	}
}

type auditor struct {
	fset     *token.FileSet
	info     *types.Info
	scope    *types.Scope
	findings []string
}

func (a *auditor) report(pos token.Pos, format string, args ...any) {
	p := a.fset.Position(pos)
	a.findings = append(a.findings, fmt.Sprintf("%s:%d: %s", filepath.Base(p.Filename), p.Line, fmt.Sprintf(format, args...)))
}

// global returns the package-level variable an lvalue-like expression is
// rooted at, following indexing, field selection and slicing.
func (a *auditor) global(e ast.Expr) (*types.Var, bool) {
	for {
		switch x := e.(type) {
		case *ast.Ident:
			v, ok := a.info.Uses[x].(*types.Var)
			return v, ok && v.Parent() == a.scope
		case *ast.IndexExpr:
			e = x.X
		case *ast.IndexListExpr:
			e = x.X
		case *ast.SelectorExpr:
			if sel := a.info.Selections[x]; sel == nil || sel.Kind() != types.FieldVal {
				return nil, false
			}
			e = x.X
		case *ast.SliceExpr:
			e = x.X
		case *ast.ParenExpr:
			e = x.X
		default:
			return nil, false
		}
	}
}

func (a *auditor) write(e ast.Expr, what string) {
	if v, ok := a.global(e); ok {
		a.report(e.Pos(), "%s package variable %s", what, v.Name())
	}
}

func (a *auditor) file(file *ast.File) {
	for _, decl := range file.Decls {
		if fn, ok := decl.(*ast.FuncDecl); ok && fn.Recv == nil && fn.Name.Name == "init" {
			a.report(fn.Pos(), "init function")
		}
	}
	var enclosing []string
	var visit func(n ast.Node) bool
	visit = func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncDecl:
			enclosing = append(enclosing, n.Name.Name)
			if n.Body != nil {
				ast.Inspect(n.Body, visit)
			}
			enclosing = enclosing[:len(enclosing)-1]
			return false
		case *ast.AssignStmt:
			if n.Tok != token.DEFINE {
				for _, lhs := range n.Lhs {
					a.write(lhs, "write to")
				}
			}
		case *ast.IncDecStmt:
			a.write(n.X, "write to")
		case *ast.RangeStmt:
			if n.Tok == token.ASSIGN {
				for _, e := range []ast.Expr{n.Key, n.Value} {
					if e != nil {
						a.write(e, "write to")
					}
				}
			}
		case *ast.UnaryExpr:
			if n.Op == token.AND {
				a.write(n.X, "address of")
			}
		case *ast.SliceExpr:
			if tv, ok := a.info.Types[n.X]; ok {
				if _, isString := tv.Type.Underlying().(*types.Basic); !isString {
					a.write(n.X, "aliasing slice of")
				}
			}
		case *ast.CallExpr:
			a.call(n, enclosing)
		case *ast.SelectorExpr:
			a.selector(n)
		}
		return true
	}
	ast.Inspect(file, visit)
}

func (a *auditor) call(n *ast.CallExpr, enclosing []string) {
	switch fun := n.Fun.(type) {
	case *ast.Ident:
		if b, ok := a.info.Uses[fun].(*types.Builtin); ok {
			switch b.Name() {
			case "panic":
				if len(enclosing) == 0 || !mustName.MatchString(enclosing[len(enclosing)-1]) {
					where := "package scope"
					if len(enclosing) > 0 {
						where = enclosing[len(enclosing)-1]
					}
					a.report(n.Pos(), "panic outside a Must function (%s)", where)
				}
			case "copy", "append", "delete", "clear":
				if len(n.Args) > 0 {
					a.write(n.Args[0], b.Name()+" through")
				}
			}
		}
	}
}

// selector flags a pointer-receiver method selected on a package
// variable, whether it is called directly or taken as a method value.
func (a *auditor) selector(n *ast.SelectorExpr) {
	sel := a.info.Selections[n]
	if sel == nil || sel.Kind() != types.MethodVal {
		return
	}
	if sig, ok := sel.Obj().Type().(*types.Signature); ok && sig.Recv() != nil {
		if _, pointer := sig.Recv().Type().(*types.Pointer); pointer {
			a.write(n.X, "pointer-receiver method on")
		}
	}
}

func main() {
	dir := "."
	if len(os.Args) > 1 {
		dir = os.Args[1]
	}
	findings, err := auditDir(dir)
	if err != nil {
		fmt.Fprintln(os.Stderr, "check-state:", err)
		os.Exit(1)
	}
	for _, f := range findings {
		fmt.Fprintln(os.Stderr, "check-state:", f)
	}
	if len(findings) > 0 {
		os.Exit(1)
	}
	fmt.Println("check-state: library has no mutable package state, no init and no unplanned panic")
}
