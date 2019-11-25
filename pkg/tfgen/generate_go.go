// Copyright 2016-2018, Pulumi Corporation.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Pulling out some of the repeated strings tokens into constants would harm readability, so we just ignore the
// goconst linter's warning.
//
// nolint: goconst
package tfgen

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strconv"
	"strings"

	"github.com/golang/glog"
	"github.com/hashicorp/terraform-plugin-sdk/helper/schema"
	"github.com/pkg/errors"
	"github.com/pulumi/pulumi/pkg/diag"
	"github.com/pulumi/pulumi/pkg/tools"
	"github.com/pulumi/pulumi/pkg/util/cmdutil"
	"github.com/pulumi/pulumi/pkg/util/contract"

	"github.com/pulumi/pulumi-terraform-bridge/pkg/tfbridge"
)

// newGoGenerator returns a language generator that understands how to produce Go packages.
func newGoGenerator(pkg, version string, info tfbridge.ProviderInfo, overlaysDir, outDir string) langGenerator {
	return &goGenerator{
		pkg:         pkg,
		version:     version,
		info:        info,
		overlaysDir: overlaysDir,
		outDir:      outDir,
	}
}

type goGenerator struct {
	pkg         string
	version     string
	info        tfbridge.ProviderInfo
	overlaysDir string
	outDir      string
	needsUtils  bool
}

type goTypeKind int

const (
	goKindInput  = 1 << 1
	goKindOutput = 1 << 2
	goKindPlain  = 1 << 3
)

type goNestedType struct {
	declarer declarer
	kinds    goTypeKind
	typ      *propertyType
}

type goNestedTypes struct {
	memberNames map[string]bool
	nameToType  map[string]*goNestedType
	perDeclarer map[declarer][]*goNestedType
}

// Each nested input type needs an `Input` interface, an inputty type that implements that interface, and a plain
// type.
//
// Each nested output type needs an `Output` type and a plain type. If the output type has a corresponding input
// type, it does not need to redefine the plain type, and its `Output` type should implement the `Input` inerface.
//
// Nested types include array types.
func gatherGoNestedTypesForModule(mod *module) *goNestedTypes {
	nt := &goNestedTypes{
		memberNames: make(map[string]bool),
		nameToType:  make(map[string]*goNestedType),
		perDeclarer: make(map[declarer][]*goNestedType),
	}

	for _, member := range mod.members {
		nt.memberNames[member.Name()] = true
	}

	for _, member := range mod.members {
		switch member := member.(type) {
		case *resourceType:
			nt.gatherFromProperties(member, member.name, "", member.inprops, goKindInput|goKindOutput|goKindPlain)
			nt.gatherFromProperties(member, member.name, "", member.outprops, goKindOutput|goKindPlain)
			if !member.IsProvider() {
				nt.gatherFromProperties(member, member.name, "", member.statet.properties, goKindInput|goKindOutput|goKindPlain)
			}
		case *resourceFunc:
			name := strings.Title(member.name)
			nt.gatherFromProperties(member, name, "Args", member.args, goKindPlain)
			nt.gatherFromProperties(member, name, "Result", member.rets, goKindPlain)
		case *variable:
			nt.gatherFromPropertyType(member, member.name, "", "", member.typ, goKindPlain)
		}
	}

	return nt
}

func (nt *goNestedTypes) getDeclaredTypes(declarer declarer) []*goNestedType {
	return nt.perDeclarer[declarer]
}

func (nt *goNestedTypes) declareType(
	declarer declarer, namePrefix, name, nameSuffix string, typ *propertyType, goKinds goTypeKind) string {

	// Generate a name for this nested type.
	baseName := namePrefix + strings.Title(name)

	// Override the nested type name, if necessary.
	if typ.nestedType.Name().String() != "" {
		baseName = typ.nestedType.Name().String()
	}

	nameSuffix = strings.Title(nameSuffix)

	// If there is already a module member with this name, disambiguate based on the declarer type.
	typeName := baseName + nameSuffix
	if nt.memberNames[typeName] {
		switch declarer.(type) {
		case *resourceType:
			typeName = baseName + "Resource" + nameSuffix
		case *resourceFunc:
			typeName = baseName + "Func" + nameSuffix
		case *variable:
			typeName = baseName + "Var" + nameSuffix
		}
	}

	typ.name = typeName

	if existing := nt.nameToType[typeName]; existing != nil {
		if existing.declarer != declarer {
			contract.Failf("Nested type %q declared by %s was already declared by %s",
				typeName, existing.declarer.Name(), declarer.Name())
		}
		existing.kinds |= goKinds
		return baseName
	}

	t := &goNestedType{
		declarer: declarer,
		kinds:    goKinds,
		typ:      typ,
	}

	nt.nameToType[typeName] = t
	nt.perDeclarer[declarer] = append(nt.perDeclarer[declarer], t)

	return baseName
}

func (nt *goNestedTypes) gatherFromProperties(
	declarer declarer, namePrefix, nameSuffix string, ps []*variable, goKinds goTypeKind) {

	for _, p := range ps {
		nt.gatherFromPropertyType(declarer, namePrefix, p.name, nameSuffix, p.typ, goKinds)
	}
}

func (nt *goNestedTypes) gatherFromPropertyType(
	declarer declarer, namePrefix, name, nameSuffix string, typ *propertyType, goKinds goTypeKind) {

	switch typ.kind {
	case kindList, kindSet:
		if typ.element != nil {
			nt.gatherFromPropertyType(declarer, namePrefix, name, nameSuffix, typ.element, goKinds)
			if goKinds != goKindPlain && typ.element.kind == kindObject {
				nt.declareType(declarer, "", typ.element.name+"Array", nameSuffix, typ, goKinds)
			}
		}
	case kindMap:
		if typ.element != nil {
			nt.gatherFromPropertyType(declarer, namePrefix, name, nameSuffix, typ.element, goKinds)
			if goKinds != goKindPlain && typ.element.kind == kindObject {
				nt.declareType(declarer, "", typ.element.name+"Map", nameSuffix, typ, goKinds)
			}
		}
	case kindObject:
		baseName := nt.declareType(declarer, namePrefix, name, nameSuffix, typ, goKinds)
		nt.gatherFromProperties(declarer, baseName, nameSuffix, typ.properties, goKinds)
	}
}

// commentChars returns the comment characters to use for single-line comments.
func (g *goGenerator) commentChars() string {
	return "//"
}

// moduleDir returns the directory for the given module.
func (g *goGenerator) moduleDir(mod *module) string {
	dir := filepath.Join(g.outDir, g.pkg)
	if mod.name != "" {
		dir = filepath.Join(dir, mod.name)
	}
	return dir
}

type imports struct {
	Errors         bool // true to import github.com/pkg/errors.
	Pulumi         bool // true to import github.com/pulumi/pulumi/sdk/go/pulumi.
	Config         bool // true to import github.com/pulumi/pulumi/sdk/go/pulumi/config.
	ReflectContext bool // true to import reflect and context.
}

// openWriter opens a writer for the given module and file name, emitting the standard header automatically.
func (g *goGenerator) openWriter(mod *module, name string, ims imports) (*tools.GenWriter, error) {
	dir := g.moduleDir(mod)
	file := filepath.Join(dir, name)
	w, err := tools.NewGenWriter(tfgen, file)
	if err != nil {
		return nil, err
	}

	// Emit a standard warning header ("do not edit", etc).
	w.EmitHeaderWarning(g.commentChars())

	// Emit the Go package name.
	pkg := g.goPackageName(mod)
	w.Writefmtln("package %s", pkg)
	w.Writefmtln("")

	// If needed, emit import statements.
	g.emitImports(w, ims)

	return w, nil
}

// goPackageName returns the Go package name for this module (package if no sub-module, module otherwise).
func (g *goGenerator) goPackageName(mod *module) string {
	if mod.name == "" {
		return g.pkg
	}
	return mod.name
}

func (g *goGenerator) emitImports(w *tools.GenWriter, ims imports) {
	if ims.Errors || ims.Pulumi || ims.Config || ims.ReflectContext {
		w.Writefmtln("import (")
		if ims.ReflectContext {
			w.Writefmtln("\t\"context\"")
			w.Writefmtln("\t\"reflect\"")
		}
		if ims.Errors {
			w.Writefmtln("\t\"github.com/pkg/errors\"")
		}
		if ims.Pulumi {
			w.Writefmtln("\t\"github.com/pulumi/pulumi/sdk/go/pulumi\"")
		}
		if ims.Config {
			w.Writefmtln("\t\"github.com/pulumi/pulumi/sdk/go/pulumi/config\"")
		}
		w.Writefmtln(")")
		w.Writefmtln("")
	}
}

// emitPackage emits an entire package pack into the configured output directory with the configured settings.
func (g *goGenerator) emitPackage(pack *pkg) error {
	// Ensure that we have a root module.
	root := pack.modules.ensureModule("")
	if pack.provider != nil {
		root.members = append(root.members, pack.provider)
	}

	// Generate individual modules and their contents as packages.
	if err := g.emitModules(pack.modules); err != nil {
		return err
	}

	// Finally emit the non-code package metadata.
	return g.emitPackageMetadata(pack)
}

// emitModules emits all modules in the given module map.  It returns a full list of files, a map of module to its
// associated index, and any error that occurred, if any.
func (g *goGenerator) emitModules(mmap moduleMap) error {
	for _, mod := range mmap.values() {
		if err := g.emitModule(mod); err != nil {
			return err
		}
	}
	return nil
}

// emitModule emits a module as a Go package.  This emits a single file per member just for ease of managemnet.
// For example, imagine a module m with many members; the result is:
//
//     m/
//         m.go
//         member1.go
//         member<etc>.go
//         memberN.go
//
// The one special case is the configuration module, which yields a vars.ts file containing all exported variables.
//
// Note that the special module "" represents the top-most package module and won't be placed in a sub-directory.
func (g *goGenerator) emitModule(mod *module) error {
	glog.V(3).Infof("emitModule(%s)", mod.name)

	defer func() { g.needsUtils = false }()

	// Ensure that the target module directory exists.
	dir := g.moduleDir(mod)
	if err := tools.EnsureDir(dir); err != nil {
		return errors.Wrapf(err, "creating module directory")
	}

	// Gather the nested types for this module.
	nested := gatherGoNestedTypesForModule(mod)

	// Ensure that the module has a module-wide comment.
	if err := g.ensurePackageComment(mod, dir); err != nil {
		return errors.Wrapf(err, "creating module comment file")
	}

	// Now, enumerate each module member, in the order presented to us, and do the right thing.
	for _, member := range mod.members {
		if err := g.emitModuleMember(mod, member, nested); err != nil {
			return errors.Wrapf(err, "emitting module %s member %s", mod.name, member.Name())
		}
	}

	// If this is a config module, we need to emit the configuration variables.
	//
	// TODO(pdg): emit nested config types
	if mod.config() {
		if err := g.emitConfigVariables(mod); err != nil {
			return errors.Wrapf(err, "emitting config module variables")
		}
	}

	// If any part of this module needs internal utilities, emit them now.
	if g.needsUtils {
		if err := g.emitUtilities(mod); err != nil {
			return errors.Wrapf(err, "emitting utilities file")
		}
	}

	return nil
}

// ensurePackageComment writes out a file with a module-wide comment, provided one doesn't already exist.
func (g *goGenerator) ensurePackageComment(mod *module, dir string) error {
	pkg := g.goPackageName(mod)
	rf := filepath.Join(dir, "_about.go")
	_, err := os.Stat(rf)
	if err == nil {
		return nil // file already exists, exit right away.
	} else if !os.IsNotExist(err) {
		return err // legitimate error, propagate it.
	}

	// If we got here, the module comment file doesn't already exist -- write out a stock one.
	w, err := tools.NewGenWriter(tfgen, rf)
	if err != nil {
		return err
	}
	defer contract.IgnoreClose(w)

	w.Writefmtln("//nolint: lll")
	// Fake up a comment that makes it clear to Go that this is a module-wide comment.
	w.Writefmtln("// Package %[1]s exports types, functions, subpackages for provisioning %[1]s resources.", pkg)
	w.Writefmtln("//")

	downstreamLicense := g.info.GetTFProviderLicense()
	licenseTypeURL := getLicenseTypeURL(downstreamLicense)
	readme := fmt.Sprintf(standardDocReadme, g.pkg, g.info.Name, g.info.GetGitHubOrg(), downstreamLicense, licenseTypeURL)
	for _, line := range strings.Split(readme, "\n") {
		w.Writefmtln("// %s", line)
	}

	w.Writefmtln("package %s", pkg)

	return nil
}

// emitModuleMember emits the given member into its own file.
func (g *goGenerator) emitModuleMember(mod *module, member moduleMember, nested *goNestedTypes) error {
	glog.V(3).Infof("emitModuleMember(%s, %s)", mod, member.Name())

	switch t := member.(type) {
	case *resourceType:
		return g.emitResourceType(mod, t, nested)
	case *resourceFunc:
		return g.emitResourceFunc(mod, t, nested)
	case *variable:
		contract.Assertf(mod.config(),
			"only expected top-level variables in config module (%s is not one)", mod.name)
		// skip the variable, we will process it later.
		return nil
	case *overlayFile:
		return g.emitOverlay(mod, t)
	default:
		contract.Failf("unexpected member type: %v", reflect.TypeOf(member))
		return nil
	}
}

// emitConfigVariables emits all config vaiables in the given module into its own file.
func (g *goGenerator) emitConfigVariables(mod *module) error {
	// Create a single file into which all configuration variables will go.
	w, err := g.openWriter(mod, "config.go", imports{Pulumi: true, Config: true})
	if err != nil {
		return err
	}
	defer contract.IgnoreClose(w)

	// Ensure we import any custom schemas referenced by the variables.
	var infos []*tfbridge.SchemaInfo
	for _, member := range mod.members {
		if v, ok := member.(*variable); ok {
			infos = append(infos, v.info)
		}
	}
	if err = g.emitCustomImports(w, mod, infos); err != nil {
		return err
	}

	// For each config variable, emit a helper function that reads from the context.
	for i, member := range mod.members {
		if v, ok := member.(*variable); ok {
			g.emitConfigAccessor(w, v)
		}
		if i != len(mod.members)-1 {
			w.Writefmtln("")
		}
	}

	return nil
}

func (g *goGenerator) emitConfigAccessor(w *tools.GenWriter, v *variable) {
	getfunc := "Get"

	var gettype string
	var functype string
	switch v.schema.Type {
	case schema.TypeBool:
		gettype, functype = "bool", "Bool"
	case schema.TypeInt:
		gettype, functype = "int", "Int"
	case schema.TypeFloat:
		gettype, functype = "float64", "Float64"
	default:
		gettype, functype = "string", ""
	}

	if v.doc != "" && v.doc != elidedDocComment {
		g.emitDocComment(w, v.doc, v.docURL, "")
	} else if v.rawdoc != "" {
		g.emitRawDocComment(w, v.rawdoc, "")
	}

	defaultValue, configKey := g.goDefaultValue(v), fmt.Sprintf("\"%s:%s\"", g.pkg, v.name)

	w.Writefmtln("func Get%s(ctx *pulumi.Context) %s {", upperFirst(v.name), gettype)
	if defaultValue != "" {
		w.Writefmtln("\tv, err := config.Try%s(ctx, %s)", functype, configKey)
		w.Writefmtln("\tif err == nil {")
		w.Writefmtln("\t\treturn v")
		w.Writefmtln("\t}")
		w.Writefmtln("\tif dv, ok := %s.(%s); ok {", defaultValue, gettype)
		w.Writefmtln("\t\treturn dv")
		w.Writefmtln("\t}")
		w.Writefmtln("\treturn v")
	} else {
		w.Writefmtln("\treturn config.%s%s(ctx, \"%s:%s\")", getfunc, functype, g.pkg, v.name)
	}

	w.Writefmtln("}")
}

// emitUtilities
func (g *goGenerator) emitUtilities(mod *module) error {
	// Open the utilities.ts file for this module and ready it for writing.
	w, err := g.openWriter(mod, "internal_utilities.go", imports{})
	if err != nil {
		return err
	}
	defer contract.IgnoreClose(w)

	// TODO: use w.WriteString
	w.Writefmt(goUtilitiesFile)
	return nil
}

func (g *goGenerator) emitDocComment(w *tools.GenWriter, comment, docURL, prefix string) {
	if comment == elidedDocComment && docURL == "" {
		return
	}

	if comment != elidedDocComment {
		lines := strings.Split(comment, "\n")
		for i, docLine := range lines {
			// Break if we get to the last line and it's empty
			if i == len(lines)-1 && strings.TrimSpace(docLine) == "" {
				break
			}
			// Print the line of documentation
			w.Writefmtln("%s// %s", prefix, docLine)
		}

		if docURL != "" {
			w.Writefmtln("%s//", prefix)
		}
	}

	if docURL != "" {
		w.Writefmtln("%s// > This content is derived from %s.", prefix, docURL)
	}
}

func (g *goGenerator) emitRawDocComment(w *tools.GenWriter, comment, prefix string) {
	if comment != "" {
		curr := 0
		w.Writefmt("%s// ", prefix)
		for _, word := range strings.Fields(comment) {
			word = sanitizeForDocComment(word)
			if curr > 0 {
				if curr+len(word)+1 > (maxWidth - len(prefix)) {
					curr = 0
					w.Writefmt("\n%s// ", prefix)
				} else {
					w.Writefmt(" ")
					curr++
				}
			}
			w.Writefmt(word)
			curr += len(word)
		}
		w.Writefmtln("")
	}
}

type goResourceGenerator struct {
	g *goGenerator

	mod    *module
	res    *resourceType
	fun    *resourceFunc
	nested []*goNestedType

	name string
	w    *tools.GenWriter
}

func newGoResourceGenerator(g *goGenerator, mod *module, res *resourceType,
	nested *goNestedTypes) *goResourceGenerator {

	return &goResourceGenerator{
		g:      g,
		mod:    mod,
		res:    res,
		nested: nested.getDeclaredTypes(res),
		name:   res.name,
	}
}

func newGoDatasourceGenerator(g *goGenerator, mod *module, fun *resourceFunc,
	nested *goNestedTypes) *goResourceGenerator {

	return &goResourceGenerator{
		g:      g,
		mod:    mod,
		fun:    fun,
		nested: nested.getDeclaredTypes(fun),
		name:   fun.name,
	}
}

func (rg *goResourceGenerator) emit() error {
	// Create a resource source file into which all of this resource's types will go.
	imps := rg.getImports()
	w, err := rg.g.openWriter(rg.mod, lowerFirst(rg.name)+".go", imps)
	if err != nil {
		return err
	}
	defer contract.IgnoreClose(w)
	rg.w = w

	if rg.res != nil {
		if err = rg.generateResourceType(); err != nil {
			return err
		}
	} else {
		contract.Assert(rg.fun != nil)
		if err = rg.generateDatasourceFunc(); err != nil {
			return err
		}
	}
	rg.generateNestedTypes()

	return nil
}

func (rg *goResourceGenerator) getImports() imports {
	imps := imports{Pulumi: true}

	// If we have any nested input or output types, we need to import reflect.
	for _, nt := range rg.nested {
		if nt.kinds&(goKindInput|goKindOutput) != 0 {
			imps.ReflectContext = true
			break
		}
	}

	// See if we'll be generating an error. If yes, we need to import.
	if rg.res != nil {
		for _, prop := range rg.res.inprops {
			if !prop.optional() {
				imps.Errors = true
				break
			}
		}
	}

	return imps
}

func (rg *goResourceGenerator) generateResourceType() error {
	name := rg.res.name

	// Ensure that we've emitted any custom imports pertaining to any of the field types.
	var fldinfos []*tfbridge.SchemaInfo
	for _, fldinfo := range rg.res.info.Fields {
		fldinfos = append(fldinfos, fldinfo)
	}
	if err := rg.g.emitCustomImports(rg.w, rg.mod, fldinfos); err != nil {
		return err
	}

	// Define the resource type structure, just a basic wrapper around the resource registration information.
	if rg.res.doc != "" {
		rg.g.emitDocComment(rg.w, rg.res.doc, rg.res.docURL, "")
	}
	if !rg.res.IsProvider() {
		if rg.res.info.DeprecationMessage != "" {
			rg.w.Writefmtln("// Deprecated: %s", rg.res.info.DeprecationMessage)
		}
	}
	rg.w.Writefmtln("type %s struct {", name)
	if rg.res.IsProvider() {
		rg.w.Writefmtln("\tpulumi.ProviderResourceState")
	} else {
		rg.w.Writefmtln("\tpulumi.CustomResourceState")
	}
	for _, prop := range rg.res.outprops {
		rg.w.Writefmtln("")

		if prop.doc != "" && prop.doc != elidedDocComment {
			rg.g.emitDocComment(rg.w, prop.doc, prop.docURL, "\t")
		} else if prop.rawdoc != "" {
			rg.g.emitRawDocComment(rg.w, prop.rawdoc, "\t")
		}

		outType := goOutputPropertyType(prop)
		rg.w.Writefmtln("\t%s %s `pulumi:\"%s\"`", upperFirst(prop.name), outType, prop.name)
	}
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")

	// Create a constructor function that registers a new instance of this resource.
	argsType := rg.res.argst.name
	rg.w.Writefmtln("// New%s registers a new resource with the given unique name, arguments, and options.", name)
	if rg.res.info.DeprecationMessage != "" {
		rg.w.Writefmtln("// Deprecated: %s", rg.res.info.DeprecationMessage)
	}
	rg.w.Writefmtln("func New%s(ctx *pulumi.Context,", name)
	rg.w.Writefmtln("\tname string, args *%s, opts ...pulumi.ResourceOption) (*%s, error) {", argsType, name)

	// Ensure required arguments are present.
	for _, prop := range rg.res.inprops {
		if !prop.optional() {
			rg.w.Writefmtln("\tif args == nil || args.%s == nil {", upperFirst(prop.name))
			rg.w.Writefmtln("\t\treturn nil, errors.New(\"missing required argument '%s'\")", upperFirst(prop.name))
			rg.w.Writefmtln("\t}")
		}
	}

	// Produce the input map.
	rg.w.Writefmtln("\tinputs := map[string]pulumi.Input{}")
	hasDefault := make(map[*variable]bool)
	for _, prop := range rg.res.inprops {
		if defaultValue := rg.g.goDefaultValue(prop); defaultValue != "" {
			hasDefault[prop] = true
			rg.w.Writefmtln("\tinputs[\"%s\"] = %s", prop.name, defaultValue)
		}
	}
	rg.w.Writefmtln("\tif args != nil {")
	for _, prop := range rg.res.inprops {
		rg.w.Writefmtln("\t\tif i := args.%s; i != nil { inputs[\"%s\"] = i%s }",
			upperFirst(prop.name), prop.name, goOutputMethod(prop))
	}
	rg.w.Writefmtln("\t}")

	// Finally make the call to registration.
	rg.w.Writefmtln("\tvar resource %s", name)
	rg.w.Writefmtln("\terr := ctx.RegisterResource(\"%s\", name, inputs, &resource, opts...)", rg.res.info.Tok)
	rg.w.Writefmtln("\tif err != nil {")
	rg.w.Writefmtln("\t\treturn nil, err")
	rg.w.Writefmtln("\t}")
	rg.w.Writefmtln("\treturn &resource, nil")
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")

	// Emit a factory function that reads existing instances of this resource.
	if !rg.res.IsProvider() {
		stateType := rg.res.statet.name
		rg.w.Writefmtln("// Get%[1]s gets an existing %[1]s resource's state with the given name, ID, and optional", name)
		rg.w.Writefmtln("// state properties that are used to uniquely qualify the lookup (nil if not required).")
		if rg.res.info.DeprecationMessage != "" {
			rg.w.Writefmtln("// Deprecated: %s", rg.res.info.DeprecationMessage)
		}
		rg.w.Writefmtln("func Get%s(ctx *pulumi.Context,", name)
		rg.w.Writefmtln("\tname string, id pulumi.IDInput, state *%s, opts ...pulumi.ResourceOption) (*%s, error) {",
			stateType, name)
		rg.w.Writefmtln("\tinputs := map[string]pulumi.Input{}")
		rg.w.Writefmtln("\tif state != nil {")
		for _, prop := range rg.res.outprops {
			rg.w.Writefmtln("\t\tif i := state.%s; i != nil { inputs[\"%s\"] = i%s }",
				upperFirst(prop.name), prop.name, goOutputMethod(prop))
		}
		rg.w.Writefmtln("\t}")
		rg.w.Writefmtln("\tvar resource %s", name)
		rg.w.Writefmtln("\terr := ctx.ReadResource(\"%s\", name, id, inputs, &resource, opts...)", rg.res.info.Tok)
		rg.w.Writefmtln("\tif err != nil {")
		rg.w.Writefmtln("\t\treturn nil, err")
		rg.w.Writefmtln("\t}")
		rg.w.Writefmtln("\treturn &resource, nil")
		rg.w.Writefmtln("}")
		rg.w.Writefmtln("")

		// Emit the state type for get methods.
		rg.generatePlainType(rg.res.statet, true)
		rg.w.Writefmtln("")
	}

	// Emit the argument type for construction.
	rg.generatePlainType(rg.res.argst, true)

	return nil
}

func (rg *goResourceGenerator) generateDatasourceFunc() error {
	// Ensure that we've emitted any custom imports pertaining to any of the field types.
	var fldinfos []*tfbridge.SchemaInfo
	for _, fldinfo := range rg.fun.info.Fields {
		fldinfos = append(fldinfos, fldinfo)
	}
	if err := rg.g.emitCustomImports(rg.w, rg.mod, fldinfos); err != nil {
		return err
	}

	// Write the TypeDoc/JSDoc for the data source function.
	if rg.fun.doc != "" {
		rg.g.emitDocComment(rg.w, rg.fun.doc, rg.fun.docURL, "")
	}

	if rg.fun.info.DeprecationMessage != "" {
		rg.w.Writefmtln("// Deprecated: %s", rg.fun.info.DeprecationMessage)
	}

	// If the function starts with New or Get, it will conflict; so rename them.
	funname := upperFirst(rg.fun.name)
	if strings.Index(funname, "New") == 0 {
		funname = "Create" + funname[3:]
	} else if strings.Index(funname, "Get") == 0 {
		funname = "Lookup" + funname[3:]
	}

	// Now, emit the function signature.
	argsig := "ctx *pulumi.Context"
	if rg.fun.argst != nil {
		argsig = fmt.Sprintf("%s, args *%s", argsig, rg.fun.argst.name)
	}
	var retty string
	if rg.fun.retst == nil {
		retty = "error"
	} else {
		retty = fmt.Sprintf("(*%s, error)", rg.fun.retst.name)
	}
	rg.w.Writefmtln("func %s(%s, opts ...pulumi.InvokeOption) %s {", funname, argsig, retty)

	// Make a map of inputs to pass to the runtime function.
	var inputsVar string
	if rg.fun.argst == nil {
		inputsVar = "nil"
	} else {
		inputsVar = "args"
	}

	// Now simply invoke the runtime function with the arguments.
	var outputsType string
	if rg.fun.retst == nil {
		outputsType = "struct{}"
	} else {
		outputsType = rg.fun.retst.name
	}
	rg.w.Writefmtln("\tvar rv %s", outputsType)
	rg.w.Writefmtln("\terr := ctx.Invoke(\"%s\", %s, &rv, opts...)", rg.fun.info.Tok, inputsVar)

	if rg.fun.retst == nil {
		rg.w.Writefmtln("\treturn err")
	} else {
		// Check the error before proceeding.
		rg.w.Writefmtln("\tif err != nil {")
		rg.w.Writefmtln("\t\treturn nil, err")
		rg.w.Writefmtln("\t}")

		// Return the result.
		rg.w.Writefmtln("\treturn &rv, nil")
	}
	rg.w.Writefmtln("}")

	// If there are argument and/or return types, emit them.
	if rg.fun.argst != nil {
		rg.w.Writefmtln("")
		rg.generatePlainType(rg.fun.argst, false)
	}
	if rg.fun.retst != nil {
		rg.w.Writefmtln("")
		rg.generatePlainType(rg.fun.retst, false)
	}

	return nil
}

func (rg *goResourceGenerator) generatePlainType(typ *propertyType, inputProperties bool) {
	contract.Assert(typ.kind == kindObject)

	if typ.doc != "" {
		rg.g.emitDocComment(rg.w, typ.doc, "", "")
	}
	rg.w.Writefmtln("type %s struct {", typ.name)
	for _, prop := range typ.properties {
		if prop.doc != "" && prop.doc != elidedDocComment {
			rg.g.emitDocComment(rg.w, prop.doc, prop.docURL, "\t")
		} else if prop.rawdoc != "" {
			rg.g.emitRawDocComment(rg.w, prop.rawdoc, "\t")
		}

		var typ string
		if inputProperties {
			typ = goInputPropertyType(prop)
		} else {
			typ = goPlainPropertyType(prop)
		}

		rg.w.Writefmtln("\t%s %s `pulumi:\"%s\"`", upperFirst(prop.name), typ, prop.name)
	}
	rg.w.Writefmtln("}")
}

func (rg *goResourceGenerator) generateInputType(typ *propertyType) {
	// Generate the input interface.
	rg.w.Writefmtln("type %sInput interface {", typ.name)
	rg.w.Writefmtln("\tpulumi.Input")
	rg.w.Writefmtln("")
	rg.w.Writefmtln("\tTo%sOutput() %sOutput", typ.name, typ.name)
	rg.w.Writefmtln("\tTo%sOutputWithContext(ctx context.Context) %sOutput", typ.name, typ.name)
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")

	if typ.doc != "" {
		rg.g.emitDocComment(rg.w, typ.doc, "", "")
	}
	switch typ.kind {
	case kindSet, kindList:
		rg.w.Writefmtln("type %sArgs []%s", typ.name, goInputType(typ.element))
	case kindMap:
		rg.w.Writefmtln("type %sArgs map[string]%s", typ.name, goInputType(typ.element))
	default:
		rg.w.Writefmtln("type %sArgs struct {", typ.name)
		for _, prop := range typ.properties {
			if prop.doc != "" && prop.doc != elidedDocComment {
				rg.g.emitDocComment(rg.w, prop.doc, prop.docURL, "\t")
			} else if prop.rawdoc != "" {
				rg.g.emitRawDocComment(rg.w, prop.rawdoc, "\t")
			}

			rg.w.Writefmtln("\t%s %s `pulumi:\"%s\"`", upperFirst(prop.name), goInputPropertyType(prop), prop.name)
		}
		rg.w.Writefmtln("}")
	}
	rg.w.Writefmtln("")

	// Generate the implementation of the input interface.
	rg.w.Writefmtln("func (%sArgs) ElementType() reflect.Type {", typ.name)
	rg.w.Writefmtln("\treturn %sType", lowerFirst(typ.name))
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")
	rg.w.Writefmtln("func (a %sArgs) To%sOutput() %sOutput {", typ.name, typ.name, typ.name)
	rg.w.Writefmtln("\treturn pulumi.ToOutput(a).(%sOutput)", typ.name)
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")
	rg.w.Writefmtln("func (a %sArgs) To%sOutputWithContext(ctx context.Context) %sOutput {", typ.name, typ.name, typ.name)
	rg.w.Writefmtln("\treturn pulumi.ToOutputWithContext(ctx, a).(%sOutput)", typ.name)
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")
}

func (rg *goResourceGenerator) generateOutputType(typ *propertyType) {
	if typ.doc != "" {
		rg.g.emitDocComment(rg.w, typ.doc, "", "")
	}

	rg.w.Writefmtln("type %sOutput struct { *pulumi.OutputState }", typ.name)
	rg.w.Writefmtln("")

	// Note: this is the germ of an idea that may reshape the way we do inputs and outputs. Inputs
	// would be things that are deeply inputty (i.e. only primitives may be resolved values);
	// input interfaces for complex types would declare len/index methods and property accessors; all
	// types on those accessors would be output types. This adds some implementation complexity, but
	// may bring with it more clarity and flexibility. It also makes up for the lack of lifted property
	// accesses somewhat.

	switch typ.kind {
	case kindSet, kindList:
		rg.w.Writefmtln("func (o %sOutput) Index(i pulumi.IntInput) %s {", typ.name, goOutputType(typ.element))
		rg.w.Writefmtln("\treturn pulumi.All(o, i).Apply(func(vs []interface{}) %s {", goPlainType(typ.element))
		rg.w.Writefmtln("\t\treturn vs[0].(%s)[vs[1].(int)]", goPlainType(typ))
		rg.w.Writefmtln("\t}).(%s)", goOutputType(typ.element))
		rg.w.Writefmtln("}")
	case kindMap:
		// TODO(pdg): tuple-typed output?
		rg.w.Writefmtln("func (o %sOutput) MapIndex(k pulumi.StringInput) %s {", typ.name, goOutputType(typ.element))
		rg.w.Writefmtln("\treturn pulumi.All(o, k).Apply(func(vs []interface{}) %s {", goPlainType(typ.element))
		rg.w.Writefmtln("\t\treturn vs[0].(%s)[vs[1].(string)]", goPlainType(typ))
		rg.w.Writefmtln("\t}).(%s)", goOutputType(typ.element))
		rg.w.Writefmtln("}")
	default:
		for i, prop := range typ.properties {
			if i > 0 {
				rg.w.Writefmtln("")
			}

			if prop.doc != "" && prop.doc != elidedDocComment {
				rg.g.emitDocComment(rg.w, prop.doc, prop.docURL, "")
			} else if prop.rawdoc != "" {
				rg.g.emitRawDocComment(rg.w, prop.rawdoc, "")
			}
			rg.w.Writefmtln("func (o %sOutput) %s() %s {", typ.name, upperFirst(prop.name), goOutputPropertyType(prop))
			rg.w.Writefmtln("\treturn o.Apply(func(v %s) %s {", goPlainType(typ), goPlainType(prop.typ))
			if prop.optional() {
				rg.w.Writefmtln("\t\tif v.%[1]s == nil { return *new(%s) } else { return *v.%[1]s }",
					upperFirst(prop.name), goPlainType(prop.typ))
			} else {
				rg.w.Writefmtln("\t\treturn v.%s", upperFirst(prop.name))
			}
			rg.w.Writefmtln("\t}).(%s)", goOutputPropertyType(prop))
			rg.w.Writefmtln("}")
		}
	}
	rg.w.Writefmtln("")

	// Generate the implementation of the input interface.
	rg.w.Writefmtln("func (%sOutput) ElementType() reflect.Type {", typ.name)
	rg.w.Writefmtln("\treturn %sType", lowerFirst(typ.name))
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")
	rg.w.Writefmtln("func (o %[1]sOutput) To%[1]sOutput() %[1]sOutput {", typ.name)
	rg.w.Writefmtln("\treturn o")
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")
	rg.w.Writefmtln("func (o %[1]sOutput) To%[1]sOutputWithContext(ctx context.Context) %[1]sOutput {", typ.name)
	rg.w.Writefmtln("\treturn o")
	rg.w.Writefmtln("}")
	rg.w.Writefmtln("")
	rg.w.Writefmtln("func init() { pulumi.RegisterOutputType(%sOutput{}) }", typ.name)
	rg.w.Writefmtln("")
}

func (rg *goResourceGenerator) generateNestedTypes() {
	sort.Slice(rg.nested, func(i, j int) bool {
		a, b := rg.nested[i], rg.nested[j]
		return a.typ.name < b.typ.name
	})

	for _, nt := range rg.nested {
		contract.Assert(nt.declarer == rg.res || nt.declarer == rg.fun)
		contract.Assert(nt.kinds&goKindPlain != 0)

		if nt.typ.kind == kindObject {
			rg.generatePlainType(nt.typ, false)
		}

		if nt.kinds&(goKindInput|goKindOutput) != 0 {
			rg.w.Writefmtln("var %sType = reflect.TypeOf((*%s)(nil)).Elem()", lowerFirst(nt.typ.name),
				goPlainType(nt.typ))
			rg.w.Writefmtln("")
		}

		if nt.kinds&goKindInput != 0 {
			rg.generateInputType(nt.typ)
		}
		if nt.kinds&goKindOutput != 0 {
			rg.generateOutputType(nt.typ)
		}
	}
}

//nolint:lll
func (g *goGenerator) emitResourceType(mod *module, res *resourceType, nested *goNestedTypes) error {
	rg := newGoResourceGenerator(g, mod, res, nested)
	return rg.emit()
}

func (g *goGenerator) emitResourceFunc(mod *module, fun *resourceFunc, nested *goNestedTypes) error {
	rg := newGoDatasourceGenerator(g, mod, fun, nested)
	return rg.emit()
}

// emitOverlay copies an overlay from its source to the target, and returns the resulting file to be exported.
func (g *goGenerator) emitOverlay(mod *module, overlay *overlayFile) error {
	// Copy the file from the overlays directory to the destination.
	dir := g.moduleDir(mod)
	dst := filepath.Join(dir, overlay.name)
	if overlay.Copy() {
		return copyFile(overlay.src, dst)
	}
	_, err := os.Stat(dst)
	return err
}

// emitPackageMetadata generates all the non-code metadata required by a Pulumi package.
func (g *goGenerator) emitPackageMetadata(pack *pkg) error {
	// TODO: generate Gopkg.* files?
	return nil
}

// emitCustomImports traverses a custom schema map, deeply, to figure out the set of imported names and files that
// will be required to access those names.  WARNING: this routine doesn't (yet) attempt to eliminate naming collisions.
func (g *goGenerator) emitCustomImports(w *tools.GenWriter, mod *module, infos []*tfbridge.SchemaInfo) error {
	// TODO: implement this; until we do, we can't easily add overlays with intra- or inter-package references.
	return nil
}

// goPlainType returns the Go plain type name for a resource property.
func goPlainPropertyType(v *variable) string {
	typ := goPlainType(v.typ)
	if v.optional() {
		typ = "*" + typ
	}
	return typ
}

// goPlainType returns the Go plain type name for a given Terraform schema and bridge override info.
func goPlainType(typ *propertyType) string {
	// Prefer overrides over the underlying type.
	switch {
	case typ == nil:
		return "interface{}"
	case typ.asset != nil:
		if typ.asset.IsArchive() {
			return fmt.Sprintf("pulumi.%s", typ.asset.Type())
		}
		return "pulumi.AssetOrArchive"
	}

	// First figure out the raw type.
	switch typ.kind {
	case kindBool:
		return "bool"
	case kindInt:
		return "int"
	case kindFloat:
		return "float64"
	case kindString:
		return "string"
	case kindSet, kindList:
		return "[]" + goPlainType(typ.element)
	case kindMap:
		if typ.element == nil {
			return "map[string]string"
		}
		return "map[string]" + goPlainType(typ.element)
	case kindObject:
		return typ.name
	default:
		contract.Failf("Unrecognized type kind: %v", typ.kind)
		return ""
	}
}

// goElementType returns the Go element input or output type for a resource property type.
func goElementType(typ *propertyType) string {
	switch {
	case typ == nil:
		return "pulumi."
	case typ.asset != nil:
		if typ.asset.IsArchive() {
			return "pulumi." + typ.asset.Type()
		}
		return "pulumi.AssetOrArchive"
	}

	switch typ.kind {
	case kindBool:
		return "pulumi.Bool"
	case kindInt:
		return "pulumi.Int"
	case kindFloat:
		return "pulumi.Float64"
	case kindString:
		return "pulumi.String"
	case kindSet, kindList, kindMap:
		return "pulumi."
	case kindObject:
		return typ.name
	default:
		contract.Failf("Unrecognized schema type: %v", typ.kind)
		return ""
	}
}

// goInputPropertyType returns the Go input type name for a resource property.
func goInputPropertyType(v *variable) string {
	return goInputType(v.typ)
}

// goInputType returns the Go input type name for a given type.
func goInputType(typ *propertyType) string {
	t := goElementType(typ)

	switch typ.kind {
	case kindSet, kindList:
		return fmt.Sprintf("%sArrayInput", goElementType(typ.element))
	case kindMap:
		return fmt.Sprintf("%sMapInput", goElementType(typ.element))
	}

	return fmt.Sprintf("%sInput", t)
}

// goOutputPropertyType returns the Go output type name for a resource property.
func goOutputPropertyType(v *variable) string {
	return goOutputType(v.typ)
}

// goOutputType returns the Go output type name for a given Terraform schema and bridge override info.
func goOutputType(typ *propertyType) string {
	t := goElementType(typ)

	switch typ.kind {
	case kindSet, kindList:
		return fmt.Sprintf("%sArrayOutput", goElementType(typ.element))
	case kindMap:
		return fmt.Sprintf("%sMapOutput", goElementType(typ.element))
	}

	if t == "pulumi." {
		t = "pulumi.Any"
	}
	return fmt.Sprintf("%sOutput", t)
}

// goOutputMethod returns the "To*Output()" method for a given property.
func goOutputMethod(v *variable) string {
	t := goOutputPropertyType(v)
	if t == "pulumi.AnyOutput" {
		return ""
	}
	return fmt.Sprintf(".To%s()", strings.TrimPrefix(t, "pulumi."))
}

func goPrimitiveValue(value interface{}) (string, error) {
	v := reflect.ValueOf(value)
	if v.Kind() == reflect.Interface {
		v = v.Elem()
	}

	switch v.Kind() {
	case reflect.Bool:
		if v.Bool() {
			return "true", nil
		}
		return "false", nil
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32:
		return strconv.FormatInt(v.Int(), 10), nil
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32:
		return strconv.FormatUint(v.Uint(), 10), nil
	case reflect.Float32, reflect.Float64:
		return strconv.FormatFloat(v.Float(), 'f', -1, 64), nil
	case reflect.String:
		return fmt.Sprintf("%q", v.String()), nil
	default:
		return "", errors.Errorf("unsupported default value of type %T", value)
	}
}

func (g *goGenerator) goDefaultValue(v *variable) string {
	defaultValue := ""
	if v.info == nil || v.info.Default == nil {
		return defaultValue
	}
	defaults := v.info.Default

	if defaults.Value != nil {
		dv, err := goPrimitiveValue(defaults.Value)
		if err != nil {
			cmdutil.Diag().Warningf(diag.Message("", err.Error()))
			return defaultValue
		}
		defaultValue = dv
	}

	if len(defaults.EnvVars) > 0 {
		g.needsUtils = true

		parser, outDefault := "nil", "\"\""
		switch v.schema.Type {
		case schema.TypeBool:
			parser, outDefault = "parseEnvBool", "false"
		case schema.TypeInt:
			parser, outDefault = "parseEnvInt", "0"
		case schema.TypeFloat:
			parser, outDefault = "parseEnvFloat", "0.0"
		}

		if defaultValue == "" {
			if v.out {
				defaultValue = outDefault
			} else {
				defaultValue = "nil"
			}
		}

		defaultValue = fmt.Sprintf("getEnvOrDefault(%s, %s", defaultValue, parser)
		for _, e := range defaults.EnvVars {
			defaultValue += fmt.Sprintf(", %q", e)
		}
		defaultValue += ")"
	}

	if defaultValue == "" {
		return ""
	}
	return fmt.Sprintf("pulumi.Any(%s)", defaultValue)
}
