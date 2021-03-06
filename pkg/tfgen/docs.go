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

package tfgen

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"os"
	"path"
	"regexp"
	"sort"
	"strings"

	"github.com/hashicorp/go-multierror"
	"github.com/pulumi/pulumi-terraform-bridge/v2/pkg/tfbridge"
	"github.com/pulumi/pulumi/sdk/v2/go/common/diag"
	"github.com/pulumi/pulumi/sdk/v2/go/common/util/cmdutil"
	"github.com/pulumi/pulumi/sdk/v2/go/common/util/contract"
	"github.com/pulumi/tf2pulumi/convert"
	"github.com/spf13/afero"
)

// argumentDocs contains the documentation metadata for an argument of the resource.
type argumentDocs struct {
	// The description for this argument.
	description string

	// (Optional) The names and descriptions for each argument of this argument.
	arguments map[string]string

	// Whether this argument was derived from a nested object. Used to determine
	// whether to append descriptions that have continued to the following line
	isNested bool
}

// entityDocs represents the documentation for a resource or datasource as extracted from TF markdown.
type entityDocs struct {
	// Description is the description of the resource
	Description string

	// Arguments maps the name of each argument of the resource to its metadata.
	// Each argument has a description. Some arguments have their own arguments.
	//
	// For example, using a couple arguments from s3_bucket.html.markdown, we
	// expect to see a map like this, where "bucket" and "website" are top-level
	// arguments, and "index_document" is an argument of "website":
	//  - bucket
	//  	- description: "(Optional, Forces new resource) The name of the bucket.
	//  		If omitted, Terraform will assign a random, unique name."
	//  - website
	//  	- description: "(Optional) A website object (documented below)."
	//  	- arguments:
	//  		- index_document: "(Required, unless using `redirect_all_requests_to`)
	//				Amazon S3 returns this index document when requests are made to the
	//			 	root domain or any of the subfolders."
	//  - index_document
	//  	- description: "(Required, unless using `redirect_all_requests_to`)
	// 			Amazon S3 returns this index document when requests are made to the
	//			root domain or any of the subfolders."
	//  	- isNested: true
	// "index_document" is recorded like a top level argument since sometimes object names in
	// the TF markdown are inconsistent. For example, see `cors_rule` in s3_bucket.html.markdown.
	Arguments map[string]*argumentDocs

	// Attributes includes the names and descriptions for each attribute of the resource
	Attributes map[string]string

	// URL is the source documentation URL page
	URL string
}

// DocKind indicates what kind of entity's documentation is being requested.
type DocKind string

const (
	// ResourceDocs indicates documentation pertaining to resource entities.
	ResourceDocs DocKind = "r"
	// DataSourceDocs indicates documentation pertaining to data source entities.
	DataSourceDocs DocKind = "d"
)

func getRepoPath(org string, provider string) (string, error) {
	gomod, err := LoadGoMod()
	if err != nil {
		return "", err
	}

	calculatedImportPath := fmt.Sprintf("github.com/%s/terraform-provider-%s", org, provider)
	importPath, version, err := FindEffectiveModuleForImportPath(gomod, calculatedImportPath)
	if err != nil {
		return "", err
	}

	repo := GetModuleRoot(importPath, version)
	if fileInfo, err := os.Stat(repo); err != nil || !fileInfo.IsDir() {
		return "", err
	}

	return repo, nil
}

func getMarkdownDetails(g *generator, org string, provider string, resourcePrefix string, kind DocKind,
	rawname string, info tfbridge.ResourceOrDataSourceInfo) ([]byte, string, bool) {

	repoPath, err := getRepoPath(org, provider)
	if err != nil {
		return nil, "", false
	}

	possibleMarkdownNames := []string{
		// Most frequently, docs leave off the provider prefix
		withoutPackageName(resourcePrefix, rawname) + ".html.markdown",
		withoutPackageName(resourcePrefix, rawname) + ".markdown",
		withoutPackageName(resourcePrefix, rawname) + ".html.md",
		// But for some providers, the prefix is included in the name of the doc file
		rawname + ".html.markdown",
		rawname + ".markdown",
		rawname + ".html.md",
	}

	var docinfo *tfbridge.DocInfo
	if info != nil {
		docinfo = info.GetDocs()
	}

	if docinfo != nil && docinfo.Source != "" {
		possibleMarkdownNames = append(possibleMarkdownNames, docinfo.Source)
	}

	markdownBytes, markdownFileName, found := readMarkdown(repoPath, kind, possibleMarkdownNames)
	if !found {
		return nil, "", false
	}

	return markdownBytes, markdownFileName, true
}

// getDocsForProvider extracts documentation details for the given package from
// TF website documentation markdown content
func getDocsForProvider(g *generator, org string, provider string, resourcePrefix string, kind DocKind,
	rawname string, info tfbridge.ResourceOrDataSourceInfo) (entityDocs, error) {

	markdownBytes, markdownFileName, found := getMarkdownDetails(g, org, provider, resourcePrefix, kind, rawname, info)
	if !found {
		cmdutil.Diag().Warningf(
			diag.Message("", "Could not find docs for resource %v; consider overriding doc source location"), rawname)
		return entityDocs{}, nil
	}

	doc, err := parseTFMarkdown(g, info, kind, string(markdownBytes), markdownFileName, resourcePrefix, rawname)
	if err != nil {
		return entityDocs{}, err
	}

	var docinfo *tfbridge.DocInfo
	if info != nil {
		docinfo = info.GetDocs()
	}
	if docinfo != nil {
		// Merge Attributes from source into target
		if err := mergeDocs(g, info, org, provider, resourcePrefix, kind, doc,
			docinfo.IncludeAttributesFrom, true, true); err != nil {
			return doc, err
		}

		// Merge Arguments from source into Attributes of target
		if err := mergeDocs(g, info, org, provider, resourcePrefix, kind, doc,
			docinfo.IncludeAttributesFromArguments, true, false); err != nil {
			return doc, err
		}

		// Merge Arguments from source into target
		if err := mergeDocs(g, info, org, provider, provider, kind, doc,
			docinfo.IncludeArgumentsFrom, false, false); err != nil {
			return doc, err
		}
	}

	return doc, nil
}

// readMarkdown searches all possible locations for the markdown content
func readMarkdown(repo string, kind DocKind, possibleLocations []string) ([]byte, string, bool) {
	for _, name := range possibleLocations {
		location := path.Join(repo, "website", "docs", string(kind), name)
		markdownBytes, err := ioutil.ReadFile(location)
		if err == nil {
			return markdownBytes, name, true
		}
	}
	return nil, "", false
}

// mergeDocs adds the docs specified by extractDoc from sourceFrom into the targetDocs
func mergeDocs(g *generator, info tfbridge.ResourceOrDataSourceInfo, org string, provider string,
	resourcePrefix string,
	kind DocKind, docs entityDocs, sourceFrom string,
	useTargetAttributes bool, useSourceAttributes bool) error {

	if sourceFrom != "" {
		sourceDocs, err := getDocsForProvider(g, org, provider, resourcePrefix, kind, sourceFrom, nil)
		if err != nil {
			return err
		}

		if useTargetAttributes && useSourceAttributes {
			for k, v := range sourceDocs.Attributes {
				docs.Attributes[k] = v
			}
		} else if useTargetAttributes && !useSourceAttributes {
			for k, v := range sourceDocs.Arguments {
				docs.Attributes[k] = v.description
				for kk, vv := range v.arguments {
					docs.Attributes[kk] = vv
				}
			}
		} else if !useTargetAttributes && !useSourceAttributes {
			for k, v := range sourceDocs.Arguments { // string -> argument
				arguments := sourceDocs.Arguments[k].arguments
				docArguments := make(map[string]string)
				for kk, vv := range arguments {
					docArguments[kk] = vv
				}
				docs.Arguments[k] = &argumentDocs{
					description: v.description,
					arguments:   docArguments,
				}
			}
		}
	}
	return nil
}

// nolint:lll
var (
	// For example:
	// [1]: https://docs.aws.amazon.com/lambda/latest/dg/welcome.html
	linkFooterRegexp = regexp.MustCompile(`(?m)^(\[\d+\]):\s(.*)`)

	argumentBulletRegexp = regexp.MustCompile(
		"^\\s*\\*\\s+`([a-zA-z0-9_]*)`\\s*(\\([a-zA-Z]*\\)\\s*)?[–-]?\\s+(\\([^\\)]*\\)\\s*)?(.*)")

	nestedObjectRegexps = []*regexp.Regexp{
		// For example:
		// s3_bucket.html.markdown: "The `website` object supports the following:"
		// ami.html.markdown: "When `virtualization_type` is "hvm" the following additional arguments apply:"
		regexp.MustCompile("`([a-z_]+)`.*following"),

		// For example:
		// athena_workgroup.html.markdown: "#### result_configuration Argument Reference"
		regexp.MustCompile("(?i)## ([a-z_]+).* argument reference"),
	}

	attributeBulletRegexp = regexp.MustCompile("\\*\\s+`([a-zA-z0-9_]*)`\\s+[–-]?\\s+(.*)")

	docsBaseURL    = "https://github.com/%s/terraform-provider-%s/blob/master/website/docs"
	docsDetailsURL = docsBaseURL + "/%s/%s"

	standardDocReadme = `> This provider is a derived work of the [Terraform Provider](https://github.com/%[3]s/terraform-provider-%[2]s)
> distributed under [%[4]s](%[5]s). If you encounter a bug or missing feature,
> first check the [` + "`pulumi/pulumi-%[1]s`" + ` repo](https://github.com/pulumi/pulumi-%[1]s/issues); however, if that doesn't turn up anything,
> please consult the source [` + "`%[3]s/terraform-provider-%[2]s`" + ` repo](https://github.com/%[3]s/terraform-provider-%[2]s/issues).`
	attributionFormatString = "This Pulumi package is based on the [`%[1]s` Terraform Provider](https://github.com/%[2]s/terraform-provider-%[1]s)."
)

// groupLines groups a collection of strings, a, by a given separator, sep.
func groupLines(lines []string, sep string) [][]string {
	var buffer []string
	var sections [][]string
	for _, line := range lines {
		if strings.Index(line, sep) == 0 {
			sections = append(sections, buffer)
			buffer = []string{}
		}
		buffer = append(buffer, line)
	}
	if len(buffer) > 0 {
		sections = append(sections, buffer)
	}
	return sections
}

// splitGroupLines splits and groups a string, s, by a given separator, sep.
func splitGroupLines(s, sep string) [][]string {
	return groupLines(strings.Split(s, "\n"), sep)
}

// getDocsBaseURL gets the base URL for a given provider's documentation source.
func getDocsBaseURL(org, p string) string {
	return fmt.Sprintf(docsBaseURL, org, p)
}

// getDocsDetailsURL gets the detailed resource or data source documentation source.
func getDocsDetailsURL(org, p, kind, markdownFileName string) string {
	return fmt.Sprintf(docsDetailsURL, org, p, kind, markdownFileName)
}

// getDocsIndexURL gets the given provider's documentation index page's source URL.
func getDocsIndexURL(org, p string) string {
	return getDocsBaseURL(org, p) + "/index.html.markdown"
}

// parseTFMarkdown takes a TF website markdown doc and extracts a structured representation for use in
// generating doc comments
func parseTFMarkdown(g *generator, info tfbridge.ResourceOrDataSourceInfo, kind DocKind,
	markdown, markdownFileName, resourcePrefix, rawname string) (entityDocs, error) {

	p := &tfMarkdownParser{
		g:                g,
		info:             info,
		kind:             kind,
		markdown:         markdown,
		markdownFileName: markdownFileName,
		resourcePrefix:   resourcePrefix,
		rawname:          rawname,
	}
	return p.parse()
}

type tfMarkdownParser struct {
	g                *generator
	info             tfbridge.ResourceOrDataSourceInfo
	kind             DocKind
	markdown         string
	markdownFileName string
	resourcePrefix   string
	rawname          string

	ret entityDocs
}

const (
	sectionOther               = 0
	sectionExampleUsage        = 1
	sectionArgsReference       = 2
	sectionAttributesReference = 3
	sectionFrontMatter         = 4
)

func (p *tfMarkdownParser) parse() (entityDocs, error) {
	p.ret = entityDocs{
		Arguments:  make(map[string]*argumentDocs),
		Attributes: make(map[string]string),
		URL:        getDocsDetailsURL(p.g.info.GetGitHubOrg(), p.resourcePrefix, string(p.kind), p.markdownFileName),
	}

	// Replace any Windows-style newlines.
	markdown := strings.Replace(p.markdown, "\r\n", "\n", -1)

	// Split the sections by H2 topics in the Markdown file.
	sections := splitGroupLines(markdown, "## ")

	// Reparent examples that are peers of the "Example Usage" section (if any) and fixup some example titles.
	sections = p.reformatExamples(sections)

	for _, section := range sections {
		if err := p.parseSection(section); err != nil {
			return entityDocs{}, err
		}
	}

	// Get links.
	footerLinks := getFooterLinks(markdown)

	doc, elided := cleanupDoc(p.g, p.info, p.ret, footerLinks)
	if elided {
		cmdutil.Diag().Warningf(diag.Message("",
			"Resource %v contains an <elided> doc reference that needs updated"), p.rawname)
	}

	return doc, nil
}

// fixExampleTitles transforms H4 sections that contain code snippets into H3 sections.
func (p *tfMarkdownParser) fixExampleTitles(lines []string) {
	inSection, sectionIndex := false, 0
	for i, line := range lines {
		if inSection && strings.HasPrefix(line, "```") {
			lines[sectionIndex] = strings.Replace(lines[sectionIndex], "#### ", "### ", 1)
			inSection = false
		} else if strings.HasPrefix(line, "#### ") {
			inSection, sectionIndex = true, i
		}
	}
}

var exampleHeaderRegexp = regexp.MustCompile(`(?i)^(## Example Usage\s*)(?:(?:(?:for|of|[\pP]+)\s*)?(.*?)\s*)?$`)

// reformatExamples reparents examples that are peers of the "Example Usage" section (if any) and fixup some example
// titles.
func (p *tfMarkdownParser) reformatExamples(sections [][]string) [][]string {
	canonicalExampleUsageSectionIndex := -1
	var exampleUsageSection []string
	var exampleSectionIndices []int
	for i, s := range sections {
		matches := exampleHeaderRegexp.FindStringSubmatch(s[0])
		if len(matches) == 0 {
			continue
		}

		if len(matches[1]) == len(s[0]) {
			// This is the canonical example usage section. Prepend its contents to any other content we've collected.
			// If there are multiple canonical example usage sections, treat the first such section as the canonical
			// example usage section and append other sections under an H3.
			if canonicalExampleUsageSectionIndex == -1 {
				canonicalExampleUsageSectionIndex = i

				// Copy the section over. Note that we intentionally avoid copying the first line and any whitespace
				// that follows it, as we will overwrite that content with the canonical header later.
				for s = s[1:]; len(s) > 0 && isBlank(s[0]); s = s[1:] {
				}

				sectionCopy := make([]string, len(s)+2)
				copy(sectionCopy[2:], s)

				if len(exampleUsageSection) != 0 {
					exampleUsageSection = append(sectionCopy, exampleUsageSection...)
				} else {
					exampleUsageSection = sectionCopy
				}
			} else {
				exampleUsageSection = append(exampleUsageSection, "", "### Additional Examples")
				exampleUsageSection = append(exampleUsageSection, s[1:]...)
			}
		} else {
			// This is a qualified example usage section. Retitle it using an H3 and its qualifier, and append it to
			// the output.
			exampleUsageSection = append(exampleUsageSection, "", "### "+strings.Title(matches[2]))
			exampleUsageSection = append(exampleUsageSection, s[1:]...)
		}

		exampleSectionIndices = append(exampleSectionIndices, i)
	}

	if len(exampleSectionIndices) == 0 {
		return sections
	}

	// If we did not find a canonical example usage section, prepend a blank line to the output. This line will be
	// replaced by the canonical example usage H2.
	if canonicalExampleUsageSectionIndex == -1 {
		canonicalExampleUsageSectionIndex = exampleSectionIndices[0]
		exampleUsageSection = append([]string{""}, exampleUsageSection...)
	}

	// Ensure that the output begins with the canonical example usage header.
	exampleUsageSection[0] = "## Example Usage"

	// Fixup example titles and replace the contents of the canonical example usage section with the output.
	p.fixExampleTitles(exampleUsageSection)
	sections[canonicalExampleUsageSectionIndex] = exampleUsageSection

	// If there is only one example section, we're done. Otherwise, we need to remove all non-canonical example usage
	// sections.
	if len(exampleSectionIndices) == 1 {
		return sections
	}

	result := sections[:0]
	for i, s := range sections {
		if len(exampleSectionIndices) > 0 && i == exampleSectionIndices[0] {
			exampleSectionIndices = exampleSectionIndices[1:]
			if i != canonicalExampleUsageSectionIndex {
				continue
			}
		}
		result = append(result, s)
	}
	return result
}

func (p *tfMarkdownParser) parseSection(section []string) error {
	// Extract the header name, since this will drive how we process the content.
	if len(section) == 0 {
		cmdutil.Diag().Warningf(diag.Message("",
			"Unparseable H2 doc section for %v; consider overriding doc source location"), p.rawname)
		return nil
	}

	// Skip certain headers that we don't support.
	header := section[0]
	if strings.Index(header, "## ") == 0 {
		header = header[3:]
	}

	sectionKind := sectionOther
	switch header {
	case "Import", "Imports", "Timeout", "Timeouts", "User Project Override", "User Project Overrides":
		ignoredDocSections++
		ignoredDocHeaders[header]++
		return nil
	case "Example Usage":
		sectionKind = sectionExampleUsage
	case "Arguments Reference", "Argument Reference", "Nested Blocks", "Nested blocks":
		sectionKind = sectionArgsReference
	case "Attributes Reference", "Attribute Reference":
		sectionKind = sectionAttributesReference
	case "---":
		sectionKind = sectionFrontMatter
	}

	if sectionKind == sectionExampleUsage {
		// Add shortcode around each examples block.
		p.ret.Description += "{{% examples %}}\n"
	}

	// Now split the sections by H3 topics. This is done because we'll ignore sub-sections with code
	// snippets that are unparseable (we don't want to ignore entire H2 sections).
	var wroteHeader bool
	for _, subsection := range groupLines(section[1:], "### ") {
		if len(subsection) == 0 {
			cmdutil.Diag().Warningf(diag.Message("",
				"Unparseable H3 doc section for %v; consider overriding doc source location"), p.rawname)
			continue
		}

		// Skip empty sections (they just add unnecessary padding and headers).
		allEmpty := true
		for _, sub := range subsection {
			if !isBlank(sub) {
				allEmpty = false
				break
			}
		}
		if allEmpty {
			continue
		}

		// Convert or remove code snippets, if there are any. If this yields a fatal error, we
		// bail out, but most errors are ignorable and just lead to us skipping one section.
		subsection, hasExamples, skippedExamples := p.parseExamples(subsection)
		if hasExamples && sectionKind != sectionExampleUsage {
			cmdutil.Diag().Warningf(diag.Message("",
				"Unexpected code snippets in section %v for resource %v"), header, p.rawname)
		}

		// Now process the content based on the H2 topic. These are mostly standard across TF's docs.
		switch sectionKind {
		case sectionArgsReference:
			p.parseArgReferenceSection(subsection)
		case sectionAttributesReference:
			p.parseAttributesReferenceSection(subsection)
		case sectionFrontMatter:
			p.parseFrontMatter(subsection)
		default:
			// These sections are non-essential. If we skipped any examples, we will omit the entire section.
			if skippedExamples {
				continue
			}

			// Determine if this is a nested argument section.
			_, isArgument := p.ret.Arguments[header]
			if isArgument || strings.HasSuffix(header, "Configuration Block") {
				p.parseArgReferenceSection(subsection)
				continue
			}

			// For all other sections, append them to the description section.
			if !wroteHeader {
				p.ret.Description += fmt.Sprintf("## %s\n", header)
				wroteHeader = true
				if !isBlank(subsection[0]) {
					p.ret.Description += "\n"
				}
			}
			description := strings.Join(subsection, "\n") + "\n"
			if sectionKind == sectionExampleUsage {
				// Wrap each example in shortcode.
				description = "{{% example %}}\n" + description + "{{% /example %}}\n"
			}
			p.ret.Description += description
		}
	}

	// Add the closing shortcode around the examples block.
	if sectionKind == sectionExampleUsage {
		p.ret.Description += "{{% /examples %}}\n"
	}

	return nil
}

func getFooterLinks(markdown string) map[string]string {
	links := make(map[string]string)
	lines := strings.Split(markdown, "\n")
	for _, line := range lines {
		matches := linkFooterRegexp.FindStringSubmatch(line)
		if len(matches) == 3 {
			links[matches[1]] = matches[2]
		}
	}
	return links
}

func (p *tfMarkdownParser) parseArgReferenceSection(subsection []string) {
	var lastMatch, nested string
	for _, line := range subsection {
		matches := argumentBulletRegexp.FindStringSubmatch(line)
		if len(matches) >= 4 {
			// found a property bullet, extract the name and description
			if nested != "" {
				// We found this line within a nested field. We should record it as such.
				if p.ret.Arguments[nested] == nil {
					p.ret.Arguments[nested] = &argumentDocs{
						arguments: make(map[string]string),
					}
				} else if p.ret.Arguments[nested].arguments == nil {
					p.ret.Arguments[nested].arguments = make(map[string]string)
				}
				p.ret.Arguments[nested].arguments[matches[1]] = matches[4]

				// Also record this as a top-level argument just in case, since sometimes the recorded nested
				// argument doesn't match the resource's argument.
				// For example, see `cors_rule` in s3_bucket.html.markdown.
				if p.ret.Arguments[matches[1]] == nil {
					p.ret.Arguments[matches[1]] = &argumentDocs{
						description: matches[4],
						isNested:    true, // Mark that this argument comes from a nested field.
					}
				}
			} else {
				if !strings.HasSuffix(line, "supports the following:") {
					p.ret.Arguments[matches[1]] = &argumentDocs{description: matches[4]}
				}
			}
			lastMatch = matches[1]
		} else if !isBlank(line) && lastMatch != "" {
			// this is a continuation of the previous bullet
			if nested != "" {
				p.ret.Arguments[nested].arguments[lastMatch] += "\n" + strings.TrimSpace(line)

				// Also update the top-level argument if we took it from a nested field.
				if p.ret.Arguments[lastMatch].isNested {
					p.ret.Arguments[lastMatch].description += "\n" + strings.TrimSpace(line)
				}
			} else {
				p.ret.Arguments[lastMatch].description += "\n" + strings.TrimSpace(line)
			}
		} else {
			// This line might declare the beginning of a nested object.
			// If we do not find a "nested", then this is an empty line or there were no bullets yet.
			for _, match := range nestedObjectRegexps {
				matches := match.FindStringSubmatch(line)
				if len(matches) >= 2 {
					nested = strings.ToLower(matches[1])
					break
				}
			}

			// Clear the lastMatch.
			lastMatch = ""
		}
	}
}

func (p *tfMarkdownParser) parseAttributesReferenceSection(subsection []string) {
	var lastMatch string
	for _, line := range subsection {
		matches := attributeBulletRegexp.FindStringSubmatch(line)
		if len(matches) >= 2 {
			// found a property bullet, extract the name and description
			p.ret.Attributes[matches[1]] = matches[2]
			lastMatch = matches[1]
		} else if !isBlank(line) && lastMatch != "" {
			// this is a continuation of the previous bullet
			p.ret.Attributes[lastMatch] += "\n" + strings.TrimSpace(line)
		} else {
			// This is an empty line or there were no bullets yet - clear the lastMatch
			lastMatch = ""
		}
	}
}

func (p *tfMarkdownParser) parseFrontMatter(subsection []string) {
	// The header of the MarkDown will have two "---"s paired up to delineate the header. Skip this.
	var foundEndHeader bool
	for len(subsection) > 0 {
		curr := subsection[0]
		subsection = subsection[1:]
		if curr == "---" {
			foundEndHeader = true
			break
		}
	}
	if !foundEndHeader {
		cmdutil.Diag().Warningf(
			diag.Message("", "Expected to pair --- begin/end for resource %v's Markdown header"), p.rawname)
	}

	// Now extract the description section. We assume here that the first H1 (line starting with #) is the name
	// of the resource, because we aren't detecting code fencing. Comments in HCL are prefixed with # (the
	// same as H1 in Markdown, so we treat further H1's in this section as part of the description. If there
	// are no matching H1s, we emit a warning for the resource as it is likely a problem with the documentation.
	lastBlank := true
	var foundH1Resource bool
	for _, line := range subsection {
		if strings.Index(line, "# ") == 0 {
			foundH1Resource = true
			lastBlank = true
		} else if !isBlank(line) || !lastBlank {
			p.ret.Description += line + "\n"
			lastBlank = false
		} else if isBlank(line) {
			lastBlank = true
		}
	}
	if !foundH1Resource {
		cmdutil.Diag().Warningf(diag.Message("", "Expected an H1 in markdown for resource %v"), p.rawname)
	}
}

var (
	ignoredDocSections int
	ignoredDocHeaders  = make(map[string]int)
	hclBlocksSucceeded int
	hclBlocksFailed    int
	hclFailures        = make(map[string]bool)
)

// isBlank returns true if the line is all whitespace.
func isBlank(line string) bool {
	return strings.TrimSpace(line) == ""
}

// trimTrailingBlanks removes any blank lines from the end of an array.
func trimTrailingBlanks(lines []string) []string {
	for len(lines) > 0 && isBlank(lines[len(lines)-1]) {
		lines = lines[:len(lines)-1]
	}
	return lines
}

// printDocStats outputs warnings and, if flags are set, stdout diagnostics pertaining to documentation conversion.
func printDocStats(printIgnoreDetails, printHCLFailureDetails bool) {
	// These summaries are printed on each run, to help us keep an eye on success/failure rates.
	if ignoredDocSections > 0 {
		cmdutil.Diag().Warningf(
			diag.Message("", "%d documentation sections ignored"), ignoredDocSections)
	}
	if hclBlocksFailed > 0 {
		cmdutil.Diag().Warningf(
			diag.Message("", "%d/%d documentation code blocks failed to convert"),
			hclBlocksFailed, hclBlocksFailed+hclBlocksSucceeded)
	}

	// These more detailed outputs are suppressed by default, but can be enabled to track down failures.
	if printIgnoreDetails {
		fmt.Printf("---IGNORES---\n")
		var ignores []string
		for ignore := range ignoredDocHeaders {
			ignores = append(ignores, ignore)
		}
		sort.Strings(ignores)
		for _, ignore := range ignores {
			fmt.Printf("[%d] %s\n", ignoredDocHeaders[ignore], ignore)
		}
	}
	if printHCLFailureDetails {
		fmt.Printf("---HCL FAILURES---\n")
		var failures []string
		for failure := range hclFailures {
			failures = append(failures, failure)
		}
		sort.Strings(failures)
		for i, failure := range failures {
			fmt.Printf("%d: %s\n", i, failure)
		}
	}
}

// parseExamples processes any code snippets in a subsection, either converting them to Pulumi code snippets or
// removing them. If an error converting a code example occurs or any examples are present and the caller has requested
// they be removed, the bool (skip) will be true.
func (p *tfMarkdownParser) parseExamples(lines []string) ([]string, bool, bool) {
	// Each `Example ...` section contains one or more examples written in HCL, optionally separated by
	// comments about the examples. We will attempt to convert them using our `tf2pulumi` tool, and append
	// them to the description. If we can't, we'll simply log a warning and keep moving along.
	var result []string
	var hasExamples bool
	var skippedExamples bool
	var inCodeBlock bool
	var inOICSButton bool
	var codeBlockStart int
	for i, line := range lines {
		switch {
		case inCodeBlock:
			if strings.Index(line, "```") != 0 {
				continue
			}

			if p.g.language.shouldConvertExamples() {
				hcl := strings.Join(lines[codeBlockStart+1:i], "\n")

				// We've got some code -- assume it's HCL and try to convert it.
				lines, stderr, err := p.convertHCL(hcl)
				if err != nil {
					skippedExamples = true
					hclFailures[stderr] = true
					hclBlocksFailed++
				} else {
					result = append(result, lines...)
					hclBlocksSucceeded++
				}

				hasExamples = true
			} else {
				skippedExamples = true
			}

			inCodeBlock = false
		case inOICSButton:
			if strings.Index(lines[i], "</div>") == 0 {
				inOICSButton = false
			}
		default:
			if strings.Index(line, "```") == 0 {
				inCodeBlock, codeBlockStart = true, i
			} else if strings.Index(line, "<div") == 0 && strings.Contains(line, "oics-button") {
				inOICSButton = true
			} else {
				result = append(result, line)
			}
		}
	}
	if inCodeBlock {
		skippedExamples = true
	}

	return result, hasExamples, skippedExamples
}

// convertHCL converts an in-memory, simple HCL program to Pulumi, and returns it as a string. In the event
// of failure, the error returned will be non-nil, and the second string contains the stderr stream of details.
func (p *tfMarkdownParser) convertHCL(hcl string) ([]string, string, error) {
	// Fixup the HCL as necessary.
	if fixed, ok := fixHcl(hcl); ok {
		hcl = fixed
	}

	input := afero.NewMemMapFs()
	f, err := input.Create("/main.tf")
	contract.AssertNoError(err)
	_, err = f.Write([]byte(hcl))
	contract.AssertNoError(err)
	contract.IgnoreClose(f)

	var result []string
	var stderr bytes.Buffer
	convertHCL := func(languageName string) (err error) {
		defer func() {
			v := recover()
			contract.Ignore(v)
		}()

		files, diags, err := convert.Convert(convert.Options{
			Root:                  input,
			TargetLanguage:        languageName,
			AllowMissingVariables: true,
			FilterResourceNames:   true,
			PackageCache:          p.g.packageCache,
			PluginHost:            p.g.pluginHost,
			ProviderInfoSource:    p.g.infoSource,
		})
		if err != nil {
			return fmt.Errorf("failied to convert HCL to %v: %w", languageName, err)
		}
		if diags.All.HasErrors() {
			if stderr.Len() != 0 {
				_, err := fmt.Fprintf(&stderr, "\n")
				contract.IgnoreError(err)
			}
			_, err := fmt.Fprintf(&stderr, "# %s\n", languageName)
			contract.IgnoreError(err)

			_, err = fmt.Fprintf(&stderr, "%s\n\n", hcl)
			contract.IgnoreError(err)

			err = diags.NewDiagnosticWriter(&stderr, 0, false).WriteDiagnostics(diags.All)
			contract.IgnoreError(err)

			return fmt.Errorf("failied to convert HCL to %v", languageName)
		}

		contract.Assert(len(files) == 1)

		// Add a fenced code-block with the resulting code snippet.
		for _, output := range files {
			result = append(result, "```"+languageName)
			codeLines := strings.Split(string(output), "\n")
			codeLines = trimTrailingBlanks(codeLines)
			result = append(result, codeLines...)
			result = append(result, "```")
		}

		return nil
	}

	switch p.g.language {
	case nodeJS:
		err = convertHCL("typescript")
	case python:
		err = convertHCL("python")
	case csharp:
		err = convertHCL("csharp")
	case pulumiSchema:
		langs := []string{"typescript", "python", "csharp"}
		for _, lang := range langs {
			if langErr := convertHCL(lang); langErr != nil {
				err = multierror.Append(err, langErr)
			}
		}
	}
	if err != nil {
		return nil, stderr.String(), err
	}
	return result, "", nil
}

func cleanupDoc(g *generator, info tfbridge.ResourceOrDataSourceInfo, doc entityDocs,
	footerLinks map[string]string) (entityDocs, bool) {
	elidedDoc := false
	newargs := make(map[string]*argumentDocs, len(doc.Arguments))
	for k, v := range doc.Arguments {
		cleanedText, elided := cleanupText(g, info, v.description, footerLinks)
		if elided {
			elidedDoc = true
		}

		newargs[k] = &argumentDocs{
			description: cleanedText,
			arguments:   make(map[string]string, len(v.arguments)),
		}

		// Clean nested arguments (if any)
		for kk, vv := range v.arguments {
			cleanedText, elided := cleanupText(g, info, vv, footerLinks)
			if elided {
				elidedDoc = true
			}
			newargs[k].arguments[kk] = cleanedText
		}
	}
	newattrs := make(map[string]string, len(doc.Attributes))
	for k, v := range doc.Attributes {
		cleanupText, elided := cleanupText(g, info, v, footerLinks)
		if elided {
			elidedDoc = true
		}
		newattrs[k] = cleanupText
	}
	cleanupText, elided := cleanupText(g, info, doc.Description, footerLinks)
	if elided {
		elidedDoc = true
	}
	return entityDocs{
		Description: cleanupText,
		Arguments:   newargs,
		Attributes:  newattrs,
		URL:         doc.URL,
	}, elidedDoc

}

var markdownLink = regexp.MustCompile(`\[([^\]]*)\]\(([^\)]*)\)`)
var codeLikeSingleWord = regexp.MustCompile("([\\s`\"\\[])(([0-9a-z]+_)+[0-9a-z]+)([\\s`\"\\]])")

// Regex for catching reference links, e.g. [1]: /docs/providers/aws/d/networ_interface.html
var markdownPageReferenceLink = regexp.MustCompile(`\[[1-9]+\]: /docs/providers(?:/[a-z1-9_]+)+\.[a-z]+`)

const elidedDocComment = "<elided>"

// cleanupText processes markdown strings from TF docs and cleans them for inclusion in Pulumi docs
func cleanupText(g *generator, info tfbridge.ResourceOrDataSourceInfo, text string,
	footerLinks map[string]string) (string, bool) {

	// Remove incorrect documentation that should have been cleaned up in our forks.
	// TODO: fail the build in the face of such text, once we have a processes in place.
	if strings.Contains(text, "Terraform") || strings.Contains(text, "terraform") {
		return "", true
	}

	// Replace occurrences of "->" or "~>" with just ">", to get a proper MarkDown note.
	text = strings.Replace(text, "-> ", "> ", -1)
	text = strings.Replace(text, "~> ", "> ", -1)

	// Trim Prefixes we see when the description is spread across multiple lines.
	text = strings.TrimPrefix(text, "-\n(Required)\n")
	text = strings.TrimPrefix(text, "-\n(Optional)\n")

	// Find markdown Terraform docs site reference links.
	text = markdownPageReferenceLink.ReplaceAllStringFunc(text, func(referenceLink string) string {
		parts := strings.Split(referenceLink, " ")
		// Add Terraform domain to avoid broken links.
		return fmt.Sprintf("%s https://www.terraform.io%s", parts[0], parts[1])
	})

	// Find links from the footer links.
	text = replaceFooterLinks(text, footerLinks)

	// Find URLs and re-write local links
	text = markdownLink.ReplaceAllStringFunc(text, func(link string) string {
		parts := markdownLink.FindStringSubmatch(link)
		url := parts[2]
		if strings.HasPrefix(url, "http") {
			// Absolute URL, return as-is
			return link
		} else if strings.HasPrefix(url, "/") {
			// Relative URL to the root of the Terraform docs site, rewrite to absolute
			return fmt.Sprintf("[%s](https://www.terraform.io%s)", parts[1], url)
		} else if strings.HasPrefix(url, "#") {
			// Anchor in current page,  can't be resolved currently so remove the link.
			// Note: This throws away potentially valuable information in the name of not having broken links.
			return parts[1]
		}
		// Relative URL to the current page, can't be resolved currently so remove the link.
		// Note: This throws away potentially valuable information in the name of not having broken links.
		return parts[1]
	})

	// Fixup resource and property name references
	text = codeLikeSingleWord.ReplaceAllStringFunc(text, func(match string) string {
		parts := codeLikeSingleWord.FindStringSubmatch(match)
		name := parts[2]
		if resInfo, hasResourceInfo := g.info.Resources[name]; hasResourceInfo {
			// This is a resource name
			resname, mod := resourceName(g.info.GetResourcePrefix(), name, resInfo, false)
			modname := extractModuleName(mod)
			switch g.language {
			case golang, python:
				// Use `ec2.Instance` format
				return parts[1] + modname + "." + resname + parts[4]
			default:
				// Use `aws.ec2.Instance` format
				return parts[1] + g.pkg + "." + modname + "." + resname + parts[4]
			}
		} else if dataInfo, hasDatasourceInfo := g.info.DataSources[name]; hasDatasourceInfo {
			// This is a data source name
			getname, mod := dataSourceName(g.info.GetResourcePrefix(), name, dataInfo)
			modname := extractModuleName(mod)
			switch g.language {
			case golang, python:
				// Use `ec2.getAmi` format
				return parts[1] + modname + "." + getname + parts[4]
			default:
				// Use `aws.ec2.getAmi` format
				return parts[1] + g.pkg + "." + modname + "." + getname + parts[4]
			}
		}
		// Else just treat as a property name
		switch g.language {
		case nodeJS, golang:
			// Use `camelCase` format
			pname := propertyName(name, nil, nil)
			return parts[1] + pname + parts[4]
		default:
			return match
		}
	})

	// Finally, trim any trailing blank lines and return the result.
	lines := strings.Split(text, "\n")
	lines = trimTrailingBlanks(lines)
	return strings.Join(lines, "\n"), false
}

// For example:
// [What is AWS Lambda?][1]
var linkWithFooterRefRegexp = regexp.MustCompile(`(\[[a-zA-Z?.! ]+\])(\[[0-9]+\])`)

// replaceFooterLinks replaces all links with a reference to a footer link.
func replaceFooterLinks(text string, footerLinks map[string]string) string {
	if len(footerLinks) == 0 {
		return text
	}
	return linkWithFooterRefRegexp.ReplaceAllStringFunc(text, func(link string) string {
		parts := linkWithFooterRefRegexp.FindStringSubmatch(link)
		linkText := parts[1]
		linkRef := parts[2]

		// If we have a footer link for the reference, we need to replace it.
		if footerLink, ok := footerLinks[linkRef]; ok {
			return linkText + "(" + footerLink + ")"
		}
		return link
	})
}
