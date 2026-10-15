# XHTML contract audit (investigation only)

This branch is an isolated reproducer, not a proposed production correction. Its purpose is to test whether the library's ".xhtml = well-formed XML" description follows from the actual renderer and the `WellFormedHtml` Lean predicate. The examples do not use `Node.unsafeRaw`.

From the repository root, under Lean 4.34.1:

```bash
lake build
lake env lean repros/XhtmlContractAudit.lean > /tmp/xhtml-contract.tsv
python3 repros/check_xml_contract.py < /tmp/xhtml-contract.tsv
lake test
```

Preserve command exit codes and complete output. The Python checker intentionally expects valid XML for `control-valid`, and invalid XML for the seven identified counterexample classes. The `duplicate-formal-witness` case also constructs a Lean proof of `WellFormedHtml .xhtml` for a node whose serialized output contains a duplicate attribute. That is a gap in the predicate's coverage, not a contradiction in Lean.

The `unbound-namespace-prefix` result relies on namespace-aware XML parsing. XML 1.0 itself permits colons in names, while XML Namespaces imposes extra conditions. The `arbitrary-tag-name` case uses an API exception already noted in the upstream README; it is a scope control, not a claim about typed tag helpers.

Reproducing failures does not settle the correction. Deduplicating attributes changes compositional rendering behavior and affects the existing `attrsRender_append` theorem in `test/HtmlTests/Escape.lean`. Any proposed patch must choose explicit precedence, account for collisions after `sanitizeAttrName`, and respect existing behavior in both HTML5 and XHTML dialects. Character handling is a separate correction. Do not commit a production change without resolving those contracts.
