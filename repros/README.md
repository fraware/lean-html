# Attribute-name uniqueness experiment

**Not a PR. Not compiled in this environment.** Based on upstream `56d842fe8b1f05028b0b5083fc25270235f19857`.

This branch implements first-occurrence precedence at `Attrs.render`. Duplicate detection uses **sanitized names**, so `"a b"` and `"a_b"` collide. It covers typed/raw tag attributes, direct `Node.element` calls, and HTML5 flags. The typed attribute list is emitted first, so it takes precedence over later `rawAttrs`. Only the public renderer deduplicates; the raw serializer is private.

This **changes rendered output** when duplicate attributes are supplied in either dialect, although the public function signatures remain unchanged. The original unconditional `attrsRender_append` law is false under this semantic rule. Do not restore it without a disjointness hypothesis. A first-wins theorem and targeted guards replace it on the experimental branch.

Use an isolated Linux/WSL2 worktree at the exact commit:

```bash
set -euo pipefail
lake build
lake env lean repros/XhtmlContractAudit.lean > /tmp/xhtml-unique-attrs-audit.tsv
python3 repros/check_xml_contract.py < /tmp/xhtml-unique-attrs-audit.tsv
lake test
git diff --check 56d842fe8b1f05028b0b5083fc25270235f19857 HEAD
```

**Proof upgrade required before upstream submission:** prove that the serialized names in `Attrs.unique` are pairwise distinct for arbitrary input, including collisions created by sanitization. Preserve `Attrs.render_safe` and `Attrs.render_wellFormed`. Strengthen the formal output contract appropriately; the current `WellFormedAttrs` predicate itself does not express uniqueness. Verify the test suite has no admitted proofs or suppressions. Evaluate time complexity for many attributes and collisions between flag/value fragments.

The attribute precedence rule and output compatibility require maintainer agreement. The pre-existing XML-illegal-character and namespace cases are deliberately untouched.

Downstream: in a disposable `lean-markdown` worktree, temporarily replace only the pinned `lean-html` dependency with this fork branch, run `lake update html`, `lake build`, and `lake test`. Preserve the original lockfile and report all changes; never commit dependency overrides.
