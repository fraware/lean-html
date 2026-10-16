# Attribute-name uniqueness experiment

**Not a PR. Not compiled in this environment.** Based on upstream `56d842fe8b1f05028b0b5083fc25270235f19857`.

This branch implements first-occurrence precedence at `Attrs.render`. Duplicate detection uses **sanitized names** and dialect-specific comparison keys: HTML5 folds ASCII case, while XML compares exact names. Thus `"a b"` and `"a_b"` collide in both dialects, and `"id"` and `"ID"` collide only in HTML5. It covers typed/raw tag attributes, direct `Node.element` calls, and HTML5 flags. Typed attributes are emitted first and take precedence over later `rawAttrs`.

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

**Proof upgrade required before upstream submission:** compile the independently developed generic no-duplicate-names theorem as a tracked test and prove the stronger dialect-specific claim using `AttrFragment.nameKey`. The old external theorem used exact sanitized names and predates HTML5 ASCII case-folding. Preserve `Attrs.render_safe` and `Attrs.render_wellFormed`, and restore the append theorem under a properly proved disjointness condition if useful to downstream consumers. The current `WellFormedAttrs` predicate describes shape, not uniqueness, so do not overstate the formal guarantee. Check the revised `attrsRender_firstWins` proof, all existing tests, and asymptotic behavior for larger attribute lists.

The attribute precedence rule and output compatibility require maintainer agreement. The pre-existing XML-illegal-character and namespace cases are deliberately untouched.

Downstream: in a disposable `lean-markdown` worktree, temporarily replace only the pinned `lean-html` dependency with this fork branch, run `lake update html`, `lake build`, and `lake test`. Preserve the original lockfile and report all changes; never commit dependency overrides.
