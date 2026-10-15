# XML 1.0 character normalization experiment

**Not a PR. Not compiled in this environment.** Based on upstream `56d842fe8b1f05028b0b5083fc25270235f19857`.

This branch leaves the public signatures of `escapeChar`, `escape`, `Attrs.render`, and `Node.render` unchanged. It replaces characters excluded from XML 1.0's Fifth Edition `Char` production with U+FFFD inside `escape`. That path is shared by HTML5 and XHTML, because text is escaped before dialect selection; the choice is intentionally experimental and changes both dialects for formerly unsupported characters.

The existing `escape_safe` theorem is adapted to the additional preprocessing stage, with `escapeChar_clean` unchanged. Tests cover U+0000, U+001F, U+FFFE, U+FFFF, TAB, LF, CR, escaped attributes, and ordinary Unicode. The audit harness expects both NUL cases to become valid XML. Other known invalid cases still fail.

Run on the **exact commit** in a separate clean Linux or WSL2 worktree:

```bash
set -euo pipefail
lake build
lake env lean repros/XhtmlContractAudit.lean > /tmp/xhtml-xml10-audit.tsv
python3 repros/check_xml_contract.py < /tmp/xhtml-xml10-audit.tsv
lake test
git diff --check 56d842fe8b1f05028b0b5083fc25270235f19857 HEAD
```

**Proof upgrade required before any upstream submission:** establish `isXml10Char` preservation for all characters emitted by `escape`, not just the existing prohibition on raw `<`, `>`, `"`. Inspect XML 1.0 boundary values, surrogate handling by Lean's `Char`, invalid-UTF-8 handling, and potential security implications of lossy replacement. Reconcile the behavioral policy with the maintainer before merging. The pre-existing duplicate-attribute and namespace issues remain independent.

Downstream: in a disposable `lean-markdown` worktree, temporarily replace only the pinned `lean-html` dependency with this fork branch, run `lake update html`, `lake build`, and `lake test`. Preserve the original lockfile and report all changes; never commit dependency overrides.
