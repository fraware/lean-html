/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Html

namespace HtmlContractAudit

open Html

private def duplicateAttrs : Attrs :=
  [.value "id" "first", .value "id" "second"]

private def duplicateNode : Node .flow :=
  Node.element .flow "div" [] duplicateAttrs

-- This proof intentionally witnesses what the current *formal* predicate admits.
-- The emitted XML must independently be checked against a conforming parser.
example : WellFormedHtml .xhtml (duplicateNode.render (dialect := .xhtml)) := by
  apply Node.render_wellFormed duplicateNode (dialect := .xhtml)
  unfold duplicateNode
  exact Node.element_wellFormed .flow "div" [] duplicateAttrs (by simp)

private def nul : String := String.singleton (Char.ofNat 0)

private def cases : List (String × String) := [
  ("control-valid", (div [p ["OK"]]).render (dialect := .xhtml)),
  ("duplicate-typed-raw", (div [] { id := "first" }
    (rawAttrs := [("id", "second")])).render (dialect := .xhtml)),
  ("duplicate-sanitized", (div []
    (rawAttrs := [("a b", "first"), ("a_b", "second")])).render (dialect := .xhtml)),
  ("duplicate-formal-witness", duplicateNode.render (dialect := .xhtml)),
  ("nul-text", (p [(nul : Node .phrasing)]).render (dialect := .xhtml)),
  ("nul-attribute", (div [] { title := nul }).render (dialect := .xhtml)),
  ("unbound-namespace-prefix", (div []
    (rawAttrs := [("v-on:click", "go")])).render (dialect := .xhtml)),
  ("arbitrary-tag-name", (Node.element .flow "bad tag" []).render (dialect := .xhtml))
]

-- Distinct machine-readable records; the NUL-containing cases are emitted as raw bytes.
#eval show IO Unit from do
  for (name, output) in cases do
    IO.println ("XHTML_CASE\t" ++ name ++ "\t" ++ output)

end HtmlContractAudit
