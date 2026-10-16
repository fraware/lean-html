/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Html.Escape
meta import Html.Escape

namespace HtmlTests

open Html

#guard escape "<script>" = "&lt;script&gt;"
#guard escape "\"onclick=\"" = "&quot;onclick=&quot;"
#guard escape "a & b" = "a &amp; b"
#guard escape "" = ""
#guard escape "héllo wörld 日本語" = "héllo wörld 日本語"
#guard escape "&<>\"" = "&amp;&lt;&gt;&quot;"
#guard escape "&amp;" = "&amp;amp;"  -- already-escaped input isn't special-cased; re-escaping & first is correct

/-- **Compositionality:** escaping two fragments and concatenating the results
is the same as escaping their concatenation directly. No double-escaping
and no under-escaping happens at the fragment boundary. -/
theorem escape_append (a b : String) : escape (a ++ b) = escape a ++ escape b := by
  unfold escape
  rw [String.toList_append, List.map_append, String.join_append]

/-- **The paired renderer-side invariant:** `renderAttr` always embeds the escaped
value between two literal `"` delimiters. Combined with `escape_safe`, this rules
out attribute-value breakout: the value can never contain a raw `"` to close the
attribute early, nor a raw `<`/`>` to open a new tag. -/
theorem renderAttr_safe (name value : String) :
    renderAttr name value = s!" {name}=\"" ++ escape value ++ "\"" ∧
      ∀ c ∈ (escape value).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' :=
  ⟨rfl, escape_safe value⟩

/-- When two fragments have the same serialized name, the first wins, in
either output dialect. The earlier unconditional append law cannot hold. -/
theorem attrsRender_firstWins (first second : String) (dialect : Dialect) :
    Attrs.render [.value "id" first, .value "id" second] dialect =
      Attrs.render [.value "id" first] dialect := by
  cases dialect <;>
    simp [Attrs.render, Attrs.unique, Attrs.uniqueGo, AttrFragment.nameKey,
      AttrFragment.name, sanitizeAttrName,
      sanitizeAttrNameChar, isAttrNameChar, isAttrNameStartChar]

#guard Attrs.render [.value "id" "first", .value "id" "second"] .xhtml =
  " id=\"first\""
#guard Attrs.render [.value "id" "first", .value "id" "second"] .html5 =
  " id=\"first\""
#guard Attrs.render [.value "a b" "first", .value "a_b" "second"] .xhtml =
  " a_b=\"first\""
#guard Attrs.render [.flag "hidden", .value "hidden" "override"] .xhtml =
  " hidden=\"hidden\""
#guard Attrs.render [.value "id" "first", .flag "id"] .html5 =
  " id=\"first\""
#guard Attrs.render [.value "id" "first", .value "ID" "second"] .html5 =
  " id=\"first\""
#guard Attrs.render [.value "id" "first", .value "ID" "second"] .xhtml =
  " id=\"first\" ID=\"second\""
#guard Attrs.render [.value "ID" "first", .value "id" "second"] .html5 =
  " ID=\"first\""
#guard Attrs.render (reqAttr "id" "first" ++ [.value "id" "second"]) .xhtml =
  Attrs.render (reqAttr "id" "first") .xhtml

theorem attrsRender_reqAttr (name value : String) (dialect : Dialect) :
    Attrs.render (reqAttr name value) dialect = renderAttr (sanitizeAttrName name) value := by
  simp [Attrs.render, Attrs.unique, Attrs.uniqueGo, reqAttr, AttrFragment.render]

theorem attrsRender_optAttr_none (name : String) (dialect : Dialect) :
    Attrs.render (optAttr name none) dialect = "" := by
  simp [Attrs.render, Attrs.unique, Attrs.uniqueGo, optAttr]

theorem attrsRender_optAttr_some (name value : String) (dialect : Dialect) :
    Attrs.render (optAttr name (some value)) dialect = renderAttr (sanitizeAttrName name) value := by
  simp [Attrs.render, Attrs.unique, Attrs.uniqueGo, optAttr, AttrFragment.render]

/-- A `false` boolean attribute contributes nothing at all: never `name="false"`,
which the HTML spec reads as the attribute being *present*, hence true. -/
theorem attrsRender_flagAttr_false (name : String) (dialect : Dialect) :
    Attrs.render (flagAttr name false) dialect = "" := by
  simp [Attrs.render, Attrs.unique, Attrs.uniqueGo, flagAttr]

theorem attrsRender_flagAttr_true_html5 (name : String) :
    Attrs.render (flagAttr name true) .html5 = " " ++ sanitizeAttrName name := by
  simp [Attrs.render, Attrs.unique, Attrs.uniqueGo, flagAttr, AttrFragment.render, toString]

/-- The same attribute in XML, where a bare name isn't well-formed: HTML5 reads
`name="name"` as present, so the two renderings agree on meaning. -/
theorem attrsRender_flagAttr_true_xhtml (name : String) :
    Attrs.render (flagAttr name true) .xhtml
      = renderAttr (sanitizeAttrName name) (sanitizeAttrName name) := by
  simp [Attrs.render, Attrs.unique, Attrs.uniqueGo, flagAttr, AttrFragment.render]

end HtmlTests
