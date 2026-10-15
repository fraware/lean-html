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

-- XML 1.0 excludes most C0 controls and the BMP noncharacters FFFE/FFFF.
-- Its Char production retains TAB, LF and CR, which must remain untouched.
#guard escape (String.singleton (Char.ofNat 0)) = "�"
#guard escape (String.singleton (Char.ofNat 0x1F)) = "�"
#guard escape (String.singleton (Char.ofNat 0xFFFE)) = "�"
#guard escape (String.singleton (Char.ofNat 0xFFFF)) = "�"
#guard escape (String.singleton (Char.ofNat 0x9)) = "\t"
#guard escape (String.singleton (Char.ofNat 0xA)) = "\n"
#guard escape (String.singleton (Char.ofNat 0xD)) = "\r"
#guard escape "héllo 日本語" = "héllo 日本語"
#guard renderAttr "title" (String.singleton (Char.ofNat 0)) = " title=\"�\""

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

/-- **Compositionality of attribute rendering:** an `Attrs` list renders to the
concatenation of its parts' renderings. Every `<Tag>Attrs.render` in
`Html/Attrs.lean` is a `++` chain over the primitives below, so this plus the
primitive laws pins down each record's output without enumerating its fields. -/
theorem attrsRender_append (a b : Attrs) (dialect : Dialect) :
    Attrs.render (a ++ b) dialect = Attrs.render a dialect ++ Attrs.render b dialect := by
  unfold Attrs.render
  rw [List.map_append, String.join_append]

theorem attrsRender_reqAttr (name value : String) (dialect : Dialect) :
    Attrs.render (reqAttr name value) dialect = renderAttr (sanitizeAttrName name) value := by
  simp [Attrs.render, reqAttr, AttrFragment.render]

theorem attrsRender_optAttr_none (name : String) (dialect : Dialect) :
    Attrs.render (optAttr name none) dialect = "" := by
  simp [Attrs.render, optAttr]

theorem attrsRender_optAttr_some (name value : String) (dialect : Dialect) :
    Attrs.render (optAttr name (some value)) dialect = renderAttr (sanitizeAttrName name) value := by
  simp [Attrs.render, optAttr, AttrFragment.render]

/-- A `false` boolean attribute contributes nothing at all: never `name="false"`,
which the HTML spec reads as the attribute being *present*, hence true. -/
theorem attrsRender_flagAttr_false (name : String) (dialect : Dialect) :
    Attrs.render (flagAttr name false) dialect = "" := by
  simp [Attrs.render, flagAttr]

theorem attrsRender_flagAttr_true_html5 (name : String) :
    Attrs.render (flagAttr name true) .html5 = " " ++ sanitizeAttrName name := by
  simp [Attrs.render, flagAttr, AttrFragment.render, toString]

/-- The same attribute in XML, where a bare name isn't well-formed: HTML5 reads
`name="name"` as present, so the two renderings agree on meaning. -/
theorem attrsRender_flagAttr_true_xhtml (name : String) :
    Attrs.render (flagAttr name true) .xhtml
      = renderAttr (sanitizeAttrName name) (sanitizeAttrName name) := by
  simp [Attrs.render, flagAttr, AttrFragment.render]

end HtmlTests
