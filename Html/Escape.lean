/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Html.Dialect

@[expose] public section

namespace Html

/-- Escapes `&`, `<`, `>`, `"` -/
def escapeChar (c : Char) : String :=
  match c with
  | '&' => "&amp;" -- Must be first
  | '<' => "&lt;"
  | '>' => "&gt;"
  | '"' => "&quot;"
  | c    => String.singleton c

def escape (s : String) : String :=
  String.join (s.toList.map escapeChar)

/-- Render one attribute as `name="escaped value"`, with a leading space
so callers can concatenate these directly after a tag name. -/
def renderAttr (name value : String) : String :=
  s!" {name}=\"{escape value}\""

/-- Characters allowed to *begin* a sanitized attribute name: XML's
`NameStartChar` production, restricted to ASCII. -/
def isAttrNameStartChar (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == ':'

/-- Characters allowed in a sanitized attribute name, adding to
`isAttrNameStartChar` the three that XML admits everywhere but first.
Between them these cover real-world names (`data-x`, `aria-label`,
`v-on:click`) while excluding anything (whitespace, `=`, `<`, `>`, quotes)
that would let a name break out of the tag it's rendered into. -/
def isAttrNameChar (c : Char) : Bool :=
  isAttrNameStartChar c || c.isDigit || c == '-' || c == '.'

def sanitizeAttrNameChar (c : Char) : Char :=
  if isAttrNameChar c then c else '_'

/-- Coerce an arbitrary string into a safe attribute name: every
disallowed character becomes `_`, and a further `_` is prepended unless
what's left already begins with an `isAttrNameStartChar`, which also
covers the empty string, giving `_`. Mirrors `escape`'s role for
attribute *values*: callers can pass untrusted strings as `rawAttrs`
names (`Html/Attrs.lean`'s `renderRawAttrs`) and still get well-formed
output. -/
def sanitizeAttrName (s : String) : String :=
  (if (s.map sanitizeAttrNameChar).toList.head?.any isAttrNameStartChar then "" else "_")
    ++ s.map sanitizeAttrNameChar

/-- One rendered attribute: a `name="value"` pair, or a bare boolean flag
(`name`, no value). Names and values are stored *unsanitized/unescaped*;
`AttrFragment.render` is the only place that happens. -/
inductive AttrFragment where
  | value (name val : String)
  | flag (name : String)

/-- An attribute list, in emission order. This is the only type
`Html/Node.lean`'s element constructors accept for attributes, and it's
what they *store*: an `Attrs` value can't smuggle in an unescaped
`<`/`>`/`"` no matter what strings its fragments carry, because turning it
into a string always goes through `Attrs.render` below. Keeping the list
rather than its rendering is also what lets the dialect be chosen at
render time. -/
abbrev Attrs := List AttrFragment

/-- Render one fragment, sanitizing its name and escaping its value. XML
has no bare attributes, so a flag becomes `name="name"` there. -/
def AttrFragment.render (dialect : Dialect) : AttrFragment → String
  | .value name val => renderAttr (sanitizeAttrName name) val
  | .flag name =>
    match dialect with
    | .html5 => s!" {sanitizeAttrName name}"
    | .xhtml => renderAttr (sanitizeAttrName name) (sanitizeAttrName name)

/-- Names are compared after sanitization, since distinct inputs can render identically. -/
def AttrFragment.name : AttrFragment → String
  | .value name _ => name
  | .flag name => name

/-- ASCII lowercasing for HTML attribute-name comparison. -/
def asciiLowerAttrChar (c : Char) : Char :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then Char.ofNat (c.toNat + 32) else c

/-- HTML5 compares ASCII attribute names without case; XML preserves case. -/
def AttrFragment.nameKey (dialect : Dialect) (f : AttrFragment) : String :=
  let name := sanitizeAttrName f.name
  match dialect with
  | .html5 => name.map asciiLowerAttrChar
  | .xhtml => name

/-- Keep the first fragment for each serialized name, preserving input order. -/
def Attrs.uniqueGo (dialect : Dialect) (seen : List String) : Attrs → Attrs
  | [] => []
  | f :: rest =>
    let name := f.nameKey dialect
    if seen.contains name then Attrs.uniqueGo dialect seen rest
    else f :: Attrs.uniqueGo dialect (name :: seen) rest

def Attrs.unique (attrs : Attrs) (dialect : Dialect := .html5) : Attrs :=
  Attrs.uniqueGo dialect [] attrs

/-- Serialize a list of fragments, without resolving duplicate names. -/
private def Attrs.renderFragments (attrs : Attrs) (dialect : Dialect := .html5) : String :=
  String.join (attrs.map (AttrFragment.render dialect))

/-- Render each sanitized name once; the first fragment takes precedence. -/
def Attrs.render (attrs : Attrs) (dialect : Dialect := .html5) : String :=
  String.join ((Attrs.unique attrs dialect).map (AttrFragment.render dialect))

/-- A single required `name="value"` attribute. -/
def reqAttr (name value : String) : Attrs := [.value name value]

/-- A single `name="value"` attribute when present, nothing otherwise. -/
def optAttr (name : String) : Option String → Attrs
  | none => []
  | some v => [.value name v]

/-- A single bare `name` flag when `true`, nothing otherwise. -/
def flagAttr (name : String) (b : Bool) : Attrs :=
  if b then [.flag name] else []

/-- Render arbitrary `(name, value)` pairs: values escaped, names sanitized
(see `sanitizeAttrName`) so a name containing e.g. a space or `"` can't
break out of the tag it's rendered into. -/
def renderRawAttrs (attrs : List (String × String)) (dialect : Dialect := .html5) : String :=
  Attrs.render (attrs.map fun (n, v) => .value n v) dialect

/-- `String.join` over a mapped list preserves "every character satisfies `P`",
given every individual mapped piece does. -/
private theorem join_map_safe {α : Type} {P : Char → Prop} (f : α → String) (l : List α)
    (h : ∀ x ∈ l, ∀ c ∈ (f x).toList, P c) : ∀ c ∈ (String.join (l.map f)).toList, P c := by
  intro c hc
  rw [String.toList_join] at hc
  simp only [List.mem_flatMap, List.mem_map] at hc
  obtain ⟨y, ⟨x, hxmem, hxeq⟩, hcy⟩ := hc
  exact h x hxmem c (hxeq ▸ hcy)

/-- Concatenation preserves "every character satisfies `P`". -/
private theorem append_safe {P : Char → Prop} {a b : String}
    (ha : ∀ c ∈ a.toList, P c) (hb : ∀ c ∈ b.toList, P c) : ∀ c ∈ (a ++ b).toList, P c := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  exact hc.elim (ha c) (hb c)

private def isDangerous (c : Char) : Bool := c == '<' || c == '>' || c == '"'

private theorem escapeChar_clean (c : Char) :
    ∀ c' ∈ (escapeChar c).toList, isDangerous c' = false := by
  unfold escapeChar
  split
  case h_1 => decide
  case h_2 => decide
  case h_3 => decide
  case h_4 => decide
  case h_5 =>
    intro c' hc'
    simp only [String.toList_singleton, List.mem_singleton] at hc'
    subst hc'
    unfold isDangerous
    simp_all

/-- **The XSS-relevant safety property:** `escape`'s output never contains a raw
(unescaped) `<`, `>`, or `"`. This is what makes double-quote-delimited,
escaped attribute values and escaped text content safe against markup
breakout, given a renderer that keeps the escaped value between its two
literal `"` delimiters. -/
theorem escape_safe (s : String) : ∀ c ∈ (escape s).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' :=
  join_map_safe escapeChar s.toList fun c0 _ c hc => by
    have h := escapeChar_clean c0 c hc
    unfold isDangerous at h
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩

private theorem map_sanitizeAttrNameChar_safe (s : String) :
    ∀ c ∈ (s.map sanitizeAttrNameChar).toList, isAttrNameChar c = true := by
  rw [String.toList_map]
  intro c hc
  obtain ⟨c', _, heq⟩ := List.mem_map.mp hc
  simp only [sanitizeAttrNameChar] at heq
  split at heq <;> subst heq <;> first | assumption | decide

/-- **The rawAttrs-name-relevant safety property:** `sanitizeAttrName`'s output
consists entirely of `isAttrNameChar` characters; no whitespace, `=`, `<`,
`>`, or quote can survive sanitization. This is what closes the `renderRawAttrs`
gap: an untrusted attribute name can no longer break out of the tag it's
rendered into (compare `escape_safe`, which gives the same guarantee for
attribute *values*). -/
theorem sanitizeAttrName_safe (s : String) :
    ∀ c ∈ (sanitizeAttrName s).toList, isAttrNameChar c = true := by
  unfold sanitizeAttrName
  refine append_safe ?_ (map_sanitizeAttrNameChar_safe s)
  split <;> decide

/-- `sanitizeAttrName`'s output is non-empty and starts with a character XML
admits as the first of a `Name`, which `sanitizeAttrName_safe` alone doesn't
give: a digit, `-`, and `.` are legal later in a name but not first. -/
theorem sanitizeAttrName_start (s : String) :
    (sanitizeAttrName s).toList.head?.any isAttrNameStartChar = true := by
  unfold sanitizeAttrName
  split
  · rename_i h; simpa using h
  · rw [String.toList_append]; rfl

/-- What `Attrs.render` guarantees about every name it emits: XML's `Name`
production, restricted to ASCII. HTML is laxer, so a name meeting this is
valid in both dialects. -/
structure IsAttrName (s : String) : Prop where
  start : s.toList.head?.any isAttrNameStartChar
  chars : ∀ c ∈ s.toList, isAttrNameChar c

theorem sanitizeAttrName_isAttrName (s : String) : IsAttrName (sanitizeAttrName s) :=
  ⟨sanitizeAttrName_start s, sanitizeAttrName_safe s⟩

/-- The shape of a rendered attribute string, stated independently of
`Attrs`: a concatenation of ` name="value"` pairs, each name an
`IsAttrName` and no value carrying a raw `<`, `>`, or `"`. Bare flags
(` name`, no value) are admitted under `.html5` only; there's deliberately
no `.xhtml` case for them, so this predicate holding at `.xhtml` *is* the
statement that XML output gives every attribute a value. -/
inductive WellFormedAttrs : Dialect → String → Prop where
  | nil {d : Dialect} : WellFormedAttrs d ""
  | value {d : Dialect} {name value rest : String} (hname : IsAttrName name)
      (hvalue : ∀ c ∈ value.toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"')
      (hrest : WellFormedAttrs d rest) :
      WellFormedAttrs d (" " ++ name ++ "=\"" ++ value ++ "\"" ++ rest)
  | flag {name rest : String} (hname : IsAttrName name)
      (hrest : WellFormedAttrs .html5 rest) :
      WellFormedAttrs .html5 (" " ++ name ++ rest)

private theorem isAttrNameChar_safe (c : Char) (h : isAttrNameChar c = true) :
    c ≠ '<' ∧ c ≠ '>' := by
  unfold isAttrNameChar isAttrNameStartChar at h
  constructor <;> (rintro rfl; simp_all)

private theorem renderAttr_sanitized_safe (name value : String) :
    ∀ c ∈ (renderAttr (sanitizeAttrName name) value).toList, c ≠ '<' ∧ c ≠ '>' := by
  have heq : renderAttr (sanitizeAttrName name) value
      = " " ++ sanitizeAttrName name ++ "=\"" ++ escape value ++ "\"" := rfl
  simp only [heq]
  refine append_safe (P := fun c => c ≠ '<' ∧ c ≠ '>')
    (append_safe (append_safe (append_safe (by decide)
      (fun c hc => isAttrNameChar_safe c (sanitizeAttrName_safe name c hc))) (by decide))
      (fun c hc => ⟨(escape_safe value c hc).1, (escape_safe value c hc).2.1⟩)) (by decide)

private theorem AttrFragment.render_safe (dialect : Dialect) (f : AttrFragment) :
    ∀ c ∈ (f.render dialect).toList, c ≠ '<' ∧ c ≠ '>' := by
  cases f with
  | value name val => exact renderAttr_sanitized_safe name val
  | flag name =>
    cases dialect with
    | html5 =>
      have heq : (AttrFragment.flag name).render .html5 = " " ++ sanitizeAttrName name := rfl
      simp only [heq]
      exact append_safe (by decide)
        (fun c hc => isAttrNameChar_safe c (sanitizeAttrName_safe name c hc))
    | xhtml => exact renderAttr_sanitized_safe name (sanitizeAttrName name)

/-- **The well-formedness-relevant safety property:** no matter what
fragments an `Attrs` value contains, `Attrs.render`'s output never contains
a raw `<` or `>`; every name goes through `sanitizeAttrName_safe`, every
value through `escape_safe`. -/
theorem Attrs.render_safe (attrs : Attrs) (dialect : Dialect := .html5) :
    ∀ c ∈ (Attrs.render attrs dialect).toList, c ≠ '<' ∧ c ≠ '>' := by
  exact join_map_safe _ (Attrs.unique attrs dialect) fun f _ =>
    AttrFragment.render_safe dialect f

private theorem Attrs.renderFragments_wellFormed (attrs : Attrs) (dialect : Dialect := .html5) :
    WellFormedAttrs dialect (Attrs.renderFragments attrs dialect) := by
  induction attrs with
  | nil => simpa [Attrs.renderFragments] using WellFormedAttrs.nil (d := dialect)
  | cons f rest ih =>
    have hcons : Attrs.renderFragments (f :: rest) dialect
        = f.render dialect ++ Attrs.renderFragments rest dialect := by
      simp [Attrs.renderFragments]
    rw [hcons]
    cases f with
    | value name val =>
      have heq : (AttrFragment.value name val).render dialect
          = " " ++ sanitizeAttrName name ++ "=\"" ++ escape val ++ "\"" := rfl
      rw [heq]
      exact .value (sanitizeAttrName_isAttrName name) (escape_safe val) ih
    | flag name =>
      cases dialect with
      | html5 =>
        have heq : (AttrFragment.flag name).render .html5 = " " ++ sanitizeAttrName name := rfl
        rw [heq]
        exact .flag (sanitizeAttrName_isAttrName name) ih
      | xhtml =>
        have heq : (AttrFragment.flag name).render .xhtml
            = " " ++ sanitizeAttrName name ++ "=\"" ++ escape (sanitizeAttrName name) ++ "\"" := rfl
        rw [heq]
        exact .value (sanitizeAttrName_isAttrName name) (escape_safe (sanitizeAttrName name)) ih

/-- **The attribute-shape theorem:** every string `Attrs.render` produces is a
well-formed run of attributes for the dialect it was asked for. At `.xhtml`
this is the stronger claim, `WellFormedAttrs` having no bare flag there. -/
theorem Attrs.render_wellFormed (attrs : Attrs) (dialect : Dialect := .html5) :
    WellFormedAttrs dialect (Attrs.render attrs dialect) := by
  exact Attrs.renderFragments_wellFormed (Attrs.unique attrs dialect) dialect

end Html
