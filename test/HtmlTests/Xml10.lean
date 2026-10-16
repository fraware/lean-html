/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Html.Escape
meta import Html.Escape

namespace HtmlTests

open Html

/-- XML 1.0 Fifth Edition Char, associated to match `isXml10Char`'s `||` chain. -/
def Xml10Char (c : Char) : Prop :=
  ((((c.toNat = 0x9 ∨ c.toNat = 0xA) ∨ c.toNat = 0xD) ∨
      (0x20 ≤ c.toNat ∧ c.toNat ≤ 0xD7FF)) ∨
    (0xE000 ≤ c.toNat ∧ c.toNat ≤ 0xFFFD)) ∨
    (0x10000 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF)

instance (c : Char) : Decidable (Xml10Char c) := by
  unfold Xml10Char
  infer_instance

theorem isXml10Char_iff (c : Char) : isXml10Char c = true ↔ Xml10Char c := by
  unfold isXml10Char Xml10Char
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]

theorem xml10SafeChar_xml (c : Char) : Xml10Char (xml10SafeChar c) := by
  unfold xml10SafeChar
  split
  · rename_i h
    exact (isXml10Char_iff c).mp h
  · decide

theorem escapeChar_xml (c : Char) (h : Xml10Char c) :
    ∀ c' ∈ (escapeChar c).toList, Xml10Char c' := by
  unfold escapeChar
  split
  case h_1 => decide
  case h_2 => decide
  case h_3 => decide
  case h_4 => decide
  case h_5 =>
    intro c' hc
    simp only [String.toList_singleton, List.mem_singleton] at hc
    subst hc
    exact h

private theorem join_map_xml {α : Type} (f : α → String) (l : List α)
    (h : ∀ x ∈ l, ∀ c ∈ (f x).toList, Xml10Char c) :
    ∀ c ∈ (String.join (l.map f)).toList, Xml10Char c := by
  intro c hc
  rw [String.toList_join] at hc
  simp only [List.mem_flatMap, List.mem_map] at hc
  obtain ⟨y, ⟨x, hxmem, hxeq⟩, hcy⟩ := hc
  exact h x hxmem c (hxeq ▸ hcy)

theorem escape_xml10 (s : String) : ∀ c ∈ (escape s).toList, Xml10Char c := by
  unfold escape
  refine join_map_xml (fun c => escapeChar (xml10SafeChar c)) s.toList ?_
  intro c0 _ c hc
  exact escapeChar_xml (xml10SafeChar c0) (xml10SafeChar_xml c0) c hc

theorem renderAttr_value_xml10 (value : String) :
    ∀ c ∈ (escape value).toList, Xml10Char c :=
  escape_xml10 value

end HtmlTests
