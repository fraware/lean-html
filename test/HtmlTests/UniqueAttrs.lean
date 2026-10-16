/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Html.Escape

namespace HtmlTests

open Html

/-- `uniqueGo` keeps a fragment iff its effective name is new. -/
theorem uniqueGo_cons (dialect : Dialect) (seen : List String) (f : AttrFragment) (rest : Attrs) :
    Attrs.uniqueGo dialect seen (f :: rest) =
      if seen.contains (f.nameKey dialect) then
        Attrs.uniqueGo dialect seen rest
      else
        f :: Attrs.uniqueGo dialect (f.nameKey dialect :: seen) rest := by
  simp [Attrs.uniqueGo]

theorem uniqueGo_names (dialect : Dialect) (seen : List String) (attrs : Attrs) :
    ((Attrs.uniqueGo dialect seen attrs).map (AttrFragment.nameKey dialect)).Nodup ∧
      ∀ n, n ∈ (Attrs.uniqueGo dialect seen attrs).map (AttrFragment.nameKey dialect) →
        n ∉ seen := by
  induction attrs generalizing seen with
  | nil =>
    simp [Attrs.uniqueGo]
  | cons f rest ih =>
    rw [uniqueGo_cons]
    split
    · exact ih seen
    · rename_i hnotcontains
      simp only [List.map_cons]
      have hnot : f.nameKey dialect ∉ seen := by
        intro hin
        exact hnotcontains ((List.contains_iff_mem).mpr hin)
      have ih' := ih (f.nameKey dialect :: seen)
      refine ⟨?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, ih'.1⟩
        intro hin
        exact ih'.2 (f.nameKey dialect) hin List.mem_cons_self
      · intro n hn hseen
        simp only [List.mem_cons] at hn
        cases hn with
        | inl heq =>
          subst heq
          exact hnot hseen
        | inr hin =>
          exact ih'.2 n hin (List.mem_cons_of_mem _ hseen)

/-- Effective names kept by the public deduplicator are pairwise distinct in
both dialects. The key is `AttrFragment.nameKey`: sanitization, then ASCII
case-folding for `.html5` only. -/
theorem unique_nameKeys_nodup (attrs : Attrs) (dialect : Dialect) :
    ((Attrs.unique attrs dialect).map (AttrFragment.nameKey dialect)).Nodup :=
  (uniqueGo_names dialect [] attrs).1

/-- `Attrs.render` serializes exactly the fragments `Attrs.unique` kept. -/
theorem render_serializes_unique (attrs : Attrs) (dialect : Dialect) :
    Attrs.render attrs dialect =
      String.join ((Attrs.unique attrs dialect).map (AttrFragment.render dialect)) := by
  simp [Attrs.render]

/-- Two seen-lists that agree on every name still present yield the same
deduplication. -/
theorem uniqueGo_congr_seen (dialect : Dialect) (seen seen' : List String) (attrs : Attrs)
    (h : ∀ n ∈ attrs.map (AttrFragment.nameKey dialect),
      seen.contains n = seen'.contains n) :
    Attrs.uniqueGo dialect seen attrs = Attrs.uniqueGo dialect seen' attrs := by
  induction attrs generalizing seen seen' with
  | nil =>
    simp [Attrs.uniqueGo]
  | cons f rest ih =>
    have hf : f.nameKey dialect ∈ (f :: rest).map (AttrFragment.nameKey dialect) := by
      simp
    have hhead := h (f.nameKey dialect) hf
    rw [uniqueGo_cons, uniqueGo_cons, hhead]
    split
    · apply ih
      intro n hn
      exact h n (List.mem_cons_of_mem _ hn)
    · apply congrArg (f :: ·)
      apply ih
      intro n hn
      have hmem : decide (n ∈ seen) = decide (n ∈ seen') := by
        simpa [List.contains_eq_mem] using h n (List.mem_cons_of_mem _ hn)
      simp only [List.contains_eq_mem, List.decide_mem_cons]
      rw [hmem]

/-- Names absent from `seen` are filtered exactly as they would be from an
empty seen-list. -/
theorem uniqueGo_of_disjoint_seen (dialect : Dialect) (seen : List String) (attrs : Attrs)
    (h : ∀ n ∈ attrs.map (AttrFragment.nameKey dialect), n ∉ seen) :
    Attrs.uniqueGo dialect seen attrs = Attrs.uniqueGo dialect [] attrs := by
  apply uniqueGo_congr_seen
  intro n hn
  have hnseen : n ∉ seen := h n hn
  simp [List.contains_eq_mem, List.not_mem_nil, hnseen]

/-- Processing `a ++ b` prepends the kept names of `a`, in reverse, to `seen`. -/
theorem uniqueGo_append (dialect : Dialect) (seen : List String) (a b : Attrs) :
    Attrs.uniqueGo dialect seen (a ++ b) =
      Attrs.uniqueGo dialect seen a ++
        Attrs.uniqueGo dialect
          (((Attrs.uniqueGo dialect seen a).map (AttrFragment.nameKey dialect)).reverse ++ seen)
          b := by
  induction a generalizing seen with
  | nil =>
    simp [Attrs.uniqueGo]
  | cons f rest ih =>
    rw [List.cons_append, uniqueGo_cons (rest := rest ++ b), uniqueGo_cons (rest := rest)]
    split
    · exact ih seen
    · rw [ih (f.nameKey dialect :: seen)]
      simp [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append]

/-- No effective name of `b` was already kept from `a`. -/
theorem unique_append_of_disjoint (a b : Attrs) (dialect : Dialect)
    (h : ∀ n ∈ b.map (AttrFragment.nameKey dialect),
      n ∉ (Attrs.unique a dialect).map (AttrFragment.nameKey dialect)) :
    Attrs.unique (a ++ b) dialect = Attrs.unique a dialect ++ Attrs.unique b dialect := by
  unfold Attrs.unique
  rw [uniqueGo_append]
  refine congrArg (Attrs.uniqueGo dialect [] a ++ ·) ?_
  apply uniqueGo_of_disjoint_seen
  intro n hn hmem
  simp only [List.mem_append, List.mem_reverse, List.mem_nil_iff, or_false] at hmem
  exact h n hn hmem

/-- `Attrs.render` commutes with concatenation when the two lists have
disjoint effective names. The unconditional form is false: a shared name
keeps the first fragment and drops the second. -/
theorem attrsRender_append (a b : Attrs) (dialect : Dialect)
    (h : ∀ n ∈ b.map (AttrFragment.nameKey dialect),
      n ∉ (Attrs.unique a dialect).map (AttrFragment.nameKey dialect)) :
    Attrs.render (a ++ b) dialect = Attrs.render a dialect ++ Attrs.render b dialect := by
  simp only [Attrs.render, unique_append_of_disjoint a b dialect h, List.map_append,
    String.join_append]

end HtmlTests
