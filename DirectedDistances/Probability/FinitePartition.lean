/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict

/-! # Finite disjoint partitions of restricted pushforward measures

Generic finite-additivity algebra for the actual past-event assembly in
Source applications must produce every per-piece measure identity; this
module neither assumes nor proves a conditional renewal law. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory

/-- If each piece of a finite measurable disjoint partition has the same
normalized pushed-forward measure, then so does their union. The common
event is intersected with each piece before restriction. No finiteness or
positivity assumption on either measure is needed for this measure identity. -/
theorem map_restrict_biUnion_inter_eq_smul
    {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ρ : Measure β) (I : Finset ι) (s : ι → Set α)
    (hs : ∀ i ∈ I, MeasurableSet (s i))
    (hd : (I : Set ι).Pairwise (fun i j => Disjoint (s i) (s j)))
    (B : Set α) (hB : MeasurableSet B) (f : α → β) (hf : Measurable f)
    (hpiece : ∀ i ∈ I,
      (μ.restrict (s i ∩ B)).map f = μ (s i ∩ B) • ρ) :
    (μ.restrict ((⋃ i ∈ I, s i) ∩ B)).map f =
      μ ((⋃ i ∈ I, s i) ∩ B) • ρ := by
  classical
  revert hs hd hpiece
  induction I using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp
  | @insert a I ha ih =>
    intro hs hd hpiece
    have hsI : ∀ i ∈ I, MeasurableSet (s i) :=
      fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hdI : (I : Set ι).Pairwise (fun i j => Disjoint (s i) (s j)) :=
      fun i hi j hj hij => hd (Finset.mem_insert_of_mem hi)
        (Finset.mem_insert_of_mem hj) hij
    have hpieceI : ∀ i ∈ I,
        (μ.restrict (s i ∩ B)).map f = μ (s i ∩ B) • ρ :=
      fun i hi => hpiece i (Finset.mem_insert_of_mem hi)
    have hI := ih hsI hdI hpieceI
    let U : Set α := ⋃ i ∈ I, s i
    have hU : MeasurableSet U :=
      MeasurableSet.biUnion I.countable_toSet hsI
    have hdis : Disjoint (s a) U := by
      apply Set.disjoint_left.mpr
      intro x hxa hxU
      simp only [U, Set.mem_iUnion] at hxU
      obtain ⟨j, hj, hxj⟩ := hxU
      have haj : a ≠ j := by
        rintro rfl
        exact ha hj
      exact Set.disjoint_left.mp
        (hd (Finset.mem_insert_self a I) (Finset.mem_insert_of_mem hj) haj) hxa hxj
    have hdisB : Disjoint (s a ∩ B) (U ∩ B) :=
      hdis.mono Set.inter_subset_left Set.inter_subset_left
    have hsplit : ((⋃ i ∈ insert a I, s i) ∩ B) = (s a ∩ B) ∪ (U ∩ B) := by
      have hu : (⋃ i ∈ insert a I, s i) = s a ∪ U := by
        ext x
        simp only [U, Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨i, hi, hxi⟩
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Or.inl hxi
          · exact Or.inr ⟨i, hi, hxi⟩
        · rintro (hxa | ⟨i, hi, hxi⟩)
          · exact ⟨a, Finset.mem_insert_self a I, hxa⟩
          · exact ⟨i, Finset.mem_insert_of_mem hi, hxi⟩
      rw [hu, Set.union_inter_distrib_right]
    rw [hsplit, Measure.restrict_union hdisB (hU.inter hB),
      Measure.map_add _ _ hf, hpiece a (Finset.mem_insert_self a I), hI,
      measure_union hdisB (hU.inter hB), add_smul]

end DirectedDistances.Probability
