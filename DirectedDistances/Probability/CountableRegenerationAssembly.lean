/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict

/-! # Countable assembly of restricted pushforward laws

Generic countable-additivity algebra supporting the random finite-time
assembly for Lemma 4.9 (`lem-renewal`), unchanged
all piece identities and a common measurable map on its actual domain.
This module neither defines a renewal time nor proves the paper theorem. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory

/-- Countable disjoint-partition assembly of actual restricted pushforward
laws. Source applications must produce every per-piece identity.
No positivity or finiteness assumption is required. -/
theorem map_restrict_iUnion_inter_eq_smul
    {ι α β : Type*} [Countable ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ρ : Measure β) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (B : Set α) (hB : MeasurableSet B)
    (f : α → β) (hf : Measurable f)
    (hpiece : ∀ i,
      (μ.restrict (s i ∩ B)).map f = μ (s i ∩ B) • ρ) :
    (μ.restrict ((⋃ i, s i) ∩ B)).map f =
      μ ((⋃ i, s i) ∩ B) • ρ := by
  have hsB : ∀ i, MeasurableSet (s i ∩ B) :=
    fun i => (hs i).inter hB
  have hdB : Pairwise (fun i j =>
      Disjoint (s i ∩ B) (s j ∩ B)) :=
    fun i j hij =>
      (hd hij).mono Set.inter_subset_left Set.inter_subset_left
  have hunion : ((⋃ i, s i) ∩ B) = ⋃ i, s i ∩ B :=
    Set.iUnion_inter B s
  apply Measure.ext
  intro t ht
  calc
    (μ.restrict ((⋃ i, s i) ∩ B)).map f t
        = μ.restrict (⋃ i, s i ∩ B) (f ⁻¹' t) := by
            rw [Measure.map_apply hf ht, hunion]
    _ = ∑' i, μ.restrict (s i ∩ B) (f ⁻¹' t) :=
      Measure.restrict_iUnion_apply hdB hsB (ht.preimage hf)
    _ = ∑' i, μ (s i ∩ B) * ρ t := by
      apply tsum_congr
      intro i
      calc
        μ.restrict (s i ∩ B) (f ⁻¹' t)
            = ((μ.restrict (s i ∩ B)).map f) t :=
              (Measure.map_apply hf ht).symm
        _ = (μ (s i ∩ B) • ρ) t := by rw [hpiece i]
        _ = μ (s i ∩ B) * ρ t := rfl
    _ = (∑' i, μ (s i ∩ B)) * ρ t :=
      ENNReal.tsum_mul_right
    _ = μ (⋃ i, s i ∩ B) * ρ t := by
      rw [measure_iUnion hdB hsB]
    _ = (μ ((⋃ i, s i) ∩ B) • ρ) t := by
      rw [hunion]
      rfl

end DirectedDistances.Probability
