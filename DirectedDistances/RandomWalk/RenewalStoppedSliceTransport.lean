/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalRandomTimeAssembly
public import DirectedDistances.RandomWalk.RenewalStoppedHistory

/-! # Actual dependent history tests for positive renewal-rank slices

Internal source-law consumption for Lemma 4.9 (`lem-renewal`), unchanged
dependent whole finite history produces every fixed-prefix test needed by
the actual-law sum; none of those measurability obligations is assumed.
This module does not define source renewal times or assert paper closure. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory

/-- Restriction and pullback along a measurable subtype commute. -/
theorem subtype_comap_restrict_preimage
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (E D : Set α) (hE : MeasurableSet E) :
    (μ.comap (Subtype.val : E → α)).restrict
        ((Subtype.val : E → α) ⁻¹' D) =
      (μ.restrict D).comap (Subtype.val : E → α) :=
  ((MeasurableEmbedding.subtype_coe hE).comap_restrict μ D).symm

/-- A measurable map on a genuine subtype agreeing with an ambient map on
a slice has the same restricted pushforward. No mass assumption is needed.
Integrated from the read-only Codex3 subtype-transport proof proposal. -/
theorem map_subtype_comap_restrict_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (E D : Set α)
    (hE : MeasurableSet E) (hDE : D ⊆ E)
    (f : E → β) (g : α → β)
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x : E, x.val ∈ D → f x = g x.val) :
    ((μ.comap (Subtype.val : E → α)).restrict
        ((Subtype.val : E → α) ⁻¹' D)).map f =
      (μ.restrict D).map g := by
  have he : MeasurableEmbedding (Subtype.val : E → α) :=
    MeasurableEmbedding.subtype_coe hE
  rw [subtype_comap_restrict_preimage μ E D hE]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs,
    he.comap_apply (μ.restrict D),
    Measure.restrict_apply (he.measurableSet_image.mpr (hs.preimage hf)),
    Measure.map_apply hg hs,
    Measure.restrict_apply (hs.preimage hg)]
  have himage :
      ((Subtype.val : E → α) '' (f ⁻¹' s)) ∩ D =
        (g ⁻¹' s) ∩ D := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hxD⟩
      subst x
      change f y ∈ s at hy
      change g y.val ∈ s ∧ y.val ∈ D
      exact ⟨(hfg y hxD) ▸ hy, hxD⟩
    · rintro ⟨hxg, hxD⟩
      refine ⟨⟨⟨x, hDE hxD⟩, ?_, rfl⟩, hxD⟩
      change f ⟨x, hDE hxD⟩ ∈ s
      rw [hfg ⟨x, hDE hxD⟩ hxD]
      exact hxg
  exact congrArg μ himage

end DirectedDistances.Probability

namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- A whole dependent-history test on an actual finite-time slice is exactly
the pullback of its fixed-prefix test on the corresponding extended-time
fiber. This is a carrier identity for any supplied time, with no renewal
or conditional-law assumption. -/
theorem finiteTime_history_slice_preimage
    (T : (ℕ → ℤ × ℤ) → WithTop ℕ)
    (H : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)) (n : ℕ) :
    {ω : {p // T p < ⊤} | finiteTimeIndex T ω = n ∧
      stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val) ω ∈ H} =
      Subtype.val ⁻¹' {p | T p = (n : WithTop ℕ) ∧
        (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
          Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H} := by
  ext ω
  constructor
  · rintro ⟨hn, hH⟩
    refine ⟨(finiteTimeIndex_eq_iff T ω n).mp hn, ?_⟩
    rw [stoppedVectorHistory_eq_of_time _ _ _ n hn] at hH
    exact hH
  · rintro ⟨hn, hH⟩
    have hi := (finiteTimeIndex_eq_iff T ω n).mpr hn
    refine ⟨hi, ?_⟩
    rw [stoppedVectorHistory_eq_of_time _ _ _ n hi]
    exact hH

/-- Transport the actual whole finite-time future and dependent-history test
on one finite slice to the ambient fixed-time future. This is valid for any
measurable extended time and does not assume a stopping-time or reset law. -/
theorem finiteTime_vectorFuture_history_slice_map
    (μ : Measure (ℕ → ℤ × ℤ))
    (T : (ℕ → ℤ × ℤ) → WithTop ℕ) (hT : Measurable T)
    (H : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)) (n : ℕ) :
    ((μ.comap (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ))).restrict
      {ω | finiteTimeIndex T ω = n ∧
        stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val) ω ∈ H}).map
      (stoppedVectorFuture (finiteTimeIndex T) (fun ω => ω.val)) =
    (μ.restrict {p | T p = (n : WithTop ℕ) ∧
      (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
        Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H}).map
      (fun p => fun k => p (n + k) - p n) := by
  rw [finiteTime_history_slice_preimage]
  apply DirectedDistances.Probability.map_subtype_comap_restrict_eq μ
    {p | T p < ⊤}
    {p | T p = (n : WithTop ℕ) ∧
      (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
        Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H}
  · exact hT measurableSet_Iio
  · intro p hp
    change T p < ⊤
    rw [hp.1]
    exact WithTop.coe_lt_top n
  · exact measurable_finiteTime_vectorFuture T (fun p => p) hT measurable_id
  · exact measurable_stoppedVectorFuture (fun _ => n) (fun p => p)
      measurable_const measurable_id
  · intro ω hω
    exact stoppedVectorFuture_eq_of_time _ _ ω n
      ((finiteTimeIndex_eq_iff T ω n).mpr hω.1)

/-- Actual countable rank-slice future law tested against an arbitrary
measurable dependent whole history. Each fixed-prefix test's measurability
is supplied by the actual history carrier producer. -/
theorem conditionedSource_tagged_history_sum
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (m : ℕ) (H : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ))
    (hH : MeasurableSet H) :
    let E : ℕ → Set (ℕ → ℤ × ℤ) := fun n =>
      {p | (⟨n + 1, fun j : Fin (n + 2) => p j.val⟩ :
        Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H} ∩
      ({p | (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
        (((Finset.Icc 1 (n + 1)).filter fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → i ≤ n + 1 → (p j).1 ≤ (p i).1).card = m)} ∩
        {p | ∀ k, (p (n + 1)).1 ≤ (p (n + 1 + k)).1})
    Measure.sum (fun n => (ν.restrict (E n)).map
        (fun p => fun k => p (n + 1 + k) - p (n + 1))) =
      (∑' n, ν (E n)) • ν := by
  exact conditionedSource_renewal_history_sum ν hRN m _
    (fun n => measurableSet_history_test_prefix_comap H hH (n + 1))

end DirectedDistances.RandomWalk
