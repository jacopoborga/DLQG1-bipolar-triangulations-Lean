module

public import DirectedDistances.Probability.SkorokhodJ1WindowCompactness
public import Mathlib.MeasureTheory.Measure.Tight

import Mathlib.Analysis.SpecificLimits.Basic

/-! # Tightness from supremum and modulus bounds on a J1 window

The measurable space is arbitrary: tightness and the outer-measure bounds used here
do not require measurable bad events, a Borel-space instance, or finite measures.
No measurable-space instance is added. The existential bad-supremum event matches
pointwise compactness bounds and can be bounded using a finite sampled maximum. -/

public section
namespace DirectedDistances.Probability

open MeasureTheory Set
open scoped ENNReal Topology

/-- supremum and modulus bounds give uniform compact containment of window measures
(Billingsley 1999, Thm 13.2 sufficiency, window form); not the paper result. -/
theorem exists_compact_window_set_of_sup_modulus
    {T : ℝ} (hT : 0 < T) {ι : Type*} [MeasurableSpace (J1WindowD T hT)]
    (μ : ι → Measure (J1WindowD T hT))
    (hsup : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ i,
      μ i {f | ∃ t, M < |f.path.1 t|} ≤ ENNReal.ofReal ε)
    (hmod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∀ i,
        μ i {f | ε < cadlagModulus (hT := hT) f.path δ} ≤ ENNReal.ofReal η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (J1WindowD T hT), IsCompact K ∧
      ∀ i, μ i Kᶜ ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨M, hM⟩ := hsup (ε / 2) (by positivity)
  have hchoices (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∀ i,
      μ i {f | 1 / (k + 1 : ℝ) < cadlagModulus (hT := hT) f.path δ} ≤
        ENNReal.ofReal (ε / 4 * (1 / 2 : ℝ) ^ k) :=
    hmod (1 / (k + 1 : ℝ)) (by positivity)
      (ε / 4 * (1 / 2 : ℝ) ^ k) (by positivity)
  choose δ hδpos hδT hδ using hchoices
  let A : Set (J1WindowD T hT) := {f | (∀ t, |f.path.1 t| ≤ M) ∧
    ∀ k : ℕ, cadlagModulus (hT := hT) f.path (δ k) ≤ 1 / (k + 1 : ℝ)}
  have hcompact : IsCompact (closure A) := by
    apply isCompact_closure_of_bdd_sup_modulus hT A
    · exact ⟨M, fun f hf => hf.1⟩
    · intro r hr
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
      exact ⟨δ k, hδpos k, hδT k, fun f hf => (hf.2 k).trans hk.le⟩
  have hsum : (∑' k : ℕ, ENNReal.ofReal (ε / 4 * (1 / 2 : ℝ) ^ k)) =
      ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_two.mul_left (ε / 4)), tsum_mul_left, tsum_geometric_two]
    congr 1
    ring
  refine ⟨closure A, hcompact, fun i => ?_⟩
  have hsubset : (closure A)ᶜ ⊆
      {f | ∃ t, M < |f.path.1 t|} ∪
        ⋃ k : ℕ, {f | 1 / (k + 1 : ℝ) <
          cadlagModulus (hT := hT) f.path (δ k)} := by
    intro f hf
    by_cases hs : ∃ t, M < |f.path.1 t|
    · exact Or.inl hs
    · right
      have hnot : f ∉ A := fun h => hf (subset_closure h)
      have hs' : ∀ t, |f.path.1 t| ≤ M := by
        intro t
        exact le_of_not_gt (fun h => hs ⟨t, h⟩)
      have hm : ¬ ∀ k : ℕ,
          cadlagModulus (hT := hT) f.path (δ k) ≤ 1 / (k + 1 : ℝ) :=
        fun h => hnot ⟨hs', h⟩
      obtain ⟨k, hk⟩ := not_forall.mp hm
      exact mem_iUnion.mpr ⟨k, lt_of_not_ge hk⟩
  calc
    μ i (closure A)ᶜ ≤ μ i ({f | ∃ t, M < |f.path.1 t|} ∪
        ⋃ k : ℕ, {f | 1 / (k + 1 : ℝ) <
          cadlagModulus (hT := hT) f.path (δ k)}) := measure_mono hsubset
    _ ≤ μ i {f | ∃ t, M < |f.path.1 t|} +
        μ i (⋃ k : ℕ, {f | 1 / (k + 1 : ℝ) <
          cadlagModulus (hT := hT) f.path (δ k)}) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) +
        ∑' k : ℕ, μ i {f | 1 / (k + 1 : ℝ) <
          cadlagModulus (hT := hT) f.path (δ k)} :=
      add_le_add (hM i) (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal (ε / 2) +
        ∑' k : ℕ, ENNReal.ofReal (ε / 4 * (1 / 2 : ℝ) ^ k) :=
      add_le_add le_rfl (tsum_le_tsum (fun k => hδ k i))
    _ = ENNReal.ofReal ε := by
      rw [hsum, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- supremum and modulus bounds imply tightness of an arbitrarily indexed family
(Billingsley 1999, Thm 13.2 sufficiency, window form); not the paper result. -/
theorem isTightMeasureSet_range_of_sup_modulus
    {T : ℝ} (hT : 0 < T) {ι : Type*} [MeasurableSpace (J1WindowD T hT)]
    (μ : ι → Measure (J1WindowD T hT))
    (hsup : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ i,
      μ i {f | ∃ t, M < |f.path.1 t|} ≤ ENNReal.ofReal ε)
    (hmod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∀ i,
        μ i {f | ε < cadlagModulus (hT := hT) f.path δ} ≤ ENNReal.ofReal η) :
    MeasureTheory.IsTightMeasureSet (Set.range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ => htop ▸ le_top⟩
  · obtain ⟨K, hK, hbound⟩ := exists_compact_window_set_of_sup_modulus hT μ hsup hmod
      (ENNReal.toReal_pos hε.ne' htop)
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (hbound i).trans_eq (ENNReal.ofReal_toReal htop)

end DirectedDistances.Probability
