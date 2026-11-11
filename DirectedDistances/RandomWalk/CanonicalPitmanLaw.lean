/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.IIDPitmanProcess

/-! Supporting lemmas for paper labels `lem-lazy-walk-flip` (see CORRESPONDENCE.md). -/











public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal
/-- Every actual source path has the genuine original global-prefix mass 3^(-n). -/
theorem canonicalLazyWalk_prefix_pointmass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) :
    ∀ (n : ℕ) (q : LazyPath n),
    μ {ω | (fun j : Fin (n + 1) => globalIIDLazyWalk ξ ω j.val) = q.val} =
      ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  intro n q
  have hevent : {ω | (fun j : Fin (n + 1) => globalIIDLazyWalk ξ ω j.val) = q.val} =
      {ω | lazyIIDPrefix ξ n ω = q} := by
    ext ω
    have hc : (lazyIIDPrefix ξ n ω).val =
        fun j : Fin (n + 1) => globalIIDLazyWalk ξ ω j.val :=
      funext (lazyIIDPrefix_apply ξ n ω)
    change (fun j : Fin (n + 1) => globalIIDLazyWalk ξ ω j.val) = q.val ↔
      lazyIIDPrefix ξ n ω = q
    rw [← hc]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hevent]
  simpa only [one_div, ENNReal.inv_pow] using measure_lazyIIDPrefix hξ hind hlaw n q

/-- Every actual transformed global-prefix mass has the source endpoint weight
on the nonnegative event, and vanishes outside it. -/
theorem canonicalPitman_prefix_pointmass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) :
    ∀ (n : ℕ) (q : LazyPath n),
    μ {ω | (fun j : Fin (n + 1) => globalLazyPhi (globalIIDLazyWalk ξ ω) j.val) = q.val} =
      if ∀ j : Fin (n + 1), 0 ≤ q.val j then
        (((q.val (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) * ((3 : ℝ≥0∞) ^ n)⁻¹ else 0 := by
  intro n q
  have hevent :
      {ω | (fun j : Fin (n + 1) => globalLazyPhi (globalIIDLazyWalk ξ ω) j.val) = q.val} =
        {ω | pitmanIIDPrefix ξ n ω = q} := by
    ext ω
    have hc : (pitmanIIDPrefix ξ n ω).val =
        fun j : Fin (n + 1) => globalLazyPhi (globalIIDLazyWalk ξ ω) j.val :=
      funext (pitmanIIDPrefix_apply_global ξ n ω)
    change (fun j : Fin (n + 1) => globalLazyPhi (globalIIDLazyWalk ξ ω) j.val) = q.val ↔
      pitmanIIDPrefix ξ n ω = q
    rw [← hc]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hevent]
  simpa only [one_div, ENNReal.inv_pow, ite_mul, zero_mul] using
    measure_pitmanIIDPrefix hξ hind hlaw n q

/-- The actual globally transformed canonical path starts at zero, stays
nonnegative and has legal lazy increments, for every sample path. -/
theorem canonicalPitman_path_properties {Ω : Type*} (ξ : ℕ → Ω → Fin 3) (ω : Ω) :
    globalLazyPhi (globalIIDLazyWalk ξ ω) 0 = 0 ∧
      (∀ j : ℕ, 0 ≤ globalLazyPhi (globalIIDLazyWalk ξ ω) j) ∧
      (∀ j : ℕ, globalLazyPhi (globalIIDLazyWalk ξ ω) (j + 1) -
        globalLazyPhi (globalIIDLazyWalk ξ ω) j ∈ ({-1, 0, 1} : Set ℤ)) := by
  have hstart := globalIIDLazyWalk_zero ξ ω
  refine ⟨?_, globalLazyPhi_nonneg_of_start_zero _ hstart, ?_⟩
  · rw [globalLazyPhi_zero, hstart]
    rfl
  · apply globalLazyPhi_step_of_legal_steps _ hstart
    intro j
    rw [globalIIDLazyWalk_step]
    apply lazy_increment_iff.mpr
    have hcode := (ξ j ω).isLt
    constructor <;> omega
end DirectedDistances.RandomWalk
