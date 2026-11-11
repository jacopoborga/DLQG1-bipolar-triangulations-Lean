/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorBarrierJoint
public import DirectedDistances.RandomWalk.ConditionedVectorTrajectory
public import DirectedDistances.RandomWalk.LazySurvivalProbability
import DirectedDistances.RandomWalk.ConditionedVectorPrefixSupport
import DirectedDistances.RandomWalk.ConditionedVectorFactorization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal BigOperators Topology

/-- Return probability bound after time `n` for a law with the source RN identity. -/
theorem conditionedSource_measure_return_le (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ))
    [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (a n : ℕ) :
    ν.real {p | ∃ j, (p (n + j)).1 ≤ (a : ℤ)} ≤
      ((a : ℝ) + 1) / ((x : ℝ) + 1) *
        (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).real
          {w | ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1} := by
  classical
  let U : Measure (Fin n → Fin 3) := Measure.uniformOfFinset Finset.univ
  have : IsProbabilityMeasure U :=
    ⟨by
      rw [Measure.uniformOfFinset_apply]
      simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      exact ENNReal.div_self (by positivity) (by norm_num)⟩
  let S : Set (Fin n → Fin 3) := {w | ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1}
  let F : Set (ℕ → ℤ × ℤ) := {p | ∃ j, (p (n + j)).1 ≤ (a : ℤ)}
  let G : Set (ℕ → ℤ × ℤ) := {p | ∀ j, ((a + 1 : ℕ) : ℤ) ≤ (p (n + j)).1}
  let C (w : Fin n → Fin 3) : Set (ℕ → ℤ × ℤ) :=
    {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w}
  have hF : MeasurableSet F := by
    have : F = ⋃ j : ℕ, {p : ℕ → ℤ × ℤ | (p (n + j)).1 ≤ (a : ℤ)} := by
      ext p; simp [F]
    rw [this]
    exact MeasurableSet.iUnion fun j =>
      measurableSet_le (measurable_pi_apply (n + j)).fst measurable_const
  have hG : MeasurableSet G := by
    have : G = ⋂ j : ℕ, {p : ℕ → ℤ × ℤ | ((a + 1 : ℕ) : ℤ) ≤ (p (n + j)).1} := by
      ext p; simp [G]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le measurable_const (measurable_pi_apply (n + j)).fst
  have hC : ∀ w, MeasurableSet (C w) := fun w =>
    (measurableSet_singleton _).preimage (by fun_prop)
  have hcover : F =ᵐ[ν] ⋃ w : Fin n → Fin 3, C w ∩ F := by
    filter_upwards [conditionedSource_ae_prefix_mem_range x y ν hRN n] with p hp
    apply propext
    constructor
    · intro hpF
      obtain ⟨w, hw⟩ := hp
      exact Set.mem_iUnion.mpr ⟨w, hw.symm, hpF⟩
    · intro hpA
      obtain ⟨w, _, hpF⟩ := Set.mem_iUnion.mp hpA
      exact hpF
  have hdis : Pairwise (Disjoint on fun w => C w ∩ F) := by
    intro w v hwv
    apply Set.disjoint_left.mpr
    rintro p ⟨hcw, _⟩ ⟨hcv, _⟩
    exact hwv (lazyTwoDimensionalPrefix_injective (x : ℤ) y (hcw.symm.trans hcv))
  have hsum : ν.real F = ∑ w : Fin n → Fin 3, ν.real (C w ∩ F) := by
    calc ν.real F = ν.real (⋃ w : Fin n → Fin 3, C w ∩ F) :=
          congrArg ENNReal.toReal (measure_congr hcover)
      _ = _ := measureReal_iUnion_fintype hdis fun w => (hC w).inter hF
  have hUsing : ∀ w : Fin n → Fin 3, U.real {w} = ((3 : ℝ) ^ n)⁻¹ := by
    intro w
    simp only [U, Measure.real, Measure.uniformOfFinset_apply_singleton, Finset.mem_univ,
      ↓reduceIte, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [ENNReal.toReal_inv]
    simp
  have hterm : ∀ w : Fin n → Fin 3, ν.real (C w ∩ F) ≤
      ((a : ℝ) + 1) / ((x : ℝ) + 1) * (if w ∈ S then U.real {w} else 0) := by
    intro w
    have hatom := conditionedSource_prefix_atom x y ν hRN n w
    by_cases hs : w ∈ S
    · simp only [hs, ↓reduceIte, hUsing]
      have hs' : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 := hs
      let X : ℕ := (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1.toNat
      have hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ) :=
        (Int.toNat_of_nonneg (hs' (Fin.last n))).symm
      have hXR : (((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 : ℤ) : ℝ) = (X : ℝ) := by
        rw [hX]; simp
      have hCreal : ν.real (C w) = ((X : ℝ) + 1) / ((x : ℝ) + 1) * ((3 : ℝ) ^ n)⁻¹ := by
        have h1 : ν (C w) = _ := hatom
        rw [Measure.real, h1]
        simp only [hs', implies_true, ↓reduceIte]
        rw [hXR, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_inv]
        simp
      have hxpos : (0 : ℝ) < (x : ℝ) + 1 := by positivity
      by_cases hXa : a + 1 ≤ X
      · have hb := conditionedSource_prefix_inter_future_barrier x y ν hRN n X (a + 1) w hs'
          hXa hX
        change ν.real (C w ∩ G) = _ at hb
        have hsplit : ν.real (C w ∩ F) + ν.real (C w ∩ G) = ν.real (C w) := by
          have hd : Disjoint (C w ∩ F) (C w ∩ G) := by
            apply Set.disjoint_left.mpr
            rintro p ⟨_, ⟨j, hj⟩⟩ ⟨_, hg⟩
            have := hg j
            push_cast at this
            omega
          have hu : (C w ∩ F) ∪ (C w ∩ G) = C w := by
            ext p
            constructor
            · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
            · intro h
              by_cases hpF : p ∈ F
              · exact Or.inl ⟨h, hpF⟩
              · refine Or.inr ⟨h, fun j => ?_⟩
                have : ¬ ∃ j, (p (n + j)).1 ≤ (a : ℤ) := hpF
                push Not at this
                have := this j
                push_cast
                omega
          have := measureReal_union (μ := ν) hd ((hC w).inter hG)
            (measure_ne_top _ _) (measure_ne_top _ _)
          rw [hu] at this
          exact this.symm
        have hcast : (((X - (a + 1) : ℕ) : ℝ)) = (X : ℝ) - a - 1 := by
          rw [Nat.cast_sub hXa]; push_cast; ring
        rw [hcast, hCreal] at hb
        have hXpos : (0 : ℝ) < (X : ℝ) + 1 := by positivity
        have hFeq : ν.real (C w ∩ F) =
            ((a : ℝ) + 1) / ((x : ℝ) + 1) * ((3 : ℝ) ^ n)⁻¹ := by
          have : ν.real (C w ∩ F) = ν.real (C w) - ν.real (C w ∩ G) := by
            linarith
          rw [this, hb, hCreal]
          field_simp
          ring
        exact hFeq.le
      · have hXa' : X ≤ a := by omega
        calc ν.real (C w ∩ F) ≤ ν.real (C w) := measureReal_mono Set.inter_subset_left
          _ = ((X : ℝ) + 1) / ((x : ℝ) + 1) * ((3 : ℝ) ^ n)⁻¹ := hCreal
          _ ≤ ((a : ℝ) + 1) / ((x : ℝ) + 1) * ((3 : ℝ) ^ n)⁻¹ := by
            have : (X : ℝ) ≤ a := by exact_mod_cast hXa'
            gcongr
    · simp only [hs, ↓reduceIte, mul_zero]
      have hs' : ¬ ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 := hs
      have hz : ν (C w) = 0 := by
        have h1 : ν (C w) = _ := hatom
        rw [h1]
        simp only [hs', ↓reduceIte, zero_mul]
      have : ν (C w ∩ F) = 0 := measure_mono_null Set.inter_subset_left hz
      simp [Measure.real, this]
  have hUsum : ∑ w : Fin n → Fin 3, (if w ∈ S then U.real {w} else 0) = U.real S := by
    rw [← Finset.sum_filter]
    have := sum_measureReal_singleton (μ := U) (Finset.univ.filter fun w => w ∈ S)
    rw [this]
    congr 1
    ext w; simp
  calc ν.real F = ∑ w : Fin n → Fin 3, ν.real (C w ∩ F) := hsum
    _ ≤ ∑ w : Fin n → Fin 3,
        ((a : ℝ) + 1) / ((x : ℝ) + 1) * (if w ∈ S then U.real {w} else 0) :=
        Finset.sum_le_sum fun w _ => hterm w
    _ = ((a : ℝ) + 1) / ((x : ℝ) + 1) * U.real S := by
        rw [← Finset.mul_sum, hUsum]

/-- Almost sure divergence of the first coordinate for any law with the source RN identity. -/
theorem conditionedSource_tendsto_fst_atTop (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ))
    [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) :
    ∀ᵐ p ∂ν, Filter.Tendsto (fun j => (p j).1) Filter.atTop Filter.atTop := by
  have hnull : ∀ a : ℕ, ν (⋂ n : ℕ, {p : ℕ → ℤ × ℤ | ∃ j, (p (n + j)).1 ≤ (a : ℤ)}) = 0 := by
    intro a
    have hle : ν.real (⋂ n : ℕ, {p : ℕ → ℤ × ℤ | ∃ j, (p (n + j)).1 ≤ (a : ℤ)}) ≤ 0 := by
      have ht : Tendsto (fun n : ℕ =>
          ((a : ℝ) + 1) / ((x : ℝ) + 1) *
            (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).real
              {w | ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1}) atTop (𝓝 0) := by
        have := (tendsto_uniform_lazyWordSurvives_real x).const_mul
          (((a : ℝ) + 1) / ((x : ℝ) + 1))
        rw [mul_zero] at this
        exact this
      refine le_of_tendsto_of_tendsto' tendsto_const_nhds ht fun n => ?_
      exact (measureReal_mono (Set.iInter_subset _ n)).trans
        (conditionedSource_measure_return_le x y ν hRN a n)
    have h0 : ν.real (⋂ n : ℕ, {p : ℕ → ℤ × ℤ | ∃ j, (p (n + j)).1 ≤ (a : ℤ)}) = 0 :=
      le_antisymm hle measureReal_nonneg
    simpa [Measure.real] using (ENNReal.toReal_eq_zero_iff _ |>.mp h0).resolve_right
      (measure_ne_top _ _)
  have hall : ∀ᵐ p ∂ν, ∀ a : ℕ,
      p ∉ ⋂ n : ℕ, {p : ℕ → ℤ × ℤ | ∃ j, (p (n + j)).1 ≤ (a : ℤ)} :=
    ae_all_iff.mpr fun a => measure_eq_zero_iff_ae_notMem.mp (hnull a)
  filter_upwards [hall] with p hp
  rw [Filter.tendsto_atTop_atTop]
  intro b
  have hp' := hp b.toNat
  simp only [Set.mem_iInter, not_forall] at hp'
  obtain ⟨n, hn⟩ := hp'
  refine ⟨n, fun m hm => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hn
  refine ⟨m - n, ?_⟩
  have : n + (m - n) = m := by omega
  rw [this]
  have := Int.self_le_toNat b
  omega

/-- Almost sure divergence of the first coordinate of the constructed conditioned law. -/
theorem conditionedVectorPathLaw_tendsto_fst_atTop (x : ℕ) (y : ℤ) :
    ∀ᵐ p ∂(conditionedVectorPathLaw x y),
      Filter.Tendsto (fun j => (p j).1) Filter.atTop Filter.atTop :=
  conditionedSource_tendsto_fst_atTop x y (conditionedVectorPathLaw x y)
    (conditionedVectorPathLaw_map_prefix x y)

end DirectedDistances.RandomWalk
