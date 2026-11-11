/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-! # Hoeffding concentration for finite alphabets

A generic finite-alphabet replacement for the Cramér concentration step in
This helper estimates empirical symbol frequencies for iid finite-valued
variables; it is not itself a formalization of the paper's bridge statement. -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

noncomputable section

local instance (priority := 100) classicalDecEq {α : Type*} [Fintype α] : DecidableEq α :=
  Classical.decEq α

/-- For iid finite-alphabet variables, all empirical symbol frequencies are
simultaneously close to their common marginal with Hoeffding's exponential
bound. This is a generic helper for the Cramér step in Lemma 5.18 -/
theorem finiteAlphabetHoeffding
    {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {ν : Measure α} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → α}
    (hX : ∀ s, Measurable (X s)) (hind : iIndepFun X μ)
    (hlaw : ∀ s, μ.map (X s) = ν)
    (L : ℕ) (hL : 0 < L) (δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω | ∃ a : α,
      δ < |(L : ℝ)⁻¹ *
        ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|} ≤
      2 * Fintype.card α * Real.exp (-2 * δ ^ 2 * L) := by
  classical
  let Y : α → ℕ → Ω → ℝ := fun a s ω =>
    (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}
  have hYmeas (a : α) (s : ℕ) : Measurable (Y a s) := by
    have hindicator : Measurable (fun ω : Ω => if X s ω = a then (1 : ℝ) else 0) := by
      exact Measurable.ite (hX s (measurableSet_singleton a)) measurable_const measurable_const
    exact hindicator.sub measurable_const
  have hindY (a : α) : iIndepFun (fun s ω => Y a s ω) μ := by
    have hg : Measurable (fun b : α => (if b = a then (1 : ℝ) else 0) - ν.real {a}) := by
      exact (Measurable.ite (measurableSet_singleton a) measurable_const measurable_const).sub
        measurable_const
    simpa [Y, Function.comp_def] using
      (hind.comp (fun _ : ℕ => fun b : α =>
        (if b = a then (1 : ℝ) else 0) - ν.real {a}) (fun _ => hg))
  have hprob_bounds (a : α) : 0 ≤ ν.real {a} ∧ ν.real {a} ≤ 1 := by
    constructor
    · exact measureReal_nonneg
    · calc
        ν.real {a} ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp
  have hsingle (a : α) (s : ℕ) :
      HasSubgaussianMGF (fun ω => Y a s ω) (1 / 4 : NNReal) μ := by
    let p : ℝ := ν.real {a}
    have hp0 : 0 ≤ p := (hprob_bounds a).1
    have hp1 : p ≤ 1 := (hprob_bounds a).2
    have hs : MeasurableSet {ω : Ω | X s ω = a} := hX s (measurableSet_singleton a)
    have hindicator_eq : (fun ω : Ω => if X s ω = a then (1 : ℝ) else 0) =
        ({ω : Ω | X s ω = a}.indicator fun _ => (1 : ℝ)) := by
      funext ω
      simp [Set.indicator_apply]
    have hindicator_integrable :
        Integrable (fun ω : Ω => if X s ω = a then (1 : ℝ) else 0) μ := by
      rw [hindicator_eq]
      exact (integrable_const (1 : ℝ)).indicator hs
    have hmass : μ.real {ω : Ω | X s ω = a} = p := by
      have hmap := congrArg (fun m : Measure α => m.real {a}) (hlaw s)
      rw [map_measureReal_apply (hX s) (measurableSet_singleton a)] at hmap
      have hsets : X s ⁻¹' ({a} : Set α) = {ω : Ω | X s ω = a} := by
        ext ω
        rfl
      rw [hsets] at hmap
      simpa [p] using hmap
    have hmean : ∫ ω, (if X s ω = a then (1 : ℝ) else 0) ∂μ = p := by
      calc
        ∫ ω, (if X s ω = a then (1 : ℝ) else 0) ∂μ =
            μ.real {ω : Ω | X s ω = a} := by
              simpa [Set.indicator_apply] using (integral_indicator_one (μ := μ) hs)
        _ = p := hmass
    have hzero : ∫ ω, Y a s ω ∂μ = 0 := by
      dsimp [Y]
      rw [integral_sub hindicator_integrable (integrable_const (ν.real {a})), hmean, integral_const]
      have hμuniv : μ.real Set.univ = 1 := by simp [Measure.real]
      rw [hμuniv]
      dsimp [p]
      ring
    have hb : ∀ᵐ ω ∂μ, Y a s ω ∈ Set.Icc (-p) (1 - p) := by
      filter_upwards with ω
      dsimp [Y]
      by_cases h : X s ω = a <;> simp [h] <;> constructor <;> linarith
    have hparam : ((‖(1 - p) - (-p)‖₊ / 2) ^ 2) = (1 / 4 : NNReal) := by
      have hwidth : (1 - p) - (-p) = (1 : ℝ) := by ring
      rw [hwidth]
      apply NNReal.coe_inj.mp
      push_cast
      norm_num
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := fun ω => Y a s ω) (a := -p) (b := 1 - p)
      (hYmeas a s |>.aemeasurable) hb hzero
    rw [hparam] at h
    norm_num at h ⊢
    exact h
  have htail (a : α) :
      μ.real {ω | δ < |(L : ℝ)⁻¹ *
        ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|} ≤
      2 * Real.exp (-2 * δ ^ 2 * L) := by
    let S : Ω → ℝ := fun ω => ∑ s ∈ Finset.range L, Y a s ω
    have hsumId (ω : Ω) :
        S ω = ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) -
          (L : ℝ) * ν.real {a} := by
      simp [S, Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
    have hdev (ω : Ω) :
        (L : ℝ)⁻¹ *
          ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a} =
          (L : ℝ)⁻¹ * S ω := by
      rw [hsumId]
      field_simp
    have hpos :
        μ.real {ω | (L : ℝ) * δ ≤ S ω} ≤ Real.exp (-2 * δ ^ 2 * L) := by
      have hraw := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
        (hindY a) (s := Finset.range L)
        (h_subG := fun s hs => hsingle a s) (ε := (L : ℝ) * δ) (hε := by positivity)
      have htailRaw : μ.real {ω | (L : ℝ) * δ ≤ S ω} ≤
          Real.exp (-((L : ℝ) * δ) ^ 2 /
            (2 * ((L : ℝ) * (4 : ℝ)⁻¹))) := by
        simpa [S] using hraw
      calc
        μ.real {ω | (L : ℝ) * δ ≤ S ω} ≤
            Real.exp (-((L : ℝ) * δ) ^ 2 /
              (2 * ((L : ℝ) * (4 : ℝ)⁻¹))) := htailRaw
        _ = Real.exp (-2 * δ ^ 2 * L) := by
          congr 1
          field_simp
          ring
    have hneg :
        μ.real {ω | (L : ℝ) * δ ≤ -S ω} ≤ Real.exp (-2 * δ ^ 2 * L) := by
      have hraw := (HasSubgaussianMGF.sum_of_iIndepFun (hindY a)
        (s := Finset.range L) (fun s hs => hsingle a s)).neg.measure_ge_le
          (ε := (L : ℝ) * δ) (by positivity)
      have htailRaw : μ.real {ω | (L : ℝ) * δ ≤ -S ω} ≤
          Real.exp (-((L : ℝ) * δ) ^ 2 /
            (2 * ((L : ℝ) * (4 : ℝ)⁻¹))) := by
        simpa [S, Finset.sum_neg_distrib] using hraw
      calc
        μ.real {ω | (L : ℝ) * δ ≤ -S ω} ≤
            Real.exp (-((L : ℝ) * δ) ^ 2 /
              (2 * ((L : ℝ) * (4 : ℝ)⁻¹))) := htailRaw
        _ = Real.exp (-2 * δ ^ 2 * L) := by
          congr 1
          field_simp
          ring
    have hsubset : {ω | δ < |(L : ℝ)⁻¹ *
        ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|} ⊆
        {ω | (L : ℝ) * δ ≤ S ω} ∪ {ω | (L : ℝ) * δ ≤ -S ω} := by
      intro ω hω
      change δ < |(L : ℝ)⁻¹ *
        ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}| at hω
      rw [hdev ω] at hω
      rcases le_total 0 (S ω) with hS | hS
      · left
        have hδ : δ < (L : ℝ)⁻¹ * S ω := by
          simpa [abs_of_nonneg (mul_nonneg (inv_pos.mpr hLpos).le hS)] using hω
        have := mul_lt_mul_of_pos_left hδ hLpos
        have hinv : (L : ℝ) * ((L : ℝ)⁻¹ * S ω) = S ω := by field_simp
        rw [hinv] at this
        exact le_of_lt this
      · right
        have hδ : δ < -((L : ℝ)⁻¹ * S ω) := by
          have habs : |(L : ℝ)⁻¹ * S ω| = -((L : ℝ)⁻¹ * S ω) :=
            abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hLpos).le hS)
          simpa [habs] using hω
        have := mul_lt_mul_of_pos_left hδ hLpos
        have hinv : (L : ℝ) * -((L : ℝ)⁻¹ * S ω) = -S ω := by field_simp
        rw [hinv] at this
        exact le_of_lt this
    calc
      μ.real {ω | δ < |(L : ℝ)⁻¹ *
          ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|} ≤
          μ.real ({ω | (L : ℝ) * δ ≤ S ω} ∪ {ω | (L : ℝ) * δ ≤ -S ω}) :=
            measureReal_mono hsubset
      _ ≤ μ.real {ω | (L : ℝ) * δ ≤ S ω} + μ.real {ω | (L : ℝ) * δ ≤ -S ω} :=
            measureReal_union_le _ _
      _ ≤ Real.exp (-2 * δ ^ 2 * L) + Real.exp (-2 * δ ^ 2 * L) := add_le_add hpos hneg
      _ = 2 * Real.exp (-2 * δ ^ 2 * L) := by ring
  have hmainset :
      {ω | ∃ a : α, δ < |(L : ℝ)⁻¹ *
        ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|} =
      ⋃ a : α, {ω | δ < |(L : ℝ)⁻¹ *
        ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|} := by
    ext ω
    simp
  rw [hmainset]
  calc
    μ.real (⋃ a : α, {ω | δ < |(L : ℝ)⁻¹ *
        ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|}) ≤
        ∑ a : α, μ.real {ω | δ < |(L : ℝ)⁻¹ *
          ∑ s ∈ Finset.range L, (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : α, 2 * Real.exp (-2 * δ ^ 2 * L) :=
      Finset.sum_le_sum fun a _ => htail a
    _ = 2 * Fintype.card α * Real.exp (-2 * δ ^ 2 * L) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

end

end DirectedDistances.Probability
