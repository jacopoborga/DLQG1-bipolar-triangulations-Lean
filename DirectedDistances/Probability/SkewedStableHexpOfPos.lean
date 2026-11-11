module

public import DirectedDistances.Probability.SkewedStableCLT
import Mathlib.Topology.Order.LeftRight

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology





theorem skewStable_hexp_of_pos_expansion {φ : ℝ → ℂ} {κp : ℂ} {ν : ℝ}
    (hν : 0 < ν) (hφ0 : φ 0 = 1) (hconj : ∀ t, φ (-t) = star (φ t))
    (hpos : (fun t : ℝ ↦ φ t - (1 - κp * ((t ^ ν : ℝ) : ℂ)))
      =o[𝓝[>] 0] (fun t : ℝ ↦ t ^ ν)) :
    (fun t : ℝ ↦ φ t -
      (1 - (if 0 ≤ t then κp else star κp) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t : ℝ ↦ |t| ^ ν) := by
  let f : ℝ → ℂ := fun t ↦ φ t -
    (1 - (if 0 ≤ t then κp else star κp) * (|t| ^ ν : ℝ))
  change f =o[𝓝 0] (fun t : ℝ ↦ |t| ^ ν)
  have hr : f =o[𝓝[>] 0] (fun t : ℝ ↦ |t| ^ ν) := by
    apply hpos.congr'
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      change 0 < t at ht
      simp only [f, ite_eq_left ht.le, abs_of_pos ht]
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      change 0 < t at ht
      rw [abs_of_pos ht]
  have hnmap : Tendsto (fun t : ℝ ↦ -t) (𝓝[<] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [neg_zero] using
        (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      change t < 0 at ht
      exact neg_pos.mpr ht
  have hl : f =o[𝓝[<] 0] (fun t : ℝ ↦ |t| ^ ν) := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    filter_upwards [(hpos.comp_tendsto hnmap).bound hc,
      eventually_mem_nhdsWithin] with t ht hlt
    change t < 0 at hlt
    have heq : f t = star (φ (-t) - (1 - κp * (((-t) ^ ν : ℝ) : ℂ))) := by
      dsimp only [f]
      rw [ite_eq_right (not_le_of_gt hlt), abs_of_neg hlt, star_sub, star_sub,
        star_one, star_mul', ← hconj (-t), neg_neg]
      simp only [Complex.star_def, Complex.conj_ofReal]
    simpa only [Function.comp_apply, heq, norm_star, abs_of_neg hlt] using ht
  have hz : f =o[pure 0] (fun t : ℝ ↦ |t| ^ ν) := by
    apply Asymptotics.isLittleO_pure.mpr
    simp only [f, hφ0, abs_zero, Real.zero_rpow hν.ne', Complex.ofReal_zero,
      mul_zero, sub_zero, sub_self]
  rw [← nhdsLT_sup_nhdsGE (0 : ℝ)]
  apply hl.sup
  rw [← nhdsGT_sup_nhdsWithin_singleton, nhdsWithin_singleton]
  exact hr.sup hz





theorem charFun_hexp_of_pos_expansion {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {κp : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hpos : (fun t : ℝ ↦ charFun μ t - (1 - κp * ((t ^ ν : ℝ) : ℂ)))
      =o[𝓝[>] 0] (fun t : ℝ ↦ t ^ ν)) :
    (fun t : ℝ ↦ charFun μ t -
      (1 - (if 0 ≤ t then κp else star κp) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t : ℝ ↦ |t| ^ ν) := by
  apply skewStable_hexp_of_pos_expansion hν (by simp) (fun t ↦ charFun_neg t) hpos





theorem tendsto_charFun_skewStable_sum_of_pos_expansion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {κp : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hpos : (fun t : ℝ ↦ charFun (P.map (X 0)) t -
      (1 - κp * ((t ^ ν : ℝ) : ℂ))) =o[𝓝[>] 0] (fun t : ℝ ↦ t ^ ν)) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun
      (P.map (fun ω ↦ (n : ℝ) ^ (-1 / ν) * ∑ k ∈ Finset.range n, X k ω)) t)
      atTop (𝓝 (Complex.exp (-((if 0 ≤ t then κp else star κp) * (|t| ^ ν : ℝ))))) := by
  have : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hident 0).aemeasurable_fst).mpr inferInstance
  exact tendsto_charFun_skewStable_sum hindep hident hν
    (charFun_hexp_of_pos_expansion hν hpos) t

end DirectedDistances.Probability
