module

public import DirectedDistances.Probability.StableCLT
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Scalar helper toward E-STABLE / thm-busemann-conv
sign-dependent complex characteristic-function expansion; no functional convergence,
tightness of paths or Busemann law identification is claimed; not the paper result. -/
theorem tendsto_charFun_skewStable_pow {μ : Measure ℝ} {κp κm : ℂ} {ν : ℝ}
    (hν : 0 < ν)
    (hexp : (fun t ↦ charFun μ t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun μ ((n : ℝ) ^ (-1 / ν) * t) ^ n)
      atTop (𝓝 (Complex.exp (-((if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ))))) := by
  have hscale (n : ℕ) : |(n : ℝ) ^ (-1 / ν) * t| ^ ν = |t| ^ ν / n := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
      Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_nonneg t),
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    rw [div_mul_cancel₀ _ hν.ne', Real.rpow_neg_one]
    ring
  have hs : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-1 / ν) * t) atTop (𝓝 0) := by
    simpa only [neg_div, one_div, zero_mul, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (inv_pos.mpr hν)).comp
        tendsto_natCast_atTop_atTop).mul_const t
  have he := hexp.comp_tendsto hs
  have he' : (fun n : ℕ ↦ charFun μ ((n : ℝ) ^ (-1 / ν) * t) -
      (1 + (-((if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ))) / n)) =o[atTop]
      (fun n : ℕ ↦ |t| ^ ν * (1 / (n : ℝ))) := by
    apply he.congr'
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
      dsimp only [Function.comp_apply]
      simp only [mul_nonneg_iff_of_pos_left (Real.rpow_pos_of_pos hnpos _), hscale]
      push_cast
      ring
    · apply Eventually.of_forall
      intro n
      dsimp only [Function.comp_apply]
      rw [hscale]
      ring
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
  have hn : (fun n : ℕ ↦ ‖(1 / (n : ℂ))‖) =
      (fun n : ℕ ↦ ‖(1 / (n : ℝ))‖) := by simp
  rw [← Asymptotics.isLittleO_norm_right, hn, Asymptotics.isLittleO_norm_right]
  exact he'.of_const_mul_right

/-- Scalar helper toward E-STABLE / thm-busemann-conv
sign-dependent complex characteristic-function expansion; no functional convergence,
tightness of paths or Busemann law identification is claimed; not the paper result. -/
theorem tendsto_charFun_skewStable_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun
      (P.map (fun ω ↦ (n : ℝ) ^ (-1 / ν) * ∑ k ∈ Finset.range n, X k ω)) t)
      atTop (𝓝 (Complex.exp (-((if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ))))) := by
  simp_rw [charFun_mul_sum hindep hident]
  exact tendsto_charFun_skewStable_pow hν hexp t

/-- Scalar helper toward E-STABLE / thm-busemann-conv
sign-dependent complex characteristic-function expansion; no functional convergence,
tightness of paths or Busemann law identification is claimed; not the paper result. -/
theorem exists_skewStableLaw_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {κp κm : ℂ} {ν : ℝ} (hκ : 0 < κp.re ∧ 0 < κm.re) (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) :
    ∃ stableLaw : ProbabilityMeasure ℝ,
      (∀ t, charFun stableLaw t =
        Complex.exp (-((if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))) ∧
      TendstoInDistribution
        (fun n : ℕ ↦ fun ω ↦ (n : ℝ) ^ (-1 / ν) * ∑ k ∈ Finset.range n, X k ω)
        atTop (fun x : ℝ ↦ x) (fun _ ↦ P) (stableLaw : Measure ℝ) ∧
      (∀ x, (stableLaw : Measure ℝ) ≠ Measure.dirac x) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun n ↦
    ⟨P.map (fun ω ↦ (n : ℝ) ^ (-1 / ν) * ∑ k ∈ Finset.range n, X k ω),
      inferInstance⟩
  have hf : ContinuousAt (fun t : ℝ ↦
      Complex.exp (-((if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))) 0 := by
    have hp : Continuous (fun t : ℝ ↦ |t| ^ ν) :=
      (Real.continuous_rpow_const hν.le).comp continuous_abs
    have hp0 : Tendsto (fun t : ℝ ↦ ((|t| ^ ν : ℝ) : ℂ)) (𝓝 0) (𝓝 0) := by
      simpa only [Function.comp_def, abs_zero, Real.zero_rpow hν.ne',
        Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto _).comp (hp.tendsto 0)
    have hb (κ : ℂ) : Tendsto (fun t : ℝ ↦ Complex.exp (-(κ * (|t| ^ ν : ℝ))))
        (𝓝 0) (𝓝 1) := by
      simpa only [Function.comp_def, mul_zero, neg_zero, Complex.exp_zero] using
        (Complex.continuous_exp.tendsto _).comp (hp0.const_mul κ).neg
    change Tendsto _ (𝓝 0) _
    simp only [abs_zero, Real.zero_rpow hν.ne', Complex.ofReal_zero, mul_zero,
      neg_zero, Complex.exp_zero]
    convert (hb κp).if' (p := fun t : ℝ ↦ 0 ≤ t) (hb κm) using 1
    funext t
    split_ifs <;> rfl
  obtain ⟨stableLaw, hLaw, -⟩ := existsUnique_probabilityMeasure_of_tendsto_charFun μ hf
    (tendsto_charFun_skewStable_sum hindep hident hν hexp)
  have hcf : ∀ t, charFun stableLaw t =
      Complex.exp (-((if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ))) := congrFun hLaw.1
  refine ⟨stableLaw, hcf, ?_, ?_⟩
  · apply TendstoInDistribution.of_tendsto_charFun (fun n ↦ ?_) (by fun_prop)
    · intro t
      simpa only [Measure.map_id', hcf] using
        tendsto_charFun_skewStable_sum hindep hident hν hexp t
    · exact (Measurable.const_mul
        (Finset.measurable_fun_sum _ (fun k _ ↦ hX k)) _).aemeasurable
  · intro x hx
    have hnorm : ‖charFun stableLaw (1 : ℝ)‖ < 1 := by
      rw [hcf]
      simpa only [zero_le_one, ite_true, abs_one, Real.one_rpow, Complex.ofReal_one,
        mul_one, Complex.norm_exp, Complex.neg_re] using
        Real.exp_lt_one_iff.mpr (neg_neg_of_pos hκ.1)
    rw [hx, charFun_dirac, Complex.norm_exp_ofReal_mul_I] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm

end DirectedDistances.Probability
