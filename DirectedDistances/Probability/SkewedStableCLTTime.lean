module

public import DirectedDistances.Probability.SkewedStableCLT
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- A complex power limit with an asymptotically proportional natural exponent. -/
theorem tendsto_pow_exp_of_tendsto_natCast_mul_sub_one
    {z : ℕ → ℂ} {m : ℕ → ℕ} {a : ℂ} {s : ℝ}
    (hz : Tendsto (fun n : ℕ ↦ (n : ℂ) * (z n - 1)) atTop (𝓝 a))
    (hm : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto (fun n ↦ z n ^ m n) atTop (𝓝 (Complex.exp ((s : ℂ) * a))) := by
  have hi : Tendsto (fun n : ℕ ↦ ((n : ℂ)⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).ofReal
  have hw : Tendsto (fun n ↦ z n - 1) atTop (𝓝 0) := by
    have hmul : Tendsto (fun n : ℕ ↦ (n : ℂ) * (z n - 1) * (n : ℂ)⁻¹)
        atTop (𝓝 0) := by simpa using hz.mul hi
    apply hmul.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp [Nat.cast_ne_zero.mpr hn]
  have hz1 : Tendsto z atTop (𝓝 1) := by
    simpa using hw.add_const 1
  have hl : Tendsto (fun n : ℕ ↦ (n : ℂ) * Complex.log (z n)) atTop (𝓝 a) := by
    simpa using Complex.tendsto_nat_mul_log_one_add_of_tendsto hz
  have hml : Tendsto (fun n ↦ (m n : ℂ) * Complex.log (z n))
      atTop (𝓝 ((s : ℂ) * a)) := by
    apply (hm.ofReal.mul hl).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hn]
  apply ((Complex.continuous_exp.tendsto _).comp hml).congr'
  filter_upwards [hz1.eventually_ne one_ne_zero] with n hn
  dsimp only [Function.comp_apply]
  rw [Complex.exp_nat_mul, Complex.exp_log hn]

private theorem tendsto_charFun_skewStable_natCast_mul_sub_one
    {μ : Measure ℝ} {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun μ t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℂ) *
      (charFun μ ((n : ℝ) ^ (-1 / ν) * t) - 1))
      atTop (𝓝 (-((if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))) := by
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
  have hn : (fun n : ℕ ↦ ‖(1 / (n : ℂ))‖) =
      (fun n : ℕ ↦ ‖(1 / (n : ℝ))‖) := by simp
  have hf : (fun n : ℕ ↦ charFun μ ((n : ℝ) ^ (-1 / ν) * t) -
      (1 + (-((if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ))) / n)) =o[atTop]
      (fun n : ℕ ↦ 1 / (n : ℂ)) := by
    rw [← Asymptotics.isLittleO_norm_right, hn, Asymptotics.isLittleO_norm_right]
    exact he'.of_const_mul_right
  apply tendsto_sub_nhds_zero_iff.mp
  apply hf.tendsto_inv_smul_nhds_zero.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn0
  simp only [one_div, inv_inv, smul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hn0]
  ring


/-- Scalar helper toward E-STABLE / thm-busemann-conv
normalized iid partial sums at time s; no joint finite-dimensional or functional
convergence, tightness of paths or Busemann law identification is claimed;
not the paper result. -/
theorem tendsto_charFun_skewStable_sum_floor {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun
      (P.map (fun ω ↦ (n : ℝ) ^ (-1 / ν) *
        ∑ k ∈ Finset.range ⌊(n : ℝ) * s⌋₊, X k ω)) θ)
      atTop (𝓝 (Complex.exp (-((s : ℂ) *
        ((if 0 ≤ θ then κp else κm) * (|θ| ^ ν : ℝ)))))) := by
  simp_rw [charFun_mul_sum hindep hident]
  have hm : Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * s⌋₊ : ℝ) / n)
      atTop (𝓝 s) := by
    simpa only [Function.comp_def, mul_comm] using
      (tendsto_nat_floor_mul_div_atTop hs).comp tendsto_natCast_atTop_atTop
  simpa only [mul_neg] using tendsto_pow_exp_of_tendsto_natCast_mul_sub_one
    (tendsto_charFun_skewStable_natCast_mul_sub_one hν hexp θ) hm

private theorem charFun_mul_finset_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (a θ : ℝ) (I : Finset ℕ) :
    charFun (P.map (fun ω ↦ a * ∑ k ∈ I, X k ω)) θ =
      charFun (P.map (X 0)) (a * θ) ^ I.card := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp,
    (hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ ↦ mX _)]
  · simp [fun i ↦ (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ mX _

/-- Scalar helper toward E-STABLE / thm-busemann-conv
normalized iid partial sums over a time block; no joint finite-dimensional or
functional convergence, tightness of paths or Busemann law identification is claimed;
not the paper result. -/
theorem tendsto_charFun_skewStable_sum_block {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (θ : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun
      (P.map (fun ω ↦ (n : ℝ) ^ (-1 / ν) *
        ∑ k ∈ Finset.Ico ⌊(n : ℝ) * s⌋₊ ⌊(n : ℝ) * t⌋₊, X k ω)) θ)
      atTop (𝓝 (Complex.exp (-(((t - s : ℝ) : ℂ) *
        ((if 0 ≤ θ then κp else κm) * (|θ| ^ ν : ℝ)))))) := by
  simp_rw [charFun_mul_finset_sum hindep hident, Nat.card_Ico]
  have hfloor (u : ℝ) (hu : 0 ≤ u) :
      Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * u⌋₊ : ℝ) / n) atTop (𝓝 u) := by
    simpa only [Function.comp_def, mul_comm] using
      (tendsto_nat_floor_mul_div_atTop hu).comp tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ ↦
      ((⌊(n : ℝ) * t⌋₊ - ⌊(n : ℝ) * s⌋₊ : ℕ) : ℝ) / n)
      atTop (𝓝 (t - s)) := by
    apply ((hfloor t (hs.trans hst)).sub (hfloor s hs)).congr
    intro n
    rw [Nat.cast_sub (Nat.floor_mono (mul_le_mul_of_nonneg_left hst
      (Nat.cast_nonneg n))), sub_div]
  simpa only [mul_neg] using tendsto_pow_exp_of_tendsto_natCast_mul_sub_one
    (tendsto_charFun_skewStable_natCast_mul_sub_one hν hexp θ) hm

end DirectedDistances.Probability
