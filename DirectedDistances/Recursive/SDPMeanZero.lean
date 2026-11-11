module

public import DirectedDistances.Recursive.SDPSideExpansions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Generic first-moment and mean-zero helpers

Generic analysis helpers for the mean-zero clause of `thm-busemann-tail` (vb),
to the Busemann increments remains conditional on the identification of their
laws and on items ind/stationary/sym; no KMSW objects are constructed here. -/

public section
namespace DirectedDistances.Recursive.SDPExpansion

open Filter Asymptotics MeasureTheory Set
open scoped Topology

/-- Generic layer-cake helper for `thm-busemann-tail` (vb),
gives a genuine summable first absolute moment. This is not a paper statement. -/
theorem summable_abs_int_mul_of_tail_isBigO {p : ℤ → ℝ}
    (hp : ∀ y, 0 ≤ p y) (hs : HasSum p 1) {α : ℝ} (hα : 1 < α)
    (htail : (fun R : ℝ => ∑' y : ℤ, if R < |(y : ℝ)| then p y else 0)
      =O[atTop] (fun R : ℝ => R ^ (-α))) :
    Summable (fun y : ℤ => |(y : ℝ)| * p y) := by
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.mp htail
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hbound
  let A : ℝ := max 1 A₀
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let H : ℝ → ℝ := fun R =>
    (Ioc 0 A).indicator (fun _ => (1 : ℝ)) R +
      (Ioi A).indicator (fun R => C * R ^ (-α)) R
  have hH : Integrable H := by
    apply Integrable.add
    · exact (integrableOn_const (s := Ioc (0 : ℝ) A)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
          measurableSet_Ioc
    · have hi : IntegrableOn (fun R : ℝ => C * R ^ (-α)) (Ioi A) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith : -α < -1) hA).const_mul C
      exact hi.integrable_indicator measurableSet_Ioi
  let q : ℤ → ℝ → ℝ := fun y => (Ioo 0 |(y : ℝ)|).indicator (fun _ => p y)
  have hq (y : ℤ) : Integrable (q y) :=
    (integrableOn_const (s := Ioo (0 : ℝ) |(y : ℝ)|)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator
        measurableSet_Ioo
  have hqi (y : ℤ) : (∫ R : ℝ, q y R) = |(y : ℝ)| * p y := by
    dsimp only [q]
    rw [integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le (abs_nonneg _), sub_zero, smul_eq_mul]
  apply summable_of_sum_le (fun y => mul_nonneg (abs_nonneg _) (hp y))
  intro s
  rw [show (∑ y ∈ s, |(y : ℝ)| * p y) = ∫ R : ℝ, ∑ y ∈ s, q y R by
    rw [integral_finsetSum s (fun y _ => hq y)]
    exact Finset.sum_congr rfl (fun y _ => (hqi y).symm)]
  apply integral_mono (integrable_finsetSum s (fun y _ => hq y)) hH
  intro R
  have hHnonneg : 0 ≤ H R := by
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun x hx => mul_nonneg hC.le
        (Real.rpow_nonneg (hA.le.trans (le_of_lt hx)) _)) _)
  by_cases hR : 0 < R
  · have hqeq (y : ℤ) : q y R = if R < |(y : ℝ)| then p y else 0 := by
      simp only [q, indicator_apply, mem_Ioo, hR, true_and]
    simp_rw [hqeq]
    by_cases hRA : R ≤ A
    · have hHR : H R = 1 := by simp [H, hR, hRA, not_lt.mpr hRA]
      rw [hHR]
      calc
        _ ≤ ∑ y ∈ s, p y := Finset.sum_le_sum (fun y _ => by split <;> simp_all)
        _ ≤ ∑' y, p y := hs.summable.sum_le_tsum s (fun y _ => hp y)
        _ = 1 := hs.tsum_eq
    · have hAR : A < R := lt_of_not_ge hRA
      have hHR : H R = C * R ^ (-α) := by simp [H, hR, hRA, hAR]
      rw [hHR]
      have htr : Summable (fun y : ℤ => if R < |(y : ℝ)| then p y else 0) := by
        apply hs.summable.of_nonneg_of_le
        · intro y; split <;> simp_all
        · intro y; split <;> simp_all
      calc
        _ ≤ ∑' y : ℤ, if R < |(y : ℝ)| then p y else 0 :=
          htr.sum_le_tsum s (fun y _ => by split <;> simp_all)
        _ ≤ C * R ^ (-α) := by
          have hb := hA₀ R ((le_max_right 1 A₀).trans hAR.le)
          exact (le_abs_self _).trans (by
            simpa only [Real.norm_eq_abs,
              abs_of_nonneg (Real.rpow_nonneg hR.le _)] using hb)
  · have hz (y : ℤ) : q y R = 0 := by simp [q, not_lt.mp hR]
    simpa only [hz, Finset.sum_const_zero] using hHnonneg

/-- Generic symmetry helper for the mean-zero clause of `thm-busemann-tail` -/
theorem tsum_int_mul_eq_zero_of_symmetric {p : ℤ → ℝ}
    (hsymm : ∀ y, p (-y) = p y) :
    (∑' y : ℤ, (y : ℝ) * p y) = 0 := by
  have h := (Equiv.neg ℤ).tsum_eq (fun y : ℤ => (y : ℝ) * p y)
  simp only [Equiv.neg_apply, Int.cast_neg, hsymm, neg_mul, tsum_neg] at h
  linarith

private theorem tendsto_integer_sine_quotient {p : ℤ → ℝ}
    (hp : ∀ y, 0 ≤ p y)
    (hm : Summable (fun y : ℤ => |(y : ℝ)| * p y)) :
    Tendsto (fun t : ℝ => (∑' y : ℤ, p y * Real.sin ((y : ℝ) * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' y : ℤ, (y : ℝ) * p y)) := by
  have hterm (y : ℤ) : Tendsto
      (fun t : ℝ => p y * Real.sin ((y : ℝ) * t) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 ((y : ℝ) * p y)) := by
    have hd : HasDerivAt (fun t : ℝ => Real.sin ((y : ℝ) * t)) (y : ℝ) 0 := by
      simpa only [id_eq, mul_zero, Real.cos_zero, one_mul, mul_one] using
        (((hasDerivAt_id (0 : ℝ)).const_mul (y : ℝ)).sin)
    simpa only [zero_add, mul_zero, Real.sin_zero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hd.tendsto_slope_zero_right.const_mul (p y)
  have hdom : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ∀ y : ℤ, ‖p y * Real.sin ((y : ℝ) * t) / t‖ ≤ |(y : ℝ)| * p y := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    intro y
    have ht0 : 0 < t := ht
    rw [norm_div, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp y),
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht0]
    apply (div_le_iff₀ ht0).2
    have hb := Real.abs_sin_le_abs (x := (y : ℝ) * t)
    rw [abs_mul, abs_of_pos ht0] at hb
    exact (mul_le_mul_of_nonneg_left hb (hp y)).trans_eq (by ring)
  simpa only [tsum_div_const] using tendsto_tsum_of_dominated_convergence hm hterm hdom

/-- Generic characteristic-function helper for `thm-busemann-tail` (vb),
right linear coefficient force the actual integer mean to vanish. Application
to Busemann increments remains conditional on ind/stationary/sym. -/
theorem tsum_int_mul_eq_zero_of_sdpCF_isLittleO {p : ℤ → ℝ}
    (hp : ∀ y, 0 ≤ p y) (hs : HasSum p 1)
    (hsupp : ∀ y : ℤ, y < -1 → p y = 0)
    (hm : Summable (fun y : ℤ => |(y : ℝ)| * p y))
    (hcf : (fun t : ℝ => sdpCF p t - 1) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (t : ℂ))) :
    (∑' y : ℤ, (y : ℝ) * p y) = 0 := by
  have hseries (t : ℝ) : Summable (fun y : {y : ℤ // -1 ≤ y} =>
      (p y : ℂ) * Complex.exp ((((t * (y : ℝ) : ℝ) : ℂ) * Complex.I))) := by
    apply (hs.summable.subtype (fun y : ℤ => -1 ≤ y)).of_norm_bounded
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp y),
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact le_rfl
  have him (t : ℝ) : (sdpCF p t).im = ∑' y : ℤ, p y * Real.sin ((y : ℝ) * t) := by
    unfold sdpCF
    rw [Complex.im_tsum (hseries t)]
    have hterm (y : {y : ℤ // -1 ≤ y}) :
        ((p y : ℂ) * Complex.exp ((((t * (y : ℝ) : ℝ) : ℂ) * Complex.I))).im =
          p y * Real.sin ((y : ℝ) * t) := by
      simp [Complex.mul_im, Complex.exp_im, mul_comm]
    simp_rw [hterm]
    apply tsum_subtype_eq_of_support_subset
      (f := fun y : ℤ => p y * Real.sin ((y : ℝ) * t)) (s := {y : ℤ | -1 ≤ y})
    intro y hy
    by_contra h
    have hz := hsupp y (lt_of_not_ge h)
    exact hy (by simp [hz])
  have hzero := Complex.continuous_im.continuousAt.tendsto.comp
    hcf.tendsto_div_nhds_zero
  have hzero' : Tendsto
      (fun t : ℝ => (∑' y : ℤ, p y * Real.sin ((y : ℝ) * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, Complex.div_ofReal_im, Complex.sub_im, Complex.one_im,
      sub_zero, him, Complex.zero_im] using hzero
  exact tendsto_nhds_unique (tendsto_integer_sine_quotient hp hm) hzero'

/-- Generic scale helper for `thm-busemann-tail` (vb),
than one is little-o of the linear scale. Not a paper statement. -/
theorem ofReal_rpow_isLittleO_linear {α : ℝ} (hα : 1 < α) :
    (fun t : ℝ => ((t ^ α : ℝ) : ℂ)) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (t : ℂ)) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun h => False.elim ((Complex.ofReal_ne_zero.mpr (ne_of_gt ht)) h)
  · have hpow : Tendsto (fun t : ℝ => t ^ (α - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 (α - 1)
        (Or.inr (by linarith))).tendsto.mono_left
          (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
      simpa only [Real.zero_rpow (by linarith : α - 1 ≠ 0)] using h
    apply (Complex.continuous_ofReal.continuousAt.tendsto.comp hpow).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_def]
    rw [← Complex.ofReal_div, Real.rpow_sub (show 0 < t from ht), Real.rpow_one]

/-- Generic expansion helper for `thm-busemann-tail` (vb),
has zero linear coefficient. Not a paper statement. -/
theorem sdpCF_isLittleO_linear_of_expansion {p : ℤ → ℝ} {c : ℂ} {α : ℝ}
    (hα : 1 < α)
    (hexp : (fun t : ℝ => sdpCF p t - 1 - c * ((t ^ α : ℝ) : ℂ))
      =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ α : ℝ) : ℂ))) :
    (fun t : ℝ => sdpCF p t - 1) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (t : ℂ)) := by
  have hpow := ofReal_rpow_isLittleO_linear hα
  simpa only [sub_add_cancel] using (hexp.trans hpow).add (hpow.const_mul_left c)

/-- Generic tail-expansion helper for `thm-busemann-tail` (vb),
the big-O tail bound, including a zero leading coefficient. Not a paper statement. -/
theorem tail_isBigO_of_expansion {T : ℝ → ℝ} {C α : ℝ}
    (hexp : (fun R : ℝ => T R - C * R ^ (-α))
      =o[atTop] (fun R : ℝ => R ^ (-α))) :
    T =O[atTop] (fun R : ℝ => R ^ (-α)) := by
  simpa only [sub_add_cancel] using
    hexp.isBigO.add (isBigO_const_mul_self C (fun R : ℝ => R ^ (-α)) atTop)

/-- Generic support bridge for `thm-busemann-tail` (vb),
tail equals the absolute tail for `R ≥ 1`. Thus the source's one-sided tail
bound also gives a genuine first absolute moment. Not a paper statement. -/
theorem summable_abs_int_mul_of_one_sided_tail_isBigO {p : ℤ → ℝ}
    (hp : ∀ y, 0 ≤ p y) (hs : HasSum p 1)
    (hsupp : ∀ y : ℤ, y < -1 → p y = 0) {α : ℝ} (hα : 1 < α)
    (htail : (fun R : ℝ => ∑' y : ℤ, if R < (y : ℝ) then p y else 0)
      =O[atTop] (fun R : ℝ => R ^ (-α))) :
    Summable (fun y : ℤ => |(y : ℝ)| * p y) := by
  apply summable_abs_int_mul_of_tail_isBigO hp hs hα
  apply htail.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  apply tsum_congr
  intro y
  by_cases hy : y < -1
  · simp only [hsupp y hy, ite_self]
  · have hyR : (-1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_of_not_gt hy
    by_cases hyn : 0 ≤ (y : ℝ)
    · rw [abs_of_nonneg hyn]
    · have hyneg : (y : ℝ) < 0 := lt_of_not_ge hyn
      have habs : |(y : ℝ)| ≤ R := by rw [abs_of_neg hyneg]; linarith
      have hle : (y : ℝ) ≤ R := by linarith
      simp only [not_lt.mpr hle, not_lt.mpr habs, ite_false]

/-- Generic assembly for the mean-zero clause of `thm-busemann-tail` (vb),
characteristic expansions give both an actual first absolute moment and zero
mean. Not a paper statement; application to Busemann increments is conditional
on their law identification and items ind/stationary/sym. -/
theorem first_moment_and_mean_zero_of_sdp_expansions {p : ℤ → ℝ}
    (hp : ∀ y, 0 ≤ p y) (hs : HasSum p 1)
    (hsupp : ∀ y : ℤ, y < -1 → p y = 0) {α : ℝ} (hα : 1 < α)
    {C : ℝ} {c : ℂ}
    (htail : (fun R : ℝ =>
      (∑' y : ℤ, if R < (y : ℝ) then p y else 0) - C * R ^ (-α))
      =o[atTop] (fun R : ℝ => R ^ (-α)))
    (hcf : (fun t : ℝ => sdpCF p t - 1 - c * ((t ^ α : ℝ) : ℂ))
      =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ α : ℝ) : ℂ))) :
    Summable (fun y : ℤ => |(y : ℝ)| * p y) ∧
      (∑' y : ℤ, (y : ℝ) * p y) = 0 := by
  have hm := summable_abs_int_mul_of_one_sided_tail_isBigO hp hs hsupp hα
    (tail_isBigO_of_expansion htail)
  exact ⟨hm, tsum_int_mul_eq_zero_of_sdpCF_isLittleO hp hs hsupp hm
    (sdpCF_isLittleO_linear_of_expansion hα hcf)⟩

end DirectedDistances.Recursive.SDPExpansion
