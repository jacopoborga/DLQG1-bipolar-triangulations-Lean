module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.MeasureTheory.Integral.Bochner.Set







public section
namespace DirectedDistances.Probability

open MeasureTheory
open Filter
open scoped ENNReal




theorem integral_posPart_eq_half_integral_abs_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 1 μ) (hmean : ∫ ω, X ω ∂μ = 0) :
    ∫ ω, (X ω)⁺ ∂μ = (∫ ω, |X ω| ∂μ) / 2 := by
  have h := integral_abs_eq_two_mul_integral_posPart_sub_integral (f := X)
    (memLp_one_iff_integrable.mp hX)
  rw [hmean] at h
  linarith




theorem integral_abs_moment_sq_ge_second_moment_cube_div_fourth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 4 μ)
    (h4 : 0 < ∫ ω, X ω ^ 4 ∂μ) :
    (∫ ω, |X ω| ∂μ) ^ 2 ≥
      (∫ ω, X ω ^ 2 ∂μ) ^ 3 / (8 * ∫ ω, X ω ^ 4 ∂μ) := by
  let m1 : ℝ := ∫ ω, |X ω| ∂μ
  let m2 : ℝ := ∫ ω, X ω ^ 2 ∂μ
  let m4 : ℝ := ∫ ω, X ω ^ 4 ∂μ
  have hX1 : MemLp X 1 μ := hX.mono_exponent (by norm_num)
  have hX2 : MemLp X 2 μ := hX.mono_exponent (by norm_num)
  have hAbs : Integrable (fun ω => |X ω|) μ := by
    simpa [Real.norm_eq_abs] using hX1.integrable_norm_rpow'
  have hSq : Integrable (fun ω => X ω ^ 2) μ := by
    simpa [Real.norm_eq_abs, abs_sq] using hX2.integrable_norm_rpow'
  have hFourthAbs : Integrable (fun ω => |X ω| ^ 4) μ := by
    simpa [Real.norm_eq_abs] using hX.integrable_norm_rpow'
  have hFourth : Integrable (fun ω => X ω ^ 4) μ :=
    hFourthAbs.congr (Eventually.of_forall fun ω => by
      exact pow_abs_two_mul (X ω) (n := 2))
  have hpoint (s : ℝ) (hs : 0 < s) (ω : Ω) :
      X ω ^ 2 ≤ s * |X ω| + X ω ^ 4 / s ^ 2 := by
    let y := |X ω|
    have hy : 0 ≤ y := abs_nonneg _
    by_cases hys : y ≤ s
    · have hsmall : y ^ 2 ≤ s * y := by
        nlinarith [mul_nonneg hy (sub_nonneg.mpr hys)]
      calc
        X ω ^ 2 = y ^ 2 := by simp [y]
        _ ≤ s * y := hsmall
        _ ≤ s * y + X ω ^ 4 / s ^ 2 := le_add_of_nonneg_right (by positivity)
    · have hsy : s < y := lt_of_not_ge hys
      have hsq : s ^ 2 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - s)]
      have hmul : y ^ 2 * s ^ 2 ≤ y ^ 4 := by
        calc
          y ^ 2 * s ^ 2 ≤ y ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg y)
          _ = y ^ 4 := by ring
      have hdiv : y ^ 2 ≤ y ^ 4 / s ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hs)).2 hmul
      calc
        X ω ^ 2 = y ^ 2 := by simp [y]
        _ ≤ y ^ 4 / s ^ 2 := hdiv
        _ = X ω ^ 4 / s ^ 2 := by
          exact congrArg (fun z : ℝ => z / s ^ 2)
            (pow_abs_two_mul (X ω) (n := 2))
        _ ≤ s * |X ω| + X ω ^ 4 / s ^ 2 := le_add_of_nonneg_left (by positivity)
  have hIneq (s : ℝ) (hs : 0 < s) : m2 ≤ s * m1 + m4 / s ^ 2 := by
    have hR : Integrable (fun ω => s * |X ω| + X ω ^ 4 / s ^ 2) μ :=
      (hAbs.const_mul s).add (hFourth.div_const (s ^ 2))
    have hi := integral_mono hSq hR (hpoint s hs)
    rw [integral_add (hAbs.const_mul s) (hFourth.div_const (s ^ 2)),
      integral_const_mul, integral_div] at hi
    simpa [m1, m2, m4] using hi
  have hm1 : 0 ≤ m1 :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω => abs_nonneg (X ω))
  have hm2 : 0 ≤ m2 :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω => sq_nonneg (X ω))
  have hm4 : 0 < m4 := by simpa [m4] using h4
  by_cases hm2zero : m2 = 0
  · simp [m2, hm2zero]
    positivity
  · have hm2pos : 0 < m2 := lt_of_le_of_ne hm2 (Ne.symm hm2zero)
    by_cases hm1zero : m1 = 0
    · let s : ℝ := 1 + m4 / m2
      have hs : 0 < s := by positivity
      have hratio : m4 / m2 < s ^ 2 := by
        dsimp [s]
        nlinarith [sq_nonneg (m4 / m2)]
      have hstrict : m4 < m2 * s ^ 2 := by
        simpa [mul_comm] using (div_lt_iff₀ hm2pos).1 hratio
      have hle := hIneq s hs
      have hle' : m2 ≤ m4 / s ^ 2 := by simpa [hm1zero] using hle
      have hlt : m4 / s ^ 2 < m2 := (div_lt_iff₀ (sq_pos_of_pos hs)).2 hstrict
      exact (not_lt_of_ge hle' hlt).elim
    · have hm1pos : 0 < m1 := lt_of_le_of_ne hm1 (Ne.symm hm1zero)
      let s : ℝ := m2 / (2 * m1)
      have hs : 0 < s := by positivity
      have hle := hIneq s hs
      have hsm : s * m1 = m2 / 2 := by
        dsimp [s]
        field_simp
      have htail : m2 / 2 ≤ m4 / s ^ 2 := by rw [hsm] at hle; linarith
      have htail' : (m2 / 2) * s ^ 2 ≤ m4 :=
        (le_div_iff₀ (sq_pos_of_pos hs)).1 htail
      have hscale : m2 ^ 3 = (m2 / 2 * s ^ 2) * (8 * m1 ^ 2) := by
        dsimp [s]
        field_simp
        ring
      have hprod : m2 ^ 3 ≤ 8 * m1 ^ 2 * m4 := by
        calc
          m2 ^ 3 = (m2 / 2 * s ^ 2) * (8 * m1 ^ 2) := hscale
          _ ≤ m4 * (8 * m1 ^ 2) :=
            mul_le_mul_of_nonneg_right htail' (by positivity)
          _ = 8 * m1 ^ 2 * m4 := by ring
      have hprod' : m2 ^ 3 ≤ m1 ^ 2 * (8 * m4) := by nlinarith [hprod]
      have hfinal : m2 ^ 3 / (8 * m4) ≤ m1 ^ 2 :=
        (div_le_iff₀ (by positivity : 0 < 8 * m4)).2 hprod'
      simpa [m1, m2, m4] using hfinal




theorem prob_pos_ge_of_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 4 μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (h4 : 0 < ∫ ω, X ω ^ 4 ∂μ) :
    (∫ ω, X ω ^ 2 ∂μ) ^ 2 / (128 * ∫ ω, X ω ^ 4 ∂μ) ≤
      (μ {ω | 0 < X ω}).toReal := by
  let m1 : ℝ := ∫ ω, |X ω| ∂μ
  let m2 : ℝ := ∫ ω, X ω ^ 2 ∂μ
  let m4 : ℝ := ∫ ω, X ω ^ 4 ∂μ
  let P1 : ℝ := ∫ ω, (X ω)⁺ ∂μ
  let A : Set Ω := {ω | 0 < X ω}
  let p : ℝ := (μ A).toReal
  have hX1 : MemLp X 1 μ := hX.mono_exponent (by norm_num)
  have hX2 : MemLp X 2 μ := hX.mono_exponent (by norm_num)
  have hmeanPos := integral_posPart_eq_half_integral_abs_of_mean_zero hX1 hmean
  have hSq : Integrable (fun ω => X ω ^ 2) μ := by
    simpa [Real.norm_eq_abs, abs_sq] using hX2.integrable_norm_rpow'
  have hm2nonneg : 0 ≤ m2 :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω => sq_nonneg (X ω))
  have hm4pos : 0 < m4 := by simpa [m4] using h4
  have hm2pos : 0 < m2 := by
    by_contra hnot
    have hm2zero : m2 = 0 := le_antisymm (le_of_not_gt hnot) hm2nonneg
    have hzero := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun ω => sq_nonneg (X ω)) hSq).1 (by simpa [m2] using hm2zero)
    have hFourthAbs : Integrable (fun ω => |X ω| ^ 4) μ := by
      simpa [Real.norm_eq_abs] using hX.integrable_norm_rpow'
    have hFourth : Integrable (fun ω => X ω ^ 4) μ :=
      hFourthAbs.congr (Eventually.of_forall fun ω => by
        exact pow_abs_two_mul (X ω) (n := 2))
    have hzero4 : (fun ω => X ω ^ 4) =ᵐ[μ] 0 := by
      filter_upwards [hzero] with ω hω
      have hx : X ω = 0 := (sq_eq_zero_iff).mp hω
      simp [hx]
    have h4zero : ∫ ω, X ω ^ 4 ∂μ = 0 := by
      rw [integral_congr_ae hzero4]
      simp
    linarith
  have hMoment := integral_abs_moment_sq_ge_second_moment_cube_div_fourth hX h4
  have hMoment' : m2 ^ 3 / (8 * m4) ≤ m1 ^ 2 := by
    simpa [m1, m2, m4] using hMoment
  have hm1nonneg : 0 ≤ m1 :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω => abs_nonneg (X ω))
  have hquotpos : 0 < m2 ^ 3 / (8 * m4) :=
    div_pos (pow_pos hm2pos 3) (by positivity)
  have hm1pos : 0 < m1 := by
    have hsqpos : 0 < m1 ^ 2 := lt_of_lt_of_le hquotpos hMoment'
    nlinarith
  have hP1eq : P1 = m1 / 2 := by
    dsimp [P1, m1]
    exact hmeanPos
  have hP1pos : 0 < P1 := by rw [hP1eq]; linarith
  have hA : NullMeasurableSet A μ := by
    exact hX.aestronglyMeasurable.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
  have hInd : Integrable (A.indicator fun _ : Ω => (1 : ℝ)) μ := by
    exact memLp_one_iff_integrable.mp
      (memLp_indicator_const (p := 1) hA 1 (Or.inr (measure_ne_top μ A)))
  have hIndIntegral :
      (∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) = (μ A).toReal := by
    calc
      _ = ∫ ω in A, (1 : ℝ) ∂μ := by rw [integral_indicator₀ hA]
      _ = μ.real A := by simp
      _ = (μ A).toReal := rfl
  have hpoint (r : ℝ) (hr : 0 < r) (ω : Ω) :
      (X ω)⁺ ≤ r * (A.indicator fun _ : Ω => (1 : ℝ)) ω + X ω ^ 2 / r := by
    by_cases hx : 0 < X ω
    · have hIndVal : (A.indicator fun _ : Ω => (1 : ℝ)) ω = 1 := by
        simp [A, Set.indicator, hx]
      rw [hIndVal]
      simp only [mul_one]
      by_cases hxr : X ω ≤ r
      · have hplus : (X ω)⁺ = X ω := by simp [PosPart.posPart, le_of_lt hx]
        rw [hplus]
        calc
          X ω ≤ r := hxr
          _ ≤ r + X ω ^ 2 / r := le_add_of_nonneg_right (by positivity)
      · have hrx : r < X ω := lt_of_not_ge hxr
        have hle : X ω ≤ X ω ^ 2 / r := (le_div_iff₀ hr).2 (by
          nlinarith [mul_nonneg (sub_nonneg.mpr hrx.le) (le_of_lt hx)])
        have hplus : (X ω)⁺ = X ω := by simp [PosPart.posPart, le_of_lt hx]
        rw [hplus]
        calc
          X ω ≤ X ω ^ 2 / r := hle
          _ ≤ r + X ω ^ 2 / r := le_add_of_nonneg_left (by positivity)
    · have hxle : X ω ≤ 0 := le_of_not_gt hx
      have hIndVal : (A.indicator fun _ : Ω => (1 : ℝ)) ω = 0 := by
        simp [A, Set.indicator, hx]
      rw [hIndVal]
      have hplus : (X ω)⁺ = 0 := by simp [PosPart.posPart, hxle]
      rw [hplus]
      positivity
  let r : ℝ := 2 * m2 / P1
  have hr : 0 < r := by positivity
  have hR : Integrable
      (fun ω => r * (A.indicator fun _ : Ω => (1 : ℝ)) ω + X ω ^ 2 / r) μ :=
    (hInd.const_mul r).add (hSq.div_const r)
  have hmono := integral_mono_of_nonneg
    (Eventually.of_forall fun ω => by positivity) hR (Eventually.of_forall (hpoint r hr))
  have hbound : P1 ≤ r * p + m2 / r := by
    have hrewritten := hmono
    rw [integral_add (hInd.const_mul r) (hSq.div_const r), integral_const_mul,
      integral_div, hIndIntegral] at hrewritten
    simpa [P1, p, m2] using hrewritten
  have htail : P1 / 2 ≤ r * p := by
    have hdiv : m2 / r = P1 / 2 := by
      dsimp [r]
      field_simp
    rw [hdiv] at hbound
    linarith
  have hpRatio : (P1 / 2) / r ≤ p := by
    exact (div_le_iff₀ hr).2 (by simpa [mul_comm] using htail)
  have hratioEq : (P1 / 2) / r = P1 ^ 2 / (4 * m2) := by
    dsimp [r]
    field_simp [ne_of_gt hP1pos, ne_of_gt hm2pos]
    ring
  have hpP1 : P1 ^ 2 / (4 * m2) ≤ p := by rw [← hratioEq]; exact hpRatio
  have hpM1 : m1 ^ 2 / (16 * m2) ≤ p := by
    calc
      m1 ^ 2 / (16 * m2) = (m1 / 2) ^ 2 / (4 * m2) := by ring
      _ = P1 ^ 2 / (4 * m2) := by rw [← hP1eq]
      _ ≤ p := hpP1
  have hMomentScaled : m2 ^ 2 / (128 * m4) ≤ m1 ^ 2 / (16 * m2) := by
    calc
      m2 ^ 2 / (128 * m4) = (m2 ^ 3 / (8 * m4)) / (16 * m2) := by
        field_simp [ne_of_gt hm2pos, ne_of_gt hm4pos]
        ring
      _ ≤ m1 ^ 2 / (16 * m2) :=
        div_le_div_of_nonneg_right hMoment' (by positivity)
  have hfinal : m2 ^ 2 / (128 * m4) ≤ p := hMomentScaled.trans hpM1
  simpa [A, p, m2, m4] using hfinal

end DirectedDistances.Probability
