/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanWholePath
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/

/-! Helper toward Lemma 4.11: Gaussian Fourier calculations and rotation
reduction for the shifted radial sinc integral. The full shifted radial formula
and the resulting process-law identification are not asserted here. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal RealInnerProductSpace

section GaussianShift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Helper toward Lemma 4.11: the exact complex Fourier integral of a shifted,
scaled standard Gaussian, including zero elapsed time and zero frequency. -/
theorem integral_exp_inner_stdGaussian_shift (u : ℝ≥0) (x θ : E) (a : ℝ) :
    (∫ z : E, Complex.exp ((a * ⟪θ, x + Real.sqrt u • z⟫ : ℝ) * Complex.I)
      ∂stdGaussian E) =
    Complex.exp ((-(u : ℝ) * a ^ 2 * ‖θ‖ ^ 2 / 2 : ℝ) : ℂ) *
      Complex.exp ((a * ⟪θ, x⟫ : ℝ) * Complex.I) := by
  have hc := charFun_map_const_add
    (μ := (stdGaussian E).map (fun z : E => Real.sqrt u • z)) x (a • θ)
  rw [charFun_map_smul, charFun_stdGaussian] at hc
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)] at hc
  have hn : ‖Real.sqrt u • a • θ‖ ^ 2 = (u : ℝ) * a ^ 2 * ‖θ‖ ^ 2 := by
    rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, Real.sq_sqrt u.coe_nonneg]
    ring
  have he : -(‖Real.sqrt u • a • θ‖ : ℂ) ^ 2 / 2 =
      ((-(u : ℝ) * a ^ 2 * ‖θ‖ ^ 2 / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hn]
    push_cast
    ring
  rw [he] at hc
  simpa only [real_inner_smul_right, real_inner_comm θ, Complex.ofReal_mul] using hc

/-- Helper toward Lemma 4.11: every shifted Gaussian plane wave has the
exact heat multiplier. No rotational or spherical averaging premise is used. -/
theorem integral_cos_inner_stdGaussian_shift (u : ℝ≥0) (x θ : E) (a : ℝ) :
    (∫ z : E, Real.cos (a * ⟪θ, x + Real.sqrt u • z⟫) ∂stdGaussian E) =
    Real.cos (a * ⟪θ, x⟫) * Real.exp (-(u : ℝ) * a ^ 2 * ‖θ‖ ^ 2 / 2) := by
  have hi : Integrable
      (fun z : E => Complex.exp ((a * ⟪θ, x + Real.sqrt u • z⟫ : ℝ) * Complex.I))
      (stdGaussian E) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Eventually.of_forall (fun z => by simp [Complex.norm_exp])
  have hc := congrArg Complex.re (integral_exp_inner_stdGaussian_shift u x θ a)
  have hr : (∫ z : E,
      (Complex.exp ((a * ⟪θ, x + Real.sqrt u • z⟫ : ℝ) * Complex.I)).re
        ∂stdGaussian E) =
      (∫ z : E, Complex.exp ((a * ⟪θ, x + Real.sqrt u • z⟫ : ℝ) * Complex.I)
        ∂stdGaussian E).re := integral_re hi
  rw [← hr] at hc
  rw [← Complex.ofReal_exp] at hc
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re] at hc
  simpa only [mul_comm] using hc

/-- Helper toward Lemma 4.11: averaging the Gaussian plane-wave formula over
any finite measure on the unit sphere gives the radial heat multiplier.
The identification of a spherical cosine average with sinc is separate. -/
theorem integral_sphere_cos_stdGaussian_shift
    (σ : Measure (Metric.sphere (0 : E) 1)) [IsFiniteMeasure σ]
    (u : ℝ≥0) (x : E) (a : ℝ) :
    (∫ z : E, (∫ θ : Metric.sphere (0 : E) 1,
      Real.cos (a * ⟪(θ : E), x + Real.sqrt u • z⟫) ∂σ) ∂stdGaussian E) =
    Real.exp (-(u : ℝ) * a ^ 2 / 2) *
      ∫ θ : Metric.sphere (0 : E) 1, Real.cos (a * ⟪(θ : E), x⟫) ∂σ := by
  have hi : Integrable
      (fun p : E × Metric.sphere (0 : E) 1 =>
        Real.cos (a * ⟪(p.2 : E), x + Real.sqrt u • p.1⟫))
      ((stdGaussian E).prod σ) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Eventually.of_forall (fun p => Real.abs_cos_le_one _)
  rw [integral_integral_swap hi]
  have he (θ : Metric.sphere (0 : E) 1) :
      (∫ z : E, Real.cos (a * ⟪(θ : E), x + Real.sqrt u • z⟫)
        ∂stdGaussian E) =
      Real.cos (a * ⟪(θ : E), x⟫) * Real.exp (-(u : ℝ) * a ^ 2 / 2) := by
    have hθ : ‖(θ : E)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
    rw [integral_cos_inner_stdGaussian_shift, hθ, one_pow, mul_one]
  simp_rw [he]
  rw [integral_mul_const, mul_comm]

/-- Helper toward Lemma 4.11: the sine transform of a shifted centered
Gaussian has the exact variance multiplier, including zero variance. -/
theorem integral_sin_gaussian_shift (u : ℝ≥0) (r a : ℝ) :
    (∫ z : ℝ, Real.sin (a * (r + z)) ∂gaussianReal 0 u) =
      Real.sin (a * r) * Real.exp (-(u : ℝ) * a^2 / 2) := by
  have hi : Integrable
      (fun z : ℝ => Complex.exp ((a * (r + z) : ℝ) * Complex.I))
      (gaussianReal 0 u) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Eventually.of_forall (fun z => by simp [Complex.norm_exp])
  have hc := charFun_map_const_add (μ := gaussianReal 0 u) r a
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    charFun_gaussianReal] at hc
  have hz : Complex.exp ((a : ℂ) * 0 * Complex.I - u * (a : ℂ)^2 / 2) =
      ((Real.exp (-(u : ℝ) * a^2 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [Complex.ofReal_zero] at hc
  rw [hz] at hc
  have him := congrArg Complex.im hc
  have hI : (∫ z : ℝ,
      (Complex.exp ((a * (r + z) : ℝ) * Complex.I)).im ∂gaussianReal 0 u) =
      (∫ z : ℝ, Complex.exp ((a * (r + z) : ℝ) * Complex.I)
        ∂gaussianReal 0 u).im := integral_im hi
  have he : (∫ z : ℝ, Complex.exp ((a * (r + z) : ℝ) * Complex.I)
      ∂gaussianReal 0 u) =
      (∫ z : ℝ, Complex.exp ((a : ℂ) * (r + z : ℝ) * Complex.I)
        ∂gaussianReal 0 u) := by simp only [Complex.ofReal_mul]
  rw [← he, ← hI] at him
  simp only [Complex.exp_ofReal_mul_I_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, RCLike.inner_apply, conj_trivial,
    Complex.exp_ofReal_mul_I_im] at him
  simpa only [mul_comm] using him

/-- Helper toward Lemma 4.11: Gaussian smoothing of a radial sinc test is
unchanged when its shift is transformed by a linear isometry. -/
theorem integral_sinc_norm_stdGaussian_isometry
    (u : ℝ≥0) (a : ℝ) (x : E) (e : E ≃ₗᵢ[ℝ] E) :
    (∫ z : E, Real.sinc (a * ‖e x + Real.sqrt u • z‖) ∂stdGaussian E) =
      ∫ z : E, Real.sinc (a * ‖x + Real.sqrt u • z‖) ∂stdGaussian E := by
  have hm := stdGaussian_map e
  calc
    _ = ∫ z : E, Real.sinc (a * ‖e x + Real.sqrt u • z‖)
        ∂(stdGaussian E).map e := by rw [hm]
    _ = ∫ z : E, Real.sinc (a * ‖e x + Real.sqrt u • e z‖)
        ∂stdGaussian E := integral_map (by fun_prop) (by fun_prop)
    _ = _ := by
      congr 1
      funext z
      rw [← e.map_smul, ← e.map_add, e.norm_map]

/-- Helper toward Lemma 4.11: the shifted radial sinc integral depends only
on the Euclidean norm of the shift. The witnessing rotation is a reflection. -/
theorem integral_sinc_norm_stdGaussian_eq_of_norm_eq
    (u : ℝ≥0) (a : ℝ) {x y : E} (hxy : ‖x‖ = ‖y‖) :
    (∫ z : E, Real.sinc (a * ‖x + Real.sqrt u • z‖) ∂stdGaussian E) =
      ∫ z : E, Real.sinc (a * ‖y + Real.sqrt u • z‖) ∂stdGaussian E := by
  let e := (ℝ ∙ (x - y))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  exact (he ▸ integral_sinc_norm_stdGaussian_isometry u a x e).symm

end GaussianShift

private theorem norm_toLp_three (x : Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ =
      Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  congr 1
  ring

/-- Helper toward Lemma 4.11: the shifted product-Gaussian radial integral
is the Gaussian convolution of the Euclidean radial sinc test, with the exact
variance scaling, including zero variance. -/
theorem integral_sinc_gaussian_radial3_shift_standardize
    (u : ℝ≥0) (x : Fin 3 → ℝ) (a : ℝ) :
    (∫ d : Fin 3 → ℝ, Real.sinc (a * Real.sqrt
      ((x 0 + d 0)^2 + (x 1 + d 1)^2 + (x 2 + d 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 u)) =
    ∫ z : EuclideanSpace ℝ (Fin 3),
      Real.sinc (a * ‖WithLp.toLp 2 x + Real.sqrt u • z‖)
        ∂stdGaussian (EuclideanSpace ℝ (Fin 3)) := by
  let S (d : Fin 3 → ℝ) (i : Fin 3) := Real.sqrt u * d i
  have hmap : (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map S =
      Measure.pi (fun _ : Fin 3 => gaussianReal 0 u) := by
    rw [Measure.pi_map_pi (fun _ =>
      (by fun_prop : AEMeasurable (fun d : ℝ => Real.sqrt u * d) (gaussianReal 0 1)))]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul]
    congr 1
    · exact mul_zero _
    · apply NNReal.coe_injective
      simp only [NNReal.coe_mk, mul_one]
      exact Real.sq_sqrt u.coe_nonneg
  rw [← hmap, integral_map (by fun_prop : AEMeasurable S
    (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1))) (by fun_prop)]
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun d => by
    dsimp only
    have he : WithLp.toLp 2 x + Real.sqrt u • WithLp.toLp 2 d =
        (WithLp.toLp 2 (fun i => x i + S d i) : EuclideanSpace ℝ (Fin 3)) := by
      ext i
      rfl
    rw [he, norm_toLp_three])

/-- Helper toward Lemma 4.11: a general nonzero three-dimensional shift
reduces exactly to an axial shift of the same radius. This proves the rotation
step; the one-dimensional axial radial integration is still required. -/
theorem integral_sinc_gaussian_radial3_shift_eq_axial
    (u : ℝ≥0) (x : Fin 3 → ℝ) (a : ℝ) :
    (∫ d : Fin 3 → ℝ, Real.sinc (a * Real.sqrt
      ((x 0 + d 0)^2 + (x 1 + d 1)^2 + (x 2 + d 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 u)) =
    ∫ d : Fin 3 → ℝ, Real.sinc (a * Real.sqrt
      ((Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) + d 0)^2 +
        (d 1)^2 + (d 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 u) := by
  let r := Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2)
  let y : Fin 3 → ℝ := fun i => if i = 0 then r else 0
  have hn : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ =
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3))‖ := by
    rw [norm_toLp_three, norm_toLp_three]
    simp only [y, ite_true, show (1 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 0 by decide, ite_false, zero_pow (by decide : 2 ≠ 0),
      add_zero]
    exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  have he := integral_sinc_norm_stdGaussian_eq_of_norm_eq u a hn
  rw [← integral_sinc_gaussian_radial3_shift_standardize,
    ← integral_sinc_gaussian_radial3_shift_standardize] at he
  simpa only [y, ite_true, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, zero_add] using he

/-- Helper toward Lemma 4.11: the quadratic characteristic integral of a
noncentral Gaussian differs from its centered counterpart by the exact
noncentral exponential factor. This is an equality of complex integrals. -/
theorem integral_exp_gaussian_shift_sq (b r : ℝ) :
    (∫ z : ℝ, Complex.exp ((b : ℂ) * (r + z : ℝ) ^ 2 * Complex.I)
      ∂gaussianReal 0 1) =
    (∫ z : ℝ, Complex.exp ((b : ℂ) * (z : ℂ) ^ 2 * Complex.I)
      ∂gaussianReal 0 1) *
      Complex.exp ((b : ℂ) * Complex.I * r ^ 2 / (1 - 2 * (b : ℂ) * Complex.I)) := by
  let q : ℂ := 1 / 2 - (b : ℂ) * Complex.I
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hq : (-q).re < 0 := by simp [q]
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  have hd : (1 - 2 * (b : ℂ) * Complex.I) = 2 * q := by dsimp [q]; ring
  have he (r : ℝ) :
      (∫ z : ℝ, Complex.exp ((b : ℂ) * (r + z : ℝ) ^ 2 * Complex.I)
        ∂gaussianReal 0 1) =
      (c : ℂ) * (Real.pi / q) ^ (1 / 2 : ℂ) *
        Complex.exp ((b : ℂ) * Complex.I * r ^ 2 /
          (1 - 2 * (b : ℂ) * Complex.I)) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
    have hp (z : ℝ) :
        gaussianPDFReal 0 1 z •
          Complex.exp ((b : ℂ) * (r + z : ℝ) ^ 2 * Complex.I) =
        (c : ℂ) * Complex.exp
          (-q * (z : ℂ)^2 + (2 * (b : ℂ) * Complex.I * r) * z +
            (b : ℂ) * Complex.I * r^2) := by
      simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero,
        Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_exp,
        Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
        Complex.ofReal_add]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      · simp only [c, Complex.ofReal_inv]
      · dsimp [q]
        ring
    simp_rw [hp]
    rw [integral_const_mul, integral_cexp_quadratic hq]
    simp only [neg_neg]
    have hex : (b : ℂ) * Complex.I * r^2 -
        (2 * (b : ℂ) * Complex.I * r)^2 / (4 * -q) =
        (b : ℂ) * Complex.I * r^2 / (1 - 2 * (b : ℂ) * Complex.I) := by
      rw [hd]
      field_simp [hq0]
      dsimp [q]
      ring
    rw [hex]
    ring
  rw [he r]
  have hzero := he 0
  simp only [Complex.ofReal_zero, zero_add, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_div, Complex.exp_zero, mul_one] at hzero
  rw [hzero]

private theorem hasDerivAt_integral_exp_gaussian_shift_sq (b r : ℝ) :
    HasDerivAt
      (fun c : ℝ => ∫ z : ℝ,
        Complex.exp ((b : ℂ) * (c + z : ℝ)^2 * Complex.I) ∂gaussianReal 0 1)
      (2 * (b : ℂ) * Complex.I *
        ∫ z : ℝ, (r + z : ℝ) *
          Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I) ∂gaussianReal 0 1) r := by
  have hZ : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hnorm (c z : ℝ) :
      ‖Complex.exp ((b : ℂ) * (c + z : ℝ)^2 * Complex.I)‖ = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  have hi : Integrable
      (fun z : ℝ => Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I))
      (gaussianReal 0 1) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Eventually.of_forall (fun z => (hnorm r z).le)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1)
    (F := fun c z : ℝ => Complex.exp ((b : ℂ) * (c + z : ℝ)^2 * Complex.I))
    (F' := fun c z : ℝ => 2 * (b : ℂ) * Complex.I * (c + z : ℝ) *
      Complex.exp ((b : ℂ) * (c + z : ℝ)^2 * Complex.I))
    (bound := fun z : ℝ => 2 * |b| * (|r| + 1 + |z|))
    (s := Metric.ball r 1) (Metric.ball_mem_nhds r (by norm_num))
    (Eventually.of_forall (fun _ => by fun_prop)) hi (by fun_prop)
    (Eventually.of_forall (fun z c hc => by
      have hcr : |c - r| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hc
      have hca : |c| ≤ |r| + 1 := by
        have hh := abs_add_le (c - r) r
        rw [sub_add_cancel] at hh
        linarith only [hh, hcr]
      have hcz : |c + z| ≤ |r| + 1 + |z| := by
        linarith only [abs_add_le c z, hca]
      simpa only [norm_mul, hnorm, Complex.norm_real, Complex.norm_I,
        Complex.norm_ofNat, Real.norm_eq_abs, mul_one] using
        mul_le_mul_of_nonneg_left hcz (by positivity : 0 ≤ 2 * |b|)))
    (((integrable_const (|r| + 1)).add hZ.abs).const_mul (2 * |b|))
    (Eventually.of_forall (fun z c _ => by
      convert ((((((hasDerivAt_id' c).add_const z).pow 2).ofReal_comp.const_mul
        (b : ℂ)).mul_const Complex.I).cexp) using 1 <;>
        dsimp only [Pi.pow_apply] <;> push_cast <;> ring))
  simpa only [mul_assoc, integral_const_mul] using hd.2

/-- Helper toward Lemma 4.11: the first noncentral Gaussian quadratic moment
has the exact factor needed to identify the axial three-dimensional radius.
The formula includes zero Fourier frequency and zero shift. -/
theorem integral_mul_exp_gaussian_shift_sq (b r : ℝ) :
    (1 - 2 * (b : ℂ) * Complex.I) *
      (∫ z : ℝ, (r + z : ℝ) *
        Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I) ∂gaussianReal 0 1) =
    (r : ℂ) *
      ∫ z : ℝ, Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I)
        ∂gaussianReal 0 1 := by
  by_cases hb : b = 0
  · subst b
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, sub_zero,
      Complex.exp_zero, mul_one, integral_const, probReal_univ, one_mul]
    rw [integral_complex_ofReal]
    have hZ : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
    rw [integral_add (integrable_const _) hZ, integral_const,
      integral_id_gaussianReal]
    simp
  let K := ∫ z : ℝ, Complex.exp ((b : ℂ) * (z : ℂ)^2 * Complex.I)
    ∂gaussianReal 0 1
  let d : ℂ := 1 - 2 * (b : ℂ) * Complex.I
  have hd0 : d ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [d] at hr
  have hclosed : HasDerivAt
      (fun c : ℝ => K * Complex.exp ((b : ℂ) * Complex.I * (c : ℂ)^2 / d))
      (K * Complex.exp ((b : ℂ) * Complex.I * (r : ℂ)^2 / d) *
        (2 * (b : ℂ) * Complex.I * r / d)) r := by
    convert ((((((hasDerivAt_id' r).pow 2).ofReal_comp.const_mul
      ((b : ℂ) * Complex.I)).div_const d).cexp).const_mul K) using 1 <;>
      dsimp only [Pi.pow_apply] <;> push_cast <;> ring
  have hder := hasDerivAt_integral_exp_gaussian_shift_sq b r
  simp_rw [integral_exp_gaussian_shift_sq] at hder
  have he := hder.unique hclosed
  have ht : 2 * (b : ℂ) * Complex.I ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (Complex.ofReal_ne_zero.mpr hb)) Complex.I_ne_zero
  apply (mul_left_cancel₀ ht)
  change (2 * (b : ℂ) * Complex.I) * (d * _) =
    (2 * (b : ℂ) * Complex.I) * ((r : ℂ) * _)
  rw [integral_exp_gaussian_shift_sq]
  change (2 * (b : ℂ) * Complex.I) * (d * _) =
    (2 * (b : ℂ) * Complex.I) * ((r : ℂ) * (K * _))
  have he' := congrArg (fun w : ℂ => w * d) he
  rw [mul_assoc (K * _) _ d, div_mul_cancel₀ _ hd0] at he'
  linear_combination he'

private theorem gaussian_square_charFun_mul_sq (b : ℝ) :
    (1 - 2 * (b : ℂ) * Complex.I) *
      (∫ z : ℝ, Complex.exp ((b : ℂ) * (z : ℂ)^2 * Complex.I)
        ∂gaussianReal 0 1)^2 = 1 := by
  let q : ℂ := 1 / 2 - (b : ℂ) * Complex.I
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hq : 0 < q.re := by simp [q]
  have he : (∫ z : ℝ, Complex.exp ((b : ℂ) * (z : ℂ)^2 * Complex.I)
      ∂gaussianReal 0 1) = (c : ℂ) * ∫ z : ℝ, Complex.exp (-q * (z : ℂ)^2) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num), ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero,
        Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_exp,
        Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      · simp only [c, Complex.ofReal_inv]
      · dsimp [q]; ring)
  rw [he, mul_pow, integral_gaussian_sq_complex hq]
  have hc : (c : ℂ)^2 * (2 * Real.pi) = 1 := by
    have hr : c^2 * (2 * Real.pi) = 1 := by
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt (by positivity)]
      exact inv_mul_cancel₀ (by positivity)
    exact_mod_cast hr
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  have hd : 1 - 2 * (b : ℂ) * Complex.I = 2 * q := by dsimp [q]; ring
  rw [hd]
  calc
    _ = (c : ℂ)^2 * (2 * Real.pi) := by field_simp [hq0]
    _ = 1 := hc

/-- Helper toward Lemma 4.11: the squared axial three-dimensional Gaussian
radius has exactly the signed first-moment transform of a shifted scalar
Gaussian. This supplies the Fourier step of the noncentral radial law. -/
theorem gaussian_axial3_quadratic_charFun (b r : ℝ) :
    (r : ℂ) * (∫ z : Fin 3 → ℝ, Complex.exp ((b : ℂ) *
      ((r + z 0)^2 + (z 1)^2 + (z 2)^2 : ℝ) * Complex.I)
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) =
    ∫ z : ℝ, (r + z : ℝ) *
      Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I) ∂gaussianReal 0 1 := by
  let K := ∫ z : ℝ, Complex.exp ((b : ℂ) * (z : ℂ)^2 * Complex.I)
    ∂gaussianReal 0 1
  let H := ∫ z : ℝ, Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I)
    ∂gaussianReal 0 1
  let J := ∫ z : ℝ, (r + z : ℝ) *
    Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I) ∂gaussianReal 0 1
  have he (z : Fin 3 → ℝ) :
      Complex.exp ((b : ℂ) * ((r + z 0)^2 + (z 1)^2 + (z 2)^2 : ℝ) * Complex.I) =
      ∏ i : Fin 3, Complex.exp ((b : ℂ) *
        (if i = 0 then (r + z i)^2 else (z i)^2 : ℝ) * Complex.I) := by
    simp only [Fin.prod_univ_succ, ite_true, Fin.succ_ne_zero, ite_false,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Complex.ofReal_add, Complex.ofReal_pow, mul_add, add_mul, Complex.exp_add]
    ring
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun (i : Fin 3) (z : ℝ) =>
    Complex.exp ((b : ℂ) * (if i = 0 then (r + z)^2 else z^2 : ℝ) * Complex.I))]
  simp only [Fin.prod_univ_succ, ite_true, Fin.succ_ne_zero, ite_false,
    Fin.prod_univ_zero, mul_one, Complex.ofReal_pow]
  change (r : ℂ) * (H * (K * K)) = J
  have hk : (1 - 2 * (b : ℂ) * Complex.I) * K^2 = 1 := gaussian_square_charFun_mul_sq b
  have hj : (1 - 2 * (b : ℂ) * Complex.I) * J = (r : ℂ) * H :=
    integral_mul_exp_gaussian_shift_sq b r
  linear_combination J * hk - K^2 * hj

private theorem gaussian_linear_pos_integrable (r ε : ℝ) :
    Integrable (fun z : ℝ => max (ε * (r + z)) 0) (gaussianReal 0 1) := by
  have hZ : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  exact (((integrable_const r).add hZ).const_mul ε).sup (integrable_const 0)

private theorem gaussian_linear_pos_finite (r ε : ℝ) :
    IsFiniteMeasure ((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (ε * (r + z)) 0))) := by
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall (fun z => le_max_right _ _))).2
      (gaussian_linear_pos_integrable r ε)

private theorem integrable_exp_sq (μ : Measure ℝ) [IsFiniteMeasure μ] (b : ℝ) :
    Integrable (fun q : ℝ => Complex.exp ((b : ℂ) * q * Complex.I)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  exact Eventually.of_forall (fun q => by simp [Complex.norm_exp])

private theorem integral_gaussian_linear_pos_map (r ε : ℝ)
    (f : ℝ → ℂ) (hf : Measurable f) :
    (∫ q, f q ∂(((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (ε * (r + z)) 0)))).map
        (fun z : ℝ => (r + z)^2)) =
    ∫ z : ℝ, (max (ε * (r + z)) 0 : ℝ) * f ((r + z)^2)
      ∂gaussianReal 0 1 := by
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), Complex.real_smul]

/-- Helper toward Lemma 4.11: an exact identity of finite positive measures
encodes the signed noncentral radial law. The positive and negative scalar
weights are explicit; no radial transition law is assumed. -/
theorem gaussian_axial3_square_measure_identity (r : ℝ) (hr : 0 ≤ r) :
    (((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (r + z) 0))).map
        (fun z : ℝ => (r + z)^2)) =
    ENNReal.ofReal r • ((Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map
      (fun z : Fin 3 → ℝ => (r + z 0)^2 + (z 1)^2 + (z 2)^2)) +
    (((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (-(r + z)) 0))).map
        (fun z : ℝ => (r + z)^2)) := by
  have hP : IsFiniteMeasure ((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (r + z) 0))) := by
    simpa only [one_mul] using gaussian_linear_pos_finite r 1
  have hN : IsFiniteMeasure ((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (-(r + z)) 0))) := by
    simpa only [neg_one_mul] using gaussian_linear_pos_finite r (-1)
  have hS : IsFiniteMeasure (ENNReal.ofReal r •
      ((Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map
        (fun z : Fin 3 → ℝ => (r + z 0)^2 + (z 1)^2 + (z 2)^2))) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  apply Measure.ext_of_charFun
  funext b
  rw [charFun_apply_real, charFun_apply_real,
    integral_add_measure (integrable_exp_sq _ b) (integrable_exp_sq _ b),
    integral_smul_measure, ENNReal.toReal_ofReal hr,
    Complex.real_smul]
  have hp := integral_gaussian_linear_pos_map r 1
    (fun q => Complex.exp ((b : ℂ) * q * Complex.I)) (by fun_prop)
  have hn := integral_gaussian_linear_pos_map r (-1)
    (fun q => Complex.exp ((b : ℂ) * q * Complex.I)) (by fun_prop)
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  rw [hp, hn, integral_map (by fun_prop) (by fun_prop), gaussian_axial3_quadratic_charFun]
  simp only [Complex.ofReal_pow]
  have hint (ε : ℝ) : Integrable
      (fun z : ℝ => (max (ε * (r + z)) 0 : ℝ) *
        Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I))
      (gaussianReal 0 1) := by
    apply Integrable.mono' (gaussian_linear_pos_integrable r ε).abs (by fun_prop)
    exact Eventually.of_forall (fun z => by
      rw [norm_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs])
  have hpI := hint 1
  have hnI := hint (-1)
  simp only [one_mul] at hpI
  simp only [neg_one_mul] at hnI
  apply sub_eq_iff_eq_add.mp
  rw [← integral_sub hpI hnI]
  have he (z : ℝ) :
      (max (r + z) 0 : ℝ) * Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I) -
      (max (-(r + z)) 0 : ℝ) * Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I) =
      (r + z : ℝ) * Complex.exp ((b : ℂ) * (r + z : ℝ)^2 * Complex.I) := by
    by_cases hz : 0 ≤ r + z
    · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
      simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    · rw [max_eq_right (le_of_not_ge hz), max_eq_left (neg_nonneg.mpr (le_of_not_ge hz))]
      push_cast
      ring
  simp_rw [he]

/-- Helper toward Lemma 4.11: the signed scalar sinc moment at a nonzero
shift is explicit. Multiplication by the shift removes the axial density's
denominator; the identity also holds at zero shift and zero variance. -/
theorem integral_mul_sinc_gaussian_shift (u : ℝ≥0) (r a : ℝ) :
    (∫ z : ℝ, (r + z) * Real.sinc (a * (r + z)) ∂gaussianReal 0 u) =
      r * Real.sinc (a * r) * Real.exp (-(u : ℝ) * a^2 / 2) := by
  have hs (y : ℝ) : a * (y * Real.sinc (a * y)) = Real.sin (a * y) := by
    by_cases h : a * y = 0
    · rw [← mul_assoc, h, zero_mul, Real.sin_zero]
    · rw [Real.sinc_of_ne_zero h]
      calc
        _ = (a * y) * Real.sin (a * y) / (a * y) := by ring
        _ = _ := mul_div_cancel_left₀ _ h
  by_cases ha : a = 0
  · subst a
    simp only [zero_mul, Real.sinc_zero, mul_one, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_div, Real.exp_zero]
    have hZ : Integrable (fun z : ℝ => z) (gaussianReal 0 u) :=
      (memLp_id_gaussianReal (μ := 0) (v := u) 1).integrable (by norm_num)
    rw [integral_add (integrable_const _) hZ, integral_const, integral_id_gaussianReal]
    simp
  apply mul_left_cancel₀ ha
  rw [← integral_const_mul]
  simp_rw [hs]
  rw [integral_sin_gaussian_shift]
  rw [← hs r]
  ring

private theorem integral_gaussian_linear_pos_map_real (r ε : ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ q, f q ∂(((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (ε * (r + z)) 0)))).map
        (fun z : ℝ => (r + z)^2)) =
    ∫ z : ℝ, max (ε * (r + z)) 0 * f ((r + z)^2) ∂gaussianReal 0 1 := by
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]

/-- Helper toward Lemma 4.11: the noncentral axial Gaussian sinc formula
at unit variance follows from the signed radial measure identity. -/
theorem integral_sinc_gaussian_axial3 (r : ℝ) (hr : 0 < r) (a : ℝ) :
    (∫ z : Fin 3 → ℝ, Real.sinc (a * Real.sqrt
      ((r + z 0)^2 + (z 1)^2 + (z 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) =
      Real.sinc (a * r) * Real.exp (-a^2 / 2) := by
  have hP : IsFiniteMeasure ((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (r + z) 0))) := by
    simpa only [one_mul] using gaussian_linear_pos_finite r 1
  have hN : IsFiniteMeasure ((gaussianReal 0 1).withDensity
      (fun z : ℝ => ENNReal.ofReal (max (-(r + z)) 0))) := by
    simpa only [neg_one_mul] using gaussian_linear_pos_finite r (-1)
  have hS : IsFiniteMeasure (ENNReal.ofReal r •
      ((Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map
        (fun z : Fin 3 → ℝ => (r + z 0)^2 + (z 1)^2 + (z 2)^2))) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  have hi (μ : Measure ℝ) [IsFiniteMeasure μ] :
      Integrable (fun q : ℝ => Real.sinc (a * Real.sqrt q)) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Eventually.of_forall (fun q => Real.abs_sinc_le_one _)
  have he := congrArg (fun μ : Measure ℝ =>
    ∫ q : ℝ, Real.sinc (a * Real.sqrt q) ∂μ)
      (gaussian_axial3_square_measure_identity r hr.le)
  rw [integral_add_measure (hi _) (hi _), integral_smul_measure,
    ENNReal.toReal_ofReal hr.le, smul_eq_mul] at he
  have hp := integral_gaussian_linear_pos_map_real r 1
    (fun q => Real.sinc (a * Real.sqrt q)) (by fun_prop)
  have hn := integral_gaussian_linear_pos_map_real r (-1)
    (fun q => Real.sinc (a * Real.sqrt q)) (by fun_prop)
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  rw [hp, hn, integral_map (by fun_prop) (by fun_prop)] at he
  have hs (y : ℝ) : Real.sinc (a * Real.sqrt (y^2)) = Real.sinc (a * y) := by
    rw [Real.sqrt_sq_eq_abs]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
    · rw [abs_of_neg (lt_of_not_ge hy), mul_neg, Real.sinc_neg]
  simp_rw [hs] at he
  have hint (ε : ℝ) : Integrable
      (fun z : ℝ => max (ε * (r + z)) 0 * Real.sinc (a * (r + z)))
      (gaussianReal 0 1) := by
    apply Integrable.mono' (gaussian_linear_pos_integrable r ε).abs (by fun_prop)
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (abs_nonneg _)).trans
        (by rw [mul_one]))
  have hpI := hint 1
  have hnI := hint (-1)
  simp only [one_mul] at hpI
  simp only [neg_one_mul] at hnI
  have hd :
      (∫ z : ℝ, max (r + z) 0 * Real.sinc (a * (r + z)) ∂gaussianReal 0 1) -
      (∫ z : ℝ, max (-(r + z)) 0 * Real.sinc (a * (r + z)) ∂gaussianReal 0 1) =
      r * Real.sinc (a * r) * Real.exp (-a^2 / 2) := by
    rw [← integral_sub hpI hnI]
    have hw (z : ℝ) : max (r + z) 0 - max (-(r + z)) 0 = r + z := by
      by_cases hz : 0 ≤ r + z
      · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), sub_zero]
      · rw [max_eq_right (le_of_not_ge hz), max_eq_left (neg_nonneg.mpr (le_of_not_ge hz))]
        ring
    simp_rw [← sub_mul, hw]
    simpa only [NNReal.coe_one, neg_mul, one_mul] using integral_mul_sinc_gaussian_shift 1 r a
  apply mul_left_cancel₀ hr.ne'
  linarith only [he, hd]

/-- Helper toward Lemma 4.11: the nonzero-shift three-dimensional Gaussian
sinc formula at unit variance, on the coordinate carrier used by the paths. -/
theorem integral_sinc_gaussian_radial3_shift_one (x : Fin 3 → ℝ) (a : ℝ) :
    (∫ d : Fin 3 → ℝ, Real.sinc (a * Real.sqrt
      ((x 0 + d 0)^2 + (x 1 + d 1)^2 + (x 2 + d 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) =
    Real.sinc (a * Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2)) *
      Real.exp (-a^2 / 2) := by
  rw [integral_sinc_gaussian_radial3_shift_eq_axial]
  by_cases hr : Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) = 0
  · simp only [hr, zero_add, mul_zero, Real.sinc_zero, one_mul]
    exact integral_sinc_gaussian_radial3 a
  · exact integral_sinc_gaussian_axial3 _
      (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)) a

private theorem integral_sinc_norm_stdGaussian_three_one
    (x : EuclideanSpace ℝ (Fin 3)) (a : ℝ) :
    (∫ z : EuclideanSpace ℝ (Fin 3), Real.sinc (a * ‖x + z‖)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 3))) =
    Real.sinc (a * ‖x‖) * Real.exp (-a^2 / 2) := by
  have h := integral_sinc_gaussian_radial3_shift_one (fun i => x i) a
  rw [integral_sinc_gaussian_radial3_shift_standardize] at h
  simpa only [NNReal.coe_one, Real.sqrt_one, one_smul, ← norm_toLp_three] using h

/-- Helper toward Lemma 4.11: the full shifted radial Gaussian sinc formula
has the exact elapsed-time multiplier, including zero variance and zero shift. -/
theorem integral_sinc_gaussian_radial3_shift
    (u : ℝ≥0) (x : Fin 3 → ℝ) (a : ℝ) :
    (∫ d : Fin 3 → ℝ, Real.sinc (a * Real.sqrt
      ((x 0 + d 0)^2 + (x 1 + d 1)^2 + (x 2 + d 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 u)) =
    Real.sinc (a * Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2)) *
      Real.exp (-(u : ℝ) * a^2 / 2) := by
  rw [integral_sinc_gaussian_radial3_shift_standardize, ← norm_toLp_three]
  by_cases hu : u = 0
  · subst u
    simp
  have hc : Real.sqrt (u : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu))
  let X : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 x
  have he (z : EuclideanSpace ℝ (Fin 3)) :
      X + Real.sqrt u • z = Real.sqrt u • ((Real.sqrt u)⁻¹ • X + z) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
  change (∫ z : EuclideanSpace ℝ (Fin 3), Real.sinc (a * ‖X + Real.sqrt u • z‖)
    ∂stdGaussian (EuclideanSpace ℝ (Fin 3))) = _
  simp_rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ← mul_assoc]
  rw [integral_sinc_norm_stdGaussian_three_one, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hf : a * Real.sqrt u * ((Real.sqrt u)⁻¹ * ‖X‖) = a * ‖X‖ := by
    rw [mul_assoc a (Real.sqrt u), ← mul_assoc (Real.sqrt u), mul_inv_cancel₀ hc, one_mul]
  rw [hf, mul_pow, Real.sq_sqrt u.coe_nonneg]
  congr 2
  ring

local instance pitmanWholePath2ContinuousMapMeasurableSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance pitmanWholePath2ContinuousMapBorelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance pitmanWholePath2ContinuousMapSecondCountable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

open DirectedDistances.RandomWalk

/-- Helper toward Lemma 4.11: the three-dimensional Brownian radius satisfies
the exact finite-past sinc transition identity, including repeated past times,
the empty past, and zero elapsed time. -/
theorem radial3_past_sinc_transition
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (s u : ℝ≥0) {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ j, t j ≤ s)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    (∫ p, F (fun j => radial3Path (firstThreePath p) (t j)) *
      Real.sinc (a * radial3Path (firstThreePath p) (s + u)) ∂W₄) =
    Real.exp (-(u : ℝ) * a^2 / 2) *
      ∫ p, F (fun j => radial3Path (firstThreePath p) (t j)) *
        Real.sinc (a * radial3Path (firstThreePath p) s) ∂W₄ := by
  rw [radial3_past_sinc_eq_gaussian_integral W₄ hB hI s u t ht F a]
  have he (p : C(ℝ≥0, Fin 4 → ℝ)) :
      (∫ d : Fin 3 → ℝ, Real.sinc (a * Real.sqrt
        ((p s 0 + d 0)^2 + (p s 1 + d 1)^2 + (p s 2 + d 2)^2))
          ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 u)) =
      Real.sinc (a * radial3Path (firstThreePath p) s) *
        Real.exp (-(u : ℝ) * a^2 / 2) :=
    integral_sinc_gaussian_radial3_shift u (fun i => p s i.castSucc) a
  simp_rw [he]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

/-- Helper toward Lemma 4.11: the scalar Pitman process and the Brownian
radius have identical two-time laws, with zero and repeated times permitted. -/
theorem scalarPitman_radial3_identDistrib_two_time
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (s u : ℝ≥0) :
    IdentDistrib
      (fun p => (scalarPitman (pathCoordinate p 0) s,
        scalarPitman (pathCoordinate p 0) (s + u)))
      (fun p => (radial3Path (firstThreePath p) s,
        radial3Path (firstThreePath p) (s + u))) W₄ W₄ := by
  have hprod : IdentDistrib
      (fun p => ((fun _ : Fin 1 => scalarPitman (pathCoordinate p 0) s),
        scalarPitman (pathCoordinate p 0) (s + u)))
      (fun p => ((fun _ : Fin 1 => radial3Path (firstThreePath p) s),
        radial3Path (firstThreePath p) (s + u))) W₄ W₄ := by
    apply WholePathSinc.identDistrib_prod_of_integral_mul_sinc_eq_of_nonneg
    · have hm (t : ℝ≥0) : Measurable
          (fun p : C(ℝ≥0, Fin 4 → ℝ) => scalarPitman (pathCoordinate p 0) t) :=
        ((continuous_eval_const t).comp
          (continuous_scalarPitman.comp (continuous_pathCoordinate 0))).measurable
      exact ((measurable_pi_iff.mpr (fun _ => hm s)).prodMk (hm (s + u))).aemeasurable
    · have hm (t : ℝ≥0) : Measurable
          (fun p : C(ℝ≥0, Fin 4 → ℝ) => radial3Path (firstThreePath p) t) :=
        ((continuous_eval_const t).comp
          (continuous_radial3Path.comp continuous_firstThreePath)).measurable
      exact ((measurable_pi_iff.mpr (fun _ => hm s)).prodMk (hm (s + u))).aemeasurable
    · exact (scalarPitman_nonneg_ae W₄ (hB 0)).mono (fun p hp => hp (s + u))
    · exact Eventually.of_forall (fun p => Real.sqrt_nonneg _)
    · intro F a
      rw [scalarPitman_past_sinc_transition W₄ hB hI s u
        (fun _ : Fin 1 => s) (fun _ => le_rfl) F a,
        radial3_past_sinc_transition W₄ hB hI s u
          (fun _ : Fin 1 => s) (fun _ => le_rfl) F a]
      congr 1
      exact ((scalarPitman_radial3_identDistrib_eval W₄ hB hI s).comp
        (by fun_prop : Measurable (fun x : ℝ =>
          F (fun _ : Fin 1 => x) * Real.sinc (a * x)))).integral_eq
  exact hprod.comp (by fun_prop : Measurable
    (fun z : (Fin 1 → ℝ) × ℝ => (z.1 0, z.2)))





















end DirectedDistances.Probability
