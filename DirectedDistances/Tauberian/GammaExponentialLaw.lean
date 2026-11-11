/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.KaramataGamma
public import DirectedDistances.Tauberian.WeakCutoff
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The exponential image of the normalized Gamma law

The positive Gamma density of shape τ and rate one is normalized before it is
bundled as a probability measure. Its image under x ↦ exp(-x) is supported on
the literal unit-interval subtype. These are the actual comparison laws used
in the Laplace Tauberian desmoothing argument. -/

public section
namespace DirectedDistances.Tauberian

open MeasureTheory Set
open scoped Topology

/-- The Gamma density on its positive carrier has mass one. -/
theorem gamma_positive_density_mass {τ : ℝ} (hτ : 0 < τ) :
    (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume).withDensity
      (fun x => ENNReal.ofReal ((x : ℝ) ^ (τ - 1) * Real.exp (-(x : ℝ)) / Real.Gamma τ))
      Set.univ = 1 := by
  have hi := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp
    (gamma_density_integrable_mass_one hτ).1
  change Integrable (fun x : Ioi (0 : ℝ) =>
    (x : ℝ) ^ (τ - 1) * Real.exp (-(x : ℝ)) / Real.Gamma τ)
    (Measure.comap Subtype.val volume) at hi
  have hm := (gamma_density_integrable_mass_one hτ).2
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioi
      (fun x : ℝ => x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ), hm, ENNReal.ofReal_one]
  · exact ae_of_all _ fun x => gamma_density_nonneg hτ x.property

/-- The actual normalized Gamma(shape τ, rate one) law on positive reals. -/
@[expose] noncomputable def gammaPositiveLaw (τ : ℝ) (hτ : 0 < τ) :
    ProbabilityMeasure (Ioi (0 : ℝ)) :=
  ⟨(Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume).withDensity
    (fun x => ENNReal.ofReal ((x : ℝ) ^ (τ - 1) * Real.exp (-(x : ℝ)) / Real.Gamma τ)),
    ⟨gamma_positive_density_mass hτ⟩⟩

/-- The exponential image map has the unit interval as its actual carrier. -/
@[expose] noncomputable def expNegPositive (x : Ioi (0 : ℝ)) : Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-(x : ℝ)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr x.property.le)⟩

/-- The positive exponential image map is continuous. -/
theorem continuous_expNegPositive : Continuous expNegPositive :=
  (Real.continuous_exp.comp continuous_subtype_val.neg).subtype_mk _

/-- The actual exponential image of the normalized positive Gamma law. -/
@[expose] noncomputable def gammaExponentialLaw (τ : ℝ) (hτ : 0 < τ) :
    ProbabilityMeasure (Icc (0 : ℝ) 1) :=
  (gammaPositiveLaw τ hτ).map expNegPositive

/-- The exponential image has full mass on the strict interior `(0,1)`. -/
theorem gammaExponentialLaw_interior_mass {τ : ℝ} (hτ : 0 < τ) :
    (gammaExponentialLaw τ hτ : Measure (Icc (0 : ℝ) 1))
      {y | 0 < (y : ℝ) ∧ (y : ℝ) < 1} = 1 := by
  change (Measure.map expNegPositive (gammaPositiveLaw τ hτ : Measure (Ioi (0 : ℝ)))) _ = 1
  rw [Measure.map_apply (s := {y : Icc (0 : ℝ) 1 | 0 < (y : ℝ) ∧ (y : ℝ) < 1})
    continuous_expNegPositive.measurable
    ((isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)).measurableSet]
  have he : expNegPositive ⁻¹' {y : Icc (0 : ℝ) 1 | 0 < (y : ℝ) ∧ (y : ℝ) < 1} =
      Set.univ := by
    ext x
    change (0 < Real.exp (-(x : ℝ)) ∧ Real.exp (-(x : ℝ)) < 1) ↔ True
    exact iff_true_intro ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos x.property)⟩
  rw [he, measure_univ]

/-- Integral characterization of the positive Gamma law by its density. -/
theorem integral_gammaPositiveLaw {τ : ℝ} (hτ : 0 < τ) (f : ℝ → ℝ) :
    (∫ x : Ioi (0 : ℝ), f (x : ℝ) ∂(gammaPositiveLaw τ hτ : Measure (Ioi (0 : ℝ)))) =
      ∫ x in Ioi (0 : ℝ), (x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ) * f x := by
  change (∫ x : Ioi (0 : ℝ), f (x : ℝ) ∂
    (Measure.comap Subtype.val volume).withDensity
      (fun x => ENNReal.ofReal ((x : ℝ) ^ (τ - 1) * Real.exp (-(x : ℝ)) / Real.Gamma τ))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ x : Ioi (0 : ℝ),
        ((x : ℝ) ^ (τ - 1) * Real.exp (-(x : ℝ)) / Real.Gamma τ) * f (x : ℝ)
        ∂(Measure.comap Subtype.val volume) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change (ENNReal.ofReal _).toReal * _ = _
        rw [ENNReal.toReal_ofReal (gamma_density_nonneg hτ x.property)]
    _ = _ := integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioi
      (fun x : ℝ => (x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ) * f x)

/-- Integrals of measurable unit-interval tests against the exponential Gamma
law are the actual density-weighted exponential pullbacks. -/
theorem integral_gammaExponentialLaw {τ : ℝ} (hτ : 0 < τ)
    (f : Icc (0 : ℝ) 1 → ℝ) (hf : StronglyMeasurable f) :
    (∫ y, f y ∂(gammaExponentialLaw τ hτ : Measure (Icc (0 : ℝ) 1))) =
      ∫ x : Ioi (0 : ℝ), f (expNegPositive x)
        ∂(gammaPositiveLaw τ hτ : Measure (Ioi (0 : ℝ))) := by
  exact integral_map_of_stronglyMeasurable continuous_expNegPositive.measurable hf

/-- All natural monomial moments of the exponential Gamma law are explicit. -/
theorem integral_gammaExponentialLaw_monomial {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    (∫ y : Icc (0 : ℝ) 1, (y : ℝ) ^ k
      ∂(gammaExponentialLaw τ hτ : Measure (Icc (0 : ℝ) 1))) =
      ((k : ℝ) + 1) ^ (-τ) := by
  rw [integral_gammaExponentialLaw hτ _ (by fun_prop)]
  have he (x : Ioi (0 : ℝ)) : (expNegPositive x : ℝ) ^ k =
      Real.exp (-(k : ℝ) * (x : ℝ)) := by
    change Real.exp (-(x : ℝ)) ^ k = _
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  rw [integral_gammaPositiveLaw hτ (fun x => Real.exp (-(k : ℝ) * x))]
  convert integral_gamma_weighted_moment hτ (Nat.cast_nonneg k) using 1
  congr 1
  funext x
  ring

/-- The positive Gamma law has no point masses, as its density is with
respect to ordinary Lebesgue measure on the positive subtype. -/
theorem gammaPositiveLaw_singleton {τ : ℝ} (hτ : 0 < τ) (x : Ioi (0 : ℝ)) :
    (gammaPositiveLaw τ hτ : Measure (Ioi (0 : ℝ))) {x} = 0 := by
  apply withDensity_absolutelyContinuous _ _
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply]
  simp only [Set.image_singleton, MeasureTheory.measure_singleton]

/-- The exponential Gamma law has no atom at the desmoothing threshold. -/
theorem gammaExponentialLaw_no_atom_exp_neg_one {τ : ℝ} (hτ : 0 < τ) :
    (gammaExponentialLaw τ hτ : Measure (Icc (0 : ℝ) 1))
      {y | (y : ℝ) = Real.exp (-1)} = 0 := by
  change (Measure.map expNegPositive (gammaPositiveLaw τ hτ : Measure (Ioi (0 : ℝ)))) _ = 0
  rw [Measure.map_apply continuous_expNegPositive.measurable
    (isClosed_eq continuous_subtype_val continuous_const).measurableSet]
  have he : expNegPositive ⁻¹' {y : Icc (0 : ℝ) 1 | (y : ℝ) = Real.exp (-1)} =
      {(⟨1, zero_lt_one⟩ : Ioi (0 : ℝ))} := by
    ext x
    change (Real.exp (-(x : ℝ)) = Real.exp (-1)) ↔ x = ⟨1, zero_lt_one⟩
    rw [Real.exp_eq_exp]
    constructor
    · intro hx
      apply Subtype.ext
      linarith only [hx]
    · rintro rfl
      rfl
  rw [he, gammaPositiveLaw_singleton hτ]

/-- The desmoothing cutoff of the exponential Gamma law has its exact Gamma
normalization. All reciprocal integrands are integrable by the proved cutoff
bound on the actual unit interval law. -/
theorem integral_gammaExponentialLaw_reciprocal_cutoff {τ : ℝ} (hτ : 0 < τ) :
    (∫ y : Icc (0 : ℝ) 1,
      (if Real.exp (-1) ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0)
      ∂(gammaExponentialLaw τ hτ : Measure (Icc (0 : ℝ) 1))) =
      1 / Real.Gamma (τ + 1) := by
  rw [integral_gammaExponentialLaw hτ _
    (measurable_reciprocal_cutoff (Real.exp (-1))).stronglyMeasurable]
  have he (x : Ioi (0 : ℝ)) :
      (if Real.exp (-1) ≤ (expNegPositive x : ℝ)
        then (expNegPositive x : ℝ)⁻¹ else 0) =
      if (x : ℝ) ≤ 1 then Real.exp (x : ℝ) else 0 := by
    change (if Real.exp (-1) ≤ Real.exp (-(x : ℝ)) then
      (Real.exp (-(x : ℝ)))⁻¹ else 0) = _
    have hc : Real.exp (-1) ≤ Real.exp (-(x : ℝ)) ↔ (x : ℝ) ≤ 1 := by
      rw [Real.exp_le_exp]
      constructor <;> intro h <;> linarith only [h]
    by_cases hx : (x : ℝ) ≤ 1
    · rw [ite_eq_left (hc.mpr hx), ite_eq_left hx, Real.exp_neg, inv_inv]
    · rw [ite_eq_right (fun h => hx (hc.mp h)), ite_eq_right hx]
  simp_rw [he]
  rw [integral_gammaPositiveLaw hτ (fun x => if x ≤ 1 then Real.exp x else 0)]
  have hind (x : ℝ) :
      (x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ) *
        (if x ≤ 1 then Real.exp x else 0) =
      (Iic (1 : ℝ)).indicator (fun x => x ^ (τ - 1) / Real.Gamma τ) x := by
    by_cases hx : x ≤ 1
    · rw [ite_eq_left hx, Set.indicator_of_mem hx, Real.exp_neg]
      field_simp
    · rw [ite_eq_right hx, Set.indicator_of_notMem hx, mul_zero]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, integral_div]
  have hp : (∫ x in Ioc (0 : ℝ) 1, x ^ (τ - 1)) = 1 / τ := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith only [hτ] : -1 < τ - 1))]
    rw [sub_add_cancel, Real.one_rpow, Real.zero_rpow hτ.ne', sub_zero]
  rw [hp, Real.Gamma_add_one hτ.ne']
  field_simp

end DirectedDistances.Tauberian
