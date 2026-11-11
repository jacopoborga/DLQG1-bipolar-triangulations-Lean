/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.SDPSideExpansions
public import DirectedDistances.Paper.Section6.Tauberian
public import DirectedDistances.Tauberian.NormalizedBoundary
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import DirectedDistances.Recursive.SDPSideSelection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # SDP tails from the selected side expansions

The one-sided `F⁻` and `G` expansions below are explicit inputs from
adopted here, and these theorems do not assert the paper's printed tail
statement or constants. -/

public section
namespace DirectedDistances.Recursive

open Filter Asymptotics MeasureTheory
open DirectedDistances.Recursive.SDPExpansion
open scoped Topology

section SDP

variable {f g : ℤ → ℝ}

/-- The conditional positive `f` weight, indexed by `n ↦ n + 1`, as in the -/
@[expose] noncomputable def sdpPositiveWeight (f : ℤ → ℝ) (n : ℕ) : ℝ :=
  (2 / (1 - f 0)) * f (-((n : ℤ) + 1))

/-- The probability space underlying `X`, before applying `Nat.succ` to its
outcome. -/
@[expose] noncomputable def sdpPositiveMeasure (f : ℤ → ℝ) : Measure ℕ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (sdpPositiveWeight f n) • Measure.dirac n

/-- The conditional nonnegative `g` weight defining `Y` in -/
@[expose] noncomputable def sdpNonnegativeWeight (g : ℤ → ℝ) (n : ℕ) : ℝ :=
  g n / (1 - g (-1))

/-- The probability space carrying the nonnegative random variable `Y`. -/
@[expose] noncomputable def sdpNonnegativeMeasure (g : ℤ → ℝ) : Measure ℕ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (sdpNonnegativeWeight g n) • Measure.dirac n

/-- The selected `F⁻` expansion for `κ=0` in Proposition 6.8. The branch
coefficient is `(-1+i√3)/2`, exactly as printed in the characteristic -/
private def sdpFminusExpansion (f g : ℤ → ℝ) : Prop :=
  (fun t : ℝ =>
    negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) -
    (((-2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ) -
    ((((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
      (((g (-1)) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
      (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
  ) =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ))

/-- The selected `G` expansion for `κ=0` in Proposition 6.8, with coefficient -/
private def sdpGExpansion (g : ℤ → ℝ) : Prop :=
  (fun t : ℝ =>
    sdpCF g t - 1 -
    (((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
      (((g (-1)) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
      (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
  ) =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ))

private theorem sdp_selected_expansions_predicates_of_master
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (hκ : 3 - 6 * (g (-1)) ^ 2 - f 0 = 0) :
    sdpFminusExpansion f g ∧ sdpGExpansion g := by
  simpa [sdpFminusExpansion, sdpGExpansion] using
    sdp_kappa_zero_side_expansions_of_master
      hf hfs hg hgs hsymm hgsupp hrec hκ

private def sdpNegativeIndexEquiv : ℕ ≃ {k : ℤ // k ≤ -1} where
  toFun n := ⟨-((n : ℤ) + 1), by omega⟩
  invFun k := (-k.val - 1).toNat
  left_inv n := by simp
  right_inv k := by
    apply Subtype.ext
    have hk : 0 ≤ -k.val - 1 := by omega
    have hcast : (((-k.val - 1).toNat : ℕ) : ℤ) = -k.val - 1 :=
      Int.toNat_of_nonneg hk
    change -((((-k.val - 1).toNat : ℕ) : ℤ) + 1) = k.val
    rw [hcast]
    omega

private def sdpFromMinusOneIndexEquiv : ℕ ≃ {k : ℤ // -1 ≤ k} where
  toFun n := ⟨(n : ℤ) - 1, by omega⟩
  invFun k := (k.val + 1).toNat
  left_inv n := by simp
  right_inv k := by
    apply Subtype.ext
    have hk : 0 ≤ k.val + 1 := by omega
    have hcast : (((k.val + 1).toNat : ℕ) : ℤ) = k.val + 1 :=
      Int.toNat_of_nonneg hk
    change (((k.val + 1).toNat : ℕ) : ℤ) - 1 = k.val
    rw [hcast]
    omega

private theorem sdp_negative_nat_mass_hasSum (hf : ∀ x, 0 ≤ f x)
    (hfs : HasSum f (1 : ℝ)) (hsymm : ∀ x, f (-x) = f x) :
    HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) ((1 - f 0) / 2) := by
  have hpos : Summable (fun n : ℕ => f n) :=
    hfs.summable.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    apply hfs.summable.comp_injective
    intro a b hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  have hwhole : (∑' k : ℤ, f k) =
      (∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one hpos hneg
  have hsplit := hpos.tsum_eq_zero_add
  have hreflect : (fun n : ℕ => f (-((n : ℤ) + 1))) =
      fun n : ℕ => f ((n + 1 : ℕ) : ℤ) := by
    funext n
    have hcast : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast, hsymm]
  have htotal := hfs.tsum_eq
  rw [hwhole, hsplit, ← hreflect] at htotal
  have hmass : ∑' n : ℕ, f (-((n : ℤ) + 1)) = (1 - f 0) / 2 := by
    have htotal' : f 0 + (∑' n : ℕ, f (-((n : ℤ) + 1))) +
        ∑' n : ℕ, f (-((n : ℤ) + 1)) = 1 := by
      simpa using htotal
    linarith
  exact hmass ▸ hneg.hasSum

private theorem sdp_positive_weight_hasSum (hf : ∀ x, 0 ≤ f x)
    (hfs : HasSum f (1 : ℝ)) (hsymm : ∀ x, f (-x) = f x)
    (h0 : f 0 < 1) : HasSum (sdpPositiveWeight f) 1 := by
  have hside := sdp_negative_nat_mass_hasSum hf hfs hsymm
  have hden : 0 < 1 - f 0 := sub_pos.mpr h0
  have hcoef : (2 / (1 - f 0)) * ((1 - f 0) / 2) = 1 := by
    field_simp
  convert hside.mul_left (2 / (1 - f 0)) using 1
  · rfl
  · exact hcoef.symm

/-- `X` is a genuine probability law, with its `x` atom equal to
`2 f(x)/(1-f(0))` for `x ≥ 1`. The source uses `f(-x)=f(x)` to identify this
with the positive-indexed weight above. -/
theorem sdp_positive_measure_isProbability_of_expansions
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x) (h0 : f 0 < 1) :
    IsProbabilityMeasure (sdpPositiveMeasure f) := by
  have hden : 0 < 1 - f 0 := sub_pos.mpr h0
  apply HasSum.isProbabilityMeasure_sum_dirac
  · intro n
    dsimp [sdpPositiveWeight]
    exact mul_nonneg (div_nonneg (by norm_num) hden.le) (hf _)
  · exact sdp_positive_weight_hasSum hf hfs hsymm h0

private theorem sdp_nonnegative_weight_hasSum (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, y < -1 → g y = 0) (hq : g (-1) < 1) :
    HasSum (sdpNonnegativeWeight g) 1 := by
  have hpos : Summable (fun n : ℕ => g n) :=
    hgs.summable.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) := by
    apply hgs.summable.comp_injective
    intro a b hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  have hnegValue : (∑' n : ℕ, g (-((n : ℤ) + 1))) = g (-1) := by
    apply tsum_eq_single 0
    · intro n hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hidx : -((n : ℤ) + 1) < -1 := by omega
      have hzero := hgsupp _ hidx
      simpa only [hzero]
  have hwhole : (∑' k : ℤ, g k) =
      (∑' n : ℕ, g n) + ∑' n : ℕ, g (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one hpos hneg
  have htotal := hgs.tsum_eq
  rw [hwhole, hnegValue] at htotal
  have hposValue : (∑' n : ℕ, g n) = 1 - g (-1) := by linarith
  have hscaled := hpos.hasSum.mul_left (1 / (1 - g (-1)))
  have hden : 0 < 1 - g (-1) := sub_pos.mpr hq
  have hcoef : (1 / (1 - g (-1))) * (1 - g (-1)) = 1 := by
    field_simp
  convert hscaled using 1
  · funext n
    simp only [sdpNonnegativeWeight, div_eq_mul_inv]
    ring
  · rw [hposValue]
    exact hcoef.symm

/-- The law of `Y`, whose atom at `y ≥ 0` is `g(y)/(1-g(-1))`. -/
theorem sdp_nonnegative_measure_isProbability_of_expansions
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, y < -1 → g y = 0) (hq : g (-1) < 1) :
    IsProbabilityMeasure (sdpNonnegativeMeasure g) := by
  have hden : 0 < 1 - g (-1) := sub_pos.mpr hq
  apply HasSum.isProbabilityMeasure_sum_dirac
  · intro n
    dsimp [sdpNonnegativeWeight]
    exact div_nonneg (hg n) hden.le
  · exact sdp_nonnegative_weight_hasSum hgs hgsupp hq

/-- Atoms of the positive-increment law have the source normalization. -/
theorem sdp_positive_measure_atom_of_expansions
    (hf : ∀ x, 0 ≤ f x) (hsymm : ∀ x, f (-x) = f x) (h0 : f 0 < 1)
    (x : ℕ) (hx : 1 ≤ x) :
    ((sdpPositiveMeasure f).map Nat.succ).real {x} =
      2 * f (x : ℤ) / (1 - f 0) := by
  rw [Measure.real, Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpre : Nat.succ ⁻¹' ({x} : Set ℕ) = {x - 1} := by
    ext n
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [hpre, sdpPositiveMeasure, Measure.sum_smul_dirac_singleton]
  have hidx : -((((x - 1 : ℕ) : ℤ) + 1)) = -(x : ℤ) := by omega
  have hden : 0 < 1 - f 0 := sub_pos.mpr h0
  have hw : 0 ≤ sdpPositiveWeight f (x - 1) := by
    dsimp [sdpPositiveWeight]
    exact mul_nonneg (div_nonneg (by norm_num) hden.le) (hf _)
  rw [ENNReal.toReal_ofReal hw, sdpPositiveWeight, hidx, hsymm]
  field_simp [ne_of_gt hden]
  <;> ring

private theorem sdp_negativeCF_neg_eq_star (f : ℤ → ℝ) (t : ℝ) :
    negativeCF f (-t) = star (negativeCF f t) := by
  unfold negativeCF
  rw [Complex.star_def, Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp only [Complex.conj_I, Complex.ofReal_neg, neg_mul]
  ring

private theorem sdpCF_neg_eq_star (g : ℤ → ℝ) (t : ℝ) :
    sdpCF g (-t) = star (sdpCF g t) := by
  unfold sdpCF
  rw [Complex.star_def, Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp only [Complex.conj_I, Complex.ofReal_neg, neg_mul]
  ring

private theorem sdp_positive_characteristic (hf : ∀ x, 0 ≤ f x)
    (hfs : HasSum f (1 : ℝ)) (h0 : f 0 < 1) (t : ℝ) :
    (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂sdpPositiveMeasure f) =
      (((2 / (1 - f 0) : ℝ) : ℂ) * negativeCF f (-t)) := by
  have hc (n : ℕ) : ENNReal.ofReal (sdpPositiveWeight f n) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hden : 0 < 1 - f 0 := by linarith
  change (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂Measure.sum (fun n : ℕ =>
        ENNReal.ofReal (sdpPositiveWeight f n) • Measure.dirac n)) = _
  have hsubsum : Summable (fun k : {k : ℤ // k ≤ -1} =>
      (f k.val : ℂ) * Complex.exp ((((-t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I))) := by
    apply Summable.of_norm_bounded (hfs.summable.subtype (fun k : ℤ => k ≤ -1))
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hf k.val), Complex.norm_exp_ofReal_mul_I, mul_one]
    simp only [Function.comp_apply]
    exact le_rfl
  have hsub : HasSum (fun k : {k : ℤ // k ≤ -1} =>
      (f k.val : ℂ) * Complex.exp ((((-t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I)))
      (negativeCF f (-t)) := by
    change HasSum _ (∑' k : {k : ℤ // k ≤ -1}, _)
    exact hsubsum.hasSum
  have hnat := sdpNegativeIndexEquiv.hasSum_iff.mpr hsub
  have hscaled := hnat.mul_left (((2 / (1 - f 0) : ℝ) : ℂ))
  have hseries : HasSum (fun n : ℕ =>
      (sdpPositiveWeight f n : ℂ) *
        Complex.exp ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))
      (((2 / (1 - f 0) : ℝ) : ℂ) * negativeCF f (-t)) := by
    convert hscaled using 1
    · funext n
      simp only [Function.comp_apply, sdpNegativeIndexEquiv, Equiv.coe_fn_mk,
        sdpPositiveWeight]
      push_cast
      ring
  calc
    (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂Measure.sum (fun n : ℕ =>
        ENNReal.ofReal (sdpPositiveWeight f n) • Measure.dirac n)) =
      ∑' n : ℕ, (sdpPositiveWeight f n : ℂ) *
        Complex.exp ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) := by
          rw [integral_sum_dirac hc]
          apply tsum_congr
          intro n
          have hw : 0 ≤ sdpPositiveWeight f n := by
            dsimp [sdpPositiveWeight]
            exact mul_nonneg (div_nonneg (by norm_num) hden.le) (hf _)
          rw [ENNReal.toReal_ofReal hw]
          simp only [Complex.real_smul]
    _ = ((2 / (1 - f 0) : ℝ) : ℂ) * negativeCF f (-t) := hseries.tsum_eq

private theorem sdp_nonnegative_characteristic (hg : ∀ y, 0 ≤ g y)
    (hgs : HasSum g (1 : ℝ)) (hgsupp : ∀ y, y < -1 → g y = 0)
    (hq : g (-1) < 1) (t : ℝ) :
    (∫ n : ℕ, Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂sdpNonnegativeMeasure g) =
      (((1 / (1 - g (-1)) : ℝ) : ℂ) *
        (sdpCF g t - (g (-1) : ℂ) *
          Complex.exp ((((-t : ℝ) : ℂ) * Complex.I)))) := by
  have hc (n : ℕ) : ENNReal.ofReal (sdpNonnegativeWeight g n) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hden : 0 < 1 - g (-1) := sub_pos.mpr hq
  change (∫ n : ℕ, Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂Measure.sum (fun n : ℕ =>
        ENNReal.ofReal (sdpNonnegativeWeight g n) • Measure.dirac n)) = _
  have hposSum : Summable (fun n : ℕ => (g n : ℂ) *
      Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))) := by
    apply Summable.of_norm_bounded (hgs.summable.comp_injective Nat.cast_injective)
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hg n), Complex.norm_exp_ofReal_mul_I, mul_one]
    simp only [Function.comp_apply]
    exact le_rfl
  have hsub : Summable (fun k : {k : ℤ // -1 ≤ k} =>
      (g k.val : ℂ) * Complex.exp ((((t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I))) := by
    apply Summable.of_norm_bounded (hgs.summable.subtype (fun k : ℤ => -1 ≤ k))
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hg k.val), Complex.norm_exp_ofReal_mul_I, mul_one]
    simp only [Function.comp_apply]
    exact le_rfl
  have hnat0 := sdpFromMinusOneIndexEquiv.hasSum_iff.mpr hsub.hasSum
  have hnat : HasSum (fun n : ℕ => (g ((n : ℤ) - 1) : ℂ) *
      Complex.exp ((((t * (((n : ℤ) - 1) : ℝ) : ℝ) : ℂ) * Complex.I)))
      (∑' k : {k : ℤ // -1 ≤ k},
        (g k.val : ℂ) * Complex.exp ((((t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I))) := by
    convert hnat0 using 1
    funext n
    simp [sdpFromMinusOneIndexEquiv]
  have hsplit := hnat.summable.tsum_eq_zero_add
  have hshift : sdpCF g t =
      (g (-1) : ℂ) * Complex.exp ((((-t : ℝ) : ℂ) * Complex.I)) +
        ∑' n : ℕ, (g n : ℂ) *
          Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    calc
      sdpCF g t = ∑' n : ℕ, (g (((n : ℤ) - 1)) : ℂ) *
          Complex.exp ((((t * (((n : ℤ) - 1) : ℝ) : ℝ) : ℂ) * Complex.I)) :=
            by
              change (∑' k : {k : ℤ // -1 ≤ k},
                (g k.val : ℂ) * Complex.exp
                  ((((t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I))) = _
              exact hnat.tsum_eq.symm
      _ = _ := by
        calc
          _ = (fun n : ℕ =>
              (g (((n : ℤ) - 1)) : ℂ) *
                Complex.exp ((((t * (((n : ℤ) - 1) : ℝ) : ℝ) : ℂ) * Complex.I))) 0 +
              ∑' n : ℕ, (fun m : ℕ =>
                (g (((m : ℤ) - 1)) : ℂ) *
                  Complex.exp ((((t * (((m : ℤ) - 1) : ℝ) : ℝ) : ℂ) * Complex.I))) (n + 1) :=
                hsplit
          _ = (g (-1) : ℂ) * Complex.exp ((((-t : ℝ) : ℂ) * Complex.I)) +
              ∑' n : ℕ, (g n : ℂ) *
                Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
                  congr 1
                  · simp [sdpFromMinusOneIndexEquiv]
                  · apply tsum_congr
                    intro n
                    simp [sdpFromMinusOneIndexEquiv]
  have hscaled : (∑' n : ℕ, (sdpNonnegativeWeight g n : ℂ) *
      Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))) =
      (((1 / (1 - g (-1)) : ℝ) : ℂ) *
        ∑' n : ℕ, (g n : ℂ) *
          Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hw : sdpNonnegativeWeight g n =
        (1 / (1 - g (-1))) * g n := by
      dsimp [sdpNonnegativeWeight]
      field_simp [ne_of_gt hden]
      <;> ring
    rw [hw]
    push_cast
    ring
  calc
    (∫ n : ℕ, Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂Measure.sum (fun n : ℕ =>
        ENNReal.ofReal (sdpNonnegativeWeight g n) • Measure.dirac n)) =
      ∑' n : ℕ, (sdpNonnegativeWeight g n : ℂ) *
        Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
          rw [integral_sum_dirac hc]
          apply tsum_congr
          intro n
          have hw : 0 ≤ sdpNonnegativeWeight g n := by
            dsimp [sdpNonnegativeWeight]
            exact div_nonneg (hg n) hden.le
          rw [ENNReal.toReal_ofReal hw]
          simp only [Complex.real_smul]
    _ = _ := by rw [hscaled, hshift]; ring

private theorem littleO_star {F : ℝ → ℂ} {G : ℝ → ℝ} {l : Filter ℝ}
    (h : F =o[l] G) : (fun t => star (F t)) =o[l] G := by
  rw [isLittleO_iff] at h ⊢
  intro ε hε
  filter_upwards [h (c := ε) hε] with t ht
  simpa only [norm_star] using ht

private theorem littleO_extend_conjugate {φ : ℝ → ℂ} {c : ℂ} {ν : ℝ}
    (hpos : (fun t : ℝ => φ t - 1 - c * (((t ^ ν : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ ν))
    (hconj : ∀ t : ℝ, φ (-t) = star (φ t)) :
    (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))
      ) =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) := by
  have hpos' : (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ)) ) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    apply hpos.congr'
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htp : 0 < t := Set.mem_Ioi.mp ht
      simp [htp, abs_of_pos htp]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact congrArg (fun r : ℝ => r ^ ν) (abs_of_pos (Set.mem_Ioi.mp ht)).symm
  have hnegMap : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    have hcont : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero] using
        ((continuous_neg.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          nhdsWithin_le_nhds)
    refine ⟨hcont, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact neg_pos.mpr (Set.mem_Iio.mp ht)
  have hnegComp := hpos.comp_tendsto hnegMap
  have hnegStar : (fun t : ℝ => star
      ((φ (-t) - 1 - c * ((((-t) ^ ν : ℝ) : ℂ)))) ) =o[𝓝[<] (0 : ℝ)]
      (fun t : ℝ => ((-t) ^ ν)) := littleO_star hnegComp
  have hneg : (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))) =o[𝓝[<] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    apply hnegStar.congr'
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htn : t < 0 := Set.mem_Iio.mp ht
      have hsym' : φ t = star (φ (-t)) := by
        simpa only [neg_neg] using hconj (-t)
      calc
        star (φ (-t) - 1 - c * ((((-t) ^ ν : ℝ) : ℂ))) =
            star (φ (-t)) - 1 - (star c) * (((|t| ^ ν : ℝ) : ℂ)) := by
              simp [abs_of_neg htn]
        _ = φ t - 1 - (star c) * (((|t| ^ ν : ℝ) : ℂ)) := by rw [← hsym']
        _ = φ t - 1 - (if 0 < t then c else star c) *
              (((|t| ^ ν : ℝ) : ℂ)) := by simp [not_lt.mpr htn.le]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [abs_of_neg (Set.mem_Iio.mp ht)]
  have hfilter : 𝓝[<] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ) = 𝓝[≠] (0 : ℝ) := by
    rw [← nhdsWithin_union]
    congr 1
    ext t
    simp [Set.mem_Iio, Set.mem_Ioi]
  rw [← hfilter]
  exact hneg.sup hpos'

private theorem littleO_extend_conjugate_linear {φ : ℝ → ℂ} {c : ℂ}
    {c₁ ν : ℝ}
    (hpos : (fun t : ℝ => φ t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      c * (((t ^ ν : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ ν))
    (hconj : ∀ t : ℝ, φ (-t) = star (φ t)) :
    (fun t : ℝ => φ t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))) =o[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
  let ψ : ℝ → ℂ := fun t => φ t - ((c₁ : ℂ) * Complex.I) * (t : ℂ)
  have hposψ : (fun t : ℝ => ψ t - 1 - c * (((t ^ ν : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ ν) := by
    convert hpos using 1
    funext t
    dsimp [ψ]
    ring
  have hconjψ (t : ℝ) : ψ (-t) = star (ψ t) := by
    dsimp [ψ]
    rw [hconj t]
    simp only [Complex.star_def, map_sub, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.ofReal_neg]
    ring
  have hout := littleO_extend_conjugate hposψ hconjψ
  convert hout using 1
  funext t
  dsimp [ψ]
  ring

/-- The exact selected `F⁻` expansion and the law of `X` imply its
characteristic expansion with `c₁=4g(-1)^2/(1-f(0))` and
no correction is adopted and the coefficients here are not the paper's
printed tail statement. `eq:asympt-exp`, -/
private theorem sdp_positive_characteristic_expansion_of_expansions
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x) (h0 : f 0 < 1)
    (hq : 0 < g (-1))
    (hFminus : sdpFminusExpansion f g) :
    let c₁ : ℝ := 4 * (g (-1)) ^ 2 / (1 - f 0)
    let c₂ : ℂ := (((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) *
      (((g (-1)) ^ (2 / 3 : ℝ) : ℝ) : ℂ)) / (1 - f 0 : ℝ)
    (fun t : ℝ =>
      (∫ n : ℕ, Complex.exp
        ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
        ∂sdpPositiveMeasure f) - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c₂ else star c₂) *
        (((|t| ^ (4 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ (4 / 3 : ℝ)) := by
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  let dF : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let dG : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let den : ℝ := 1 - f 0
  let scale : ℝ := 2 / den
  let c₁ : ℝ := 4 * (g (-1)) ^ 2 / den
  let c₂ : ℂ := (((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) *
    (b : ℂ)) / (den : ℝ)
  dsimp only [c₁, c₂]
  have hbase : (((1 - f 0) / 2 : ℝ) : ℂ) * (scale : ℂ) = 1 := by
    have hreal : ((1 - f 0) / 2) * (2 / (1 - f 0)) = 1 := by
      field_simp [ne_of_gt (sub_pos.mpr h0)]
    exact_mod_cast hreal
  have hbase' : (scale : ℂ) * ((1 - (f 0 : ℂ)) / 2) = 1 := by
    have h := hbase
    push_cast at h
    calc
      (scale : ℂ) * ((1 - (f 0 : ℂ)) / 2) =
          ((1 - (f 0 : ℂ)) / 2) * (scale : ℂ) := by ring
      _ = 1 := h
  have hden : den ≠ 0 := by dsimp [den]; linarith
  have hdenpos : 0 < den := by dsimp [den]; linarith
  have hc₁ : ((scale : ℝ) : ℂ) *
      (((2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I) =
      (c₁ : ℂ) * Complex.I := by
    dsimp [scale, den, c₁]
    push_cast
    field_simp [hden]
    <;> ring
  have hFco : ((scale : ℝ) : ℂ) * star
      (((((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
        (b : ℂ))) = c₂ := by
    dsimp [scale, den, c₂, b]
    simp [Complex.star_def]
    norm_num
    have hstarTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      exact map_ofNat (starRingEnd ℂ) 2
    rw [hstarTwo]
    push_cast
    field_simp [hden]
    <;> ring
  have hstar := littleO_star hFminus
  have hstar' : (fun t : ℝ => star (negativeCF f t) -
      (((1 - f 0) / 2 : ℝ) : ℂ) -
      (((2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ) -
      (dG * (b : ℂ)) * (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
    convert hstar using 1
    funext t
    simp [dG, b, map_sub, map_mul, Complex.star_def]
    <;> ring
  have hscaled := hstar'.const_smul_left (scale : ℂ)
  have hpos : (fun t : ℝ =>
      ((scale : ℂ) * star (negativeCF f t)) - 1 -
        ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
        c₂ * (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
    apply hscaled.congr'
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change (scale : ℂ) *
        (star (negativeCF f t) - (((1 - f 0) / 2 : ℝ) : ℂ) -
          (((2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ) -
          (dG * (b : ℂ)) * (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) = _
      calc
        _ = (scale : ℂ) * star (negativeCF f t) -
              (scale : ℂ) * (((1 - f 0) / 2 : ℂ)) -
              ((scale : ℂ) * (((2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I)) *
                (t : ℂ) -
              ((scale : ℂ) * (dG * (b : ℂ))) *
                (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) := by
          push_cast
          ring
        _ = _ := by
          rw [hbase', hc₁]
          have hFco' : (scale : ℂ) * (dG * (b : ℂ)) = c₂ := by
            have hd : star dF = dG := by
              simp [dF, dG, Complex.star_def]
              <;> ring
            have hb : star (b : ℂ) = (b : ℂ) := by
              exact Complex.conj_ofReal b
            have hstarco : star (dF * (b : ℂ)) = dG * (b : ℂ) := by
              rw [star_mul, hd, hb]
              ring
            calc
              (scale : ℂ) * (dG * (b : ℂ)) =
                  (scale : ℂ) * star (dF * (b : ℂ)) := by
                rw [hstarco]
              _ = c₂ := hFco
          rw [hFco']
    · exact Filter.Eventually.of_forall fun _ => rfl
  let φ : ℝ → ℂ := fun t => ∫ n : ℕ, Complex.exp
    ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) ∂sdpPositiveMeasure f
  have hchar (t : ℝ) : φ t = ((scale : ℂ) * star (negativeCF f t)) := by
    dsimp [φ, scale, den]
    rw [sdp_positive_characteristic hf hfs h0 t, sdp_negativeCF_neg_eq_star]
    rw [← starRingEnd_apply]
  have hposφ : (fun t : ℝ => φ t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      c₂ * (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
    convert hpos using 1
    funext t
    rw [hchar]
  have hconj (t : ℝ) : φ (-t) = star (φ t) := by
    rw [hchar (-t), hchar t, sdp_negativeCF_neg_eq_star]
    simp only [star_mul, star_star]
    have hscale : star (scale : ℂ) = (scale : ℂ) := by
      simp [Complex.star_def]
    rw [hscale]
    ring
  simpa only [φ] using littleO_extend_conjugate_linear hposφ hconj

private theorem sdp_g_nat_mass_hasSum (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, y < -1 → g y = 0) :
    HasSum (fun n : ℕ => g n) (1 - g (-1)) := by
  have hpos : Summable (fun n : ℕ => g n) :=
    hgs.summable.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) := by
    apply hgs.summable.comp_injective
    intro a b hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  have hnegValue : (∑' n : ℕ, g (-((n : ℤ) + 1))) = g (-1) := by
    apply tsum_eq_single 0
    · intro n hn
      have hidx : -((n : ℤ) + 1) < -1 := by omega
      have hzero := hgsupp _ hidx
      simpa only [hzero]
  have hwhole : (∑' k : ℤ, g k) =
      (∑' n : ℕ, g n) + ∑' n : ℕ, g (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one hpos hneg
  have htotal := hgs.tsum_eq
  rw [hwhole, hnegValue] at htotal
  have hmass : ∑' n : ℕ, g n = 1 - g (-1) := by linarith
  exact hmass ▸ hpos.hasSum

private theorem sdp_integral_id_of_sum (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (t : ℝ) :
    (∫ n : ℕ, Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂Measure.sum (fun n : ℕ => ENNReal.ofReal (w n) • Measure.dirac n)) =
      ∑' n : ℕ, (w n : ℂ) * Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  have hc (n : ℕ) : ENNReal.ofReal (w n) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [integral_sum_dirac hc]
  apply tsum_congr
  intro n
  simp only [ENNReal.toReal_ofReal (hw n), Complex.real_smul]

private theorem sdp_nonnegative_measure_tail_tsum (hg : ∀ y, 0 ≤ g y)
    (hq : g (-1) < 1) (R : ℝ) :
    (sdpNonnegativeMeasure g).real {n : ℕ | R < (n : ℝ)} =
      ∑' n : ℕ, if R < (n : ℝ) then sdpNonnegativeWeight g n else 0 := by
  simp only [Measure.real, sdpNonnegativeMeasure, Measure.sum_apply_of_countable,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    mul_ite, Pi.one_apply, mul_one, mul_zero]
  rw [ENNReal.tsum_toReal_eq (by intro n; split_ifs <;> simp)]
  apply tsum_congr
  intro n
  by_cases hn : R < (n : ℝ)
  · have hw : 0 ≤ sdpNonnegativeWeight g n := by
      dsimp [sdpNonnegativeWeight]
      exact div_nonneg (hg n) (sub_nonneg.mpr hq.le)
    simp [hn, ENNReal.toReal_ofReal hw]
  · simp [hn]

/-- The selected `G` expansion and normalization of the `Y` law imply the
characteristic expansion with `c₁=g(-1)/(1-g(-1))` and
no correction is adopted, and these coefficients do not assert the paper's
printed tail constants. `eq:asympt-exp`, -/
private theorem sdp_nonnegative_characteristic_expansion_of_expansions
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, y < -1 → g y = 0) (hq : 0 < g (-1))
    (hq1 : g (-1) < 1)
    (hG : sdpGExpansion g) :
    let c₁ : ℝ := g (-1) / (1 - g (-1))
    let c₂ : ℂ := (((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
      (((g (-1)) ^ (2 / 3 : ℝ) : ℝ) : ℂ) / (1 - g (-1) : ℝ)
    (fun t : ℝ =>
      (∫ n : ℕ, Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))
        ∂sdpNonnegativeMeasure g) - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c₂ else star c₂) *
        (((|t| ^ (4 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ (4 / 3 : ℝ)) := by
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  let d : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let den : ℝ := 1 - g (-1)
  let scale : ℝ := 1 / den
  let c₁ : ℝ := g (-1) / den
  let c₂ : ℂ := d * (b : ℂ) / (den : ℝ)
  dsimp only [c₁, c₂]
  have hden : 0 < den := by dsimp [den]; linarith
  have hdenNe : den ≠ 0 := hden.ne'
  have hExp := DirectedDistances.Tauberian.exp_angle_linear_error_isLittleO
    (by norm_num : (1 / 3 : ℝ) < 1)
  have hExpStar := littleO_star hExp
  have hExpPos : (fun t : ℝ =>
      Complex.exp (((-t : ℝ) : ℂ) * Complex.I) - 1 +
        ((t : ℂ) * Complex.I)) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
    rw [isLittleO_iff] at hExpStar ⊢
    intro ε hε
    have hevent := (hExpStar (c := ε) hε).filter_mono (nhdsGT_le_nhdsNE 0)
    filter_upwards [hevent, self_mem_nhdsWithin] with t ht hmem
    have htpos : 0 < t := Set.mem_Ioi.mp hmem
    have hfun : star (Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I) =
        Complex.exp (((-t : ℝ) : ℂ) * Complex.I) - 1 + (t : ℂ) * Complex.I := by
      simp only [Complex.star_def, map_sub, map_mul, Complex.conj_ofReal,
        Complex.conj_I, ← Complex.exp_conj, Complex.ofReal_neg, neg_mul, neg_neg, map_one]
      ring
    rw [hfun, abs_of_pos htpos] at ht
    have hexp : (1 : ℝ) + 1 / 3 = 4 / 3 := by norm_num
    simpa only [hexp] using ht
  have hGerr : (fun t : ℝ => sdpCF g t - 1 - (d * (b : ℂ)) *
      (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
    delta sdpGExpansion at hG
    simpa [b, d] using hG
  have hExpErr := hExpPos.const_smul_left (g (-1) : ℂ)
  have hnum := hGerr.sub hExpErr
  have hscaled := hnum.const_smul_left (scale : ℂ)
  have hbase : ((g (-1) : ℂ) * (scale : ℂ)) =
      (c₁ : ℂ) := by
    dsimp [scale, c₁, den]
    push_cast
    field_simp [hdenNe]
    <;> ring
    <;> simp
  have hcoeff : ((d * (b : ℂ)) * (scale : ℂ)) = c₂ := by
    dsimp [c₂, scale]
    change (d * (b : ℂ)) * ((1 / den : ℝ) : ℂ) =
      (d * (b : ℂ)) / (den : ℝ)
    rw [Complex.ofReal_div]
    field_simp [hdenNe]
    <;> ring
    <;> simp
  have hbase' : (scale : ℂ) * (g (-1) : ℂ) = c₁ := by
    calc
      _ = (g (-1) : ℂ) * (scale : ℂ) := by ring
      _ = c₁ := hbase
  have hcoeff' : (scale : ℂ) * (d * (b : ℂ)) = c₂ := by
    calc
      _ = (d * (b : ℂ)) * (scale : ℂ) := by ring
      _ = c₂ := hcoeff
  have hnorm : (scale : ℂ) * (1 - (g (-1) : ℂ)) = 1 := by
    dsimp [scale, den]
    push_cast
    have hdenC : (1 - (g (-1) : ℂ)) ≠ 0 := by exact_mod_cast hdenNe
    field_simp [hdenC]
  have hpos : (fun t : ℝ =>
      ((scale : ℂ) * (sdpCF g t - (g (-1) : ℂ) *
        Complex.exp ((((-t : ℝ) : ℂ) * Complex.I)))) - 1 -
      ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      c₂ * (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
    apply hscaled.congr'
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change (scale : ℂ) *
        (sdpCF g t - 1 - (d * (b : ℂ)) *
          (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) -
          (g (-1) : ℂ) *
            (Complex.exp (((-t : ℝ) : ℂ) * Complex.I) - 1 +
              (t : ℂ) * Complex.I)) = _
      calc
        _ = (scale : ℂ) * sdpCF g t -
              (scale : ℂ) * (1 - (g (-1) : ℂ)) -
              ((scale : ℂ) * (g (-1) : ℂ)) *
                Complex.exp (((-t : ℝ) : ℂ) * Complex.I) -
              ((scale : ℂ) * (g (-1) : ℂ) * Complex.I) * (t : ℂ) -
              ((scale : ℂ) * (d * (b : ℂ))) *
                (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) := by ring
        _ = _ := by
          rw [hnorm, hbase', hcoeff']
          linear_combination
            (Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) * hbase'
    · exact Filter.Eventually.of_forall fun _ => rfl
  let φ : ℝ → ℂ := fun t => ∫ n : ℕ,
    Complex.exp ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I)) ∂sdpNonnegativeMeasure g
  have hchar (t : ℝ) : φ t = (scale : ℂ) *
      (sdpCF g t - (g (-1) : ℂ) *
        Complex.exp ((((-t : ℝ) : ℂ) * Complex.I))) := by
    dsimp [φ, scale, den]
    exact sdp_nonnegative_characteristic hg hgs hgsupp hq1 t
  have hposφ : (fun t : ℝ => φ t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      c₂ * (((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
    convert hpos using 1
    funext t
    rw [hchar]
  have hconj (t : ℝ) : φ (-t) = star (φ t) := by
    rw [hchar (-t), hchar t, sdpCF_neg_eq_star, neg_neg]
    have hexp : star (Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) =
        Complex.exp ((t : ℂ) * Complex.I) := by
      simp [Complex.star_def, ← Complex.exp_conj]
    have hscale : star (scale : ℂ) = (scale : ℂ) := by
      simp [Complex.star_def]
    have hg : star (g (-1) : ℂ) = (g (-1) : ℂ) := by
      simp [Complex.star_def]
    rw [star_mul, hscale, star_sub, star_mul, hg, hexp]
    ring
  simpa only [φ] using littleO_extend_conjugate_linear hposφ hconj

private theorem sdp_gamma_reflection_thirds :
    Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) =
      2 * Real.pi / Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
  have harg : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  have hpi : Real.pi * (1 / 3 : ℝ) = Real.pi / 3 := by ring
  rw [harg, hpi, Real.sin_pi_div_three] at h
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  calc
    Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) =
        Real.pi / (Real.sqrt 3 / 2) := h
    _ = 2 * Real.pi / Real.sqrt 3 := by
      field_simp [ne_of_gt hsqrt]
      <;> ring

/-- `X` with coefficient `√3 Γ(1/3) g(-1)^(2/3)/(3π(1-f(0)))`.
and the coefficient is not the paper's printed one. -/
private theorem sdp_positive_measure_tail_asymptotic_of_expansions
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x) (h0 : f 0 < 1) (hq : 0 < g (-1))
    (hFminus : sdpFminusExpansion f g) :
    (fun R : ℝ => (sdpPositiveMeasure f).real
      {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
        (Real.sqrt 3 * Real.Gamma (1 / 3 : ℝ) *
          ((g (-1)) ^ (2 / 3 : ℝ)) /
            (3 * Real.pi * (1 - f 0))) * R ^ (-(4 / 3 : ℝ))) =o[atTop]
      (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) := by
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  let den : ℝ := 1 - f 0
  let c₁ : ℝ := 4 * (g (-1)) ^ 2 / den
  let c₂ : ℂ := (((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) *
    (b : ℂ)) / (den : ℝ)
  change (fun R : ℝ => (sdpPositiveMeasure f).real
      {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
        (Real.sqrt 3 * Real.Gamma (1 / 3 : ℝ) * b /
            (3 * Real.pi * den)) * R ^ (-(4 / 3 : ℝ))) =o[atTop]
      (fun R : ℝ => R ^ (-(4 / 3 : ℝ)))
  have hden : 0 < den := by dsimp [den]; linarith
  have hb : 0 < b := Real.rpow_pos_of_pos hq _
  have hzero : f 0 < 1 := h0
  letI : IsProbabilityMeasure (sdpPositiveMeasure f) :=
    sdp_positive_measure_isProbability_of_expansions hf hfs hsymm h0
  have hchar := sdp_positive_characteristic_expansion_of_expansions
    hf hfs hsymm h0 hq hFminus
  have hcRe : c₂.im = -(Real.sqrt 3 * b / den) := by
    dsimp [c₂]
    rw [Complex.div_ofReal_im, Complex.mul_im]
    simp
    field_simp [hden.ne']
    <;> ring
  have hcne : c₂.im ≠ 0 := by rw [hcRe]; exact neg_ne_zero.mpr (div_pos (by positivity) hden).ne'
  have hc₁ : 0 < c₁ := by
    dsimp [c₁]
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hq)) hden
  have hcase := (DirectedDistances.Paper.Section6.tauberian_characteristic
    ℕ (sdpPositiveMeasure f) Nat.succ (by fun_prop)).2
  have hexp : (1 : ℝ) + 1 / 3 = 4 / 3 := by norm_num
  have hresult := hcase c₁ hc₁ c₂ hcne (1 / 3 : ℝ) (by norm_num) (by norm_num) (by
    simpa only [c₁, c₂, den, b, Complex.star_def, Nat.succ_eq_add_one, hexp] using hchar)
  have hconst : -(((1 / 3 : ℝ) * c₂.im) / Real.Gamma (1 - (1 / 3 : ℝ))) /
      Real.cos (Real.pi * (1 / 3 : ℝ) / 2) =
      Real.sqrt 3 * Real.Gamma (1 / 3 : ℝ) * b /
        (3 * Real.pi * den) := by
    rw [hcRe, show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
      show Real.cos (Real.pi * (1 / 3 : ℝ) / 2) = Real.sqrt 3 / 2 by
        rw [show Real.pi * (1 / 3 : ℝ) / 2 = Real.pi / 6 by ring,
          Real.cos_pi_div_six]]
    have hGamma : Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) =
        2 * Real.pi / Real.sqrt 3 := sdp_gamma_reflection_thirds
    have hsqrtpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hGamma' : Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) *
        Real.sqrt 3 = 2 * Real.pi := by
      rw [hGamma]
      field_simp [hsqrtpos.ne']
    have hGpos : 0 < Real.Gamma (2 / 3 : ℝ) :=
      Real.Gamma_pos_of_pos (by norm_num)
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hden.ne', hGpos.ne', hpi]
    rw [← hGamma']
    ring
  have htail := hresult.2.2
  have hexpR : -(1 / 3 : ℝ) - 1 = -(4 / 3 : ℝ) := by norm_num
  rw [hconst] at htail
  simpa only [Nat.succ_eq_add_one, hexpR] using htail

/-- The absolute tail of the symmetric `f` increment is the unconditioned
version of the preceding `X` tail. Its coefficient is
is adopted, and this is not the paper's printed constant. -/
theorem sdp_f_absolute_tail_asymptotic_of_master
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (hκ : 3 - 6 * (g (-1)) ^ 2 - f 0 = 0) :
    (fun R : ℝ => (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
      (Real.Gamma (1 / 3 : ℝ) * ((g (-1)) ^ (2 / 3 : ℝ)) /
        (Real.sqrt 3 * Real.pi)) *
          R ^ (-(4 / 3 : ℝ))) =o[atTop] (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) := by
  obtain ⟨h0, hq⟩ := sdp_side_nondegenerate_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  have hFminus := (sdp_selected_expansions_predicates_of_master
    hf hfs hg hgs hsymm hgsupp hrec hκ).1
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  let den : ℝ := 1 - f 0
  let a : ℝ := Real.sqrt 3 * Real.Gamma (1 / 3 : ℝ) * b /
    (3 * Real.pi * den)
  letI : IsProbabilityMeasure (sdpPositiveMeasure f) :=
    sdp_positive_measure_isProbability_of_expansions hf hfs hsymm h0
  have hmeasure := sdp_positive_measure_tail_asymptotic_of_expansions
    hf hfs hsymm h0 hq hFminus
  have hscaled : (fun R : ℝ => den *
      ((sdpPositiveMeasure f).real
        {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} - a * R ^ (-(4 / 3 : ℝ)))) =o[atTop]
        (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) := by
    convert hmeasure.const_mul_left den using 1 <;> simp [a, den] <;> ring
  have hbridge (R : ℝ) (hR : 0 ≤ R) :
      (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) =
        den * (sdpPositiveMeasure f).real
          {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} := by
    let q : ℤ → ℝ := {x : ℤ | R < |(x : ℝ)|}.indicator f
    have hqEven : q.Even := by
      intro x
      simp [q, Set.indicator_apply, Set.mem_setOf_eq, abs_neg, hsymm]
    have hqSummable : Summable q := by
      change Summable ({x : ℤ | R < |(x : ℝ)|}.indicator f)
      exact hfs.summable.indicator _
    have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat (f := q) hqEven hqSummable
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => q n)] at hsplit
    have hsplit' : (∑' x : ℤ, q x) =
        q 0 + 2 • (∑' n : ℕ, q ((n : ℤ) + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hsplit
    have hq0 : q 0 = 0 := by simp [q, hR]
    have hpos : (∑' n : ℕ, q ((n : ℤ) + 1)) =
        ∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then
          f (-((n + 1 : ℕ) : ℤ)) else 0 := by
      apply tsum_congr
      intro n
      have hidx : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
      calc
        q ((n : ℤ) + 1) = q ((n + 1 : ℕ) : ℤ) := congrArg q hidx.symm
        _ = if R < ((n + 1 : ℕ) : ℝ) then
              f (-((n + 1 : ℕ) : ℤ)) else 0 := by
          have hnonneg : 0 ≤ (((n + 1 : ℕ) : ℤ) : ℝ) := by positivity
          have hrealcast : (((n + 1 : ℕ) : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by norm_cast
          simp only [q, Set.indicator_apply, Set.mem_setOf_eq]
          rw [abs_of_nonneg hnonneg, hrealcast]
          by_cases htail : R < ((n + 1 : ℕ) : ℝ)
          · have htail' : R < (n : ℝ) + 1 := by
              simpa only [Nat.cast_add, Nat.cast_one] using htail
            simpa [htail'] using (hsymm ((n + 1 : ℕ) : ℤ)).symm
          · have htail' : ¬ R < (n : ℝ) + 1 := by
              simpa only [Nat.cast_add, Nat.cast_one] using htail
            simp [htail']
    have hμ : (sdpPositiveMeasure f).real
        {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} =
        ∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then
          sdpPositiveWeight f n else 0 := by
      simp only [Measure.real, sdpPositiveMeasure, Measure.sum_apply_of_countable,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
        mul_ite, Pi.one_apply, mul_one, mul_zero]
      rw [ENNReal.tsum_toReal_eq (by intro n; split_ifs <;> simp)]
      apply tsum_congr
      intro n
      have hw : 0 ≤ sdpPositiveWeight f n := by
          dsimp [sdpPositiveWeight]
          exact mul_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr h0.le)) (hf _)
      by_cases hn : R < (n : ℝ) + 1
      · simp [hn, ENNReal.toReal_ofReal hw]
      · simp [hn]
    have hweights :
        (∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then sdpPositiveWeight f n else 0) =
          (2 / den) * (∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then
            f (-((n + 1 : ℕ) : ℤ)) else 0) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      by_cases hn : R < ((n + 1 : ℕ) : ℝ)
      · simp [hn, sdpPositiveWeight, den]
      · simp [hn, sdpPositiveWeight, den]
    change (∑' x : ℤ, q x) = _
    rw [hsplit', hq0, hpos, hμ, hweights]
    have hden : den ≠ 0 := by dsimp [den]; linarith
    field_simp [hden]
    <;> norm_num [two_smul]
    <;> ring
    <;> ring
  have hleft : (fun R : ℝ =>
      (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
        (Real.Gamma (1 / 3 : ℝ) * b /
          (Real.sqrt 3 * Real.pi)) * R ^ (-(4 / 3 : ℝ))) =ᶠ[atTop]
      (fun R : ℝ => den *
        ((sdpPositiveMeasure f).real
          {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} - a * R ^ (-(4 / 3 : ℝ)))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    rw [hbridge R hR]
    have hcoef : (Real.Gamma (1 / 3 : ℝ) * b /
        (Real.sqrt 3 * Real.pi)) = den * a := by
      dsimp [a, den]
      have hsqrtne : Real.sqrt 3 ≠ 0 :=
        (Real.sqrt_pos.2 (by norm_num)).ne'
      have hsquare : (Real.sqrt 3) ^ 2 = 3 :=
        Real.sq_sqrt (by norm_num)
      field_simp [ne_of_gt (sub_pos.mpr h0), Real.pi_ne_zero, hsqrtne]
      rw [hsquare]
      ring
    rw [hcoef]
    ring
  convert hscaled.congr' hleft.symm (Filter.Eventually.of_forall fun _ => rfl) using 1

/-- The strict tail of the normalized nonnegative `Y` law has coefficient
no correction is adopted, and this is not the paper's printed constant. -/
private theorem sdp_nonnegative_measure_tail_asymptotic_of_expansions
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, y < -1 → g y = 0) (hq : 0 < g (-1)) (hq1 : g (-1) < 1)
    (hG : sdpGExpansion g) :
    (fun R : ℝ => (sdpNonnegativeMeasure g).real
      {n : ℕ | R < (n : ℝ)} -
        ((Real.Gamma (1 / 3 : ℝ) * ((g (-1)) ^ (2 / 3 : ℝ)) /
          (2 * Real.sqrt 3 * Real.pi * (1 - g (-1)))) *
            R ^ (-(4 / 3 : ℝ)))) =o[atTop] (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) := by
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  let den : ℝ := 1 - g (-1)
  let c₁ : ℝ := g (-1) / den
  let c₂ : ℂ := (((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
    (b : ℂ) / (den : ℝ)
  change (fun R : ℝ => (sdpNonnegativeMeasure g).real
      {n : ℕ | R < (n : ℝ)} -
        ((Real.Gamma (1 / 3 : ℝ) * b /
          (2 * Real.sqrt 3 * Real.pi * den)) *
            R ^ (-(4 / 3 : ℝ)))) =o[atTop] (fun R : ℝ => R ^ (-(4 / 3 : ℝ)))
  have hden : 0 < den := by dsimp [den]; linarith
  have hb : 0 < b := Real.rpow_pos_of_pos hq _
  letI : IsProbabilityMeasure (sdpNonnegativeMeasure g) :=
    sdp_nonnegative_measure_isProbability_of_expansions hg hgs hgsupp hq1
  have hchar := sdp_nonnegative_characteristic_expansion_of_expansions
    hg hgs hgsupp hq hq1 hG
  have hcIm : c₂.im = -(Real.sqrt 3 * b / (2 * den)) := by
    let d : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    have hd : d.im = -(Real.sqrt 3) / 2 := by
      simp [d, Complex.mul_im]
      <;> ring
    have hdb : (d * (b : ℂ)).im = -(Real.sqrt 3 / 2) * b := by
      rw [Complex.mul_im]
      simp [hd]
      <;> ring
    change ((d * (b : ℂ)) / (den : ℝ)).im = _
    rw [Complex.div_ofReal_im, hdb]
    field_simp [hden.ne']
    <;> ring
  have hcne : c₂.im ≠ 0 := by
    rw [hcIm]
    exact neg_ne_zero.mpr (div_pos (by positivity) (mul_pos (by norm_num) hden)).ne'
  have hc₁ : 0 < c₁ := by dsimp [c₁]; exact div_pos hq hden
  have hcase := (DirectedDistances.Paper.Section6.tauberian_characteristic
    ℕ (sdpNonnegativeMeasure g) id (by fun_prop)).2
  have hexp : (1 : ℝ) + 1 / 3 = 4 / 3 := by norm_num
  have hresult := hcase c₁ hc₁ c₂ hcne (1 / 3 : ℝ) (by norm_num) (by norm_num) (by
    simpa only [c₁, c₂, den, b, Complex.star_def, hexp, id_eq] using hchar)
  have hconst : -(((1 / 3 : ℝ) * c₂.im) / Real.Gamma (1 - (1 / 3 : ℝ))) /
      Real.cos (Real.pi * (1 / 3 : ℝ) / 2) =
      Real.Gamma (1 / 3 : ℝ) * b /
        (2 * Real.sqrt 3 * Real.pi * den) := by
    rw [hcIm, show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
      show Real.cos (Real.pi * (1 / 3 : ℝ) / 2) = Real.sqrt 3 / 2 by
        rw [show Real.pi * (1 / 3 : ℝ) / 2 = Real.pi / 6 by ring,
          Real.cos_pi_div_six]]
    have hGamma : Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) =
        2 * Real.pi / Real.sqrt 3 := sdp_gamma_reflection_thirds
    have hsqrtpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hGamma' : Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) *
        Real.sqrt 3 = 2 * Real.pi := by
      rw [hGamma]
      field_simp [hsqrtpos.ne']
    have hGpos : 0 < Real.Gamma (2 / 3 : ℝ) :=
      Real.Gamma_pos_of_pos (by norm_num)
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hden.ne', hGpos.ne', hpi]
    have hsquare : Real.sqrt 3 * Real.sqrt 3 = 3 := by
      rw [← sq]; exact Real.sq_sqrt (by norm_num)
    calc
      Real.sqrt 3 * 2 * Real.pi = Real.sqrt 3 * (2 * Real.pi) := by ring
      _ = Real.sqrt 3 *
          (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) * Real.sqrt 3) := by
            rw [← hGamma']
      _ = 3 * Real.Gamma (2 / 3 : ℝ) * Real.Gamma (1 / 3 : ℝ) := by
            rw [show Real.sqrt 3 *
              (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) * Real.sqrt 3) =
              (Real.sqrt 3 * Real.sqrt 3) * Real.Gamma (2 / 3 : ℝ) * Real.Gamma (1 / 3 : ℝ) by ring,
              hsquare]
  have htail := hresult.2.2
  have hexpR : -(1 / 3 : ℝ) - 1 = -(4 / 3 : ℝ) := by norm_num
  rw [hconst] at htail
  simpa only [id_eq, hexpR] using htail

/-- The unnormalized positive `g` tail has coefficient
is adopted, and this is not the paper's printed constant. -/
theorem sdp_g_positive_tail_asymptotic_of_master
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (hκ : 3 - 6 * (g (-1)) ^ 2 - f 0 = 0) :
    (fun R : ℝ => (∑' y : ℤ, if R < (y : ℝ) then g y else 0) -
      (Real.Gamma (1 / 3 : ℝ) * ((g (-1)) ^ (2 / 3 : ℝ)) /
        (2 * Real.sqrt 3 * Real.pi)) * R ^ (-(4 / 3 : ℝ))) =o[atTop]
      (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) := by
  obtain ⟨_, hq⟩ := sdp_side_nondegenerate_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  have hmass := sdp_g_nat_mass_hasSum hgs hgsupp
  have hmassEq := hmass.tsum_eq
  have hdenNonneg : 0 ≤ 1 - g (-1) := by
    rw [← hmassEq]
    exact tsum_nonneg fun n : ℕ => hg n
  have hle : g (-1) ≤ 1 := by linarith
  have hneq : g (-1) ≠ 1 := by
    intro heq
    have hκ' : 3 - 6 * (1 : ℝ) ^ 2 - f 0 = 0 := by simpa [heq] using hκ
    have hf0 := hf 0
    norm_num at hκ'
    linarith
  have hq1 : g (-1) < 1 := by
    by_contra hnot
    have heq : g (-1) = 1 := le_antisymm hle (le_of_not_gt hnot)
    exact hneq heq
  have hG := (sdp_selected_expansions_predicates_of_master
    hf hfs hg hgs hsymm hgsupp hrec hκ).2
  let den : ℝ := 1 - g (-1)
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  have hden : 0 < den := by dsimp [den]; linarith
  have hmeasure := sdp_nonnegative_measure_tail_asymptotic_of_expansions
    hg hgs hgsupp hq hq1 hG
  have hscaled : (fun R : ℝ => den *
      ((sdpNonnegativeMeasure g).real {n : ℕ | R < (n : ℝ)} -
        (Real.Gamma (1 / 3 : ℝ) * b /
          (2 * Real.sqrt 3 * Real.pi * den)) * R ^ (-(4 / 3 : ℝ)))) =o[atTop]
      (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) := by
    exact hmeasure.const_mul_left den
  have hbridge : (fun R : ℝ =>
      ∑' y : ℤ, if R < (y : ℝ) then g y else 0) =ᶠ[atTop]
      (fun R : ℝ => den * (sdpNonnegativeMeasure g).real
        {n : ℕ | R < (n : ℝ)}) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    let q : ℤ → ℝ := {y : ℤ | R < (y : ℝ)}.indicator g
    have hqSummable : Summable q := by
      change Summable ({y : ℤ | R < (y : ℝ)}.indicator g)
      exact hgs.summable.indicator _
    have hposSummable : Summable (fun n : ℕ => q (n : ℤ)) :=
      hqSummable.comp_injective Nat.cast_injective
    have hnegSummable : Summable (fun n : ℕ => q (-((n : ℤ) + 1))) :=
      hqSummable.comp_injective (by
        intro m n h
        exact Int.negSucc.inj (by simpa only [Int.negSucc_eq] using h))
    have hsplit := tsum_of_nat_of_neg_add_one (f := q) hposSummable hnegSummable
    have hq0 : q 0 = 0 := by
      simp [q, Set.indicator_apply, not_lt.mpr hR]
    have hpos : (∑' n : ℕ, q (n : ℤ)) =
        ∑' n : ℕ, if R < (n : ℝ) then g n else 0 := by
      apply tsum_congr
      intro n
      simp only [q, Set.indicator_apply, Set.mem_setOf_eq]
      norm_cast
    have hterms : (fun n : ℕ => q (-((n : ℤ) + 1))) = fun _ => 0 := by
      funext n
      have hle : (((-((n : ℤ) + 1) : ℤ) : ℝ)) ≤ 0 := by norm_cast; omega
      have hnot : ¬ R < (((-((n : ℤ) + 1) : ℤ) : ℝ)) := not_lt_of_ge (le_trans hle hR)
      change ({y : ℤ | R < (y : ℝ)}.indicator g) (-((n : ℤ) + 1)) = 0
      exact Set.indicator_of_notMem (by simpa only [Set.mem_setOf_eq] using hnot) _
    have hneg : (∑' n : ℕ, q (-((n : ℤ) + 1))) = 0 := by
      rw [hterms]
      simp
    have hμ : (sdpNonnegativeMeasure g).real {n : ℕ | R < (n : ℝ)} =
        ∑' n : ℕ, if R < (n : ℝ) then sdpNonnegativeWeight g n else 0 :=
      sdp_nonnegative_measure_tail_tsum hg hq1 R
    have hweights :
        (∑' n : ℕ, if R < (n : ℝ) then sdpNonnegativeWeight g n else 0) =
          (1 / den) * (∑' n : ℕ, if R < (n : ℝ) then g n else 0) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      by_cases hn : R < (n : ℝ)
      · simp only [hn, if_true, sdpNonnegativeWeight, div_eq_mul_inv, den]
        ring
      · simp [hn]
    change (∑' y : ℤ, q y) = _
    rw [hsplit, hpos, hneg, hμ, hweights]
    have hdenNe : den ≠ 0 := hden.ne'
    field_simp [hdenNe]
    <;> ring
  have hcoef : (Real.Gamma (1 / 3 : ℝ) * b /
      (2 * Real.sqrt 3 * Real.pi * den)) * den =
        Real.Gamma (1 / 3 : ℝ) * b / (2 * Real.sqrt 3 * Real.pi) := by
    have hsqrtne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    field_simp [hden.ne', hsqrtne, Real.pi_ne_zero]
    <;> ring
  have hleft : (fun R : ℝ =>
      (∑' y : ℤ, if R < (y : ℝ) then g y else 0) -
        (Real.Gamma (1 / 3 : ℝ) * b /
          (2 * Real.sqrt 3 * Real.pi)) * R ^ (-(4 / 3 : ℝ))) =ᶠ[atTop]
      (fun R : ℝ => den * ((sdpNonnegativeMeasure g).real
        {n : ℕ | R < (n : ℝ)} -
        (Real.Gamma (1 / 3 : ℝ) * b /
          (2 * Real.sqrt 3 * Real.pi * den)) * R ^ (-(4 / 3 : ℝ)))) := by
    filter_upwards [hbridge] with R hR
    rw [hR, ← hcoef]
    ring
  exact hscaled.congr' hleft.symm (Filter.Eventually.of_forall fun _ => rfl)

end SDP

end DirectedDistances.Recursive
