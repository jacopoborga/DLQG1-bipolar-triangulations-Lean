/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.LDPNondegenerate
public import DirectedDistances.Recursive.LDPQuadraticFromMaster
public import DirectedDistances.Recursive.LDPSideSign
public import DirectedDistances.Paper.Section6.Tauberian
public import DirectedDistances.Tauberian.GeneratingFunctionLaw
public import DirectedDistances.Tauberian.TailPowerTransfer
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Supporting lemmas for paper labels `lem:Y-not-const`, `prop:Tauberian` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.Recursive

open Filter Asymptotics MeasureTheory
open scoped Topology

section LDP

variable {f g : ℤ → ℝ}
variable (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
variable (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
variable (hsymm : ∀ x, f (-x) = f x)
variable (hgsupp : ∀ y, 0 ≤ y → g y = 0)
variable (hrec : ∀ x y : ℤ, y ≤ -1 →
  3 * f x * g y =
    f x * f y +
    f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
    (if y = -1 then
      (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
     else 0))

include hf hfs hg hgs hsymm hgsupp hrec

/-- The LDP master premises rule out a unit atom at zero, as in the first step
this is Lemma 6.6 (`lem:Y-not-const`). -/
theorem ldp_f_zero_ne_one : f 0 ≠ 1 := by
  have h := ldp_pmf_nondegenerate_of_master hf hfs hg hgs hsymm hgsupp hrec
  exact ne_of_lt (h.1 0)

include hf hfs hsymm

omit hg hgs hgsupp hrec in
private theorem ldp_negative_nat_mass_hasSum :
    HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) ((1 - f 0) / 2) := by
  have hcf := hasSum_negativeCF hf hfs.summable 0
  rw [negativeCF_zero hf hfs hsymm] at hcf
  have hcast : HasSum (fun n : ℕ => ((f (-((n : ℤ) + 1)) : ℝ) : ℂ))
      (((1 - f 0) / 2 : ℝ) : ℂ) := by
    convert hcf using 1; simp [cfPhase]
  exact (Complex.hasSum_ofReal).mp hcast

/-- The normalized positive-increment mass, indexed by `n ↦ n + 1`. -/
@[expose] noncomputable def ldpPositiveWeight (f : ℤ → ℝ) (n : ℕ) : ℝ :=
  (2 / (1 - f 0)) * f (-((n : ℤ) + 1))

/-- The positive-increment probability space before the random variable
`n ↦ n + 1` is applied. -/
@[expose] noncomputable def ldpPositiveMeasure (f : ℤ → ℝ) : Measure ℕ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (ldpPositiveWeight f n) • Measure.dirac n

/-- The reflected negative-increment mass, indexed by `n ↦ n + 1`. -/
@[expose] noncomputable def ldpReflectedGWeight (g : ℤ → ℝ) (n : ℕ) : ℝ :=
  g (-((n : ℤ) + 1))

/-- The probability space for the reflected negative increment. -/
@[expose] noncomputable def ldpReflectedGMeasure (g : ℤ → ℝ) : Measure ℕ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (ldpReflectedGWeight g n) • Measure.dirac n

omit hg hgs hgsupp hrec in
private theorem ldp_positive_weight_hasSum (h0 : f 0 < 1) :
    HasSum (ldpPositiveWeight f) 1 := by
  have hb := ldp_negative_nat_mass_hasSum hf hfs hsymm
  have hden : 0 < 1 - f 0 := sub_pos.mpr h0
  have hcoef : (2 / (1 - f 0)) * ((1 - f 0) / 2) = 1 := by
    field_simp
  convert hb.mul_left (2 / (1 - f 0)) using 1
  · rfl
  · exact hcoef.symm

omit hf hfs hg hsymm hrec in
private theorem ldp_g_reflected_weight_hasSum :
    HasSum (ldpReflectedGWeight g) 1 := by
  have hgc : HasSum (fun k : ℤ => (g k : ℂ)) (1 : ℂ) :=
    (Complex.hasSum_ofReal).mpr hgs
  have hneg := hasSum_neg_half hgc (fun k hk => by
    simp [hgsupp k hk])
  exact (Complex.hasSum_ofReal).mp hneg

omit hg hgs hgsupp hrec in
theorem ldp_positive_measure_isProbability (h0 : f 0 < 1) :
    IsProbabilityMeasure (ldpPositiveMeasure f) := by
  have hden : 0 < 1 - f 0 := sub_pos.mpr h0
  apply HasSum.isProbabilityMeasure_sum_dirac
  · intro n
    dsimp [ldpPositiveWeight]
    exact mul_nonneg (div_nonneg (by norm_num) hden.le) (hf _)
  · exact ldp_positive_weight_hasSum hf hfs hsymm h0


omit hf hfs hg hgs hsymm hgsupp hrec in
private theorem integral_succ_characteristic_of_sum (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (t : ℝ) :
    (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂Measure.sum (fun n : ℕ => ENNReal.ofReal (w n) • Measure.dirac n)) =
      ∑' n : ℕ, (w n : ℂ) * Complex.exp
        ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  have hc (n : ℕ) : ENNReal.ofReal (w n) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [integral_sum_dirac hc]
  apply tsum_congr
  intro n
  simp only [ENNReal.toReal_ofReal (hw n), Complex.real_smul]


omit hg hgs hgsupp hrec in
private theorem ldp_positive_characteristic_eq_negative (h0 : f 0 < 1) (t : ℝ) :
    (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂ldpPositiveMeasure f) =
      (((2 / (1 - f 0) : ℝ) : ℂ) * negativeCF f (-t)) := by
  rw [ldpPositiveMeasure]
  have hpos := (hasSum_negativeCF hf hfs.summable (-t)).mul_left
    (((2 / (1 - f 0) : ℝ) : ℂ))
  have hseries : HasSum (fun n : ℕ =>
      (ldpPositiveWeight f n : ℂ) * Complex.exp
        ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))
      (((2 / (1 - f 0) : ℝ) : ℂ) * negativeCF f (-t)) := by
    convert hpos using 1
    funext n
    have hphase : cfPhase (-t) (-((n : ℤ) + 1)) = Complex.exp
        ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      dsimp [cfPhase]
      congr 1
      push_cast
      ring
    dsimp [ldpPositiveWeight]
    rw [hphase]
    push_cast
    ring
  rw [integral_succ_characteristic_of_sum (ldpPositiveWeight f)
    (by intro n; dsimp [ldpPositiveWeight]; exact
      mul_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr h0.le)) (hf _)) t]
  exact hseries.tsum_eq

omit hf hfs hsymm hrec in
private theorem ldp_g_characteristic_eq_negative (t : ℝ) :
    (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂ldpReflectedGMeasure g) = negativeCF g (-t) := by
  rw [ldpReflectedGMeasure]
  have hseries : HasSum (fun n : ℕ =>
      (ldpReflectedGWeight g n : ℂ) * Complex.exp
        ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))
      (negativeCF g (-t)) := by
    convert hasSum_negativeCF hg hgs.summable (-t) using 1
    funext n
    have hphase : cfPhase (-t) (-((n : ℤ) + 1)) = Complex.exp
        ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      dsimp [cfPhase]
      congr 1
      push_cast
      ring
    dsimp [ldpReflectedGWeight]
    rw [hphase]
  rw [integral_succ_characteristic_of_sum (ldpReflectedGWeight g)
    (by intro n; exact hg _) t]
  exact hseries.tsum_eq

omit hf hfs hg hgs hgsupp hrec in
/-- The law of the nonzero absolute LDP increment on `ℕ`, obtained by applying
`n ↦ n + 1` to `ldpPositiveMeasure`, has the source masses
`2 f(x)/(1-f(0))` for `x ≥ 1`; its characteristic function is the positive
part `2(F-F⁻-f(0))/(1-f(0))`. Proposition 6.1 and -/
theorem ldp_positive_law_atom (x : ℕ) (hx : 1 ≤ x) :
    (ldpPositiveMeasure f).map Nat.succ {x} =
      ENNReal.ofReal (2 * f (x : ℤ) / (1 - f 0)) := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpre : Nat.succ ⁻¹' ({x} : Set ℕ) = {x - 1} := by
    ext n
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [hpre, ldpPositiveMeasure, Measure.sum_smul_dirac_singleton]
  have hidx : (((x - 1 : ℕ) : ℤ) + 1) = (x : ℤ) := by omega
  rw [ldpPositiveWeight, hidx, hsymm]
  congr 1
  ring

omit hf hfs hg hgs hgsupp hsymm hrec in
/-- The reflected negative LDP increment law has mass `g(-x)` at each
`x ≥ 1`. This is the law used for `eq:conc-asympt-2`, -/
theorem ldp_reflected_g_law_atom (x : ℕ) (hx : 1 ≤ x) :
    (ldpReflectedGMeasure g).map Nat.succ {x} =
      ENNReal.ofReal (g (-(x : ℤ))) := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpre : Nat.succ ⁻¹' ({x} : Set ℕ) = {x - 1} := by
    ext n
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [hpre, ldpReflectedGMeasure, Measure.sum_smul_dirac_singleton]
  have hidx : (((x - 1 : ℕ) : ℤ) + 1) = (x : ℤ) := by omega
  rw [ldpReflectedGWeight, hidx]

include hf hfs hg hgs hsymm hgsupp hrec
/-- The pushforward law by `n ↦ n + 1` is a probability measure, so its
fibers give the stated probability masses. Proposition 6.2, -/
theorem ldp_positive_law_isProbability (h0 : f 0 < 1) :
    IsProbabilityMeasure ((ldpPositiveMeasure f).map Nat.succ) := by
  letI : IsProbabilityMeasure (ldpPositiveMeasure f) :=
    ldp_positive_measure_isProbability hf hfs hsymm h0
  infer_instance

include hf hfs hg hgs hsymm hgsupp hrec
/-- Probability form of the positive-law atom formula. Proposition 6.2, -/
theorem ldp_positive_law_probability (h0 : f 0 < 1) (x : ℕ) (hx : 1 ≤ x) :
    ((ldpPositiveMeasure f).map Nat.succ).real {x} =
      2 * f (x : ℤ) / (1 - f 0) := by
  rw [Measure.real, ldp_positive_law_atom hsymm x hx]
  exact ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (by norm_num) (hf _))
    (sub_nonneg.mpr h0.le))

include hf hfs hg hgs hsymm hgsupp hrec
/-- The reflected `g` law is already a probability measure by its total mass;
its atoms are `g(-x)` for `x ≥ 1`. Proposition 6.2, -/
theorem ldp_reflected_g_law_isProbability :
    IsProbabilityMeasure ((ldpReflectedGMeasure g).map Nat.succ) := by
  letI : IsProbabilityMeasure (ldpReflectedGMeasure g) := by
    apply HasSum.isProbabilityMeasure_sum_dirac
    · intro n
      exact hg _
    · exact ldp_g_reflected_weight_hasSum hgs hgsupp
  infer_instance

include hf hfs hg hgs hsymm hgsupp hrec
/-- Probability form of the reflected-law atom formula. Proposition 6.2, -/
theorem ldp_reflected_g_law_probability (x : ℕ) (hx : 1 ≤ x) :
    ((ldpReflectedGMeasure g).map Nat.succ).real {x} = g (-(x : ℤ)) := by
  rw [Measure.real, ldp_reflected_g_law_atom x hx]
  exact ENNReal.toReal_ofReal (hg _)

omit hg hgs hgsupp hrec in
/-- The probability-law characteristic function is exactly the source positive
part `2(F-F⁻-f(0))/(1-f(0))`. Proposition 6.2, -/
theorem ldp_positive_law_characteristic (h0 : f 0 < 1) (t : ℝ) :
    (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂ldpPositiveMeasure f) =
      (((2 / (1 - f 0) : ℝ) : ℂ) *
        (integerCF f t - negativeCF f t - (f 0 : ℂ))) := by
  rw [ldp_positive_characteristic_eq_negative hf hfs hsymm h0 t]
  have hsplit := integerCF_eq_split hf hfs.summable hsymm t
  rw [hsplit]
  ring

omit hf hfs hg hgs hsymm hgsupp hrec in
private theorem negativeCF_neg_eq_star {p : ℤ → ℝ} (t : ℝ) :
    negativeCF p (-t) = star (negativeCF p t) := by
  unfold negativeCF
  rw [Complex.star_def, Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp only [Complex.conj_I, Complex.ofReal_neg, neg_mul]
  ring

omit hf hfs hg hgs hsymm hgsupp hrec in
private theorem littleO_star {F : ℝ → ℂ} {G : ℝ → ℝ} {l : Filter ℝ}
    (h : F =o[l] G) : (fun t => star (F t)) =o[l] G := by
  rw [isLittleO_iff] at h ⊢
  intro ε hε
  filter_upwards [h (c := ε) hε] with t ht
  simpa only [norm_star] using ht

omit hf hfs hg hgs hsymm hgsupp hrec in
private theorem littleO_extend_conjugate {φ : ℝ → ℂ} {c : ℂ} {ν : ℝ}
    (hpos : (fun t : ℝ => φ t - 1 - c * (((t ^ ν : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ ν))
    (hconj : ∀ t : ℝ, φ (-t) = star (φ t)) :
    (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))) =o[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
  have hpos' : (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    apply hpos.congr'
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      have htp : 0 < t := Set.mem_Ioi.mp ht
      simp [htp, abs_of_pos htp]
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      exact congrArg (fun r : ℝ => r ^ ν) (abs_of_pos (Set.mem_Ioi.mp ht)).symm
  have hnegMap : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    have hcont : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero] using
        ((continuous_neg.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          nhdsWithin_le_nhds)
    refine ⟨hcont, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact neg_pos.mpr (Set.mem_Iio.mp ht)
  have hnegComp := hpos.comp_tendsto hnegMap
  have hnegStar : (fun t : ℝ => star
      ((φ (-t) - 1 - c * ((((-t) ^ ν : ℝ) : ℂ)))) ) =o[𝓝[<] (0 : ℝ)]
      (fun t : ℝ => ((-t) ^ ν)) := littleO_star hnegComp
  have hneg : (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))) =o[𝓝[<] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    apply hnegStar.congr'
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      have htn : t < 0 := Set.mem_Iio.mp ht
      have hsym' : φ t = star (φ (-t)) := by
        simpa only [neg_neg] using hconj (-t)
      calc
        star (φ (-t) - 1 - c * ((((-t) ^ ν : ℝ) : ℂ))) =
            star (φ (-t)) - 1 - (star c) * (((|t| ^ ν : ℝ) : ℂ)) := by
              simp [abs_of_neg htn]
        _ = φ t - 1 - (star c) * (((|t| ^ ν : ℝ) : ℂ)) := by rw [← hsym']
        _ = φ t - 1 - (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ)) := by
              simp [not_lt.mpr htn.le]
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      rw [abs_of_neg (Set.mem_Iio.mp ht)]
  have hfilter : 𝓝[<] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ) = 𝓝[≠] (0 : ℝ) := by
    rw [← nhdsWithin_union]
    congr 1
    ext t
    simp [Set.mem_Iio, Set.mem_Ioi]
  rw [← hfilter]
  exact hneg.sup hpos'

omit hf hfs hsymm hrec in
/-- The reflected law `Y` with masses `g(-y)`, `y ≥ 1`, has characteristic
function `G(-t)`. Proposition 6.2 and `eq:conc-asympt-2`, -/
theorem ldp_reflected_g_law_characteristic (t : ℝ) :
    (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂ldpReflectedGMeasure g) = negativeCF g (-t) :=
  ldp_g_characteristic_eq_negative hg hgs hgsupp t

omit hf hfs hsymm hrec in
theorem ldp_reflected_g_measure_isProbability :
    IsProbabilityMeasure (ldpReflectedGMeasure g) := by
  apply HasSum.isProbabilityMeasure_sum_dirac
  · intro n
    exact hg _
  · exact ldp_g_reflected_weight_hasSum hgs hgsupp


include hf hfs hg hgs hsymm hgsupp hrec
/-- The actual characteristic function of the normalized positive part of the
symmetric LDP increment has the two-sided expansion required by Proposition
6.1. The coefficient is the one in the proof of `eq:conc-asympt-1`, -/
theorem ldp_positive_characteristic_expansion :
    let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
    let c : ℂ := (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) /
      ((1 - f 0 : ℝ) : ℂ)) * (a : ℂ)
    (fun t : ℝ =>
      (∫ n : ℕ, Complex.exp ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
        ∂ldpPositiveMeasure f) - 1 -
      (if 0 < t then c else star c) * (((|t| ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (2 / 3 : ℝ)) := by
  let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
  let d : ℂ := ((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2
  let s : ℝ := 2 / (1 - f 0)
  let c : ℂ := (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) /
    ((1 - f 0 : ℝ) : ℂ)) * (a : ℂ)
  change (fun t : ℝ =>
      (∫ n : ℕ, Complex.exp ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
        ∂ldpPositiveMeasure f) - 1 -
      (if 0 < t then c else star c) * (((|t| ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (2 / 3 : ℝ))
  have h0 : f 0 < 1 := (ldp_pmf_nondegenerate_of_master hf hfs hg hgs hsymm hgsupp hrec).1 0
  have hden : 0 < 1 - f 0 := sub_pos.mpr h0
  have hbase : 0 < (3 + f 0) / 2 := by
    have hf0 := hf 0
    positivity
  have ha : 0 < a := Real.rpow_pos_of_pos hbase _
  have hside := ldp_side_expansions_of_master hf hfs hg hgs hsymm hgsupp hrec
  have hsideF : (fun t : ℝ => negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) -
      (d * (a : ℂ)) * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
    simpa [a, d] using hside.1
  have hstar := littleO_star hsideF
  have hstar' : (fun t : ℝ => star (negativeCF f t) -
      (((1 - f 0) / 2 : ℝ) : ℂ) - star (d * (a : ℂ)) *
        (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
    simpa [map_sub, map_mul] using hstar
  have hscaleR : (2 / (1 - f 0)) * ((1 - f 0) / 2) = 1 := by
    field_simp [ne_of_gt hden]
  have hscale : ((s : ℝ) : ℂ) * (((1 - f 0) / 2 : ℝ) : ℂ) = 1 := by
    exact_mod_cast hscaleR
  have hcoeff : ((s : ℝ) : ℂ) * star (d * (a : ℂ)) = c := by
    calc
      ((s : ℝ) : ℂ) * star (d * (a : ℂ)) =
          ((2 / (1 - f 0) : ℝ) : ℂ) *
            (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2) * (a : ℂ) := by
              simp [s, d, Complex.star_def]
              ring
      _ = c := by
          dsimp [c]
          push_cast
          field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hden)]
  have hscaled := hstar'.const_smul_left (((s : ℝ) : ℂ))
  have hpos : (fun t : ℝ =>
      (((s : ℝ) : ℂ) * star (negativeCF f t)) - 1 -
        c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
    apply hscaled.congr'
    · exact Filter.Eventually.of_forall fun t => by
        calc
          ((s : ℝ) : ℂ) •
              (star (negativeCF f t) - (((1 - f 0) / 2 : ℝ) : ℂ) -
                star (d * (a : ℂ)) * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) =
              ((s : ℝ) : ℂ) * star (negativeCF f t) -
                ((s : ℝ) : ℂ) * (((1 - f 0) / 2 : ℝ) : ℂ) -
                (((s : ℝ) : ℂ) * star (d * (a : ℂ))) *
                  (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
                    rw [smul_eq_mul]
                    ring
          _ = ((s : ℝ) : ℂ) * star (negativeCF f t) - 1 -
                c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by rw [hscale, hcoeff]
    · exact Filter.Eventually.of_forall fun _ => rfl
  let φ : ℝ → ℂ := fun t =>
    ∫ n : ℕ, Complex.exp ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂ldpPositiveMeasure f
  have hchar (t : ℝ) : φ t = ((s : ℝ) : ℂ) * star (negativeCF f t) := by
    change (∫ n : ℕ, Complex.exp
      ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ∂ldpPositiveMeasure f) = _
    rw [ldp_positive_characteristic_eq_negative hf hfs hsymm h0 t,
      negativeCF_neg_eq_star]
  have hposφ : (fun t : ℝ => φ t - 1 - c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
      =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
    convert hpos using 1
    funext t
    rw [hchar]
  have hconj (t : ℝ) : φ (-t) = star (φ t) := by
    rw [hchar, hchar, negativeCF_neg_eq_star]
    simp [φ, s]
  have hfull := littleO_extend_conjugate hposφ hconj
  convert hfull using 1

include hf hfs hg hgs hsymm hgsupp hrec
/-- The characteristic function of `Y` with masses `g(-y)`, `y ≥ 1`, has the
conjugate side expansion from Proposition 6.2, `eq:conc-asympt-2`, -/
theorem ldp_reflected_g_characteristic_expansion :
    let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
    let c : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
    (fun t : ℝ =>
      (∫ n : ℕ, Complex.exp ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
        ∂ldpReflectedGMeasure g) - 1 -
      (if 0 < t then c else star c) * (((|t| ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (2 / 3 : ℝ)) := by
  let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
  let d : ℂ := ((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2
  let c : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
  change (fun t : ℝ =>
      (∫ n : ℕ, Complex.exp ((((t * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
        ∂ldpReflectedGMeasure g) - 1 -
      (if 0 < t then c else star c) * (((|t| ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (2 / 3 : ℝ))
  have hside := ldp_side_expansions_of_master hf hfs hg hgs hsymm hgsupp hrec
  have hsideG : (fun t : ℝ => negativeCF g t - 1 -
      (d * (a : ℂ)) * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
    simpa [a, d] using hside.2
  have hstar1 := littleO_star hsideG
  have hstar' : (fun t : ℝ => negativeCF g (-t) - 1 - star (d * (a : ℂ)) *
      (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
    convert hstar1 using 1
    funext t
    rw [negativeCF_neg_eq_star]
    simp [map_sub, map_mul]
  have hcoef : star (d * (a : ℂ)) = c := by
    simp [c, d, Complex.star_def]
  have hpos : (fun t : ℝ => negativeCF g (-t) - 1 - c *
      (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
    convert hstar' using 1
    funext t
    rw [hcoef]
  let φ : ℝ → ℂ := fun t => negativeCF g (-t)
  have hposφ : (fun t : ℝ => φ t - 1 - c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
      =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
    simpa [φ] using hpos
  have hconj (t : ℝ) : φ (-t) = star (φ t) := by
    simp [φ, negativeCF_neg_eq_star]
  have hfull := littleO_extend_conjugate hposφ hconj
  simpa only [φ, ldp_reflected_g_law_characteristic hg hgs hgsupp] using hfull

omit hfs hg hgs hsymm hgsupp hrec in
private theorem ldp_positive_measure_tail_tsum (h0 : f 0 < 1) (R : ℝ) :
    (ldpPositiveMeasure f).real {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} =
      ∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then ldpPositiveWeight f n else 0 := by
  simp only [Measure.real, ldpPositiveMeasure, Measure.sum_apply_of_countable,
    Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator_apply, mul_ite, Pi.one_apply, mul_one,
    mul_zero]
  rw [ENNReal.tsum_toReal_eq (by intro n; split_ifs <;> simp)]
  apply tsum_congr
  intro n
  by_cases hn : R < ((n + 1 : ℕ) : ℝ)
  · have hn' : R < (n : ℝ) + 1 := by simpa using hn
    have hw : 0 ≤ ldpPositiveWeight f n := by
      dsimp [ldpPositiveWeight]
      exact mul_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr h0.le)) (hf _)
    simp [hn', ENNReal.toReal_ofReal hw]
  · have hn' : ¬ R < (n : ℝ) + 1 := by simpa using hn
    simp [hn']

omit hf hfs hgs hsymm hgsupp hrec in
private theorem ldp_reflected_g_measure_tail_tsum (R : ℝ) :
    (ldpReflectedGMeasure g).real {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} =
      ∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then ldpReflectedGWeight g n else 0 := by
  simp only [Measure.real, ldpReflectedGMeasure, Measure.sum_apply_of_countable,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    mul_ite, Pi.one_apply, mul_one, mul_zero]
  rw [ENNReal.tsum_toReal_eq (by intro n; split_ifs <;> simp)]
  apply tsum_congr
  intro n
  by_cases hn : R < ((n + 1 : ℕ) : ℝ)
  · have hn' : R < (n : ℝ) + 1 := by simpa using hn
    have hw : 0 ≤ ldpReflectedGWeight g n := by
      exact hg _
    simp [hn', ENNReal.toReal_ofReal hw]
  · have hn' : ¬ R < (n : ℝ) + 1 := by simpa using hn
    simp [hn']

private theorem ldp_f_absolute_tail_eq_measure (h0 : f 0 < 1) (R : ℝ)
    (hR : 0 ≤ R) :
    (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) =
      (1 - f 0) * (ldpPositiveMeasure f).real
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
  have hq0 : q 0 = 0 := by
    simp [q, hR]
  have hpos : (∑' n : ℕ, q ((n : ℤ) + 1)) =
      ∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then
        f (-((n + 1 : ℕ) : ℤ)) else 0 := by
    apply tsum_congr
    intro n
    have hidx : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
    calc
      q ((n : ℤ) + 1) = q ((n + 1 : ℕ) : ℤ) := congrArg q hidx.symm
      _ = if R < ((n + 1 : ℕ) : ℝ) then f (-((n + 1 : ℕ) : ℤ)) else 0 := by
        have hnonneg : 0 ≤ (((n + 1 : ℕ) : ℤ) : ℝ) := by positivity
        have hrealcast : (((n + 1 : ℕ) : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by norm_cast
        simp only [q, Set.indicator_apply, Set.mem_setOf_eq]
        rw [abs_of_nonneg hnonneg, hrealcast]
        by_cases htail : R < ((n + 1 : ℕ) : ℝ)
        · have htail' : R < (n : ℝ) + 1 := by
            simpa only [Nat.cast_add, Nat.cast_one] using htail
          simpa [htail'] using (hsymm ((n + 1 : ℕ) : ℤ)).symm
        · have htail'' : ¬ R < (n : ℝ) + 1 := by
            simpa only [Nat.cast_add, Nat.cast_one] using htail
          simp [htail'']
  have hμ := ldp_positive_measure_tail_tsum hf h0 R
  have hweights :
      (∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then ldpPositiveWeight f n else 0) =
        (2 / (1 - f 0)) *
          (∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then
            f (-((n + 1 : ℕ) : ℤ)) else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hidx : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
    by_cases hn : R < ((n + 1 : ℕ) : ℝ)
    · simp [hn, ldpPositiveWeight, hidx]
    · simp [hn, ldpPositiveWeight, hidx]
  change (∑' x : ℤ, q x) = _
  rw [hsplit', hq0, hpos, hμ, hweights]
  have hden : 1 - f 0 ≠ 0 := (sub_pos.mpr h0).ne'
  field_simp [hden]
  <;> ring

omit hf hfs hsymm hrec in
private theorem ldp_g_negative_tail_eq_measure (R : ℝ) (hR : 0 ≤ R) :
    (∑' y : ℤ, if (y : ℝ) < -R then g y else 0) =
      (ldpReflectedGMeasure g).real
        {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} := by
  let q : ℤ → ℝ := {y : ℤ | (y : ℝ) < -R}.indicator g
  have hqSummable : Summable q := by
    change Summable ({y : ℤ | (y : ℝ) < -R}.indicator g)
    exact hgs.summable.indicator _
  have hposSummable : Summable (fun n : ℕ => q ((n : ℤ) + 1)) := by
    apply Summable.congr (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    intro n
    have hn : 0 ≤ (n : ℤ) + 1 := by omega
    have hgz := hgsupp ((n : ℤ) + 1) hn
    simp [q, Set.indicator_apply, hgz]
  have hnegSummable : Summable (fun n : ℕ => q (-((n : ℤ) + 1))) :=
    hqSummable.comp_injective (by
      intro m n h
      exact Int.negSucc.inj (by simpa only [Int.negSucc_eq] using h))
  have hsplit := tsum_of_add_one_of_neg_add_one (f := q)
    hposSummable hnegSummable
  have hq0 : q 0 = 0 := by
    have hg0 : g 0 = 0 := hgsupp 0 (by norm_num)
    simp [q, Set.indicator_apply, hg0]
  have hpos : (∑' n : ℕ, q ((n : ℤ) + 1)) = 0 := by
    calc
      (∑' n : ℕ, q ((n : ℤ) + 1)) = ∑' n : ℕ, 0 := by
        apply tsum_congr
        intro n
        have hn : 0 ≤ (n : ℤ) + 1 := by omega
        have hgz := hgsupp ((n : ℤ) + 1) hn
        simp [q, Set.indicator_apply, hgz]
      _ = 0 := tsum_zero
  have hneg : (∑' n : ℕ, q (-((n : ℤ) + 1))) =
      ∑' n : ℕ, if R < ((n + 1 : ℕ) : ℝ) then
        g (-((n : ℤ) + 1)) else 0 := by
    apply tsum_congr
    intro n
    have harg : (((-((n : ℤ) + 1) : ℤ) : ℝ)) = -((n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    simp only [q, Set.indicator_apply, Set.mem_setOf_eq]
    rw [harg]
    by_cases htail : R < ((n + 1 : ℕ) : ℝ)
    · have htail' : -((n + 1 : ℕ) : ℝ) < -R := by linarith
      simp [htail, htail']
    · have htail' : ¬ -((n + 1 : ℕ) : ℝ) < -R := by linarith
      simp [htail, htail']
  have hμ := ldp_reflected_g_measure_tail_tsum hg R
  change (∑' y : ℤ, q y) = _
  rw [hsplit, hpos, hq0, hneg, hμ]
  simp_rw [ldpReflectedGWeight]
  simp

omit hf hfs hg hgs hsymm hgsupp hrec in
private theorem ldp_gamma_reflection_thirds :
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

omit hf hfs hg hgs hsymm hgsupp hrec in
private theorem ldp_gamma_ratio_thirds :
    2 / Real.Gamma (1 / 3 : ℝ) =
      Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi := by
  have hgamma := ldp_gamma_reflection_thirds
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hgamma' : Real.sqrt 3 *
      (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ)) = 2 * Real.pi := by
    rw [hgamma]
    field_simp [ne_of_gt hsqrt]
  have hGpos : 0 < Real.Gamma (1 / 3 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  field_simp [ne_of_gt hGpos, Real.pi_ne_zero]
  nlinarith [hgamma']

include hf hfs hg hgs hsymm hgsupp hrec
/-- Proposition 6.1 applied to the normalized nonzero symmetric increment
law gives its real strict-tail asymptotic, with coefficient determined by -/
theorem ldp_positive_measure_tail_asymptotic :
    let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
    (fun R : ℝ => (ldpPositiveMeasure f).real
      {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
        (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ))) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) := by
  let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
  let c : ℂ := (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) /
    (1 - f 0 : ℝ)) * (a : ℂ)
  change (fun R : ℝ => (ldpPositiveMeasure f).real
    {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
      (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ))) * R ^ (-(2 / 3 : ℝ)))
    =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ)))
  have h0 : f 0 < 1 :=
    (ldp_pmf_nondegenerate_of_master hf hfs hg hgs hsymm hgsupp hrec).1 0
  have hden : 0 < 1 - f 0 := sub_pos.mpr h0
  have hf0 : 0 ≤ f 0 := hf 0
  have hbase : 0 < (3 + f 0) / 2 := by positivity
  have ha : 0 < a := Real.rpow_pos_of_pos hbase _
  have hcRe : c.re = -(a / (1 - f 0)) := by
    change (((( (-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) /
      (1 - f 0 : ℝ)) * (a : ℂ)).re) = _
    rw [Complex.mul_re, Complex.div_ofReal_re]
    simp
    field_simp [hden.ne']
    <;> ring
  have hcne : c.re ≠ 0 := by
    rw [hcRe]
    exact neg_ne_zero.mpr (div_pos ha hden).ne'
  letI : IsProbabilityMeasure (ldpPositiveMeasure f) :=
    ldp_positive_measure_isProbability hf hfs hsymm h0
  have hchar := ldp_positive_characteristic_expansion hf hfs hg hgs hsymm hgsupp hrec
  have hX : Measurable (Nat.succ : ℕ → ℕ) := by fun_prop
  have hcase := (DirectedDistances.Paper.Section6.tauberian_characteristic
    ℕ (ldpPositiveMeasure f) Nat.succ hX).1
  have hresult := hcase c hcne (2 / 3 : ℝ) (by norm_num) (by norm_num) (by
    simpa only [a, c, Nat.succ_eq_add_one, Complex.star_def] using hchar)
  have hconst : -(c.re / Real.Gamma (1 - (2 / 3 : ℝ))) /
      Real.cos (Real.pi * (2 / 3 : ℝ) / 2) =
      2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ)) := by
    rw [hcRe]
    have harg : (1 : ℝ) - 2 / 3 = 1 / 3 := by norm_num
    have hcos : Real.cos (Real.pi * (2 / 3 : ℝ) / 2) = 1 / 2 := by
      rw [show Real.pi * (2 / 3 : ℝ) / 2 = Real.pi / 3 by ring,
        Real.cos_pi_div_three]
    rw [harg, hcos]
    field_simp [hden.ne', (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne']
    <;> ring
  have htail := hresult.2.2.2
  change (fun R : ℝ => (ldpPositiveMeasure f).real
      {ω : ℕ | R < (Nat.succ ω : ℝ)} -
        (-(c.re / Real.Gamma (1 - (2 / 3 : ℝ))) /
          Real.cos (Real.pi * (2 / 3 : ℝ) / 2)) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) at htail
  rw [hconst] at htail
  exact htail

include hf hfs hg hgs hsymm hgsupp hrec
/-- Proposition 6.1 applied to the reflected `g` law gives the strict
negative-increment tail coefficient in `eq:conc-asympt-2` -/
theorem ldp_reflected_g_measure_tail_asymptotic :
    let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
    (fun R : ℝ => (ldpReflectedGMeasure g).real
      {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
        (a / Real.Gamma (1 / 3 : ℝ)) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) := by
  let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
  let c : ℂ := (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2) * (a : ℂ)
  change (fun R : ℝ => (ldpReflectedGMeasure g).real
    {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
      (a / Real.Gamma (1 / 3 : ℝ)) * R ^ (-(2 / 3 : ℝ)))
    =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ)))
  have hf0 : 0 ≤ f 0 := hf 0
  have hbase : 0 < (3 + f 0) / 2 := by positivity
  have ha : 0 < a := Real.rpow_pos_of_pos hbase _
  have hcRe : c.re = -(a / 2) := by
    change (((( (-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / (2 : ℝ)) *
      (a : ℂ)).re) = _
    rw [Complex.mul_re, Complex.div_ofReal_re]
    simp
    ring
  have hcne : c.re ≠ 0 := by rw [hcRe]; exact (neg_ne_zero.mpr (by positivity))
  letI : IsProbabilityMeasure (ldpReflectedGMeasure g) :=
    ldp_reflected_g_measure_isProbability hg hgs hgsupp
  have hchar := ldp_reflected_g_characteristic_expansion hf hfs hg hgs hsymm hgsupp hrec
  have hX : Measurable (Nat.succ : ℕ → ℕ) := by fun_prop
  have hcase := (DirectedDistances.Paper.Section6.tauberian_characteristic
    ℕ (ldpReflectedGMeasure g) Nat.succ hX).1
  have hresult := hcase c hcne (2 / 3 : ℝ) (by norm_num) (by norm_num) (by
    simpa only [a, c, Nat.succ_eq_add_one, Complex.star_def] using hchar)
  have hconst : -(c.re / Real.Gamma (1 - (2 / 3 : ℝ))) /
      Real.cos (Real.pi * (2 / 3 : ℝ) / 2) = a / Real.Gamma (1 / 3 : ℝ) := by
    rw [hcRe]
    have harg : (1 : ℝ) - 2 / 3 = 1 / 3 := by norm_num
    have hcos : Real.cos (Real.pi * (2 / 3 : ℝ) / 2) = 1 / 2 := by
      rw [show Real.pi * (2 / 3 : ℝ) / 2 = Real.pi / 3 by ring,
        Real.cos_pi_div_three]
    rw [harg, hcos]
    field_simp [(Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne']
    <;> ring
  have htail := hresult.2.2.2
  change (fun R : ℝ => (ldpReflectedGMeasure g).real
      {ω : ℕ | R < (Nat.succ ω : ℝ)} -
        (-(c.re / Real.Gamma (1 - (2 / 3 : ℝ))) /
          Real.cos (Real.pi * (2 / 3 : ℝ) / 2)) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) at htail
  rw [hconst] at htail
  exact htail

include hf hfs hg hgs hsymm hgsupp hrec
/-- The source pmf tail for the absolute LDP increment, in the closed form of -/
theorem ldp_f_absolute_tail_asymptotic_of_master :
    let κ : ℝ := 3 + f 0
    (fun R : ℝ =>
      (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) *
          (κ / 2) ^ (1 / 3 : ℝ) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) := by
  let κ : ℝ := 3 + f 0
  let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
  change (fun R : ℝ =>
      (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) * a *
          R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ)))
  have h0 : f 0 < 1 :=
    (ldp_pmf_nondegenerate_of_master hf hfs hg hgs hsymm hgsupp hrec).1 0
  have hden : 0 < 1 - f 0 := sub_pos.mpr h0
  have hGammaPos : 0 < Real.Gamma (1 / 3 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hmeasure := ldp_positive_measure_tail_asymptotic
    hf hfs hg hgs hsymm hgsupp hrec
  change (fun R : ℝ => (ldpPositiveMeasure f).real
      {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
        (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ))) *
          R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) at hmeasure
  have hscaled : (fun R : ℝ => (1 - f 0) *
      ((ldpPositiveMeasure f).real {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
        (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ))) *
          R ^ (-(2 / 3 : ℝ)))) =o[atTop]
      (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) := by
    exact hmeasure.const_mul_left (1 - f 0)
  have hcoef : (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) * a =
      (1 - f 0) * (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ))) := by
    calc
      (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) * a =
          (2 / Real.Gamma (1 / 3 : ℝ)) * a := by
            rw [ldp_gamma_ratio_thirds]
      _ = (1 - f 0) *
          (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ))) := by
            field_simp [hden.ne', hGammaPos.ne']
            <;> ring
  have hleft : (fun R : ℝ =>
      (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) * a *
          R ^ (-(2 / 3 : ℝ))) =ᶠ[atTop]
      (fun R : ℝ => (1 - f 0) *
        ((ldpPositiveMeasure f).real {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
          (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ))) *
            R ^ (-(2 / 3 : ℝ)))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have hbridge := ldp_f_absolute_tail_eq_measure
      hf hfs hg hgs hsymm hgsupp hrec h0 R hR
    rw [hbridge]
    calc
      (1 - f 0) * (ldpPositiveMeasure f).real
          {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
            (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) * a *
              R ^ (-(2 / 3 : ℝ)) =
        (1 - f 0) * (ldpPositiveMeasure f).real
            {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
          ((1 - f 0) * (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ)))) *
            R ^ (-(2 / 3 : ℝ)) := by rw [hcoef]
      _ = (1 - f 0) * ((ldpPositiveMeasure f).real
            {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
          (2 * a / ((1 - f 0) * Real.Gamma (1 / 3 : ℝ))) *
            R ^ (-(2 / 3 : ℝ))) := by ring
  exact hscaled.congr' hleft.symm
    (Filter.Eventually.of_forall fun _ => rfl)

include hf hfs hg hgs hsymm hgsupp hrec
/-- The source pmf tail for the negative `g` increment, in the closed form of -/
theorem ldp_g_negative_tail_asymptotic_of_master :
    let κ : ℝ := 3 + f 0
    (fun R : ℝ =>
      (∑' y : ℤ, if (y : ℝ) < -R then g y else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) *
          (κ / 2) ^ (1 / 3 : ℝ) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) := by
  let κ : ℝ := 3 + f 0
  let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
  change (fun R : ℝ =>
      (∑' y : ℤ, if (y : ℝ) < -R then g y else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) * a *
          R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ)))
  have hGammaPos : 0 < Real.Gamma (1 / 3 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hmeasure := ldp_reflected_g_measure_tail_asymptotic
    hf hfs hg hgs hsymm hgsupp hrec
  change (fun R : ℝ => (ldpReflectedGMeasure g).real
      {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
        (a / Real.Gamma (1 / 3 : ℝ)) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) at hmeasure
  have hsplit : Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) /
      (2 * Real.pi) =
      (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) / 2 := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hcoef : (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) /
      (2 * Real.pi)) * a = a / Real.Gamma (1 / 3 : ℝ) := by
    calc
      (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) * a =
          ((Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) / 2) * a := by
            rw [hsplit]
      _ = ((2 / Real.Gamma (1 / 3 : ℝ)) / 2) * a := by
            rw [← ldp_gamma_ratio_thirds]
      _ = a / Real.Gamma (1 / 3 : ℝ) := by
            field_simp [hGammaPos.ne']
            <;> ring
  have hleft : (fun R : ℝ =>
      (∑' y : ℤ, if (y : ℝ) < -R then g y else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) * a *
          R ^ (-(2 / 3 : ℝ))) =ᶠ[atTop]
      (fun R : ℝ => (ldpReflectedGMeasure g).real
        {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
          (a / Real.Gamma (1 / 3 : ℝ)) * R ^ (-(2 / 3 : ℝ))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have hbridge := ldp_g_negative_tail_eq_measure hg hgs hgsupp R hR
    calc
      (∑' y : ℤ, if (y : ℝ) < -R then g y else 0) -
          (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) * a *
            R ^ (-(2 / 3 : ℝ)) =
        (ldpReflectedGMeasure g).real
          {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
            ((Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) * a) *
              R ^ (-(2 / 3 : ℝ)) := by rw [hbridge]
      _ = (ldpReflectedGMeasure g).real
          {n : ℕ | R < ((n + 1 : ℕ) : ℝ)} -
            (a / Real.Gamma (1 / 3 : ℝ)) * R ^ (-(2 / 3 : ℝ)) := by
              rw [hcoef]
  exact hmeasure.congr' hleft.symm
    (Filter.Eventually.of_forall fun _ => rfl)

end LDP

end DirectedDistances.Recursive
