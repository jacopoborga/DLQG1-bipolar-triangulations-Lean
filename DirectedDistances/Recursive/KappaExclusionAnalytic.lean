/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.StableCLT
public import DirectedDistances.Recursive.SDPExpansionF
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Analytic kappa-positive exclusion helpers for the SDP case

This file formalizes the analytic half of the `κ > 0` exclusion in
scalar CLT input cited there as [JS, Chapter VII]. These are helper statements,
not a formalization of the paper's geometric argument or its exclusion result. -/

public section

namespace DirectedDistances.Recursive.SDPExpansion

open Asymptotics Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

/-- The real-line law obtained by placing the symmetric integer pmf at its
integer values. -/
@[expose] noncomputable def mu_f (f : ℤ → ℝ) : Measure ℝ :=
  Measure.sum fun k : ℤ => ENNReal.ofReal (f k) • Measure.dirac (k : ℝ)

/-- A nonnegative summable integer mass of total mass one gives a probability
measure on the real line. -/
theorem mu_f_isProbabilityMeasure {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hfs : HasSum f (1 : ℝ)) :
    IsProbabilityMeasure (mu_f f) := by
  exact HasSum.isProbabilityMeasure_sum_dirac hf hfs

/-- The characteristic function of `mu_f` is the integer characteristic -/
theorem mu_f_charFun {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) (t : ℝ) :
    charFun (mu_f f) t = integerCF f t := by
  rw [charFun_apply_real]
  change (∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂
    Measure.sum (fun k : ℤ => ENNReal.ofReal (f k) • Measure.dirac (k : ℝ))) = _
  rw [integral_sum_dirac (fun k => ENNReal.ofReal_ne_top)]
  rw [integerCF]
  apply tsum_congr
  intro k
  simp only [ENNReal.toReal_ofReal (hf k), Complex.real_smul]
  congr 1
  push_cast
  ring

/-- The law `mu_f` is symmetric under reflection, by reindexing the integer
mass with `k ↦ -k`. -/
theorem mu_f_symmetric {f : ℤ → ℝ} (hsymm : ∀ k : ℤ, f (-k) = f k) :
    (mu_f f).map (fun x : ℝ => -x) = mu_f f := by
  rw [mu_f, Measure.map_sum (measurable_neg.aemeasurable)]
  simp_rw [Measure.map_smul _ measurable_neg.aemeasurable, Measure.map_dirac]
  rw [← Measure.sum_comp_equiv (Equiv.neg ℤ)
    (fun k : ℤ => ENNReal.ofReal (f k) • Measure.dirac (-(k : ℝ)))]
  congr 1
  funext k
  simp [hsymm]

/-- Reflection symmetry makes the real characteristic function even. -/
theorem mu_f_charFun_even {f : ℤ → ℝ}
    (hsymm : ∀ k : ℤ, f (-k) = f k) (t : ℝ) :
    charFun (mu_f f) (-t) = charFun (mu_f f) t := by
  have hneg : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by
    funext x
    ring
  calc
    charFun (mu_f f) (-t) = charFun ((mu_f f).map ((-1 : ℝ) * ·)) t := by
      simpa only [neg_one_mul] using (charFun_map_mul (μ := mu_f f) (-1) t).symm
    _ = charFun ((mu_f f).map (fun x : ℝ => -x)) t := by rw [hneg]
    _ = charFun (mu_f f) t := by rw [mu_f_symmetric hsymm]

/-- The characteristic function of the symmetric law is real. This follows
from evenness and `charFun_neg`, rather than from a separate series estimate. -/
theorem mu_f_charFun_im_zero {f : ℤ → ℝ}
    (hsymm : ∀ k : ℤ, f (-k) = f k) (t : ℝ) :
    (charFun (mu_f f) t).im = 0 := by
  have heven := mu_f_charFun_even hsymm t
  rw [charFun_neg] at heven
  have him := congrArg Complex.im heven
  have him' : -(charFun (mu_f f) t).im = (charFun (mu_f f) t).im := by
    simpa using him
  nlinarith

/-- The positive-side characteristic expansion extends to a two-sided
expansion for the symmetric real law. This is the transform input to the
heavy-tailed CLT, not a paper theorem. -/
theorem mu_f_twoSided_expansion {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hfs : HasSum f (1 : ℝ)) (hsymm : ∀ k : ℤ, f (-k) = f k)
    {a : ℝ} (_ha : 0 < a)
    (hExp : (fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (a : ℂ) * (t ^ (2 / 3 : ℝ) : ℝ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (2 / 3 : ℝ))) :
    (fun t : ℝ => charFun (mu_f f) t -
        ((1 : ℂ) - (a : ℂ) * (|t| ^ (2 / 3 : ℝ) : ℝ))) =o[𝓝 0]
      (fun t : ℝ => |t| ^ (2 / 3 : ℝ)) := by
  let E : ℝ → ℂ := fun t => charFun (mu_f f) t -
    ((1 : ℂ) - (a : ℂ) * (|t| ^ (2 / 3 : ℝ) : ℝ))
  let G : ℝ → ℝ := fun t => |t| ^ (2 / 3 : ℝ)
  have hpos : E =o[𝓝[>] (0 : ℝ)] G := by
    apply isLittleO_iff.2
    intro c hc
    have hb := hExp.bound hc
    filter_upwards [hb, self_mem_nhdsWithin] with t ht htp
    simpa [E, G, mu_f_charFun hf t, abs_of_pos htp] using ht
  have hEe : ∀ t, E (-t) = E t := by
    intro t
    simp [E, mu_f_charFun_even hsymm t, abs_neg]
  have hGe : ∀ t, G (-t) = G t := by
    intro t
    simp [G, abs_neg]
  have hneg : E =o[𝓝[<] (0 : ℝ)] G := by
    have hmap : Tendsto (fun t : ℝ => -t)
        (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hcont : ContinuousAt (fun t : ℝ => -t) (0 : ℝ) := continuous_neg.continuousAt
        simpa using hcont.tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    have hcomp := hpos.comp_tendsto hmap
    convert hcomp using 1 <;> ext t
    · exact (hEe t).symm
    · exact (hGe t).symm
  have hμ : IsProbabilityMeasure (mu_f f) := mu_f_isProbabilityMeasure hf hfs
  have h0cf : charFun (mu_f f) 0 = 1 := by
    simp [charFun_zero, Measure.real, hμ.measure_univ]
  have hzero : E =o[pure (0 : ℝ)] G := by
    apply isLittleO_iff.2
    intro c hc
    simp [E, G, h0cf]
  have hfilter : 𝓝[<] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ) = 𝓝[≠] (0 : ℝ) := by
    rw [← nhdsWithin_union]
    congr 1
    ext t
    simp
  have hpunc : E =o[𝓝[≠] (0 : ℝ)] G := by
    rw [← hfilter]
    exact hneg.sup hpos
  simpa only [← nhdsNE_sup_pure (0 : ℝ)] using hpunc.sup hzero

/-- Continuity from below supplies a positive threshold with positive mass
from any symmetric non-Dirac probability law that charges `(0,∞)`. -/
private theorem exists_pos_Ioi_mass {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : 0 < μ (Ioi 0)) : ∃ ε : ℝ, 0 < ε ∧ 0 < μ (Ioi ε) := by
  let s : ℕ → Set ℝ := fun n => Ioi (1 / ((n : ℝ) + 1))
  have hsmono : Monotone s := by
    intro n m hnm x hx
    have hden : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      nlinarith
    have hdenpos : 0 < (n : ℝ) + 1 := by positivity
    have hdenpos' : 0 < (m : ℝ) + 1 := by positivity
    have hrecip : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hdenpos hden
    exact lt_of_le_of_lt hrecip hx
  have hUnion : (⋃ n : ℕ, s n) = Ioi 0 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioi, s]
    constructor
    · rintro ⟨n, hn⟩
      have hnpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact lt_trans hnpos hn
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / x)
      have hden : 0 < (n : ℝ) + 1 := by positivity
      have hn' : 1 < x * ((n : ℝ) + 1) := by
        have := (div_lt_iff₀ hx).mp hn
        nlinarith
      refine ⟨n, ?_⟩
      rw [div_lt_iff₀ hden]
      exact hn'
  have hmeasure : μ (Ioi 0) = ⨆ n : ℕ, μ (s n) := by
    rw [← hUnion]
    exact hsmono.measure_iUnion
  rw [hmeasure] at hμ
  obtain ⟨n, hn⟩ := (lt_iSup_iff).mp hμ
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

/-- For iid variables with law `mu_f`, the `2/3` stable limit gives a fixed
positive lower-tail probability above a `k^(3/2)` threshold. This is the scalar
heavy-tailed CLT input cited as [JS, Chapter VII] in -/
theorem iid_sum_has_positive_three_halves_tail
    {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ k : ℤ, f (-k) = f k) {a : ℝ} (ha : 0 < a)
    (hExp : (fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (a : ℂ) * (t ^ (2 / 3 : ℝ) : ℝ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (2 / 3 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hLaw : P.map (X 0) = mu_f f) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      c ≤ (P.real {ω | ε * (k : ℝ) ^ (3 / 2 : ℝ) <
        ∑ i ∈ Finset.range k, X i ω}) := by
  have hexpStable :
      (fun t : ℝ => charFun (P.map (X 0)) t -
        (1 - (a : ℂ) * (|t| ^ (2 / 3 : ℝ) : ℝ))) =o[𝓝 0]
        (fun t : ℝ => |t| ^ (2 / 3 : ℝ)) := by
    rw [hLaw]
    exact mu_f_twoSided_expansion hf hfs hsymm ha hExp
  obtain ⟨ν, hνcf, hdist, hνnondeg, hνsymm, hνpos⟩ :=
    DirectedDistances.Probability.exists_stableLaw_tendstoInDistribution
      (hX := hX) hindep hident ha (by norm_num : (0 : ℝ) < 2 / 3) hexpStable
  obtain ⟨ε, hε, hεmass⟩ := exists_pos_Ioi_mass hνpos
  let Y : ℕ → Ω → ℝ := fun k ω =>
    (k : ℝ) ^ (-1 / (2 / 3 : ℝ)) * ∑ i ∈ Finset.range k, X i ω
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    hdist.tendsto (G := Ioi ε) isOpen_Ioi
  let m : ℝ≥0∞ := (ν : Measure ℝ) (Ioi ε)
  have hfinite : m ≠ ∞ :=
    measure_ne_top (ν : Measure ℝ) (Ioi ε)
  let c : ℝ := m.toReal / 2
  have hc : 0 < c := half_pos (ENNReal.toReal_pos hεmass.ne' hfinite)
  have hsmall : ENNReal.ofReal c < m := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal hc.le hfinite).mpr
    exact half_lt_self (ENNReal.toReal_pos hεmass.ne' hfinite)
  have hprob : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal c < (P.map (Y k)) (Ioi ε) :=
    eventually_lt_of_lt_liminf (hsmall.trans_le (by simpa [Y, m] using hport))
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hprob
  refine ⟨ε, hε, c, hc, max K₀ 1, fun k hk => ?_⟩
  have hk₀ : 0 < (k : ℝ) := by
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
    exact_mod_cast (Nat.zero_lt_of_lt hk1)
  have hscale : (k : ℝ) ^ (-1 / (2 / 3 : ℝ)) =
      1 / ((k : ℝ) ^ (3 / 2 : ℝ)) := by
    rw [show (-1 / (2 / 3 : ℝ)) = -(3 / 2 : ℝ) by norm_num,
      Real.rpow_neg hk₀.le]
    simp only [one_div]
  have hden : 0 < (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hk₀ _
  have hY : Measurable (Y k) := by
    dsimp [Y]
    exact Measurable.const_mul (Finset.measurable_fun_sum _ (fun i _ => hX i)) _
  have hmeas := (hK₀ k (le_trans (le_max_left _ _) hk)).le
  have hmap : ENNReal.ofReal c ≤ (P {ω | ε < Y k ω}) := by
    rw [Measure.map_apply hY isOpen_Ioi.measurableSet] at hmeas
    simpa only [Set.preimage, Set.mem_Ioi] using hmeas
  have hreal := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hmap
  have hsum_eq : {ω | ε < Y k ω} =
      {ω | ε * (k : ℝ) ^ (3 / 2 : ℝ) <
        ∑ i ∈ Finset.range k, X i ω} := by
    ext ω
    dsimp [Y]
    rw [hscale]
    rw [show (1 / ((k : ℝ) ^ (3 / 2 : ℝ))) *
        (∑ i ∈ Finset.range k, X i ω) =
          (∑ i ∈ Finset.range k, X i ω) / ((k : ℝ) ^ (3 / 2 : ℝ)) by
      rw [div_eq_mul_inv]
      ring]
    exact lt_div_iff₀ hden
  simpa [Measure.real, hsum_eq] using hreal

/-- The analytic heavy-tailed input contradicts any uniform high-probability
linear upper bound. This establishes only the analytic half of the `κ > 0`
bound used by the paper is a separate input. -/
theorem not_uniform_high_probability_linear_bound
    {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ k : ℤ, f (-k) = f k) {a : ℝ} (ha : 0 < a)
    (hExp : (fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (a : ℂ) * (t ^ (2 / 3 : ℝ) : ℝ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (2 / 3 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hLaw : P.map (X 0) = mu_f f) :
    ¬ ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤ (P.real {ω | ∑ i ∈ Finset.range k, X i ω ≤
        2 * A * (k : ℝ) + 1}) := by
  obtain ⟨ε, hε, c, hc, K, htail⟩ :=
    iid_sum_has_positive_three_halves_tail hf hfs hsymm ha hExp
      hX hindep hident hLaw
  intro hlinear
  let δ : ℝ := c / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A, hA⟩ := hlinear δ hδ
  have hroot : Tendsto (fun k : ℕ => (k : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ k : ℕ in atTop,
      2 * A + 1 < ε * (k : ℝ) ^ (1 / 2 : ℝ) := by
    filter_upwards [hroot.eventually (eventually_gt_atTop ((2 * A + 1) / ε))]
      with k hk
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hk
  have hpositive : ∀ᶠ k : ℕ in atTop, 1 ≤ k :=
    eventually_atTop.2 ⟨1, fun k hk => hk⟩
  have hbound : ∀ᶠ k : ℕ in atTop,
      2 * A * (k : ℝ) + 1 < ε * (k : ℝ) ^ (3 / 2 : ℝ) := by
    filter_upwards [hlarge, hpositive] with k hklarge hkpos
    have hkreal : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hkpos)
    have hpow : (k : ℝ) ^ (3 / 2 : ℝ) =
        (k : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hkreal, Real.rpow_one]
    calc
      2 * A * (k : ℝ) + 1 = 1 + 2 * A * (k : ℝ) := by ring
      _ ≤ (k : ℝ) + 2 * A * (k : ℝ) := by
        have hkreal' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        simpa [add_comm] using add_le_add_right hkreal' (2 * A * (k : ℝ))
      _ = (k : ℝ) * (2 * A + 1) := by ring
      _ < (k : ℝ) * (ε * (k : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_lt_mul_of_pos_left hklarge hkreal
      _ = ε * (k : ℝ) ^ (3 / 2 : ℝ) := by rw [hpow]; ring
  obtain ⟨Klin, hKlin⟩ := eventually_atTop.1 hbound
  let k : ℕ := max K Klin
  have hkK : K ≤ k := le_max_left _ _
  have hkLin : Klin ≤ k := le_max_right _ _
  have hthreshold := hKlin k hkLin
  let E : Set Ω := {ω | ε * (k : ℝ) ^ (3 / 2 : ℝ) <
    ∑ i ∈ Finset.range k, X i ω}
  let H : Set Ω := {ω | ∑ i ∈ Finset.range k, X i ω ≤ 2 * A * (k : ℝ) + 1}
  have hSmeas : Measurable (fun ω => ∑ i ∈ Finset.range k, X i ω) :=
    Finset.measurable_fun_sum _ (fun i _ => hX i)
  have hEm : MeasurableSet E := by
    change MeasurableSet ((fun ω => ∑ i ∈ Finset.range k, X i ω) ⁻¹'
      Ioi (ε * (k : ℝ) ^ (3 / 2 : ℝ)))
    exact (isOpen_Ioi.measurableSet.preimage hSmeas)
  have hsub : H ⊆ Eᶜ := by
    intro ω hω hEω
    dsimp [H] at hω
    dsimp [E] at hEω
    exact not_lt_of_ge (le_trans hω (le_of_lt hthreshold)) hEω
  have hcompl := probReal_add_probReal_compl (μ := P) hEm
  have htailk : c ≤ P.real E := by simpa [E] using htail k hkK
  have hlinearK : 1 - δ ≤ P.real H := by simpa [H] using hA k
  have hsmall : P.real H ≤ P.real Eᶜ :=
    measureReal_mono (μ := P) hsub (measure_ne_top P _)
  have hcompl' : P.real E + P.real Eᶜ = 1 := hcompl
  have hdelta_lt_c : δ < c := by dsimp [δ]; linarith
  linarith

end DirectedDistances.Recursive.SDPExpansion
