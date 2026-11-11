/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantBridgeGoodMiddle
public import DirectedDistances.RandomWalk.QuadrantBridgePaddingEmbedding
public import DirectedDistances.PaperProofs.Section3.UIBOTQuadrantBridgeCarrier
import all DirectedDistances.RandomWalk.QuadrantBridgeGoodMiddle
import all DirectedDistances.RandomWalk.QuadrantBridgePadding2
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Subexponential conditioning helpers toward Proposition 3.9 -/

public section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open scoped ENNReal

private noncomputable def goodFiniteWordsEquiv (m k : ℕ) :
    {q : Fin m → Fin 3 // ∃ w : BoundedPaddingMiddleWords m k,
      w.val = List.ofFn q} ≃ BoundedPaddingMiddleWords m k := by
  classical
  let f : {q : Fin m → Fin 3 // ∃ w : BoundedPaddingMiddleWords m k,
      w.val = List.ofFn q} → BoundedPaddingMiddleWords m k :=
    fun q => Classical.choose q.property
  have hf (q) : (f q).val = List.ofFn q.val := Classical.choose_spec q.property
  apply Equiv.ofBijective f
  constructor
  · intro q r h
    apply Subtype.ext
    apply List.ofFn_injective
    rw [← hf q, ← hf r, h]
  · intro w
    let q := (uibotFiniteWordEquiv m).symm ⟨w.val, w.property.1⟩
    have hq : List.ofFn q = w.val :=
      congrArg Subtype.val ((uibotFiniteWordEquiv m).apply_symm_apply
        ⟨w.val, w.property.1⟩)
    refine ⟨⟨q, w, hq.symm⟩, ?_⟩
    apply Subtype.ext
    exact (hf _).trans hq

/-- Helper toward Proposition 3.9: the good middle-word event has probability
equal to its finite word count divided by the size of the uniform alphabet power. -/
theorem boundedPaddingMiddleWords_goodEvent_probability (m k : ℕ) :
    iidCodeMeasure.real (boundedPaddingMiddleWordsGoodEvent m k) =
      (Nat.card (BoundedPaddingMiddleWords m k) : ℝ) / (3 : ℝ) ^ m := by
  classical
  let s : Set (Fin m → Fin 3) :=
    {q | ∃ w : BoundedPaddingMiddleWords m k, w.val = List.ofFn q}
  have hevent : boundedPaddingMiddleWordsGoodEvent m k =
      (fun ω : ℕ → Fin 3 => fun i : Fin m => ω (i.val + 1)) ⁻¹' s := rfl
  have hcard : (Finset.univ.filter (fun q : Fin m → Fin 3 => q ∈ s)).card =
      Nat.card (BoundedPaddingMiddleWords m k) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (goodFiniteWordsEquiv m k)
  rw [Measure.real, hevent, ← Measure.map_apply (by fun_prop) (Set.to_countable s).measurableSet,
    iidCodeMeasure_map_firstCodes, Measure.uniformOfFinset_apply, hcard]
  simp [ENNReal.toReal_div, ENNReal.toReal_pow]

/-- Helper toward Proposition 3.9: the Gaussian maximal estimate gives a
lower bound on the number of bounded middle words, without a counting premise. -/
theorem boundedPaddingMiddleWords_card_lower (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (3 : ℝ) ^ m * (1 - 4 * Real.exp (-((k : ℝ) ^ 2) / (2 * (m : ℝ)))) ≤
      (Nat.card (BoundedPaddingMiddleWords m k) : ℝ) := by
  have hmeas : MeasurableSet (boundedPaddingMiddleWordsGoodEvent m k) := by
    change MeasurableSet ((fun ω : ℕ → Fin 3 =>
      fun i : Fin m => ω (i.val + 1)) ⁻¹'
      {q | ∃ w : BoundedPaddingMiddleWords m k, w.val = List.ofFn q})
    exact (Set.to_countable _).measurableSet.preimage (by fun_prop)
  have htail := (measureReal_mono
    (boundedPaddingMiddleWordsGoodEvent_compl_subset_blockMax m k)).trans
      (iidCodeWalk_blockMax_tail 0 m hm (k : ℝ) (by exact_mod_cast hk))
  have hsum := measureReal_add_measureReal_compl (μ := iidCodeMeasure) hmeas
  rw [probReal_univ, boundedPaddingMiddleWords_goodEvent_probability] at hsum
  have hp : (0 : ℝ) < 3 ^ m := by positivity
  rw [mul_comm]
  apply (le_div_iff₀ hp).mp
  linarith only [htail, hsum]

private theorem admissible_probability_padding_lower
    (ℓ ρ n k : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hk : max 0 (max (ρ - 1) 1) ≤ k)
    (hN : padding2PrefixLength 0 (ρ - 1) k +
      padding2LoopBudget (ℓ - 1) 0 k < n - 1)
    (hc : n + ℓ + ρ ≡ 0 [MOD 3]) :
    letI : MeasurableSpace (Fin 3) := ⊤
    let m := padding2MiddleLength 0 (ρ - 1) (ℓ - 1) 0 k (n - 1)
    (1 - 4 * Real.exp (-((k : ℝ) ^ 2) / (2 * (m : ℝ)))) *
      ((3 : ℝ) ^ m / (3 : ℝ) ^ (n - 1)) ≤
      (uibotFiniteIIDWordLaw n).real {w | KMSWWalkAdmissible ℓ ρ n w} := by
  let : MeasurableSpace (Fin 3) := ⊤
  dsimp only
  let m := padding2MiddleLength 0 (ρ - 1) (ℓ - 1) 0 k (n - 1)
  have hm : 0 < m := by unfold m padding2MiddleLength; omega
  have hkpos : 0 < k := by omega
  have hcong : (0 : ℤ) - (ρ - 1 : ℕ) - (n - 1 : ℕ) ≡
      ((ℓ - 1 : ℕ) : ℤ) - 0 [ZMOD (3 : ℤ)] := by
    unfold Nat.ModEq at hc
    unfold Int.ModEq
    omega
  have hcard := padding2_card_le_quadrantBridgeWords
    0 (ρ - 1) (ℓ - 1) 0 k (n - 1) hk hN.le hcong
  have hlower := boundedPaddingMiddleWords_card_lower m k hm hkpos
  have hreal : (Nat.card (BoundedPaddingMiddleWords m k) : ℝ) ≤
      Nat.card (QuadrantBridgeWords (n - 1) (0, ρ - 1) (ℓ - 1, 0)) := by
    exact_mod_cast hcard
  rw [Measure.real, uibotFiniteIIDWordLaw_admissible_eq_card_quadrantBridgeWords
    ℓ ρ n hℓ hρ hn]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]
  change (1 - _) * (3 ^ m / 3 ^ (n - 1)) ≤ _
  rw [← mul_div_assoc, mul_comm (1 - _)]
  exact div_le_div_of_nonneg_right (hlower.trans hreal) (by positivity)

private noncomputable def conditioningCutoff (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ (3 / 4 : ℝ)⌉₊

private theorem conditioningCutoff_div_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (conditioningCutoff n : ℝ) / n)
      Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 4 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      tendsto_natCast_atTop_atTop
  have hc := (tendsto_nat_ceil_div_atTop (R := ℝ)).comp hp
  have hr := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hprod := hc.mul hr
  simp only [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp only [Function.comp_def]
  rw [show -(1 / 4 : ℝ) = 3 / 4 - 1 by norm_num,
    Real.rpow_sub hnpos, Real.rpow_one]
  dsimp only [conditioningCutoff]
  field_simp

private theorem conditioningCutoff_tendsto_atTop :
    Filter.Tendsto conditioningCutoff Filter.atTop Filter.atTop := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [hp.eventually (Filter.eventually_ge_atTop (b : ℝ))] with n hn
  have h := hn.trans (Nat.le_ceil ((n : ℝ) ^ (3 / 4 : ℝ)))
  exact_mod_cast h

private theorem conditioning_budget_eventually (ℓ ρ : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      padding2PrefixLength 0 (ρ - 1) (conditioningCutoff n) +
        padding2LoopBudget (ℓ - 1) 0 (conditioningCutoff n) < n - 1 := by
  have ht : Filter.Tendsto
      (fun n : ℕ => (9 * (conditioningCutoff n : ℝ) + 2 * ℓ) / n)
      Filter.atTop (nhds 0) := by
    have h := (conditioningCutoff_div_tendsto_zero.const_mul 9).add
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 * (ℓ : ℝ)))
    simpa only [mul_zero, add_zero, add_div, mul_div_assoc] using h
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    Filter.eventually_ge_atTop 4] with n hn hn4
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb := (div_lt_iff₀ hnpos).mp hn
  have hb' : 9 * conditioningCutoff n + 2 * ℓ < n - 1 := by
    have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hlt : (9 * conditioningCutoff n + 2 * ℓ : ℕ) + 1 < (n : ℝ) := by
      push_cast
      linarith only [hb, hn4']
    have : 9 * conditioningCutoff n + 2 * ℓ + 1 < n := by exact_mod_cast hlt
    omega
  unfold padding2PrefixLength padding2LoopBudget
  omega

private theorem conditioning_middleLength_eventually_pos (ℓ ρ : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < padding2MiddleLength 0 (ρ - 1) (ℓ - 1) 0
        (conditioningCutoff n) (n - 1) := by
  filter_upwards [conditioning_budget_eventually ℓ ρ] with n hn
  unfold padding2MiddleLength
  omega

private theorem conditioning_gaussian_error_tendsto_zero (ℓ ρ : ℕ) :
    Filter.Tendsto (fun n : ℕ =>
      4 * Real.exp (-((conditioningCutoff n : ℝ) ^ 2) /
        (2 * (padding2MiddleLength 0 (ρ - 1) (ℓ - 1) 0
          (conditioningCutoff n) (n - 1) : ℝ)))) Filter.atTop (nhds 0) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hexponent : Filter.Tendsto (fun n : ℕ =>
      ((conditioningCutoff n : ℝ) ^ 2) /
        (2 * (padding2MiddleLength 0 (ρ - 1) (ℓ - 1) 0
          (conditioningCutoff n) (n - 1) : ℝ))) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [hp.eventually (Filter.eventually_ge_atTop (2 * b)),
      conditioning_middleLength_eventually_pos ℓ ρ] with n hn hm
    let m := padding2MiddleLength 0 (ρ - 1) (ℓ - 1) 0 (conditioningCutoff n) (n - 1)
    have hmn : m ≤ n := by unfold m padding2MiddleLength; omega
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hnpos : (0 : ℝ) < n := hmpos.trans_le hmn'
    dsimp only [Function.comp_def] at hn
    have hs : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hk := Nat.le_ceil ((n : ℝ) ^ (3 / 4 : ℝ))
    have hsq : (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) ≤
        (conditioningCutoff n : ℝ) ^ 2 := by
      calc
        (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
            ((n : ℝ) ^ (3 / 4 : ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          rw [show (3 / 4 : ℝ) * (2 : ℕ) = 1 + 1 / 2 by norm_num,
            Real.rpow_add hnpos, Real.rpow_one]
        _ ≤ (conditioningCutoff n : ℝ) ^ 2 := by
          exact pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hk 2
    change b ≤ (conditioningCutoff n : ℝ) ^ 2 / (2 * (m : ℝ))
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
    have hmul := mul_le_mul_of_nonneg_right hn (le_of_lt hmpos)
    have hmul' := mul_le_mul_of_nonneg_left hmn' hs
    nlinarith only [hmul, hmul', hsq]
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hexponent).const_mul 4
  simpa only [mul_zero, neg_div, Function.comp_def] using h

/-- Helper toward Proposition 3.9: the probability of the exact finite
admissible word event is eventually at least every prescribed exponential
scale, along the necessary size-boundary congruence. -/
theorem uibotFiniteIIDWordLaw_admissible_subexponential
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) :
    letI : MeasurableSpace (Fin 3) := ⊤
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        n + ℓ + ρ ≡ 0 [MOD 3] →
          Real.exp (-ε * (n : ℝ)) ≤
            (uibotFiniteIIDWordLaw n).real
              {w | KMSWWalkAdmissible ℓ ρ n w} := by
  let : MeasurableSpace (Fin 3) := ⊤
  intro ε hε
  have hcost : Filter.Tendsto (fun n : ℕ =>
      (Real.log 3 * (9 * (conditioningCutoff n : ℝ) + 2 * ℓ) + Real.log 2) / n)
      Filter.atTop (nhds 0) := by
    have h := (conditioningCutoff_div_tendsto_zero.const_mul (Real.log 3 * 9)).add
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ)
        (Real.log 3 * (2 * ℓ) + Real.log 2))
    simp only [mul_zero, add_zero] at h
    convert h using 1
    funext n
    ring
  filter_upwards [hcost.eventually (gt_mem_nhds hε),
    (conditioning_gaussian_error_tendsto_zero ℓ ρ).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    conditioning_budget_eventually ℓ ρ,
    conditioningCutoff_tendsto_atTop.eventually
      (Filter.eventually_ge_atTop (max 0 (max (ρ - 1) 1))),
    Filter.eventually_ge_atTop 1] with n hcostn herr hbudget hk hn
  intro hc
  let k := conditioningCutoff n
  let P := padding2PrefixLength 0 (ρ - 1) k
  let Q := padding2LoopBudget (ℓ - 1) 0 k
  let m := padding2MiddleLength 0 (ρ - 1) (ℓ - 1) 0 k (n - 1)
  have hbudget' : P + Q < n - 1 := hbudget
  have hnm : n - 1 = m + (P + Q) := by
    dsimp only [m, P, Q, padding2MiddleLength]
    dsimp only [P, Q] at hbudget'
    omega
  have hbudget_bound : P + Q ≤ 9 * k + 2 * ℓ := by
    dsimp only [P, Q, padding2PrefixLength, padding2LoopBudget]
    omega
  have hbudget_bound' : ((P + Q : ℕ) : ℝ) ≤ 9 * (k : ℝ) + 2 * ℓ := by
    exact_mod_cast hbudget_bound
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcostn' := (div_lt_iff₀ hnpos).mp hcostn
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hscale : Real.log 2 + Real.log 3 * (P + Q : ℕ) ≤ ε * n := by
    have hb := mul_le_mul_of_nonneg_left hbudget_bound' hlog3
    dsimp only [k] at hb
    linarith only [hb, hcostn']
  have hratio : (3 : ℝ) ^ m / 3 ^ (n - 1) =
      Real.exp (-Real.log 3 * (P + Q : ℕ)) := by
    rw [hnm, pow_add]
    rw [neg_mul, mul_comm (Real.log 3), Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    field_simp
  have hhalf : Real.exp (-(Real.log 2 + Real.log 3 * (P + Q : ℕ))) =
      (1 / 2 : ℝ) * ((3 : ℝ) ^ m / 3 ^ (n - 1)) := by
    rw [hratio, neg_add, Real.exp_add, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [neg_mul, one_div]
  have hlower := admissible_probability_padding_lower ℓ ρ n k hℓ hρ hn hk hbudget hc
  dsimp only at hlower
  calc
    Real.exp (-ε * (n : ℝ)) ≤
        Real.exp (-(Real.log 2 + Real.log 3 * (P + Q : ℕ))) := by
      apply Real.exp_le_exp.mpr
      linarith only [hscale]
    _ = (1 / 2 : ℝ) * ((3 : ℝ) ^ m / 3 ^ (n - 1)) := hhalf
    _ ≤ (1 - 4 * Real.exp (-((k : ℝ) ^ 2) / (2 * (m : ℝ)))) *
        ((3 : ℝ) ^ m / 3 ^ (n - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [k, m]
      linarith only [herr]
    _ ≤ (uibotFiniteIIDWordLaw n).real {w | KMSWWalkAdmissible ℓ ρ n w} := hlower

end DirectedDistances.PaperProofs.Section3
