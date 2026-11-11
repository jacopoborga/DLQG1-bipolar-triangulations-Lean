/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.StrictRecordCount
public import DirectedDistances.RandomWalk.ConditionedVectorPrefixSupport
public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Regular record counts on a block event

Deterministic and measure-theoretic counting ingredients in the proof of -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The block event forces at least square-root many regular strict records.
This is the deterministic counting step in Lemma 4.12 -/
theorem sqrt_le_card_regularRecords_of_block (p : ℕ → ℤ × ℤ) (N : ℕ)
    (hstep : ∀ i, i < N → (p i).2 - 1 ≤ (p (i + 1)).2)
    (hE : p ∈ {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}) :
    Real.sqrt N ≤ (((Finset.Icc ((N + 1) / 2) N).filter
      (fun n => p ∈ {p : ℕ → ℤ × ℤ |
        (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n})).card : ℝ) := by
  classical
  rcases hE with ⟨hregular, hearly, hterminal⟩
  let m : ℕ := N / 2
  let b : ℤ := ⌈-(Real.sqrt N)⌉
  let r : ℕ → ℤ := fun i => (p i).2
  have hmN : m ≤ N := by dsimp [m]; omega
  have hstep' : ∀ i, i < N → r i - 1 ≤ r (i + 1) := by
    simpa only [r] using hstep
  have hearly' : ∀ i, i ≤ m → b ≤ r i := by
    intro i hi
    have hiReal : (i : ℝ) ≤ (N : ℝ) / 2 := by
      dsimp [m] at hi
      calc
        (i : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hi
        _ ≤ (N : ℝ) / 2 := Nat.cast_div_le
    have hri := hearly i hiReal
    dsimp [b, r]
    exact Int.ceil_le.mpr hri
  have hcount := sub_terminal_toNat_le_card_strictRecords r m N b hmN hstep' hearly'
  have hfloor : (b - r N).toNat = b - r N := by
    apply Int.toNat_of_nonneg
    have hb : (-(Real.sqrt N) : ℝ) ≤ (b : ℝ) := by
      dsimp [b]
      exact Int.le_ceil _
    have hbr : (Real.sqrt N : ℝ) ≤ (b : ℝ) - (r N : ℝ) := by
      dsimp [r]
      linarith
    exact_mod_cast (show (0 : ℝ) ≤ (b : ℝ) - (r N : ℝ) by
      linarith [Real.sqrt_nonneg N])
  have hheight : (Real.sqrt N : ℝ) ≤ ((b - r N : ℤ) : ℝ) := by
    have hb : (-(Real.sqrt N) : ℝ) ≤ (b : ℝ) := by
      dsimp [b]
      exact Int.le_ceil _
    have ht : (r N : ℝ) ≤ -2 * Real.sqrt N := by
      dsimp [r]
      exact_mod_cast hterminal
    dsimp [r]
    push_cast
    linarith
  have hcountReal : (((b - r N).toNat : ℕ) : ℝ) ≤
      (((Finset.Icc (m + 1) N).filter fun n =>
        ∀ j, j < n → r n ≤ r j - 1).card : ℝ) := by
    exact_mod_cast hcount
  have hrealCount : (Real.sqrt N : ℝ) ≤
      (((Finset.Icc (m + 1) N).filter fun n =>
        ∀ j, j < n → r n ≤ r j - 1).card : ℝ) := by
    calc
      (Real.sqrt N : ℝ) ≤ ((b - r N : ℤ) : ℝ) := hheight
      _ = (((b - r N).toNat : ℕ) : ℝ) := by exact_mod_cast hfloor.symm
      _ ≤ _ := hcountReal
  have hsubset : Finset.Icc (m + 1) N ⊆ Finset.Icc ((N + 1) / 2) N := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    constructor
    · dsimp [m] at hn
      omega
    · exact hn.2
  have hregularRecords :
      ((Finset.Icc (m + 1) N).filter fun n =>
        ∀ j, j < n → r n ≤ r j - 1) ⊆
      (Finset.Icc ((N + 1) / 2) N).filter (fun n => p ∈ {p : ℕ → ℤ × ℤ |
        (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n}) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnrecord⟩
    apply Finset.mem_filter.mpr
    refine ⟨hsubset hnIcc, ?_⟩
    have hnNat : (N + 1) / 2 ≤ n := by
      simp only [Finset.mem_Icc] at hnIcc
      dsimp [m] at hnIcc
      omega
    have hnlow : (N : ℝ) / 2 ≤ n := by
      have hceil : N ≤ 2 * ((N + 1) / 2) := by omega
      have hceilR : (N : ℝ) ≤ 2 * (((N + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast hceil
      calc
        (N : ℝ) / 2 ≤ ((N + 1) / 2 : ℕ) := by
          nlinarith
        _ ≤ n := by exact_mod_cast hnNat
    have hnup : n ≤ N := by
      simp only [Finset.mem_Icc] at hnIcc
      exact hnIcc.2
    have hreg := hregular n hnlow hnup
    change (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧ _
    exact ⟨hnrecord, hreg⟩
  have hcard := Finset.card_le_card hregularRecords
  exact hrealCount.trans (by exact_mod_cast hcard)

/-- The regular strict-record event is measurable for the product sigma-algebra. -/
theorem measurableSet_regularRecord (n : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
      Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} := by
  classical
  have hrecords : MeasurableSet {p : ℕ → ℤ × ℤ | ∀ j, j < n → (p n).2 ≤ (p j).2 - 1} := by
    rw [show {p : ℕ → ℤ × ℤ | ∀ j, j < n → (p n).2 ≤ (p j).2 - 1} =
      ⋂ j : ℕ, {p | j < n → (p n).2 ≤ (p j).2 - 1} by ext p; simp]
    refine MeasurableSet.iInter fun j => ?_
    by_cases hj : j < n
    · have hRn : Measurable (fun p : ℕ → ℤ × ℤ => (p n).2) := by fun_prop
      have hRj : Measurable (fun p : ℕ → ℤ × ℤ => (p j).2 - 1) := by fun_prop
      simpa [hj] using measurableSet_le hRn hRj
    · simp [hj]
  have hL : Measurable (fun p : ℕ → ℤ × ℤ => ((p n).1 : ℝ)) := by fun_prop
  have hlow : MeasurableSet {p : ℕ → ℤ × ℤ | Real.sqrt n / 100 ≤ ((p n).1 : ℝ)} :=
    measurableSet_le measurable_const hL
  have hupp : MeasurableSet {p : ℕ → ℤ × ℤ | ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} :=
    measurableSet_le hL measurable_const
  rw [Set.ofPred_and, Set.ofPred_and]
  exact hrecords.inter (hlow.inter hupp)

/-- The block event is measurable for the product sigma-algebra. -/
theorem measurableSet_recordBlock (N : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by
  classical
  have hregular : MeasurableSet {p : ℕ → ℤ × ℤ |
      ∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} := by
    rw [show {p : ℕ → ℤ × ℤ | ∀ n : ℕ,
        (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} =
      ⋂ n : ℕ, {p | (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} by
      ext p; simp]
    refine MeasurableSet.iInter fun n => ?_
    by_cases hdom₁ : (N : ℝ) / 2 ≤ n
    · by_cases hdom₂ : n ≤ N
      · have hL : Measurable (fun p : ℕ → ℤ × ℤ => ((p n).1 : ℝ)) := by fun_prop
        have hlo : MeasurableSet {p : ℕ → ℤ × ℤ | Real.sqrt n / 100 ≤ ((p n).1 : ℝ)} :=
          measurableSet_le measurable_const hL
        have hup : MeasurableSet {p : ℕ → ℤ × ℤ | ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} :=
          measurableSet_le hL measurable_const
        have hboth : MeasurableSet {p : ℕ → ℤ × ℤ |
            Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} := by
          rw [Set.ofPred_and]
          exact hlo.inter hup
        simpa [hdom₁, hdom₂] using hboth
      · simp [hdom₂]
    · simp [hdom₁]
  have hearly : MeasurableSet {p : ℕ → ℤ × ℤ |
      ∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)} := by
    rw [show {p : ℕ → ℤ × ℤ | ∀ n : ℕ,
        (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)} =
      ⋂ n : ℕ, {p | (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)} by
      ext p; simp]
    refine MeasurableSet.iInter fun n => ?_
    by_cases hn : (n : ℝ) ≤ (N : ℝ) / 2
    · have hR : Measurable (fun p : ℕ → ℤ × ℤ => ((p n).2 : ℝ)) := by fun_prop
      simpa [hn] using measurableSet_le measurable_const hR
    · simp [hn]
  have hterminal : MeasurableSet {p : ℕ → ℤ × ℤ | ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by
    have hR : Measurable (fun p : ℕ → ℤ × ℤ => ((p N).2 : ℝ)) := by fun_prop
    exact measurableSet_le hR measurable_const
  rw [Set.ofPred_and, Set.ofPred_and]
  exact hregular.inter (hearly.inter hterminal)

/-- Integrating the block record count gives the expectation inequality (4.14), -/
theorem sqrt_mul_measureReal_block_le_sum (μ : Measure (ℕ → ℤ × ℤ)) [IsFiniteMeasure μ]
    (hstep : ∀ᵐ p ∂μ, ∀ i, (p i).2 - 1 ≤ (p (i + 1)).2) (N : ℕ) :
    Real.sqrt N * μ.real {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} ≤
      ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real {p : ℕ → ℤ × ℤ |
        (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} := by
  classical
  let S := Finset.Icc ((N + 1) / 2) N
  let f : (ℕ → ℤ × ℤ) → ℝ := {p : ℕ → ℤ × ℤ |
    (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
      Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
    (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
    ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}.indicator (fun _ => Real.sqrt N)
  let g : (ℕ → ℤ × ℤ) → ℝ := fun p => ∑ n ∈ S,
    ({p : ℕ → ℤ × ℤ |
    (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
    Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n}).indicator
      (fun _ => (1 : ℝ)) p
  have hEm : MeasurableSet {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by
    exact measurableSet_recordBlock N
  have hFm : ∀ n ∈ S, MeasurableSet {p : ℕ → ℤ × ℤ |
      (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
      Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} := by
    intro n hn
    exact measurableSet_regularRecord n
  have hfint : Integrable f μ := (integrable_const _).indicator hEm
  have hgint : Integrable g μ := by
    dsimp [g]
    apply integrable_finsetSum S
    intro n hn
    exact (integrable_const _).indicator (hFm n hn)
  have hpoint : f ≤ᵐ[μ] g := by
    filter_upwards [hstep] with p hp
    by_cases hEp : p ∈ {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}
    · have hcnt := sqrt_le_card_regularRecords_of_block p N (fun i _ => hp i) hEp
      have hsum : g p = (((S.filter fun n => p ∈ {p : ℕ → ℤ × ℤ |
          (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n}).card : ℕ) : ℝ) := by
        dsimp [g, S]
        simp [Set.indicator, Finset.sum_boole]
      have hcnt' : Real.sqrt N ≤ (((S.filter fun n => p ∈ {p : ℕ → ℤ × ℤ |
          (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n}).card : ℕ) : ℝ) := by
        simpa only [S] using hcnt
      change {p : ℕ → ℤ × ℤ |
          (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
            Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
          (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
          ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}.indicator (fun _ => Real.sqrt N) p ≤ g p
      rw [Set.indicator_of_mem hEp, hsum]
      exact hcnt'
    · have hnonneg : ∀ n ∈ S, 0 ≤ ({p : ℕ → ℤ × ℤ |
          (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n}).indicator
          (fun _ => (1 : ℝ)) p := by
        intro n hn
        by_cases hpF : p ∈ {p : ℕ → ℤ × ℤ |
            (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
            Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n}
        · rw [Set.indicator_of_mem hpF]
          norm_num
        · rw [Set.indicator_of_notMem hpF]
      change {p : ℕ → ℤ × ℤ |
          (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
            Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
          (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
          ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}.indicator (fun _ => Real.sqrt N) p ≤ g p
      rw [Set.indicator_of_notMem hEp]
      dsimp [g]
      exact Finset.sum_nonneg fun n hn => hnonneg n hn
  calc
    Real.sqrt N * μ.real {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} = ∫ p, f p ∂μ := by
      dsimp [f]
      rw [integral_indicator_const (Real.sqrt N) hEm]
      simp [smul_eq_mul, mul_comm]
    _ ≤ ∫ p, g p ∂μ := integral_mono_ae hfint hgint hpoint
    _ = ∑ n ∈ S, μ.real {p : ℕ → ℤ × ℤ |
        (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} := by
      rw [integral_finsetSum S (fun n hn => (integrable_const _).indicator (hFm n hn))]
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_indicator_one (hFm n hn)

/-- A single uniform lower bound for the block probabilities yields the -/
theorem block_sum_lower_bound_of_block_prob (μ : Measure (ℕ → ℤ × ℤ)) [IsFiniteMeasure μ]
    (hstep : ∀ᵐ p ∂μ, ∀ i, (p i).2 - 1 ≤ (p (i + 1)).2) (q : ℝ)
    (hE : ∀ N : ℕ, 100 ≤ N → q ≤ μ.real {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}) :
    ∀ N : ℕ, 100 ≤ N →
      q * Real.sqrt N ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real {p : ℕ → ℤ × ℤ |
        (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} := by
  intro N hN
  have h := sqrt_mul_measureReal_block_le_sum μ hstep N
  have hq := hE N hN
  calc
    q * Real.sqrt N ≤ μ.real {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} * Real.sqrt N :=
      mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg N)
    _ = Real.sqrt N * μ.real {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by ring
    _ ≤ _ := h

private theorem lazyTwoDimensionalPrefix_last_step_snd {n : ℕ}
    (x y : ℤ) (w : Fin (n + 1) → Fin 3) :
    (lazyTwoDimensionalPrefix x y w (Fin.last (n + 1))).2 =
      (lazyTwoDimensionalPrefix x y w ⟨n, by omega⟩).2 +
        (lazyTwoDimensionalStep (w (Fin.last n))).2 := by
  simp [lazyTwoDimensionalPrefix, Fin.last, Finset.sum_filter, Fin.sum_univ_castSucc]
  ring

/-- The actual source-step support gives the down-step bound for a path law -/
theorem conditionedSource_ae_secondCoordinate_downStep (x : ℕ) (y : ℤ)
    (ν : Measure (ℕ → ℤ × ℤ))
    (hRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) :
    ∀ᵐ p ∂ν, ∀ i, (p i).2 - 1 ≤ (p (i + 1)).2 := by
  filter_upwards [conditionedSource_ae_all_prefixes_mem_range x y ν hRN] with p hp i
  obtain ⟨w, hw⟩ := hp (i + 1)
  have hstart := congrFun hw ⟨i, by omega⟩
  have hend := congrFun hw (Fin.last (i + 1))
  have hinc := lazyTwoDimensionalPrefix_last_step_snd x y w
  rw [hend, hstart] at hinc
  simp only [Fin.val_last] at hinc
  have hstepval : (lazyTwoDimensionalStep (w (Fin.last i))).2 ≥ -1 := by
    unfold lazyTwoDimensionalStep
    split_ifs <;> norm_num
  linarith

end DirectedDistances.RandomWalk
