module

public import DirectedDistances.Recursive.BusemannWholeLineJumpBound
public import DirectedDistances.Probability.WholeLineGlueLaw

import all DirectedDistances.Probability.SkorokhodJ1WholeLineLocal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped Topology

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The local J1 window error is bounded by the first negative step jump. -/
theorem ldpBusemannWholeLinePath_glue_window_distance_bound
    (n m : ℕ) (ω : ℕ → Fin 3) :
    wholeLineJ1WindowDistance m (ldpBusemannWholeLinePath n ω)
      (wholeLineGlueZero
        (ldpBusemannWholeLinePositiveHalf n ω,
         ldpBusemannWholeLineNegativeHalf n ω)) ≤
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        |(busemannLDPMeasurableVersion ω (-1) : ℝ)| := by
  let C := ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
    |(busemannLDPMeasurableVersion ω (-1) : ℝ)|
  let : Nonempty (J1Window (2 * ((m : ℝ) + 1))) :=
    ⟨⟨0, ⟨le_rfl, (by positivity : 0 < 2 * ((m : ℝ) + 1)).le⟩⟩⟩
  have hsup :
      (⨆ u : J1Window (2 * ((m : ℝ) + 1)),
        |(wholeLineJ1WindowPath m (ldpBusemannWholeLinePath n ω)).1 u -
          (wholeLineJ1WindowPath m
            (wholeLineGlueZero
              (ldpBusemannWholeLinePositiveHalf n ω,
               ldpBusemannWholeLineNegativeHalf n ω))).1 u|) ≤ C := by
    apply ciSup_le
    intro u
    let t := wholeLineJ1WindowTime m u
    have hcut0 : 0 ≤ wholeLineJ1Cutoff m t := by
      unfold wholeLineJ1Cutoff
      positivity
    have hcut1 : wholeLineJ1Cutoff m t ≤ 1 := by
      unfold wholeLineJ1Cutoff
      exact max_le (by norm_num) (min_le_left _ _)
    have hpoint := ldpBusemannWholeLinePath_glue_value_bound n ω t
    change |wholeLineJ1Cutoff m t *
        (ldpBusemannWholeLinePath n ω).1 t -
      wholeLineJ1Cutoff m t *
        (wholeLineGlueZero
          (ldpBusemannWholeLinePositiveHalf n ω,
           ldpBusemannWholeLineNegativeHalf n ω)).1 t| ≤ C
    rw [← mul_sub, abs_mul]
    calc
      |wholeLineJ1Cutoff m t| *
          |(ldpBusemannWholeLinePath n ω).1 t -
            (wholeLineGlueZero
              (ldpBusemannWholeLinePositiveHalf n ω,
               ldpBusemannWholeLineNegativeHalf n ω)).1 t| ≤
        1 * C := mul_le_mul
          (by simpa only [abs_of_nonneg hcut0] using hcut1) hpoint
          (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
  change j1WindowDist (by positivity :
      0 < 2 * ((m : ℝ) + 1))
      (wholeLineJ1WindowPath m (ldpBusemannWholeLinePath n ω))
      (wholeLineJ1WindowPath m
        (wholeLineGlueZero
          (ldpBusemannWholeLinePositiveHalf n ω,
           ldpBusemannWholeLineNegativeHalf n ω))) ≤ C
  exact (j1WindowDist_le_sup_dist (by positivity) _ _).trans hsup

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The weighted whole-line local J1 distance is bounded by twice the first-step error. -/
theorem ldpBusemannWholeLinePath_glue_local_distance_bound
    (n : ℕ) (ω : ℕ → Fin 3) :
    dist (ldpBusemannWholeLinePath n ω)
      (wholeLineGlueZero
        (ldpBusemannWholeLinePositiveHalf n ω,
         ldpBusemannWholeLineNegativeHalf n ω)) ≤
      2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        |(busemannLDPMeasurableVersion ω (-1) : ℝ)|) := by
  let C := ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
    |(busemannLDPMeasurableVersion ω (-1) : ℝ)|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  change wholeLineLocalJ1Distance _ _ ≤ 2 * C
  unfold wholeLineLocalJ1Distance
  have hgeom : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
    summable_geometric_two
  have hupper : Summable (fun m : ℕ => C * (1 / 2 : ℝ) ^ m) :=
    hgeom.mul_left C
  calc
    (∑' m : ℕ, wholeLineLocalJ1Term m
        (ldpBusemannWholeLinePath n ω)
        (wholeLineGlueZero
          (ldpBusemannWholeLinePositiveHalf n ω,
           ldpBusemannWholeLineNegativeHalf n ω))) ≤
      ∑' m : ℕ, C * (1 / 2 : ℝ) ^ m := by
        apply (wholeLineLocalJ1Term_summable _ _).tsum_le_tsum
        intro m
        rw [wholeLineLocalJ1Term]
        calc
          (1 / 2 : ℝ) ^ (m + 1) *
              min 1 (wholeLineJ1WindowDistance m
                (ldpBusemannWholeLinePath n ω)
                (wholeLineGlueZero
                  (ldpBusemannWholeLinePositiveHalf n ω,
                   ldpBusemannWholeLineNegativeHalf n ω))) ≤
            (1 / 2 : ℝ) ^ (m + 1) * C :=
              mul_le_mul_of_nonneg_left
                ((min_le_right _ _).trans
                  (ldpBusemannWholeLinePath_glue_window_distance_bound n m ω))
                (by positivity)
          _ ≤ C * (1 / 2 : ℝ) ^ m := by
            calc
              (1 / 2 : ℝ) ^ (m + 1) * C =
                  C * ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m) := by
                    rw [pow_succ]
                    ring
              _ ≤ C * (1 * (1 / 2 : ℝ) ^ m) :=
                mul_le_mul_of_nonneg_left (by norm_num) hC
              _ = C * (1 / 2 : ℝ) ^ m := by ring
        exact hupper
    _ = 2 * C := by
      rw [tsum_mul_left, tsum_geometric_two]
      ring


private theorem measurableIntCastReal : Measurable (fun z : ℤ => (z : ℝ)) :=
  measurable_of_countable _

private theorem ldpBusemannJumpCoefficient_tendsto :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))
      atTop (𝓝 0) := by
  have hq : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (f₁ := fun n : ℕ => (n : ℝ))
      (f₂ := fun n : ℕ => ((n + 1 : ℕ) : ℝ))
    · filter_upwards [] with n
      exact_mod_cast Nat.le_succ n
    · exact tendsto_natCast_atTop_atTop
  have h :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (3 / 2 : ℝ))).comp hq
  have hpow : (-3 / 2 : ℝ) = -(3 / 2 : ℝ) := by ring
  rw [hpow]
  change Tendsto
    ((fun x : ℝ => x ^ (-(3 / 2 : ℝ))) ∘
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0)
  exact h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The probability of a local J1 error of fixed positive size tends to zero. -/
theorem tendsto_iidCodeMeasure_real_ldpBusemannWholeLinePath_glue_error
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n => iidCodeMeasure.real
        {ω | ε ≤ dist (ldpBusemannWholeLinePath n ω)
          (wholeLineGlueZero
            (ldpBusemannWholeLinePositiveHalf n ω,
             ldpBusemannWholeLineNegativeHalf n ω))})
      atTop (𝓝 0) := by
  let B : (ℕ → Fin 3) → ℝ :=
    fun ω => (busemannLDPMeasurableVersion ω (-1) : ℝ)
  let S : ℕ → Set (ℕ → Fin 3) := fun n =>
    {ω | ε ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω|}
  have hB : Measurable B := by
    dsimp [B]
    exact measurableIntCastReal.comp
      (measurable_busemannLDPMeasurableVersion (-1))
  have hcoeff : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))
      atTop (𝓝 0) := ldpBusemannJumpCoefficient_tendsto
  have hanti : Antitone S := by
    intro n m hnm ω hω
    change ε ≤ 2 * (((m + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω| at hω
    have hpow : ((m + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
      · exact_mod_cast Nat.add_le_add_right hnm 1
      · norm_num
    have hprod :
        2 * (((m + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω| ≤
          2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω| := by
      calc
        2 * (((m + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω| =
            2 * ((((m + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω|) := by
          ring
        _ ≤ 2 * ((((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)) (by norm_num)
        _ = 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω| := by
          ring
    exact hω.trans hprod
  have hSmeas : ∀ n, MeasurableSet (S n) := by
    intro n
    change MeasurableSet
      {ω | ε ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω|}
    exact measurableSet_le measurable_const
      ((measurable_const : Measurable
        (fun _ : ℕ → Fin 3 =>
          2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)))).mul
        (continuous_abs.measurable.comp hB))
  have hinter : (⋂ n, S n) = ∅ := by
    ext ω
    constructor
    · intro hω
      have hlim : Tendsto
          (fun n : ℕ => 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω|)
          atTop (𝓝 0) := by
        simpa only [mul_zero, zero_mul] using
          (hcoeff.const_mul (2 : ℝ)).mul_const (|B ω|)
      obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
      have hωn : ε ≤
          2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω| := by
        exact Set.mem_iInter.mp hω n
      exact (not_lt_of_ge hωn) hn
    · simp
  have hcont : Tendsto (fun n => iidCodeMeasure (S n)) atTop
      (𝓝 (iidCodeMeasure (⋂ n, S n))) :=
    tendsto_measure_iInter_atTop
      (fun n => (hSmeas n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top iidCodeMeasure (S 0)⟩
  have hcontZero : Tendsto (fun n => iidCodeMeasure (S n)) atTop
      (𝓝 0) := by
    simpa only [hinter, measure_empty] using hcont
  have hcontReal : Tendsto (fun n => iidCodeMeasure.real (S n)) atTop
      (𝓝 0) := by
    change Tendsto
      (ENNReal.toReal ∘ fun n => iidCodeMeasure (S n)) atTop (𝓝 0)
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcontZero
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [(Metric.tendsto_nhds.mp hcontReal δ hδ)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hn' : iidCodeMeasure.real (S n) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hn
  calc
    iidCodeMeasure.real
        {ω | ε ≤ dist (ldpBusemannWholeLinePath n ω)
          (wholeLineGlueZero
            (ldpBusemannWholeLinePositiveHalf n ω,
             ldpBusemannWholeLineNegativeHalf n ω))} ≤
        iidCodeMeasure.real (S n) := by
      change (iidCodeMeasure
        {ω | ε ≤ dist (ldpBusemannWholeLinePath n ω)
          (wholeLineGlueZero
            (ldpBusemannWholeLinePositiveHalf n ω,
             ldpBusemannWholeLineNegativeHalf n ω))}).toReal ≤
        (iidCodeMeasure (S n)).toReal
      refine ENNReal.toReal_mono
        (measure_ne_top iidCodeMeasure (S n)) ?_
      apply measure_mono
      intro ω hω
      change ε ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) * |B ω|
      change ε ≤ dist (ldpBusemannWholeLinePath n ω)
        (wholeLineGlueZero
          (ldpBusemannWholeLinePositiveHalf n ω,
           ldpBusemannWholeLineNegativeHalf n ω)) at hω
      have hbound :=
        ldpBusemannWholeLinePath_glue_local_distance_bound n ω
      exact hω.trans (by simpa [B, mul_assoc] using hbound)
    _ < δ := hn'

end DirectedDistances.Recursive
