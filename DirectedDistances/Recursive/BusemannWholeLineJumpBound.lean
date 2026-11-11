module

public import DirectedDistances.Recursive.BusemannWholeLineJump

import DirectedDistances.Probability.SkorokhodFloorStep
import DirectedDistances.Probability.SkorokhodJ1WholeLineLocal

public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped Topology

private theorem subtype_coe_tendsto_left_bound {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t : Set.Ici (0 : ℝ) => (t : ℝ))
      (nhdsWithin ⟨s, hs.le⟩ (Set.Iio ⟨s, hs.le⟩))
      (nhdsWithin s (Set.Iio s)) := by
  apply ContinuousWithinAt.tendsto_nhdsWithin
  · exact continuous_subtype_val.continuousWithinAt
  · intro t ht
    exact Set.mem_Iio.mpr (Subtype.coe_lt_coe.mpr ht)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The negative half's left limit is its ceiling-minus-one sample. -/
private theorem ldpBusemannNegativeHalf_leftLim_apply (n : ℕ) (ω : ℕ → Fin 3)
    {s : ℝ} (hs : 0 < s) :
    (ldpBusemannWholeLineNegativeHalf n ω).val.1.leftLim ⟨s, hs.le⟩ =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (ldpBusemannNegativeSamples ω
          (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ) := by
  have hne : NeBot (𝓝[<] (⟨s, hs.le⟩ : Set.Ici (0 : ℝ))) :=
    nhdsLT_neBot_of_exists_lt ⟨⟨0, le_rfl⟩, hs⟩
  have h := floorStep_left_limit
    (fun j : ℤ => (ldpBusemannNegativeSamples ω j.toNat : ℝ))
    (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity) s
  have hc := h.comp (subtype_coe_tendsto_left_bound hs)
  have hc' : Tendsto
      (fun t : Set.Ici (0 : ℝ) =>
        ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
          (ldpBusemannNegativeSamples ω
            ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ))
      (nhdsWithin ⟨s, hs.le⟩ (Set.Iio ⟨s, hs.le⟩))
      (𝓝 (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (ldpBusemannNegativeSamples ω
          (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ))) := by
    convert hc using 1
    · funext t
      congr 2
  change (ldpBusemannWholeLineNegativeHalfPath n ω).1.leftLim ⟨s, hs.le⟩ = _
  exact leftLim_eq_of_tendsto
    (f := fun t : Set.Ici (0 : ℝ) =>
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (ldpBusemannNegativeSamples ω
      ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ))
    (a := ⟨s, hs.le⟩)
    (y := ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (ldpBusemannNegativeSamples ω
        (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ))
    (h := hne) hc'

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The whole-line path and zero glue agree off the first negative mesh interval. -/
theorem glue_matches_outside_first_negative_step (n : ℕ) (ω : ℕ → Fin 3)
    {t : ℝ}
    (ht : t < -1 / ((n + 1 : ℕ) : ℝ) ∨ 0 ≤ t) :
    (wholeLineGlueZero
      (ldpBusemannWholeLinePositiveHalf n ω,
       ldpBusemannWholeLineNegativeHalf n ω)).1 t =
      (ldpBusemannWholeLinePath n ω).1 t := by
  rcases ht with ht | ht
  · have hb : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hrecip : 0 < 1 / ((n + 1 : ℕ) : ℝ) := one_div_pos.mpr hb
    have ht' : t < -(1 / ((n + 1 : ℕ) : ℝ)) := by
      simpa only [neg_div] using ht
    have hstep : 1 / ((n + 1 : ℕ) : ℝ) < -t := by
      have h := neg_lt_neg ht'
      simpa using h
    have hs : 0 < -t := lt_trans hrecip hstep
    have hbs : 1 < ((n + 1 : ℕ) : ℝ) * -t := by
      have hmul := (div_lt_iff₀ hb).mp hstep
      nlinarith only [hmul]
    change wholeLineGlue
      (ldpBusemannWholeLinePositiveHalf n ω).val
      (ldpBusemannWholeLineNegativeHalf n ω).val
      (ldpBusemannWholeLinePositiveHalf n ω).property
      (ldpBusemannWholeLineNegativeHalf n ω).property t = _
    have ht0 : t < 0 := lt_trans ht' (neg_lt_zero.mpr hrecip)
    rw [wholeLineGlue_negative _ _ _ _ ht0]
    rw [ldpBusemannNegativeHalf_leftLim_apply n ω hs]
    rw [ldpBusemannWholeLinePath_apply]
    have hceil : (1 : ℤ) < ⌈((n + 1 : ℕ) : ℝ) * -t⌉ := by
      exact Int.lt_ceil.mpr (by exact_mod_cast hbs)
    have hidx : 0 ≤ ⌈((n + 1 : ℕ) : ℝ) * -t⌉ - 1 := by omega
    have hidxcast :
        (((⌈((n + 1 : ℕ) : ℝ) * -t⌉ - 1).toNat : ℕ) : ℤ) =
          ⌈((n + 1 : ℕ) : ℝ) * -t⌉ - 1 := Int.toNat_of_nonneg hidx
    have hsample : ldpBusemannNegativeSamples ω
        (⌈((n + 1 : ℕ) : ℝ) * -t⌉ - 1).toNat =
          busemannLDPMeasurableVersion ω
            (-⌈((n + 1 : ℕ) : ℝ) * -t⌉) := by
      unfold ldpBusemannNegativeSamples
      rw [ite_eq_right (by
        intro h
        have hcast := congrArg (fun z : ℕ => (z : ℤ)) h
        rw [hidxcast] at hcast
        omega)]
      rw [hidxcast]
      congr 1
      omega
    have hfloor :
        ⌊((n + 1 : ℕ) : ℝ) * t⌋ =
          -⌈((n + 1 : ℕ) : ℝ) * -t⌉ := by
      rw [show ((n + 1 : ℕ) : ℝ) * t =
        -(((n + 1 : ℕ) : ℝ) * -t) by ring, Int.floor_neg]
    rw [hsample, hfloor]
  · change wholeLineGlue
      (ldpBusemannWholeLinePositiveHalf n ω).val
      (ldpBusemannWholeLineNegativeHalf n ω).val
      (ldpBusemannWholeLinePositiveHalf n ω).property
      (ldpBusemannWholeLineNegativeHalf n ω).property t = _
    rw [wholeLineGlue_nonnegative _ _ _ _ ⟨t, ht⟩]
    rw [ldpBusemannWholeLinePath_nonnegative n ω ⟨t, ht⟩]
    rfl

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The path and its zero glue differ only on the first negative mesh interval. -/
theorem ldpBusemannWholeLinePath_glue_value_bound (n : ℕ) (ω : ℕ → Fin 3)
    (t : ℝ) :
    |(ldpBusemannWholeLinePath n ω).1 t -
        (wholeLineGlueZero
          (ldpBusemannWholeLinePositiveHalf n ω,
           ldpBusemannWholeLineNegativeHalf n ω)).1 t| ≤
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        |(busemannLDPMeasurableVersion ω (-1) : ℝ)| := by
  by_cases hleft : t < -1 / ((n + 1 : ℕ) : ℝ)
  · rw [glue_matches_outside_first_negative_step n ω (Or.inl hleft)]
    simp
    positivity
  · by_cases hright : 0 ≤ t
    · rw [glue_matches_outside_first_negative_step n ω (Or.inr hright)]
      simp
      positivity
    · have hb : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hlo : -1 / ((n + 1 : ℕ) : ℝ) ≤ t := le_of_not_gt hleft
      have hhi : t < 0 := lt_of_not_ge hright
      have hs : 0 < -t := neg_pos.mpr hhi
      have hsle : -t ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
        have hlo' : -(1 / ((n + 1 : ℕ) : ℝ)) ≤ t := by
          simpa only [neg_div] using hlo
        linarith
      have hmul : 0 < ((n + 1 : ℕ) : ℝ) * -t ∧
          ((n + 1 : ℕ) : ℝ) * -t ≤ 1 := by
        constructor
        · exact mul_pos hb hs
        · calc
            ((n + 1 : ℕ) : ℝ) * -t ≤
                ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hsle hb.le
            _ = 1 := by field_simp
      have hceil : ⌈((n + 1 : ℕ) : ℝ) * -t⌉ = 1 :=
        Int.ceil_eq_iff.mpr (by constructor <;> norm_num at * <;> linarith)
      have hfloor : ⌊((n + 1 : ℕ) : ℝ) * t⌋ = -1 :=
        Int.floor_eq_iff.mpr ?_
      · have hglue :
            (wholeLineGlueZero
              (ldpBusemannWholeLinePositiveHalf n ω,
               ldpBusemannWholeLineNegativeHalf n ω)).1 t = 0 := by
          change wholeLineGlue
            (ldpBusemannWholeLinePositiveHalf n ω).val
            (ldpBusemannWholeLineNegativeHalf n ω).val
            (ldpBusemannWholeLinePositiveHalf n ω).property
            (ldpBusemannWholeLineNegativeHalf n ω).property t = 0
          rw [wholeLineGlue_negative _ _ _ _ hhi]
          rw [ldpBusemannNegativeHalf_leftLim_apply n ω hs, hceil]
          simp [ldpBusemannNegativeSamples]
        rw [ldpBusemannWholeLinePath_apply, hfloor, hglue]
        simp only [sub_zero]
        rw [abs_mul, abs_of_nonneg (by positivity :
          0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))]
      · constructor
        · have hmul' := mul_le_mul_of_nonneg_left hlo hb.le
          have hprod :
              ((n + 1 : ℕ) : ℝ) * (-1 / ((n + 1 : ℕ) : ℝ)) = -1 := by
            field_simp
          rw [hprod] at hmul'
          exact_mod_cast hmul'
        · simpa using mul_neg_of_pos_of_neg hb hhi

end DirectedDistances.Recursive
