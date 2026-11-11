/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.BusemannWindowLimitSDP
public import DirectedDistances.Probability.SkorokhodJ1WindowPolish
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Negative excursions in SDP window limits

Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The source uses the SDP stable-process limit and its zero probability of staying
positive on a positive-length interval to obtain the negative-crossing estimate -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.Probability
open scoped Topology ENNReal

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
If every weak limit of the SDP windows has a negative value somewhere in (0,1)
with probability one, then its negative-neighborhood probabilities tend to one
as the threshold decreases. The remaining input is the zero-excursion property
of each window limit, not the threshold conclusion itself. -/
theorem sdp_window_negative_threshold_of_zero_excursion
    (hzero : ∀ ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)),
      Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num)) atTop (𝓝 ν) →
      (ν : Measure (J1WindowD 1 (by norm_num)))
        {x : J1WindowD 1 (by norm_num) |
          ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ x.path.1 t < 0} = 1) :
    ∀ ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)),
      Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num)) atTop (𝓝 ν) →
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 < A ∧
        1 - ε ≤ (ν : Measure (J1WindowD 1 (by norm_num))).real
          {x : J1WindowD 1 (by norm_num) |
            ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
              x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))} := by
  classical
  intro ν hν ε hε
  let U : ℝ → Set (J1WindowD 1 (by norm_num)) := fun A =>
    if hA : 1 < A then
      {x | ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
        x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))}
    else ∅
  let V : Set (J1WindowD 1 (by norm_num)) :=
    {x | ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      x.path.1 t < 0}
  have hmono : Monotone U := by
    intro a b hab
    by_cases ha : 1 < a
    · have hb : 1 < b := lt_of_lt_of_le ha hab
      simp only [U, dite_eq_left ha, dite_eq_left hb]
      rintro x ⟨t, ht0, ht1, hxt⟩
      refine ⟨t, ht0, ht1, ?_⟩
      have hp : b ^ (-(1 / 2 : ℝ)) ≤ a ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hab (by norm_num)
      exact hxt.trans_le (neg_le_neg hp)
    · simp [U, ha]
  have hUnion : (⋃ A : ℝ, U A) = V := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨A, hxA⟩
      by_cases hA : 1 < A
      · simp only [U, dite_eq_left hA] at hxA
        rcases hxA with ⟨t, ht0, ht1, hxt⟩
        refine ⟨t, ht0, ht1, ?_⟩
        have hp : 0 < A ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_pos_of_pos (by linarith) _
        linarith
      · simp [U, hA] at hxA
    · rintro ⟨t, ht0, ht1, hxt⟩
      let d : ℝ := -x.path.1 t
      have hd : 0 < d := by dsimp [d]; linarith
      have hlim : Tendsto (fun A : ℝ => A ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by norm_num)
      have hevent : ∀ᶠ A : ℝ in atTop, A ^ (-(1 / 2 : ℝ)) < d :=
        hlim.eventually (gt_mem_nhds hd)
      obtain ⟨B, hB⟩ := eventually_atTop.1 hevent
      let A : ℝ := max B 2
      have hA : 1 < A := by
        dsimp [A]
        exact lt_of_lt_of_le (by norm_num) (le_max_right B 2)
      have hBA : B ≤ A := by dsimp [A]; exact le_max_left B 2
      have hsmall : A ^ (-(1 / 2 : ℝ)) < d := hB A hBA
      apply Set.mem_iUnion.mpr
      refine ⟨A, ?_⟩
      simp only [U, dite_eq_left hA]
      refine ⟨t, ht0, ht1, ?_⟩
      dsimp [d] at hsmall ⊢
      linarith
  have hfull : (ν : Measure (J1WindowD 1 (by norm_num))) V = 1 := hzero ν hν
  have hsup : (⨆ A : ℝ, (ν : Measure (J1WindowD 1 (by norm_num))) (U A)) = 1 := by
    calc
      _ = (ν : Measure (J1WindowD 1 (by norm_num))) (⋃ A : ℝ, U A) :=
        hmono.measure_iUnion.symm
      _ = 1 := by rw [hUnion]; exact hfull
  by_cases hε : 1 ≤ ε
  · refine ⟨2, by norm_num, ?_⟩
    have hnonneg : 0 ≤ (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
          x.path.1 t < -(2 ^ (-(1 / 2 : ℝ)))} := measureReal_nonneg
    linarith
  · have hεlt : ε < 1 := lt_of_not_ge hε
    let c : ℝ := 1 - ε
    have hc : 0 < c := by dsimp [c]; linarith
    have hc1 : c < 1 := by dsimp [c]; linarith
    have hlt : ENNReal.ofReal c < ⨆ A : ℝ,
        (ν : Measure (J1WindowD 1 (by norm_num))) (U A) := by
      rw [hsup]
      exact (ENNReal.ofReal_lt_one).2 hc1
    obtain ⟨A, hAmeasure⟩ := lt_iSup_iff.mp hlt
    have hA : 1 < A := by
      by_contra hnot
      have hzeroSet : U A = ∅ := by simp [U, not_lt.mp hnot]
      rw [hzeroSet, measure_empty] at hAmeasure
      exact (not_lt_of_ge (bot_le : (0 : ENNReal) ≤ ENNReal.ofReal c)) hAmeasure
    have hbound : ENNReal.ofReal c <
        (ν : Measure (J1WindowD 1 (by norm_num)))
          {x : J1WindowD 1 (by norm_num) |
            ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
              x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))} := by
      simpa [U, hA] using hAmeasure
    have hfinite := measure_ne_top (ν : Measure (J1WindowD 1 (by norm_num)))
      {x : J1WindowD 1 (by norm_num) |
        ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
          x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))}
    have hreal : c < (ν : Measure (J1WindowD 1 (by norm_num))).real
        {x : J1WindowD 1 (by norm_num) |
          ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
            x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))} :=
      (ENNReal.ofReal_lt_iff_lt_toReal hc.le hfinite).mp hbound
    refine ⟨A, hA, ?_⟩
    dsimp [c] at hreal
    exact le_of_lt hreal

end DirectedDistances.Recursive
