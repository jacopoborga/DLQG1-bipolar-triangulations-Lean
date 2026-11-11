/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoundaryRecordsUL
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.RandomWalk.IIDCodeRelabel
import Mathlib.Tactic.FinCases
meta import Lean.Elab.Tactic.Omega

/-! # Walk-level times for the north flow line

The recursive first-hit times and their code-step identities in
This file formalizes the walk-level times and step identities. The deterministic
reachability characterization still needs a bridge from stage boundary data to
paths in the infinite present-edge graph. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open DirectedDistances.RandomWalk
open scoped Classical

/-- The two families of future one-level hits needed to define the walk-level
flow-line times (`lem-flow-line-times`, -/
@[expose] def HasFlowLineHits (w : ℕ → Fin 3) : Prop :=
  (∀ n, ∃ m, n + 1 ≤ m ∧ L w m = L w n - 1) ∧
  (∀ n, ∃ m, n + 1 ≤ m ∧ R w m = R w n - 1)

private theorem L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem R_succ (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem lazyStep_fst_lower (c : Fin 3) :
    -1 ≤ (lazyTwoDimensionalStep c).1 := by
  fin_cases c <;> simp [lazyTwoDimensionalStep]

private theorem lazyStep_snd_lower (c : Fin 3) :
    -1 ≤ (lazyTwoDimensionalStep c).2 := by
  fin_cases c <;> simp [lazyTwoDimensionalStep]

private theorem lazyStep_fst_eq_neg_one_iff (c : Fin 3) :
    (lazyTwoDimensionalStep c).1 = -1 ↔ c = 0 := by
  fin_cases c <;> simp [lazyTwoDimensionalStep]

private theorem lazyStep_snd_eq_neg_one_iff (c : Fin 3) :
    (lazyTwoDimensionalStep c).2 = -1 ↔ c = 2 := by
  fin_cases c <;> simp [lazyTwoDimensionalStep]

private theorem L_succ_lower (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) := by
  rw [L_succ]
  have h := lazyStep_fst_lower (w n)
  omega

private theorem R_succ_lower (w : ℕ → Fin 3) (n : ℕ) :
    R w n - 1 ≤ R w (n + 1) := by
  rw [R_succ]
  have h := lazyStep_snd_lower (w n)
  omega

private theorem L_lower_bound (w : ℕ → Fin 3) (n : ℕ) :
    -(n : ℤ) ≤ L w n := by
  induction n with
  | zero => simp [L]
  | succ n ih =>
      have h := L_succ_lower w n
      change -(↑(n + 1) : ℤ) ≤ L w (n + 1)
      omega

private theorem R_lower_bound (w : ℕ → Fin 3) (n : ℕ) :
    -(n : ℤ) ≤ R w n := by
  induction n with
  | zero => simp [R]
  | succ n ih =>
      have h := R_succ_lower w n
      change -(↑(n + 1) : ℤ) ≤ R w (n + 1)
      omega

private theorem future_L_hit_of_unbounded (w : ℕ → Fin 3)
    (hu : ∀ a : ℤ, ∃ n, L w n ≤ a) (t : ℕ) :
    ∃ n, t + 1 ≤ n ∧ L w n = L w t - 1 := by
  classical
  let target := L w t - 1
  obtain ⟨m, hm⟩ := hu (-(t : ℤ) - 1)
  have hmt : t < m := by
    by_contra h
    have hle : m ≤ t := by omega
    have hb := L_lower_bound w m
    omega
  have hex : ∃ n, t + 1 ≤ n ∧ L w n ≤ target := by
    refine ⟨m, ?_, ?_⟩
    · omega
    · have ht := L_lower_bound w t
      dsimp [target]
      omega
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  have hprev : t ≤ n - 1 := by omega
  have hprevLt : n - 1 < n := by omega
  have hprevVal : target < L w (n - 1) := by
    by_cases hEq : n - 1 = t
    · rw [hEq]
      dsimp [target]
      omega
    · have hnot := Nat.find_min hex (by omega : n - 1 < n)
      have hprevGt : t + 1 ≤ n - 1 := by omega
      have hcoordGt : target < L w (n - 1) := by
        by_contra hle
        exact hnot ⟨hprevGt, by omega⟩
      have hstep := L_succ_lower w (n - 1)
      have hsplit : n - 1 + 1 = n := by omega
      rw [hsplit] at hstep
      dsimp [target] at *
      omega
  have hstep := L_succ_lower w (n - 1)
  have hsplit : n - 1 + 1 = n := by omega
  rw [hsplit] at hstep
  have hnVal : L w n ≤ target := by simpa only [n] using hn.2
  dsimp [target] at *
  change L w n ≤ L w t - 1 at hnVal
  have hnVal : L w n ≤ L w t - 1 := hnVal
  refine ⟨n, hn.1, ?_⟩
  omega

private theorem future_R_hit_of_unbounded (w : ℕ → Fin 3)
    (hu : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ) :
    ∃ n, t + 1 ≤ n ∧ R w n = R w t - 1 := by
  classical
  let target := R w t - 1
  obtain ⟨m, hm⟩ := hu (-(t : ℤ) - 1)
  have hmt : t < m := by
    by_contra h
    have hle : m ≤ t := by omega
    have hb := R_lower_bound w m
    omega
  have hex : ∃ n, t + 1 ≤ n ∧ R w n ≤ target := by
    refine ⟨m, ?_, ?_⟩
    · omega
    · have ht := R_lower_bound w t
      dsimp [target]
      omega
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  have hprev : t ≤ n - 1 := by omega
  have hprevVal : target < R w (n - 1) := by
    by_cases hEq : n - 1 = t
    · rw [hEq]
      dsimp [target]
      omega
    · have hnot := Nat.find_min hex (by omega : n - 1 < n)
      have hprevGt : t + 1 ≤ n - 1 := by omega
      have hcoordGt : target < R w (n - 1) := by
        by_contra hle
        exact hnot ⟨hprevGt, by omega⟩
      have hstep := R_succ_lower w (n - 1)
      have hsplit : n - 1 + 1 = n := by omega
      rw [hsplit] at hstep
      dsimp [target] at *
      omega
  have hstep := R_succ_lower w (n - 1)
  have hsplit : n - 1 + 1 = n := by omega
  rw [hsplit] at hstep
  have hnVal : R w n ≤ target := by simpa only [n] using hn.2
  dsimp [target] at *
  change R w n ≤ R w t - 1 at hnVal
  have hnVal : R w n ≤ R w t - 1 := hnVal
  refine ⟨n, hn.1, ?_⟩
  omega

/-- In the iid code model, the two future-hit conditions hold almost surely.
The code sequence used by the stages is `ω (i + 1)`, matching the source
walk's dummy time-zero convention (`lem-flow-line-times`, -/
theorem ae_hasFlowLineHits :
    ∀ᵐ ω ∂iidCodeMeasure, HasFlowLineHits (fun i => ω (i + 1)) := by
  filter_upwards [ae_codeWalk_fst_unbounded_below,
    ae_codeWalk_snd_unbounded_below] with ω hL hR
  constructor
  · intro n
    have hcoord : ∀ a : ℤ, ∃ m, L (fun i => ω (i + 1)) m ≤ a := by
      intro a
      obtain ⟨m, hm⟩ := hL a
      refine ⟨m, ?_⟩
      have hEq : L (fun i => ω (i + 1)) m = (codeWalk ω m).1 := by
        simp only [L, codeWalk, Prod.fst_sum]
      rw [hEq]
      exact hm
    exact future_L_hit_of_unbounded _ hcoord n
  · intro n
    have hcoord : ∀ a : ℤ, ∃ m, R (fun i => ω (i + 1)) m ≤ a := by
      intro a
      obtain ⟨m, hm⟩ := hR a
      refine ⟨m, ?_⟩
      have hEq : R (fun i => ω (i + 1)) m = (codeWalk ω m).2 := by
        simp only [R, codeWalk, Prod.snd_sum]
      rw [hEq]
      exact hm
    exact future_R_hit_of_unbounded _ hcoord n

/-- The least horizontal hit strictly after a specified time -/
@[expose] noncomputable def firstFlowLHit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t : ℕ) : ℕ :=
  by
    classical
    change (∀ n, ∃ m, n + 1 ≤ m ∧ L w m = L w n - 1) ∧ _ at h
    exact Nat.find (h.1 t)

/-- The least vertical hit strictly after a specified time -/
@[expose] noncomputable def firstFlowRHit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t : ℕ) : ℕ :=
  by
    classical
    change _ ∧ (∀ n, ∃ m, n + 1 ≤ m ∧ R w m = R w n - 1) at h
    exact Nat.find (h.2 t)

theorem firstFlowLHit_spec (w : ℕ → Fin 3) (h : HasFlowLineHits w) (t : ℕ) :
    t + 1 ≤ firstFlowLHit w h t ∧
      L w (firstFlowLHit w h t) = L w t - 1 :=
  by
    change (∀ n, ∃ m, n + 1 ≤ m ∧ L w m = L w n - 1) ∧ _ at h
    change t + 1 ≤ Nat.find (h.1 t) ∧
      L w (Nat.find (h.1 t)) = L w t - 1
    exact Nat.find_spec (h.1 t)

theorem firstFlowRHit_spec (w : ℕ → Fin 3) (h : HasFlowLineHits w) (t : ℕ) :
    t + 1 ≤ firstFlowRHit w h t ∧
      R w (firstFlowRHit w h t) = R w t - 1 :=
  by
    change _ ∧ (∀ n, ∃ m, n + 1 ≤ m ∧ R w m = R w n - 1) at h
    change t + 1 ≤ Nat.find (h.2 t) ∧
      R w (Nat.find (h.2 t)) = R w t - 1
    exact Nat.find_spec (h.2 t)

/-- Paired walk-level flow-line times. At index `k`, the first component is
`N_{k+1}^R` and the second is `N_{k+1}^L` from the source indexing -/
@[expose] noncomputable def flowLineTimes (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ × ℕ
  | 0 => (0, firstFlowLHit w h 0)
  | k + 1 =>
      let r := firstFlowRHit w h (flowLineTimes w h k).2
      (r, firstFlowLHit w h r)

/-- Horizontal-side entrance times, zero-indexed as `N_{k+1}^R`. -/
@[expose] noncomputable def walkNR (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : ℕ := (flowLineTimes w h k).1

/-- Horizontal-side exit times, zero-indexed as `N_{k+1}^L`. -/
@[expose] noncomputable def walkNL (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : ℕ := (flowLineTimes w h k).2

theorem walkNR_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    walkNR w h 0 = 0 := rfl

theorem walkNL_spec (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    walkNR w h k + 1 ≤ walkNL w h k ∧
      L w (walkNL w h k) = L w (walkNR w h k) - 1 := by
  cases k with
  | zero => exact firstFlowLHit_spec w h 0
  | succ k =>
      change firstFlowRHit w h (walkNL w h k) + 1 ≤
          firstFlowLHit w h (firstFlowRHit w h (walkNL w h k)) ∧ _
      exact firstFlowLHit_spec w h _

theorem walkNR_succ_spec (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    walkNL w h k + 1 ≤ walkNR w h (k + 1) ∧
      R w (walkNR w h (k + 1)) = R w (walkNL w h k) - 1 := by
  exact firstFlowRHit_spec w h (walkNL w h k)

private theorem firstFlowLHit_previous_level (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t : ℕ) :
    L w (firstFlowLHit w h t - 1) = L w t := by
  classical
  change (∀ m, ∃ n, m + 1 ≤ n ∧ L w n = L w m - 1) ∧ _ at h
  let target := L w t - 1
  have hn := firstFlowLHit_spec w h t
  have hmin : ∀ j, t + 1 ≤ j → j < firstFlowLHit w h t →
      L w j ≠ target := by
    intro j hj hjn heq
    have hfind : j < Nat.find (h.1 t) := by
      exact hjn
    have hnot := Nat.find_min (h.1 t) hfind
    exact hnot ⟨hj, by simpa [target] using heq⟩
  have hstart : L w t = target + 1 := by dsimp [target]; omega
  have hbefore : ∀ j, t ≤ j → j < firstFlowLHit w h t → target < L w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro _
        rw [hstart]
        omega
    | succ j hj ih =>
        intro hjn
        have hprev := ih (by omega)
        have hneq := hmin (j + 1) (by omega) hjn
        have hstep := L_succ_lower w j
        omega
  have hindex : t ≤ firstFlowLHit w h t - 1 ∧
      firstFlowLHit w h t - 1 < firstFlowLHit w h t := by omega
  have hprevgt := hbefore (firstFlowLHit w h t - 1) hindex.1 hindex.2
  have hstep := L_succ_lower w (firstFlowLHit w h t - 1)
  have hsucc : firstFlowLHit w h t - 1 + 1 = firstFlowLHit w h t := by omega
  rw [hsucc] at hstep
  have hhit := hn.2
  change L w (firstFlowLHit w h t) = L w t - 1 at hhit
  dsimp [target] at hprevgt hhit
  have hprev : L w (firstFlowLHit w h t - 1) = L w t := by omega
  exact hprev

private theorem firstFlowRHit_previous_level (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t : ℕ) :
    R w (firstFlowRHit w h t - 1) = R w t := by
  classical
  change _ ∧ (∀ m, ∃ n, m + 1 ≤ n ∧ R w n = R w m - 1) at h
  let target := R w t - 1
  have hn := firstFlowRHit_spec w h t
  have hmin : ∀ j, t + 1 ≤ j → j < firstFlowRHit w h t →
      R w j ≠ target := by
    intro j hj hjn heq
    have hfind : j < Nat.find (h.2 t) := by
      exact hjn
    have hnot := Nat.find_min (h.2 t) hfind
    exact hnot ⟨hj, by simpa [target] using heq⟩
  have hstart : R w t = target + 1 := by dsimp [target]; omega
  have hbefore : ∀ j, t ≤ j → j < firstFlowRHit w h t → target < R w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro _
        rw [hstart]
        omega
    | succ j hj ih =>
        intro hjn
        have hprev := ih (by omega)
        have hneq := hmin (j + 1) (by omega) hjn
        have hstep := R_succ_lower w j
        omega
  have hindex : t ≤ firstFlowRHit w h t - 1 ∧
      firstFlowRHit w h t - 1 < firstFlowRHit w h t := by omega
  have hprevgt := hbefore (firstFlowRHit w h t - 1) hindex.1 hindex.2
  have hstep := R_succ_lower w (firstFlowRHit w h t - 1)
  have hsucc : firstFlowRHit w h t - 1 + 1 = firstFlowRHit w h t := by omega
  rw [hsucc] at hstep
  have hhit := hn.2
  change R w (firstFlowRHit w h t) = R w t - 1 at hhit
  dsimp [target] at hprevgt hhit
  have hprev : R w (firstFlowRHit w h t - 1) = R w t := by omega
  exact hprev

/-- At each walk-level left exit, the preceding code is `(-1,0)`, expressed -/
theorem walkNL_previous_code (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    w (walkNL w h k - 1) = 0 := by
  have hlevel : L w (walkNL w h k - 1) = L w (walkNR w h k) := by
    cases k with
    | zero => simpa [walkNL, walkNR, flowLineTimes] using
        firstFlowLHit_previous_level w h 0
    | succ k => simpa [walkNL, walkNR, flowLineTimes] using
        firstFlowLHit_previous_level w h (firstFlowRHit w h (walkNL w h k))
  have hspec := walkNL_spec w h k
  have hstep := L_succ w (walkNL w h k - 1)
  have hindex : walkNL w h k - 1 + 1 = walkNL w h k := by omega
  rw [hindex] at hstep
  have hdelta : (lazyTwoDimensionalStep (w (walkNL w h k - 1))).1 = -1 := by
    have hspec' : L w (walkNL w h k) = L w (walkNR w h k) - 1 := hspec.2
    omega
  exact (lazyStep_fst_eq_neg_one_iff _).1 hdelta

/-- At each subsequent walk-level right entrance, the preceding code is
`(1,-1)`, expressed as code `2` (`eq:ref-for-lat-disc2`, -/
theorem walkNR_succ_previous_code (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    w (walkNR w h (k + 1) - 1) = 2 := by
  have hlevel : R w (walkNR w h (k + 1) - 1) = R w (walkNL w h k) := by
    simpa [walkNR, walkNL, flowLineTimes] using
      firstFlowRHit_previous_level w h (walkNL w h k)
  have hspec := walkNR_succ_spec w h k
  have hstep := R_succ w (walkNR w h (k + 1) - 1)
  have hindex : walkNR w h (k + 1) - 1 + 1 = walkNR w h (k + 1) := by omega
  rw [hindex] at hstep
  have hdelta : (lazyTwoDimensionalStep (w (walkNR w h (k + 1) - 1))).2 = -1 := by
    have hspec' : R w (walkNR w h (k + 1)) = R w (walkNL w h k) - 1 := hspec.2
    omega
  exact (lazyStep_snd_eq_neg_one_iff _).1 hdelta

/-- The literal two-coordinate code step at a walk-level left exit -/
theorem walkNL_previous_step (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    (L w (walkNL w h k) - L w (walkNL w h k - 1),
      R w (walkNL w h k) - R w (walkNL w h k - 1)) = (-1, 0) := by
  have hc := walkNL_previous_code w h k
  have hindex : walkNL w h k - 1 + 1 = walkNL w h k := by
    have := walkNL_spec w h k
    omega
  have hL := L_succ w (walkNL w h k - 1)
  have hR := R_succ w (walkNL w h k - 1)
  rw [hindex] at hL hR
  have hL' : L w (walkNL w h k) =
      L w (walkNL w h k - 1) - 1 := by
    simp [hc, lazyTwoDimensionalStep] at hL
    omega
  have hR' : R w (walkNL w h k) = R w (walkNL w h k - 1) := by
    simpa [hc, lazyTwoDimensionalStep] using hR
  apply Prod.ext <;> simp [hL', hR']

/-- The literal two-coordinate code step at a subsequent walk-level right -/
theorem walkNR_succ_previous_step (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    (L w (walkNR w h (k + 1)) - L w (walkNR w h (k + 1) - 1),
      R w (walkNR w h (k + 1)) - R w (walkNR w h (k + 1) - 1)) = (1, -1) := by
  have hc := walkNR_succ_previous_code w h k
  have hindex : walkNR w h (k + 1) - 1 + 1 = walkNR w h (k + 1) := by
    have := walkNR_succ_spec w h k
    omega
  have hL := L_succ w (walkNR w h (k + 1) - 1)
  have hR := R_succ w (walkNR w h (k + 1) - 1)
  rw [hindex] at hL hR
  have hL' : L w (walkNR w h (k + 1)) =
      L w (walkNR w h (k + 1) - 1) + 1 := by
    simpa [hc, lazyTwoDimensionalStep] using hL
  have hR' : R w (walkNR w h (k + 1)) =
      R w (walkNR w h (k + 1) - 1) - 1 := by
    simp [hc, lazyTwoDimensionalStep] at hR
    omega
  apply Prod.ext <;> simp [hL', hR']

