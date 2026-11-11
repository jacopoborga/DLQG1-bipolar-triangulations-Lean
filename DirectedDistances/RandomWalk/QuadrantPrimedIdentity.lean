/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantWalkLaw

/-! # Primed interval walk and the R-Pitman path

L-phase stream after its initial step is removed -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW

private theorem globalLazyRunningMinimum_succ_local (p : ℕ → ℤ) (n : ℕ) :
    globalLazyRunningMinimum p (n + 1) =
      min (globalLazyRunningMinimum p n) (p (n + 1)) := by
  have h := runningMinimum_succ (fun j : Fin (n + 1 + 1) => p j.val)
    (⟨n, by omega⟩ : Fin (n + 1))
  simpa only [runningMinimum_prefix_eq_global, Fin.val_succ, Fin.val_castSucc] using h

private theorem runningMin_eq_globalLazyRunningMinimum (p : ℕ → ℤ) (n : ℕ) :
    runningMin p n = globalLazyRunningMinimum p n := by
  induction n with
  | zero => simp [runningMin]
  | succ n ih =>
      rw [runningMin, globalLazyRunningMinimum_succ_local, ih]

private theorem lExcursionShift_step_eq_rPitman (x : ℕ → Fin 3) (n : ℕ) :
    lazyTwoDimensionalStep (lExcursionShift x (n + 1)) =
      stepRotateInv (vectorPitman
        (fun k => stepRotate (codeWalk (lExcursionDummyPrefix x) k)) (n + 1)) -
        stepRotateInv (vectorPitman
          (fun k => stepRotate (codeWalk (lExcursionDummyPrefix x) k)) n) := by
  have hqstep :
      codeWalk (lExcursionDummyPrefix x) (n + 1) =
        codeWalk (lExcursionDummyPrefix x) n + lazyTwoDimensionalStep (x n) := by
    have hs := codeWalk_succ_sub (lExcursionDummyPrefix x) n
    have hcode : lExcursionDummyPrefix x (n + 1) = x n := by
      simp [lExcursionDummyPrefix]
    rw [hcode] at hs
    exact (sub_eq_iff_eq_add.mp hs).trans (add_comm _ _)
  have hmin (j : ℕ) :
      globalLazyRunningMinimum
        (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) j =
        runningMin (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) j :=
    (runningMin_eq_globalLazyRunningMinimum
      (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) j).symm
  rw [rPitman_pathwise, rPitman_pathwise]
  change lazyTwoDimensionalStep (lExcursionShift x (n + 1)) =
      ((codeWalk (lExcursionDummyPrefix x) (n + 1)).1 +
          globalLazyRunningMinimum
            (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) (n + 1),
        (codeWalk (lExcursionDummyPrefix x) (n + 1)).2 -
          2 * globalLazyRunningMinimum
            (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) (n + 1)) -
      ((codeWalk (lExcursionDummyPrefix x) n).1 +
          globalLazyRunningMinimum
            (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n,
        (codeWalk (lExcursionDummyPrefix x) n).2 -
          2 * globalLazyRunningMinimum
            (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n)
  by_cases hrecord :
      (codeWalk (lExcursionDummyPrefix x) (n + 1)).2 <
        runningMin (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n
  · have hdrop : (lazyTwoDimensionalStep (x n)).2 < 0 := by
      have hlt := lt_of_lt_of_le hrecord
        (runningMin_le
          (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n n le_rfl)
      have hs := congrArg Prod.snd hqstep
      simp only [Prod.snd_add] at hs
      rw [hs] at hlt
      omega
    have hx : x n = 2 := by
      by_cases h0 : x n = 0
      · simp [h0, lazyTwoDimensionalStep] at hdrop
      by_cases h1 : x n = 1
      · simp [h1, lazyTwoDimensionalStep] at hdrop
      have hv0 : (x n).val ≠ 0 := by
        intro hv
        exact h0 (Fin.ext hv)
      have hv1 : (x n).val ≠ 1 := by
        intro hv
        exact h1 (Fin.ext hv)
      apply Fin.ext
      have hv := (x n).isLt
      omega
    have hcurrent : runningMin
        (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n =
          (codeWalk (lExcursionDummyPrefix x) n).2 := by
      have hrec' := hrecord
      rw [hqstep, hx] at hrec'
      simp only [lazyTwoDimensionalStep_two, Prod.snd_add] at hrec'
      have hminle := runningMin_le
        (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n n le_rfl
      omega
    have hminNext : globalLazyRunningMinimum
        (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) (n + 1) =
          (codeWalk (lExcursionDummyPrefix x) (n + 1)).2 := by
      rw [globalLazyRunningMinimum_succ_local, hmin]
      exact min_eq_right (le_of_lt hrecord)
    rw [hmin n, hminNext, hqstep]
    simp [lExcursionShift_succ, hrecord, hx, lazyTwoDimensionalStep]
    rw [hcurrent]
    constructor <;> omega
  · have hminNext : globalLazyRunningMinimum
        (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) (n + 1) =
          globalLazyRunningMinimum
            (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n := by
      rw [globalLazyRunningMinimum_succ_local]
      rw [hmin n]
      exact min_eq_left (le_of_not_gt hrecord)
    rw [hmin n, hminNext, hqstep]
    simp [lExcursionShift_succ, hrecord, lazyTwoDimensionalStep]
    simp only [hmin n]
    constructor <;> omega

private theorem lExcursionShift_tail_integrate_eq_rPitmanCodeWalk
    (x : ℕ → Fin 3) (m : ℕ) :
    integrateCodes (fun i => lExcursionShift x (i + 1)) m =
      rPitmanCodeWalk (lExcursionDummyPrefix x) m := by
  induction m with
  | zero =>
      simp [integrateCodes, rPitmanCodeWalk, vectorPitman, codeWalk_zero, stepRotate,
        stepRotateInv, globalLazyPhi, globalLazyRunningMinimum_zero]
      rfl
  | succ m ih =>
      have hint : integrateCodes (fun i => lExcursionShift x (i + 1)) (m + 1) =
          integrateCodes (fun i => lExcursionShift x (i + 1)) m +
            lazyTwoDimensionalStep (lExcursionShift x (m + 1)) := by
        unfold integrateCodes
        exact Finset.sum_range_succ _ _
      rw [hint, ih]
      have hstep := lExcursionShift_step_eq_rPitman x m
      change lazyTwoDimensionalStep (lExcursionShift x (m + 1)) =
        rPitmanCodeWalk (lExcursionDummyPrefix x) (m + 1) -
          rPitmanCodeWalk (lExcursionDummyPrefix x) m at hstep
      rw [hstep]
      abel

private theorem integrateCodes_succ_local (c : ℕ → Fin 3) (n : ℕ) :
    integrateCodes c (n + 1) =
      integrateCodes c n + lazyTwoDimensionalStep (c n) := by
  unfold integrateCodes
  exact Finset.sum_range_succ _ _

private theorem integrateCodes_tail_sub (c : ℕ → Fin 3) (m : ℕ) :
    integrateCodes c (m + 1) - integrateCodes c 1 =
      integrateCodes (fun i => c (i + 1)) m := by
  induction m with
  | zero =>
      rw [integrateCodes_succ_local]
      simp [integrateCodes]
  | succ m ih =>
      calc
        integrateCodes c ((m + 1) + 1) - integrateCodes c 1 =
            integrateCodes c (m + 1) + lazyTwoDimensionalStep (c (m + 1)) -
              integrateCodes c 1 := by rw [integrateCodes_succ_local]
        _ = (integrateCodes c (m + 1) - integrateCodes c 1) +
              lazyTwoDimensionalStep (c (m + 1)) := by abel
        _ = integrateCodes (fun i => c (i + 1)) m +
              lazyTwoDimensionalStep (c (m + 1)) := by rw [ih]
        _ = integrateCodes (fun i => c (i + 1)) (m + 1) := by
              symm
              exact integrateCodes_succ_local _ m

/-- vertex, is the R-Pitman path of the second phase stream. The proof uses the
primed interval recoding and the strict-record flip of the Pitman transform -/
theorem quadrantPrimedIntervalWalk_shift_eq_rPitmanCodeWalk
    (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    quadrantPrimedIntervalWalk ω h (m + 1) -
        quadrantPrimedIntervalWalk ω h 1 =
      rPitmanCodeWalk ((phaseSplit ω).2) m := by
  change integrateCodes (primedCode ω h) (m + 1) -
      integrateCodes (primedCode ω h) 1 = _
  have hcode : primedCode ω h = lExcursionShift (lCode ω) := by
    funext i
    exact primedCode_eq_lExcursionShift ω h i
  rw [hcode, integrateCodes_tail_sub]
  have hstream : lExcursionDummyPrefix (lCode ω) = (phaseSplit ω).2 := by
    funext i
    cases i with
    | zero => simp [lExcursionDummyPrefix, phaseSplit]
    | succ i => simp [lExcursionDummyPrefix, lCode, phaseSplit]
  rw [← hstream]
  exact lExcursionShift_tail_integrate_eq_rPitmanCodeWalk (lCode ω) m

/-- Almost surely one flow-line-hit witness gives the shifted C13 primed
interval path as the R-Pitman path at every horizon -/
theorem iidCodeMeasure_ae_quadrantPrimedIntervalWalk_shift_eq_rPitmanCodeWalk :
    ∀ᵐ ω ∂iidCodeMeasure, ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
      ∀ m, quadrantPrimedIntervalWalk ω h (m + 1) -
          quadrantPrimedIntervalWalk ω h 1 =
        rPitmanCodeWalk ((phaseSplit ω).2) m := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times] with ω hhits
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa using hhits 0
  exact ⟨h, fun m => quadrantPrimedIntervalWalk_shift_eq_rPitmanCodeWalk ω h m⟩

/-- Almost surely the same flow-line-hit witness identifies both interval
walks with the two independent phase-split Pitman paths. The corresponding
path laws and independence are stated for these measurable representatives -/
theorem iidCodeMeasure_ae_quadrantIntervalWalks_eq_splitPitman :
    ∀ᵐ ω ∂iidCodeMeasure, ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
      quadrantHatIntervalWalk ω h =
          vectorPitmanCodeWalk ((phaseSplit ω).1) ∧
        ∀ m, quadrantPrimedIntervalWalk ω h (m + 1) -
            quadrantPrimedIntervalWalk ω h 1 =
          rPitmanCodeWalk ((phaseSplit ω).2) m := by
  filter_upwards [iidCodeMeasure_ae_quadrantHatIntervalWalk_eq_vectorPitmanCodeWalk]
    with ω hhat
  obtain ⟨h, hhat⟩ := hhat
  exact ⟨h, hhat, fun m =>
    quadrantPrimedIntervalWalk_shift_eq_rPitmanCodeWalk ω h m⟩

/-- The measurable R-Pitman representative of the shifted primed interval
walk has the exact all-horizon conditioned prefix law. Its a.e. pathwise
identification with the interval walk is in
`iidCodeMeasure_ae_quadrantIntervalWalks_eq_splitPitman` -/
theorem quadrantPrimedIntervalWalk_shift_proxy_prefix_law (n : ℕ) :
    iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
      rPitmanCodeWalk ((phaseSplit ω).2) j.val) =
        ((Measure.uniformOfFinset
          (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).2 then
            ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) /
              ((0 : ℝ) + 1)) else 0) :=
  (quadrant_walk_split_pitman_prefix_laws n).2

/-- Independence of the measurable Pitman representatives of the two
interval walks, combined with their almost-sure pathwise identification above -/
theorem quadrant_interval_walk_pitman_proxies_independent :
    (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) ⟂ᵢ[iidCodeMeasure]
      (fun ω => rPitmanCodeWalk ((phaseSplit ω).2)) :=
  quadrant_walk_split_pitman_independent

end DirectedDistances.RandomWalk

