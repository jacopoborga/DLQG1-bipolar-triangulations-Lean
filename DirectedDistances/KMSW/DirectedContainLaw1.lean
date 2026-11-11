/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.KMSWShift

/-! # KMSW stage-process law at boundary hits

The first strong-Markov-property sentence of Lemma `lem-directed-contain`
seen from a hit. This file proves that law for the finite KMSW stage process
and relates its hit time to the code-walk first-hit time. The geometric
identification of the shifted map as a submap of the original map, and the
UIQBOT law for the hatted map using `prop-future-map-law`, are outside this
data. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory

/-- Use the discrete measurable space on the finite-stage bookkeeping state. -/
instance State.instMeasurableSpace : MeasurableSpace State := ⊤

/-- The full finite-stage KMSW process started from its root edge -/
@[expose] def stageProcess (u : ℕ → Fin 3) : ℕ → State :=
  fun m => kmswStage u m

private theorem kmswStage_eq_of_prefix_eq (u v : ℕ → Fin 3) :
    ∀ n, (∀ i < n, u i = v i) → kmswStage u n = kmswStage v n := by
  intro n
  induction n with
  | zero => intro; rfl
  | succ n ih =>
    intro h
    change kmswStep (kmswStage u n) (u n) =
      kmswStep (kmswStage v n) (v n)
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

private def stageCodePrefix (m : ℕ) (u : ℕ → Fin 3) : Fin m → Fin 3 :=
  fun i => u i.val

private def extendStageCodePrefix (m : ℕ) (p : Fin m → Fin 3) : ℕ → Fin 3 :=
  fun i => if h : i < m then p ⟨i, h⟩ else 0

private def stageFromCodePrefix (m : ℕ) (p : Fin m → Fin 3) : State :=
  kmswStage (extendStageCodePrefix m p) m

private theorem measurable_stageCodePrefix (m : ℕ) :
    Measurable (stageCodePrefix m) := by
  exact measurable_pi_iff.mpr fun i => measurable_pi_apply i.val

private theorem measurable_stageFromCodePrefix (m : ℕ) :
    Measurable (stageFromCodePrefix m) := by
  exact measurable_of_finite _

private theorem stageFromCodePrefix_eq (u : ℕ → Fin 3) (m : ℕ) :
    stageFromCodePrefix m (stageCodePrefix m u) = kmswStage u m := by
  apply (kmswStage_eq_of_prefix_eq (extendStageCodePrefix m (stageCodePrefix m u)) u m)
  intro i hi
  simp [extendStageCodePrefix, stageCodePrefix, hi]

private theorem measurable_kmswStage_at (m : ℕ) :
    Measurable (fun u => kmswStage u m) := by
  have hfactor : (fun u => kmswStage u m) =
      (fun u => stageFromCodePrefix m (stageCodePrefix m u)) := by
    funext u
    exact (stageFromCodePrefix_eq u m).symm
  rw [hfactor]
  exact (measurable_stageFromCodePrefix m).comp (measurable_stageCodePrefix m)

/-- Measurability of the stage process in the product σ-algebra. Each stage
depends only on the first `m` codes, so it factors through the finite prefix -/
theorem measurable_stageProcess : Measurable stageProcess := by
  exact Measurable.of_eval fun m => measurable_kmswStage_at m

/-- At the first time the second coordinate reaches `-k`, the future KMSW
stage process has the same law as the process formed from the original codes
after their deterministic time-zero coordinate (`lem-directed-contain`, -/
theorem iidCodeMeasure_map_stageProcess_future_at_rightHit (k : ℤ) (_hk : 1 ≤ k) :
    RandomWalk.iidCodeMeasure.map
        (fun ω => stageProcess
          (fun i => ω ((RandomWalk.codeSndFirstHit (-k) ω).toNat + i + 1))) =
      RandomWalk.iidCodeMeasure.map (fun ω => stageProcess (fun i => ω (i + 1))) := by
  exact iidCodeMeasure_map_futureObject_at_rightHit
    stageProcess measurable_stageProcess k

/-- At the first time the first coordinate reaches `k`, the future KMSW
stage process has the same law as the process formed from the original codes
after their deterministic time-zero coordinate (`lem-directed-contain`, -/
theorem iidCodeMeasure_map_stageProcess_future_at_leftHit (k : ℤ) (_hk : k ≤ -1) :
    RandomWalk.iidCodeMeasure.map
        (fun ω => stageProcess
          (fun i => ω ((RandomWalk.codeFstFirstHit k ω).toNat + i + 1))) =
      RandomWalk.iidCodeMeasure.map (fun ω => stageProcess (fun i => ω (i + 1))) := by
  exact iidCodeMeasure_map_futureObject_at_leftHit
    stageProcess measurable_stageProcess k

private theorem codeWalk_eq_stageCodeCoordinates (ω : ℕ → Fin 3) (n : ℕ) :
    RandomWalk.codeWalk ω n =
      (L (fun i => ω (i + 1)) n, R (fun i => ω (i + 1)) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let w : ℕ → Fin 3 := fun i => ω (i + 1)
    have hwalk : RandomWalk.codeWalk ω (n + 1) =
        RandomWalk.codeWalk ω n + RandomWalk.lazyTwoDimensionalStep (ω (n + 1)) := by
      have h := RandomWalk.codeWalk_succ_sub ω n
      calc
        RandomWalk.codeWalk ω (n + 1) =
            (RandomWalk.codeWalk ω (n + 1) - RandomWalk.codeWalk ω n) +
              RandomWalk.codeWalk ω n := by abel
        _ = _ := by rw [h]; abel
    have hL : L w (n + 1) = L w n +
        (RandomWalk.lazyTwoDimensionalStep (ω (n + 1))).1 := by
      simp only [L, w, Finset.sum_range_succ]
    have hR : R w (n + 1) = R w n +
        (RandomWalk.lazyTwoDimensionalStep (ω (n + 1))).2 := by
      simp only [R, w, Finset.sum_range_succ]
    rw [hwalk, ih, hL, hR]
    rfl

/-- For `w i = ω (i + 1)`, the boundary time of the hit of `R = -k` is the
code walk's first hit time of `-k` (`eqn-bdy-vertex-kmsw` and -/
theorem codeSndFirstHit_eq_boundaryHitTime (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) {k : ℤ} (hk : 1 ≤ k) :
    RandomWalk.codeSndFirstHit (-k) ω =
      (boundaryHitTime (fun i => ω (i + 1)) h k : ℕ∞) := by
  classical
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  have hp (n : ℕ) : (RandomWalk.codeWalk ω n).2 = -k ↔ R w n = -k := by
    rw [codeWalk_eq_stageCodeCoordinates]
  have hcode : ∃ n, (RandomWalk.codeWalk ω n).2 = -k := by
    obtain ⟨n, hn⟩ := h.rightHit k hk
    exact ⟨n, (hp n).2 hn⟩
  have hfind : Nat.find hcode = Nat.find (h.rightHit k hk) := by
    apply Nat.find_congr'
    intro n
    exact hp n
  have htime : boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_left (by omega : 0 < k)]
  rw [RandomWalk.codeSndFirstHit, dite_eq_left hcode, hfind, htime]

/-- For `w i = ω (i + 1)`, the boundary time of the hit of `L = k` is the
code walk's first hit time of `k` (`eqn-bdy-vertex-kmsw` and -/
theorem codeFstFirstHit_eq_boundaryHitTime (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) {k : ℤ} (hk : k ≤ -1) :
    RandomWalk.codeFstFirstHit k ω =
      (boundaryHitTime (fun i => ω (i + 1)) h k : ℕ∞) := by
  classical
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  have hp (n : ℕ) : (RandomWalk.codeWalk ω n).1 = k ↔ L w n = k := by
    rw [codeWalk_eq_stageCodeCoordinates]
  have hcode : ∃ n, (RandomWalk.codeWalk ω n).1 = k := by
    obtain ⟨n, hn⟩ := h.leftHit k hk
    exact ⟨n, (hp n).2 hn⟩
  have hfind : Nat.find hcode = Nat.find (h.leftHit k hk) := by
    apply Nat.find_congr'
    intro n
    exact hp n
  have htime : boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  rw [RandomWalk.codeFstFirstHit, dite_eq_left hcode, hfind, htime]

/-- Shifting the KMSW run by any deterministic time `t` starts the run from
the global stage at `t` and yields the global stage at `t + m`
`w i = ω (i + 1)`, this is the stage-process form of
`kmswRun_shift_eq_stage`. -/
theorem kmswRun_stageProcess_shift (ω : ℕ → Fin 3) (t m : ℕ) :
    kmswRun (stageProcess (fun i => ω (i + 1)) t)
      (fun i => ω (t + i + 1)) m =
    stageProcess (fun i => ω (i + 1)) (t + m) := by
  simpa [stageProcess, Nat.add_assoc] using
    kmswRun_shift_eq_stage (fun i => ω (i + 1)) t m

/-- The stages after the second-coordinate hit are the run of its future
codes from the global stage at that same hit time
boundary-hit witnesses are supplied, `codeSndFirstHit_eq_boundaryHitTime`
identifies this time with `boundaryHitTime`. -/
theorem kmswRun_stageProcess_after_rightCodeHit (ω : ℕ → Fin 3) (k : ℤ) (m : ℕ) :
    kmswRun
      (stageProcess (fun i => ω (i + 1)) (RandomWalk.codeSndFirstHit (-k) ω).toNat)
      (fun i => ω ((RandomWalk.codeSndFirstHit (-k) ω).toNat + i + 1)) m =
    stageProcess (fun i => ω (i + 1)) ((RandomWalk.codeSndFirstHit (-k) ω).toNat + m) := by
  exact kmswRun_stageProcess_shift ω (RandomWalk.codeSndFirstHit (-k) ω).toNat m

/-- The stages after the first-coordinate hit are the run of its future
codes from the global stage at that same hit time
boundary-hit witnesses are supplied, `codeFstFirstHit_eq_boundaryHitTime`
identifies this time with `boundaryHitTime`. -/
theorem kmswRun_stageProcess_after_leftCodeHit (ω : ℕ → Fin 3) (k : ℤ) (m : ℕ) :
    kmswRun
      (stageProcess (fun i => ω (i + 1)) (RandomWalk.codeFstFirstHit k ω).toNat)
      (fun i => ω ((RandomWalk.codeFstFirstHit k ω).toNat + i + 1)) m =
    stageProcess (fun i => ω (i + 1)) ((RandomWalk.codeFstFirstHit k ω).toNat + m) := by
  exact kmswRun_stageProcess_shift ω (RandomWalk.codeFstFirstHit k ω).toNat m

end DirectedDistances.KMSW
