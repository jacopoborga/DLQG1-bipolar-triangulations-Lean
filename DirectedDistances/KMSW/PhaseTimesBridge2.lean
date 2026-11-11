/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.PhaseTimesBridge

/-! # Enumerating the phase times of the quadrant splitter


* `rPhaseTime ω h m` is the zero-based enumeration (index `m` here,
  `rCount = m`), in increasing order, of the times at which the splitter
  *state* is in the R phase; likewise `lPhaseTime` for the L phase.  These are
  NOT equated here with the source's `S_m` / `S'_m`: the printed counting
  definition `eqn-walk-quadrant-time` has a zero-time issue (recorded as source
* The Lean split streams select the code `w n`, i.e. the increment *leaving*
  the enumerated phase state `n` (`Z(n+1) - Z(n)`).  `codeWalk (phaseSplit ω).1`
  (resp. `.2`) is the sum of the increments leaving the enumerated R-phase
  (resp. L-phase) states (`codeWalk_rStream_eq_rPhaseSum`,
  `codeWalk_lStream_eq_lPhaseSum`).  By contrast `eqn-walk-quadrant` selects
  increments *arriving* at the selected times (`Z(S_m) - Z(S_m - 1)`); the two
  differ (e.g. for a walk starting `(-1,0), (1,-1)` the Lean R stream starts
  with `(-1,0)`, while the source concatenation `eqn-quad-pre2` starts with
  `(1,-1)`).  Hence these sums are NOT identified here with `Ẑ` of
  `eqn-walk-quadrant`, nor with the pre-replacement `Ẑ'` of
  `eqn-walk-quadrant'`; an additional boundary/index reconciliation is
  required and is not provided.
* Indexing: `walkNR k = N_{k+1}^R` and `walkNL k = N_{k+1}^L`.  R-phase times
  lie in `[walkNR k, walkNL k)` and L-phase times in
  `[walkNL k, walkNR (k + 1))`.

This file does not state `lem-quad-kmsw`; it enumerates the phase times,
proves the leaving-increment identities above, and proves an almost-sure
count-divergence lemma for the split streams
(`ae_quadrantSplitState_counts_tend_to_infinity`). -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private theorem rCount_add_on_R_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k d : ℕ)
    (hd : walkNR (fun i => ω (i + 1)) h k + d ≤
      walkNL (fun i => ω (i + 1)) h k) :
    (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k + d)).rCount =
      (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).rCount + d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNR (fun i => ω (i + 1)) h k + d ≤
          walkNL (fun i => ω (i + 1)) h k := by omega
      have hp : (quadrantSplitState ω
          (walkNR (fun i => ω (i + 1)) h k + d)).phase = .r := by
        apply (quadrantSplitState_rPhase_iff ω h _).2
        exact ⟨k, by omega, by omega⟩
      have hs : (quadrantSplitState ω
          (walkNR (fun i => ω (i + 1)) h k + d + 1)).rCount =
          (quadrantSplitState ω
            (walkNR (fun i => ω (i + 1)) h k + d)).rCount + 1 := by
        rw [quadrantSplitState, quadrantSplitAdvance_rCount]
        simp [hp]
      rw [show walkNR (fun i => ω (i + 1)) h k + (d + 1) =
        (walkNR (fun i => ω (i + 1)) h k + d) + 1 by omega]
      rw [hs, ih hd']
      omega

private theorem rCount_constant_on_L_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k d : ℕ)
    (hd : walkNL (fun i => ω (i + 1)) h k + d ≤
      walkNR (fun i => ω (i + 1)) h (k + 1)) :
    (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k + d)).rCount =
      (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).rCount := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNL (fun i => ω (i + 1)) h k + d ≤
          walkNR (fun i => ω (i + 1)) h (k + 1) := by omega
      have hp : (quadrantSplitState ω
          (walkNL (fun i => ω (i + 1)) h k + d)).phase = .l := by
        apply (quadrantSplitState_lPhase_iff ω h _).2
        exact ⟨k, by omega, by omega⟩
      have hs : (quadrantSplitState ω
          (walkNL (fun i => ω (i + 1)) h k + d + 1)).rCount =
          (quadrantSplitState ω
            (walkNL (fun i => ω (i + 1)) h k + d)).rCount := by
        rw [quadrantSplitState, quadrantSplitAdvance_rCount]
        simp [hp]
      rw [show walkNL (fun i => ω (i + 1)) h k + (d + 1) =
        (walkNL (fun i => ω (i + 1)) h k + d) + 1 by omega]
      rw [hs, ih hd']

private theorem walkNR_ge_index_local (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ k, k ≤ walkNR w h k := by
  intro k
  induction k with
  | zero => simp [walkNR_zero]
  | succ k ih =>
      have hL := walkNL_spec w h k
      have hR := walkNR_succ_spec w h k
      omega

/-- There is an R-phase state strictly after every state time, by the
unbounded sequence of flow-line return times. -/
theorem rPhase_exists_after (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (n : ℕ) :
    ∃ m, n < m ∧ (quadrantSplitState ω m).phase = .r := by
  let w := fun i => ω (i + 1)
  refine ⟨walkNR w h (n + 1), ?_, ?_⟩
  · have hb := walkNR_ge_index_local w h (n + 1)
    omega
  · exact (quadrantSplitState_at_walkNR ω h (n + 1)).1

private theorem rCount_at_walkNR_succ (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h (k + 1))).rCount =
      (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).rCount +
        (walkNL (fun i => ω (i + 1)) h k - walkNR (fun i => ω (i + 1)) h k) := by
  let tR := walkNR (fun i => ω (i + 1)) h k
  let tL := walkNL (fun i => ω (i + 1)) h k
  let tNext := walkNR (fun i => ω (i + 1)) h (k + 1)
  have hL := walkNL_spec (fun i => ω (i + 1)) h k
  have hR := walkNR_succ_spec (fun i => ω (i + 1)) h k
  have hblockR := rCount_add_on_R_interval ω h k (tL - tR) (by omega)
  have hblockL := rCount_constant_on_L_interval ω h k (tNext - tL) (by omega)
  have hidxL : tR + (tL - tR) = tL := by omega
  have hidxR : tL + (tNext - tL) = tNext := by omega
  calc
    (quadrantSplitState ω tNext).rCount =
        (quadrantSplitState ω (tL + (tNext - tL))).rCount := by rw [hidxR]
    _ = (quadrantSplitState ω tL).rCount := hblockL
    _ = (quadrantSplitState ω (tR + (tL - tR))).rCount := by rw [hidxL]
    _ = (quadrantSplitState ω tR).rCount + (tL - tR) := hblockR

private theorem rPhase_next_count (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (n : ℕ)
    (hp : (quadrantSplitState ω n).phase = .r) :
    ∃ m, n < m ∧ (quadrantSplitState ω m).phase = .r ∧
      (quadrantSplitState ω m).rCount = (quadrantSplitState ω n).rCount + 1 := by
  obtain ⟨k, hn0, hn1⟩ := (quadrantSplitState_rPhase_iff ω h n).1 hp
  by_cases hcontinue : n + 1 < walkNL (fun i => ω (i + 1)) h k
  · have hp' : (quadrantSplitState ω (n + 1)).phase = .r := by
      apply (quadrantSplitState_rPhase_iff ω h _).2
      exact ⟨k, by omega, hcontinue⟩
    refine ⟨n + 1, by omega, hp', ?_⟩
    rw [quadrantSplitState, quadrantSplitAdvance_rCount]
    simp [hp]
  · have hboundary : n + 1 = walkNL (fun i => ω (i + 1)) h k := by omega
    let tL := walkNL (fun i => ω (i + 1)) h k
    let tNext := walkNR (fun i => ω (i + 1)) h (k + 1)
    have hpNext : (quadrantSplitState ω tNext).phase = .r :=
      (quadrantSplitState_at_walkNR ω h (k + 1)).1
    have hidxL : n + 1 = tL := by simpa [tL] using hboundary
    have hidxNext : tL + (tNext - tL) = tNext := by
      have hgap := walkNR_succ_spec (fun i => ω (i + 1)) h k
      omega
    have hcountBoundary : (quadrantSplitState ω tL).rCount =
        (quadrantSplitState ω n).rCount + 1 := by
      rw [← hidxL, quadrantSplitState, quadrantSplitAdvance_rCount]
      simp [hp]
    have hcountNext := rCount_constant_on_L_interval ω h k (tNext - tL) (by
      have hgap := walkNR_succ_spec (fun i => ω (i + 1)) h k
      omega)
    refine ⟨tNext, ?_, hpNext, ?_⟩
    · have hgap := walkNR_succ_spec (fun i => ω (i + 1)) h k
      omega
    · rw [← hidxNext, hcountNext, hcountBoundary]

/-- The zero-based enumeration of the R-phase STATE times: the times at which
the splitter state is in the R phase and ready to consume the next R code.
Not equated with the source's `S_m` (`eqn-walk-quadrant-time`, -/
@[expose] noncomputable def rPhaseTime (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) : ℕ → ℕ
  | 0 => 0
  | m + 1 => Nat.find (rPhase_exists_after ω h (rPhaseTime ω h m))

/-- Every enumerated R-phase time has phase `r`. -/
theorem rPhaseTime_phase (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    (quadrantSplitState ω (rPhaseTime ω h m)).phase = .r := by
  induction m with
  | zero => simp [rPhaseTime, quadrantSplitState, quadrantSplitStart]
  | succ m ih =>
      exact (Nat.find_spec (rPhase_exists_after ω h (rPhaseTime ω h m))).2

/-- Consecutive entries of `rPhaseTime` are strictly ordered. -/
theorem rPhaseTime_lt_succ (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    rPhaseTime ω h m < rPhaseTime ω h (m + 1) := by
  simpa [rPhaseTime] using
    (Nat.find_spec (rPhase_exists_after ω h (rPhaseTime ω h m))).1

/-- The enumerated R-phase state times `rPhaseTime` of this file increase
strictly (not identified here with the source's R-times, see the module -/
theorem strictMono_rPhaseTime (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    StrictMono (rPhaseTime ω h) :=
  strictMono_nat_of_lt_succ (rPhaseTime_lt_succ ω h)

/-- The R-phase time with index `m` has consumed exactly `m` R codes. -/
theorem rPhaseTime_rCount (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    (quadrantSplitState ω (rPhaseTime ω h m)).rCount = m := by
  induction m with
  | zero => simp [rPhaseTime, quadrantSplitState, quadrantSplitStart]
  | succ m ih =>
      let t := rPhaseTime ω h m
      let u := rPhaseTime ω h (m + 1)
      have hnext := rPhase_next_count ω h t (rPhaseTime_phase ω h m)
      obtain ⟨q, htq, hpq, hcountq⟩ := hnext
      have hu_spec : t < u ∧ (quadrantSplitState ω u).phase = .r := by
        simpa [u, rPhaseTime] using
          (Nat.find_spec (rPhase_exists_after ω h t))
      have huq : u ≤ q := by
        dsimp [u]
        exact Nat.find_min' (rPhase_exists_after ω h t) (show t < q ∧
          (quadrantSplitState ω q).phase = .r from ⟨htq, hpq⟩)
      have ht1u : t + 1 ≤ u := by omega
      have hlow := quadrantSplitState_rCount_mono ω (t + 1) u ht1u
      have hstep : (quadrantSplitState ω (t + 1)).rCount =
          (quadrantSplitState ω t).rCount + 1 := by
        have htphase : (quadrantSplitState ω t).phase = .r := by
          simpa [t] using rPhaseTime_phase ω h m
        calc
          (quadrantSplitState ω (t + 1)).rCount =
              (quadrantSplitAdvance (quadrantSplitState ω t) (ω (t + 1))).rCount := by
                rw [quadrantSplitState]
          _ = (quadrantSplitState ω t).rCount + 1 := by
            rw [quadrantSplitAdvance_rCount]
            simp [htphase]
      have hlow' : m + 1 ≤ (quadrantSplitState ω u).rCount := by
        calc
          m + 1 = (quadrantSplitState ω (t + 1)).rCount := by
            rw [hstep, ih]
          _ ≤ (quadrantSplitState ω u).rCount := hlow
      have huq' := quadrantSplitState_rCount_mono ω u q huq
      have hupper : (quadrantSplitState ω u).rCount ≤ m + 1 := by
        calc
          (quadrantSplitState ω u).rCount ≤ (quadrantSplitState ω q).rCount := huq'
          _ = (quadrantSplitState ω t).rCount + 1 := hcountq
          _ = m + 1 := by
            have htcount : (quadrantSplitState ω t).rCount = m := by
              simpa [t] using ih
            exact congrArg (fun x : ℕ => x + 1) htcount
      have hlowS : m + 1 ≤
          (quadrantSplitState ω (rPhaseTime ω h (m + 1))).rCount := by
        simpa [u] using hlow'
      have hupperS :
          (quadrantSplitState ω (rPhaseTime ω h (m + 1))).rCount ≤ m + 1 := by
        simpa [u] using hupper
      exact le_antisymm hupperS hlowS

/-- Every enumerated R-phase time belongs to one of the half-open intervals
`[walkNR k, walkNL k)`, i.e. `[N_{k+1}^R, N_{k+1}^L)` in the source indexing -/
theorem rPhaseTime_mem_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    ∃ k, walkNR (fun i => ω (i + 1)) h k ≤ rPhaseTime ω h m ∧
      rPhaseTime ω h m < walkNL (fun i => ω (i + 1)) h k :=
  (quadrantSplitState_rPhase_iff ω h (rPhaseTime ω h m)).1
    (rPhaseTime_phase ω h m)

/-- The R-phase code sequence with its dummy code removed. -/
@[expose] noncomputable def rCode (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun m => (phaseSplit ω).1 (m + 1)

/-- The L-phase code sequence with its dummy code removed. -/
@[expose] noncomputable def lCode (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun m => (phaseSplit ω).2 (m + 1)

/-- The R-phase code at index `m` is the original walk code `w n` at the
enumerated R-phase state time `n`, i.e. the increment leaving that state.  This
is not identified here with the arriving increment of `eqn-walk-quadrant` -/
theorem rCode_eq_walk_at_rPhaseTime (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    rCode ω m = (fun i => ω (i + 1)) (rPhaseTime ω h m) := by
  unfold rCode
  have hindex : m + 1 =
      (quadrantSplitState ω (rPhaseTime ω h m)).rCount + 1 := by
    have hc := rPhaseTime_rCount ω h m
    omega
  rw [hindex]
  exact phaseSplit_rCode_at_walk_step ω (rPhaseTime ω h m)
    (rPhaseTime_phase ω h m)

private theorem lCount_constant_on_R_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k d : ℕ)
    (hd : walkNR (fun i => ω (i + 1)) h k + d ≤
      walkNL (fun i => ω (i + 1)) h k) :
    (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k + d)).lCount =
      (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).lCount := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNR (fun i => ω (i + 1)) h k + d ≤
          walkNL (fun i => ω (i + 1)) h k := by omega
      have hp : (quadrantSplitState ω
          (walkNR (fun i => ω (i + 1)) h k + d)).phase = .r := by
        apply (quadrantSplitState_rPhase_iff ω h _).2
        exact ⟨k, by omega, by omega⟩
      have hs : (quadrantSplitState ω
          (walkNR (fun i => ω (i + 1)) h k + d + 1)).lCount =
          (quadrantSplitState ω
            (walkNR (fun i => ω (i + 1)) h k + d)).lCount := by
        rw [quadrantSplitState, quadrantSplitAdvance_lCount]
        simp [hp]
      rw [show walkNR (fun i => ω (i + 1)) h k + (d + 1) =
        (walkNR (fun i => ω (i + 1)) h k + d) + 1 by omega]
      rw [hs, ih hd']

private theorem lCount_add_on_L_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k d : ℕ)
    (hd : walkNL (fun i => ω (i + 1)) h k + d ≤
      walkNR (fun i => ω (i + 1)) h (k + 1)) :
    (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k + d)).lCount =
      (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).lCount + d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNL (fun i => ω (i + 1)) h k + d ≤
          walkNR (fun i => ω (i + 1)) h (k + 1) := by omega
      have hp : (quadrantSplitState ω
          (walkNL (fun i => ω (i + 1)) h k + d)).phase = .l := by
        apply (quadrantSplitState_lPhase_iff ω h _).2
        exact ⟨k, by omega, by omega⟩
      have hs : (quadrantSplitState ω
          (walkNL (fun i => ω (i + 1)) h k + d + 1)).lCount =
          (quadrantSplitState ω
            (walkNL (fun i => ω (i + 1)) h k + d)).lCount + 1 := by
        rw [quadrantSplitState, quadrantSplitAdvance_lCount]
        simp [hp]
      rw [show walkNL (fun i => ω (i + 1)) h k + (d + 1) =
        (walkNL (fun i => ω (i + 1)) h k + d) + 1 by omega]
      rw [hs, ih hd']
      omega

private theorem walkNL_ge_index_local (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ k, k ≤ walkNL w h k := by
  intro k
  have hNR := walkNR_ge_index_local w h k
  have hL := walkNL_spec w h k
  omega

/-- There is an L-phase state strictly after every state time, by the
unbounded sequence of flow-line return times. -/
theorem lPhase_exists_after (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (n : ℕ) :
    ∃ m, n < m ∧ (quadrantSplitState ω m).phase = .l := by
  let w := fun i => ω (i + 1)
  refine ⟨walkNL w h (n + 1), ?_, ?_⟩
  · have hb := walkNL_ge_index_local w h (n + 1)
    omega
  · exact (quadrantSplitState_at_walkNL ω h (n + 1)).1

private theorem lCount_at_walkNL_succ (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h (k + 1))).lCount =
      (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).lCount +
        (walkNR (fun i => ω (i + 1)) h (k + 1) - walkNL (fun i => ω (i + 1)) h k) := by
  let tL := walkNL (fun i => ω (i + 1)) h k
  let tR := walkNR (fun i => ω (i + 1)) h (k + 1)
  let tNext := walkNL (fun i => ω (i + 1)) h (k + 1)
  have hR := walkNR_succ_spec (fun i => ω (i + 1)) h k
  have hL := walkNL_spec (fun i => ω (i + 1)) h (k + 1)
  have hblockL := lCount_add_on_L_interval ω h k (tR - tL) (by omega)
  have hblockR := lCount_constant_on_R_interval ω h (k + 1) (tNext - tR) (by omega)
  have hidxR : tL + (tR - tL) = tR := by omega
  have hidxL : tR + (tNext - tR) = tNext := by omega
  calc
    (quadrantSplitState ω tNext).lCount =
        (quadrantSplitState ω (tR + (tNext - tR))).lCount := by rw [hidxL]
    _ = (quadrantSplitState ω tR).lCount := hblockR
    _ = (quadrantSplitState ω (tL + (tR - tL))).lCount := by rw [hidxR]
    _ = (quadrantSplitState ω tL).lCount + (tR - tL) := hblockL

private theorem lPhase_next_count (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (n : ℕ)
    (hp : (quadrantSplitState ω n).phase = .l) :
    ∃ m, n < m ∧ (quadrantSplitState ω m).phase = .l ∧
      (quadrantSplitState ω m).lCount = (quadrantSplitState ω n).lCount + 1 := by
  obtain ⟨k, hn0, hn1⟩ := (quadrantSplitState_lPhase_iff ω h n).1 hp
  by_cases hcontinue : n + 1 < walkNR (fun i => ω (i + 1)) h (k + 1)
  · have hp' : (quadrantSplitState ω (n + 1)).phase = .l := by
      apply (quadrantSplitState_lPhase_iff ω h _).2
      exact ⟨k, by omega, hcontinue⟩
    refine ⟨n + 1, by omega, hp', ?_⟩
    rw [quadrantSplitState, quadrantSplitAdvance_lCount]
    simp [hp]
  · have hboundary : n + 1 = walkNR (fun i => ω (i + 1)) h (k + 1) := by omega
    let tR := walkNR (fun i => ω (i + 1)) h (k + 1)
    let tNext := walkNL (fun i => ω (i + 1)) h (k + 1)
    have hpNext : (quadrantSplitState ω tNext).phase = .l :=
      (quadrantSplitState_at_walkNL ω h (k + 1)).1
    have hidxR : n + 1 = tR := by simpa [tR] using hboundary
    have hidxNext : tR + (tNext - tR) = tNext := by
      have hgap := walkNL_spec (fun i => ω (i + 1)) h (k + 1)
      omega
    have hcountBoundary : (quadrantSplitState ω tR).lCount =
        (quadrantSplitState ω n).lCount + 1 := by
      rw [← hidxR, quadrantSplitState, quadrantSplitAdvance_lCount]
      simp [hp]
    have hcountNext := lCount_constant_on_R_interval ω h (k + 1) (tNext - tR) (by
      have hgap := walkNL_spec (fun i => ω (i + 1)) h (k + 1)
      omega)
    refine ⟨tNext, ?_, hpNext, ?_⟩
    · have hgap := walkNL_spec (fun i => ω (i + 1)) h (k + 1)
      omega
    · rw [← hidxNext, hcountNext, hcountBoundary]

/-- The zero-based enumeration of the L-phase STATE times, defined just as for
the R phase.  Not equated with the source's `S'_m` (`eqn-walk-quadrant-time`, -/
@[expose] noncomputable def lPhaseTime (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) : ℕ → ℕ
  | 0 => Nat.find (lPhase_exists_after ω h 0)
  | m + 1 => Nat.find (lPhase_exists_after ω h (lPhaseTime ω h m))

/-- Every enumerated L-phase time has phase `l`. -/
theorem lPhaseTime_phase (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    (quadrantSplitState ω (lPhaseTime ω h m)).phase = .l := by
  cases m with
  | zero => exact (Nat.find_spec (lPhase_exists_after ω h 0)).2
  | succ m =>
      simpa [lPhaseTime] using
        (Nat.find_spec (lPhase_exists_after ω h (lPhaseTime ω h m))).2

/-- Consecutive entries of `lPhaseTime` are strictly ordered. -/
theorem lPhaseTime_lt_succ (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    lPhaseTime ω h m < lPhaseTime ω h (m + 1) := by
  simpa [lPhaseTime] using
    (Nat.find_spec (lPhase_exists_after ω h (lPhaseTime ω h m))).1

/-- The enumerated L-phase state times `lPhaseTime` of this file increase
strictly (not identified here with the source's L-times, see the module -/
theorem strictMono_lPhaseTime (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    StrictMono (lPhaseTime ω h) :=
  strictMono_nat_of_lt_succ (lPhaseTime_lt_succ ω h)

/-- The L-phase time with index `m` has consumed exactly `m` L codes. -/
theorem lPhaseTime_lCount (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    (quadrantSplitState ω (lPhaseTime ω h m)).lCount = m := by
  induction m with
  | zero =>
      let t := walkNL (fun i => ω (i + 1)) h 0
      have ht : (quadrantSplitState ω t).phase = .l :=
        (quadrantSplitState_at_walkNL ω h 0).1
      have hzeroTime : walkNR (fun i => ω (i + 1)) h 0 = 0 :=
        walkNR_zero _ _
      have hfirst : ∀ n < t, ¬ (quadrantSplitState ω n).phase = .l := by
        intro n hn
        have hp := (quadrantSplitState_rPhase_iff ω h n).2
          ⟨0, by rw [hzeroTime]; omega, by simpa [t] using hn⟩
        simp [hp]
      have hfind : Nat.find (lPhase_exists_after ω h 0) = t := by
        apply (Nat.find_eq_iff (lPhase_exists_after ω h 0)).2
        constructor
        · exact ⟨by
            have hs := walkNL_spec (fun i => ω (i + 1)) h 0
            rw [hzeroTime] at hs
            omega, ht⟩
        · intro n hn hphase
          exact hfirst n hn hphase.2
      have hblock := lCount_constant_on_R_interval ω h 0 t (by
        rw [hzeroTime]
        omega)
      change (quadrantSplitState ω (Nat.find (lPhase_exists_after ω h 0))).lCount = 0
      rw [hfind]
      simpa [quadrantSplitState, quadrantSplitStart, hzeroTime] using hblock
  | succ m ih =>
      let t := lPhaseTime ω h m
      let u := lPhaseTime ω h (m + 1)
      obtain ⟨q, htq, hpq, hcountq⟩ :=
        lPhase_next_count ω h t (lPhaseTime_phase ω h m)
      have hu_spec : t < u ∧ (quadrantSplitState ω u).phase = .l := by
        simpa [u, lPhaseTime] using (Nat.find_spec (lPhase_exists_after ω h t))
      have huq : u ≤ q := by
        dsimp [u]
        exact Nat.find_min' (lPhase_exists_after ω h t) (show t < q ∧
          (quadrantSplitState ω q).phase = .l from ⟨htq, hpq⟩)
      have ht1u : t + 1 ≤ u := by omega
      have hlow := quadrantSplitState_lCount_mono ω (t + 1) u ht1u
      have hstep : (quadrantSplitState ω (t + 1)).lCount =
          (quadrantSplitState ω t).lCount + 1 := by
        have htphase : (quadrantSplitState ω t).phase = .l := by
          simpa [t] using lPhaseTime_phase ω h m
        calc
          (quadrantSplitState ω (t + 1)).lCount =
              (quadrantSplitAdvance (quadrantSplitState ω t) (ω (t + 1))).lCount := by
                rw [quadrantSplitState]
          _ = (quadrantSplitState ω t).lCount + 1 := by
            rw [quadrantSplitAdvance_lCount]
            simp [htphase]
      have hlow' : m + 1 ≤ (quadrantSplitState ω u).lCount := by
        calc
          m + 1 = (quadrantSplitState ω (t + 1)).lCount := by
            rw [hstep, ih]
          _ ≤ (quadrantSplitState ω u).lCount := hlow
      have huq' := quadrantSplitState_lCount_mono ω u q huq
      have hupper : (quadrantSplitState ω u).lCount ≤ m + 1 := by
        calc
          (quadrantSplitState ω u).lCount ≤ (quadrantSplitState ω q).lCount := huq'
          _ = (quadrantSplitState ω t).lCount + 1 := hcountq
          _ = m + 1 := by
            have htcount : (quadrantSplitState ω t).lCount = m := by
              simpa [t] using ih
            exact congrArg (fun x : ℕ => x + 1) htcount
      have hlowS : m + 1 ≤
          (quadrantSplitState ω (lPhaseTime ω h (m + 1))).lCount := by
        simpa [u] using hlow'
      have hupperS :
          (quadrantSplitState ω (lPhaseTime ω h (m + 1))).lCount ≤ m + 1 := by
        simpa [u] using hupper
      exact le_antisymm hupperS hlowS

/-- Every enumerated L-phase time belongs to one of the half-open intervals
`[walkNL k, walkNR (k + 1))`, i.e. `[N_{k+1}^L, N_{k+2}^R)` in the source -/
theorem lPhaseTime_mem_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    ∃ k, walkNL (fun i => ω (i + 1)) h k ≤ lPhaseTime ω h m ∧
      lPhaseTime ω h m < walkNR (fun i => ω (i + 1)) h (k + 1) :=
  (quadrantSplitState_lPhase_iff ω h (lPhaseTime ω h m)).1
    (lPhaseTime_phase ω h m)

/-- The L-phase code at index `m` is the original walk code `w n` at the
enumerated L-phase state time `n`, i.e. the increment leaving that state.  This
is not identified here with the arriving increment of `eqn-walk-quadrant`, nor
with the pre-replacement increments of `eqn-walk-quadrant'` -/
theorem lCode_eq_walk_at_lPhaseTime (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    lCode ω m = (fun i => ω (i + 1)) (lPhaseTime ω h m) := by
  unfold lCode
  have hindex : m + 1 =
      (quadrantSplitState ω (lPhaseTime ω h m)).lCount + 1 := by
    have hc := lPhaseTime_lCount ω h m
    omega
  rw [hindex]
  exact phaseSplit_lCode_at_walk_step ω (lPhaseTime ω h m)
    (lPhaseTime_phase ω h m)

/-- The integrated R-phase code sequence is the sum of the first `m`
increments leaving the enumerated R-phase states.  This is NOT identified here
with `Ẑ` of `eqn-walk-quadrant` (arriving increments,
reconciliation is required and is not provided. -/
theorem integrateCodes_rCode_eq_rPhaseSum (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    integrateCodes (rCode ω) m =
      ∑ j ∈ Finset.range m,
        lazyTwoDimensionalStep ((fun i => ω (i + 1)) (rPhaseTime ω h j)) := by
  unfold integrateCodes
  apply Finset.sum_congr rfl
  intro j hj
  rw [rCode_eq_walk_at_rPhaseTime]

/-- The integrated L-phase code sequence is the sum of the first `m`
increments leaving the enumerated L-phase states.  This is NOT identified here
with `Ẑ` of `eqn-walk-quadrant` (arriving increments) nor with the
pre-replacement `Ẑ'` of `eqn-walk-quadrant'`
reconciliation is required and is not provided. -/
theorem integrateCodes_lCode_eq_lPhaseSum (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    integrateCodes (lCode ω) m =
      ∑ j ∈ Finset.range m,
        lazyTwoDimensionalStep ((fun i => ω (i + 1)) (lPhaseTime ω h j)) := by
  unfold integrateCodes
  apply Finset.sum_congr rfl
  intro j hj
  rw [lCode_eq_walk_at_lPhaseTime]

/-- The R code walk from the dummy-prefixed split stream agrees with the
integrated zero-based R code sequence. -/
theorem codeWalk_rStream_eq_integrateCodes (ω : ℕ → Fin 3) (m : ℕ) :
    codeWalk (phaseSplit ω).1 m = integrateCodes (rCode ω) m := by
  rw [codeWalk_eq_integrateCodes]
  rfl

/-- The R code walk is the sum of the increments leaving the enumerated
R-phase states.  This is NOT identified here with `Ẑ` of `eqn-walk-quadrant`
pre-replacement `Ẑ'` of `eqn-walk-quadrant'`; an additional boundary/index
reconciliation is required and is not provided. -/
theorem codeWalk_rStream_eq_rPhaseSum (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    codeWalk (phaseSplit ω).1 m =
      ∑ j ∈ Finset.range m,
        lazyTwoDimensionalStep ((fun i => ω (i + 1)) (rPhaseTime ω h j)) := by
  rw [codeWalk_rStream_eq_integrateCodes]
  exact integrateCodes_rCode_eq_rPhaseSum ω h m

/-- The L code walk from the dummy-prefixed split stream agrees with the
integrated zero-based L code sequence. -/
theorem codeWalk_lStream_eq_integrateCodes (ω : ℕ → Fin 3) (m : ℕ) :
    codeWalk (phaseSplit ω).2 m = integrateCodes (lCode ω) m := by
  rw [codeWalk_eq_integrateCodes]
  rfl

/-- The raw L code walk is the sum of the increments leaving the enumerated
L-phase states.  This is NOT identified here with `Ẑ` of `eqn-walk-quadrant`
(arriving increments) nor with the pre-replacement `Ẑ'` of
boundary/index reconciliation is required and is not provided. -/
theorem codeWalk_lStream_eq_lPhaseSum (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    codeWalk (phaseSplit ω).2 m =
      ∑ j ∈ Finset.range m,
        lazyTwoDimensionalStep ((fun i => ω (i + 1)) (lPhaseTime ω h j)) := by
  rw [codeWalk_lStream_eq_integrateCodes]
  exact integrateCodes_lCode_eq_lPhaseSum ω h m

private theorem measurableSet_codeWalk_fst_hits_all :
    MeasurableSet {ω : ℕ → Fin 3 | ∀ z : ℤ, ∃ n, (codeWalk ω n).1 = z} := by
  have hset : {ω : ℕ → Fin 3 | ∀ z : ℤ, ∃ n, (codeWalk ω n).1 = z} =
      ⋂ z : ℤ, {ω | ∃ n, (codeWalk ω n).1 = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  apply MeasurableSet.iInter
  intro z
  have hset' : {ω : ℕ → Fin 3 | ∃ n, (codeWalk ω n).1 = z} =
      ⋃ n, {ω | (codeWalk ω n).1 = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset']
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_eq_fun
    (((measurable_pi_apply n).comp measurable_codeWalk).fst) measurable_const

private theorem measurableSet_codeWalk_snd_hits_all :
    MeasurableSet {ω : ℕ → Fin 3 | ∀ z : ℤ, ∃ n, (codeWalk ω n).2 = z} := by
  have hset : {ω : ℕ → Fin 3 | ∀ z : ℤ, ∃ n, (codeWalk ω n).2 = z} =
      ⋂ z : ℤ, {ω | ∃ n, (codeWalk ω n).2 = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  apply MeasurableSet.iInter
  intro z
  have hset' : {ω : ℕ → Fin 3 | ∃ n, (codeWalk ω n).2 = z} =
      ⋃ n, {ω | (codeWalk ω n).2 = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset']
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_eq_fun
    (((measurable_pi_apply n).comp measurable_codeWalk).snd) measurable_const

private def phaseTimesCodePrefix (n : ℕ) (ω : ℕ → Fin 3) :
    Fin (n + 1) → Fin 3 := fun j => ω j.val

private def phaseTimesCodePrefixExtend {n : ℕ}
    (q : Fin (n + 1) → Fin 3) : ℕ → Fin 3 :=
  fun i => if hi : i ≤ n then q ⟨i, by omega⟩ else 0

private theorem phaseTimesCodePrefixExtend_apply {n : ℕ}
    (q : Fin (n + 1) → Fin 3) (i : ℕ) (hi : i ≤ n) :
    phaseTimesCodePrefixExtend q i = q ⟨i, by omega⟩ := by
  simp [phaseTimesCodePrefixExtend, hi]

private theorem quadrantSplitState_eq_of_prefix_local (ω ν : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i ≤ n, ω i = ν i) : quadrantSplitState ω n = quadrantSplitState ν n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hrec : quadrantSplitState ω n = quadrantSplitState ν n := by
        apply ih
        intro i hi
        exact h i (by omega)
      change quadrantSplitAdvance (quadrantSplitState ω n) (ω (n + 1)) =
        quadrantSplitAdvance (quadrantSplitState ν n) (ν (n + 1))
      rw [hrec, h (n + 1) (by omega)]

private theorem measurable_splitRCount (n : ℕ) :
    Measurable (fun ω => (quadrantSplitState ω n).rCount) := by
  let pfx := fun ω : ℕ → Fin 3 => phaseTimesCodePrefix n ω
  let factor := fun q : Fin (n + 1) → Fin 3 =>
    (quadrantSplitState (phaseTimesCodePrefixExtend q) n).rCount
  have hpfx : Measurable pfx := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.val
  have hfactor : Measurable factor := measurable_of_countable factor
  have heq : (fun ω => (quadrantSplitState ω n).rCount) = factor ∘ pfx := by
    funext ω
    dsimp [factor, pfx]
    apply congrArg QuadrantSplitState.rCount
    apply quadrantSplitState_eq_of_prefix_local
    intro i hi
    rw [phaseTimesCodePrefixExtend_apply _ i hi]
    rfl
  rw [heq]
  exact hfactor.comp hpfx

private theorem measurable_splitLCount (n : ℕ) :
    Measurable (fun ω => (quadrantSplitState ω n).lCount) := by
  let pfx := fun ω : ℕ → Fin 3 => phaseTimesCodePrefix n ω
  let factor := fun q : Fin (n + 1) → Fin 3 =>
    (quadrantSplitState (phaseTimesCodePrefixExtend q) n).lCount
  have hpfx : Measurable pfx := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.val
  have hfactor : Measurable factor := measurable_of_countable factor
  have heq : (fun ω => (quadrantSplitState ω n).lCount) = factor ∘ pfx := by
    funext ω
    dsimp [factor, pfx]
    apply congrArg QuadrantSplitState.lCount
    apply quadrantSplitState_eq_of_prefix_local
    intro i hi
    rw [phaseTimesCodePrefixExtend_apply _ i hi]
    rfl
  rw [heq]
  exact hfactor.comp hpfx

/-- Almost surely both streams of the split iid code sequence consume
arbitrarily many codes, by the interleaving count theorem
(this uses the splitting of the iid codes modelled on `lem-quadrant-walk`, -/
theorem ae_quadrantSplitState_counts_tend_to_infinity :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ k, ∃ N, ∀ n ≥ N,
      k ≤ (quadrantSplitState ω n).rCount ∧
      k ≤ (quadrantSplitState ω n).lCount := by
  apply ae_all_iff.mpr
  intro k
  let Q : Set ((ℕ → Fin 3) × (ℕ → Fin 3)) :=
    {ab | ∃ N, ∀ n, N ≤ n →
      k ≤ (quadrantSplitState (interleave ab) n).rCount ∧
      k ≤ (quadrantSplitState (interleave ab) n).lCount}
  have hQr (n : ℕ) :
      Measurable fun ab : (ℕ → Fin 3) × (ℕ → Fin 3) =>
        (quadrantSplitState (interleave ab) n).rCount :=
    measurable_splitRCount n |>.comp measurable_interleave
  have hQl (n : ℕ) :
      Measurable fun ab : (ℕ → Fin 3) × (ℕ → Fin 3) =>
        (quadrantSplitState (interleave ab) n).lCount :=
    measurable_splitLCount n |>.comp measurable_interleave
  have hQeq : Q = ⋃ N, ⋂ n,
      {ab | n < N ∨
        (k ≤ (quadrantSplitState (interleave ab) n).rCount ∧
         k ≤ (quadrantSplitState (interleave ab) n).lCount)} := by
    ext ab
    simp only [Q, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨N, hN⟩
      refine ⟨N, fun n => ?_⟩
      by_cases hn : N ≤ n
      · exact Or.inr (hN n hn)
      · exact Or.inl (by omega)
    · rintro ⟨N, hN⟩
      refine ⟨N, fun n hn => ?_⟩
      have h := hN n
      cases h with
      | inl hlt => omega
      | inr hcount => exact hcount
  have hQset : MeasurableSet Q := by
    rw [hQeq]
    apply MeasurableSet.iUnion
    intro N
    apply MeasurableSet.iInter
    intro n
    have hset : {ab | n < N ∨
        (k ≤ (quadrantSplitState (interleave ab) n).rCount ∧
         k ≤ (quadrantSplitState (interleave ab) n).lCount)} =
        if n < N then Set.univ else {ab |
          k ≤ (quadrantSplitState (interleave ab) n).rCount ∧
          k ≤ (quadrantSplitState (interleave ab) n).lCount} := by
      ext ab
      by_cases hn : n < N <;> simp [hn]
    rw [hset]
    by_cases hn : n < N
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      exact (measurableSet_le measurable_const (hQr n)).inter
        (measurableSet_le measurable_const (hQl n))
  have hHitA : ∀ᵐ a ∂iidCodeMeasure,
      ∀ z : ℤ, ∃ n, (codeWalk a n).1 = z := by
    apply ae_all_iff.mpr
    intro z
    exact ae_exists_codeWalk_fst_eq_int z
  have hHitB : ∀ᵐ b ∂iidCodeMeasure,
      ∀ z : ℤ, ∃ n, (codeWalk b n).2 = z := by
    apply ae_all_iff.mpr
    intro z
    exact ae_exists_codeWalk_snd_eq_int z
  have hPairSet : MeasurableSet {ab : (ℕ → Fin 3) × (ℕ → Fin 3) |
      (∀ z : ℤ, ∃ n, (codeWalk ab.1 n).1 = z) ∧
      (∀ z : ℤ, ∃ n, (codeWalk ab.2 n).2 = z)} := by
    exact (measurableSet_codeWalk_fst_hits_all.preimage measurable_fst).inter
      (measurableSet_codeWalk_snd_hits_all.preimage measurable_snd)
  have hPair : ∀ᵐ ab ∂(iidCodeMeasure.prod iidCodeMeasure),
      (∀ z : ℤ, ∃ n, (codeWalk ab.1 n).1 = z) ∧
      (∀ z : ℤ, ∃ n, (codeWalk ab.2 n).2 = z) := by
    rw [Measure.ae_prod_iff_ae_ae hPairSet]
    filter_upwards [hHitA] with a ha
    filter_upwards [hHitB] with b hb
    exact ⟨ha, hb⟩
  have hQprod : ∀ᵐ ab ∂(iidCodeMeasure.prod iidCodeMeasure), ab ∈ Q := by
    filter_upwards [hPair] with ab hab
    obtain ⟨N, hN⟩ := quadrantInterleaveState_counts_tend_to_infinity ab
      hab.1 hab.2 k
    refine ⟨N, fun n hn => ?_⟩
    simpa only [quadrantSplitState_interleave] using hN n hn
  have hQmap : ∀ᵐ ab ∂iidCodeMeasure.map phaseSplit, ab ∈ Q := by
    rw [map_phaseSplit_iidCodeMeasure]
    exact hQprod
  have hPreimage := (ae_map_iff measurable_phaseSplit.aemeasurable hQset).1 hQmap
  filter_upwards [hPreimage] with ω hω
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, fun n hn => ?_⟩
  simpa only [quadrantSplitState_interleave, quadrantInterleaveState_phaseSplit] using
    hN n hn

end DirectedDistances.KMSW
