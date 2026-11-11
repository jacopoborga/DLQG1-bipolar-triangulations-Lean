/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.HatFaceRotation

/-! # Hatted boundary facts

Boundary rotation and the induced limit assembly remain; these helpers are not
counted as the paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem hatUR_edge_lt_nextEdge (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m e : ℕ) (he : e ∈ (kmswStage (hatCodes w h) m).UR) :
    e < (kmswStage (hatCodes w h) m).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) m).2
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr he))

/-- Every finite stage of the hatted code has empty lower-left boundary. This
is a helper for the hatted half of `lem-quad-kmsw` -/
theorem hat_LL_nil (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, (kmswStage (hatCodes w h) m).LL = [] := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      change (kmswStepOfStep (kmswStage (hatCodes w h) m)
        (kmswCodeStep (hatCodes w h m))).LL = []
      cases hc : kmswCodeStep (hatCodes w h m) with
      | left =>
          have hn := noFreshLeftSource_hatCodes w h m hc
          cases hp : (kmswStage (hatCodes w h) m).UL.dropLast.reverse with
          | nil => exact (hn hp).elim
          | cons e es =>
              simpa only [kmswStepOfStep, hp, State.addEdge] using ih
      | up => simpa only [kmswStepOfStep, State.addEdge] using ih
      | down =>
          cases hu : (kmswStage (hatCodes w h) m).UR <;>
            simpa only [kmswStepOfStep, hu, State.addEdge] using ih

/-- The global vertical coordinate is unbounded below, re-derived from
`HasFlowLineHits`; this global fact is an input to the hatted-half helpers for -/
theorem R_unbounded_of_hasFlowLineHits (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ a : ℤ, ∃ m, R w m ≤ a := by
  have hlevels : ∀ k : ℕ, ∃ n, R w n = -(k : ℤ) := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp [R]⟩
    | succ k ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, _, hm⟩ := h.2 n
        exact ⟨m, by rw [hm, hn]; omega⟩
  intro a
  cases a with
  | ofNat a => exact ⟨0, by simp [R]⟩
  | negSucc k =>
      obtain ⟨n, hn⟩ := hlevels (k + 1)
      exact ⟨n, by omega⟩

private theorem R_succ_hatBoundary (u : ℕ → Fin 3) (n : ℕ) :
    R u (n + 1) = R u n + (RandomWalk.lazyTwoDimensionalStep (u n)).2 := by
  simp only [R, Finset.sum_range_succ]

private theorem lazyStep_snd_lower_hatBoundary (c : Fin 3) :
    (-1 : ℤ) ≤ (RandomWalk.lazyTwoDimensionalStep c).2 := by
  fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]

private theorem R_floor_before_firstFlowRHit_hatBoundary
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (a n : ℕ)
    (han : a ≤ n) (hn : n < firstFlowRHit w h a) : R w a ≤ R w n := by
  have hnot : ∀ j, a + 1 ≤ j → j < firstFlowRHit w h a →
      R w j ≠ R w a - 1 := by
    intro j hj hjlt heq
    change j < Nat.find (h.2 a) at hjlt
    exact Nat.find_min (h.2 a) hjlt ⟨hj, heq⟩
  have hstep : ∀ j, R w j - 1 ≤ R w (j + 1) := by
    intro j
    rw [R_succ_hatBoundary]
    have hb := lazyStep_snd_lower_hatBoundary (w j)
    omega
  have hfloor : ∀ j, a ≤ j → j < firstFlowRHit w h a → R w a ≤ R w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro _
        exact le_rfl
    | succ j hj ih =>
        intro hjlt
        by_contra hbad
        have hprev := ih (by omega)
        have hnext := hstep j
        have hnotNext := hnot (j + 1) (by omega) (by omega)
        have htarget : R w (j + 1) = R w a - 1 := by omega
        exact hnotNext htarget
  exact hfloor n han hn

private theorem hat_R_eq_global_at_quadrantRStageTime
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, R (hatCodes w h) m = R w (quadrantRStageTime w h m) := by
  intro m
  induction m with
  | zero =>
      have htime : quadrantRStageTime w h 0 = 0 :=
        quadrantRStageTime_eq_of_initial_R w h (by
          have hpos := (walkNL_spec w h 0).1
          rw [walkNR_zero] at hpos
          omega)
      simp [R, htime]
  | succ m ih =>
      rw [R_succ_hatBoundary (hatCodes w h) m, ih]
      by_cases hex : ∃ k, hatExitIndex w h k = m
      · obtain ⟨k, rfl⟩ := hex
        have htime0 :
            quadrantRStageTime w h (hatExitIndex w h k) = walkNL w h k - 1 :=
          quadrantRStageTime_hatExitIndex w h k
        have htime1 :
            quadrantRStageTime w h (hatExitIndex w h k + 1) =
              walkNR w h (k + 1) := by
          rw [← hatCodeTime_succ w h (hatExitIndex w h k),
            hatCodeTime_at_exit]
          have hpos := (walkNR_succ_spec w h k).1
          omega
        have hleft : R w (walkNL w h k) = R w (walkNL w h k - 1) := by
          have hidx : walkNL w h k - 1 + 1 = walkNL w h k := by
            have hgap := (walkNL_spec w h k).1
            omega
          calc
            R w (walkNL w h k) = R w (walkNL w h k - 1 + 1) :=
              congrArg (R w) hidx.symm
            _ = R w (walkNL w h k - 1) +
                (RandomWalk.lazyTwoDimensionalStep (w (walkNL w h k - 1))).2 :=
              R_succ_hatBoundary w (walkNL w h k - 1)
            _ = R w (walkNL w h k - 1) := by
              rw [walkNL_previous_code w h k]
              simp [RandomWalk.lazyTwoDimensionalStep]
        have hdrop :
            R w (walkNR w h (k + 1)) = R w (walkNL w h k - 1) - 1 := by
          rw [(walkNR_succ_spec w h k).2, hleft]
        rw [htime0, htime1, hatCodes_at_exit]
        change R w (walkNL w h k - 1) +
            (RandomWalk.lazyTwoDimensionalStep (2 : Fin 3)).2 =
          R w (walkNR w h (k + 1))
        rw [hdrop]
        rfl
      · have hnot : ¬ ∃ k, hatExitIndex w h k = m := hex
        have htimeCode :
            hatCodeTime w h m = quadrantRStageTime w h m :=
          hatCodeTime_of_not_exit w h m hnot
        have htimeNext :
            quadrantRStageTime w h (m + 1) =
              quadrantRStageTime w h m + 1 := by
          rw [← hatCodeTime_succ w h m, htimeCode]
        have hcode : hatCodes w h m = w (quadrantRStageTime w h m) := by
          rw [hatCodes, htimeCode]
        rw [htimeNext, hcode, R_succ_hatBoundary]

/-- The vertical coordinate of the hatted source walk is unbounded below.
The source-walk identity and the alignment of its selected times with
`quadrantRStageTime` identify it with the global vertical coordinate at those -/
theorem hat_R_unbounded_hatted (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ a : ℤ, ∃ m, R (hatCodes w h) m ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := R_unbounded_of_hasFlowLineHits w h a
  let τ := quadrantTrajectoryOfStageCodes w
  have hτ : HasFlowLineHits (fun i => τ (i + 1)) := by
    simpa [τ, quadrantTrajectoryOfStageCodes] using h
  obtain ⟨k, hright | hleft⟩ := flowLine_phase_partition w h n
  · let m := (RandomWalk.quadrantSplitState τ n).rCount
    have hbounds : ∃ j, walkNR (fun i => τ (i + 1)) hτ j ≤ n ∧
        n < walkNL (fun i => τ (i + 1)) hτ j := by
      refine ⟨k, ?_, ?_⟩
      · simpa [τ, quadrantTrajectoryOfStageCodes] using hright.1
      · simpa [τ, quadrantTrajectoryOfStageCodes] using hright.2
    have hphase : (RandomWalk.quadrantSplitState τ n).phase = .r :=
      (quadrantSplitState_rPhase_iff τ hτ n).2 hbounds
    have htime : quadrantRStageTime w h m = n := by
      exact (quadrantRStageCodes_RPhaseTime_unique w m n
        (quadrantRStageTime w h m) hphase rfl
        (quadrantRStageTime_spec w h m).1
        (quadrantRStageTime_spec w h m).2.1).symm
    exact ⟨m, by rw [hat_R_eq_global_at_quadrantRStageTime w h m, htime]; exact hn⟩
  · let m := hatExitIndex w h k + 1
    have htime : quadrantRStageTime w h m = walkNR w h (k + 1) := by
      dsimp [m]
      rw [← hatCodeTime_succ w h (hatExitIndex w h k), hatCodeTime_at_exit]
      have hpos := (walkNR_succ_spec w h k).1
      omega
    have hfirst : n < firstFlowRHit w h (walkNL w h k) := by
      simpa [walkNR, walkNL, flowLineTimes] using hleft.2
    have hfloor := R_floor_before_firstFlowRHit_hatBoundary w h
      (walkNL w h k) n hleft.1 hfirst
    have hrightCoord : R w (walkNR w h (k + 1)) ≤ R w n := by
      have hdrop := (walkNR_succ_spec w h k).2
      omega
    exact ⟨m, by
      rw [hat_R_eq_global_at_quadrantRStageTime w h m, htime]
      exact hrightCoord.trans hn⟩

/-- Every edge on the hatted upper-right boundary is eventually present.
Hatted-half helper for `lem-quad-kmsw` -/
theorem hat_UR_eventually_present (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m e : ℕ) (he : e ∈ (kmswStage (hatCodes w h) m).UR) :
    ∃ m', m ≤ m' ∧ (kmswStage (hatCodes w h) m').present e = true := by
  have heBound := hatUR_edge_lt_nextEdge w h m e he
  obtain ⟨j, hjBound, hjPresent⟩ :=
    hatLocal_allocated_edge_present w h m e heBound
  refine ⟨max m j, Nat.le_max_left _ _, ?_⟩
  exact (present_mono (hatCodes w h) hjBound hjPresent (max m j)
    (Nat.le_max_right _ _)).2

/-- No edge ID occurs on the hatted UR or LL boundaries at arbitrarily late
stages. This is the boundary reconciliation helper for the hatted half of -/
theorem hat_eventual_boundary (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ e, (∀ m₀, ∃ m ≥ m₀,
      e ∈ (kmswStage (hatCodes w h) m).UR ++ (kmswStage (hatCodes w h) m).LL) → False := by
  intro e hInf
  obtain ⟨m, _, hmem⟩ := hInf 0
  have hUR : e ∈ (kmswStage (hatCodes w h) m).UR := by
    simpa [hat_LL_nil w h m] using hmem
  have heBound := hatUR_edge_lt_nextEdge w h m e hUR
  obtain ⟨k, hmk, hkPresent⟩ := hat_UR_eventually_present w h m e hUR
  obtain ⟨n, hkn, hmemn⟩ := hInf k
  have hURn : e ∈ (kmswStage (hatCodes w h) n).UR := by
    simpa [hat_LL_nil w h n] using hmemn
  have hboundn := hatUR_edge_lt_nextEdge w h n e hURn
  have hpresentn : (kmswStage (hatCodes w h) n).present e = true :=
    (present_mono (hatCodes w h) (heBound.trans_le
      (kmswStage_nextEdge_mono (hatCodes w h) hmk)) hkPresent n hkn).2
  have hmissingn : (kmswStage (hatCodes w h) n).present e = false :=
    ((kmswStage_status (hatCodes w h) n).1 e hboundn).mpr (Or.inl hURn)
  rw [hmissingn] at hpresentn
  contradiction

/-- Each edge ID is eventually absent from the hatted UR and LL boundaries.
This is the positive eventual form of the boundary reconciliation helper for
the hatted half of `lem-quad-kmsw` -/
theorem hat_eventually_not_boundary (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ e, ∃ m₀, ∀ m ≥ m₀,
      e ∉ (kmswStage (hatCodes w h) m).UR ++ (kmswStage (hatCodes w h) m).LL := by
  classical
  intro e
  by_contra hh
  have hInf : ∀ m₀, ∃ m ≥ m₀,
      e ∈ (kmswStage (hatCodes w h) m).UR ++ (kmswStage (hatCodes w h) m).LL := by
    intro m₀
    have hno : ¬ ∀ m ≥ m₀,
        e ∉ (kmswStage (hatCodes w h) m).UR ++ (kmswStage (hatCodes w h) m).LL :=
      (not_exists.mp hh) m₀
    obtain ⟨m, hm⟩ := not_forall.mp hno
    obtain ⟨hle, hmem⟩ := not_imp.mp hm
    exact ⟨m, hle, not_not.mp hmem⟩
  exact hat_eventual_boundary w h e hInf

/-- The hatted dart map sends each west/east incident vertex to the image of
that same local vertex. The false side is the west (tail) side and the true
side is the east (head) side. Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_tail_head (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (d : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    (if (hatDartMap w h m d).2 then
      (kmswStage w (quadrantRStageTime w h m)).east (hatDartMap w h m d).1.val
     else (kmswStage w (quadrantRStageTime w h m)).west (hatDartMap w h m d).1.val) =
    hatAllVertexMap w h m
      (if d.2 then (kmswStage (hatCodes w h) m).east d.1.val
       else (kmswStage (hatCodes w h) m).west d.1.val) := by
  have hi := (hatAll_sim w h m).incidenceSim.incidence d.1.val d.1.isLt
  cases hs : d.2 <;> simp [hatDartMap, hs, hi]

/-- The hatted dart map preserves the side bit of every local dart -/
theorem hatDartMap_snd (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    (hatDartMap w h m d).2 = d.2 := rfl

end DirectedDistances.KMSW
