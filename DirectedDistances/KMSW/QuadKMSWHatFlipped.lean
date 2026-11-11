module

public import DirectedDistances.KMSW.QuadKMSWHatSim
import DirectedDistances.KMSW.FlowLineTimesIff
import DirectedDistances.KMSW.StageSubgraph

/-! # Exit-replaced codes for the partial M-hat simulation

Helpers for `lem-quad-kmsw`, `eqn-walk-quadrant`, and `eqn-quad-pre`
codes. At each exit we instead read the code arriving at the next R entry.
This is a partial M-hat simulation, not the full `lem-quad-kmsw`.
Identifying `hatCodes` with `rCodeSequence` needs `ZHatConverse`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open scoped Classical

/-- The raw R-code index of the last R state of phase `k` -/
@[expose] noncomputable def hatExitIndex (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) : ℕ :=
  (quadrantSplitState (quadrantTrajectoryOfStageCodes w) (walkNL w h k - 1)).rCount

private theorem exit_phase (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
      (walkNL w h k - 1)).phase = .r := by
  have hb := (walkNL_spec w h k).1
  apply (quadrantSplitState_rPhase_iff (quadrantTrajectoryOfStageCodes w) h _).2
  refine ⟨k, ?_, ?_⟩
  · change walkNR w h k ≤ walkNL w h k - 1
    omega
  · change walkNL w h k - 1 < walkNL w h k
    omega

/-- The canonical raw time at an exit index is the pre-exit state -/
theorem quadrantRStageTime_hatExitIndex (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageTime w h (hatExitIndex w h k) = walkNL w h k - 1 := by
  exact quadrantRStageCodes_RPhaseTime_unique w _ _ _
    (quadrantRStageTime_spec w h _).1 (quadrantRStageTime_spec w h _).2.1
    (exit_phase w h k) rfl

private theorem walkNL_strictMono_local (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    StrictMono (walkNL w h) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h₁ := (walkNR_succ_spec w h k).1
  have h₂ := (walkNL_spec w h (k + 1)).1
  omega

/-- Distinct phases have distinct exit-code indices, so replacing an exit
does not require an ambiguous choice (`eqn-quad-pre`, -/
theorem hatExitIndex_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (hatExitIndex w h) := by
  intro k l heq
  have ht := congrArg (quadrantRStageTime w h) heq
  rw [quadrantRStageTime_hatExitIndex, quadrantRStageTime_hatExitIndex] at ht
  have hk := (walkNL_spec w h k).1
  have hl := (walkNL_spec w h l).1
  exact (walkNL_strictMono_local w h).injective (by omega)

/-- The time map `T'`: replace the departing exit time by the time of the
code arriving at the next R entry (`eqn-walk-quadrant`, -/
@[expose] noncomputable def hatCodeTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : ℕ :=
  by
  classical
  exact if hex : ∃ k, hatExitIndex w h k = m then
    walkNR w h (Classical.choose hex + 1) - 1
  else quadrantRStageTime w h m

/-- The arriving-increment code stream, with exactly the departing exit
codes replaced (`eqn-walk-quadrant`, -/
@[expose] noncomputable def hatCodes (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : Fin 3 := w (hatCodeTime w h m)

/-- Off exit indices `T'` is the raw extraction time (`eqn-quad-pre`, -/
theorem hatCodeTime_of_not_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : ¬ ∃ k, hatExitIndex w h k = m) :
    hatCodeTime w h m = quadrantRStageTime w h m := by
  simp [hatCodeTime, hm]

/-- At an exit index `T'` reads the next re-entry code (`lem-flow-line-times`, -/
theorem hatCodeTime_at_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    hatCodeTime w h (hatExitIndex w h k) = walkNR w h (k + 1) - 1 := by
  have hex : ∃ l, hatExitIndex w h l = hatExitIndex w h k := ⟨k, rfl⟩
  have hchoose : Classical.choose hex = k :=
    hatExitIndex_injective w h (Classical.choose_spec hex)
  simp only [hatCodeTime, dite_eq_left hex, hchoose]

/-- Away from exits, the arriving stream agrees with the raw R stream -/
theorem hatCodes_of_not_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : ¬ ∃ k, hatExitIndex w h k = m) :
    hatCodes w h m = quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) m := by
  rw [hatCodes, hatCodeTime_of_not_exit w h m hm]
  exact (quadrantRStageTime_spec w h m).2.2.symm

/-- Each replaced exit reads code `2 = (1,-1)`, the single edge arriving at
re-entry (`lem-flow-line-times`, `lem-quad-kmsw`, -/
theorem hatCodes_at_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    hatCodes w h (hatExitIndex w h k) = 2 := by
  rw [hatCodes, hatCodeTime_at_exit]
  exact walkNR_succ_previous_code w h k

/-- At exactly an exit index the raw departing code `0` is replaced by `2`.
This is the time-side replacement formula; identifying its exit test with
the law-side strict-minimum test needs `ZHatConverse` -/
theorem hatCodes_pointwise (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    hatCodes w h m =
      if ∃ k, hatExitIndex w h k = m then 2
      else quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) m := by
  classical
  by_cases hex : ∃ k, hatExitIndex w h k = m
  · obtain ⟨k, rfl⟩ := hex
    rw [ite_eq_left ⟨k, rfl⟩]
    exact hatCodes_at_exit w h k
  · rw [ite_eq_right hex]
    exact hatCodes_of_not_exit w h m hex

/-- The raw value at each replaced index is `0`, as dictated by the last
departing R-state code (`eq:ref-for-lat-disc`, `eqn-quad-pre`, -/
theorem hatExitIndex_raw_code (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) (hatExitIndex w h k) = 0 := by
  rw [(quadrantRStageTime_spec w h _).2.2, quadrantRStageTime_hatExitIndex]
  exact walkNL_previous_code w h k

private theorem rStageTime_after_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) : quadrantRStageTime w h (hatExitIndex w h k + 1) = walkNR w h (k + 1) := by
  let ω := quadrantTrajectoryOfStageCodes w
  let n := walkNL w h k - 1
  have hpos := (walkNL_spec w h k).1
  have hgap := (walkNR_succ_spec w h k).1
  have hn : n + 1 = walkNL w h k := by dsimp [n]; omega
  have hc : (quadrantSplitState ω (walkNL w h k)).rCount = hatExitIndex w h k + 1 := by
    rw [← hn, quadrantSplitState, quadrantSplitAdvance_rCount]
    have hp : (quadrantSplitState ω n).phase = .r := exit_phase w h k
    rw [hp, ite_eq_left rfl]
    rfl
  have hL := quadrantSplit_rCount_at_LInterval w h k
    (walkNR w h (k + 1) - walkNL w h k) (by omega)
  have htime : walkNL w h k + (walkNR w h (k + 1) - walkNL w h k) =
      walkNR w h (k + 1) := by omega
  rw [htime] at hL
  have hcR : (quadrantSplitState ω (walkNR w h (k + 1))).rCount =
      hatExitIndex w h k + 1 := hL.trans hc
  have hpR : (quadrantSplitState ω (walkNR w h (k + 1))).phase = .r :=
    (quadrantSplitState_at_walkNR ω h (k + 1)).1
  exact quadrantRStageCodes_RPhaseTime_unique w _ _ _
    (quadrantRStageTime_spec w h _).1 (quadrantRStageTime_spec w h _).2.1 hpR hcR

/-- The replaced code arrives exactly at the next canonical R-state time.
This holds for every code index, including every exit; it fixes the stage
indexing but asserts no later-phase state simulation (`eqn-walk-quadrant`, -/
theorem hatCodeTime_succ (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    hatCodeTime w h m + 1 = quadrantRStageTime w h (m + 1) := by
  by_cases hex : ∃ k, hatExitIndex w h k = m
  · obtain ⟨k, rfl⟩ := hex
    rw [hatCodeTime_at_exit, rStageTime_after_exit]
    have hgap := (walkNR_succ_spec w h k).1
    omega
  · let ω := quadrantTrajectoryOfStageCodes w
    let n := quadrantRStageTime w h m
    have hs := quadrantRStageTime_spec w h m
    obtain ⟨k, hentry, hexit⟩ := (quadrantSplitState_rPhase_iff ω h n).1 hs.1
    change walkNR w h k ≤ n at hentry
    change n < walkNL w h k at hexit
    have hnext : n + 1 < walkNL w h k := by
      by_contra hnot
      have hlast : n = walkNL w h k - 1 := by omega
      apply hex
      refine ⟨k, ?_⟩
      change (quadrantSplitState ω (walkNL w h k - 1)).rCount = m
      rw [← hlast]
      exact hs.2.1
    have hp : (quadrantSplitState ω (n + 1)).phase = .r := by
      apply (quadrantSplitState_rPhase_iff ω h (n + 1)).2
      refine ⟨k, ?_, ?_⟩
      · change walkNR w h k ≤ n + 1
        omega
      · exact hnext
    have hc : (quadrantSplitState ω (n + 1)).rCount = m + 1 := by
      rw [quadrantSplitState, quadrantSplitAdvance_rCount]
      rw [hs.1, ite_eq_left rfl, hs.2.1]
    have heq := quadrantRStageCodes_RPhaseTime_unique w (m + 1)
      (quadrantRStageTime w h (m + 1)) (n + 1)
      (quadrantRStageTime_spec w h _).1 (quadrantRStageTime_spec w h _).2.1 hp hc
    rw [hatCodeTime_of_not_exit w h m hex, heq]

private theorem initial_count (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : m < walkNL w h 0) :
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w) m).rCount = m := by
  have hc := quadrantSplit_rCount_at_RInterval w h 0 m (by rw [walkNR_zero]; omega)
  simpa [walkNR_zero, quadrantSplitState, quadrantSplitStart] using hc

/-- The first exit code has index `walkNL 0 - 1`, with no shift in the -/
theorem hatExitIndex_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    hatExitIndex w h 0 = walkNL w h 0 - 1 := by
  have hp := (walkNL_spec w h 0).1
  exact initial_count w h (by omega)

private theorem no_exit_before_first (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : m < walkNL w h 0 - 1) :
    ¬ ∃ k, hatExitIndex w h k = m := by
  rintro ⟨k, hk⟩
  have ht := quadrantRStageTime_hatExitIndex w h k
  rw [hk, quadrantRStageTime_eq_of_initial_R w h (by omega)] at ht
  have hfirst := (walkNL_strictMono_local w h).monotone (Nat.zero_le k)
  omega

/-- Before the first replaced code, `T'` is identity (`eqn-quad-pre2`, -/
theorem hatCodeTime_initial (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : m < walkNL w h 0 - 1) : hatCodeTime w h m = m := by
  rw [hatCodeTime_of_not_exit w h m (no_exit_before_first w h hm)]
  exact quadrantRStageTime_eq_of_initial_R w h (by omega)

/-- The literal global code prefix is retained before the first exit code -/
theorem hatCodes_initial (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : m < walkNL w h 0 - 1) : hatCodes w h m = w m := by
  rw [hatCodes, hatCodeTime_initial w h hm]

private theorem stage_eq_prefix (u v : ℕ → Fin 3) :
    ∀ m, (∀ i < m, u i = v i) → kmswStage u m = kmswStage v m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro heq
      rw [kmswStage, kmswStage, ih (fun i hi => heq i (by omega)), heq m (by omega)]

/-- The hatted stage agrees with the global stage through the state just
before the first replaced code (`eqn-quad-pre2`, -/
theorem hatStage_initial (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : m ≤ walkNL w h 0 - 1) :
    kmswStage (hatCodes w h) m = kmswStage w m := by
  apply stage_eq_prefix
  intro i hi
  exact hatCodes_initial w h (by omega)

/-- Identity simulation for all codes strictly before the first exit index.
The first replaced code itself is not covered; this is a partial M-hat -/
theorem hatStage_identitySim_before_first_exit
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m : ℕ}
    (hm : m < walkNL w h 0 - 1) :
    Sim (kmswStage (hatCodes w h) (m + 1))
      (kmswStage w (hatCodeTime w h m + 1)) id id := by
  rw [hatCodeTime_initial w h hm, hatStage_initial w h (by omega)]
  have hs := quadrantFirstRStage_identitySim_through_exit w h (m := m + 1) (by omega)
  rw [quadrantFirstRStage_eq_through_exit w h (m := m + 1) (by omega)] at hs
  exact hs

/-- On the common initial stages, the identity edge map agrees with the
raw activation-time edge map (`eqn-quad-pre2`, -/
theorem hatStage_edgeMap_agrees_initial
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m : ℕ}
    (hm : m ≤ walkNL w h 0 - 1) (e : ℕ)
    (he : e < (kmswStage (hatCodes w h) m).nextEdge)
    (hp : (kmswStage (hatCodes w h) m).present e = true) :
    ∃ hr : EdgePresent (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) e,
      quadrantRStagePresentEdgeMap w h ⟨e, hr⟩ = id e := by
  have hpos := (walkNL_spec w h 0).1
  have hstage : kmswStage (hatCodes w h) m =
      kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m :=
    (hatStage_initial w h hm).trans
      (quadrantFirstRStage_eq_through_exit w h (by omega)).symm
  rw [hstage] at he hp
  exact ⟨⟨m, he, hp⟩,
    quadrantRStagePresentEdgeMap_eq_id_initial_R w h (by omega) e he hp⟩

open Quiver

private def hatPendingEastFrontier (s : State) : List ℕ :=
  s.east s.active :: s.UR.map s.east

private theorem hatPendingEastFrontier_left (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) :
    hatPendingEastFrontier (kmswStage w (n + 1)) =
      hatPendingEastFrontier (kmswStage w n) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hUR : t.UR = s.UR := by
    change (kmswStep s (w n)).UR = _
    rw [hc]
    cases hp : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
  have hEast : t.east t.active = s.east s.active := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
    rw [hc]
    cases hp : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
  have hmap : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
    have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) heBound).2
  change t.east t.active :: t.UR.map t.east =
    s.east s.active :: s.UR.map s.east
  rw [hEast, hUR, hmap]

private theorem hatPendingEastFrontier_up (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    hatPendingEastFrontier (kmswStage w (n + 1)) =
      (kmswStage w n).nextVertex :: hatPendingEastFrontier (kmswStage w n) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
    change (kmswStep s (w n)).UR = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep]
  have hEast : t.east t.active = s.nextVertex := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  have hNewEast : t.east (s.nextEdge + 1) = s.east s.active := by
    change (kmswStep s (w n)).east (s.nextEdge + 1) = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  have hmap : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
    have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) heBound).2
  change t.east t.active :: t.UR.map t.east =
    s.nextVertex :: s.east s.active :: s.UR.map s.east
  rw [hEast, hUR, List.map_cons, hNewEast, hmap]

private theorem hatPendingEastFrontier_down_cons (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (e : ℕ) (es : List ℕ)
    (hUR : (kmswStage w n).UR = e :: es) :
    hatPendingEastFrontier (kmswStage w n) =
      (kmswStage w n).east (act w n) ::
        hatPendingEastFrontier (kmswStage w (n + 1)) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  change s.UR = e :: es at hUR
  have hEast : t.east t.active = s.east e := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = s.east e
    rw [hc]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hUR' : t.UR = es := by
    change (kmswStep s (w n)).UR = es
    rw [hc]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hmap : es.map t.east = es.map s.east := by
    apply List.map_congr_left
    intro f hf
    have hfmem : f ∈ s.UR := by rw [hUR]; simp [hf]
    have hfAll : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr hfmem))
    have hfBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 f hfAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) hfBound).2
  change s.east s.active :: s.UR.map s.east =
    s.east s.active :: (t.east t.active :: t.UR.map t.east)
  rw [hUR, List.map_cons, hEast, hUR', hmap]

private theorem hatPendingEastFrontier_down_nil (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    hatPendingEastFrontier (kmswStage w (n + 1)) =
      [(kmswStage w n).nextVertex] := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  change t.east t.active :: t.UR.map t.east = _
  simp [t, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hc,
    hUR, State.addEdge]

private theorem hatPendingEastFrontier_balanced (w : ℕ → Fin 3) {t n : ℕ}
    (htn : t ≤ n)
    (habove : ∀ j, t ≤ j → j ≤ n → R w t ≤ R w j) :
    ∃ p : List ℕ,
      hatPendingEastFrontier (kmswStage w n) =
        p ++ hatPendingEastFrontier (kmswStage w t) ∧
      (p.length : ℤ) = R w n - R w t := by
  have haux : ∀ n, t ≤ n →
      (∀ j, t ≤ j → j ≤ n → R w t ≤ R w j) →
      ∃ p : List ℕ,
        hatPendingEastFrontier (kmswStage w n) =
          p ++ hatPendingEastFrontier (kmswStage w t) ∧
        (p.length : ℤ) = R w n - R w t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro htn hbound
        by_cases hEq : n = t
        · subst n
          refine ⟨[], ?_, ?_⟩
          · simp
          · simp [R]
        · have hnpos : 0 < n := by omega
          obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          have htq : t ≤ q := by omega
          have hboundq : ∀ j, t ≤ j → j ≤ q → R w t ≤ R w j := by
            intro j hjt hjq
            exact hbound j hjt (by omega)
          obtain ⟨p, hp, hplen⟩ := ih q (by omega) htq hboundq
          have hpost : R w t ≤ R w (q + 1) := hbound (q + 1) (by omega) le_rfl
          have hRstep : R w (q + 1) = R w q +
              (RandomWalk.lazyTwoDimensionalStep (w q)).2 := Finset.sum_range_succ _ _
          by_cases hc0 : w q = 0
          · have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = 0 := by
              simp [hc0, RandomWalk.lazyTwoDimensionalStep]
            have hpending := hatPendingEastFrontier_left w q hc0
            refine ⟨p, ?_, ?_⟩
            · simpa [hRstep, hcode] using hpending.trans hp
            · rw [hRstep, hcode]
              omega
          · by_cases hc1 : w q = 1
            · have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = 1 := by
                simp [hc1, RandomWalk.lazyTwoDimensionalStep]
              have hpending := hatPendingEastFrontier_up w q hc1
              refine ⟨(kmswStage w q).nextVertex :: p, ?_, ?_⟩
              · rw [hpending, hp]
                simp [List.cons_append]
              · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
                rw [hRstep, hcode]
                omega
            · have hc2 : w q = 2 := by
                apply Fin.ext
                have hval := (w q).isLt
                have hnot0 : (w q).val ≠ 0 := by
                  intro hv
                  exact hc0 (Fin.ext hv)
                have hnot1 : (w q).val ≠ 1 := by
                  intro hv
                  exact hc1 (Fin.ext hv)
                omega
              have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = -1 := by
                simp [hc2, RandomWalk.lazyTwoDimensionalStep]
              have hnet : 1 ≤ R w q - R w t := by
                rw [hRstep, hcode] at hpost
                omega
              have hpPos : 0 < p.length := by
                have : (0 : ℤ) < (p.length : ℤ) := by rw [hplen]; omega
                exact_mod_cast this
              have hpne : p ≠ [] := by
                intro he
                simp [he] at hpPos
              obtain ⟨a, ps, rfl⟩ := List.exists_cons_of_ne_nil hpne
              have hURne : (kmswStage w q).UR ≠ [] := by
                intro hUR
                have hlenOld : (hatPendingEastFrontier (kmswStage w q)).length = 1 := by
                  simp [hatPendingEastFrontier, hUR]
                have hbasePos : 0 <
                    (hatPendingEastFrontier (kmswStage w t)).length := by
                  simp [hatPendingEastFrontier]
                rw [hp] at hlenOld
                simp only [List.length_append, List.length_cons] at hlenOld
                omega
              obtain ⟨e, es, hUR⟩ : ∃ e es, (kmswStage w q).UR = e :: es := by
                cases h : (kmswStage w q).UR with
                | nil => exact (hURne h).elim
                | cons e es => exact ⟨e, es, rfl⟩
              have hpop := hatPendingEastFrontier_down_cons w q hc2 e es hUR
              have htail : ps ++ hatPendingEastFrontier (kmswStage w t) =
                  hatPendingEastFrontier (kmswStage w (q + 1)) := by
                have hcons : a :: (ps ++ hatPendingEastFrontier (kmswStage w t)) =
                    (kmswStage w q).east (act w q) ::
                      hatPendingEastFrontier (kmswStage w (q + 1)) := by
                  simpa [List.cons_append] using hp.symm.trans hpop
                exact congrArg List.tail hcons
              refine ⟨ps, htail.symm, ?_⟩
              simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hplen
              rw [hRstep, hcode]
              omega
  exact haux n htn habove


private theorem hatUR_balanced (w : ℕ → Fin 3) {t n : ℕ}
    (htn : t ≤ n) (habove : ∀ j, t ≤ j → j ≤ n → R w t ≤ R w j) :
    ∃ p : List ℕ, (kmswStage w n).UR = p ++ (kmswStage w t).UR ∧
      (p.length : ℤ) = R w n - R w t := by
  induction n, htn using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ n htn ih =>
    obtain ⟨p, hp, hlen⟩ := ih (fun j hj hjn => habove j hj (by omega))
    have hR : R w (n + 1) = R w n + (lazyTwoDimensionalStep (w n)).2 :=
      Finset.sum_range_succ _ _
    have hpost := habove (n + 1) (by omega) le_rfl
    by_cases h0 : w n = 0
    · refine ⟨p, ?_, ?_⟩
      · cases hpred : (kmswStage w n).UL.dropLast.reverse <;>
          simpa [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
            hpred, State.addEdge] using hp
      · simpa [hR, h0, lazyTwoDimensionalStep] using hlen
    · by_cases h1 : w n = 1
      · refine ⟨((kmswStage w n).nextEdge + 1) :: p, ?_, ?_⟩
        · simpa [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
            List.cons_append] using congrArg (List.cons ((kmswStage w n).nextEdge + 1)) hp
        · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          rw [hR, h1]
          simp only [lazyTwoDimensionalStep_one] at *
          omega
      · have h2 : w n = 2 := by
          have hb := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
          have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
          apply Fin.ext
          omega
        rw [h2, lazyTwoDimensionalStep_two] at hR
        have hpne : p ≠ [] := by
          intro hnil
          simp only [hnil, List.length_nil, Nat.cast_zero] at hlen
          omega
        obtain ⟨a, ps, rfl⟩ := List.exists_cons_of_ne_nil hpne
        refine ⟨ps, ?_, ?_⟩
        · simp [kmswStage, kmswStep, kmswCodeStep, h2, kmswStepOfStep,
            hp, List.cons_append]
        · simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen
          omega

private theorem hatR_floor (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k j : ℕ) (hj : walkNL w h k ≤ j) (hj' : j < walkNR w h (k + 1)) :
    R w (walkNL w h k) ≤ R w j := by
  let t := walkNL w h k
  have hhit : walkNR w h (k + 1) = firstFlowRHit w h t := rfl
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    have hprev := ih (by omega)
    have hs : R w (j + 1) = R w j + (lazyTwoDimensionalStep (w j)).2 :=
      Finset.sum_range_succ _ _
    have hlowerAll : ∀ c : Fin 3, -1 ≤ (lazyTwoDimensionalStep c).2 := by
      intro c
      fin_cases c <;> simp [lazyTwoDimensionalStep]
    have hlower := hlowerAll (w j)
    have hnot : R w (j + 1) ≠ R w t - 1 := by
      intro heq
      rw [hhit] at hj'
      exact (Nat.find_min (h.2 t) hj') ⟨by dsimp [t]; omega, heq⟩
    dsimp [t] at hnot
    omega

/-- its pre-exit stack and terminal vertex just before re-entry. This is a
boundary helper for the partial M-hat simulation (`lem-flow-line-times`, -/
theorem hatLPhase_right_boundary (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    (kmswStage w (walkNR w h (k + 1) - 1)).UR =
      (kmswStage w (walkNL w h k - 1)).UR ∧
    (kmswStage w (walkNR w h (k + 1) - 1)).east
        (kmswStage w (walkNR w h (k + 1) - 1)).active =
      (kmswStage w (walkNL w h k - 1)).east
        (kmswStage w (walkNL w h k - 1)).active := by
  let t := walkNL w h k
  let q := walkNR w h (k + 1) - 1
  have htpos := (walkNL_spec w h k).1
  have hgap := (walkNR_succ_spec w h k).1
  have htq : t ≤ q := by dsimp [t, q]; omega
  have hfloor : ∀ j, t ≤ j → j ≤ q → R w t ≤ R w j := by
    intro j hj hjq
    exact hatR_floor w h k j hj (by dsimp [q] at hjq; omega)
  have hlevel : R w q = R w t := by
    have hdelta := congrArg Prod.snd (walkNR_succ_previous_step w h k)
    have hhit := (walkNR_succ_spec w h k).2
    dsimp [q, t]
    omega
  obtain ⟨p, hp, hlen⟩ := hatUR_balanced w htq hfloor
  have hpzero : p = [] := by
    apply List.length_eq_zero_iff.mp
    rw [hlevel] at hlen
    omega
  have hUR : (kmswStage w q).UR = (kmswStage w t).UR := by
    simpa [hpzero] using hp
  obtain ⟨p', hp', hlen'⟩ := hatPendingEastFrontier_balanced w htq hfloor
  have hpzero' : p' = [] := by
    apply List.length_eq_zero_iff.mp
    rw [hlevel] at hlen'
    omega
  have heast : (kmswStage w q).east (kmswStage w q).active =
      (kmswStage w t).east (kmswStage w t).active := by
    have hh := congrArg List.head? hp'
    simpa [hatPendingEastFrontier, hpzero'] using hh
  have hcode := walkNL_previous_code w h k
  have htime : walkNL w h k - 1 + 1 = t := by dsimp [t]; omega
  have hURexit : (kmswStage w t).UR = (kmswStage w (t - 1)).UR := by
    rw [← htime]
    cases hpred : (kmswStage w (walkNL w h k - 1)).UL.dropLast.reverse <;>
      simp [kmswStage, kmswStep, kmswCodeStep, hcode, kmswStepOfStep,
        hpred, State.addEdge]
  have heastexit := hatPendingEastFrontier_left w (walkNL w h k - 1) hcode
  have hh := congrArg List.head? heastexit
  have heastexit' : (kmswStage w t).east (kmswStage w t).active =
      (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active := by
    simpa [hatPendingEastFrontier, htime, t] using hh
  exact ⟨hUR.trans hURexit, heast.trans heastexit'⟩

/-- The incidence and allocation part of `Sim`, retaining the UR prefix but
omitting the UL predecessor prefix. The UL stack can contain unreachable intervening predecessors
This relation alone is not an induction invariant for arbitrary future codes. -/
structure HatIncidenceSim (sh gl : State) (eφ vφ : ℕ → ℕ) : Prop where
  edge_bound : ∀ e, e < sh.nextEdge → eφ e < gl.nextEdge
  edge_injective : ∀ e f, e < sh.nextEdge → f < sh.nextEdge → eφ e = eφ f → e = f
  vertex_bound : ∀ v, v < sh.nextVertex → vφ v < gl.nextVertex
  vertex_injective : ∀ v z, v < sh.nextVertex → z < sh.nextVertex → vφ v = vφ z → v = z
  active : eφ sh.active = gl.active
  incidence : ∀ e, e < sh.nextEdge →
    gl.west (eφ e) = vφ (sh.west e) ∧ gl.east (eφ e) = vφ (sh.east e)
  present : ∀ e, e < sh.nextEdge → sh.present e = true → gl.present (eφ e) = true
  ur_prefix : List.map eφ sh.UR <+: gl.UR

/-- Explicit edge map across an L excursion: old IDs are retained; if the
local down step allocates, its fresh edge maps to the global fresh edge -/
@[expose] noncomputable def hatFirstExitEdgeMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ :=
  let sh := kmswStage w (walkNL w h 0 - 1)
  let gl := kmswStage w (walkNR w h 1 - 1)
  if sh.UR = [] then kmswShiftFreshEdgeMap sh gl id else id

/-- Explicit vertex map across the first L excursion, using the fresh global
vertex only when the local down step allocates (`lem-quad-kmsw`, -/
@[expose] noncomputable def hatFirstExitVertexMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ :=
  let sh := kmswStage w (walkNL w h 0 - 1)
  let gl := kmswStage w (walkNR w h 1 - 1)
  if sh.UR = [] then kmswShiftUpVertexMap sh gl id else id

private theorem hatFirstExit_incidence_nonempty
    (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hne : (kmswStage w (walkNL w h 0 - 1)).UR ≠ []) :
    HatIncidenceSim (kmswStep (kmswStage w (walkNL w h 0 - 1)) 2)
      (kmswStage w (walkNR w h 1)) id id := by
  let u := walkNL w h 0 - 1
  let q := walkNR w h 1 - 1
  let r := walkNR w h 1
  have hgap : walkNL w h 0 + 1 ≤ walkNR w h 1 := (walkNR_succ_spec w h 0).1
  have hpos := (walkNL_spec w h 0).1
  have hur : u ≤ r := by dsimp [u, r]; omega
  have hr : q + 1 = r := by dsimp [q, r]; omega
  have hcode : w q = 2 := walkNR_succ_previous_code w h 0
  obtain ⟨a, es, ha⟩ : ∃ a es, (kmswStage w u).UR = a :: es := by
    cases hx : (kmswStage w u).UR with
    | nil => exact (hne hx).elim
    | cons a es => exact ⟨a, es, rfl⟩
  have hqa : (kmswStage w q).UR = a :: es := (hatLPhase_right_boundary w h 0).1.trans ha
  have hrstage : kmswStage w r = kmswStepOfStep (kmswStage w q) .down := by
    rw [← hr]
    change kmswStep (kmswStage w q) (w q) = _
    rw [hcode]
    rfl
  have hactive : (kmswStage w r).active = a := by rw [hrstage]; simp [kmswStepOfStep, hqa]
  have hglpres : (kmswStage w r).present a = true := by
    rw [hrstage]; simp [kmswStepOfStep, hqa]
  change HatIncidenceSim (kmswStepOfStep (kmswStage w u) .down) (kmswStage w r) id id
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have he' : e < (kmswStage w u).nextEdge := by simpa [kmswStepOfStep, ha] using he
    exact he'.trans_le (kmswStage_nextEdge_mono w hur)
  · intro e f _ _ heq
    exact heq
  · intro v hv
    have hv' : v < (kmswStage w u).nextVertex := by simpa [kmswStepOfStep, ha] using hv
    exact hv'.trans_le (CutConverse.nextVertex_mono w hur)
  · intro v z _ _ heq
    exact heq
  · simpa [kmswStepOfStep, ha] using hactive.symm
  · intro e he
    have he' : e < (kmswStage w u).nextEdge := by simpa [kmswStepOfStep, ha] using he
    simpa [kmswStepOfStep, ha] using kmswStage_endpoints_stable w hur he'
  · intro e he hp
    by_cases hea : e = a
    · simpa [hea] using hglpres
    · have he' : e < (kmswStage w u).nextEdge := by simpa [kmswStepOfStep, ha] using he
      have hp' : (kmswStage w u).present e = true := by
        simpa [kmswStepOfStep, ha, hea] using hp
      exact (present_mono w he' hp' r hur).2
  · rw [hrstage]
    simp [kmswStepOfStep, ha, hqa]

private theorem hatFirstExit_incidence_empty
    (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hnil : (kmswStage w (walkNL w h 0 - 1)).UR = []) :
    HatIncidenceSim (kmswStep (kmswStage w (walkNL w h 0 - 1)) 2)
      (kmswStage w (walkNR w h 1))
      (hatFirstExitEdgeMap w h) (hatFirstExitVertexMap w h) := by
  let u := walkNL w h 0 - 1
  let q := walkNR w h 1 - 1
  let r := walkNR w h 1
  let sh := kmswStage w u
  let gl := kmswStage w q
  let ep := kmswShiftFreshEdgeMap sh gl id
  let vp := kmswShiftUpVertexMap sh gl id
  have hgap : walkNL w h 0 + 1 ≤ walkNR w h 1 := (walkNR_succ_spec w h 0).1
  have huq : u ≤ q := by dsimp [u, q]; omega
  have hur : u ≤ r := by dsimp [u, r]; omega
  have hr : q + 1 = r := by dsimp [q, r]; omega
  have hshUR : sh.UR = [] := hnil
  have hglUR : gl.UR = [] := (hatLPhase_right_boundary w h 0).1.trans hnil
  have hEast : gl.east gl.active = sh.east sh.active := (hatLPhase_right_boundary w h 0).2
  have hEdge : sh.nextEdge ≤ gl.nextEdge := kmswStage_nextEdge_mono w huq
  have hVertex : sh.nextVertex ≤ gl.nextVertex := CutConverse.nextVertex_mono w huq
  have hcode : w q = 2 := walkNR_succ_previous_code w h 0
  have hrstage : kmswStage w r = kmswStepOfStep gl .down := by
    rw [← hr]
    change kmswStep gl (w q) = _
    rw [hcode]
    rfl
  have hmapsE : hatFirstExitEdgeMap w h = ep := by
    simp [hatFirstExitEdgeMap, hnil, ep, sh, gl, u, q]
  have hmapsV : hatFirstExitVertexMap w h = vp := by
    simp [hatFirstExitVertexMap, hnil, vp, sh, gl, u, q]
  rw [hmapsE, hmapsV]
  change HatIncidenceSim (kmswStepOfStep sh .down) (kmswStage w r) ep vp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hshUR, State.addEdge] at he
      omega
    rcases hc with hold | rfl
    · have hne : e ≠ sh.nextEdge := by omega
      have hb := hold.trans_le (kmswStage_nextEdge_mono w hur)
      simpa [ep, kmswShiftFreshEdgeMap, hne] using hb
    · simp [ep, kmswShiftFreshEdgeMap, hrstage, kmswStepOfStep, hglUR, State.addEdge]

  · intro e f he hf heq
    have he' : e ≤ sh.nextEdge := by simpa [kmswStepOfStep, hshUR, State.addEdge] using he
    have hf' : f ≤ sh.nextEdge := by simpa [kmswStepOfStep, hshUR, State.addEdge] using hf
    by_cases hen : e = sh.nextEdge <;> by_cases hfn : f = sh.nextEdge
    · omega
    · simp [ep, kmswShiftFreshEdgeMap, hen, hfn] at heq
      omega
    · simp [ep, kmswShiftFreshEdgeMap, hen, hfn] at heq
      omega
    · simpa [ep, kmswShiftFreshEdgeMap, hen, hfn] using heq
  · intro v hv
    have hc : v < sh.nextVertex ∨ v = sh.nextVertex := by
      simp only [kmswStepOfStep, hshUR, State.addEdge] at hv
      omega
    rcases hc with hold | rfl
    · have hne : v ≠ sh.nextVertex := by omega
      have hb := hold.trans_le (CutConverse.nextVertex_mono w hur)
      simpa [vp, kmswShiftUpVertexMap, hne] using hb
    · simp [vp, kmswShiftUpVertexMap, hrstage, kmswStepOfStep, hglUR, State.addEdge]
  · intro v z hv hz heq
    have hv' : v ≤ sh.nextVertex := by simpa [kmswStepOfStep, hshUR, State.addEdge] using hv
    have hz' : z ≤ sh.nextVertex := by simpa [kmswStepOfStep, hshUR, State.addEdge] using hz
    by_cases hvn : v = sh.nextVertex <;> by_cases hzn : z = sh.nextVertex
    · omega
    · simp [vp, kmswShiftUpVertexMap, hvn, hzn] at heq
      omega
    · simp [vp, kmswShiftUpVertexMap, hvn, hzn] at heq
      omega
    · simpa [vp, kmswShiftUpVertexMap, hvn, hzn] using heq
  · simp [kmswStepOfStep, hshUR, hrstage, hglUR, ep, kmswShiftFreshEdgeMap]
  · intro e he
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hshUR, State.addEdge] at he
      omega
    rcases hc with hold | rfl
    · have hne : e ≠ sh.nextEdge := by omega
      have hends := kmswStage_endpoints_lt_nextVertex w u e hold
      have hw : sh.west e ≠ sh.nextVertex := by exact ne_of_lt hends.1
      have he' : sh.east e ≠ sh.nextVertex := by exact ne_of_lt hends.2
      simpa [ep, vp, kmswShiftFreshEdgeMap, kmswShiftUpVertexMap,
        kmswStepOfStep, hshUR, State.addEdge, hne, hw, he'] using
        kmswStage_endpoints_stable w hur hold
    · have hae := (kmswStage_endpoints_lt_nextVertex w u sh.active
        (act_lt_nextEdge w (Nat.le_refl u))).2
      have hvne : sh.east sh.active ≠ sh.nextVertex := ne_of_lt hae
      constructor
      · simpa [ep, vp, kmswShiftFreshEdgeMap, kmswShiftUpVertexMap,
          kmswStepOfStep, hshUR, hglUR, State.addEdge, hrstage, hvne] using hEast
      · simp [ep, vp, kmswShiftFreshEdgeMap, kmswShiftUpVertexMap,
          kmswStepOfStep, hshUR, hglUR, State.addEdge, hrstage]
  · intro e he hp
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hshUR, State.addEdge] at he
      omega
    rcases hc with hold | rfl
    · have hne : e ≠ sh.nextEdge := by omega
      have hp' : sh.present e = true := by
        simpa [kmswStepOfStep, hshUR, State.addEdge, hne] using hp
      simpa [ep, kmswShiftFreshEdgeMap, hne] using (present_mono w hold hp' r hur).2
    · simp [ep, kmswShiftFreshEdgeMap, hrstage, kmswStepOfStep, hglUR, State.addEdge]
  · simp [kmswStepOfStep, hshUR, State.addEdge]

/-- At the first exit index, the replaced down code embeds into the global
stage after the entire first L-phase, with explicit maps and all incidence,
allocation, presence, and UR-prefix fields. The UL predecessor prefix is not claimed. Together
with `hatStage_identitySim_before_first_exit` this covers every code through
the first exit. This is partial M-hat simulation, not `lem-quad-kmsw`;
identification with `rCodeSequence` still needs `ZHatConverse` -/
theorem hatStage_incidenceSim_first_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    HatIncidenceSim (kmswStage (hatCodes w h) (hatExitIndex w h 0 + 1))
      (kmswStage w (hatCodeTime w h (hatExitIndex w h 0) + 1))
      (hatFirstExitEdgeMap w h) (hatFirstExitVertexMap w h) := by
  have hgap : walkNL w h 0 + 1 ≤ walkNR w h 1 := (walkNR_succ_spec w h 0).1
  have hidx : walkNR w h 1 - 1 + 1 = walkNR w h 1 := by omega
  rw [hatCodeTime_at_exit, hidx, kmswStage, hatCodes_at_exit, hatExitIndex_zero,
    hatStage_initial w h le_rfl]
  by_cases hnil : (kmswStage w (walkNL w h 0 - 1)).UR = []
  · exact hatFirstExit_incidence_empty w h hnil
  · have hmE : hatFirstExitEdgeMap w h = id := by simp [hatFirstExitEdgeMap, hnil]
    have hmV : hatFirstExitVertexMap w h = id := by simp [hatFirstExitVertexMap, hnil]
    rw [hmE, hmV]
    exact hatFirstExit_incidence_nonempty w h hnil

/-- The first-exit edge map retains every edge allocated before the replaced
code, so it continues the identity map already identified with
`quadrantRStagePresentEdgeMap` (`lem-quad-kmsw`, -/
theorem hatFirstExitEdgeMap_old (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (e : ℕ) (he : e < (kmswStage w (walkNL w h 0 - 1)).nextEdge) :
    hatFirstExitEdgeMap w h e = e := by
  have hne : e ≠ (kmswStage w (walkNL w h 0 - 1)).nextEdge := ne_of_lt he
  unfold hatFirstExitEdgeMap
  split
  · simp [kmswShiftFreshEdgeMap, hne]
  · rfl

/-- Across every L-phase, the reachable present-edge set changes only by
adjoining the re-entry active edge (`lem-flow-line-times`, `lem-quad-kmsw`,
not a general phase-`k` incidence simulation. -/
theorem hatLPhase_reachablePresentEdges (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) :
    stageReachablePresentEdges w (walkNR w h (k + 1)) =
      stageReachablePresentEdges w (walkNL w h k - 1) ∪
        {act w (walkNR w h (k + 1))} := by
  have hgap := (walkNR_succ_spec w h k).1
  rw [lPhase_reentry_reachablePresentEdges,
    lPhase_reachablePresentEdges_eq w h k (walkNR w h (k + 1) - 1)
      (by omega) (by omega), rPhase_exit_reachablePresentEdges]

/-- A concrete obstruction to continuing the identity-based `Sim` through
an exit and re-entry. For the finite global prefix `[0,2]`, the local down
step has predecessor `[0]`, while the global re-entry has predecessor `[1]`.
Thus any edge map retaining the old root violates `ul_predecessors_prefix`.
This is a finite helper for the partial M-hat simulation, not the full -/
theorem hatFirstExit_Sim_obstruction (w : ℕ → Fin 3)
    (h0 : w 0 = 0) (h1 : w 1 = 2) (eφ vφ : ℕ → ℕ) (he0 : eφ 0 = 0) :
    ¬ Sim (kmswStage (fun _ => 2) 1) (kmswStage w 2) eφ vφ := by
  intro hs
  have hprefix := hs.ul_predecessors_prefix
  simp [kmswStage, kmswInit, kmswStep, kmswCodeStep, kmswStepOfStep,
    State.addEdge, h0, h1, he0] at hprefix

end DirectedDistances.KMSW
