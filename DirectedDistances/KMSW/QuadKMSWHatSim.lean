/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.QuadKMSWHatGeneral
public import DirectedDistances.KMSW.PhaseTimesBridge
import DirectedDistances.KMSW.OutgoingInterval
import DirectedDistances.KMSW.FlowLineTimesIff
import DirectedDistances.KMSW.StageSubgraph

/-! # Finite simulations for extracted R-phase KMSW runs

The initial R-phase state simulation is identity-valued through its exit
stage. At every later R-stage, the activation-time map on present edges is
injective and has image exactly the global reachable-present part. This map
does not cover missing allocated edges; a full vertex map with incidence
compatibility is not established here. References for extracted-code
indexing and reachability are -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open Quiver

/-- Equal finite states support the identity simulation with the stack-prefix
conditions from `KMSWShiftEmbedding.Sim`. -/
private theorem identitySim_of_eq {s t : State} (h : s = t) :
    Sim s t id id := by
  subst t
  refine {
    edge_bound := ?_
    edge_injective := ?_
    vertex_bound := ?_
    vertex_injective := ?_
    active := ?_
    incidence := ?_
    present := ?_
    ur_prefix := ?_
    ul_predecessors_prefix := ?_ }
  · intro e he
    exact he
  · intro e f _ _ hef
    exact hef
  · intro v hv
    exact hv
  · intro v z _ _ hvz
    exact hvz
  · rfl
  · intro e _
    exact ⟨rfl, rfl⟩
  · intro e _ hp
    exact hp
  · simp
  · simp

/-- The extracted R-stream stage embeds by identity into the global stage up
to and including the first R-phase exit stage (`eqn-quad-pre`, -/
theorem quadrantFirstRStage_identitySim_through_exit
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m : ℕ}
    (hm : m ≤ walkNL w h 0) :
    Sim (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m)
      (kmswStage w m) id id := by
  apply identitySim_of_eq
  exact quadrantFirstRStage_eq_through_exit w h hm

private theorem quadrantSplit_rCount_at_walkNR_ge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    ∀ k, k ≤
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (walkNR w h k)).rCount := by
  intro k
  induction k with
  | zero => simp [walkNR_zero, quadrantSplitState, quadrantSplitStart]
  | succ k ih =>
      let tR := walkNR w h k
      let tL := walkNL w h k
      let tR' := walkNR w h (k + 1)
      have hRgap : tR + 1 ≤ tL := by
        simpa [tR, tL] using (walkNL_spec w h k).1
      have hLgap : tL + 1 ≤ tR' := by
        simpa [tL, tR'] using (walkNR_succ_spec w h k).1
      have hR := quadrantSplit_rCount_at_RInterval w h k (tL - tR) (by omega)
      have hRtime : tR + (tL - tR) = tL := by omega
      rw [hRtime] at hR
      have hL := quadrantSplit_rCount_at_LInterval w h k (tR' - tL) (by omega)
      have hLtime : tL + (tR' - tL) = tR' := by omega
      rw [hLtime] at hL
      have hgap : 1 ≤ tL - tR := by omega
      dsimp [tR, tL, tR'] at *
      calc
        k + 1 ≤
            (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
              (walkNR w h k)).rCount + 1 := by omega
        _ ≤
            (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
              (walkNR w h k)).rCount + (walkNL w h k - walkNR w h k) := by omega
        _ =
            (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
              (walkNR w h (k + 1))).rCount := by
            exact hR.symm.trans hL.symm

/-- Every index of the extracted R-code stream occurs at a global time in an
R-phase. At that time its splitter counter is the index and its code is the
locates the stage to be simulated but does not itself construct its state
embedding. -/
theorem quadrantRStageCodes_has_RPhaseTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    ∃ n,
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .r ∧
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).rCount = m ∧
      quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) m = w n := by
  classical
  let ω := quadrantTrajectoryOfStageCodes w
  let r := fun n => (quadrantSplitState ω n).rCount
  have hlarge : m + 1 ≤ r (walkNR w h (m + 1)) := by
    have hb := quadrantSplit_rCount_at_walkNR_ge w h (m + 1)
    simpa [r] using hb
  have hex : ∃ n, m < r n := ⟨walkNR w h (m + 1), by omega⟩
  let t := Nat.find hex
  have ht : m < r t := Nat.find_spec hex
  have hmin : ∀ j, j < t → ¬ m < r j := by
    intro j hj
    exact Nat.find_min hex hj
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    have hzero : r t = 0 := by simp [r, ω, htzero, quadrantSplitState,
      quadrantSplitStart]
    omega
  let n := t - 1
  have hnext : n + 1 = t := by dsimp [n]; omega
  have hprev_le : r n ≤ m := by
    by_contra hnot
    have hgt : m < r n := by omega
    have hbad := hmin n (by omega)
    exact hbad hgt
  have hupper : r (n + 1) ≤ r n + 1 := by
    dsimp [r]
    rw [quadrantSplitState, quadrantSplitAdvance_rCount]
    split <;> omega
  have hcurr_gt : m < r (n + 1) := by rw [hnext]; exact ht
  have hcurr : r (n + 1) = m + 1 := by omega
  have hprev : r n = m := by omega
  have hstep :
      r (n + 1) = if (quadrantSplitState ω n).phase = .r then r n + 1 else r n := by
    dsimp [r]
    rw [quadrantSplitState, quadrantSplitAdvance_rCount]
  rw [hcurr, hprev] at hstep
  have hphase : (quadrantSplitState ω n).phase = .r := by
    by_cases hp : (quadrantSplitState ω n).phase = .r
    · exact hp
    · simp [hp] at hstep
  have hω : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa [ω, quadrantTrajectoryOfStageCodes] using h
  obtain ⟨k, hnEntry, hnExit⟩ :=
    (quadrantSplitState_rPhase_iff ω hω n).mp hphase
  have hcode := quadrantRStageCodes_at_RPhaseTime w h k n hnEntry hnExit
  have hcount : (quadrantSplitState ω n).rCount = m := by
    simpa [r, ω] using hprev
  rw [hcount] at hcode
  exact ⟨n, by simpa [ω] using hphase, by simpa [ω] using hcount, hcode⟩

private theorem quadrantSplit_rCount_strict_after_R
    (ω : ℕ → Fin 3) {n n' : ℕ}
    (hphase : (quadrantSplitState ω n).phase = .r) (hlt : n < n') :
    (quadrantSplitState ω n).rCount < (quadrantSplitState ω n').rCount := by
  have hstep : (quadrantSplitState ω (n + 1)).rCount =
      (quadrantSplitState ω n).rCount + 1 := by
    simp [quadrantSplitState, quadrantSplitAdvance_rCount, hphase]
  have hmono := quadrantSplitState_rCount_mono ω (n + 1) n'
    (Nat.succ_le_of_lt hlt)
  rw [hstep] at hmono
  omega

/-- An extracted R-code index has at most one global time in an R-phase:
the R counter increases at every step from an R state onward -/
theorem quadrantRStageCodes_RPhaseTime_unique
    (w : ℕ → Fin 3) (m n₁ n₂ : ℕ)
    (hphase₁ :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n₁).phase = .r)
    (hcount₁ :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n₁).rCount = m)
    (hphase₂ :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n₂).phase = .r)
    (hcount₂ :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n₂).rCount = m) :
    n₁ = n₂ := by
  by_contra hne
  by_cases hlt : n₁ < n₂
  · have hstrict := quadrantSplit_rCount_strict_after_R
      (quadrantTrajectoryOfStageCodes w) hphase₁ hlt
    rw [hcount₁, hcount₂] at hstrict
    omega
  · have hlt' : n₂ < n₁ := by omega
    have hstrict := quadrantSplit_rCount_strict_after_R
      (quadrantTrajectoryOfStageCodes w) hphase₂ hlt'
    rw [hcount₂, hcount₁] at hstrict
    omega

/-- The unique global time in an R-phase whose splitter counter is `m`,
whose existence and uniqueness are proved above. -/
@[expose] noncomputable def quadrantRStageTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : ℕ :=
  Classical.choose (quadrantRStageCodes_has_RPhaseTime w h m)

/-- The selected R-phase time has counter `m` and reads the corresponding -/
theorem quadrantRStageTime_spec (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
      (quadrantRStageTime w h m)).phase = .r ∧
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
      (quadrantRStageTime w h m)).rCount = m ∧
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) m =
      w (quadrantRStageTime w h m) :=
  Classical.choose_spec (quadrantRStageCodes_has_RPhaseTime w h m)

/-- On the initial R interval, the canonical time is the original stage -/
theorem quadrantRStageTime_eq_of_initial_R (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : m < walkNL w h 0) :
    quadrantRStageTime w h m = m := by
  have hω : HasFlowLineHits
      (fun i => quadrantTrajectoryOfStageCodes w (i + 1)) := by
    simpa [quadrantTrajectoryOfStageCodes] using h
  have hphase :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) m).phase = .r :=
    (quadrantSplitState_rPhase_iff (quadrantTrajectoryOfStageCodes w) hω m).2
      ⟨0, by simp [walkNR_zero], hm⟩
  have hcount := quadrantSplit_rCount_at_RInterval w h 0 m (by
    rw [walkNR_zero]
    omega)
  have hcount' :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) m).rCount = m := by
    simpa [walkNR_zero, quadrantSplitState, quadrantSplitStart] using hcount
  exact quadrantRStageCodes_RPhaseTime_unique w m
    (quadrantRStageTime w h m) m
    (quadrantRStageTime_spec w h m).1
    (quadrantRStageTime_spec w h m).2.1 hphase hcount'

/-- The canonical R-phase times increase with their extracted code index. -/
theorem quadrantRStageTime_mono (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    quadrantRStageTime w h m₁ ≤ quadrantRStageTime w h m₂ := by
  by_contra hnot
  have hlt : quadrantRStageTime w h m₂ < quadrantRStageTime w h m₁ := by omega
  have hstrict := quadrantSplit_rCount_strict_after_R
    (quadrantTrajectoryOfStageCodes w)
    (quadrantRStageTime_spec w h m₂).1 hlt
  rw [(quadrantRStageTime_spec w h m₂).2.1,
    (quadrantRStageTime_spec w h m₁).2.1] at hstrict
  omega

/-- Map a present local edge by its unique activation index to the global
active edge at the corresponding R-phase time. The domain is the subtype of
edges present in the extracted limit graph. -/
@[expose] noncomputable def quadrantRStagePresentEdgeMap
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    {e : ℕ // EdgePresent
      (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) e} → ℕ :=
  fun e => act w (quadrantRStageTime w h
    (actTime (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w))
      e.val e.property))

/-- The edge map sends each local active edge to the global active edge at
the unique R-phase time with the same code index. -/
theorem quadrantRStagePresentEdgeMap_active
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    quadrantRStagePresentEdgeMap w h
        ⟨act (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m,
          ⟨m,
            act_lt_nextEdge
              (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) le_rfl,
            kmswStage_active_present
              (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m⟩⟩ =
      act w (quadrantRStageTime w h m) := by
  let u := quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
  have hp : EdgePresent u (act u m) :=
    ⟨m, act_lt_nextEdge u le_rfl, kmswStage_active_present u m⟩
  have ht : actTime u (act u m) hp = m :=
    (actTime_eq_iff u (act u m) hp m).2 rfl
  change act w (quadrantRStageTime w h (actTime u (act u m) hp)) = _
  rw [ht]

private theorem stageReachablePresentEdges_eq_reachableActiveImage
    (w : ℕ → Fin 3) (n : ℕ) :
    stageReachablePresentEdges w n =
      {e | ∃ j ≤ n, e = act w j ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w j).west (act w j)⟩} := by
  ext e
  constructor
  · intro he
    obtain ⟨j, hj, hje⟩ := stagePresent_exists_active w n e he.1 he.2.1
    have hstable := kmswStage_endpoints_stable w (m := j) (n := n)
      (e := act w j) hj
      (act_lt_nextEdge w (le_rfl : j ≤ j))
    subst e
    refine ⟨j, hj, rfl, ?_⟩
    rw [← hstable.1]
    exact he.2.2.1
  · rintro ⟨j, hj, rfl, hwest⟩
    have hbaseBound := act_lt_nextEdge w (le_rfl : j ≤ j)
    have hbasePresent := kmswStage_active_present w j
    have hmono := present_mono w (n := j) (e := act w j)
      hbaseBound hbasePresent n hj
    have hstable := kmswStage_endpoints_stable w (m := j) (n := n)
      (e := act w j) hj hbaseBound
    have hwest' : Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).west (act w j)⟩ := by
      rw [hstable.1]
      exact hwest
    have heast := kmswStage_activeEast_reachable w j hwest
    have heast' : Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).east (act w j)⟩ := by
      rw [hstable.2]
      exact heast
    exact ⟨hmono.1, hmono.2, hwest', heast'⟩

private theorem stageReachablePresentEdges_at_RStageTime
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    stageReachablePresentEdges w (quadrantRStageTime w h m) =
      {e | ∃ j ≤ m, e = act w (quadrantRStageTime w h j)} := by
  have hω : HasFlowLineHits
      (fun i => quadrantTrajectoryOfStageCodes w (i + 1)) := by
    simpa [quadrantTrajectoryOfStageCodes] using h
  rw [stageReachablePresentEdges_eq_reachableActiveImage]
  ext e
  constructor
  · rintro ⟨t, htn, hte, hwest⟩
    obtain ⟨k, hkEntry, hkExit⟩ := (flowLineTimes_iff w h t).mp hwest
    have hphase :=
      (quadrantSplitState_rPhase_iff (quadrantTrajectoryOfStageCodes w) hω t).2
        ⟨k, hkEntry, hkExit⟩
    let j :=
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) t).rCount
    have hjcount :
        (quadrantSplitState (quadrantTrajectoryOfStageCodes w) t).rCount = j := rfl
    have hspecj := quadrantRStageTime_spec w h j
    have htimeEq := quadrantRStageCodes_RPhaseTime_unique w j t
      (quadrantRStageTime w h j) hphase hjcount hspecj.1 hspecj.2.1
    have hcountMono := quadrantSplitState_rCount_mono
      (quadrantTrajectoryOfStageCodes w) t (quadrantRStageTime w h m) htn
    have hjle : j ≤ m := by
      rw [hjcount, (quadrantRStageTime_spec w h m).2.1] at hcountMono
      exact hcountMono
    refine ⟨j, hjle, ?_⟩
    rw [← htimeEq]
    exact hte
  · rintro ⟨j, hjm, rfl⟩
    have htmono := quadrantRStageTime_mono w h hjm
    have hspecj := quadrantRStageTime_spec w h j
    obtain ⟨k, hkEntry, hkExit⟩ :=
      (quadrantSplitState_rPhase_iff (quadrantTrajectoryOfStageCodes w) hω
        (quadrantRStageTime w h j)).mp hspecj.1
    have hwest := flowLine_phase_reachable w h k
      (quadrantRStageTime w h j) hkEntry hkExit
    exact ⟨quadrantRStageTime w h j, htmono, rfl, hwest⟩

/-- The activation-time edge map sends the present edges of every extracted
R-stage onto exactly the global reachable-present edges at its canonical
R-phase time. This is the edge-image part of the desired simulation; vertex
maps and incidence compatibility are not established here. -/
theorem quadrantRStagePresentEdgeMap_image_eq_reachable
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    {e | ∃ f : {f : ℕ // EdgePresent
        (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) f},
      f.val < (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m).nextEdge ∧
      (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m).present f.val = true ∧
      quadrantRStagePresentEdgeMap w h f = e} =
      stageReachablePresentEdges w (quadrantRStageTime w h m) := by
  let u := quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
  have hset := stageReachablePresentEdges_at_RStageTime w h m
  ext e
  constructor
  · rintro ⟨f, hf, hp, hmap⟩
    obtain ⟨j, hjm, hfj⟩ := stagePresent_exists_active u m f.val hf hp
    have hActPresent : EdgePresent u (act u j) :=
      ⟨j, act_lt_nextEdge u le_rfl, kmswStage_active_present u j⟩
    have hsub : f = ⟨act u j, hActPresent⟩ := Subtype.ext hfj
    have hactiveMap := quadrantRStagePresentEdgeMap_active w h j
    have hmapActive : quadrantRStagePresentEdgeMap w h f =
        act w (quadrantRStageTime w h j) := by
      rw [hsub]
      exact hactiveMap
    have he : e = act w (quadrantRStageTime w h j) := hmap.symm.trans hmapActive
    rw [hset]
    exact ⟨j, hjm, he⟩
  · intro he
    rw [hset] at he
    obtain ⟨j, hjm, he⟩ := he
    have hbaseBound := act_lt_nextEdge u (le_rfl : j ≤ j)
    have hbasePresent := kmswStage_active_present u j
    have hstage := present_mono u (n := j) (e := act u j)
      hbaseBound hbasePresent m hjm
    have hActPresent : EdgePresent u (act u j) :=
      ⟨j, hbaseBound, hbasePresent⟩
    refine ⟨⟨act u j, hActPresent⟩, hstage.1, hstage.2, ?_⟩
    rw [quadrantRStagePresentEdgeMap_active]
    exact he.symm

/-- The activation-time edge map is injective on all edges present in the
extracted limit graph. -/
theorem quadrantRStagePresentEdgeMap_injective
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (quadrantRStagePresentEdgeMap w h) := by
  intro f g hmap
  let u := quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
  obtain ⟨mf, hmfBound, hmfPresent⟩ := f.property
  obtain ⟨mg, hmgBound, hmgPresent⟩ := g.property
  obtain ⟨j, hjm, hfj⟩ :=
    stagePresent_exists_active u mf f.val hmfBound hmfPresent
  obtain ⟨k, hkm, hgk⟩ :=
    stagePresent_exists_active u mg g.val hmgBound hmgPresent
  have hpj : EdgePresent u (act u j) :=
    ⟨j, act_lt_nextEdge u le_rfl, kmswStage_active_present u j⟩
  have hpk : EdgePresent u (act u k) :=
    ⟨k, act_lt_nextEdge u le_rfl, kmswStage_active_present u k⟩
  have hsubF : f = ⟨act u j, hpj⟩ := Subtype.ext hfj
  have hsubG : g = ⟨act u k, hpk⟩ := Subtype.ext hgk
  have hmapF : quadrantRStagePresentEdgeMap w h f =
      act w (quadrantRStageTime w h j) := by
    rw [hsubF]
    exact quadrantRStagePresentEdgeMap_active w h j
  have hmapG : quadrantRStagePresentEdgeMap w h g =
      act w (quadrantRStageTime w h k) := by
    rw [hsubG]
    exact quadrantRStagePresentEdgeMap_active w h k
  have hact : act w (quadrantRStageTime w h j) =
      act w (quadrantRStageTime w h k) := hmapF.symm.trans (hmap.trans hmapG)
  have htime : quadrantRStageTime w h j = quadrantRStageTime w h k :=
    CutConverse.act_injective w hact
  have hjk : j = k := by
    have hc := congrArg
      (fun t => (quadrantSplitState (quadrantTrajectoryOfStageCodes w) t).rCount)
      htime
    rw [(quadrantRStageTime_spec w h j).2.1,
      (quadrantRStageTime_spec w h k).2.1] at hc
    exact hc
  apply Subtype.ext
  calc
    f.val = act u j := hfj
    _ = act u k := by rw [hjk]
    _ = g.val := hgk.symm

/-- Before the first R-phase exit, the activation-time edge map reduces to
the identity map on the extracted stage's present edges. -/
theorem quadrantRStagePresentEdgeMap_eq_id_initial_R
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m : ℕ}
    (hm : m < walkNL w h 0) (e : ℕ)
    (he : e < (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m).nextEdge)
    (hp : (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m).present e = true) :
    quadrantRStagePresentEdgeMap w h
      ⟨e, ⟨m, he, hp⟩⟩ = e := by
  let u := quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
  obtain ⟨j, hjm, hje⟩ := stagePresent_exists_active u m e he hp
  have hjExit : j < walkNL w h 0 := hjm.trans_lt hm
  have hStage := quadrantFirstRStage_eq_through_exit w h (Nat.le_of_lt hjExit)
  have hTime := quadrantRStageTime_eq_of_initial_R w h hjExit
  have hActive : act u j = act w j := by
    change (kmswStage u j).active = (kmswStage w j).active
    rw [hStage]
  have hActPresent : EdgePresent u (act u j) :=
    ⟨j, act_lt_nextEdge u le_rfl, kmswStage_active_present u j⟩
  have hsub : (⟨e, ⟨m, he, hp⟩⟩ : {f : ℕ // EdgePresent u f}) =
      ⟨act u j, hActPresent⟩ := Subtype.ext hje
  calc
    quadrantRStagePresentEdgeMap w h ⟨e, ⟨m, he, hp⟩⟩ =
        quadrantRStagePresentEdgeMap w h ⟨act u j, hActPresent⟩ := by rw [hsub]
    _ = act w (quadrantRStageTime w h j) := quadrantRStagePresentEdgeMap_active w h j
    _ = act w j := by rw [hTime]
    _ = e := by rw [← hActive]; exact hje.symm

/-- At every canonical extracted R-stage time, the global active edge belongs
to the reachable-present part (`lem-flow-line-times`, -/
theorem quadrantRStageTime_active_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    act w (quadrantRStageTime w h m) ∈
      stageReachablePresentEdges w (quadrantRStageTime w h m) := by
  have hω : HasFlowLineHits
      (fun i => quadrantTrajectoryOfStageCodes w (i + 1)) := by
    simpa [quadrantTrajectoryOfStageCodes] using h
  obtain ⟨k, hnEntry, hnExit⟩ :=
    (quadrantSplitState_rPhase_iff (quadrantTrajectoryOfStageCodes w) hω
      (quadrantRStageTime w h m)).mp (quadrantRStageTime_spec w h m).1
  have hwest := flowLine_phase_reachable w h k (quadrantRStageTime w h m)
    hnEntry hnExit
  change act w (quadrantRStageTime w h m) < _ ∧
    (kmswStage w (quadrantRStageTime w h m)).present
      (act w (quadrantRStageTime w h m)) = true ∧
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (quadrantRStageTime w h m)).west
        (act w (quadrantRStageTime w h m))⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (quadrantRStageTime w h m)).east
        (act w (quadrantRStageTime w h m))⟩
  exact ⟨act_lt_nextEdge w le_rfl,
    kmswStage_active_present w (quadrantRStageTime w h m), hwest,
    kmswStage_activeEast_reachable w (quadrantRStageTime w h m) hwest⟩

/-- During the initial R-phase, the identity-simulated active edge belongs to
the global reachable-present set (`lem-flow-line-times`, -/
theorem quadrantFirstRStage_activeImage_reachable
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m : ℕ}
    (hm : m < walkNL w h 0) :
    act (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m = act w m ∧
      act w m ∈ stageReachablePresentEdges w m := by
  have hstage := quadrantFirstRStage_eq_through_exit w h (Nat.le_of_lt hm)
  have hwest := flowLine_phase_reachable w h 0 m (by simp [walkNR_zero]) hm
  constructor
  · change (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m).active =
      (kmswStage w m).active
    rw [hstage]
  · change act w m < (kmswStage w m).nextEdge ∧
      (kmswStage w m).present (act w m) = true ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w m).west (act w m)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w m).east (act w m)⟩
    exact ⟨act_lt_nextEdge w le_rfl, kmswStage_active_present w m, hwest,
      kmswStage_activeEast_reachable w m hwest⟩

/-- At the first R-phase exit, the active edge is present but its west endpoint
is not reachable, so it is outside `stageReachablePresentEdges` despite the
identity stage equality through the exit boundary. (`lem-flow-line-times`, -/
theorem quadrantFirstRStage_exit_active_not_reachable
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (kmswStage w (walkNL w h 0)).present (act w (walkNL w h 0)) = true ∧
      act w (walkNL w h 0) ∉ stageReachablePresentEdges w (walkNL w h 0) := by
  constructor
  · exact kmswStage_active_present w (walkNL w h 0)
  · intro hmem
    have hwest := (walkNL_activeWest_unreachable w h 0)
    exact hwest hmem.2.2.1

private theorem quadrantFirstRStage_presentEndpoints_reachable
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m e : ℕ}
    (hm : m < walkNL w h 0)
    (he : e < (kmswStage w m).nextEdge)
    (hp : (kmswStage w m).present e = true) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w m).west e⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w m).east e⟩ := by
  obtain ⟨j, hjm, hje⟩ := stagePresent_exists_active w m e he hp
  have hjexit : j < walkNL w h 0 := hjm.trans_lt hm
  have hwest := flowLine_phase_reachable w h 0 j (by simp [walkNR_zero]) hjexit
  have heast := kmswStage_activeEast_reachable w j hwest
  have hstable := kmswStage_endpoints_stable w hjm
    (act_lt_nextEdge w (le_rfl : j ≤ j))
  rw [hje, hstable.1, hstable.2]
  exact ⟨hwest, heast⟩

/-- Through the strict first R-phase interval, the image under the identity
edge map of the extracted stage's present edges is exactly the global
reachable-present edge set (`lem-flow-line-times`,
does not extend through the exit: there the active edge is present but is not
in the reachable-present set. -/
theorem quadrantFirstRStage_presentImage_eq_reachable
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m : ℕ}
    (hm : m < walkNL w h 0) :
    {e | ∃ f,
      f < (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m).nextEdge ∧
      (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m).present f = true ∧
      id f = e} = stageReachablePresentEdges w m := by
  have hstage := quadrantFirstRStage_eq_through_exit w h (Nat.le_of_lt hm)
  ext e
  constructor
  · rintro ⟨f, hf, hp, hfe⟩
    have hfe' : f = e := by simpa using hfe
    subst e
    have he : f < (kmswStage w m).nextEdge := by rw [← hstage]; exact hf
    have hp' : (kmswStage w m).present f = true := by rw [← hstage]; exact hp
    obtain ⟨hwest, heast⟩ :=
      quadrantFirstRStage_presentEndpoints_reachable w h hm he hp'
    exact ⟨he, hp', hwest, heast⟩
  · intro he
    refine ⟨e, ?_, ?_, ?_⟩
    · rw [hstage]
      exact he.1
    · rw [hstage]
      exact he.2.1
    · rfl

end DirectedDistances.KMSW
