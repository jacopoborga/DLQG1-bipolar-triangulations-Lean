/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundaryOrder4

/-! The corrected attachment uses the actual primed side flip. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ}

/-- Helper toward Lemma 5.5: the stopped prefix starts at the attachment
vertex, with the prescribed default also covering the empty segment. -/
theorem lPlusPrefixUpperLeftDarts_head_endpoint :
    ((lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)).head?.map
      (kmswDartEndpoint (shiftedStream W 0))).getD
        (boundaryVertex (shiftedStream W 0) h k) =
      boundaryVertex (shiftedStream W 0) h k := by
  rw [lPlusPrefixUpperLeftDarts_eq]
  cases hs : (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.reverse with
  | nil => rfl
  | cons e es =>
    change edgeEast (shiftedStream W 0) e = _
    exact lPlusPrefixUpperLeftDarts_first_starts_at_xk hs

/-- Helper toward Lemma 5.5: the initial left exit in the future stream
is its first negative boundary hit. -/
private theorem lPlus_primed_initial_exit_eq_hit
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    walkNL (boundaryGluingFutureStream W h k) hτ 0 =
      boundaryHitTime (boundaryGluingFutureStream W h k)
        (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) (-1) := by
  classical
  let u := boundaryGluingFutureStream W h k
  let hb := hatBoundaryHitWitnesses u hτ
  have hz : L u 0 = 0 := rfl
  have hs := walkNL_spec u hτ 0
  rw [walkNR_zero, hz] at hs
  have ht := boundaryHitTime_left_spec u hb (k := -1) (by omega)
  have hp : 1 ≤ boundaryHitTime u hb (-1) := by
    by_contra hn
    have he : boundaryHitTime u hb (-1) = 0 := by omega
    rw [he, hz] at ht
    contradiction
  have hf : walkNL u hτ 0 = Nat.find (hτ.1 0) := rfl
  have hbfind : boundaryHitTime u hb (-1) =
      Nat.find (hb.leftHit (-1) (by omega)) := by
    simp only [boundaryHitTime, dite_eq_right (by omega : (-1 : ℤ) ≠ 0),
      dite_eq_right (by omega : ¬ (0 : ℤ) < -1)]
  apply Nat.le_antisymm
  · rw [hf]
    exact Nat.find_min' (hτ.1 0) ⟨hp, by rw [hz]; exact ht⟩
  · rw [hbfind]
    exact Nat.find_min' (hb.leftHit (-1) (by omega)) hs.2

/-- Helper toward Lemma 5.5: the primed root traversal starts at the
attachment vertex, including when the stopped prefix is empty. -/
theorem lPlus_primed_root_starts_at_xk
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    boundaryGluingPrimedVertexMap W h k hτ
      (kmswDartEndpoint
        (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
        (0, true)) = boundaryVertex (shiftedStream W 0) h k := by
  let u := boundaryGluingFutureStream W h k
  let hb := hatBoundaryHitWitnesses u hτ
  have h1 := (primedLimit_maps_eq_of_allocated u hτ 0).2 1
    (show 1 < 2 from by omega)
  change primedLimitVertexMap u hτ 1 =
    (kmswStage u (walkNL u hτ 0)).east
      (kmswLLCreatedEdge u (walkNL u hτ 0)) at h1
  rw [lPlus_primed_initial_exit_eq_hit hτ] at h1
  have hv : primedLimitVertexMap u hτ 1 = 0 :=
    h1.trans (boundaryVertex_left_root_missing_edge u hb).2.1
  change boundaryGluingFutureVertexMap W h k (primedLimitVertexMap u hτ 1) = _
  rw [hv]
  exact boundaryGluingFutureVertexMap_zero W h k

open DirectedDistances.RandomWalk
open scoped Classical
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open Quiver MeasureTheory ProbabilityTheory Filter
open scoped Classical

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The lower-left stack changes only at a fresh left step. -/
private theorem lPlus_attachment_LL_step (s : State) (c : Fin 3) :
    (kmswStep s c).LL =
      if c = 0 ∧ s.UL.dropLast.reverse = [] then
        (s.nextEdge + 1) :: s.LL else s.LL := by
  fin_cases c
  · cases hp : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
  · simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  · cases hp : s.UR <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A reachable active west endpoint rules out creation of a missing left edge. -/
private theorem lPlus_attachment_LL_step_of_reachable (w : ℕ → Fin 3) (n : ℕ)
    (hr : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩) :
    (kmswStage w (n + 1)).LL = (kmswStage w n).LL := by
  change (kmswStep (kmswStage w n) (w n)).LL = _
  rw [lPlus_attachment_LL_step]
  apply ite_eq_right
  rintro ⟨hc, hp⟩
  have hm := (mem_stageReachableVertices_iff w (n + 1) _).mpr
    ((actReachableBefore_activeWest_iff w (n + 1)).mpr hr)
  have hh := (stageReachableVertices_left_activeWest_iff w n hc).mp hm
  rw [hp] at hh
  exact hh

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The lower-left list is unchanged throughout a right phase before its exit. -/
private theorem lPlus_attachment_LL_right_phase (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k a b : ℕ) (hab : a ≤ b) (ha : walkNR w h k ≤ a + 1)
    (hb : b < walkNL w h k) :
    (kmswStage w b).LL = (kmswStage w a).LL := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [lPlus_attachment_LL_step_of_reachable w b
      (flowLine_phase_reachable w h k (b + 1) (by omega) hb)]
    exact ih (by omega)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
At the initial left exit the sole ambient LL edge is the retained primed root. -/
private theorem lPlus_attachment_LL_initial (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (kmswStage w (walkNL w h 0)).LL =
      [kmswLLCreatedEdge w (walkNL w h 0)] := by
  let t := walkNL w h 0
  have ht : 0 < t := by
    have hh := (walkNL_spec w h 0).1
    rw [walkNR_zero] at hh
    exact hh
  have hold : (kmswStage w (t - 1)).LL = [] :=
    lPlus_attachment_LL_right_phase w h 0 0 (t - 1) (by omega)
      (by rw [walkNR_zero]; omega) (by omega)
  have hp := (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have hs := primedInitial_globalExitTransition w h
  change kmswStage w t = kmswStep (kmswStage w (t - 1)) 0 at hs
  change (kmswStage w (t - 1)).UL.dropLast.reverse = [] at hp
  rw [hs, lPlus_attachment_LL_step, ite_eq_left ⟨rfl, hp⟩, hold]
  congr 1
  change _ = (kmswStage w t).nextEdge - 1
  rw [hs]
  simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Later compressed crossing steps skip no lower-left boundary edges. -/
private theorem lPlus_attachment_LL_crossing (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    (kmswStage w (walkNL w h (k + 1))).LL =
      (kmswStage w (walkNR w h (k + 1) - 1)).LL := by
  let t := walkNL w h (k + 1)
  have ht := (walkNL_spec w h (k + 1)).1
  have hr := (walkNR_succ_spec w h k).1
  have hp := primedCrossing_exit_predecessor_nonempty w h (k + 1) (by omega)
  have hs : kmswStage w t = kmswStep (kmswStage w (t - 1)) 0 := by
    have he : t - 1 + 1 = t := by dsimp [t]; omega
    conv_lhs => rw [← he]
    change kmswStep _ (w (t - 1)) = _
    exact congrArg (kmswStep (kmswStage w (t - 1)))
      (walkNL_previous_code w h (k + 1))
  rw [hs, lPlus_attachment_LL_step, ite_eq_right (by rintro ⟨_, hh⟩; exact hp hh)]
  exact lPlus_attachment_LL_right_phase w h (k + 1) _ _ (by dsimp [t]; omega)
    (by omega) (by dsimp [t]; omega)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Ordinary compressed steps retain the same raw code and advance raw time by one. -/
private theorem lPlus_attachment_ordinary_alignment (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)) :
    primedStageTime w h (m + 1) = primedStageTime w h m + 1 ∧
      primedCode (primedSimInput w) h m = w (primedStageTime w h m) := by
  let k := primedIntervalIndex (primedSimInput w) h (m - 1)
  have hr : m ≤ primedIntervalBase (primedSimInput w) h (k + 1) := by
    have hi := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
    change m - 1 < primedIntervalBase (primedSimInput w) h (k + 1) at hi
    omega
  have hl : primedIntervalBase (primedSimInput w) h k < m := by
    cases hk : k with
    | zero => rw [primedIntervalBase_zero]; omega
    | succ j =>
      have hh := Nat.find_min
        (primedIntervalIndex_exists (primedSimInput w) h (m - 1))
        (show j < Nat.find
          (primedIntervalIndex_exists (primedSimInput w) h (m - 1)) by
          change j < k; omega)
      change ¬ m - 1 < primedIntervalBase (primedSimInput w) h (j + 1) at hh
      omega
  change m < primedIntervalBase (primedSimInput w) h (k + 1) at ho
  have ht0 := primedStageTime_block w h k m hl hr
  have ht1 := primedStageTime_block w h k (m + 1) (by omega) (by omega)
  constructor
  · rw [ht0, ht1]
    omega
  · have hc := primedCode_positive_offset (primedSimInput w) h k
      (m - primedIntervalBase (primedSimInput w) h k) (by omega) (by
        rw [primedIntervalBase_succ] at ho
        omega)
    have he : primedIntervalBase (primedSimInput w) h k +
        (m - primedIntervalBase (primedSimInput w) h k) = m := by omega
    rw [he] at hc
    change primedCode (primedSimInput w) h m =
      w (walkNL w h k + (m - primedIntervalBase (primedSimInput w) h k) - 1) at hc
    rwa [← ht0] at hc

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A fresh ordinary LL endpoint has the same ordered ambient west endpoint. -/
private theorem lPlus_attachment_fresh_west (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1))
    (hc : primedCode (primedSimInput w) h m = 0)
    (hp : (kmswStage (primedCode (primedSimInput w) h) m).UL.dropLast.reverse = []) :
    primedLimitVertexMap w h
        (edgeWest (primedCode (primedSimInput w) h)
          ((kmswStage (primedCode (primedSimInput w) h) m).nextEdge + 1)) =
      edgeWest w ((kmswStage w (primedStageTime w h m)).nextEdge + 1) := by
  let u := primedCode (primedSimInput w) h
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (primedStageTime w h m)
  have ha := kmswMissingRootStage_agree u m
  change u m = 0 at hc
  have hp' : sh.UL.dropLast.reverse = [] := by
    change (kmswMissingRootStage u m).UL.dropLast.reverse = []
    rw [ha.2.2.2.2.2.2.2.1]
    exact hp
  obtain ⟨_, hs, _⟩ := primedAll_sim w h m (by omega)
  have hgp : gl.UL.dropLast.reverse = [] := by
    have hh := hs.forget.left_predecessors
    change sh.UL.dropLast.reverse.map _ = gl.UL.dropLast.reverse at hh
    rw [hp', List.map_nil] at hh
    exact hh.symm
  have hgc : w (primedStageTime w h m) = 0 :=
    (lPlus_attachment_ordinary_alignment w h m hm ho).2.symm.trans hc
  change u m = 0 at hc
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    change kmswStep sh (u m) = _
    rw [hc]
    rfl
  have hg : kmswStage w (primedStageTime w h m + 1) =
      kmswStepOfStep gl .left := by
    change kmswStep gl (w (primedStageTime w h m)) = _
    rw [hgc]
    rfl
  have hv : sh.nextVertex < (kmswMissingRootStage u (m + 1)).nextVertex := by
    rw [hl]
    simp only [kmswStepOfStep, hp', State.addEdge]
    omega
  have he : sh.nextEdge + 1 < (kmswStage u (m + 1)).nextEdge := by
    rw [← (kmswMissingRootStage_agree u (m + 1)).2.1, hl]
    simp only [kmswStepOfStep, hp', State.addEdge]
    omega
  have hw : edgeWest u (sh.nextEdge + 1) = sh.nextVertex := by
    rw [← (edge_endpoints_eq u he).1,
      ← (kmswMissingRootStage_agree u (m + 1)).2.2.1, hl]
    simp [kmswStepOfStep, hp', State.addEdge]
  have hge : gl.nextEdge + 1 <
      (kmswStage w (primedStageTime w h m + 1)).nextEdge := by
    rw [hg]
    simp only [kmswStepOfStep, hgp, State.addEdge]
    omega
  rw [← ha.2.1, hw, (primedLimit_maps_eq_of_allocated w h (m + 1)).2 _ hv]
  simp only [primedAllVertexMap, hm, ↓reduceIte, ho]
  change primedOrdinaryStepVertexMap sh gl (u m) _ sh.nextVertex = _
  rw [hc]
  simp only [primedOrdinaryStepVertexMap, ↓reduceIte, primedOrdinaryLeftVertexMap,
    hp', kmswShiftUpVertexMap]
  rw [← (edge_endpoints_eq w hge).1, hg]
  simp [kmswStepOfStep, hgp, State.addEdge]

/-- Helper toward Lemma 5.5: a fresh ordinary missing left edge has the
same edge identity under the primed embedding. -/
private theorem lPlus_attachment_fresh_edge (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1))
    (hc : primedCode (primedSimInput w) h m = 0)
    (hp : (kmswStage (primedCode (primedSimInput w) h) m).UL.dropLast.reverse = []) :
    primedLimitEdgeMap w h
        ((kmswStage (primedCode (primedSimInput w) h) m).nextEdge + 1) =
      (kmswStage w (primedStageTime w h m)).nextEdge + 1 := by
  let u := primedCode (primedSimInput w) h
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (primedStageTime w h m)
  have ha := kmswMissingRootStage_agree u m
  change u m = 0 at hc
  have hp' : sh.UL.dropLast.reverse = [] := by
    rw [ha.2.2.2.2.2.2.2.1]
    exact hp
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    change kmswStep sh (u m) = _
    rw [hc]
    rfl
  have he : sh.nextEdge + 1 < (kmswMissingRootStage u (m + 1)).nextEdge := by
    rw [hl]
    simp only [kmswStepOfStep, hp', State.addEdge]
    omega
  rw [← ha.2.1, (primedLimit_maps_eq_of_allocated w h (m + 1)).1 _ he]
  simp only [primedAllEdgeMap, hm, ↓reduceIte, ho]
  change primedOrdinaryStepEdgeMap sh gl (u m) _ (sh.nextEdge + 1) = _
  rw [hc]
  change primedOrdinaryLeftEdgeMap sh gl _ (sh.nextEdge + 1) = _
  rw [primedOrdinaryLeftEdgeMap, ite_eq_left hp']
  simp only [kmswShiftUpEdgeMap, Nat.add_one_ne_self, ↓reduceIte]
  rfl

/-- Helper toward Lemma 5.5: adjoining the retained root gives exactly
the future LL list, preserving edge identity, west endpoint, and list order. -/
theorem lPlus_primed_LL_edge_west_list (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) :
    (kmswStage (primedCode (primedSimInput w) h) m).LL.map
        (fun e => (primedLimitEdgeMap w h e, primedLimitVertexMap w h
          (edgeWest (primedCode (primedSimInput w) h) e))) ++
        [(primedLimitEdgeMap w h 0, primedLimitVertexMap w h 0)] =
      (kmswStage w (primedStageTime w h m)).LL.map
        (fun e => (e, edgeWest w e)) := by
  let u := primedCode (primedSimInput w) h
  have hroot : (primedLimitEdgeMap w h 0, primedLimitVertexMap w h 0) =
      (kmswLLCreatedEdge w (walkNL w h 0),
        edgeWest w (kmswLLCreatedEdge w (walkNL w h 0))) := by
    rw [primedRootVertex_matches_rootEdge, primedLimitEdgeMap_zero]
  induction m with
  | zero =>
    rw [primedStageTime_zero, lPlus_attachment_LL_initial]
    exact congrArg (fun x => [x]) hroot
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      have ht := primedStageTime_after_crossing w h 0
      rw [primedIntervalBase_zero, zero_add] at ht
      rw [ht, lPlus_attachment_LL_initial]
      have hc : u 0 = 1 := primedCode_zero (primedSimInput w) h
      change (kmswStep (kmswStage u 0) (u 0)).LL.map _ ++ _ = _
      rw [hc, lPlus_attachment_LL_step, ite_eq_right (by rintro ⟨hh, _⟩; cases hh)]
      exact congrArg (fun x => [x]) hroot
    · by_cases ho : m < primedIntervalBase (primedSimInput w) h
          (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)
      · obtain ⟨ht, hc⟩ := lPlus_attachment_ordinary_alignment w h m hm ho
        rw [ht]
        change (kmswStep (kmswStage u m) (u m)).LL.map _ ++ _ =
          (kmswStep (kmswStage w (primedStageTime w h m))
            (w (primedStageTime w h m))).LL.map _
        rw [← hc, lPlus_attachment_LL_step, lPlus_attachment_LL_step]
        obtain ⟨_, hs, _⟩ := primedAll_sim w h m (by omega)
        have hp : (kmswStage u m).UL.dropLast.reverse = [] ↔
            (kmswStage w (primedStageTime w h m)).UL.dropLast.reverse = [] := by
          have hh := hs.forget.left_predecessors
          change (kmswMissingRootStage u m).UL.dropLast.reverse.map _ = _ at hh
          rw [(kmswMissingRootStage_agree u m).2.2.2.2.2.2.2.1] at hh
          exact (List.map_eq_nil_iff).symm.trans (Iff.of_eq (congrArg (· = []) hh))
        by_cases hf : u m = 0 ∧ (kmswStage u m).UL.dropLast.reverse = []
        · rw [ite_eq_left hf, ite_eq_left ⟨hf.1, hp.mp hf.2⟩]
          simp only [List.map_cons, List.cons_append]
          rw [lPlus_attachment_fresh_edge w h m hm ho hf.1 hf.2,
            lPlus_attachment_fresh_west w h m hm ho hf.1 hf.2, ih]
        · rw [ite_eq_right hf, ite_eq_right (by
            rintro ⟨hc', hp'⟩; exact hf ⟨hc', hp.mpr hp'⟩)]
          exact ih
      · let k := primedIntervalIndex (primedSimInput w) h (m - 1)
        have hr := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
        have hB : m = primedIntervalBase (primedSimInput w) h (k + 1) := by
          change m - 1 < primedIntervalBase (primedSimInput w) h (k + 1) at hr
          change ¬ m < primedIntervalBase (primedSimInput w) h (k + 1) at ho
          omega
        have hc : u m = 1 := by rw [hB]; exact (primedCrossing_codes w h k).1
        have ht := primedStageTime_after_crossing w h (k + 1)
        rw [← hB] at ht
        rw [ht, lPlus_attachment_LL_crossing, ← primedStageTime_at_crossing w h k, ← hB]
        change (kmswStep (kmswStage u m) (u m)).LL.map _ ++ _ = _
        rw [hc, lPlus_attachment_LL_step, ite_eq_right (by rintro ⟨hh, _⟩; cases hh)]
        exact ih

/-- Helper toward Lemma 5.5: the independent primed root/LL word maps
to the complete future LL word in its original order, with corrected bits. -/
theorem lPlus_primed_LL_dart_word (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) :
    (0 :: (kmswStage (primedCode (primedSimInput w) h) m).LL.reverse).map
        (fun e => primedLimitDartMap w h (e, true)) =
      (kmswStage w (primedStageTime w h m)).LL.reverse.map
        (fun e => (e, true)) := by
  let u := primedCode (primedSimInput w) h
  have hp := lPlus_primed_LL_edge_west_list w h m
  have hedge := congrArg (List.map Prod.fst) hp
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def] at hedge
  have hrev := congrArg List.reverse hedge
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, ← List.map_reverse, List.singleton_append] at hrev
  have hword : (0 :: (kmswStage u m).LL.reverse).map (primedLimitEdgeMap w h) =
      (kmswStage w (primedStageTime w h m)).LL.reverse := by
    simpa only [List.map_cons, List.map_id'] using hrev
  have hbit (e : ℕ) (he : e ∈ 0 :: (kmswStage u m).LL.reverse) :
      primedLimitSideFlip w h e = false := by
    have hm : (primedLimitEdgeMap w h e, primedLimitVertexMap w h (edgeWest u e)) ∈
        (kmswStage w (primedStageTime w h m)).LL.map (fun f => (f, edgeWest w f)) := by
      rw [← hp]
      rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _
          (List.mem_map.mpr ⟨e, List.mem_reverse.mp he, rfl⟩)
    obtain ⟨f, _, hf⟩ := List.mem_map.mp hm
    have hv : primedLimitVertexMap w h (edgeWest u e) =
        edgeWest w (primedLimitEdgeMap w h e) := by
      have heq := congrArg Prod.fst hf
      have hveq := congrArg Prod.snd hf
      dsimp only at heq hveq
      exact hveq.symm.trans (congrArg (edgeWest w) heq)
    change decide (primedLimitVertexMap w h (edgeWest u e) ≠
      edgeWest w (primedLimitEdgeMap w h e)) = false
    simp only [hv, ne_eq, not_true_eq_false, decide_false]
  calc
    _ = (0 :: (kmswStage u m).LL.reverse).map
        (fun e => (primedLimitEdgeMap w h e, true)) := by
      apply List.map_congr_left
      intro e he
      simp only [primedLimitDartMap, hbit e he, Bool.xor_false]
    _ = ((0 :: (kmswStage u m).LL.reverse).map (primedLimitEdgeMap w h)).map
        (fun e => (e, true)) := by rw [List.map_map]; rfl
    _ = _ := by rw [hword]

/-- Helper toward Lemma 5.5: at a sufficiently late compressed stage,
the future LL list starts with the stopped upper-left edges in reverse order. -/
theorem lPlus_prefix_future_LL_initial_segment
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    ∃ m : ℕ,
      ((kmswStage (boundaryGluingFutureStream W h k)
        (primedStageTime (boundaryGluingFutureStream W h k) hτ m)).LL.reverse.take
          (kmswStage (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.length).map
        (boundaryGluingEdgeMap W h k) =
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.reverse := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let G0 := kmswStage w t
  let hb := hatBoundaryHitWitnesses u hτ
  obtain ⟨l, hl⟩ := hb.leftHit (-((G0.UL.length : ℤ) + 1)) (by omega)
  let m := primedIntervalBase (primedSimInput u) hτ (l + 1)
  let n := primedStageTime u hτ m
  have hNR (j : ℕ) : j ≤ walkNR u hτ j := by
    induction j with
    | zero => rw [walkNR_zero]
    | succ j ih =>
      have hL := (walkNL_spec u hτ j).1
      have hR := (walkNR_succ_spec u hτ j).1
      omega
  have hn : l ≤ n := by
    dsimp only [n, m]
    rw [primedStageTime_at_crossing]
    have hh := hNR (l + 1)
    omega
  let F := kmswStage u n
  let d := kmswWindowPatchData w t n
  have hr := kmswWindowPatchData_rel w t n
  change KMSWWindowPatchRel G0 _ F d.φ d.A d.B d.YL d.YR d.XL d.XR at hr
  have hllen := kmswStage_LL_length u n
  have hmin := runningMin_le (L u) n l hn
  change minL u n ≤ L u l at hmin
  have hA : d.A = [] := by
    by_contra ha
    have hxl := hr.xl_nil ha
    have hs := congrArg List.length hr.ll_split
    have ht := congrArg List.length hr.left_residual
    simp only [List.length_append, List.length_map, List.length_dropLast] at ht hs
    rw [hxl] at hs
    simp only [List.length_nil] at hs
    change ((F.LL.length : ℤ)) = _ at hllen
    omega
  have hres : G0.UL.dropLast = d.YL.map d.φ := by
    simpa only [hA, List.nil_append] using hr.left_residual
  have hlen : G0.UL.dropLast.length = d.YL.length := by
    rw [hres, List.length_map]
  have htake : F.LL.reverse.take G0.UL.dropLast.length = d.YL.reverse := by
    rw [hr.ll_split, List.reverse_append, hlen]
    rw [← (List.length_reverse (as := d.YL)), List.take_left]
  refine ⟨m, ?_⟩
  change (F.LL.reverse.take G0.UL.dropLast.length).map
    (boundaryGluingEdgeMap W h k) = G0.UL.dropLast.reverse
  rw [htake, hres, ← List.map_reverse]
  apply List.map_congr_left
  intro e he
  have heF : e ∈ F.LL := by
    rw [hr.ll_split]
    exact List.mem_append_right _ (List.mem_reverse.mp he)
  have heb : e < F.nextEdge := (kmswStageFrontierChain_all u n).LL_missing_bounded e heF |>.2
  exact kmswWindowEdgeMapInf_eq_stage w t n e heb

/-- Helper toward Lemma 5.5: the independent primed root/LL initial
segment is exactly the ordered prefix under the corrected dart embedding. -/
theorem lPlus_prefix_primed_ordered_dart_image
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    let u := primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
    let p := lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)
    ∃ m : ℕ,
      (((0 :: (kmswStage u m).LL.reverse).take p.length).map
        (fun e => (e, true))).map (lMinusPrimedDartImage hτ) = p := by
  let v := boundaryGluingFutureStream W h k
  let u := primedCode (primedSimInput v) hτ
  let p := lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)
  obtain ⟨m, hm⟩ := lPlus_prefix_future_LL_initial_segment hτ
  refine ⟨m, ?_⟩
  have hlen : p.length = (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.length := by
    dsimp only [p]
    rw [lPlusPrefixUpperLeftDarts_eq, List.length_map, List.length_reverse]
  have hw := congrArg
    (List.map (fun d : ℕ × Bool => (boundaryGluingEdgeMap W h k d.1, d.2)))
    (lPlus_primed_LL_dart_word v hτ m)
  have hw' : (0 :: (kmswStage u m).LL.reverse).map
      (fun e => lMinusPrimedDartImage hτ (e, true)) =
      (kmswStage v (primedStageTime v hτ m)).LL.reverse.map
        (fun e => (boundaryGluingEdgeMap W h k e, true)) := by
    simpa only [List.map_map, Function.comp_def, primedLimitDartMap,
      lMinusPrimedDartImage, boundaryGluingPrimedEdgeMap] using hw
  have ht := congrArg (List.take p.length) hw'
  rw [← List.map_take, ← List.map_take] at ht
  change (((0 :: (kmswStage u m).LL.reverse).take p.length).map
    (fun e => (e, true))).map (lMinusPrimedDartImage hτ) = p
  rw [List.map_map]
  change ((0 :: (kmswStage u m).LL.reverse).take p.length).map
    (fun e => lMinusPrimedDartImage hτ (e, true)) = p
  rw [ht, hlen]
  have hh := congrArg (List.map (fun e => (e, true))) hm
  rw [List.map_map] at hh
  exact hh.trans (lPlusPrefixUpperLeftDarts_eq (W := W) (h := h) (k := k)).symm

/-- The ordered prefix attaches to the independently ordered primed root/LL
segment. Endpoint bits use the actual primed side flip. -/
theorem lPlus_prefix_primed_ordered_attachment_corrected
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) :
    let w := shiftedStream W 0
    let u := primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
    let p := lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)
    ∃ m : ℕ,
      let q := ((0 :: (kmswStage u m).LL.reverse).take p.length).map
        (fun e => (e, true))
      p.length = q.length ∧
        (∀ (i : ℕ) (a b : ℕ × Bool),
          p[i]? = some a → q[i]? = some b →
          a.1 = boundaryGluingPrimedEdgeMap W h k hτ b.1 ∧
          a.2 = (b.2 ^^ primedLimitSideFlip
            (boundaryGluingFutureStream W h k) hτ b.1) ∧
          kmswDartEndpoint w a = boundaryGluingPrimedVertexMap W h k hτ
            (kmswDartEndpoint u b) ∧
          kmswDartEndpoint w (a.1, !a.2) = boundaryGluingPrimedVertexMap W h k hτ
            (kmswDartEndpoint u (b.1, !b.2))) ∧
        (p.head?.map (kmswDartEndpoint w)).getD (boundaryVertex w h k) =
          boundaryVertex w h k ∧
        (q.head?.map (fun b => boundaryGluingPrimedVertexMap W h k hτ
          (kmswDartEndpoint u b))).getD
            (boundaryGluingPrimedVertexMap W h k hτ (kmswDartEndpoint u (0, true))) =
          boundaryVertex w h k ∧
        (p.getLast?.map (fun a => kmswDartEndpoint w (a.1, !a.2))).getD
            (boundaryVertex w h k) =
          (q.getLast?.map (fun b => boundaryGluingPrimedVertexMap W h k hτ
            (kmswDartEndpoint u (b.1, !b.2)))).getD (boundaryVertex w h k) := by
  let w := shiftedStream W 0
  let u := primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
  let p := lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)
  obtain ⟨m, hm⟩ := lPlus_prefix_primed_ordered_dart_image hτ
  let q := ((0 :: (kmswStage u m).LL.reverse).take p.length).map
    (fun e => (e, true))
  have himage : q.map (lMinusPrimedDartImage hτ) = p := hm
  refine ⟨m, ?_, ?_, ?_, ?_, ?_⟩
  · exact (List.length_map (lMinusPrimedDartImage hτ)).symm.trans
      (congrArg List.length himage) |>.symm
  · intro i a b ha hb
    have hi := congrArg (fun r : List (ℕ × Bool) => r[i]?) himage
    rw [List.getElem?_map, hb, Option.map_some, ha] at hi
    have heq : lMinusPrimedDartImage hτ b = a := Option.some.inj hi
    refine ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm, ?_, ?_⟩
    · rw [← heq]
      exact (lPlus_primed_dart_endpoints hτ b).1
    · rw [← heq]
      exact (lPlus_primed_dart_endpoints hτ b).2
  · exact lPlusPrefixUpperLeftDarts_head_endpoint
  · have hhead : p.head?.map (kmswDartEndpoint w) =
        q.head?.map (fun b => boundaryGluingPrimedVertexMap W h k hτ
          (kmswDartEndpoint u b)) := by
      rw [← himage, List.head?_map, Option.map_map]
      congr 1
      funext b
      exact (lPlus_primed_dart_endpoints hτ b).1
    change (q.head?.map (fun b => boundaryGluingPrimedVertexMap W h k hτ
      (kmswDartEndpoint u b))).getD
        (boundaryGluingPrimedVertexMap W h k hτ (kmswDartEndpoint u (0, true))) = _
    rw [lPlus_primed_root_starts_at_xk hτ, ← hhead]
    exact lPlusPrefixUpperLeftDarts_head_endpoint
  · have hlast : p.getLast?.map (fun a => kmswDartEndpoint w (a.1, !a.2)) =
        q.getLast?.map (fun b => boundaryGluingPrimedVertexMap W h k hτ
          (kmswDartEndpoint u (b.1, !b.2))) := by
      rw [← himage, List.getLast?_map, Option.map_map]
      congr 1
      funext b
      exact (lPlus_primed_dart_endpoints hτ b).2
    exact congrArg (fun r : Option ℕ => r.getD (boundaryVertex w h k)) hlast

end DirectedDistances.PaperProofs.Section5
