/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation12

/-! Finite present-side vertex simplicity and the cyclic stage successor. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the finite successor has no cycles. -/
theorem kmswFiniteRunNext14_acyclic {m : ℕ} (i : Fin m) :
    ¬ Relation.TransGen (fun i j : Fin m => kmswFiniteRunNext i = some j) i i := by
  have hstep : ∀ a b : Fin m, kmswFiniteRunNext a = some b → a.val < b.val := by
    intro a b hab
    unfold kmswFiniteRunNext at hab
    split at hab
    · injection hab with heq
      have := congrArg Fin.val heq
      dsimp at this
      omega
    · cases hab
  have htrans (a b : Fin m)
      (h : Relation.TransGen (fun i j : Fin m => kmswFiniteRunNext i = some j) a b) :
      a.val < b.val := by
    induction h with
    | single h => exact hstep _ _ h
    | tail _ h ih => exact lt_trans ih (hstep _ _ h)
  intro h
  exact lt_irrefl _ (htrans i i h)

/-- Helper toward Definition 3.2: a duplicate-free complete vertex list
certifies simplicity of a finite dart run, including its last vertex. -/
theorem kmswFiniteRunSide14_simple_of_vertex_list_nodup
    {V E : Type*} (M : DirectedPlaneMapWithMissing V E)
    (ds : List (E × Bool)) (hnd : ds.Nodup) (initial terminal : V)
    (hne : ds ≠ []) (label : V → ℕ)
    (hv : (ds.map (fun d => label (boundaryDartInitial M d)) ++
      [label (boundaryDartTerminal M (ds.getLast hne))]).Nodup) :
    IsSimpleBoundarySide M (kmswFiniteRunSide ds hnd initial terminal) := by
  let B := kmswFiniteRunSide ds hnd initial terminal
  let vs := ds.map (fun d => label (boundaryDartInitial M d)) ++
    [label (boundaryDartTerminal M (ds.getLast hne))]
  have hlast (i : Fin ds.length) (hi : kmswFiniteRunNext i = none) :
      i.val = ds.length - 1 := by
    unfold kmswFiniteRunNext at hi
    split at hi
    · cases hi
    · omega
  let position : B.Index ⊕ {i : B.Index // B.next i = none} → Fin vs.length
    | .inl i => ⟨i.val, by simp only [vs, List.length_append, List.length_map,
        List.length_singleton]; omega⟩
    | .inr _ => ⟨ds.length, by simp [vs]⟩
  have hget (x : B.Index ⊕ {i : B.Index // B.next i = none}) :
      vs.get (position x) = label (boundarySideVertex M B x) := by
    cases x with
    | inl i =>
      change vs[i.val]'(position (.inl i)).isLt = label (boundaryDartInitial M ds[i.val])
      simp [vs, i.isLt]
    | inr i =>
      have hi := hlast i.val i.property
      change vs[ds.length]'(position (.inr i)).isLt =
        label (boundaryDartTerminal M ds[i.val.val])
      simp [vs, List.getLast_eq_getElem, hi]
  constructor
  · intro x y hxy
    have hp : position x = position y := hv.get_inj_iff.mp
      ((hget x).trans ((congrArg label hxy).trans (hget y).symm))
    have hpv := congrArg Fin.val hp
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (Fin.ext hpv)
      | inr j => change i.val = ds.length at hpv; have := i.isLt; omega
    | inr i =>
      cases y with
      | inl j => change ds.length = j.val at hpv; have := j.isLt; omega
      | inr j =>
        apply congrArg Sum.inr
        apply Subtype.ext
        apply Fin.ext
        exact (hlast i.val i.property).trans (hlast j.val j.property).symm
  · exact kmswFiniteRunNext14_acyclic

/-- Helper toward Definition 3.2: projecting the initial stage vertices of
an allocated run recovers its endpoint labels in their original order. -/
theorem stageDarts14_initial_labels (w : ℕ → Fin 3) (n : ℕ)
    (es : List ℕ) (side : Bool)
    (hes : ∀ e ∈ es, e < (kmswStage w n).nextEdge) :
    (stageDarts (kmswStage w n) es side hes).map
      (fun d => (stageVertex w n d).val) =
    es.map (fun e => if side then (kmswStage w n).east e
      else (kmswStage w n).west e) := by
  simp only [stageDarts, List.map_map, stageVertex, stageEndpoint]
  exact List.attach_map_val (l := es)
    (f := fun e => if side then (kmswStage w n).east e else (kmswStage w n).west e)

/-- Helper toward Definition 3.2: every realized upper-left side visits
distinct vertices, including its final vertex, and has no successor cycle. -/
theorem kmswStageFiniteBoundaryPresentation14_upperLeft_simple
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    IsSimpleBoundarySide M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft := by
  let s := kmswStage w n
  have hne := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  change IsSimpleBoundarySide M (kmswFiniteRunSide _ (kmswStage_finite_run_nodup w n).1
    J.lowerLeftUpperLeft J.upperLeftUpperRight)
  apply kmswFiniteRunSide14_simple_of_vertex_list_nodup M _ _ _ _ hne Fin.val
  simp_rw [kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal,
    kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal]
  have hmap : (kmswStageULDartRun w n).map (fun d => (stageVertex w n d).val) =
      s.UL.map s.west := by
    simpa only [kmswStageULDartRun, Bool.false_eq_true, ↓reduceIte, s] using
      stageDarts14_initial_labels w n (kmswStage w n).UL false _
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hlast : (kmswStageULDartRun w n).getLast hne =
      ((⟨s.active, act_lt_nextEdge w (Nat.le_refl n)⟩ : Fin s.nextEdge), false) := by
    simp [kmswStageULDartRun, stageDarts, hxs, s]
  rw [hmap, hlast]
  change (s.UL.map s.west ++ [s.east s.active]).Nodup
  have hv := CutConverse.ul_path_vertices_nodup w n
  apply List.nodup_reverse.mp
  simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.map_reverse, CutConverse.westStack,
    act, s] using hv

/-- Helper toward Definition 3.2: along an endpoint chain, strict edge
ranks separate all vertices, including both endpoints. -/
private theorem kmswStageFiniteBoundaryPresentation14_chain_ranks
    (s : State) (r : ℕ → ℚ) (e : ℕ) (es : List ℕ)
    (hc : WestEastChain s (e :: es))
    (hr : ∀ a ∈ e :: es, r (s.west a) < r (s.east a)) :
    (r (s.west e) :: (e :: es).map (fun a => r (s.east a))).Pairwise (· < ·) := by
  induction es generalizing e with
  | nil => simpa using hr e (by simp)
  | cons f fs ih =>
    have hchain := List.isChain_cons_cons.mp hc
    have hf := ih f hchain.2 (fun a ha => hr a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons, List.pairwise_cons_cons_iff_of_trans]
    refine ⟨hr e (by simp), ?_⟩
    rw [hchain.1]
    simpa only [List.map_cons, List.pairwise_cons_cons_iff_of_trans] using hf

/-- Helper toward Definition 3.2: every realized reversed lower-right side
visits distinct vertices, including its final vertex, and has no cycle. -/
theorem kmswStageFiniteBoundaryPresentation14_lowerRight_simple
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    IsSimpleBoundarySide M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight := by
  let s := kmswStage w n
  have hne := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  change IsSimpleBoundarySide M (kmswFiniteRunSide _ (kmswStage_finite_run_nodup w n).2.2.1
    J.upperRightLowerRight J.lowerRightLowerLeft)
  apply kmswFiniteRunSide14_simple_of_vertex_list_nodup M _ _ _ _ hne Fin.val
  simp_rw [kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal,
    kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal]
  have hmap : (kmswStageLRDartRun w n).map (fun d => (stageVertex w n d).val) =
      s.LR.reverse.map s.east := by
    simpa only [kmswStageLRDartRun, ↓reduceIte, s] using
      stageDarts14_initial_labels w n (kmswStage w n).LR.reverse true _
  have hLRne : s.LR ≠ [] := (kmswStage_boundary_chain_invariant w n).2.2.2.2.1
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hLRne
  have healloc : e < s.nextEdge := stageRun_edge_bound w n e
    (Or.inr (by change e ∈ s.LR; rw [he]; simp))
  have hlast : (kmswStageLRDartRun w n).getLast hne =
      ((⟨e, healloc⟩ : Fin s.nextEdge), true) := by
    change (stageDarts s s.LR.reverse true (fun a ha =>
      stageRun_edge_bound w n a (Or.inr (List.mem_reverse.mp ha)))).getLast hne = _
    simp [stageDarts, he]
  rw [hmap, hlast]
  change (s.LR.reverse.map s.east ++ [s.west e]).Nodup
  have hc : WestEastChain s (e :: es) := by
    have hh := (kmswStage_boundary_chain_invariant w n).2.1
    change WestEastChain s (s.LL ++ s.LR) at hh
    change List.IsChain (fun a b => s.east a = s.west b) (e :: es)
    simpa only [he] using hh.right_of_append
  have hr := kmswStageFiniteBoundaryPresentation14_chain_ranks s (kmswStageRank w n)
    e es hc (by
      intro a ha
      exact kmswStageRank_strict w n a (stageRun_edge_bound w n a
        (Or.inr (by change a ∈ s.LR; simpa only [he] using ha))))
  have hv : (s.west e :: (e :: es).map s.east).Nodup := by
    have hp : ((s.west e :: (e :: es).map s.east).map (kmswStageRank w n)).Pairwise
        (· < ·) := by
      simpa only [List.map_cons, List.map_map, Function.comp_def] using hr
    exact (List.pairwise_map.mp hp).imp
      (fun h heq => (ne_of_lt h) (congrArg (kmswStageRank w n) heq))
  rw [he]
  simpa only [List.reverse_cons, List.map_reverse, List.map_cons, List.map_append,
    List.map_nil, List.append_assoc] using List.nodup_reverse.mpr hv

/-- Helper toward Definition 3.2: the cyclic stage successor preserves the -/
theorem kmswStageFiniteBoundaryPresentation14_geometric_successor
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    IsGeometricExternalFaceSucc P U
      (fun d => (stageRot w n).symm (d.1, !d.2)) := by
  refine ⟨hU, ?_⟩
  intro d hd
  refine ⟨rfl, (hborder _).2 ?_⟩
  have hmem : d ∈ stageOuterWord w n :=
    (kmsw_stage_outer_face_exact w n d).1 ((hborder d).1 hd)
  have hnext := List.formPerm_apply_mem_of_mem hmem
  rw [← stageOuterWord_faceSucc w n d hmem] at hnext
  exact (kmsw_stage_outer_face_exact w n _).2 hnext

/-- Helper toward Definition 3.2: the same successor works on every
unbounded face of the selected finite drawing. -/
theorem kmswStageFiniteBoundaryPresentation14_all_geometric_successors
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    ∀ U' : P.Face, P.IsUnbounded U' → IsGeometricExternalFaceSucc P U'
      (fun d => (stageRot w n).symm (d.1, !d.2)) := by
  obtain ⟨F, hF, hunique⟩ := P.existsUnique_unbounded_face
  intro U' hU'
  have heq : U' = U := (hunique U' hU').trans (hunique U hU).symm
  subst U'
  exact kmswStageFiniteBoundaryPresentation14_geometric_successor w n P U hU hborder

/-- Helper toward Definition 3.2: adjacent nonempty portions of a cyclic
word meet at the successor of the first portion's final dart. -/
private theorem kmswStageFiniteBoundaryPresentation14_list_handoff
    {D : Type*} [DecidableEq D] (A B : List D)
    (hA : A ≠ []) (hB : B ≠ []) (hnd : (A ++ B).Nodup) :
    (A ++ B).formPerm (A.getLast hA) = B.head hB := by
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hA
  have hBlen : 0 < B.length := List.length_pos_iff.mpr hB
  have hk : A.length - 1 + 1 < (A ++ B).length := by
    simp only [List.length_append]
    omega
  have hh := List.formPerm_apply_lt_getElem (A ++ B) hnd (A.length - 1) hk
  have hk' : A.length - 1 + 1 = A.length := by omega
  simpa [hk', List.getLast_eq_getElem, ← List.head_eq_getElem_zero hB,
    show A.length - 1 < A.length by omega] using hh

/-- Helper toward Definition 3.2: the successor at the end of any run is
the first dart after its cyclic cut, including a skip of empty runs. -/
theorem kmswStageFiniteBoundaryPresentation14_cyclic_handoff
    (w : ℕ → Fin 3) (n : ℕ)
    (A R B : List (StageDart (kmswStage w n).nextEdge))
    (hword : stageOuterWord w n = A ++ R ++ B)
    (hR : R ≠ []) (hBA : B ++ A ≠ []) :
    (stageRot w n).symm (edgeFlip _ (R.getLast hR)) = (B ++ A).head hBA := by
  have hnd : (A ++ (R ++ B)).Nodup := by
    simpa only [hword, List.append_assoc] using stageOuterWord_nodup w n
  have hrotate := List.formPerm_rotate (A ++ (R ++ B)) hnd A.length
  rw [List.rotate_append_length_eq] at hrotate
  have hnd' : (R ++ (B ++ A)).Nodup := by
    have hh := (List.nodup_rotate (l := A ++ (R ++ B)) (n := A.length)).2 hnd
    simpa only [List.rotate_append_length_eq, List.append_assoc] using hh
  have hmem : R.getLast hR ∈ stageOuterWord w n := by
    rw [hword]
    simp only [List.mem_append]
    exact Or.inl (Or.inr (List.getLast_mem hR))
  change (kmswMap w n).faceSucc (R.getLast hR) = _
  rw [stageOuterWord_faceSucc w n _ hmem, hword]
  have hperm : (A ++ R ++ B).formPerm = (R ++ (B ++ A)).formPerm := by
    simpa only [List.append_assoc] using hrotate.symm
  rw [hperm]
  exact kmswStageFiniteBoundaryPresentation14_list_handoff R (B ++ A) hR hBA hnd'

/-- Helper toward Definition 3.2: all four run ends have their cyclic -/
theorem kmswStageFiniteBoundaryPresentation14_four_run_handoffs
    (w : ℕ → Fin 3) (n : ℕ) :
    let UL := kmswStageULDartRun w n
    let UR := kmswStageURDartRun w n
    let LR := kmswStageLRDartRun w n
    let LL := kmswStageLLDartRun w n
    (∀ hUL : UL ≠ [], ∀ htail : UR ++ LR ++ LL ≠ [],
      (stageRot w n).symm (edgeFlip _ (UL.getLast hUL)) =
        (UR ++ LR ++ LL).head htail) ∧
    (∀ hUR : UR ≠ [], ∀ htail : LR ++ LL ++ UL ≠ [],
      (stageRot w n).symm (edgeFlip _ (UR.getLast hUR)) =
        (LR ++ LL ++ UL).head htail) ∧
    (∀ hLR : LR ≠ [], ∀ htail : LL ++ UL ++ UR ≠ [],
      (stageRot w n).symm (edgeFlip _ (LR.getLast hLR)) =
        (LL ++ UL ++ UR).head htail) ∧
    (∀ hLL : LL ≠ [], ∀ htail : UL ++ UR ++ LR ≠ [],
      (stageRot w n).symm (edgeFlip _ (LL.getLast hLL)) =
        (UL ++ UR ++ LR).head htail) := by
  dsimp only
  have hword : stageOuterWord w n = kmswStageULDartRun w n ++
      kmswStageURDartRun w n ++ kmswStageLRDartRun w n ++ kmswStageLLDartRun w n := by
    simp [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
      kmswStageLRDartRun, kmswStageLLDartRun]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hUL htail
    simpa only [List.append_nil] using
      kmswStageFiniteBoundaryPresentation14_cyclic_handoff w n []
        (kmswStageULDartRun w n)
        (kmswStageURDartRun w n ++ kmswStageLRDartRun w n ++ kmswStageLLDartRun w n)
        (by simpa only [List.nil_append, List.append_assoc] using hword)
        hUL (by simpa only [List.append_nil] using htail)
  · intro hUR htail
    exact kmswStageFiniteBoundaryPresentation14_cyclic_handoff w n
      (kmswStageULDartRun w n) (kmswStageURDartRun w n)
      (kmswStageLRDartRun w n ++ kmswStageLLDartRun w n)
      (by simpa only [List.append_assoc] using hword) hUR htail
  · intro hLR htail
    simpa only [List.append_assoc] using
      kmswStageFiniteBoundaryPresentation14_cyclic_handoff w n
        (kmswStageULDartRun w n ++ kmswStageURDartRun w n)
        (kmswStageLRDartRun w n) (kmswStageLLDartRun w n) hword hLR
        (by simpa only [List.append_assoc] using htail)
  · intro hLL htail
    simpa only [List.nil_append] using
      kmswStageFiniteBoundaryPresentation14_cyclic_handoff w n
        (kmswStageULDartRun w n ++ kmswStageURDartRun w n ++ kmswStageLRDartRun w n)
        (kmswStageLLDartRun w n) [] (by simpa only [List.append_nil] using hword)
        hLL (by simpa only [List.nil_append] using htail)

/-- Helper toward Definition 3.2: the finite-stage package with geometric
succession and both present-side simplicity premises discharged. All other
open premises retain their exact Presentation12 binders. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses14
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (_hU : P.IsUnbounded U)
      (_hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      ULOkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      UROkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LROkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LLOkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge)),
      ∀ (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      FiniteBoundaryPositionOrder4 (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
      RequiredFiniteBoundaryJoinEndpointLabels7
        (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
      (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (Fin (kmswStage w n).nextEdge × Bool))
      (G : PLDrawing (Fin (kmswStage w n).nextEdge × Bool)
        (Fin (kmswStage w n).nextVertex) (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial M)) (U : G.Face)
      (S : Fin (kmswStage w n).nextEdge × Bool → Fin (kmswStage w n).nextEdge × Bool),
      kmsw_stage_map_realization32 w n P M ∧
      B = kmswStageFiniteBoundaryPresentationWithJunctions w n M J ∧
      G.image = P.image ∧ IsBoundEdges32 M B G U S := by
  obtain ⟨P, U, hU, hborder, hpackage⟩ :=
    exists_kmswStage_bound_edges32_of_open_clauses5 w n
  refine ⟨P, U, hU, hborder, ?_⟩
  intro hboundary hUL hUR hLR hLL hposition hjoin
  exact hpackage
    (kmswStageFiniteBoundaryPresentation14_all_geometric_successors w n P U hU hborder)
    hboundary hUL hUR hLR hLL
    (kmswStageFiniteBoundaryPresentation14_upperLeft_simple w n P)
    (kmswStageFiniteBoundaryPresentation14_lowerRight_simple w n P)
    hposition hjoin

end DirectedDistances.PaperProofs.Section3
