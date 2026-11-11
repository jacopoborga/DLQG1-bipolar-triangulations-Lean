/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Source
public import DirectedDistances.KMSW.BoundaryLimsup
public import DirectedDistances.KMSW.StageActiveEdges











public section
namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk




@[expose] def OneSidedKMSWBoundEdges32At (w : ℕ → Fin 3) : Prop :=
  ∃ M : DirectedPlaneMapWithMissing ℕ ℕ,
    M.toPlaneMapWithMissing.src = edgeWest w ∧
    M.toPlaneMapWithMissing.tgt = edgeEast w ∧
    (∀ e, M.toPlaneMapWithMissing.missing e ↔ ¬ EdgePresent w e) ∧
    (∀ e, M.forward e = true) ∧ M.IsAcyclic ∧
    ∃ (B : BoundaryPresentationWithJunctions.{0, 0, 0, 0, 0, 0} M)
      (rot : Equiv.Perm (ℕ × Bool))
      (G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial M)) (U : G.Face) (S : ℕ × Bool → ℕ × Bool),
      DrawsMap M G ∧
      (∀ e, e ∈ upperLeftBoundary32 B ↔ kmswBoundaryLimsup State.UL w e) ∧
      (∀ e, e ∈ upperRightBoundary32 B ↔ kmswBoundaryLimsup State.UR w e) ∧
      (∀ e, e ∈ lowerRightBoundary32 B ↔ kmswBoundaryLimsup State.LR w e) ∧
      (∀ e, e ∈ lowerLeftBoundary32 B ↔ kmswBoundaryLimsup State.LL w e) ∧
      BoundEdges32SourceClauses M B G U S




@[expose] def OneSidedKMSWBoundEdges32Source : Prop :=
  ∀ w : ℕ → Fin 3, OneSidedKMSWBoundEdges32At w




@[expose] def BiInfiniteKMSWBoundEdges32Source : Prop :=
  ∀ W : ℤ → Fin 3,
    ∃ M : DirectedPlaneMapWithMissing (WholePlaneVertex W) (WholePlaneEdge W),
      M.toPlaneMapWithMissing.src = wholePlaneEdgeWest W ∧
      M.toPlaneMapWithMissing.tgt = wholePlaneEdgeEast W ∧
      (∀ e, M.toPlaneMapWithMissing.missing e ↔ ¬ wholePlaneEdgePresent W e) ∧
      (∀ e, M.forward e = true) ∧ M.IsAcyclic ∧
      ∃ (B : BoundaryPresentationWithJunctions.{0, 0, 0, 0, 0, 0} M)
        (rot : Equiv.Perm (WholePlaneEdge W × Bool))
        (G : PLDrawing (WholePlaneEdge W × Bool) (WholePlaneVertex W)
          (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
        (U : G.Face) (S : WholePlaneEdge W × Bool → WholePlaneEdge W × Bool),
        DrawsMap M G ∧
        (∀ e, e ∈ upperLeftBoundary32 B ↔ kmswBiInfiniteBoundaryLimsup State.UL W e) ∧
        (∀ e, e ∈ upperRightBoundary32 B ↔ kmswBiInfiniteBoundaryLimsup State.UR W e) ∧
        (∀ e, e ∈ lowerRightBoundary32 B ↔ kmswBiInfiniteBoundaryLimsup State.LR W e) ∧
        (∀ e, e ∈ lowerLeftBoundary32 B ↔ kmswBiInfiniteBoundaryLimsup State.LL W e) ∧
        BoundEdges32SourceClauses M B G U S

/-- Helper toward Definition 3.2: a PL drawing on the exact stable endpoint
carrier forces finite KMSW incidence; this condition cannot silently be added
to the arbitrary-stream source remark. No boundary certificate is assumed. -/
theorem kmsw_finiteIncidence_of_compatible_drawing_carriers1
    (w : ℕ → Fin 3) (M : DirectedPlaneMapWithMissing ℕ ℕ)
    (hsrc : M.toPlaneMapWithMissing.src = edgeWest w)
    (htgt : M.toPlaneMapWithMissing.tgt = edgeEast w)
    {rot : Equiv.Perm (ℕ × Bool)}
    (G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) : KMSWFiniteIncidence w := by
  intro v
  have hf : {d : ℕ × Bool | boundaryDartInitial M d = v}.Finite := by
    apply (G.locally_finite {G.pos v} Bornology.isBounded_singleton).subset
    intro d hd
    refine ⟨G.pos v, rfl, ?_⟩
    have hs : (G.arc d).start = G.pos v := (G.arc_start d).trans (congrArg G.pos hd)
    exact Or.inl hs.symm
  apply (hf.image Prod.fst).subset
  rintro e ⟨n, he, hv | hv⟩
  · refine ⟨(e, true), ?_, rfl⟩
    simp only [Set.mem_ofPred_eq, boundaryDartInitial_eq, ↓reduceIte, hsrc]
    exact (edge_endpoints_eq w he).1.symm.trans hv
  · refine ⟨(e, false), ?_, rfl⟩
    simp only [Set.mem_ofPred_eq, boundaryDartInitial_eq, Bool.false_eq_true,
      ↓reduceIte, htgt]
    exact (edge_endpoints_eq w he).2.symm.trans hv

private theorem all_up_active_west (n : ℕ) :
    (kmswStage (fun _ => (1 : Fin 3)) n).west
      (kmswStage (fun _ => (1 : Fin 3)) n).active = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (kmswStage_up_active_endpoints (fun _ => (1 : Fin 3)) n rfl).1.trans ih




theorem all_up_not_finiteIncidence_carriers1 :
    ¬ KMSWFiniteIncidence (fun _ => (1 : Fin 3)) := by
  intro hfin
  apply (Set.infinite_of_injective_forall_mem
    (f := fun n => (kmswStage (fun _ => (1 : Fin 3)) n).active)
    (fun _ _ h => CutConverse.act_injective _ h) ?_) (hfin 0)
  intro n
  exact ⟨n, kmswStage_active_lt _ n, Or.inl (all_up_active_west n)⟩




theorem not_oneSidedKMSWBoundEdges32Source_carriers1 :
    ¬ OneSidedKMSWBoundEdges32Source := by
  intro h
  obtain ⟨M, hs, ht, _, _, _, B, rot, G, U, S, _⟩ := h (fun _ => (1 : Fin 3))
  exact all_up_not_finiteIncidence_carriers1
    (kmsw_finiteIncidence_of_compatible_drawing_carriers1 _ M hs ht G)

/-- Helper toward Definition 3.2: every compatible raw one-sided drawing
has locally finite vertex image on the installed finite-incidence domain.
No transience, nonnegative L, or right-unboundedness hypothesis is needed. -/
theorem kmsw_raw_locallyFiniteVertexImage_carriers1
    (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    {rot : Equiv.Perm (ℕ × Bool)}
    (G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) rot
      (kmswLimitDartVertex w)) : LocallyFiniteVertexImage G :=
  locallyFiniteVertexImage_of_surjective G (kmswLimitDartVertex_surjective w hfin)

/-- Helper toward Definition 3.2: every compatible whole-plane carrier
drawing has locally finite vertex image, with no probabilistic hypothesis. -/
theorem kmsw_wholePlane_locallyFiniteVertexImage_carriers1
    (W : ℤ → Fin 3) {rot : Equiv.Perm (WholePlaneDart W)}
    (G : PLDrawing (WholePlaneDart W) (WholePlaneVertex W)
      (wholePlaneDartFlip W) rot (wholePlaneDartVertex W)) :
    LocallyFiniteVertexImage G :=
  locallyFiniteVertexImage_of_surjective G (WholePlanePastGlueData.vertex_incident W)

end DirectedDistances.PlanarMap

