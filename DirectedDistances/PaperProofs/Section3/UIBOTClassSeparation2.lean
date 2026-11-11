/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation
public import DirectedDistances.PaperProofs.Section3.UIBOTWholePlaneSourcePart2

/-! # The retained-face obstruction to a residual plane component

Helpers toward Proposition 3.9 and Definition 3.8
source-specific geometric separation route. The cellular extension in steps
sole coordinator. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.KMSW DirectedDistances.RandomWalk
open Set
open scoped Topology

universe uV uE uV' uE'

/-- Helper toward Proposition 3.9: a single ball isomorphism transfers the
existence of boundary vertices of all source faces to all target faces.
Inside the contradiction argument, a target face without boundary vertices
would be retained, so its source preimage supplies a boundary vertex. -/
theorem uibotClassSeparation2_face_has_boundary_vertex
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {M : DirectedPlaneMapWithMissing V E} {ρ : E × Bool}
    {N : DirectedPlaneMapWithMissing V' E'} {σ : E' × Bool} {r : ℕ}
    (J : D39GeomBallIsoV2 r M ρ N σ)
    (hsource : ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      ∃ v, M.toPlaneMapWithMissing.pos v ∈ closure F.val)
    (F : N.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
    ∃ v, N.toPlaneMapWithMissing.pos v ∈ closure F.val := by
  classical
  by_contra hnone
  let Ft : {F // F ∈ d39GeomRetainedFaces N σ r} :=
    ⟨F, by
      intro v hv
      exact (hnone ⟨v, hv⟩).elim⟩
  let Fs := J.faceEquiv.symm Ft
  obtain ⟨v, hv⟩ := hsource Fs.val
  let vb : {v // v ∈ d39GeomBallVertices M ρ r} := ⟨v, Fs.property v hv⟩
  have hfaces : J.h '' Fs.val.val = F.val := by
    exact (J.face_image_map Fs).trans
      (congrArg (fun x => x.val.val) (J.faceEquiv.apply_symm_apply Ft))
  have hcl : J.h (M.toPlaneMapWithMissing.pos v) ∈ closure F.val := by
    rw [← hfaces, ← J.h.image_closure]
    exact Set.mem_image_of_mem _ hv
  exact hnone ⟨(J.vertexEquiv vb).val, (J.pos_map vb) ▸ hcl⟩

/-- Helper toward Proposition 3.9: every glued source face has a boundary
vertex, in the actual source carrier with individual whole-plane edge IDs. -/
theorem uibotClassSeparation2_source_face_has_boundary_vertex
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      ∃ v, M.toPlaneMapWithMissing.pos v ∈ closure F.val := by
  intro G M F
  let I := uibotWholePlaneSourceIso W H G hp
  let Fg := I.faceEquiv F
  obtain ⟨d, hd⟩ := WholePlaneGlueFaceCorrespondenceFull.face_bordered
    W h0 hpast H (G.toPlaneGraphDrawingFaceEquiv Fg)
  have hc := G.dartBorders_arc_subset_closure
    (uibhbot_faceOrbit_dartVertex_surjective W H) d
    (G.toPlaneGraphDrawingFaceEquiv Fg) hd
  have hval : Fg.val = F.val := by
    rw [show Fg.val = I.h '' F.val from I.faceEquiv_val F]
    exact Set.image_id _
  refine ⟨wholePlaneDartVertex W d, ?_⟩
  change G.pos (wholePlaneDartVertex W d) ∈ closure F.val
  have hstart : (G.arc d).start ∈ closure Fg.val := hc (Or.inl rfl)
  rw [G.arc_start d, hval] at hstart
  exact hstart

/-- Helper toward Proposition 3.9: an open union of complete target faces
and the entire target drawing has no residual component if every face has
a boundary vertex. The face condition is exactly the saturation supplied by
a cellular map whose face interiors are complete target components. -/
theorem uibotClassSeparation2_open_image_eq_univ
    {V : Type uV} {E : Type uE} (N : DirectedPlaneMapWithMissing V E)
    (U : Set ℂ) (hopen : IsOpen U)
    (hvertices : ∀ v, N.toPlaneMapWithMissing.pos v ∈ U)
    (hedges : ∀ e, Set.range (N.toPlaneMapWithMissing.arc e) ⊆ U)
    (hfaces : ∀ F : N.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      (F.val ∩ U).Nonempty → F.val ⊆ U)
    (hboundary : ∀ F : N.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      ∃ v, N.toPlaneMapWithMissing.pos v ∈ closure F.val) :
    U = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro z
  by_contra hz
  let D := N.toPlaneMapWithMissing.toPlaneGraphDrawing
  have hnotdrawing : z ∉ D.image := by
    rintro (⟨v, rfl⟩ | he)
    · exact hz (hvertices v)
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp he
      exact hz (hedges e he)
  let F : D.Face := ⟨connectedComponentIn D.imageᶜ z, z, hnotdrawing, rfl⟩
  have hzF : z ∈ F.val := mem_connectedComponentIn hnotdrawing
  have hdisjoint : F.val ⊆ Uᶜ := by
    intro x hx hxU
    exact hz (hfaces F ⟨x, hx, hxU⟩ hzF)
  have hclosure : closure F.val ⊆ Uᶜ :=
    closure_minimal hdisjoint hopen.isClosed_compl
  obtain ⟨v, hv⟩ := hboundary F
  exact hclosure hv (hvertices v)

/-- Helper toward Proposition 3.9: the retained-face step (4) of the A57
route for the full deterministic source witness scope. Given the open cellular
image from step (3), one radius-one ball witness rules out every residual face.
No properness or separability condition is imposed on the target map. -/
theorem uibotClassSeparation2_source_open_image_eq_univ
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    (∀ r : ℕ, 0 < r → Nonempty (D39GeomBallIsoV2 r M ρ A.map A.root)) →
    ∀ (U : Set ℂ), IsOpen U →
      (∀ v, A.map.toPlaneMapWithMissing.pos v ∈ U) →
      (∀ e, Set.range (A.map.toPlaneMapWithMissing.arc e) ⊆ U) →
      (∀ F : A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        (F.val ∩ U).Nonempty → F.val ⊆ U) → U = Set.univ := by
  intro G M ρ hballs U hopen hvertices hedges hfaces
  obtain ⟨J⟩ := hballs 1 Nat.one_pos
  exact uibotClassSeparation2_open_image_eq_univ A.map U hopen hvertices hedges hfaces
    (uibotClassSeparation2_face_has_boundary_vertex J
      (uibotClassSeparation2_source_face_has_boundary_vertex W H h0 hpast hp))

/-- Helper toward Proposition 3.9: source face closures are compact and
contain only finitely many source vertices. This part of step (1) uses the
actual glued geometry and does not assert the missing disk charts. -/
theorem uibotClassSeparation2_source_face_compact_finite_boundary
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      IsCompact (closure F.val) ∧
        {v | M.toPlaneMapWithMissing.pos v ∈ closure F.val}.Finite := by
  intro G M F
  let I := uibotWholePlaneSourceIso W H G hp
  let Fg := I.faceEquiv F
  have hval : Fg.val = F.val := by
    rw [show Fg.val = I.h '' F.val from I.faceEquiv_val F]
    exact Set.image_id _
  have hn := WholePlanePastGlueDrawing.glueDrawing_face_bounded
    W h0 hpast H (G.toPlaneGraphDrawingFaceEquiv Fg)
  have hb : Bornology.IsBounded Fg.val := by
    by_contra h
    exact hn ((G.isUnbounded_iff_not_isBounded _).mpr h)
  rw [hval] at hb
  refine ⟨hb.isCompact_closure, ?_⟩
  have hfinite := G.locally_finite (closure F.val) hb.closure
  apply (hfinite.image (wholePlaneDartVertex W)).subset
  intro v hv
  obtain ⟨d, hd⟩ := uibhbot_faceOrbit_dartVertex_surjective W H v
  refine ⟨d, ?_, hd⟩
  refine ⟨G.pos v, hv, ?_⟩
  rw [← hd, ← G.arc_start d]
  exact Or.inl rfl

/-- Helper toward Proposition 3.9: every finite vertex set in a connected
Definition 3.8 domain lies in some positive-radius ball. -/
theorem uibotClassSeparation2_finite_vertices_in_ball
    (A : D39DomainRootedMap.{uV}) (S : Set A.V) (hS : S.Finite) :
    ∃ r : ℕ, 0 < r ∧ S ⊆ d39GeomBallVertices A.map A.root r := by
  classical
  have hcover : ∀ v : A.V, ∃ n : ℕ,
      v ∈ d39GeomBallVertices A.map A.root n := by
    intro v
    obtain ⟨p, hp⟩ :=
      (A.domain.connected (d39GeomRootVertex A.map A.root) v).exists_walk_length_eq_edist
    refine ⟨p.length, ?_⟩
    change (d39GeomGraph A.map).edist _ v ≤ _
    rw [← hp]
  choose n hn using hcover
  refine ⟨hS.toFinset.sup n + 1, Nat.succ_pos _, ?_⟩
  intro v hv
  exact D39GeomBallIsoV2.vertexBall_mono
    ((Finset.le_sup (f := n) (hS.mem_toFinset.mpr hv)).trans (Nat.le_succ _)) (hn v)

/-- Helper toward Proposition 3.9: each original source face is retained
at some positive radius. This supplies the exhaustion needed before choosing
and extending compatible maps on whole source faces in step (3). -/
theorem uibotClassSeparation2_source_face_eventually_retained
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      ∃ r : ℕ, 0 < r ∧ F ∈ d39GeomRetainedFaces M ρ r := by
  intro G M ρ F
  let A := uibotWholePlaneSourceDomain W H G hp
  obtain ⟨r, hr, hball⟩ := uibotClassSeparation2_finite_vertices_in_ball A
    {v | M.toPlaneMapWithMissing.pos v ∈ closure F.val}
    (uibotClassSeparation2_source_face_compact_finite_boundary W H h0 hpast hp F).2
  exact ⟨r, hr, hball⟩








































































end DirectedDistances.PaperProofs.Section3
end
