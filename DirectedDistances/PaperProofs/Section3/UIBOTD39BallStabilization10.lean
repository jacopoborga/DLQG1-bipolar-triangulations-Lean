/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization9

/-! # Complete original face boundaries on captured balls

The boundary statements concern original complementary components of an
arbitrary whole-plane drawing. No geometric comparison is assumed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set Metric Topology

private theorem frontier_eq_border_arcs_of_finite
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (F : P.Face) (hfin : {d | P.dartBorders d F}.Finite) :
    frontier F.val = ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image := by
  let K := ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image
  have hc : IsClosed K := hfin.isClosed_biUnion fun d _ =>
    (P.arc d).isCompact_image.isClosed
  apply Subset.antisymm
  · intro q hq
    by_contra hn
    obtain ⟨s, hs, hsafe⟩ := Metric.mem_nhds_iff.mp (hc.isOpen_compl.mem_nhds hn)
    have hqi := (P.face_open_frontier_subset_image hv F).2 hq
    have ha : ∃ d, q ∈ (P.arc d).image := by
      rcases hqi with ⟨v, rfl⟩ | h
      · obtain ⟨d, rfl⟩ := hv v
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact h
    obtain ⟨d, hd⟩ := ha
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        q ∈ (P.arc d).segmentAt i := by
      rcases hd with hstart | ⟨i, hi, hqi⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [hstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hqi⟩
    obtain ⟨i, hi, hqi⟩ := hseg
    by_cases he : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
    · obtain ⟨x, hxf, hxb, hx⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
        hv F q d hi he (frontier_subset_closure hq) hs
      obtain ⟨e, hxe, heF⟩ := P.exists_mem_arc_dartBorders_of_frontier_not_vertex
        hv F hxf hx
      exact hsafe hxb (mem_iUnion₂.mpr ⟨e, heF, hxe⟩)
    · have hqo := mem_openSegment_of_ne_left_right
        (fun h => he (Or.inl h.symm)) (fun h => he (Or.inr h.symm)) hqi
      rcases (P.mem_closure_face_openSegment_iff_dartBorders hv d F hi hqo).mp
          (frontier_subset_closure hq) with hb | hb
      · exact hn (mem_iUnion₂.mpr ⟨d, hb, (P.arc d).segmentAt_subset_image hi hqi⟩)
      · apply hn
        apply mem_iUnion₂.mpr
        refine ⟨flip d, hb, ?_⟩
        rw [P.arc_image_flip]
        exact (P.arc d).segmentAt_subset_image hi hqi
  · rintro q hq
    obtain ⟨d, hd, hqd⟩ := mem_iUnion₂.mp hq
    exact P.dartBorders_arc_subset_frontier hv d F hd hqd

private theorem vertex_closure_iff_border_endpoint
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (F : P.Face) (hfin : {d | P.dartBorders d F}.Finite) (v : V) :
    P.pos v ∈ closure F.val ↔
      ∃ d, P.dartBorders d F ∧ (vert d = v ∨ vert (flip d) = v) := by
  constructor
  · intro hcl
    have hfr : P.pos v ∈ frontier F.val := by
      rw [frontier, (P.face_open_frontier_subset_image hv F).1.interior_eq]
      exact ⟨hcl, fun h => P.face_subset_compl F h (Or.inl ⟨v, rfl⟩)⟩
    rw [frontier_eq_border_arcs_of_finite P hv F hfin] at hfr
    obtain ⟨d, hd, hmem⟩ := mem_iUnion₂.mp hfr
    have he : P.pos v = (P.arc d).start ∨ P.pos v = (P.arc d).finish := by
      by_contra hn
      exact P.interior_avoids_vertices d v
        ⟨hmem, by simpa only [mem_insert_iff, mem_singleton_iff] using hn⟩
    refine ⟨d, hd, ?_⟩
    rcases he with he | he
    · exact Or.inl (P.pos_injective ((P.arc_start d).symm.trans he.symm))
    · exact Or.inr (P.pos_injective ((P.arc_finish d).symm.trans he.symm))
  · rintro ⟨d, hd, he | he⟩
    · apply P.dartBorders_arc_subset_closure hv d F hd
      rw [← he, ← P.arc_start d]
      exact Or.inl rfl
    · apply P.dartBorders_arc_subset_closure hv d F hd
      rw [← he, ← P.arc_image_flip d, ← P.arc_start (flip d)]
      exact Or.inl rfl

private theorem bounded_face_of_finite_border_of_infinite
    {D V : Type*} [Infinite D] {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (F : P.Face) (hfin : {d | P.dartBorders d F}.Finite) :
    Bornology.IsBounded F.val := by
  have hcompact : IsCompact (frontier F.val) := by
    rw [frontier_eq_border_arcs_of_finite P hv F hfin]
    exact hfin.isCompact_biUnion fun d _ => (P.arc d).isCompact_image
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    hcompact.isBounded
  by_contra hn
  have hunb := (P.isUnbounded_iff_not_isBounded F).mpr hn
  obtain ⟨z, hz, hzR⟩ := hunb R
  have hzout : z ∈ (closedBall (0 : ℂ) R)ᶜ := by
    simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hzR
  have hout : (closedBall (0 : ℂ) R)ᶜ ⊆ F.val := by
    apply (isConnected_compl_closedBall_complex R).isPreconnected.subset_of_closure_inter_subset
      (P.face_open_frontier_subset_image hv F).1 ⟨z, hzout, hz⟩
    rintro x ⟨hxcl, hxout⟩
    by_contra hxF
    have hxf : x ∈ frontier F.val := by
      rw [frontier, (P.face_open_frontier_subset_image hv F).1.interior_eq]
      exact ⟨hxcl, hxF⟩
    exact hxout (hR hxf)
  have hi : P.image ⊆ closedBall (0 : ℂ) R := by
    intro x hx
    by_contra hxb
    exact P.face_subset_compl F (hout hxb) hx
  have hall : (Set.univ : Set D).Finite :=
    (P.locally_finite (closedBall (0 : ℂ) R) isBounded_closedBall).subset (by
      intro d _
      exact ⟨(P.arc d).start, hi (Or.inr ⟨d, Or.inl rfl⟩), Or.inl rfl⟩)
  exact Set.infinite_univ hall

private theorem closure_vertices_iff_border_endpoints
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (S : Set V) (hS : S.Finite) (F : P.Face) :
    (∀ v, P.pos v ∈ closure F.val → v ∈ S) ↔
      ∀ d, P.dartBorders d F → vert d ∈ S ∧ vert (flip d) ∈ S := by
  constructor
  · intro h d hd
    constructor
    · apply h
      apply P.dartBorders_arc_subset_closure hv d F hd
      rw [← P.arc_start d]
      exact Or.inl rfl
    · apply h
      apply P.dartBorders_arc_subset_closure hv d F hd
      rw [← P.arc_image_flip d, ← P.arc_start (flip d)]
      exact Or.inl rfl
  · intro h
    have hfin : {d | P.dartBorders d F}.Finite :=
      (P.locally_finite (P.pos '' S) (hS.image P.pos).isCompact.isBounded).subset (by
        intro d hd
        refine ⟨P.pos (vert d), ⟨vert d, (h d hd).1, rfl⟩, ?_⟩
        rw [← P.arc_start d]
        exact Or.inl rfl)
    intro v hvcl
    obtain ⟨d, hd, he | he⟩ :=
      (vertex_closure_iff_border_endpoint P hv F hfin v).mp hvcl
    · exact he ▸ (h d hd).1
    · exact he ▸ (h d hd).2

/-- Helper toward Proposition 3.9: all bordering darts of an original
retained face form a finite set, for every whole-plane drawing. -/
theorem uibotWholePlane_retainedFace_borderDarts_finite
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : G.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r) :
    {d | G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv F)}.Finite := by
  apply (Set.finite_range (fun a : StageDart
    (kmswStage (shiftedStream W N) (2 * N)).nextEdge =>
      wholePlaneDartι W N (a.1.val, a.2))).subset
  intro d hd
  obtain ⟨a, ha, _⟩ := uibotWholePlane_retainedFace_dart_allocated
    W H G hp N r hcap F hF d hd
  exact ⟨a, ha⟩

/-- Helper toward Proposition 3.9: the complete original frontier is
the union of the bordering arcs labelled inside the captured window.
This includes endpoints and polyline bends, for arbitrary G. -/
theorem uibotWholePlane_retainedFace_frontier_window
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : G.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r) :
    frontier F.val = ⋃ a : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge,
      ⋃ (_ : G.dartBorders (wholePlaneDartι W N (a.1.val, a.2))
        (G.toPlaneGraphDrawingFaceEquiv F)),
        (G.arc (wholePlaneDartι W N (a.1.val, a.2))).image := by
  have hfin := uibotWholePlane_retainedFace_borderDarts_finite W H G hp N r hcap F hF
  rw [show frontier F.val = frontier (G.toPlaneGraphDrawingFaceEquiv F).val from rfl,
    frontier_eq_border_arcs_of_finite G (uibhbot_faceOrbit_dartVertex_surjective W H) _ hfin]
  ext z
  constructor
  · intro hz
    obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hz
    obtain ⟨a, ha, _⟩ := uibotWholePlane_retainedFace_dart_allocated
      W H G hp N r hcap F hF d hd
    exact mem_iUnion₂.mpr ⟨a, ha.symm ▸ hd, ha.symm ▸ hzd⟩
  · intro hz
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨_, ha, hza⟩

/-- Helper toward Proposition 3.9: every original retained face of any
whole-plane drawing is bounded. Finite border support and local finiteness
exclude an exterior component; no canonical drawing is required. -/
theorem uibotWholePlane_retainedFace_bounded
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : G.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r) :
    Bornology.IsBounded F.val := by
  have hinj : Function.Injective (fun n : ℕ => wholePlaneDartι W 0 (n, false)) := by
    intro a b hab
    exact wholePlaneEdgeι_injective W 0 (congrArg Prod.fst hab)
  let : Infinite (WholePlaneDart W) := Infinite.of_injective _ hinj
  exact bounded_face_of_finite_border_of_infinite G
    (uibhbot_faceOrbit_dartVertex_surjective W H) (G.toPlaneGraphDrawingFaceEquiv F)
    (uibotWholePlane_retainedFace_borderDarts_finite W H G hp N r hcap F hF)

/-- Helper toward Proposition 3.9: retention of any original face in an
arbitrary whole-plane drawing is equivalent to testing the two endpoints
of every bordering dart. No face-retention premise is used in this iff. -/
theorem uibotWholePlane_face_retained_iff_borderEndpoints
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : G.toPlaneGraphDrawing.Face) :
    F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r ↔
    ∀ d, G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv F) →
      wholePlaneDartVertex W d ∈ d39GeomBallVertices
        (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G) r ∧
      wholePlaneDartVertex W (wholePlaneDartFlip W d) ∈ d39GeomBallVertices
        (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G) r := by
  have hS : (d39GeomBallVertices (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r).Finite := by
    rw [uibotWholePlaneGeometricBallVertices_eq_window W H G hp N r hcap]
    exact (Finset.finite_toSet _).image _
  exact closure_vertices_iff_border_endpoints G
    (uibhbot_faceOrbit_dartVertex_surjective W H) _ hS (G.toPlaneGraphDrawingFaceEquiv F)

/-- Helper toward Proposition 3.9: the original finite-face retention
test is exactly the bordering-dart endpoint test for every exterior-certified
drawing and every chronological root, including radius zero. -/
theorem uibotFiniteStage_face_retained_iff_borderEndpoints
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (j : ℕ) (hj : j ≤ n) (r : ℕ) (F : P.toPlaneGraphDrawing.Face) :
    F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j hj) r ↔
    ∀ d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) →
      stageVertex w n d ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j hj) r ∧
      stageVertex w n (edgeFlip _ d) ∈
        d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
          (uibotFiniteStageExteriorRoot P j hj) r := by
  exact closure_vertices_iff_border_endpoints P (kmswStageDrawing_vertex_surjective w n)
    _ (Set.toFinite _) (P.toPlaneGraphDrawingFaceEquiv F)

/-- Helper toward Proposition 3.9: boundary vertices of an arbitrary
retained whole-plane face are precisely endpoints of its captured bordering
darts, with both directions of the closure-membership characterization. -/
theorem uibotWholePlane_retainedFace_boundary_window
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : G.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r) (v : WholePlaneVertex W) :
    G.pos v ∈ closure F.val ↔
      ∃ a : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge,
        G.dartBorders (wholePlaneDartι W N (a.1.val, a.2))
          (G.toPlaneGraphDrawingFaceEquiv F) ∧
        (wholePlaneDartVertex W (wholePlaneDartι W N (a.1.val, a.2)) = v ∨
          wholePlaneDartVertex W
            (wholePlaneDartFlip W (wholePlaneDartι W N (a.1.val, a.2))) = v) := by
  rw [show closure F.val = closure (G.toPlaneGraphDrawingFaceEquiv F).val from rfl,
    vertex_closure_iff_border_endpoint G (uibhbot_faceOrbit_dartVertex_surjective W H) _
      (uibotWholePlane_retainedFace_borderDarts_finite W H G hp N r hcap F hF)]
  constructor
  · rintro ⟨d, hd, hv⟩
    obtain ⟨a, ha, _⟩ := uibotWholePlane_retainedFace_dart_allocated
      W H G hp N r hcap F hF d hd
    exact ⟨a, ha.symm ▸ hd, ha.symm ▸ hv⟩
  · rintro ⟨a, ha, hv⟩
    exact ⟨_, ha, hv⟩

end DirectedDistances.PaperProofs.Section3
end
