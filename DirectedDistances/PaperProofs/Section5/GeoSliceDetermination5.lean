/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination4
import DirectedDistances.KMSW.UIBHBOTAssemblyFaceBorders

/-! # Finite-segment face identification for geodesic slices -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}





@[expose] noncomputable def m0CutGeodesicSegmentTrace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ) : Set ℂ :=
  {(WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (P.codePath.initial 0).1.id)} ∪
    ⋃ i : Fin n, ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam P i.val))).image



theorem m0CutGeodesicSegmentTrace_isCompact
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ) :
    IsCompact (m0CutGeodesicSegmentTrace hp P n) := by
  exact isCompact_singleton.union (isCompact_iUnion fun i =>
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam P i.val))).isCompact_image)

/-- Helper toward Lemma 5.6: the finite segment is part of the actual
drawing; its endpoint is included even for a zero offset. -/
theorem m0CutGeodesicSegmentTrace_subset_drawing
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ) :
    m0CutGeodesicSegmentTrace hp P n ⊆
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).image := by
  rintro z (hz | hz)
  · exact Or.inl ⟨_, Set.mem_singleton_iff.mp hz |>.symm⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact Or.inr ⟨wholePlaneDartι W 0 (m0GeodesicSeam P i.val), hi⟩






@[expose] noncomputable def m0CutGeodesicSliceBoundaryTrace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) : Set ℂ :=
  (m0CutGeodesicSegmentTrace hp (P (k - 1)) a ∪
    m0CutGeodesicSegmentTrace hp (P k) b) ∪
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0
        (boundaryOuterEdge (shiftedStream W 0) h (k - 1), false))).image

/-- Helper toward Lemma 5.6: the finite enclosing boundary is compact. -/
theorem m0CutGeodesicSliceBoundaryTrace_isCompact
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) :
    IsCompact (m0CutGeodesicSliceBoundaryTrace hp P k a b) := by
  exact ((m0CutGeodesicSegmentTrace_isCompact hp (P (k - 1)) a).union
    (m0CutGeodesicSegmentTrace_isCompact hp (P k) b)).union
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0
          (boundaryOuterEdge (shiftedStream W 0) h (k - 1), false))).isCompact_image

/-- Helper toward Lemma 5.6: every point of the finite enclosing boundary
lies in the glued drawing, including missing geometric boundary edges. -/
theorem m0CutGeodesicSliceBoundaryTrace_subset_drawing
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) :
    m0CutGeodesicSliceBoundaryTrace hp P k a b ⊆
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).image := by
  rintro z ((hz | hz) | hz)
  · exact m0CutGeodesicSegmentTrace_subset_drawing hp (P (k - 1)) a hz
  · exact m0CutGeodesicSegmentTrace_subset_drawing hp (P k) b hz
  · exact Or.inr ⟨wholePlaneDartι W 0
      (boundaryOuterEdge (shiftedStream W 0) h (k - 1), false), hz⟩







@[expose] noncomputable def m0CutFaceEnclosedBySegments
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) : Prop :=
  F.val ⊆ m0GeodesicAmbientRegion W H h ∧
    ∀ z ∈ F.val, Bornology.IsBounded
      (connectedComponentIn (m0CutGeodesicSliceBoundaryTrace hp P k a b)ᶜ z)

/-- Helper toward Lemma 5.6: enclosure can be tested at one point of the
face, since a face cannot cross the finite enclosing boundary. -/
theorem m0CutFaceEnclosedBySegments_iff_exists
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutFaceEnclosedBySegments hp P k a b F ↔
      F.val ⊆ m0GeodesicAmbientRegion W H h ∧
        ∃ z ∈ F.val, Bornology.IsBounded
          (connectedComponentIn (m0CutGeodesicSliceBoundaryTrace hp P k a b)ᶜ z) := by
  obtain ⟨q, hq, hF⟩ := F.property
  have hconn : IsConnected F.val := by
    rw [hF]
    exact isConnected_connectedComponentIn_iff.mpr hq
  constructor
  · rintro ⟨hambient, hbounded⟩
    obtain ⟨z, hz⟩ := hconn.nonempty
    exact ⟨hambient, z, hz, hbounded z hz⟩
  · rintro ⟨hambient, z, hz, hbounded⟩
    refine ⟨hambient, fun y hy => ?_⟩
    have hsub : F.val ⊆ (m0CutGeodesicSliceBoundaryTrace hp P k a b)ᶜ := by
      intro u hu hub
      exact (WholePlanePastGlueDrawing.glueDrawing W h hp H).face_subset_compl F hu
        (m0CutGeodesicSliceBoundaryTrace_subset_drawing hp P k a b hub)
    have hycomp := hconn.isPreconnected.subset_connectedComponentIn hz hsub hy
    rw [← connectedComponentIn_eq hycomp]
    exact hbounded

/-- Helper toward Lemma 5.6: a face is represented by the candidate slice
when a run-zero dart bordering that face has a retained face successor.
This defines representation, independently of finite-segment enclosure. -/
@[expose] noncomputable def m0CutGeodesicSliceRepresentsFace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) : Prop :=
  ∃ d e : ℕ × Bool,
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d) F ∧
      (m0CutGeodesicSlice (hp := hp) P k a b hab).faceNext d e

/-- Helper toward Lemma 5.6: the two face witnesses in the candidate
successor relation are the same actual glued face, by uniqueness of the
face to the left of a dart. This strengthens the relation intersection in
`GeoSliceDetermination4`; it does not identify a finite enclosed region.
Each containment is in the named side region `m0GeodesicSideOpenRegion`
(not asserted to be open; see `M0GeodesicSideCarrier.lean:186–212`). -/
theorem m0CutGeodesicSliceRepresentsFace_iff_common_side_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutGeodesicSliceRepresentsFace hp P k a b hab F ↔
      (∃ d : ℕ × Bool,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 d) F) ∧
        F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
        F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  constructor
  · rintro ⟨d, e, hdF, hd⟩
    obtain ⟨hr, hl⟩ := (m0CutGeodesicSlice_faceNext_iff (hp := hp) P k a b hab d e).1 hd
    obtain ⟨⟨Fr, hdFr, hFr⟩, _⟩ := hr
    obtain ⟨⟨Fl, hdFl, hFl⟩, _⟩ := hl
    have hright : Fr = F := G.dartBorders_face_unique _ _ _ hdFr hdF
    have hleft : Fl = F := G.dartBorders_face_unique _ _ _ hdFl hdF
    exact ⟨⟨d, hdF⟩, hright ▸ hFr, hleft ▸ hFl⟩
  · rintro ⟨⟨d, hdF⟩, hr, hl⟩
    refine ⟨d, kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d, hdF, ?_⟩
    exact (m0CutGeodesicSlice_faceNext_iff (hp := hp) P k a b hab d _).2
      ⟨⟨⟨F, hdF, hr⟩, rfl⟩, ⟨⟨F, hdF, hl⟩, rfl⟩⟩
































































end DirectedDistances.PaperProofs.Section5
