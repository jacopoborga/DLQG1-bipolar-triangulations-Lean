/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceFaceFidelity
public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice4
public import DirectedDistances.PaperProofs.Section5.GeoSliceFaceChainClopen
public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination9

/-! Finite-segment enclosure and its identification with the source-leftmost slice. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Set
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: the finite enclosing trace consists of the two
finite geodesic segments and the lower boundary of the ambient epigraph R
between their initial vertices. The last term is specified by R's defining
seam function and those two vertices, rather than by a directed edge or an
infinite path. It closes the two segments along the boundary of R, including
when the corresponding geometric boundary edge is missing from the directed
map. Zero-length segments retain their initial vertex. -/
@[expose] noncomputable def geodesicSegmentsEnclosingTrace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) : Set ℂ :=
  (m0CutGeodesicSegmentTrace hp (P (k - 1)) a ∪
    m0CutGeodesicSegmentTrace hp (P k) b) ∪
    graphOver
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial 0).1.id)).re
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 ((P k).codePath.initial 0).1.id)).re
      (seamFun (shiftedStream W 0) h (H.1 0))

/-- Helper toward Lemma 5.6: the enclosing trace specified using R and the
finite segments agrees with the existing literal finite-boundary trace.
This identity involves no choice of leftmost path or common tail. -/
theorem geodesicSegmentsEnclosingTrace_eq_boundaryTrace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) :
    geodesicSegmentsEnclosingTrace hp P k a b =
      m0CutGeodesicSliceBoundaryTrace hp P k a b := by
  unfold geodesicSegmentsEnclosingTrace m0CutGeodesicSliceBoundaryTrace
  rw [m0CutGeodesic_initial_zero_pos hp (P (k - 1)),
    m0CutGeodesic_initial_zero_pos hp (P k),
    m0CutBoundaryEdgeTrace_eq_graphOver hp]
  simp only [sub_add_cancel]

/-- Helper toward Lemma 5.6: a retained ambient face lies between the finite
segments when its entire point set lies in one bounded connected component
of the complement of their enclosing trace. This is a literal finite-boundary
predicate: its only geometric data are the two finite segments and R, whose
lower boundary between the roots closes them. In particular it does not use
whole-path side regions or a slice face relation. The coalescence witness
specifies the source offsets but does not enter the predicate's body.
Using the closed finite boundary in the plane distinguishes enclosure by
both segments from pockets cut off by just one segment and the boundary of R. -/
@[expose] noncomputable def faceLiesBetweenSegments
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (_hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) : Prop :=
  F.val ⊆ m0GeodesicAmbientRegion W H h ∧
    ∃ z ∈ F.val,
      F.val ⊆ connectedComponentIn (geodesicSegmentsEnclosingTrace hp P k a b)ᶜ z ∧
      Bornology.IsBounded
        (connectedComponentIn (geodesicSegmentsEnclosingTrace hp P k a b)ᶜ z)

/-- Helper toward Lemma 5.6: the single bounded-component predicate agrees
with finite-boundary enclosure tested pointwise on the face. Connectedness
of the actual face supplies containment in the component; it is not assumed. -/
theorem faceLiesBetweenSegments_iff_enclosedBySegments
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    faceLiesBetweenSegments hp P k a b hab F ↔
      m0CutFaceEnclosedBySegments hp P k a b F := by
  unfold faceLiesBetweenSegments
  rw [geodesicSegmentsEnclosingTrace_eq_boundaryTrace]
  constructor
  · rintro ⟨hFR, z, hz, _, hb⟩
    exact (m0CutFaceEnclosedBySegments_iff_exists hp P k a b F).mpr
      ⟨hFR, z, hz, hb⟩
  · intro hF
    obtain ⟨hFR, z, hz, hb⟩ :=
      (m0CutFaceEnclosedBySegments_iff_exists hp P k a b F).mp hF
    have hzC : z ∈ connectedComponentIn (m0CutGeodesicSliceBoundaryTrace hp P k a b)ᶜ z :=
      mem_connectedComponentIn (fun hzB =>
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).face_subset_compl F hz
          (m0CutGeodesicSliceBoundaryTrace_subset_drawing hp P k a b hzB))
    exact ⟨hFR, z, hz,
      m0Geodesic_face_subset_slit_component hp _
        (m0CutGeodesicSliceBoundaryTrace_subset_drawing hp P k a b) z F ⟨z, hzC, hz⟩, hb⟩

/-- Helper toward Lemma 5.6: the finite enclosing trace is compact. This
also covers a single-edge slice and zero-length later segment. -/
theorem geodesicSegmentsEnclosingTrace_isCompact
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) :
    IsCompact (geodesicSegmentsEnclosingTrace hp P k a b) := by
  rw [geodesicSegmentsEnclosingTrace_eq_boundaryTrace]
  exact m0CutGeodesicSliceBoundaryTrace_isCompact hp P k a b

/-- Helper toward Lemma 5.6: the finite enclosing trace is contained in
the actual drawing, including missing geometric boundary edges. -/
theorem geodesicSegmentsEnclosingTrace_subset_drawing
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) :
    geodesicSegmentsEnclosingTrace hp P k a b ⊆
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).image := by
  rw [geodesicSegmentsEnclosingTrace_eq_boundaryTrace]
  exact m0CutGeodesicSliceBoundaryTrace_subset_drawing hp P k a b

/-- Helper toward Lemma 5.6: every face in the preceding open right region
and current open left region lies in a bounded component enclosed by the
finite segments. The shared infinite tail is eliminated in the existing
finite-boundary theorem; leftmostness is unnecessary in this direction. -/
theorem faceLiesBetweenSegments_of_side_regions
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hRight : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (hLeft : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left) :
    faceLiesBetweenSegments hp P k a b hab F := by
  apply (faceLiesBetweenSegments_iff_enclosedBySegments hp P k a b hab F).mpr
  apply m0CutFaceEnclosedBySegments_of_representsFace hp P k a b hab F
  exact (m0CutGeodesicSliceRepresentsFace_iff_side_regions hp P k a b hab F).mpr
    ⟨hRight, hLeft⟩

/-- Helper toward Lemma 5.6: a face enclosed by the finite segments of the
source's leftmost geodesics belongs to the preceding open right and current
open left regions. The leftmost hypotheses are the paper's choice of paths;
they exclude the reverse-oriented overlap without an assumed separation or
boundedness result. All coalescence offsets, including zero, are retained. -/
theorem faceLiesBetweenSegments_side_regions_of_leftmost
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : faceLiesBetweenSegments hp P k a b hab F) :
    F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left := by
  apply (m0CutGeodesicSliceRepresentsFace_iff_side_regions hp P k a b hab F).mp
  apply (m0CutGeodesicSlice_face_identification_of_leftmost hp P k
    (T (k - 1)) (T k) (hleft (k - 1)) (hleft k) a b hab F).mp
  exact (faceLiesBetweenSegments_iff_enclosedBySegments hp P k a b hab F).mp hF

/-- Helper toward Lemma 5.6: for the source's leftmost geodesics, the faces
lying between the two finite segments are exactly their open right/left
whole-path overlap. No common tail is part of the finite-boundary predicate. -/
theorem faceLiesBetweenSegments_iff_side_regions_of_leftmost
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    faceLiesBetweenSegments hp P k a b hab F ↔
      F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
        F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left :=
  ⟨faceLiesBetweenSegments_side_regions_of_leftmost hp P T hleft k a b hab F,
    fun hF => faceLiesBetweenSegments_of_side_regions hp P k a b hab F hF.1 hF.2⟩

/-- Helper toward Lemma 5.6: the slice carrier's represented retained faces
are exactly the ambient faces lying between its two finite segments. This
restates the geometric equivalence for the actual `faceNext` representation;
it makes no claim about the slice laws or completion of Lemma 5.6. -/
theorem m0CutGeodesicSlice_representsFace_iff_liesBetweenSegments
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutGeodesicSliceRepresentsFace hp P k a b hab F ↔
      faceLiesBetweenSegments hp P k a b hab F :=
  (m0CutGeodesicSliceRepresentsFace_iff_side_regions hp P k a b hab F).trans
    (faceLiesBetweenSegments_iff_side_regions_of_leftmost hp P T hleft k a b hab F).symm

/-- Helper toward Lemma 5.6: every point of the finite-boundary component
containing a retained overlap face is strictly west of the common vertex.
This includes drawing points in the component. Boundedness follows from the
proved overlap-to-enclosure direction and is not a premise. -/
theorem geodesicSegmentsEnclosingTrace_bounded_component_re_lt
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hRight : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (hLeft : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    {z w : ℂ}
    (hzF : z ∈ F.val)
    (hw : w ∈ connectedComponentIn (geodesicSegmentsEnclosingTrace hp P k a b)ᶜ z) :
    w.re < ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re := by
  have henc := (faceLiesBetweenSegments_iff_enclosedBySegments hp P k a b hab F).mp
    (faceLiesBetweenSegments_of_side_regions hp P k a b hab F hRight hLeft)
  have hb := henc.2 z hzF
  rw [geodesicSegmentsEnclosingTrace_eq_boundaryTrace] at hw
  obtain ⟨f, g, hf, hg, ha, hc, _, _, hB⟩ :=
    m0CutGeodesicSliceBoundaryTrace_exists_graphs hp P k a b hab
  have hxc : seamX (shiftedStream W 0) h (H.1 0) (k - 1) ≤
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re := by
    have hmono := (m0CutGeodesic_vertex_re_strictMono hp (P (k - 1))).monotone
      (Nat.zero_le a)
    rw [m0CutGeodesic_initial_zero_pos] at hmono
    exact hmono
  have hwB : w ∉ m0CutGeodesicSliceBoundaryTrace hp P k a b :=
    connectedComponentIn_subset _ _ hw
  rw [connectedComponentIn_eq hw, hB] at hb
  rw [hB] at hwB
  exact ((isBounded_connectedComponentIn_compl_graphOver_union_iff_min_max
    hxc hf hg ha hc hwB).mp hb).2.1

/-- Helper toward Lemma 5.6: the component containing a retained overlap
face avoids both aligned common-tail traces, including their initial common
vertex. This proves exclusion for the entire component. Its boundedness is
proved from face retention, rather than supplied as an assumption. -/
theorem geodesicSegmentsEnclosingTrace_bounded_component_disjoint_common_tail
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hRight : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (hLeft : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    {z : ℂ}
    (hzF : z ∈ F.val) :
    Disjoint (connectedComponentIn (geodesicSegmentsEnclosingTrace hp P k a b)ᶜ z)
      (pathTrace (WholePlanePastGlueDrawing.glueDrawing W h hp H)
        (fun n => wholePlaneDartι W 0 ((P (k - 1)).codePath.edge (a + n), false))) ∧
    Disjoint (connectedComponentIn (geodesicSegmentsEnclosingTrace hp P k a b)ᶜ z)
      (pathTrace (WholePlanePastGlueDrawing.glueDrawing W h hp H)
        (fun n => wholePlaneDartι W 0 ((P k).codePath.edge (b + n), false))) := by
  have hprev : Disjoint
      (connectedComponentIn (geodesicSegmentsEnclosingTrace hp P k a b)ᶜ z)
      (pathTrace (WholePlanePastGlueDrawing.glueDrawing W h hp H)
        (fun n => wholePlaneDartι W 0 ((P (k - 1)).codePath.edge (a + n), false))) := by
    apply Set.disjoint_left.mpr
    intro w hwC hwT
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hwT
    have hwlt := geodesicSegmentsEnclosingTrace_bounded_component_re_lt
      hp P k a b hab F hRight hLeft hzF hwC
    let p := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam (P (k - 1)) (a + n)))
    have hm : p.XMonotone := m0CutGeodesic_arc_xMonotone hp (P (k - 1)) (a + n)
    have hstart : p.start.re ≤ w.re := by
      have hn' : w ∈ p.image := hn
      rcases hn' with rfl | ⟨i, hi, hwi⟩
      · exact le_rfl
      · have hfirst : p.start.re ≤ (p.point i).re := by
          rw [← p.point_zero_eq_start]
          exact p.point_re_le_of_le hm (Nat.zero_le i) (by omega)
        exact hfirst.trans (p.segmentAt_re_bounds hm hi hwi).1
    change ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam (P (k - 1)) (a + n)))).start.re ≤ w.re
      at hstart
    rw [m0CutGeodesic_arc_start] at hstart
    have hmono := (m0CutGeodesic_vertex_re_strictMono hp (P (k - 1))).monotone
      (show a ≤ a + n by omega)
    exact (not_lt_of_ge (hmono.trans hstart)) hwlt
  refine ⟨hprev, Set.disjoint_left.mpr ?_⟩
  intro w hwC hwT
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hwT
  apply Set.disjoint_left.mp hprev hwC
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  have hedge := wholePlaneEdgeι_injective W 0 (hab.1 n)
  change w ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
    (wholePlaneDartι W 0 ((P (k - 1)).codePath.edge (a + n), false))).image
  rw [hedge]
  exact hn

/-- Helper toward Lemma 5.6: a face-successor pair is retained by the slice
exactly when its actual incident face lies between the finite segments and
its successor is the ambient face successor. This identifies the stored
relation itself, preserving dart identities and the existing orientation. -/
theorem m0CutGeodesicSlice_faceNext_iff_liesBetweenSegments
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (d e : ℕ × Bool) :
    (m0CutGeodesicSlice (hp := hp) P k a b hab).faceNext d e ↔
      ∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 d) F ∧
        faceLiesBetweenSegments hp P k a b hab F ∧
        kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d = e := by
  constructor
  · intro hnext
    have hsides := (m0CutGeodesicSlice_faceNext_iff (hp := hp) P k a b hab d e).mp hnext
    obtain ⟨⟨F, hdF, _⟩, hsucc⟩ := hsides.1
    refine ⟨F, hdF, ?_, hsucc⟩
    exact (m0CutGeodesicSlice_representsFace_iff_liesBetweenSegments
      hp P T hleft k a b hab F).mp ⟨d, e, hdF, hnext⟩
  · rintro ⟨F, hdF, hF, hsucc⟩
    have hsides := (faceLiesBetweenSegments_iff_side_regions_of_leftmost
      hp P T hleft k a b hab F).mp hF
    exact (m0CutGeodesicSlice_faceNext_iff (hp := hp) P k a b hab d e).mpr
      ⟨⟨⟨F, hdF, hsides.1⟩, hsucc⟩, ⟨⟨F, hdF, hsides.2⟩, hsucc⟩⟩

end DirectedDistances.PaperProofs.Section5

