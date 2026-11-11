/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination5
import DirectedDistances.KMSW.WholePlanePastGlueM0Restriction
import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsFull
import DirectedDistances.PlanarMap.GraphRegionClosure
import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
import Mathlib.Topology.Piecewise
import all DirectedDistances.PaperProofs.Section5.BoundaryGeodesicSideGluing

/-! # Finite enclosure and candidate geodesic-slice faces -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: every glued face contained in the future region
is a bounded run-zero face, with the identical point set. In particular,
the closed ambient-region convention does not admit a past face. -/
theorem m0CutFace_exists_runZero_face
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    ∃ F0 : (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).Face,
      ¬ (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).IsUnbounded F0 ∧
      F.val = F0.val := by
  rcases WholePlanePastGlueDrawing.glueDrawing_faces W h hp H F with
    hfuture | ⟨Fp, hFp, heq⟩
  · exact hfuture
  · obtain ⟨z, hz, hcomp⟩ := F.property
    have hzF : z ∈ F.val := hcomp ▸ mem_connectedComponentIn hz
    have hbelow : z.im < seamFun (shiftedStream W 0) h (H.1 0) z.re :=
      PastFacesLower.image_boundedFace_subset_lower W h hp H Fp hFp (heq ▸ hzF)
    have habove : seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im := hF hzF
    exact False.elim ((not_le_of_gt hbelow) habove)

/-- Helper toward Lemma 5.6: each face in the future region has a bordering
run-zero dart. This discharges the dart-existence part of face identification
without an enclosure or side-determination premise. -/
theorem m0CutFace_exists_runZero_bordering_dart
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    ∃ d : ℕ × Bool,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 d) F := by
  obtain ⟨F0, _, heq⟩ := m0CutFace_exists_runZero_face hp F hF
  obtain ⟨d, hd⟩ := DirectedDistances.KMSW.face_bordered (shiftedStream W 0) (H.1 0) h F0
  refine ⟨d, ?_⟩
  exact (PLDrawing.dartBorders_congr _ _ F0 F
    (WholePlanePastGlueM0Restriction.restrict_arc W h hp H d) heq).mpr hd

/-- Helper toward Lemma 5.6: candidate face representation is exactly
containment in the named side region `m0GeodesicSideOpenRegion` for the
right and left sides of the bounding paths (not asserted to be open;
see M0GeodesicSideCarrier.lean:186-212).
The run-zero bordering dart is supplied by the future-face classification. -/
theorem m0CutGeodesicSliceRepresentsFace_iff_side_regions
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutGeodesicSliceRepresentsFace hp P k a b hab F ↔
      F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left := by
  rw [m0CutGeodesicSliceRepresentsFace_iff_common_side_face]
  constructor
  · rintro ⟨_, hr, hl⟩
    exact ⟨hr, hl⟩
  · rintro ⟨hr, hl⟩
    exact ⟨m0CutFace_exists_runZero_bordering_dart hp F (fun z hz => (hr hz).1), hr, hl⟩

/-- Helper toward Lemma 5.6: one point of a glued face determines whether
the entire face belongs to the future region. Faces cannot cross the seam. -/
theorem m0CutFace_subset_ambient_iff_mem
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    {z : ℂ} (hz : z ∈ F.val) :
    F.val ⊆ m0GeodesicAmbientRegion W H h ↔
      z ∈ m0GeodesicAmbientRegion W H h := by
  constructor
  · exact fun hF => hF hz
  · intro hza
    rcases WholePlanePastGlueDrawing.glueDrawing_faces W h hp H F with
      ⟨F0, hF0, heq⟩ | ⟨Fp, hFp, heq⟩
    · intro q hq
      have hupper : seamFun (shiftedStream W 0) h (H.1 0) q.re < q.im :=
        boundedFace_subset_upper (shiftedStream W 0) h (H.1 0) F0 hF0 (heq ▸ hq)
      exact hupper.le
    · have hbelow : z.im < seamFun (shiftedStream W 0) h (H.1 0) z.re :=
        PastFacesLower.image_boundedFace_subset_lower W h hp H Fp hFp (heq ▸ hz)
      have habove : seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im := hza
      exact False.elim ((not_le_of_gt hbelow) habove)

/-- Helper toward Lemma 5.6: at a point of a future face, membership in
the named side region (not asserted to be open) is equivalent to containment
of the whole face in that region. -/
theorem m0CutFace_subset_sideOpenRegion_iff_mem
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (s : DirectedDistances.PaperProofs.Section4.ThinMapSide) {z : ℂ} (hz : z ∈ F.val)
    (hF : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    F.val ⊆ m0GeodesicSideOpenRegion hp Q s ↔
      z ∈ m0GeodesicSideOpenRegion hp Q s := by
  constructor
  · exact fun hside => hside hz
  · intro hzs
    obtain ⟨t, ht, _⟩ := m0GeodesicFace_exactly_one hp Q F hF
    cases s <;> cases t
    · exact ht
    · exact False.elim (Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q)
        hzs (ht hz))
    · exact False.elim (Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q)
        (ht hz) hzs)
    · exact ht

/-- Helper toward Lemma 5.6: candidate face membership can be tested at
any one face point, using only the two named side regions (not asserted to be open). -/
theorem m0CutGeodesicSliceRepresentsFace_iff_mem_side_regions
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    {z : ℂ} (hz : z ∈ F.val) :
    m0CutGeodesicSliceRepresentsFace hp P k a b hab F ↔
      z ∈ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
      z ∈ m0GeodesicSideOpenRegion hp (P k) .left := by
  rw [m0CutGeodesicSliceRepresentsFace_iff_side_regions]
  constructor
  · rintro ⟨hr, hl⟩
    exact ⟨hr hz, hl hz⟩
  · rintro ⟨hr, hl⟩
    have hF : F.val ⊆ m0GeodesicAmbientRegion W H h :=
      (m0CutFace_subset_ambient_iff_mem hp F hz).mpr hr.1
    exact ⟨(m0CutFace_subset_sideOpenRegion_iff_mem hp (P (k - 1)) F .right hz hF).mpr hr,
      (m0CutFace_subset_sideOpenRegion_iff_mem hp (P k) F .left hz hF).mpr hl⟩

/-- Helper toward Lemma 5.6: finite enclosure can be tested at any
specified face point. The bounded component is taken in the complement
of the finite boundary, rather than the complement of the whole drawing. -/
theorem m0CutFaceEnclosedBySegments_iff_mem_component_isBounded
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    {z : ℂ} (hz : z ∈ F.val) :
    m0CutFaceEnclosedBySegments hp P k a b F ↔
      z ∈ m0GeodesicAmbientRegion W H h ∧
        Bornology.IsBounded
          (connectedComponentIn (m0CutGeodesicSliceBoundaryTrace hp P k a b)ᶜ z) := by
  constructor
  · rintro ⟨hF, hb⟩
    exact ⟨hF hz, hb z hz⟩
  · rintro ⟨hza, hb⟩
    apply (m0CutFaceEnclosedBySegments_iff_exists hp P k a b F).mpr
    exact ⟨(m0CutFace_subset_ambient_iff_mem hp F hz).mpr hza, z, hz, hb⟩

/-- Helper toward Lemma 5.6: a finite-segment edge starts at the indexed
geodesic vertex in the glued drawing. -/
theorem m0CutGeodesic_arc_start
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (i : ℕ) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam Q i))).start =
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 (Q.codePath.initial i).1.id) := by
  rw [WholePlanePastGlueM0Restriction.restrict_arc, m0Geodesic_pos_runZero]
  rw [(monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))).arc_start]
  change (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))).pos
      (edgeWest (shiftedStream W 0) (Q.codePath.edge i)) = _
  rw [(Q.codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2]

/-- Helper toward Lemma 5.6: a finite-segment edge finishes at the next
geodesic vertex in the glued drawing. -/
theorem m0CutGeodesic_arc_finish
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (i : ℕ) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam Q i))).finish =
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 (Q.codePath.initial (i + 1)).1.id) := by
  rw [WholePlanePastGlueM0Restriction.restrict_arc, m0Geodesic_pos_runZero]
  rw [(monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))).arc_finish]
  change (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))).pos
      (edgeEast (shiftedStream W 0) (Q.codePath.edge i)) = _
  rw [(Q.codePath.edge_incoming_at_succ (shiftedStream W 0) i).2]

/-- Helper toward Lemma 5.6: the abscissas of geodesic vertices strictly
increase, including across the finite-segment junction. -/
theorem m0CutGeodesic_vertex_re_strictMono
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) :
    StrictMono (fun i => ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (Q.codePath.initial i).1.id)).re) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hi := boundaryGluing_edge_re_lt W h hp (H := H) (Q.codePath.edge i)
  rw [(Q.codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2,
    (Q.codePath.edge_incoming_at_succ (shiftedStream W 0) i).2] at hi
  exact hi

/-- Helper toward Lemma 5.6: each finite-segment edge is monotone in
abscissa in the same glued drawing as the enclosure predicate. -/
theorem m0CutGeodesic_arc_xMonotone
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (i : ℕ) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam Q i))).XMonotone := by
  rw [WholePlanePastGlueM0Restriction.restrict_arc]
  exact infinitePresentPath_arc_xMonotone (H.1 0) _ Q.codePath i

/-- Helper toward Lemma 5.6: the image of a monotone polyline stays
between its endpoint abscissas. -/
private theorem polyline_image_re_bounds {p : Polyline} (hm : p.XMonotone)
    {z : ℂ} (hz : z ∈ p.image) :
    p.start.re ≤ z.re ∧ z.re ≤ p.finish.re := by
  have hlast : p.points.length - 1 < p.points.length := by
    have hne := List.length_pos_iff.mpr p.nonempty
    omega
  have hpoint (i : ℕ) (hi : i < p.points.length) :
      p.start.re ≤ (p.point i).re ∧ (p.point i).re ≤ p.finish.re := by
    constructor
    · rw [← p.point_zero_eq_start]
      exact p.point_re_le_of_le hm (Nat.zero_le i) hi
    · rw [← p.point_last_eq_finish]
      exact p.point_re_le_of_le hm (by omega) hlast
  rcases hz with rfl | ⟨i, hi, hz⟩
  · exact ⟨le_rfl, by simpa only [p.point_zero_eq_start] using (hpoint 0 (by omega)).2⟩
  · obtain ⟨hl, hr⟩ := p.segmentAt_re_bounds hm hi hz
    exact ⟨(hpoint i (by omega)).1.trans hl, hr.trans (hpoint (i + 1) hi).2⟩

/-- Helper toward Lemma 5.6: the endpoint belongs to the finite trace,
including when the segment length is zero. -/
theorem m0CutGeodesicSegmentTrace_endpoint_mem
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (n : ℕ) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (Q.codePath.initial n).1.id) ∈
        m0CutGeodesicSegmentTrace hp Q n := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨⟨n, Nat.lt_succ_self n⟩, ?_⟩
    rw [← m0CutGeodesic_arc_finish hp Q n]
    let p := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam Q n))
    have hlen : 2 ≤ p.points.length :=
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc_length _
    change p.finish ∈ p.image
    apply Or.inr
    refine ⟨p.points.length - 2, by omega, ?_⟩
    have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
    change p.finish ∈ segment ℝ (p.point (p.points.length - 2))
      (p.point (p.points.length - 2 + 1))
    rw [hidx, p.point_last_eq_finish]
    exact right_mem_segment ℝ _ _

/-- Helper toward Lemma 5.6: the finite segment is contained in the full
geodesic trace, including its initial vertex at zero length. -/
theorem m0CutGeodesicSegmentTrace_subset_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (n : ℕ) :
    m0CutGeodesicSegmentTrace hp Q n ⊆ m0GeodesicTrace hp Q := by
  rintro z (hz | hz)
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact m0Geodesic_initial_pos_mem_trace hp Q 0
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact m0Geodesic_arc_subset_trace hp Q i.val hi

/-- Helper toward Lemma 5.6: a finite segment is the part of the whole
trace at or west of its terminal vertex. This connects the literal finite
enclosing boundary to the graph-ray descriptions used for the whole sides. -/
theorem m0CutGeodesicSegmentTrace_eq_trace_inter_re_le
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (n : ℕ) :
    m0CutGeodesicSegmentTrace hp Q n =
      m0GeodesicTrace hp Q ∩
        {z | z.re ≤ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
          (wholePlaneVertexι W 0 (Q.codePath.initial n).1.id)).re} := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let v := fun i => G.pos (wholePlaneVertexι W 0 (Q.codePath.initial i).1.id)
  have hmono : StrictMono (fun i => (v i).re) :=
    m0CutGeodesic_vertex_re_strictMono hp Q
  have hb (i : ℕ) {z : ℂ}
      (hz : z ∈ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam Q i))).image) :
      (v i).re ≤ z.re ∧ z.re ≤ (v (i + 1)).re := by
    have hbound := polyline_image_re_bounds (m0CutGeodesic_arc_xMonotone hp Q i) hz
    rw [m0CutGeodesic_arc_start, m0CutGeodesic_arc_finish] at hbound
    exact hbound
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨m0CutGeodesicSegmentTrace_subset_trace hp Q n hz, ?_⟩
    rcases hz with hz | hz
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hmono.monotone (Nat.zero_le n)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact (hb i.val hi).2.trans (hmono.monotone (by omega))
  · rintro z ⟨hz, hzn⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    by_cases hin : i < n
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hin⟩, hi⟩)
    · have hni : n ≤ i := by omega
      have hre : z.re = (v n).re :=
        le_antisymm hzn ((hmono.monotone hni).trans (hb i hi).1)
      obtain ⟨X, g, _, _, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp Q
      have hzgraph := m0Geodesic_arc_subset_trace hp Q i hi
      have hvgraph := m0Geodesic_initial_pos_mem_trace hp Q n
      rw [hgraph] at hzgraph hvgraph
      have heq : z = v n := Complex.ext hre
        (hzgraph.2.trans ((congrArg g hre).trans hvgraph.2.symm))
      rw [heq]
      exact m0CutGeodesicSegmentTrace_endpoint_mem hp Q n

/-- Helper toward Lemma 5.6: each literal finite segment is a continuous
graph on the closed interval between its endpoint abscissas. The statement
includes zero-length segments and imposes no leftmost or enclosure premise. -/
theorem m0CutGeodesicSegmentTrace_exists_graph
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (n : ℕ) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Set.Icc
        ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
          (wholePlaneVertexι W 0 (Q.codePath.initial 0).1.id)).re
        ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
          (wholePlaneVertexι W 0 (Q.codePath.initial n).1.id)).re) ∧
      m0CutGeodesicSegmentTrace hp Q n = graphOver
        ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
          (wholePlaneVertexι W 0 (Q.codePath.initial 0).1.id)).re
        ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
          (wholePlaneVertexι W 0 (Q.codePath.initial n).1.id)).re g := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let v := fun i => G.pos (wholePlaneVertexι W 0 (Q.codePath.initial i).1.id)
  obtain ⟨X, g, _, hg, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp Q
  have hroot : ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).pos
        (boundaryVertex (shiftedStream W 0) h j)).re = (v 0).re := by
    dsimp [v, G]
    rw [m0Geodesic_pos_runZero hp, m0Geodesic_initial_zero Q]
  rw [hroot] at hg hgraph
  have hvn := m0Geodesic_initial_pos_mem_trace hp Q n
  rw [hgraph] at hvn
  have hdom : Set.Icc (v 0).re (v n).re ⊆ rayDomain (v 0).re X := by
    intro x hx
    exact ⟨hx.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hx.2) hvn.1.2⟩
  refine ⟨g, hg.mono hdom, ?_⟩
  rw [m0CutGeodesicSegmentTrace_eq_trace_inter_re_le, hgraph]
  ext z
  constructor
  · rintro ⟨⟨hd, hzg⟩, hzn⟩
    exact ⟨hd.1, hzn, hzg⟩
  · rintro ⟨h0, hn, hzg⟩
    exact ⟨⟨hdom ⟨h0, hn⟩, hzg⟩, hn⟩

/-- Helper toward Lemma 5.6: the bounded complementary components of two
ordered continuous graphs with common endpoints are exactly their open
intervening region. No strict separation between the graphs is required,
so contacts and a degenerate region are allowed. -/
theorem isBounded_connectedComponentIn_compl_graphOver_union_iff
    {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x)
    (ha : f a = g a) (hb : f b = g b)
    {z : ℂ} (hz : z ∉ graphOver a b f ∪ graphOver a b g) :
    Bornology.IsBounded
        (connectedComponentIn (graphOver a b f ∪ graphOver a b g)ᶜ z) ↔
      z ∈ graphRegion a b f g := by
  let B := graphOver a b f ∪ graphOver a b g
  let K := closedGraphRegion a b f g
  let U := graphRegion a b f g
  have hBK : B ⊆ K := by
    rintro q (hq | hq)
    · exact ⟨hq.1, hq.2.1, hq.2.2.ge, hq.2.2.le.trans (hfg _ ⟨hq.1, hq.2.1⟩)⟩
    · exact ⟨hq.1, hq.2.1, (hfg _ ⟨hq.1, hq.2.1⟩).trans hq.2.2.ge, hq.2.2.le⟩
  have hKU : ∀ q ∈ K, q ∉ B → q ∈ U := by
    intro q hq hnq
    have hleft : a < q.re := by
      refine lt_of_le_of_ne hq.1 ?_
      intro heq
      apply hnq
      apply Or.inl
      refine ⟨hq.1, hq.2.1, ?_⟩
      have hsame : g q.re = f q.re := by rw [← heq, ha]
      exact le_antisymm (hq.2.2.2.trans hsame.le) hq.2.2.1
    have hright : q.re < b := by
      refine lt_of_le_of_ne hq.2.1 ?_
      intro heq
      apply hnq
      apply Or.inl
      refine ⟨hq.1, hq.2.1, ?_⟩
      have hsame : g q.re = f q.re := by rw [heq, hb]
      exact le_antisymm (hq.2.2.2.trans hsame.le) hq.2.2.1
    exact mem_graphRegion_of_mem_closedGraphRegion_of_not_mem_graphOver hq
      ⟨hleft, hright⟩ (fun h => hnq (Or.inl h)) (fun h => hnq (Or.inr h))
  constructor
  · intro hbounded
    by_contra hnotU
    have hzK : z ∈ Kᶜ := fun hK => hnotU (hKU z hK hz)
    have hsub : Kᶜ ⊆ connectedComponentIn Bᶜ z :=
      (isPathConnected_compl_closedGraphRegion hab hf hg hfg).isConnected.isPreconnected.subset_connectedComponentIn
        hzK (Set.compl_subset_compl.mpr hBK)
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (hbounded.subset hsub)
    obtain ⟨q, hq, hqR⟩ := exists_norm_gt_compl_closedGraphRegion hf hg hfg R
    exact hqR.not_ge (hR q hq)
  · intro hzU
    have hopen : IsOpen U := isOpen_graphRegion hf hg
    have hfront : frontier U ⊆ B :=
      frontier_graphRegion_subset_of_endpoint_eq hf hg ha hb
    have hsub : connectedComponentIn Bᶜ z ⊆ U := by
      apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hopen
        ⟨z, mem_connectedComponentIn hz, hzU⟩
      rintro q ⟨hcl, hcomp⟩
      by_contra hnq
      have hfr : q ∈ frontier U := by
        rw [frontier, hopen.interior_eq]
        exact ⟨hcl, hnq⟩
      exact (connectedComponentIn_subset Bᶜ z hcomp) (hfront hfr)
    exact (isBounded_graphRegion hf hg hfg).subset hsub

/-- Helper toward Lemma 5.6: for two continuous graphs with common
endpoints, bounded complementary components lie between their pointwise
minimum and maximum. This version permits the two graphs to cross. -/
theorem isBounded_connectedComponentIn_compl_graphOver_union_iff_min_max
    {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (ha : f a = g a) (hb : f b = g b)
    {z : ℂ} (hz : z ∉ graphOver a b f ∪ graphOver a b g) :
    Bornology.IsBounded
        (connectedComponentIn (graphOver a b f ∪ graphOver a b g)ᶜ z) ↔
      z ∈ graphRegion a b (fun x => min (f x) (g x)) (fun x => max (f x) (g x)) := by
  have hgraphs :
      graphOver a b (fun x => min (f x) (g x)) ∪
        graphOver a b (fun x => max (f x) (g x)) =
      graphOver a b f ∪ graphOver a b g := by
    ext q
    simp only [graphOver, Set.mem_union, Set.mem_ofPred_eq]
    by_cases hq : f q.re ≤ g q.re
    · rw [min_eq_left hq, max_eq_right hq]
    · rw [min_eq_right (le_of_not_ge hq), max_eq_left (le_of_not_ge hq)]
      exact or_comm
  have hz' : z ∉ graphOver a b (fun x => min (f x) (g x)) ∪
      graphOver a b (fun x => max (f x) (g x)) := by
    rw [hgraphs]
    exact hz
  have ha' : min (f a) (g a) = max (f a) (g a) := by
    rw [ha, min_self, max_self]
  have hb' : min (f b) (g b) = max (f b) (g b) := by
    rw [hb, min_self, max_self]
  have hiff := isBounded_connectedComponentIn_compl_graphOver_union_iff hab
    (f := fun x => min (f x) (g x)) (g := fun x => max (f x) (g x))
    (continuous_min.comp_continuousOn (hf.prodMk hg))
    (continuous_max.comp_continuousOn (hf.prodMk hg))
    (fun x _ => min_le_max) ha' hb' hz'
  rw [hgraphs] at hiff
  exact hiff

/-- Helper toward Lemma 5.6: the geometric exterior-boundary edge is the
closed seam graph between its two hit-indexed vertices. This includes
boundary edges missing from the directed map. -/
theorem m0CutBoundaryEdgeTrace_eq_graphOver
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (k : ℤ) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0
        (boundaryOuterEdge (shiftedStream W 0) h k, false))).image =
      graphOver (seamX (shiftedStream W 0) h (H.1 0) k)
        (seamX (shiftedStream W 0) h (H.1 0) (k + 1))
        (seamFun (shiftedStream W 0) h (H.1 0)) := by
  let w := shiftedStream W 0
  let G0 := monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)
  rw [WholePlanePastGlueM0Restriction.restrict_arc]
  have hflip : (G0.arc (futureMapBoundaryDart w h k)).image =
      (G0.arc (boundaryOuterEdge w h k, false)).image :=
    G0.arc_image_flip (boundaryOuterEdge w h k, false)
  rw [← hflip]
  have hsections := seam_arc_vertical_sections w h (H.1 0) k
  have hheight {q : ℂ} (hq : q ∈ (G0.arc (futureMapBoundaryDart w h k)).image) :
      q.im = seamFun w h (H.1 0) q.re := by
    apply (Set.ext_iff.mp (seamFun_graph w h (H.1 0)) q).mpr
    exact Set.mem_iUnion.mpr ⟨k, hq⟩
  ext z
  constructor
  · intro hz
    exact ⟨(hsections.1 z hz).1, (hsections.1 z hz).2, hheight hz⟩
  · rintro ⟨hlo, hhi, hz⟩
    obtain ⟨q, ⟨hq, hqre⟩, _⟩ := hsections.2 z.re hlo hhi
    have heq : q = z := Complex.ext hqre
      ((hheight hq).trans ((congrArg (seamFun w h (H.1 0)) hqre).trans hz.symm))
    exact heq ▸ hq

/-- Helper toward Lemma 5.6: two continuous graph segments meeting at
their common abscissa concatenate to one continuous graph. Degenerate
segments are included. -/
theorem graphOver_union_exists_continuousOn_graph
    {a b c : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc b c))
    (hjoin : f b = g b) :
    ∃ l : ℝ → ℝ, ContinuousOn l (Set.Icc a c) ∧
      graphOver a c l = graphOver a b f ∪ graphOver b c g ∧
      l a = f a ∧ l c = g c := by
  let l : ℝ → ℝ := fun x => if x ≤ b then f x else g x
  have hl : ContinuousOn l (Set.Icc a c) := by
    apply ContinuousOn.if
    · intro x hx
      have hxb : x = b := Set.mem_singleton_iff.mp (frontier_Iic_subset b hx.2)
      exact hxb ▸ hjoin
    · apply hf.mono
      rintro x ⟨hx, hxl⟩
      have hxb : x ≤ b := by
        change x ∈ closure (Set.Iic b) at hxl
        rw [isClosed_Iic.closure_eq] at hxl
        exact hxl
      exact ⟨hx.1, hxb⟩
    · apply hg.mono
      rintro x ⟨hx, hxr⟩
      have hbx : b ≤ x := by
        change x ∈ closure {x : ℝ | ¬x ≤ b} at hxr
        simp only [not_le] at hxr
        change x ∈ closure (Set.Ioi b) at hxr
        rw [closure_Ioi] at hxr
        exact hxr
      exact ⟨hbx, hx.2⟩
  refine ⟨l, hl, ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨hza, hzc, hzl⟩
      by_cases hzb : z.re ≤ b
      · exact Or.inl ⟨hza, hzb, by simpa only [l, ite_eq_left hzb] using hzl⟩
      · exact Or.inr ⟨(le_of_not_ge hzb), hzc,
          by simpa only [l, ite_eq_right hzb] using hzl⟩
    · rintro (⟨hza, hzb, hzf⟩ | ⟨hbz, hzc, hzg⟩)
      · exact ⟨hza, hzb.trans hbc, by simpa only [l, ite_eq_left hzb] using hzf⟩
      · refine ⟨hab.trans hbz, hzc, ?_⟩
        by_cases hzb : z.re ≤ b
        · have heq : z.re = b := le_antisymm hzb hbz
          simpa only [l, heq, hjoin, ite_self] using hzg
        · simpa only [l, ite_eq_right hzb] using hzg
  · exact ite_eq_left hab
  · by_cases hcb : c ≤ b
    · have heq : c = b := le_antisymm hcb hbc
      simp only [l, heq, hjoin, ite_self]
    · exact ite_eq_right hcb

/-- Helper toward Lemma 5.6: the actual finite slice boundary is a union
of two continuous graphs with common endpoints. One graph is the earlier
geodesic segment; the other concatenates the geometric exterior edge and
the later segment. No ordering of the two graphs is asserted here. -/
theorem m0CutGeodesicSliceBoundaryTrace_exists_graphs
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    let x := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
    let c := ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re
    ∃ f g : ℝ → ℝ,
      ContinuousOn f (Set.Icc x c) ∧ ContinuousOn g (Set.Icc x c) ∧
      f x = g x ∧ f c = g c ∧
      graphOver x c g = m0CutGeodesicSegmentTrace hp (P (k - 1)) a ∧
      graphOver x c f = m0CutGeodesicSegmentTrace hp (P k) b ∪
        ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0
            (boundaryOuterEdge (shiftedStream W 0) h (k - 1), false))).image ∧
      m0CutGeodesicSliceBoundaryTrace hp P k a b = graphOver x c f ∪ graphOver x c g := by
  dsimp only
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let x := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  let y := seamX (shiftedStream W 0) h (H.1 0) k
  let v := G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)
  let c := v.re
  let s := seamFun (shiftedStream W 0) h (H.1 0)
  have hroot (j : ℤ) : G.pos
      (wholePlaneVertexι W 0 ((P j).codePath.initial 0).1.id) =
        (⟨seamX (shiftedStream W 0) h (H.1 0) j,
          s (seamX (shiftedStream W 0) h (H.1 0) j)⟩ : ℂ) := by
    rw [m0Geodesic_pos_runZero hp, m0Geodesic_initial_zero]
    exact boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) j
  have hroot_re (j : ℤ) : (G.pos
      (wholePlaneVertexι W 0 ((P j).codePath.initial 0).1.id)).re =
        seamX (shiftedStream W 0) h (H.1 0) j := by
    have hh := congrArg Complex.re (hroot j)
    exact hh
  have hmeet : v = G.pos (wholePlaneVertexι W 0 ((P k).codePath.initial b).1.id) :=
    congrArg (fun q : PresentVertex (shiftedStream W 0) =>
      G.pos (wholePlaneVertexι W 0 q.id))
      (m0Cut_least_edge_coalescence_initial_vertex_eq P k hab)
  have hmeet_re : (G.pos (wholePlaneVertexι W 0 ((P k).codePath.initial b).1.id)).re = c :=
    (congrArg Complex.re hmeet).symm
  obtain ⟨g, hg, hgraph⟩ := m0CutGeodesicSegmentTrace_exists_graph hp (P (k - 1)) a
  rw [hroot_re (k - 1)] at hg hgraph
  obtain ⟨q, hq, hqgraph⟩ := m0CutGeodesicSegmentTrace_exists_graph hp (P k) b
  rw [hroot_re k, hmeet_re] at hq hqgraph
  have hxy : x ≤ y := (seamX_strictMono (shiftedStream W 0) h (H.1 0)
    (show k - 1 < k by omega)).le
  have hyc : y ≤ c := by
    have hmono := (m0CutGeodesic_vertex_re_strictMono hp (P k)).monotone (Nat.zero_le b)
    rw [hroot_re k, hmeet_re] at hmono
    exact hmono
  have hstart : G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial 0).1.id) ∈
      m0CutGeodesicSegmentTrace hp (P (k - 1)) a := Or.inl rfl
  rw [hgraph, hroot (k - 1)] at hstart
  have hga : g x = s x := hstart.2.2.symm
  have hqstart : G.pos (wholePlaneVertexι W 0 ((P k).codePath.initial 0).1.id) ∈
      m0CutGeodesicSegmentTrace hp (P k) b := Or.inl rfl
  rw [hqgraph, hroot k] at hqstart
  have hqy : q y = s y := hqstart.2.2.symm
  have hend := m0CutGeodesicSegmentTrace_endpoint_mem hp (P (k - 1)) a
  rw [hgraph] at hend
  have hgc : g c = v.im := hend.2.2.symm
  have hqend := m0CutGeodesicSegmentTrace_endpoint_mem hp (P k) b
  rw [hqgraph, ← hmeet] at hqend
  have hqc : q c = v.im := hqend.2.2.symm
  obtain ⟨f, hf, hfgraph, hfx, hfc⟩ := graphOver_union_exists_continuousOn_graph hxy hyc
    (seamFun_continuous (shiftedStream W 0) h (H.1 0)).continuousOn hq hqy.symm
  have hboundary := m0CutBoundaryEdgeTrace_eq_graphOver (H := H) (h := h) hp (k - 1)
  have hidx : k - 1 + 1 = k := by omega
  rw [hidx] at hboundary
  have hflocal : graphOver x c f = m0CutGeodesicSegmentTrace hp (P k) b ∪
      ((G.arc (wholePlaneDartι W 0
        (boundaryOuterEdge (shiftedStream W 0) h (k - 1), false))).image) := by
    rw [hqgraph, hboundary, hfgraph]
    dsimp only [x, y]
    exact Set.union_comm _ _
  refine ⟨f, g, hf, hg, hfx.trans hga.symm, hfc.trans (hqc.trans hgc.symm),
    hgraph.symm, hflocal, ?_⟩
  change (m0CutGeodesicSegmentTrace hp (P (k - 1)) a ∪
      m0CutGeodesicSegmentTrace hp (P k) b) ∪
        ((G.arc (wholePlaneDartι W 0
          (boundaryOuterEdge (shiftedStream W 0) h (k - 1), false))).image) = _
  rw [hgraph, hqgraph, hboundary, hfgraph]
  dsimp only [x, y, c, v, G]
  ac_rfl

/-- Helper toward Lemma 5.6: finite enclosure is exactly containment of a
future face between the pointwise minimum and maximum of two continuous
graphs describing the actual finite boundary. This does not identify that
unoriented region with the candidate's right/left whole-side overlap. -/
theorem m0CutFaceEnclosedBySegments_exists_graph_region_characterization
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    let x := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
    let c := ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re
    ∃ f g : ℝ → ℝ,
      ContinuousOn f (Set.Icc x c) ∧ ContinuousOn g (Set.Icc x c) ∧
      f x = g x ∧ f c = g c ∧
      m0CutGeodesicSliceBoundaryTrace hp P k a b = graphOver x c f ∪ graphOver x c g ∧
      ∀ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
        m0CutFaceEnclosedBySegments hp P k a b F ↔
          F.val ⊆ m0GeodesicAmbientRegion W H h ∧
            F.val ⊆ graphRegion x c (fun u => min (f u) (g u))
              (fun u => max (f u) (g u)) := by
  dsimp only
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let x := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  let c := (G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re
  obtain ⟨f, g, hf, hg, ha, hc, _, _, hB⟩ :=
    m0CutGeodesicSliceBoundaryTrace_exists_graphs hp P k a b hab
  have hxc : x ≤ c := by
    have hroot : G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial 0).1.id) ∈
        m0CutGeodesicSliceBoundaryTrace hp P k a b := Or.inl (Or.inl (Or.inl rfl))
    rw [hB] at hroot
    rcases hroot with hr | hr <;> exact hr.1.trans hr.2.1
  refine ⟨f, g, hf, hg, ha, hc, hB, ?_⟩
  intro F
  have hzB {z : ℂ} (hz : z ∈ F.val) : z ∉ graphOver x c f ∪ graphOver x c g := by
    rw [← hB]
    intro hzb
    exact G.face_subset_compl F hz
      (m0CutGeodesicSliceBoundaryTrace_subset_drawing hp P k a b hzb)
  constructor
  · rintro ⟨hambient, hbounded⟩
    refine ⟨hambient, fun z hz => ?_⟩
    apply (isBounded_connectedComponentIn_compl_graphOver_union_iff_min_max
      hxc hf hg ha hc (hzB hz)).mp
    rw [← hB]
    exact hbounded z hz
  · rintro ⟨hambient, hregion⟩
    refine ⟨hambient, fun z hz => ?_⟩
    rw [hB]
    exact (isBounded_connectedComponentIn_compl_graphOver_union_iff_min_max
      hxc hf hg ha hc (hzB hz)).mpr (hregion hz)

/-- Helper toward Lemma 5.6: the named side region `m0GeodesicSideOpenRegion`
for the left side (not asserted to be open; see M0GeodesicSideCarrier.lean:186-212)
consists exactly
of ambient points west of the root and points strictly above the trace at
their abscissa. The proper-ray escape condition excludes points beyond a
finite right endpoint from this component. -/
theorem m0CutGeodesicLeftOpen_iff_west_or_above_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (z : ℂ) :
    z ∈ m0GeodesicLeftOpen hp Q ↔
      z ∈ m0GeodesicAmbientRegion W H h ∧
        (z.re < seamX (shiftedStream W 0) h (H.1 0) j ∨
          ∃ y ∈ m0GeodesicTrace hp Q, y.re = z.re ∧ y.im < z.im) := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let x₀ := seamX (shiftedStream W 0) h (H.1 0) j
  let s := seamFun (shiftedStream W 0) h (H.1 0)
  obtain ⟨X, g, _, hg, hgraph, hescape⟩ := m0GeodesicTrace_properGraphRay hp Q
  have hroot : (⟨x₀, s x₀⟩ : ℂ) ∈ m0GeodesicTrace hp Q := by
    have hh := m0Geodesic_root_pos_mem_trace hp Q
    rw [(m0CutData W H h hLL).x_eq h hLL j, m0Geodesic_pos_runZero hp] at hh
    rw [boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) j] at hh
    exact hh
  have hrootgraph := hroot
  rw [hgraph] at hrootgraph
  let U : Set ℂ := {q | q.re ≤ x₀} ∪
    {q | q.re ∈ rayDomain x₀ X ∧ g q.re ≤ q.im}
  let D : Set ℂ := {q | x₀ ≤ q.re ∧
    (q.re ∈ rayDomain x₀ X → q.im ≤ g q.re)}
  have hU : IsClosed U :=
    (isClosed_Iic.preimage Complex.continuous_re).union
      (gluing_graphRay_epigraph_closed hg hescape)
  have hD : IsClosed D := gluing_graphRay_hypograph_closed hg
  have hcover (q : ℂ) : q ∈ U ∨ q ∈ D := by
    by_cases hqx : q.re ≤ x₀
    · exact Or.inl (Or.inl hqx)
    · by_cases hqd : q.re ∈ rayDomain x₀ X
      · rcases le_total (g q.re) q.im with hqg | hqg
        · exact Or.inl (Or.inr ⟨hqd, hqg⟩)
        · exact Or.inr ⟨(le_of_not_ge hqx), fun _ => hqg⟩
      · exact Or.inr ⟨(le_of_not_ge hqx), fun hh => (hqd hh).elim⟩
  have hcross {q : ℂ} (hqa : q ∈ m0GeodesicAmbientRegion W H h)
      (hqU : q ∈ U) (hqD : q ∈ D) : q ∈ m0GeodesicTrace hp Q := by
    rw [hgraph]
    rcases hqU with hqx | hqg
    · have heq : q.re = x₀ := le_antisymm hqx hqD.1
      have hdom : q.re ∈ rayDomain x₀ X := by
        rw [heq]
        exact hrootgraph.1
      refine ⟨hdom, le_antisymm (hqD.2 hdom) ?_⟩
      have hlow : s q.re ≤ q.im := hqa
      rw [heq, ← hrootgraph.2]
      simpa only [heq] using hlow
    · exact ⟨hqg.1, le_antisymm (hqD.2 hqg.1) hqg.2⟩
  constructor
  · intro hz
    have hza := (m0GeodesicLeftOpen_subset hp Q hz).1
    have hnotD : z ∉ D := by
      intro hzD
      let p := G.pos ((m0CutData W H h hLL).x (j - 1))
      have hpL : p ∈ m0GeodesicLeftOpen hp Q :=
        m0Geodesic_previous_pos_mem_leftOpen hp Q
      have hpU : p ∈ U := by
        apply Or.inl
        dsimp [p, G]
        rw [(m0CutData W H h hLL).x_eq h hLL (j - 1), m0Geodesic_pos_runZero hp]
        exact (seamX_strictMono (shiftedStream W 0) h (H.1 0)
          (show j - 1 < j by omega)).le
      obtain ⟨q, hqL, hqU, hqD⟩ := isPreconnected_closed_iff.mp
        (show IsPreconnected (m0GeodesicLeftOpen hp Q) from isPreconnected_connectedComponentIn)
        U D hU hD (fun q _ => hcover q) ⟨p, hpL, hpU⟩ ⟨z, hz, hzD⟩
      have hq := m0GeodesicLeftOpen_subset hp Q hqL
      exact hq.2 (hcross hq.1 hqU hqD)
    have hzU : z ∈ U := (hcover z).resolve_right hnotD
    refine ⟨hza, ?_⟩
    by_cases hzx : z.re < x₀
    · exact Or.inl hzx
    · have hzd : z.re ∈ rayDomain x₀ X := by
        rcases hzU with hzw | hzg
        · have heq : z.re = x₀ := le_antisymm hzw (le_of_not_gt hzx)
          rw [heq]
          exact hrootgraph.1
        · exact hzg.1
      have hzg : g z.re < z.im := by
        have hnot : ¬ z.im ≤ g z.re := fun hle => hnotD ⟨hzd.1, fun _ => hle⟩
        exact lt_of_not_ge hnot
      exact Or.inr ⟨⟨z.re, g z.re⟩, hgraph ▸ ⟨hzd, rfl⟩, rfl, hzg⟩
  · rintro ⟨hza, hw | ⟨y, hy, hre, him⟩⟩
    · exact boundaryGluing_west_of_root_mem_leftOpen W h j longest hp Q hza hw
    · exact boundaryGluing_above_trace_mem_leftOpen W h j longest hp Q hy hre him

/-- Helper toward Lemma 5.6: a point of a geodesic trace is at or east
of its source root. -/
theorem m0CutGeodesicTrace_root_re_le
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    {z : ℂ} (hz : z ∈ m0GeodesicTrace hp Q) :
    seamX (shiftedStream W 0) h (H.1 0) j ≤ z.re := by
  obtain ⟨_, _, _, _, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp Q
  rw [hgraph] at hz
  exact hz.1.1

/-- Helper toward Lemma 5.6: after coalescence, each point of the later
trace is either in its finite segment or in the earlier whole trace.
Equality of geometric edge identities supplies the common-tail inclusion. -/
theorem m0CutGeodesicTrace_subset_segmentTrace_union_of_coalescence
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j l : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (R : M0CutInfiniteGeodesic W H h hLL l longest) (a b : ℕ)
    (hco : M0CutEdgeTailsCoalesce Q R a b) :
    m0GeodesicTrace hp R ⊆ m0CutGeodesicSegmentTrace hp R b ∪ m0GeodesicTrace hp Q := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  by_cases hib : i < b
  · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hib⟩, hi⟩))
  · have hbi : b ≤ i := by omega
    have hidx : b + (i - b) = i := by omega
    have heq := wholePlaneEdgeι_injective W 0 (hco (i - b))
    rw [hidx] at heq
    right
    apply m0Geodesic_arc_subset_trace hp Q (a + (i - b))
    change z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (R.codePath.edge i, false))).image at hi
    rw [← heq] at hi
    exact hi

/-- Helper toward Lemma 5.6: the source root is the corresponding point
of the exterior seam graph in the glued drawing. -/
theorem m0CutGeodesic_initial_zero_pos
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {j : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (Q.codePath.initial 0).1.id) =
        (⟨seamX (shiftedStream W 0) h (H.1 0) j,
          seamFun (shiftedStream W 0) h (H.1 0)
            (seamX (shiftedStream W 0) h (H.1 0) j)⟩ : ℂ) := by
  rw [m0Geodesic_pos_runZero hp, m0Geodesic_initial_zero]
  exact boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) j

/-- Helper toward Lemma 5.6: a face represented by the candidate slice
is enclosed by the literal finite boundary. This is the candidate-to-enclosure
direction; it requires no planar-leftmost premise. -/
theorem m0CutFaceEnclosedBySegments_of_representsFace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutGeodesicSliceRepresentsFace hp P k a b hab F →
      m0CutFaceEnclosedBySegments hp P k a b F := by
  intro hrep
  obtain ⟨hrall, hlall⟩ := (m0CutGeodesicSliceRepresentsFace_iff_side_regions
    hp P k a b hab F).mp hrep
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let x := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  let y := seamX (shiftedStream W 0) h (H.1 0) k
  let c := (G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id)).re
  let s := seamFun (shiftedStream W 0) h (H.1 0)
  obtain ⟨f, g, hf, hg, ha, hc, hG, hL, hB⟩ :=
    m0CutGeodesicSliceBoundaryTrace_exists_graphs hp P k a b hab
  have hambient : F.val ⊆ m0GeodesicAmbientRegion W H h := fun z hz => (hrall hz).1
  obtain ⟨F0, hF0, hFF0⟩ := m0CutFace_exists_runZero_face hp F hambient
  obtain ⟨z, hzcompl, hFcomp⟩ := F.property
  have hzF : z ∈ F.val := hFcomp ▸ mem_connectedComponentIn hzcompl
  have hr := hrall hzF
  have hl := hlall hzF
  have hstrict : s z.re < z.im :=
    boundedFace_subset_upper (shiftedStream W 0) h (H.1 0) F0 hF0 (hFF0 ▸ hzF)
  have hzold : z ∉ m0GeodesicTrace hp (P (k - 1)) := fun hz =>
    G.face_subset_compl F hzF (m0GeodesicTrace_subset_drawing hp (P (k - 1)) hz)
  have hrootOld : (⟨x, s x⟩ : ℂ) ∈ m0GeodesicTrace hp (P (k - 1)) := by
    have hh := m0Geodesic_initial_pos_mem_trace hp (P (k - 1)) 0
    rw [m0CutGeodesic_initial_zero_pos] at hh
    exact hh
  have hmeet : G.pos (wholePlaneVertexι W 0 ((P k).codePath.initial b).1.id) =
      G.pos (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id) :=
    (congrArg (fun q : PresentVertex (shiftedStream W 0) =>
      G.pos (wholePlaneVertexι W 0 q.id))
      (m0Cut_least_edge_coalescence_initial_vertex_eq P k hab)).symm
  have hnewend : (G.pos (wholePlaneVertexι W 0 ((P k).codePath.initial b).1.id)).re = c :=
    congrArg Complex.re hmeet
  have hyc : y ≤ c := by
    have hh := (m0CutGeodesic_vertex_re_strictMono hp (P k)).monotone (Nat.zero_le b)
    rw [m0CutGeodesic_initial_zero_pos, hnewend] at hh
    exact hh
  have hnewside := (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp (P k) z).mp hl
  have hxz : x < z.re := by
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hw | heq
    · exact hr.2 (subset_closure
        (boundaryGluing_west_of_root_mem_leftOpen W h (k - 1) longest hp (P (k - 1)) hr.1 hw))
    · apply hr.2
      apply subset_closure
      apply boundaryGluing_above_trace_mem_leftOpen W h (k - 1) longest hp (P (k - 1))
        hrootOld heq.symm
      change s x < z.im
      rw [← heq]
      exact hstrict
  have hzc : z.re < c := by
    rcases hnewside.2 with hw | ⟨p, hpT, hpre, hpim⟩
    · exact hw.trans_le hyc
    · by_contra hn
      have hcp : c ≤ p.re := by rw [hpre]; exact le_of_not_gt hn
      have hpOld : p ∈ m0GeodesicTrace hp (P (k - 1)) := by
        rcases m0CutGeodesicTrace_subset_segmentTrace_union_of_coalescence hp
            (P (k - 1)) (P k) a b hab.1 hpT with hpSeg | hpOld
        · have hpL : p ∈ graphOver x c f := by rw [hL]; exact Or.inl hpSeg
          have hpc : p.re = c := le_antisymm hpL.2.1 hcp
          have hpG : p ∈ graphOver x c g :=
            ⟨hpL.1, hpL.2.1, hpL.2.2.trans (by rw [hpc, hc])⟩
          apply m0CutGeodesicSegmentTrace_subset_trace hp (P (k - 1)) a
          rw [← hG]
          exact hpG
        · exact hpOld
      exact hr.2 (subset_closure
        (boundaryGluing_above_trace_mem_leftOpen W h (k - 1) longest hp (P (k - 1))
          hpOld hpre hpim))
  have hpOld : (⟨z.re, g z.re⟩ : ℂ) ∈ m0GeodesicTrace hp (P (k - 1)) := by
    apply m0CutGeodesicSegmentTrace_subset_trace hp (P (k - 1)) a
    rw [← hG]
    exact ⟨hxz.le, hzc.le, rfl⟩
  have hupper : z.im < g z.re := by
    have hle : z.im ≤ g z.re := le_of_not_gt (fun him => hr.2 (subset_closure
      (boundaryGluing_above_trace_mem_leftOpen W h (k - 1) longest hp (P (k - 1))
        hpOld rfl him)))
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hzold
    have heqpoint : z = (⟨z.re, g z.re⟩ : ℂ) := Complex.ext rfl heq
    rw [heqpoint]
    exact hpOld
  have hlower : f z.re < z.im := by
    rcases hnewside.2 with hw | ⟨p, hpT, hpre, hpim⟩
    · have hpL : (⟨z.re, f z.re⟩ : ℂ) ∈ graphOver x c f := ⟨hxz.le, hzc.le, rfl⟩
      rw [hL] at hpL
      rcases hpL with hpSeg | hpEdge
      · have hh := m0CutGeodesicTrace_root_re_le hp (P k)
          (m0CutGeodesicSegmentTrace_subset_trace hp (P k) b hpSeg)
        exact False.elim (hw.not_ge hh)
      · have hboundary := m0CutBoundaryEdgeTrace_eq_graphOver (H := H) (h := h) hp (k - 1)
        have hidx : k - 1 + 1 = k := by omega
        rw [hidx] at hboundary
        rw [hboundary] at hpEdge
        have hfs : f z.re = s z.re := hpEdge.2.2
        rw [hfs]
        exact hstrict
    · have hpSeg : p ∈ m0CutGeodesicSegmentTrace hp (P k) b := by
        rw [m0CutGeodesicSegmentTrace_eq_trace_inter_re_le]
        refine ⟨hpT, ?_⟩
        change p.re ≤ (G.pos (wholePlaneVertexι W 0 ((P k).codePath.initial b).1.id)).re
        rw [hnewend, hpre]
        exact hzc.le
      have hpL : p ∈ graphOver x c f := by rw [hL]; exact Or.inl hpSeg
      rw [hpL.2.2, hpre] at hpim
      exact hpim
  have hfg : f z.re ≤ g z.re := hlower.le.trans hupper.le
  have hregion : z ∈ graphRegion x c (fun u => min (f u) (g u))
      (fun u => max (f u) (g u)) :=
    ⟨hxz, hzc, by simpa only [min_eq_left hfg] using hlower,
      by simpa only [max_eq_right hfg] using hupper⟩
  have hzB : z ∉ graphOver x c f ∪ graphOver x c g := by
    rw [← hB]
    exact fun hzb => G.face_subset_compl F hzF
      (m0CutGeodesicSliceBoundaryTrace_subset_drawing hp P k a b hzb)
  have hbounded := (isBounded_connectedComponentIn_compl_graphOver_union_iff_min_max
    (hxz.le.trans hzc.le) hf hg ha hc hzB).mpr hregion
  rw [← hB] at hbounded
  exact (m0CutFaceEnclosedBySegments_iff_exists hp P k a b F).mpr
    ⟨hambient, z, hzF, hbounded⟩













































end DirectedDistances.PaperProofs.Section5
