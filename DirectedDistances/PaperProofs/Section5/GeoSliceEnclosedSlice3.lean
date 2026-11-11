/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice2

/-! Retained overlap faces and finite face-boundary slit chains. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: every edge bordering a retained face of a
side belongs to that closed side, including edges of the geodesic itself. -/
theorem m0Geodesic_side_edge_of_bordering_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (d : ℕ × Bool) (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp P s)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d) F) :
    d.1 ∈ m0GeodesicSideEdges hp P s := by
  by_cases he : d.1 ∈ m0GeodesicEdges P
  · have hm := m0GeodesicEdges_subset_both hp P he
    cases s with
    | left => exact hm.1
    | right => exact hm.2
  · have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := by
      intro z hz
      cases s with
      | left => exact (m0GeodesicLeftOpen_subset hp P (hF hz)).1
      | right => exact (hF hz).1
    exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P
      he d.2 F hFR hb s).mpr hF

/-- Helper toward Lemma 5.6: every overlap edge off the preceding ray
borders a retained face lying in both required open sides. The forward face
also works when the edge belongs to the current ray. -/
theorem m0GeodesicLeftSide_off_ray_edge_has_overlap_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (e : ℕ) (heL : e ∈ m0GeodesicSideEdges hp (P k) .left)
    (heR : e ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (hoff : e ∉ m0GeodesicEdges (P (k - 1))) :
    ∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (e, false)) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right := by
  obtain ⟨F, hFR, hb⟩ := boundaryGluing_retained_borderingFace_exists W h hp e
  refine ⟨F, hb, ?_, ?_⟩
  · by_cases he : e ∈ m0GeodesicEdges (P k)
    · obtain ⟨n, hn⟩ := he
      apply boundaryGluing_forward_seam_face_left W h k longest hp (P k) n F hFR
      simpa only [m0GeodesicSeam, hn] using hb
    · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp (P k)
        he false F hFR hb .left).mp heL
  · exact (boundaryGluing_sideEdges_iff_borderingFace W h (k - 1) longest hp
      (P (k - 1)) hoff false F hFR hb .right).mp heR

/-- Helper toward Lemma 5.6: a retained left-face dart has a retained
successor dart and therefore an actual intrinsic face step. -/
theorem m0GeodesicLeftSide_bordering_face_has_successor
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .left).edges})
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp P .left)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F) :
    ∃ e : GeometricSideCell (m0GeodesicSide hp P .left),
      geometricSideRelation (m0GeodesicSide hp P .left) .faceNext (.inr d) e := by
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h :=
    fun z hz => (m0GeodesicLeftOpen_subset hp P (hF hz)).1
  have hb' := m0Geodesic_retained_face_succ_borders hp F hFR d.val hb
  have he := m0Geodesic_side_edge_of_bordering_face hp P .left _ F hF hb'
  exact ⟨.inr ⟨kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d.val, he⟩,
    ⟨⟨F, hb, hF⟩, rfl⟩⟩

/-- Helper toward Lemma 5.6: two darts bordering one retained left face
are equal or joined by one slit step. Each retained face is a triangle;
the face steps do not cross the ray, even along a ray edge. -/
theorem m0GeodesicLeftSide_common_face_eq_or_slit_step
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (v q : ℕ → GeometricSideCell (m0GeodesicSide hp P .left))
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .left).edges})
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp P .left)
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (he : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 e.val) F) :
    d = e ∨ geometricSide_slit_step (m0GeodesicSide hp P .left) v q
      (.inr d) (.inr e) := by
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h :=
    fun z hz => (m0GeodesicLeftOpen_subset hp P (hF hz)).1
  obtain ⟨F0, hF0, hval⟩ := m0Geodesic_retained_face_runZero hp F hFR
  obtain ⟨j, hj⟩ := (boundedFace_iff_creation_orbit (shiftedStream W 0)
    (H.1 0) h F0).mp hF0
  have hmem (a : ℕ × Bool)
      (ha : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 a) F) :
      a ∈ stageTriangleDartList (shiftedStream W 0) j := by
    have ha0 := (PLDrawing.dartBorders_congr _ _ F0 F
      (WholePlanePastGlueM0Restriction.restrict_arc W h hp H a) hval).mp ha
    exact (cap_border_iff (shiftedStream W 0) (H.1 0) j a).mp (hj ▸ ha0)
  have htriangle (x y : ℕ × Bool)
      (hx : x ∈ stageTriangleDartList (shiftedStream W 0) j)
      (hy : y ∈ stageTriangleDartList (shiftedStream W 0) j) :
      x = y ∨ kmswInfFaceSucc (shiftedStream W 0) (H.1 0) x = y ∨
        kmswInfFaceSucc (shiftedStream W 0) (H.1 0) y = x := by
    let t := stageTriangleDartTriple (shiftedStream W 0) j
    obtain ⟨h1, h2, h3, _⟩ :=
      capFace_triangle_darts_sameCycle (shiftedStream W 0) (H.1 0) j
    change x ∈ [t.1, t.2.1, t.2.2] at hx
    change y ∈ [t.1, t.2.1, t.2.2] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h3)
    · exact Or.inr (Or.inr h1)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h2)
    · exact Or.inl rfl
  rcases htriangle d.val e.val (hmem d.val hd) (hmem e.val he) with hde | hde | hed
  · exact Or.inl (Subtype.ext hde)
  · exact Or.inr (Or.inl ⟨⟨F, hd, hF⟩, hde⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨F, he, hF⟩, hed⟩))

/-- Helper toward Lemma 5.6: any two darts of one retained left face
have a finite slit chain, with no face-connectivity hypothesis. -/
theorem m0GeodesicLeftSide_common_face_slit_reaches
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (v q : ℕ → GeometricSideCell (m0GeodesicSide hp P .left))
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P .left).edges})
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp P .left)
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (he : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 e.val) F) :
    Relation.ReflTransGen (geometricSide_slit_step (m0GeodesicSide hp P .left) v q)
      (.inr d) (.inr e) := by
  rcases m0GeodesicLeftSide_common_face_eq_or_slit_step hp P v q d e F hF hd he with
    rfl | hstep
  · exact .refl
  · exact .single hstep

/-- Helper toward Lemma 5.6: at an off-ray vertex the incident edge has
exactly the same left-side label as the vertex, including boundary vertices. -/
theorem m0Geodesic_incident_off_ray_left_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (d : ℕ × Bool) (v : ℕ)
    (hinc : kmswLimitDartVertex (shiftedStream W 0) d = v)
    (hv : v ∉ m0GeodesicVertices Q) :
    d.1 ∉ m0GeodesicEdges Q ∧
      (d.1 ∈ m0GeodesicSideEdges hp Q .left ↔
        v ∈ m0GeodesicSideVertices hp Q .left) := by
  let z := (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
    (wholePlaneVertexι W 0 v)
  have hz : z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (d.1, false))).image := by
    simpa only [hinc] using m0Geodesic_dart_vertex_mem_arc hp d
  have hzQ : z ∉ m0GeodesicTrace hp Q :=
    fun hzQ => hv ((m0Geodesic_pos_mem_trace_iff hp Q v).mp hzQ)
  have he : d.1 ∉ m0GeodesicEdges Q := by
    rintro ⟨n, hn⟩
    apply hzQ
    apply m0Geodesic_arc_subset_trace hp Q n
    simpa only [hn, m0GeodesicSeam] using hz
  refine ⟨he, ?_⟩
  have hi := (boundaryGluing_sideEdges_iff_off_trace_point W h j longest hp Q
    he hz hzQ).1
  constructor
  · intro heL
    exact ⟨subset_closure (hi.mp heL), m0Geodesic_pos_mem_ambient hp v⟩
  · intro hvL
    exact hi.mpr (m0GeodesicLeftOpen_closure_inter_complement_subset hp Q
      ⟨hvL.1, hvL.2, hzQ⟩)

/-- Helper toward Lemma 5.6: every vertex in the closed left side has
an outgoing present edge retained in that side. A ray vertex uses its next
ray edge; an off-ray vertex uses the component incidence criterion. -/
theorem m0GeodesicLeftSide_vertex_has_outgoing_edge
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (v : ℕ) (hv : v ∈ m0GeodesicSideVertices hp P .left) :
    ∃ e : ℕ, EdgePresent (shiftedStream W 0) e ∧
      edgeWest (shiftedStream W 0) e = v ∧
      e ∈ m0GeodesicSideEdges hp P .left := by
  by_cases hvP : v ∈ m0GeodesicVertices P
  · obtain ⟨n, hn⟩ := hvP
    have he := P.codePath.edge_outgoing_at_initial (shiftedStream W 0) n
    exact ⟨P.codePath.edge n, he.1, he.2.trans hn,
      (m0GeodesicEdges_subset_both hp P ⟨n, rfl⟩).1⟩
  · obtain ⟨e, he, hev⟩ := uibot_allocated_vertex_outgoing
      (shiftedStream W 0) h.R_unbounded_below v
      (kmsw_vertex_allocated_of_finite_incidence (shiftedStream W 0) (H.1 0) v)
    exact ⟨e, he, hev,
      (m0Geodesic_incident_off_ray_left_iff hp P (e, false) v hev hvP).2.mpr hv⟩

/-- Helper toward Lemma 5.6: every overlap vertex off the preceding ray
is incident to an off-ray outgoing edge and a retained overlap face. Thus
both off-ray cell sorts reduce to retained overlap faces. -/
theorem m0GeodesicLeftSide_off_ray_vertex_has_overlap_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (v : ℕ) (hvL : v ∈ m0GeodesicSideVertices hp (P k) .left)
    (hvR : v ∈ m0GeodesicSideVertices hp (P (k - 1)) .right)
    (hoff : v ∉ m0GeodesicVertices (P (k - 1))) :
    ∃ (e : ℕ) (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face),
      EdgePresent (shiftedStream W 0) e ∧
      edgeWest (shiftedStream W 0) e = v ∧
      e ∈ m0GeodesicSideEdges hp (P k) .left ∧
      e ∉ m0GeodesicEdges (P (k - 1)) ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (e, false)) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right := by
  obtain ⟨e, he, hev, heL⟩ := m0GeodesicLeftSide_vertex_has_outgoing_edge hp (P k) v hvL
  obtain ⟨heoff, hi⟩ :=
    m0Geodesic_incident_off_ray_right_iff hp (P (k - 1)) (e, false) v hev hoff
  obtain ⟨F, hb, hFL, hFR⟩ :=
    m0GeodesicLeftSide_off_ray_edge_has_overlap_face hp P k e heL (hi.mpr hvR) heoff
  exact ⟨e, F, he, hev, heL, heoff, hb, hFL, hFR⟩

/-- Helper toward Lemma 5.6: retained left faces sharing an edge off the
preceding ray are slit-connected, for arbitrary bordering darts of the two
faces. This constructs the local dual-adjacency bridge. -/
theorem m0GeodesicLeftSide_adjacent_faces_slit_reaches
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges})
    (F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hG : G.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (he : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 e.val) G)
    (a : ℕ) (b c : Bool) (hoff : a ∉ m0GeodesicEdges (P (k - 1)))
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (a, b)) F)
    (hc : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (a, c)) G) :
    Relation.ReflTransGen
      (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain)) (.inr d) (.inr e) := by
  have haL := m0Geodesic_side_edge_of_bordering_face hp (P k) .left (a, b) F hF hb
  let db : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges} :=
    ⟨(a, b), haL⟩
  let dc : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges} :=
    ⟨(a, c), haL⟩
  have hdb := m0GeodesicLeftSide_common_face_slit_reaches hp (P k)
    (m0GeodesicSideAdjacentVertices hp P k hcontain)
    (m0GeodesicSideAdjacentDarts hp P k hcontain) d db F hF hd hb
  have hdce := m0GeodesicLeftSide_common_face_slit_reaches hp (P k)
    (m0GeodesicSideAdjacentVertices hp P k hcontain)
    (m0GeodesicSideAdjacentDarts hp P k hcontain) dc e G hG hc he
  apply hdb.trans
  apply Relation.ReflTransGen.trans (b := .inr dc) _ hdce
  by_cases hbc : b = c
  · have hde : db = dc := Subtype.ext (Prod.ext rfl hbc)
    rw [hde]
  · apply Relation.ReflTransGen.single
    apply Or.inr
    apply Or.inr
    apply Or.inl
    refine ⟨?_, ?_⟩
    · change (a, !b) = (a, c)
      have hnot : (!b) = c := by
        cases b <;> cases c
        · exact False.elim (hbc rfl)
        · rfl
        · rfl
        · exact False.elim (hbc rfl)
      exact Prod.ext rfl hnot
    · intro hray
      exact hoff ((m0GeodesicLeftSide_ray_dart_iff hp P k hcontain db).mp hray)

/-- Helper toward Lemma 5.6: a retained overlap face touching a preceding
ray edge supplies a right-face seed, and all its bordering darts are reached
from that seed. The ray orientation is forced by the actual right-side label. -/
theorem m0GeodesicLeftSide_ray_incident_overlap_face_reached
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges})
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (n : ℕ) (b : Bool)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 ((P (k - 1)).codePath.edge n, b)) F) :
    ∃ a, geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) a ∧
      Relation.ReflTransGen
        (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentVertices hp P k hcontain)
          (m0GeodesicSideAdjacentDarts hp P k hcontain)) a (.inr d) := by
  let q : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges} :=
    ⟨((P (k - 1)).codePath.edge n, b), (hcontain n).1⟩
  have hq := m0Geodesic_right_face_dart_invariant hp (P (k - 1)) (P k) q F hb hFR
  have hbtrue : b = true := by
    cases b with
    | false => exact False.elim (hq.2 n rfl)
    | true => rfl
  have hseed : geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) (.inr q) := by
    refine ⟨n, ?_, m0GeodesicLeftSide_bordering_face_has_successor hp (P k) q F hFL hb⟩
    change ((P (k - 1)).codePath.edge n, true) =
      ((P (k - 1)).codePath.edge n, b)
    exact Prod.ext rfl hbtrue.symm
  exact ⟨.inr q, hseed,
    m0GeodesicLeftSide_common_face_slit_reaches hp (P k)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) q d F hFL hb hd⟩

/-- Helper toward Lemma 5.6: every off-ray overlap cell is reached from
a dart bordering a retained overlap face. This constructs the reduction to
face exhaustion for both cell sorts; it does not assert that the face is
connected to a ray seed. -/
theorem m0GeodesicLeftSide_off_ray_cell_has_overlap_face_slit_reaches
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left))
    (hc : match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (hoff : match c with
      | .inl v => v.val ∉ m0GeodesicVertices (P (k - 1))
      | .inr d => d.val.1 ∉ m0GeodesicEdges (P (k - 1))) :
    ∃ (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
      (a : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}),
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 a.val) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
      Relation.ReflTransGen
        (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentVertices hp P k hcontain)
          (m0GeodesicSideAdjacentDarts hp P k hcontain)) (.inr a) c := by
  cases c with
  | inl v =>
    obtain ⟨e, F, _, hev, heL, _, hb, hFL, hFR⟩ :=
      m0GeodesicLeftSide_off_ray_vertex_has_overlap_face hp P k v.val v.property hc hoff
    refine ⟨F, ⟨(e, false), heL⟩, hb, hFL, hFR, .single ?_⟩
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    refine ⟨hev, ?_⟩
    intro hv
    exact hoff ((m0GeodesicLeftSide_ray_vertex_iff hp P k hcontain v).mp hv)
  | inr d =>
    obtain ⟨F, hb, hFL, hFR⟩ := m0GeodesicLeftSide_off_ray_edge_has_overlap_face
      hp P k d.val.1 d.property hc hoff
    let a : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges} :=
      ⟨(d.val.1, false), d.property⟩
    refine ⟨F, a, hb, hFL, hFR, ?_⟩
    cases hd : d.val.2 with
    | false =>
      have had : a = d := Subtype.ext (Prod.ext rfl hd.symm)
      rw [had]
    | true =>
      apply Relation.ReflTransGen.single
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨?_, ?_⟩
      · change (d.val.1, true) = d.val
        exact Prod.ext rfl hd.symm
      · intro ha
        exact hoff ((m0GeodesicLeftSide_ray_dart_iff hp P k hcontain a).mp ha)

end DirectedDistances.PaperProofs.Section5








































































































































































