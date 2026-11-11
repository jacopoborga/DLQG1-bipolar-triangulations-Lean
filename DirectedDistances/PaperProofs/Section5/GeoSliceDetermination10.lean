/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination9
import DirectedDistances.KMSW.UIBHBOTAssemblyFaceBorders

/-! Geometric trace tests for slices in a retained side. The realization maps
`pos` and `arc` are explicit inputs: the abstract `GeometricSideSubmap` does
not store an embedding. These tests use no ambient side-region predicate. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: the trace of a sequence of geometric edges,
using its supplied realization. Edge identity, including multiedges, is retained. -/
@[expose] def geometricSideEdgeTrace (arc : ℕ → Set ℂ) (q : ℕ → ℕ) : Set ℂ :=
  ⋃ n, arc (q n)

/-- Helper toward Lemma 5.6: the point is west of a trace's root, or above
the trace at the same abscissa. Only the side's endpoint map and the supplied
realization of its marked edges are used. No openness is asserted. -/
@[expose] def geometricSideAboveTrace (S : GeometricSideSubmap)
    (pos : ℕ → ℂ) (arc : ℕ → Set ℂ) (q : ℕ → ℕ) (z : ℂ) : Prop :=
  z.re < (pos (S.west (q 0))).re ∨
    ∃ y ∈ geometricSideEdgeTrace arc q, y.re = z.re ∧ y.im < z.im

/-- Helper toward Lemma 5.6: the closed region between two marked traces,
expressed by their geometry, without constructing either ambient side map. -/
@[expose] def geometricSideBetweenTraces (S : GeometricSideSubmap)
    (pos : ℕ → ℂ) (arc : ℕ → Set ℂ) (q r : ℕ → ℕ) (z : ℂ) : Prop :=
  ¬ geometricSideAboveTrace S pos arc q z ∧
    (z ∈ geometricSideEdgeTrace arc r ∨ geometricSideAboveTrace S pos arc r z)

/-- Helper toward Lemma 5.6: restrict the side's own vertices and edges
to the region between two marked traces, deleting the common tails at the
specified offsets. This is a geometric carrier, with the realization explicit. -/
@[expose] def geometricSideBetweenTraceCarrier (S : GeometricSideSubmap)
    (pos : ℕ → ℂ) (arc : ℕ → Set ℂ) (q r : ℕ → ℕ) (a b : ℕ) :
    GeometricSideSliceCarrier where
  vertices := {v | v ∈ S.vertices ∧ geometricSideBetweenTraces S pos arc q r (pos v)} \
    ({v | ∃ n, a < n ∧ v = S.west (q n)} ∪
      {v | ∃ n, b < n ∧ v = S.west (r n)})
  edges := {e | e ∈ S.edges ∧ ∀ z ∈ arc e, geometricSideBetweenTraces S pos arc q r z} \
    (Set.range (fun n => q (a + n)) ∪ Set.range (fun n => r (b + n)))

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: in the glued realization, the marked-edge
above-trace test agrees with membership in the named left component. -/
theorem m0CutGeodesic_aboveTrace_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (R : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (z : ℂ) (hz : z ∈ m0GeodesicAmbientRegion W H h) :
    geometricSideAboveTrace (m0GeodesicSide hp R s)
      (fun v => (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 v))
      (fun e => ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (e, false))).image) Q.codePath.edge z ↔
      z ∈ m0GeodesicLeftOpen hp Q := by
  have hroot :
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0
          (edgeWest (shiftedStream W 0) (Q.codePath.edge 0)))).re =
        seamX (shiftedStream W 0) h (H.1 0) j := by
    rw [(Q.codePath.edge_outgoing_at_initial (shiftedStream W 0) 0).2,
      m0CutGeodesic_initial_zero_pos hp Q]
  change (z.re < ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) (Q.codePath.edge 0)))).re ∨
    ∃ y ∈ m0GeodesicTrace hp Q,
    y.re = z.re ∧ y.im < z.im) ↔ _
  rw [hroot, m0CutGeodesicLeftOpen_iff_west_or_above_trace]
  exact ⟨fun ht => ⟨hz, ht⟩, fun ht => ht.2⟩

/-- Helper toward Lemma 5.6: the closed-left region consists of the trace
and its named left component, including every endpoint. -/
theorem m0CutGeodesic_mem_closedLeft_iff_trace_or_left
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) (z : ℂ) :
    z ∈ m0GeodesicSideRegion hp Q .left ↔
      z ∈ m0GeodesicTrace hp Q ∨ z ∈ m0GeodesicLeftOpen hp Q := by
  classical
  constructor
  · intro hz
    by_cases ht : z ∈ m0GeodesicTrace hp Q
    · exact Or.inl ht
    · exact Or.inr (m0GeodesicLeftOpen_closure_inter_complement_subset hp Q
        ⟨hz.1, hz.2, ht⟩)
  · rintro (ht | hl)
    · exact ((m0GeodesicSideRegion_inter hp Q).symm ▸ ht).1
    · exact ⟨subset_closure hl, (m0GeodesicLeftOpen_subset hp Q hl).1⟩

/-- Helper toward Lemma 5.6: the geometric between-traces test is exactly
the closed-right/closed-left overlap, at every ambient point. -/
theorem m0CutGeodesic_betweenTraces_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (j k : ℤ) (z : ℂ) (hz : z ∈ m0GeodesicAmbientRegion W H h) :
    geometricSideBetweenTraces (m0GeodesicSide hp (P k) .left)
      (fun v => (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 v))
      (fun e => ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (e, false))).image)
      (P (j - 1)).codePath.edge (P j).codePath.edge z ↔
      z ∈ m0GeodesicSideRegion hp (P (j - 1)) .right ∧
        z ∈ m0GeodesicSideRegion hp (P j) .left := by
  unfold geometricSideBetweenTraces
  rw [m0CutGeodesic_aboveTrace_iff hp (P (j - 1)) (P k) .left z hz,
    m0CutGeodesic_aboveTrace_iff hp (P j) (P k) .left z hz,
    m0CutGeodesic_mem_closedLeft_iff_trace_or_left hp (P j)]
  change (¬ z ∈ m0GeodesicLeftOpen hp (P (j - 1)) ∧ _) ↔
    ((z ∈ m0GeodesicAmbientRegion W H h ∧
      z ∉ m0GeodesicLeftOpen hp (P (j - 1))) ∧ _)
  exact ⟨fun ht => ⟨⟨hz, ht.1⟩, ht.2⟩, fun ht => ⟨ht.1.2, ht.2⟩⟩

/-- Helper toward Lemma 5.6: specialize the geometric construction to the
realization of a closed-left side and two supplied internal geodesic marks.
The embedding and the internal marks remain explicit mathematical data. -/
@[expose] noncomputable def m0CutRealizedLeftSideSlice
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (j k : ℤ) (a b : ℕ) : GeometricSideSliceCarrier :=
  geometricSideBetweenTraceCarrier (m0GeodesicSide hp (P k) .left)
    (fun v => (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 v))
    (fun e => ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).image)
    (P (j - 1)).codePath.edge (P j).codePath.edge a b

/-- Helper toward Lemma 5.6: the realized-side construction has exactly
the ambient slice vertices that belong to the supplied side. In particular,
this proves the reverse inclusion for every side index, without an ordering premise. -/
theorem m0CutRealizedLeftSideSlice_mem_vertices_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (j k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) (v : ℕ) :
    v ∈ (m0CutRealizedLeftSideSlice hp P j k a b).vertices ↔
      v ∈ (m0GeodesicSide hp (P k) .left).vertices ∧
        v ∈ (m0CutGeodesicSlice (hp := hp) P j a b hab).vertices := by
  have hwest (u : ℤ) (n : ℕ) :
      edgeWest (shiftedStream W 0) ((P u).codePath.edge n) =
        ((P u).codePath.initial n).1.id :=
    ((P u).codePath.edge_outgoing_at_initial (shiftedStream W 0) n).2
  unfold m0CutRealizedLeftSideSlice geometricSideBetweenTraceCarrier
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  rw [m0CutGeodesic_betweenTraces_iff hp P j k _ (m0Geodesic_pos_mem_ambient hp v),
    m0CutGeodesicSlice_mem_vertices_iff]
  change ((_ ∧ _) ∧ v ∉
    ({v | ∃ n, a < n ∧ v = edgeWest (shiftedStream W 0) ((P (j - 1)).codePath.edge n)} ∪
      {v | ∃ n, b < n ∧ v = edgeWest (shiftedStream W 0) ((P j).codePath.edge n)})) ↔ _
  simp only [hwest]
  exact ⟨fun ht => ⟨ht.1.1, ht.1.2, ht.2⟩,
    fun ht => ⟨⟨ht.1, ht.2.1⟩, ht.2.2⟩⟩

/-- Helper toward Lemma 5.6: the realized-side construction has exactly
the ambient slice edges that belong to the supplied side, preserving geometric
edge identity independently of directed presence. -/
theorem m0CutRealizedLeftSideSlice_mem_edges_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (j k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) (e : ℕ) :
    e ∈ (m0CutRealizedLeftSideSlice hp P j k a b).edges ↔
      e ∈ (m0GeodesicSide hp (P k) .left).edges ∧
        e ∈ (m0CutGeodesicSlice (hp := hp) P j a b hab).edges := by
  unfold m0CutRealizedLeftSideSlice geometricSideBetweenTraceCarrier
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  rw [m0CutGeodesicSlice_mem_edges_iff]
  have ht : (∀ z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).image,
      geometricSideBetweenTraces (m0GeodesicSide hp (P k) .left)
        (fun v => (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
          (wholePlaneVertexι W 0 v))
        (fun f => ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 (f, false))).image)
        (P (j - 1)).codePath.edge (P j).codePath.edge z) ↔
      e ∈ m0GeodesicSideEdges hp (P (j - 1)) .right ∧
        e ∈ m0GeodesicSideEdges hp (P j) .left := by
    constructor
    · intro hh
      exact ⟨fun z hz => ((m0CutGeodesic_betweenTraces_iff hp P j k z
        (m0Geodesic_arc_subset_ambient hp e hz)).1 (hh z hz)).1,
        fun z hz => ((m0CutGeodesic_betweenTraces_iff hp P j k z
        (m0Geodesic_arc_subset_ambient hp e hz)).1 (hh z hz)).2⟩
    · rintro ⟨hr, hl⟩ z hz
      exact (m0CutGeodesic_betweenTraces_iff hp P j k z
        (m0Geodesic_arc_subset_ambient hp e hz)).2 ⟨hr hz, hl hz⟩
  rw [ht]
  exact ⟨fun hh => ⟨hh.1.1, hh.1.2, hh.2⟩,
    fun hh => ⟨⟨hh.1, hh.2.1⟩, hh.2.2⟩⟩

/-- Helper toward Lemma 5.6: at its own upper cut, the geometric side
construction recovers both slice carriers exactly, including zero offsets.
This carrier statement does not need leftmostness or a probabilistic premise. -/
theorem m0CutRealizedLeftSideSlice_self_eq
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (j : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) :
    (m0CutRealizedLeftSideSlice hp P j j a b).vertices =
        (m0CutGeodesicSlice (hp := hp) P j a b hab).vertices ∧
      (m0CutRealizedLeftSideSlice hp P j j a b).edges =
        (m0CutGeodesicSlice (hp := hp) P j a b hab).edges := by
  constructor
  · ext v
    rw [m0CutRealizedLeftSideSlice_mem_vertices_iff hp P j j a b hab]
    exact ⟨And.right, fun hv =>
      ⟨((m0CutGeodesicSlice_mem_vertices_iff P j a b hab v).1 hv).1.2, hv⟩⟩
  · ext e
    rw [m0CutRealizedLeftSideSlice_mem_edges_iff hp P j j a b hab]
    exact ⟨And.right, fun he =>
      ⟨((m0CutGeodesicSlice_mem_edges_iff P j a b hab e).1 he).1.2, he⟩⟩

/-- Helper toward Lemma 5.6: a face is represented in a closed-left side
precisely when its point set lies in that side's named face region. The witness
uses only the side's face-successor relation and its actual bordering darts. -/
theorem m0GeodesicLeftSide_representsFace_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    (∃ d e : ℕ × Bool,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 d) F ∧
      (m0GeodesicSide hp Q .left).faceNext d e) ↔
      F.val ⊆ m0GeodesicLeftOpen hp Q := by
  constructor
  · rintro ⟨d, e, hdF, ⟨⟨F', hdF', hF'⟩, _⟩⟩
    have heq := (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders_face_unique
      _ _ _ hdF' hdF
    exact heq ▸ hF'
  · intro hF
    obtain ⟨d, hd⟩ := m0CutFace_exists_runZero_bordering_dart hp F
      (fun z hz => (m0GeodesicLeftOpen_subset hp Q (hF hz)).1)
    exact ⟨d, kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d, hd,
      ⟨⟨F, hd, hF⟩, rfl⟩⟩

/-- Helper toward Lemma 5.6: at ambient face points the between-traces
test selects exactly the two named face regions. Faces avoid both geodesic
traces, so the closed and face-region tests agree without an openness premise. -/
theorem m0CutGeodesic_face_betweenTraces_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (j k : ℤ)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    (∀ z ∈ F.val, geometricSideBetweenTraces (m0GeodesicSide hp (P k) .left)
      (fun v => (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
        (wholePlaneVertexι W 0 v))
      (fun e => ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (e, false))).image)
      (P (j - 1)).codePath.edge (P j).codePath.edge z) ↔
      F.val ⊆ m0GeodesicSideOpenRegion hp (P (j - 1)) .right ∧
        F.val ⊆ m0GeodesicSideOpenRegion hp (P j) .left := by
  have hnot (u : ℤ) {z : ℂ} (hz : z ∈ F.val) : z ∉ m0GeodesicTrace hp (P u) :=
    fun ht => (WholePlanePastGlueDrawing.glueDrawing W h hp H).face_subset_compl F hz
      (m0GeodesicTrace_subset_drawing hp (P u) ht)
  constructor
  · intro hh
    have hside z (hz : z ∈ F.val) :=
      (m0CutGeodesic_betweenTraces_iff hp P j k z (hF hz)).1 (hh z hz)
    constructor
    · intro z hz
      refine ⟨hF hz, ?_⟩
      intro hcl
      have ht : z ∈ m0GeodesicTrace hp (P (j - 1)) := by
        rw [← m0GeodesicSideRegion_inter hp (P (j - 1))]
        exact ⟨⟨hcl, hF hz⟩, (hside z hz).1⟩
      exact hnot (j - 1) hz ht
    · intro z hz
      exact ((m0CutGeodesic_mem_closedLeft_iff_trace_or_left hp (P j) z).1
        (hside z hz).2).resolve_left (hnot j hz)
  · rintro ⟨hr, hl⟩ z hz
    apply (m0CutGeodesic_betweenTraces_iff hp P j k z (hF hz)).2
    exact ⟨⟨(hr hz).1, fun hleft => (hr hz).2 (subset_closure hleft)⟩,
      ⟨subset_closure (hl hz), hF hz⟩⟩

/-- Helper toward Lemma 5.6: at the upper cut itself, represented side
faces between the two traces are precisely the faces enclosed by the finite
leftmost segments, using the proved identification from file 9. -/
theorem m0CutRealizedLeftSideSlice_self_faces_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (j : ℤ)
    (Tprev : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h (j - 1)))
    (Tnext : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h j))
    (hprev : Xdp.CutLeftmostXdp W H h hp hLL longest (j - 1) (P (j - 1)) Tprev)
    (hnext : Xdp.CutLeftmostXdp W H h hp hLL longest j (P j) Tnext)
    (a b : ℕ) (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutFaceEnclosedBySegments hp P j a b F ↔
      (∃ d e : ℕ × Bool,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 d) F ∧
        (m0GeodesicSide hp (P j) .left).faceNext d e) ∧
      (∀ z ∈ F.val, geometricSideBetweenTraces (m0GeodesicSide hp (P j) .left)
        (fun v => (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
          (wholePlaneVertexι W 0 v))
        (fun e => ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 (e, false))).image)
        (P (j - 1)).codePath.edge (P j).codePath.edge z) := by
  rw [m0CutGeodesicSlice_face_identification_of_leftmost hp P j Tprev Tnext
    hprev hnext a b hab F, m0GeodesicLeftSide_representsFace_iff,
    m0CutGeodesicSliceRepresentsFace_iff_side_regions]
  constructor
  · rintro ⟨hr, hl⟩
    exact ⟨hl, (m0CutGeodesic_face_betweenTraces_iff hp P j j F
      (fun z hz => (hr hz).1)).2 ⟨hr, hl⟩⟩
  · rintro ⟨hl, hbetween⟩
    exact (m0CutGeodesic_face_betweenTraces_iff hp P j j F
      (fun z hz => (m0GeodesicLeftOpen_subset hp (P j) (hl hz)).1)).1 hbetween

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section1

/-- Helper toward Lemma 5.6: almost surely, for every earlier slice and
later left side, the realized-side construction recovers exactly the vertices,
edges and represented faces. Both supplied geodesic marks lie inside that
side. The embedding and selection of the internal marks are still explicit;
this is not an abstract-side measurability or reconstruction theorem. -/
theorem m0Cut_ae_realizedLeftSideSlice_eq :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ j : ℤ, ∃ a b : ℕ,
          M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) ∧
        (∀ u k : ℤ, u ≤ k → ∀ n : ℕ,
          (P u).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
          ((P u).codePath.initial n).1.id ∈ (m0GeodesicSide hp (P k) .left).vertices) ∧
        (∀ j k : ℤ, j ≤ k → ∀ a b : ℕ,
          (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) →
          (m0CutRealizedLeftSideSlice hp P j k a b).vertices =
              (m0CutGeodesicSlice (hp := hp) P j a b hab).vertices ∧
          (m0CutRealizedLeftSideSlice hp P j k a b).edges =
              (m0CutGeodesicSlice (hp := hp) P j a b hab).edges ∧
          (∀ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
            m0CutFaceEnclosedBySegments hp P j a b F ↔
              (∃ d e : ℕ × Bool,
                (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
                  (wholePlaneDartι W 0 d) F ∧
                (m0GeodesicSide hp (P k) .left).faceNext d e) ∧
              (∀ z ∈ F.val,
                geometricSideBetweenTraces (m0GeodesicSide hp (P k) .left)
                  (fun v => (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
                    (wholePlaneVertexι W 0 v))
                  (fun e => ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
                    (wholePlaneDartι W 0 (e, false))).image)
                  (P (j - 1)).codePath.edge (P j).codePath.edge z))) := by
  filter_upwards [m0Cut_ae_geodesicSlice_left_right_side_containment] with W hW
  obtain ⟨H, h, hLL, hp, hselected⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, _, hc, hnest, _, hslice, _⟩ := hselected longest
  refine ⟨P, T, hleft, hc, ?_, ?_⟩
  · intro u k huk n
    constructor
    · intro z hz
      exact hnest u k huk
        ((m0GeodesicEdges_subset_both hp (P u) ⟨n, rfl⟩).1 hz)
    · have ht := m0Geodesic_initial_pos_mem_trace hp (P u) n
      rw [← m0GeodesicSideRegion_inter hp (P u)] at ht
      exact hnest u k huk ht.1
  · intro j k hjk a b hab
    obtain ⟨hvertices, hedges⟩ := hslice j k hjk a b hab
    refine ⟨?_, ?_, ?_⟩
    · ext v
      rw [m0CutRealizedLeftSideSlice_mem_vertices_iff hp P j k a b hab]
      exact ⟨And.right, fun hv => ⟨hvertices hv, hv⟩⟩
    · ext e
      rw [m0CutRealizedLeftSideSlice_mem_edges_iff hp P j k a b hab]
      exact ⟨And.right, fun he => ⟨hedges he, he⟩⟩
    · intro F
      rw [m0CutGeodesicSlice_face_identification_of_leftmost hp P j
        (T (j - 1)) (T j) (hleft (j - 1)) (hleft j) a b hab F,
        m0GeodesicLeftSide_representsFace_iff,
        m0CutGeodesicSliceRepresentsFace_iff_side_regions]
      constructor
      · rintro ⟨hr, hl⟩
        have hFk : F.val ⊆ m0GeodesicLeftOpen hp (P k) := by
          intro z hz
          have hclosed : z ∈ m0GeodesicSideRegion hp (P k) .left :=
            hnest j k hjk ⟨subset_closure (hl hz), (hr hz).1⟩
          have hnot : z ∉ m0GeodesicTrace hp (P k) := fun ht =>
            (WholePlanePastGlueDrawing.glueDrawing W h hp H).face_subset_compl F hz
              (m0GeodesicTrace_subset_drawing hp (P k) ht)
          exact ((m0CutGeodesic_mem_closedLeft_iff_trace_or_left hp (P k) z).1
            hclosed).resolve_left hnot
        exact ⟨hFk, (m0CutGeodesic_face_betweenTraces_iff hp P j k F
          (fun z hz => (hr hz).1)).2 ⟨hr, hl⟩⟩
      · rintro ⟨hFk, hbetween⟩
        exact (m0CutGeodesic_face_betweenTraces_iff hp P j k F
          (fun z hz => (m0GeodesicLeftOpen_subset hp (P k) (hFk hz)).1)).1 hbetween



































































end DirectedDistances.PaperProofs.Section5
