/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination8
import all DirectedDistances.PaperProofs.Section5.GeoSliceLeftmostNonCrossing5

/-! Local leftmost hypotheses retain the paper's two actual bounding geodesics.
No global coalescence, face identification, or measurability premise is added. -/

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

/-- Helper toward Lemma 5.6: two locally leftmost geodesics with an existing
common tail coalesce at every vertex meeting. Only their two leftmost
predicates are required, rather than a globally coalescing leftmost family. -/
theorem m0CutEdgeTailsCoalesce_of_meeting_of_leftmost
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k l : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (R : M0CutInfiniteGeodesic W H h hLL l longest)
    (TQ : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (TR : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h l))
    (hQ : Xdp.CutLeftmostXdp W H h hp hLL longest k Q TQ)
    (hR : Xdp.CutLeftmostXdp W H h hp hLL longest l R TR)
    (a b : ℕ) (hco : M0CutEdgeTailsCoalesce Q R a b)
    (i j : ℕ) (hmeet : (Q.codePath.initial i).1 = (R.codePath.initial j).1) :
    M0CutEdgeTailsCoalesce Q R i j := by
  let w := shiftedStream W 0
  let hfam : ∀ n, ∃ A : StageDrawing w n, Nonempty (MonotoneStageInvariant w n A) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  have hang (u : ℤ) (S : M0CutInfiniteGeodesic W H h hLL u longest)
      (T : InfinitePresentPath w (boundaryPresentVertex w h u))
      (hS : Xdp.CutLeftmostXdp W H h hp hLL longest u S T)
      (U : InfinitePresentPath w (boundaryPresentVertex w h u))
      (hU : if longest then U.HasLongestSegments else U.HasShortestSegments) :
      Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf w (H.1 0) hfam
        S.codePath U := by
    cases longest with
    | false =>
      have ht := (Xdp.Sdp.cutLeftmost_iff_runZero W H h hp hLL u S T).1 hS U hU
      exact ((Xdp.LeftmostXdpTransport.trace_subset_closedBetween_iff_departureArgs
        w (H.1 0) hfam (boundaryVertex w h u) S.codePath T U).1 ht).1
    | true =>
      have ht := (Xdp.cutLeftmost_iff_runZero W H h hp hLL u S T).1 hS U hU
      exact ((Xdp.LeftmostXdpTransport.trace_subset_closedBetween_iff_departureArgs
        w (H.1 0) hfam (boundaryVertex w h u) S.codePath T U).1 ht).1
  have hcode : ∃ c d, ∀ n, Q.codePath.edge (c + n) = R.codePath.edge (d + n) :=
    ⟨a, b, fun n => wholePlaneEdgeι_injective W 0 (hco n)⟩
  have he := leftmost_tails_eq_at_meeting (H.1 0) hfam longest
    Q.codePath R.codePath Q.segments R.segments
    (hang k Q TQ hQ) (hang l R TR hR) hcode i j hmeet
  exact fun n => congrArg (wholePlaneEdgeι W 0) (he n)


/-- Helper toward Lemma 5.6: the earlier closed-left side is contained in
the later one, with leftmost hypotheses only for these two geodesics. -/
theorem m0CutGeodesic_closedLeftSide_subset_of_leftmost
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ)
    (Tprev : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h (k - 1)))
    (Tnext : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hprev : Xdp.CutLeftmostXdp W H h hp hLL longest (k - 1) (P (k - 1)) Tprev)
    (hnext : Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) Tnext)
    (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    m0GeodesicSideRegion hp (P (k - 1)) .left ⊆
      m0GeodesicSideRegion hp (P k) .left := by
  have havoid (n : ℕ) (hn : n < b) :
      ((P k).codePath.initial n).1.id ∉ m0GeodesicVertices (P (k - 1)) := by
    intro hmem
    obtain ⟨i, hi⟩ := Set.mem_range.mp hmem
    have hmeet : ((P (k - 1)).codePath.initial i).1 =
        ((P k).codePath.initial n).1 := by
      apply presentVertex_eq_of_id_eq
      exact hi
    have hco := m0CutEdgeTailsCoalesce_of_meeting_of_leftmost hp
      (P (k - 1)) (P k) Tprev Tnext hprev hnext a b hab.1 i n hmeet
    exact (Nat.not_lt_of_ge (hab.2 i n hco).2) hn
  have hvertices : ∀ n, n ≤ b →
      ((P k).codePath.initial n).1.id ∈
        m0GeodesicSideVertices hp (P (k - 1)) .right := by
    intro n
    induction n with
    | zero =>
      intro _
      have hz := ((P k).codePath.initial 0).2.eq_of_length_zero
        ((P k).codePath.prefix_length 0)
      have hzero : ((P k).codePath.initial 0).1.id =
          boundaryVertex (shiftedStream W 0) h k :=
        congrArg PresentVertex.id hz.symm
      rw [hzero]
      exact m0Cut_next_boundary_mem_right_side (P (k - 1))
    | succ n ih =>
      intro hn
      rcases m0GeodesicSideEdges_cover hp (P (k - 1))
          ((P k).codePath.edge n) with he | he
      · have hwest := (m0GeodesicSide_endpoints hp (P (k - 1)) .left
          ((P k).codePath.edge n) he).1
        change edgeWest (shiftedStream W 0) ((P k).codePath.edge n) ∈
          m0GeodesicSideVertices hp (P (k - 1)) .left at hwest
        rw [((P k).codePath.edge_outgoing_at_initial (shiftedStream W 0) n).2] at hwest
        apply False.elim
        apply havoid n (by omega)
        rw [← m0GeodesicSideVertices_inter hp (P (k - 1))]
        exact ⟨hwest, ih (by omega)⟩
      · have hend := (m0GeodesicSide_endpoints hp (P (k - 1)) .right
          ((P k).codePath.edge n) he).2
        change edgeEast (shiftedStream W 0) ((P k).codePath.edge n) ∈
          m0GeodesicSideVertices hp (P (k - 1)) .right at hend
        rw [((P k).codePath.edge_incoming_at_succ (shiftedStream W 0) n).2] at hend
        exact hend
  have hedges : ∀ n, (P k).codePath.edge n ∈
      m0GeodesicSideEdges hp (P (k - 1)) .right := by
    intro n
    by_cases hn : n < b
    · rcases m0GeodesicSideEdges_cover hp (P (k - 1))
          ((P k).codePath.edge n) with he | he
      · have hwest := (m0GeodesicSide_endpoints hp (P (k - 1)) .left
          ((P k).codePath.edge n) he).1
        change edgeWest (shiftedStream W 0) ((P k).codePath.edge n) ∈
          m0GeodesicSideVertices hp (P (k - 1)) .left at hwest
        rw [((P k).codePath.edge_outgoing_at_initial (shiftedStream W 0) n).2] at hwest
        apply False.elim
        apply havoid n hn
        rw [← m0GeodesicSideVertices_inter hp (P (k - 1))]
        exact ⟨hwest, hvertices n hn.le⟩
      · exact he
    · have hidx : b + (n - b) = n := by omega
      have he := wholePlaneEdgeι_injective W 0 (hab.1 (n - b))
      rw [hidx] at he
      rw [← he]
      exact (m0CutGeodesicEdges_subset_both_closed_sides
        (hp := hp) (P (k - 1)) ⟨a + (n - b), rfl⟩).2
  have htraceDisjoint : Disjoint (m0GeodesicLeftOpen hp (P (k - 1)))
      (m0GeodesicTrace hp (P k)) := by
    apply Set.disjoint_left.mpr
    intro z hzL hzT
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hzT
    exact (hedges n hn).2 hzL
  have hsub : m0GeodesicLeftOpen hp (P (k - 1)) ⊆
      m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp (P k) := by
    intro z hz
    exact ⟨(m0GeodesicLeftOpen_subset hp (P (k - 1)) hz).1,
      Set.disjoint_left.mp htraceDisjoint hz⟩
  let z := (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
    ((m0CutData W H h hLL).x ((k - 1) - 1))
  have hzOld : z ∈ m0GeodesicLeftOpen hp (P (k - 1)) :=
    m0Geodesic_previous_pos_mem_leftOpen hp (P (k - 1))
  have hzAmbient : z ∈ m0GeodesicAmbientRegion W H h :=
    (m0GeodesicLeftOpen_subset hp (P (k - 1)) hzOld).1
  have hzAbscissa : z.re = seamX (shiftedStream W 0) h (H.1 0) ((k - 1) - 1) := by
    dsimp [z]
    rw [(m0CutData W H h hLL).x_eq h hLL ((k - 1) - 1), m0Geodesic_pos_runZero hp]
    rfl
  have hzWest : z.re < seamX (shiftedStream W 0) h (H.1 0) k := by
    rw [hzAbscissa]
    exact seamX_strictMono (shiftedStream W 0) h (H.1 0) (by omega)
  have hzNew : z ∈ m0GeodesicLeftOpen hp (P k) :=
    boundaryGluing_west_of_root_mem_leftOpen W h k longest hp (P k) hzAmbient hzWest
  have hcomponent : connectedComponentIn
      (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp (P k)) z =
        m0GeodesicLeftOpen hp (P k) := (connectedComponentIn_eq hzNew).symm
  have hleftOpen : m0GeodesicLeftOpen hp (P (k - 1)) ⊆
      m0GeodesicLeftOpen hp (P k) := by
    have hc := isPreconnected_connectedComponentIn.subset_connectedComponentIn hzOld hsub
    rw [hcomponent] at hc
    exact hc
  intro q hq
  exact ⟨closure_mono hleftOpen hq.1, hq.2⟩


/-- Helper toward Lemma 5.6: finite enclosure implies candidate face
representation at positive later offset for the paper's leftmost geodesics.
The two explicit leftmost predicates are the source hypotheses, rather than
an assumed side ordering or face-identification conclusion. -/
theorem m0CutGeodesicSliceRepresentsFace_of_enclosedBySegments_of_pos_of_leftmost
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ)
    (Tprev : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h (k - 1)))
    (Tnext : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hprev : Xdp.CutLeftmostXdp W H h hp hLL longest (k - 1) (P (k - 1)) Tprev)
    (hnext : Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) Tnext)
    (a b : ℕ) (hb : 0 < b)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutFaceEnclosedBySegments hp P k a b F →
      m0CutGeodesicSliceRepresentsFace hp P k a b hab F := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  intro henc
  rcases m0CutFaceEnclosedBySegments_representsFace_or_reverse_sides
      hp P k a (b + 1) hab F henc with hrep | hrev
  · exact hrep
  · have hnested := m0CutGeodesic_closedLeftSide_subset_of_leftmost
      hp P k Tprev Tnext hprev hnext a (b + 1) hab
    obtain ⟨z, hz, hF⟩ := F.property
    have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
    have hzOld : z ∈ m0GeodesicSideRegion hp (P (k - 1)) .left :=
      ⟨subset_closure (hrev.1 hzF), henc.1 hzF⟩
    exact False.elim ((hrev.2 hzF).2 (hnested hzOld).1)

/-- Helper toward Lemma 5.6: finite-segment enclosure is equivalent to the
candidate face representation for two leftmost bounding geodesics, including
zero offsets. This combines the unrestricted zero-offset result with the
positive-offset leftmost specialization; it is not the measurable slice law. -/
theorem m0CutGeodesicSlice_face_identification_of_leftmost
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ)
    (Tprev : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h (k - 1)))
    (Tnext : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hprev : Xdp.CutLeftmostXdp W H h hp hLL longest (k - 1) (P (k - 1)) Tprev)
    (hnext : Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) Tnext)
    (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    m0CutFaceEnclosedBySegments hp P k a b F ↔
      m0CutGeodesicSliceRepresentsFace hp P k a b hab F := by
  cases b with
  | zero => exact m0CutGeodesicSlice_face_identification_of_zero hp P k a hab F
  | succ b =>
    exact ⟨m0CutGeodesicSliceRepresentsFace_of_enclosedBySegments_of_pos_of_leftmost
      hp P k Tprev Tnext hprev hnext a (b + 1) (Nat.zero_lt_succ b) hab F,
      m0CutFaceEnclosedBySegments_of_representsFace hp P k a (b + 1) hab F⟩












































end DirectedDistances.PaperProofs.Section5
