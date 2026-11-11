/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralBipolarBoundary

public section
namespace DirectedDistances.PlanarMap

/- counterclockwise by convention (`DirectedDistances/PlanarMap/CombinatorialMap.lean:15–18`).
The KMSW non-source outgoing enumeration follows `rot` from rightmost to
leftmost, while `kmswOutgoingEdgesLeftToRight` reverses that list
(`DirectedDistances/KMSW/LeftmostGeodesicUIQBOT.lean:338–343,457–467`). Thus
the left-to-right scan direction is `rot.symm`, once the incoming or source
boundary corner is proved to be the correct cut. The finite general-base
corner/interval correspondence remains to be established here. -/

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

private theorem simplePath_length_lt_cardVertices
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) :
    n < M.toCombinatorialMap.numVertices := by
  classical
  have hlen := P.vertices_nodup.length_le_card
  rw [P.vertices_length] at hlen
  have hcard : n + 1 ≤ M.toCombinatorialMap.numVertices := by
    simpa [CombinatorialMap.numVertices] using hlen
  omega

/-- The finite set of lengths of simple directed paths from the source to a
vertex on the general base carrier (`lem-lr-ind`, -/
@[expose] noncomputable def sourceVertexPathLengthsBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    Finset ℕ := by
  classical
  exact (Finset.range B.map.toCombinatorialMap.numVertices).filter fun n =>
    ∃ _P : SimpleDirectedDartPath B.map B.source v n, True

/-- The finite set of lengths of simple directed paths from a vertex to the
sink on the general base carrier (`lem-lr-ind`, -/
@[expose] noncomputable def vertexSinkPathLengthsBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    Finset ℕ := by
  classical
  exact (Finset.range B.map.toCombinatorialMap.numVertices).filter fun n =>
    ∃ _P : SimpleDirectedDartPath B.map v B.sink n, True

/-- Membership in the source-to-vertex length set means a path of that -/
theorem mem_sourceVertexPathLengthsBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (n : ℕ) :
    n ∈ sourceVertexPathLengthsBase B v ↔
      ∃ _P : SimpleDirectedDartPath B.map B.source v n, True := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨P, _⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (simplePath_length_lt_cardVertices B.map P), ⟨P, trivial⟩⟩

/-- Membership in the vertex-to-sink length set means a path of that length -/
theorem mem_vertexSinkPathLengthsBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (n : ℕ) :
    n ∈ vertexSinkPathLengthsBase B v ↔
      ∃ _P : SimpleDirectedDartPath B.map v B.sink n, True := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨P, _⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (simplePath_length_lt_cardVertices B.map P), ⟨P, trivial⟩⟩

/-- Every source-to-vertex simple path has fewer edges than the number of -/
theorem sourceVertexPath_length_lt_cardVertices
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source v n) :
    n < B.map.toCombinatorialMap.numVertices :=
  simplePath_length_lt_cardVertices B.map P

/-- Every vertex-to-sink simple path has fewer edges than the number of -/
theorem vertexSinkPath_length_lt_cardVertices
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    {n : ℕ} (P : SimpleDirectedDartPath B.map v B.sink n) :
    n < B.map.toCombinatorialMap.numVertices :=
  simplePath_length_lt_cardVertices B.map P

/-- Longest simple-path length from the source to `v`. The value `⊥`
represents an empty path family (`lem-lr-ind`, -/
@[expose] noncomputable def ldpSourceDistanceBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    WithBot ℕ := (sourceVertexPathLengthsBase B v).max

/-- Shortest simple-path length from the source to `v`. The value `⊤`
represents an empty path family (`lem-lr-ind`, -/
@[expose] noncomputable def sdpSourceDistanceBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    WithTop ℕ := (sourceVertexPathLengthsBase B v).min

/-- Longest simple-path length from `v` to the sink. The value `⊥`
represents an empty path family (`lem-lr-ind`, -/
@[expose] noncomputable def ldpSinkDistanceBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    WithBot ℕ := (vertexSinkPathLengthsBase B v).max

/-- Shortest simple-path length from `v` to the sink. The value `⊤`
represents an empty path family (`lem-lr-ind`, -/
@[expose] noncomputable def sdpSinkDistanceBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    WithTop ℕ := (vertexSinkPathLengthsBase B v).min

/-- Every source-to-vertex simple path length is at most the longest-path
value from the source (`lem-lr-ind`, -/
theorem coe_le_ldpSourceDistanceBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source v n) :
    (n : WithBot ℕ) ≤ ldpSourceDistanceBase B v := by
  unfold ldpSourceDistanceBase
  apply Finset.le_max
  exact (mem_sourceVertexPathLengthsBase B v n).2 ⟨P, trivial⟩

/-- The shortest-path value from the source is at most every source-to-vertex
simple path length (`lem-lr-ind`, -/
theorem sdpSourceDistanceBase_le_coe
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source v n) :
    sdpSourceDistanceBase B v ≤ (n : WithTop ℕ) := by
  unfold sdpSourceDistanceBase
  apply Finset.min_le
  exact (mem_sourceVertexPathLengthsBase B v n).2 ⟨P, trivial⟩

/-- Every vertex-to-sink simple path length is at most the longest-path value -/
theorem coe_le_ldpSinkDistanceBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    {n : ℕ} (P : SimpleDirectedDartPath B.map v B.sink n) :
    (n : WithBot ℕ) ≤ ldpSinkDistanceBase B v := by
  unfold ldpSinkDistanceBase
  apply Finset.le_max
  exact (mem_vertexSinkPathLengthsBase B v n).2 ⟨P, trivial⟩

/-- The shortest-path value to the sink is at most every vertex-to-sink
simple path length (`lem-lr-ind`, -/
theorem sdpSinkDistanceBase_le_coe
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    {n : ℕ} (P : SimpleDirectedDartPath B.map v B.sink n) :
    sdpSinkDistanceBase B v ≤ (n : WithTop ℕ) := by
  unfold sdpSinkDistanceBase
  apply Finset.min_le
  exact (mem_vertexSinkPathLengthsBase B v n).2 ⟨P, trivial⟩

/-- The source-to-sink endpoint of the source distance agrees with the
attained LDP length (`lem-lr-ind`, -/
theorem ldpSourceDistanceBase_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ldpSourceDistanceBase B B.sink = (ldpLengthBase B : WithBot ℕ) := by
  change (sourceSinkPathLengthsBase B).max = _
  rw [← Finset.coe_max' (sourceSinkPathLengthsBase_nonempty B)]
  rfl

/-- The source-to-sink endpoint of the source distance agrees with the
attained SDP length (`lem-lr-ind`, -/
theorem sdpSourceDistanceBase_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    sdpSourceDistanceBase B B.sink = (sdpLengthBase B : WithTop ℕ) := by
  change (sourceSinkPathLengthsBase B).min = _
  rw [← Finset.coe_min' (sourceSinkPathLengthsBase_nonempty B)]
  rfl

/-- The source-to-sink endpoint of the sink distance agrees with the
attained LDP length (`lem-lr-ind`, -/
theorem ldpSinkDistanceBase_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ldpSinkDistanceBase B B.source = (ldpLengthBase B : WithBot ℕ) := by
  change (sourceSinkPathLengthsBase B).max = _
  rw [← Finset.coe_max' (sourceSinkPathLengthsBase_nonempty B)]
  rfl

/-- The source-to-sink endpoint of the sink distance agrees with the
attained SDP length (`lem-lr-ind`, -/
theorem sdpSinkDistanceBase_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    sdpSinkDistanceBase B B.source = (sdpLengthBase B : WithTop ℕ) := by
  change (sourceSinkPathLengthsBase B).min = _
  rw [← Finset.coe_min' (sourceSinkPathLengthsBase_nonempty B)]
  rfl

/-- A dart lies on some XDP geodesic on the general base carrier
characterization is a further required lemma; this existential definition
keeps the path-level meaning explicit. -/
@[expose] def IsXDPGeodesicDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) (d : D) : Prop :=
  ∃ n : ℕ, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
    IsXDPGeodesicBase B x P ∧ d ∈ P.darts

/-- A geodesic dart is present and oriented from its tail vertex, as the base
carrier has no missing darts (`lem-lr-ind`, -/
theorem IsXDPGeodesicDart.present_tail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) (d : D)
    (hd : IsXDPGeodesicDart B x d) : ¬ B.map.missing d ∧ B.map.tail d := by
  obtain ⟨n, P, _, hmem⟩ := hd
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  have hs := P.edge_step i
  rw [hi] at hs
  exact ⟨B.noMissingDarts d, hs.2.1⟩

/-- Every non-sink vertex occurring on an XDP geodesic has a following dart
of that same geodesic (`lem-lr-ind`, -/
theorem exists_outgoingXDPGeodesicDart_of_mem_vertices
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsXDPGeodesicBase B x P) {v : MapVertex B.map}
    (hv : v ∈ P.vertices) (hvs : v ≠ B.sink) :
    ∃ d, d ∈ P.darts ∧ dartTailVertex B.map d = v ∧
      IsXDPGeodesicDart B x d := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hi_lt : i.val < n := by
    have hi_bound : i.val < n + 1 := by
      have hlen := P.vertices_length
      simpa [hlen] using i.isLt
    by_contra h
    have hi_eq : i.val = n := by omega
    apply hvs
    calc
      v = P.vertices.get i := hi.symm
      _ = P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩ := by
        congr 1
        exact Fin.ext hi_eq
      _ = B.sink := P.end_vertex
  let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi_lt⟩
  let d := P.darts.get j
  have hs := P.edge_step j
  refine ⟨d, List.get_mem _ _, ?_, ?_⟩
  · exact hs.2.2.1.symm.trans hi
  · exact ⟨n, P, hP, List.get_mem _ _⟩

private theorem path_start_ne_end_of_pos_length
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (hn : 0 < n) : s ≠ t := by
  intro hst
  let i : Fin P.vertices.length := ⟨0, by rw [P.vertices_length]; omega⟩
  let j : Fin P.vertices.length := ⟨n, by rw [P.vertices_length]; omega⟩
  have hij : P.vertices.get i = P.vertices.get j := by
    calc
      P.vertices.get i = s := P.start_vertex
      _ = t := hst
      _ = P.vertices.get j := P.end_vertex.symm
  have hidx := P.vertices_nodup.get_inj_iff.mp hij
  have hval := congrArg Fin.val hidx
  dsimp [i, j] at hval
  omega

/-- Every extremal path type has an attained source-to-sink geodesic on the
general base carrier (`lem-lr-ind`, -/
theorem exists_isXDPGeodesicBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    ∃ n : ℕ, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P := by
  cases x with
  | ldp => exact exists_isLDPGeodesicBase B
  | sdp => exact exists_isSDPGeodesicBase B

/-- The source has an outgoing dart belonging to an XDP geodesic -/
theorem exists_outgoingXDPGeodesicDart_at_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    ∃ d, dartTailVertex B.map d = B.source ∧ IsXDPGeodesicDart B x d := by
  obtain ⟨n, P, hP⟩ := exists_isXDPGeodesicBase B x
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    have hsame : B.source = B.sink := by
      simpa using P.start_vertex.symm.trans P.end_vertex
    exact (path_start_ne_end_of_pos_length B.map B.leftPath B.left_length_pos) hsame
  have hsource : B.source ∈ P.vertices := by
    apply List.mem_iff_get.mpr
    exact ⟨⟨0, by rw [P.vertices_length]; omega⟩, P.start_vertex⟩
  obtain ⟨d, _, htail, hgeo⟩ :=
    exists_outgoingXDPGeodesicDart_of_mem_vertices B x P hP hsource
      (path_start_ne_end_of_pos_length B.map B.leftPath B.left_length_pos)
  exact ⟨d, htail, hgeo⟩

end DirectedDistances.PlanarMap
