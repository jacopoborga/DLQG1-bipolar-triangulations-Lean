/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarXDP

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/- General base carrier for the source classes `M_{ℓ,r}` in Lemma
remain individually simple, but may share vertices and geometric edges;
path piece has identical left and right boundaries, and is a base object
outside the strong carrier. -/
structure BipolarTriangulationWithBoundaryBase (D : Type*) [Fintype D]
    [DecidableEq D] (ℓ r : ℕ) where
  map : DirectedMapWithMissing D
  noMissingDarts : ∀ d, ¬ map.missing d
  planar : map.toCombinatorialMap.IsPlanar
  innerFacesDegreeThree : ∀ d, ¬ map.IsOuter d →
    map.toCombinatorialMap.faceSucc
        (map.toCombinatorialMap.faceSucc (map.toCombinatorialMap.faceSucc d)) = d ∧
      map.toCombinatorialMap.faceSucc d ≠ d ∧
      map.toCombinatorialMap.faceSucc (map.toCombinatorialMap.faceSucc d) ≠ d
  acyclic : map.IsAcyclic
  source : MapVertex map
  sink : MapVertex map
  isSource : ¬ ∃ u, map.directedStep u source
  source_unique : ∀ v, (¬ ∃ u, map.directedStep u v) → v = source
  isSink : ¬ ∃ w, map.directedStep sink w
  sink_unique : ∀ v, (¬ ∃ w, map.directedStep v w) → v = sink
  left_length_pos : 1 ≤ ℓ
  right_length_pos : 1 ≤ r
  outerWord : NonemptyWord D
  leftPath : SimpleDirectedDartPath map source sink ℓ
  rightPath : SimpleDirectedDartPath map source sink r
  outerSplit : FourArcsWitness map outerWord leftPath.darts []
    (rightPath.darts.reverse.map map.toCombinatorialMap.edgeInv) []

namespace BipolarTriangulationWithBoundary

/-- Forget only the two mutual-disjointness conditions, retaining all map,
orientation, boundary-path, and outer-face data (`lem-lr-ind`, -/
@[expose] def toBase (B : BipolarTriangulationWithBoundary D ℓ r) :
    BipolarTriangulationWithBoundaryBase D ℓ r :=
  { map := B.map
    noMissingDarts := B.noMissingDarts
    planar := B.planar
    innerFacesDegreeThree := B.innerFacesDegreeThree
    acyclic := B.acyclic
    source := B.source
    sink := B.sink
    isSource := B.isSource
    source_unique := B.source_unique
    isSink := B.isSink
    sink_unique := B.sink_unique
    left_length_pos := B.left_length_pos
    right_length_pos := B.right_length_pos
    outerWord := B.outerWord
    leftPath := B.leftPath
    rightPath := B.rightPath
    outerSplit := B.outerSplit }

end BipolarTriangulationWithBoundary

namespace BipolarTriangulationWithBoundaryBase

/-- Recover the restricted strong carrier when both mutual-disjointness
properties are supplied (`lem-lr-ind`, -/
@[expose] def toStrong (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (hv : ∀ v, v ∈ B.leftPath.vertices → v ∈ B.rightPath.vertices →
      v = B.source ∨ v = B.sink)
    (he : ∀ d, d ∈ B.leftPath.darts → ∀ e, e ∈ B.rightPath.darts →
      ¬ Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e) :
    BipolarTriangulationWithBoundary D ℓ r :=
  { map := B.map
    noMissingDarts := B.noMissingDarts
    planar := B.planar
    innerFacesDegreeThree := B.innerFacesDegreeThree
    acyclic := B.acyclic
    source := B.source
    sink := B.sink
    isSource := B.isSource
    source_unique := B.source_unique
    isSink := B.isSink
    sink_unique := B.sink_unique
    left_length_pos := B.left_length_pos
    right_length_pos := B.right_length_pos
    outerWord := B.outerWord
    leftPath := B.leftPath
    rightPath := B.rightPath
    paths_internally_vertex_disjoint := hv
    paths_edge_disjoint := he
    outerSplit := B.outerSplit }

/-- Forgetting and restoring the carrier fields round-trips on the strong -/
@[simp] theorem toBase_toStrong (B : BipolarTriangulationWithBoundary D ℓ r)
    (hv := B.paths_internally_vertex_disjoint) (he := B.paths_edge_disjoint) :
    toStrong B.toBase hv he = B := by
  cases B
  rfl

/-- Restoring and forgetting the carrier fields round-trips on the base -/
@[simp] theorem toStrong_toBase (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (hv : ∀ v, v ∈ B.leftPath.vertices → v ∈ B.rightPath.vertices →
      v = B.source ∨ v = B.sink)
    (he : ∀ d, d ∈ B.leftPath.darts → ∀ e, e ∈ B.rightPath.darts →
      ¬ Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e) :
    (toStrong B hv he).toBase = B := by
  cases B
  rfl

/-- The forgetting map is injective because it drops only proof fields -/
theorem toBase_injective : Function.Injective
    (BipolarTriangulationWithBoundary.toBase
      (D := D) (ℓ := ℓ) (r := r)) := by
  intro B C h
  cases B
  cases C
  cases h
  rfl

end BipolarTriangulationWithBoundaryBase

/-- A simple directed source-to-sink dart path is an LDP geodesic on the
general base carrier when its length is at least that of every such path -/
@[expose] def IsLDPGeodesicBase (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (_P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  ∀ {m : ℕ} (_Q : SimpleDirectedDartPath B.map B.source B.sink m), m ≤ n

/-- A simple directed source-to-sink dart path is an SDP geodesic on the
general base carrier when its length is at most that of every such path -/
@[expose] def IsSDPGeodesicBase (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (_P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  ∀ {m : ℕ} (_Q : SimpleDirectedDartPath B.map B.source B.sink m), n ≤ m

/-- Dispatch to the longest or shortest path predicate on the general base -/
@[expose] def IsXDPGeodesicBase (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (x : XDP) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  match x with
  | .ldp => IsLDPGeodesicBase B P
  | .sdp => IsSDPGeodesicBase B P

/-- Forgetting mutual boundary disjointness preserves the XDP geodesic -/
theorem isXDPGeodesic_iff_toBase
    (B : BipolarTriangulationWithBoundary D ℓ r) (x : XDP) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsXDPGeodesic B x P ↔ IsXDPGeodesicBase B.toBase x P := by
  cases x <;> rfl

private theorem simplePath_length_lt_cardBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    n < B.map.toCombinatorialMap.numVertices := by
  classical
  have hlen := P.vertices_nodup.length_le_card
  rw [P.vertices_length] at hlen
  have hcard : n + 1 ≤ B.map.toCombinatorialMap.numVertices := by
    simpa [CombinatorialMap.numVertices] using hlen
  omega

/-- The finite set of lengths realized by simple directed source-to-sink dart
paths on the base carrier. Each length is below the number of vertices -/
@[expose] noncomputable def sourceSinkPathLengthsBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : Finset ℕ := by
  classical
  exact (Finset.range B.map.toCombinatorialMap.numVertices).filter fun n =>
    ∃ _P : SimpleDirectedDartPath B.map B.source B.sink n, True

/-- Membership in `sourceSinkPathLengthsBase` means a path of that length -/
theorem mem_sourceSinkPathLengthsBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (n : ℕ) :
    n ∈ sourceSinkPathLengthsBase B ↔
      ∃ _P : SimpleDirectedDartPath B.map B.source B.sink n, True := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨P, _⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (simplePath_length_lt_cardBase B P), ⟨P, trivial⟩⟩

/-- The length set is nonempty, witnessed by the left boundary path -/
theorem sourceSinkPathLengthsBase_nonempty
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (sourceSinkPathLengthsBase B).Nonempty := by
  refine ⟨ℓ, ?_⟩
  exact (mem_sourceSinkPathLengthsBase B ℓ).2 ⟨B.leftPath, trivial⟩

/-- The maximum length of a simple directed source-to-sink dart path on the -/
@[expose] noncomputable def ldpLengthBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : ℕ :=
  (sourceSinkPathLengthsBase B).max' (sourceSinkPathLengthsBase_nonempty B)

/-- The minimum length of a simple directed source-to-sink dart path on the -/
@[expose] noncomputable def sdpLengthBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : ℕ :=
  (sourceSinkPathLengthsBase B).min' (sourceSinkPathLengthsBase_nonempty B)

/-- The maximal path length on the base carrier is attained -/
theorem ldpLengthBase_mem (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ldpLengthBase B ∈ sourceSinkPathLengthsBase B :=
  Finset.max'_mem _ _

/-- The minimal path length on the base carrier is attained -/
theorem sdpLengthBase_mem (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    sdpLengthBase B ∈ sourceSinkPathLengthsBase B :=
  Finset.min'_mem _ _

/-- Every simple directed source-to-sink base path has length at most the -/
theorem le_ldpLengthBase (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    n ≤ ldpLengthBase B := by
  have hm := (mem_sourceSinkPathLengthsBase B n).2 ⟨P, trivial⟩
  exact (sourceSinkPathLengthsBase B).le_max' n hm

/-- The attained minimal base path length is at most every source-to-sink -/
theorem sdpLengthBase_le (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    sdpLengthBase B ≤ n := by
  have hm := (mem_sourceSinkPathLengthsBase B n).2 ⟨P, trivial⟩
  exact (sourceSinkPathLengthsBase B).min'_le n hm

/-- A longest directed path exists on the finite general base carrier -/
theorem exists_isLDPGeodesicBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ∃ n : ℕ, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsLDPGeodesicBase B P := by
  obtain ⟨P, _⟩ := (mem_sourceSinkPathLengthsBase B (ldpLengthBase B)).1
    (ldpLengthBase_mem B)
  refine ⟨ldpLengthBase B, P, ?_⟩
  intro m Q
  exact (sourceSinkPathLengthsBase B).le_max' m
    ((mem_sourceSinkPathLengthsBase B m).2 ⟨Q, trivial⟩)

/-- A shortest directed path exists on the finite general base carrier -/
theorem exists_isSDPGeodesicBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ∃ n : ℕ, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsSDPGeodesicBase B P := by
  obtain ⟨P, _⟩ := (mem_sourceSinkPathLengthsBase B (sdpLengthBase B)).1
    (sdpLengthBase_mem B)
  refine ⟨sdpLengthBase B, P, ?_⟩
  intro m Q
  exact (sourceSinkPathLengthsBase B).min'_le m
    ((mem_sourceSinkPathLengthsBase B m).2 ⟨Q, trivial⟩)

/-- A path is an LDP geodesic on the base exactly when its length is the -/
theorem isLDPGeodesicBase_iff_length_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsLDPGeodesicBase B P ↔ n = ldpLengthBase B := by
  constructor
  · intro h
    obtain ⟨Q, _⟩ := (mem_sourceSinkPathLengthsBase B (ldpLengthBase B)).1
      (ldpLengthBase_mem B)
    have hmax : ldpLengthBase B ≤ n := h Q
    have hbound := le_ldpLengthBase B P
    omega
  · intro hn
    subst n
    intro m Q
    exact le_ldpLengthBase B Q

/-- A path is an SDP geodesic on the base exactly when its length is the -/
theorem isSDPGeodesicBase_iff_length_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsSDPGeodesicBase B P ↔ n = sdpLengthBase B := by
  constructor
  · intro h
    obtain ⟨Q, _⟩ := (mem_sourceSinkPathLengthsBase B (sdpLengthBase B)).1
      (sdpLengthBase_mem B)
    have hmin : n ≤ sdpLengthBase B := h Q
    have hbound := sdpLengthBase_le B P
    omega
  · intro hn
    subst n
    intro m Q
    exact sdpLengthBase_le B Q

/-- The left half-domain from `lem-lr-ind` on the general base carrier: the
right boundary has length `s` and is the unique XDP geodesic by its dart -/
@[expose] def InHalfLBase {x : XDP} (s : ℕ)
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : Prop :=
  r = s ∧ IsXDPGeodesicBase B x B.rightPath ∧
    ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
      IsXDPGeodesicBase B x Q → Q.darts = B.rightPath.darts

/-- The right half-domain from `lem-lr-ind` on the general base carrier: its
left boundary is an XDP geodesic of length `s` -/
@[expose] def InHalfRBase {x : XDP} (s : ℕ)
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : Prop :=
  ℓ = s ∧ IsXDPGeodesicBase B x B.leftPath

/-- The strong and general-base left half-domain predicates agree after
forgetting mutual boundary disjointness (`lem-lr-ind`, -/
theorem inHalfL_iff_toBase {x : XDP} (s : ℕ)
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    InHalfL (D := D) (ℓ := ℓ) (r := r) (x := x) s B ↔
      InHalfLBase (D := D) (ℓ := ℓ) (r := r) (x := x) s B.toBase := by
  rfl

/-- The strong and general-base right half-domain predicates agree after
forgetting mutual boundary disjointness (`lem-lr-ind`, -/
theorem inHalfR_iff_toBase {x : XDP} (s : ℕ)
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    InHalfR (D := D) (ℓ := ℓ) (r := r) (x := x) s B ↔
      InHalfRBase (D := D) (ℓ := ℓ) (r := r) (x := x) s B.toBase := by
  rfl

end DirectedDistances.PlanarMap
