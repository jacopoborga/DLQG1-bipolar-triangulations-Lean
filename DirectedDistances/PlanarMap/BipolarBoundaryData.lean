/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CombinatorialMap
public import DirectedDistances.PlanarMap.OuterBoundary
public import DirectedDistances.PlanarMap.EdgeOrientationFlip

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A map vertex represented by its rotation-cycle quotient class. -/
abbrev MapVertex (M : DirectedMapWithMissing D) :=
  CombinatorialMap.VertexQuotient M.toCombinatorialMap

/-- The initial vertex of a dart, represented by its rotation-cycle vertex -/
@[expose] def dartTailVertex (M : DirectedMapWithMissing D) (d : D) : MapVertex M :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot) d

/-- The terminal vertex of a dart, represented by the vertex of its opposite -/
@[expose] def dartHeadVertex (M : DirectedMapWithMissing D) (d : D) : MapVertex M :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot)
    (M.toCombinatorialMap.edgeInv d)

/-- A list of darts with an explicit list of its successive vertices. The
indexed incidence clause makes each listed dart a present oriented edge from
the corresponding vertex to the next one; vertex distinctness makes the path
simple. -/
structure SimpleDirectedDartPath (M : DirectedMapWithMissing D)
    (s t : MapVertex M) (n : ℕ) where
  darts : List D
  vertices : List (MapVertex M)
  darts_length : darts.length = n
  vertices_length : vertices.length = n + 1
  vertices_nodup : vertices.Nodup
  start_vertex : vertices.get ⟨0, by omega⟩ = s
  end_vertex : vertices.get ⟨n, by omega⟩ = t
  edge_step : ∀ i : Fin darts.length,
    ¬ M.missing (darts.get i) ∧ M.tail (darts.get i) ∧
      vertices.get ⟨i.val, by omega⟩ = dartTailVertex M (darts.get i) ∧
      vertices.get ⟨i.val + 1, by omega⟩ = dartHeadVertex M (darts.get i)

namespace SimpleDirectedDartPath

variable {M : DirectedMapWithMissing D}
variable {s t : MapVertex M} {n : ℕ}

/-- The first dart of a positive-length directed path. Helper; not counted in
the paper inventory. -/
@[expose] def firstDart (P : SimpleDirectedDartPath M s t n) (hn : 0 < n) : D :=
  P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩

end SimpleDirectedDartPath

/-- A dart is on one of the two directed outer boundary paths. Edge
membership is understood up to the edge involution, so the convention does
not depend on which of an edge's two darts is used. The relation is written
as `SameCycle edgeInv`, the body of `CombinatorialMap.EdgeRel`, because that
definition is not exposed to importing modules. Helper; not counted in the
paper inventory. -/
@[expose] def IsBoundaryEdge (M : DirectedMapWithMissing D)
    (left right : List D) (d : D) : Prop :=
  ∃ e ∈ left ++ right, Equiv.Perm.SameCycle M.toCombinatorialMap.edgeInv d e

/-- The two simple directed sides of a finite bipolar map with boundary.
The `outerSplit` witness uses `FourArcsWitness`: the left path occurs as the
upper-left arc, while the right path occurs source-to-sink in `rightPath` and
as reversed opposite darts in the lower-right outer-face arc. This is the
ordered outer-face convention of `defn:bound-edges` and the left/right paths

Scope notes. `paths_internally_vertex_disjoint` forces a simple outer
boundary. `paths_edge_disjoint` excludes exactly the single-edge map `m₀`
(`ℓ = r = 1`, one edge that is both the left and the right boundary). This is
harmless for `lem-bdy-reverse`, which needs `r ≥ 2` and `1 ≤ k ≤ r - 1`, but a
carrier for all of `M_{1,1}` (for example in `lem-lr-ind` or `lem-kmsw-left`
at `ℓ = 1`) must add `m₀` separately. Helper; not counted in the paper
inventory. -/
structure BipolarTriangulationWithBoundary (D : Type*) [Fintype D]
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
  paths_internally_vertex_disjoint : ∀ v,
    v ∈ leftPath.vertices → v ∈ rightPath.vertices → v = source ∨ v = sink
  paths_edge_disjoint : ∀ d, d ∈ leftPath.darts → ∀ e, e ∈ rightPath.darts →
    ¬ Equiv.Perm.SameCycle map.toCombinatorialMap.edgeInv d e
  outerSplit : FourArcsWitness map outerWord leftPath.darts []
    (rightPath.darts.reverse.map map.toCombinatorialMap.edgeInv) []

namespace BipolarTriangulationWithBoundary

variable {ℓ r : ℕ}

/-- Vertices lying on either of the two outer directed boundary paths.
Helper; not counted in the paper inventory. -/
@[expose] def boundaryVertices {B : BipolarTriangulationWithBoundary D ℓ r} :
    Set (MapVertex B.map) :=
  {v | v ∈ B.leftPath.vertices ∨ v ∈ B.rightPath.vertices}

/-- The edge orbits on the two directed boundary paths. Helper; not counted in
the paper inventory. -/
@[expose] def boundaryEdge {B : BipolarTriangulationWithBoundary D ℓ r}
    (d : D) : Prop := IsBoundaryEdge B.map B.leftPath.darts B.rightPath.darts d

/-- Def-reverse-map's boundary-channel condition: each boundary vertex other
than the sink receives no non-boundary edge. This includes the source, whose
indegree is zero by bipolarity (`def-reverse-map`,
inventory. -/
@[expose] def IsBoundaryChanneled (B : BipolarTriangulationWithBoundary D ℓ r) : Prop :=
  ∀ d, ¬ B.map.missing d → B.map.tail d →
    dartHeadVertex B.map d ∈ B.boundaryVertices →
    dartHeadVertex B.map d ≠ B.sink → B.boundaryEdge d

/-- The graph-level incoming-boundary-edge condition used as H3 in the
boundary-prefix-flip argument. It says that every directed edge entering a
boundary vertex other than the sink belongs to one of the two boundary paths.
counted in the paper inventory. -/
@[expose] def BoundaryFlipH3 (B : BipolarTriangulationWithBoundary D ℓ r) : Prop :=
  ∀ u v d, v ∈ B.boundaryVertices → v ≠ B.sink →
    ¬ B.map.missing d → B.map.tail d →
    dartTailVertex B.map d = u → dartHeadVertex B.map d = v → B.boundaryEdge d

/-- The maps in `InMbc ℓ r` are the boundary-channeled finite bipolar
triangulations with left and right boundary lengths `ℓ,r`, the carrier class
used by Lemma `lem-bdy-reverse` and Proposition `prop-uihbot-sym`
with explicit dart representatives; it is not a quotient by map isomorphism.
Representatives are non-unique beyond the dart labelling: the outer dart
`map.outer` and the rotation of `outerWord` are free data, so any counting or
map `m₀` is excluded (see `BipolarTriangulationWithBoundary`). Helper; not
counted in the paper inventory. -/
@[expose] def InMbc (ℓ r : ℕ)
    (B : BipolarTriangulationWithBoundary D ℓ r) : Prop :=
  B.IsBoundaryChanneled

/-- Boundary channeling implies H3, in its graph-level directed-edge form
counted in the paper inventory. -/
theorem boundaryChanneled_implies_H3
    {B : BipolarTriangulationWithBoundary D ℓ r} (hbc : B.IsBoundaryChanneled) :
    B.BoundaryFlipH3 := by
  intro u v d hv hvs hmiss htail htailV hheadV
  apply hbc d hmiss htail
  · rw [hheadV]
    exact hv
  · rw [hheadV]
    exact hvs

/-- The first left-boundary edge leaves the source and is a different edge
orbit from the first right-boundary edge. This supplies H4 for the
boundary-prefix-flip argument; edge-disjointness is the structure field
`paths_edge_disjoint`, not an extra hypothesis (`def-bipolar-bdy`,
inventory. -/
theorem firstLeftEdge_leavesSource_and_differs_from_firstRight
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    let dL := B.leftPath.firstDart (Nat.lt_of_lt_of_le (by decide) B.left_length_pos)
    let dR := B.rightPath.firstDart (Nat.lt_of_lt_of_le (by decide) B.right_length_pos)
    B.map.tail dL ∧ dartTailVertex B.map dL = B.source ∧
      ¬ Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv dL dR := by
  let iL : Fin B.leftPath.darts.length :=
    ⟨0, by rw [B.leftPath.darts_length]; exact Nat.lt_of_lt_of_le (by decide) B.left_length_pos⟩
  let iR : Fin B.rightPath.darts.length :=
    ⟨0, by rw [B.rightPath.darts_length]; exact Nat.lt_of_lt_of_le (by decide) B.right_length_pos⟩
  let dL := B.leftPath.darts.get iL
  let dR := B.rightPath.darts.get iR
  have hL := B.leftPath.edge_step iL
  have hR := B.rightPath.edge_step iR
  have hmemL : dL ∈ B.leftPath.darts := by
    dsimp [dL]
    exact List.get_mem _ _
  have hmemR : dR ∈ B.rightPath.darts := by
    dsimp [dR]
    exact List.get_mem _ _
  have htailL : B.map.tail dL := by
    simpa [dL] using hL.2.1
  have hstartL : dartTailVertex B.map dL = B.source := by
    calc
      dartTailVertex B.map dL = B.leftPath.vertices.get ⟨0, by
        rw [B.leftPath.vertices_length]
        simp⟩ := by
        simpa [dL] using hL.2.2.1.symm
      _ = B.source := B.leftPath.start_vertex
  have hdiff : ¬ Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv dL dR :=
    B.paths_edge_disjoint dL hmemL dR hmemR
  change B.map.tail dL ∧ dartTailVertex B.map dL = B.source ∧
    ¬ Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv dL dR
  exact ⟨htailL, hstartL, hdiff⟩

end BipolarTriangulationWithBoundary
end DirectedDistances.PlanarMap
