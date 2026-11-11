/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceGeometricCarrier2

/-! # Ordering of adjacent geodesic slices -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}





theorem m0CutAdjacentGeodesicSegments_mem_own_closed_sides {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    ((P (k - 1)).codePath.initial a).1 = ((P k).codePath.initial b).1 ∧
      ((∀ i < a,
        (P (k - 1)).codePath.edge i ∈
          m0GeodesicSideEdges hp (P (k - 1)) .left ∩
            m0GeodesicSideEdges hp (P (k - 1)) .right) ∧
        (∀ j < b,
          (P k).codePath.edge j ∈
            m0GeodesicSideEdges hp (P k) .left ∩
              m0GeodesicSideEdges hp (P k) .right)) := by
  refine ⟨m0Cut_least_edge_coalescence_initial_vertex_eq P k hab, ⟨?_, ?_⟩⟩
  · intro i _
    exact m0CutGeodesicEdges_subset_both_closed_sides (P (k - 1)) ⟨i, rfl⟩
  · intro j _
    exact m0CutGeodesicEdges_subset_both_closed_sides (P k) ⟨j, rfl⟩





















end DirectedDistances.PaperProofs.Section5
