/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceSideContainment3
public import DirectedDistances.PaperProofs.Section5.GeoSliceSideContainmentRight2
public import DirectedDistances.PaperProofs.Section5.GeoSliceAdjacentCoalescence

/-! # Almost-sure all-index side containment for geodesic slices -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1






theorem m0Cut_ae_leftmost_xdp_all_index_closed_side_containment :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) →
          Q = P k) ∧
        (∀ j k : ℤ, j ≤ k →
          m0GeodesicSideRegion hp (P j) .left ⊆
            m0GeodesicSideRegion hp (P k) .left) ∧
        ∀ j k : ℤ, j ≤ k →
          m0GeodesicSideRegion hp (P k) .right ⊆
            m0GeodesicSideRegion hp (P j) .right := by
  filter_upwards
    [m0Cut_ae_leftmost_xdp_adjacent_least_coalescence] with W hW
  obtain ⟨H, h, hLL, hp, hselected⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨R, T, P, hR, hleft, huniq, hc⟩ := hselected longest
  refine ⟨R, T, P, hR, hleft, huniq, ?_, ?_⟩
  · intro j k hjk
    exact m0CutGeodesicLeftSide_subset_of_adjacentCoalescence
      P T hleft hc j k hjk
  · intro j k hjk
    exact m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
      P T hleft hc j k hjk

end DirectedDistances.PaperProofs.Section5

