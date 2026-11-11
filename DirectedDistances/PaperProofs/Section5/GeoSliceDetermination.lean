/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceSideContainment4
public import DirectedDistances.PaperProofs.Section5.GeoSliceGeometricCarrier3

/-! # Determination of geodesic slices from a closed side -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section1






theorem m0Cut_ae_geodesicSlice_left_right_side_containment :
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
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) →
          Q = P k) ∧
        (∀ j : ℤ, ∃ a b : ℕ,
          M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) ∧
        (∀ j k : ℤ, j ≤ k →
          m0GeodesicSideRegion hp (P j) .left ⊆
            m0GeodesicSideRegion hp (P k) .left) ∧
        (∀ j k : ℤ, j ≤ k →
          m0GeodesicSideRegion hp (P k) .right ⊆
            m0GeodesicSideRegion hp (P j) .right) ∧
        (∀ j k : ℤ, j ≤ k → ∀ a b : ℕ,
          (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) →
          (m0CutGeodesicSlice (hp := hp) P j a b hab).vertices ⊆
              m0GeodesicSideVertices hp (P k) .left ∧
            (m0CutGeodesicSlice (hp := hp) P j a b hab).edges ⊆
              m0GeodesicSideEdges hp (P k) .left) ∧
        (∀ k j : ℤ, k < j → ∀ a b : ℕ,
          (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) →
          (m0CutGeodesicSlice (hp := hp) P j a b hab).vertices ⊆
              m0GeodesicSideVertices hp (P k) .right ∧
            (m0CutGeodesicSlice (hp := hp) P j a b hab).edges ⊆
              m0GeodesicSideEdges hp (P k) .right) := by
  filter_upwards [m0Cut_ae_leftmost_xdp_adjacent_least_coalescence]
    with W hW
  obtain ⟨H, h, hLL, hp, hselected⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨_, T, P, _, hleft, huniq, hc⟩ :=
    hselected longest
  have hleftSide : ∀ j k : ℤ, j ≤ k →
      m0GeodesicSideRegion hp (P j) .left ⊆
        m0GeodesicSideRegion hp (P k) .left := by
    intro j k hjk
    exact m0CutGeodesicLeftSide_subset_of_adjacentCoalescence
      P T hleft hc j k hjk
  have hrightSide : ∀ j k : ℤ, j ≤ k →
      m0GeodesicSideRegion hp (P k) .right ⊆
        m0GeodesicSideRegion hp (P j) .right := by
    intro j k hjk
    exact m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
      P T hleft hc j k hjk
  refine ⟨P, T, hleft, huniq, ?_, hleftSide, hrightSide, ?_, ?_⟩
  · intro j
    obtain ⟨a, b, hab⟩ := hc (j - 1)
    have hidx : (j - 1 : ℤ) + 1 = j := by omega
    rw [hidx] at hab
    exact ⟨a, b, hab⟩
  · intro j k hjk a b hab
    constructor
    · intro v hv
      have hmem :=
        (m0CutGeodesicSlice_mem_vertices_iff (hp := hp) P j a b hab v).1 hv
      exact hleftSide j k hjk hmem.1.2
    · intro e he z hz
      have hmem :=
        (m0CutGeodesicSlice_mem_edges_iff (hp := hp) P j a b hab e).1 he
      exact hleftSide j k hjk (hmem.1.2 hz)
  · intro k j hkj a b hab
    have hkj' : k ≤ j - 1 := by omega
    have hrightSide' := hrightSide k (j - 1) hkj'
    constructor
    · intro v hv
      have hmem :=
        (m0CutGeodesicSlice_mem_vertices_iff (hp := hp) P j a b hab v).1 hv
      exact hrightSide' hmem.1.1
    · intro e he z hz
      have hmem :=
        (m0CutGeodesicSlice_mem_edges_iff (hp := hp) P j a b hab e).1 he
      exact hrightSide' (hmem.1.1 hz)

















































end DirectedDistances.PaperProofs.Section5
