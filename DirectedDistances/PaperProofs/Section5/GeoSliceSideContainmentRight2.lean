/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceSideContainmentRight

/-! # All-index right-side containment for geodesic slices -/

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





theorem m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (j k : ℤ) (hjk : j ≤ k) :
    m0GeodesicSideRegion hp (P k) .right ⊆
      m0GeodesicSideRegion hp (P j) .right := by
  let n : ℕ := (k - j).toNat
  have hdiff : 0 ≤ k - j := by omega
  have hn : (n : ℤ) = k - j := by
    dsimp [n]
    exact Int.toNat_of_nonneg hdiff
  have hkn : j + (n : ℤ) = k := by omega
  have hnest : ∀ r : ℕ,
      m0GeodesicSideRegion hp (P (j + (r : ℤ))) .right ⊆
        m0GeodesicSideRegion hp (P j) .right := by
    intro r
    induction r with
    | zero =>
        change m0GeodesicSideRegion hp (P (j + (0 : ℤ))) .right ⊆ _
        rw [Int.add_zero]
    | succ r ih =>
        obtain ⟨a, b, hab⟩ := hc (j + (r : ℤ))
        have hidx₁ : (j + (r : ℤ) - 1) + 1 = j + (r : ℤ) := by omega
        have hidx₂ : (j + (r : ℤ) - 1) + 2 = j + (r : ℤ) + 1 := by omega
        have hab' : M0CutLeastEdgeCoalescence
            (P ((j + (r : ℤ) - 1) + 1))
            (P ((j + (r : ℤ) - 1) + 2)) a b := by
          rw [hidx₁, hidx₂]
          exact hab
        have hstep := m0CutGeodesicRightSide_subset_succ
          P T hleft (j + (r : ℤ) - 1) a b hab'
        have hstep' : m0GeodesicSideRegion hp
            (P (j + (r : ℤ) + 1)) .right ⊆
              m0GeodesicSideRegion hp (P (j + (r : ℤ))) .right := by
          rw [hidx₁, hidx₂] at hstep
          exact hstep
        have hcast : j + ((r + 1 : ℕ) : ℤ) = j + (r : ℤ) + 1 := by omega
        rw [hcast]
        exact hstep'.trans ih
  have hresult := hnest n
  rw [hkn] at hresult
  exact hresult





theorem m0CutGeodesicPrecoalescenceEdges_mem_right_side_of_le_index_of_adjacentCoalescence
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (j k : ℤ) (hjk : j ≤ k) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b) :
    ∀ i < b,
      (P k).codePath.edge i ∈ m0GeodesicSideEdges hp (P j) .right := by
  intro i hi
  by_cases hjkeq : j = k
  · subst j
    exact m0GeodesicEdges_subset_right hp (P k) ⟨i, rfl⟩
  · have hjklt : j < k := by omega
    have hjkm1 : j ≤ k - 1 := by omega
    have hidx : (k - 1 : ℤ) + 1 = k := by omega
    have hab' : M0CutLeastEdgeCoalescence
        (P (k - 1)) (P ((k - 1) + 1)) a b := by
      rw [hidx]
      exact hab
    have hedge' := m0CutGeodesicPrecoalescenceEdges_mem_right_side_succ
      P T hleft (k - 1) a b hab'
    rw [hidx] at hedge'
    have hedge : (P k).codePath.edge i ∈
        m0GeodesicSideEdges hp (P (k - 1)) .right := by
      exact hedge' i hi
    have hside := m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
      P T hleft hc j (k - 1) hjkm1
    change ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 ((P k).codePath.edge i, false))).image ⊆
        m0GeodesicSideRegion hp (P (k - 1)) .right at hedge
    change ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 ((P k).codePath.edge i, false))).image ⊆
        m0GeodesicSideRegion hp (P j) .right
    exact hedge.trans hside

end DirectedDistances.PaperProofs.Section5
