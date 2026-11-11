/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceSideContainment

/-! # All-index side containment for geodesic slices -/

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



theorem m0CutGeodesicLeftSide_subset_trans {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (i j k : ℤ)
    (hij : m0GeodesicSideRegion hp (P i) .left ⊆
      m0GeodesicSideRegion hp (P j) .left)
    (hjk : m0GeodesicSideRegion hp (P j) .left ⊆
      m0GeodesicSideRegion hp (P k) .left) :
    m0GeodesicSideRegion hp (P i) .left ⊆
      m0GeodesicSideRegion hp (P k) .left :=
  Set.Subset.trans hij hjk






theorem m0CutGeodesicLeftSide_subset_of_adjacentCoalescence {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (j k : ℤ) (hjk : j ≤ k) :
    m0GeodesicSideRegion hp (P j) .left ⊆
      m0GeodesicSideRegion hp (P k) .left := by
  let n : ℕ := Int.toNat (k - j)
  have hnonneg : 0 ≤ k - j := by omega
  have hncast : (n : ℤ) = k - j := by
    dsimp [n]
    exact Int.toNat_of_nonneg hnonneg
  have hindex : j + (n : ℤ) = k := by omega
  have hnested : ∀ n : ℕ,
      m0GeodesicSideRegion hp (P j) .left ⊆
        m0GeodesicSideRegion hp (P (j + (n : ℤ))) .left := by
    intro n
    induction n with
    | zero =>
        have hidx : j + ((0 : ℕ) : ℤ) = j := by omega
        rw [hidx]
    | succ n ih =>
        obtain ⟨a, b, hab⟩ := hc (j + (n : ℤ))
        have hidx₁ : (j + (n : ℤ) - 1) + 1 = j + (n : ℤ) := by omega
        have hidx₂ : (j + (n : ℤ) - 1) + 2 = (j + (n : ℤ)) + 1 := by omega
        have hab' : M0CutLeastEdgeCoalescence
            (P ((j + (n : ℤ) - 1) + 1))
            (P ((j + (n : ℤ) - 1) + 2)) a b := by
          rw [hidx₁, hidx₂]
          exact hab
        have hstep := m0CutGeodesicLeftSide_subset_succ
          P T hleft (j + (n : ℤ) - 1) a b hab'
        rw [hidx₁, hidx₂] at hstep
        have hstep' : m0GeodesicSideRegion hp (P (j + (n : ℤ))) .left ⊆
            m0GeodesicSideRegion hp (P (j + (n : ℤ) + 1)) .left := hstep
        have htrans := m0CutGeodesicLeftSide_subset_trans P j
          (j + (n : ℤ)) (j + (n : ℤ) + 1) ih hstep'
        have hidx₃ : j + ((n + 1 : ℕ) : ℤ) = j + (n : ℤ) + 1 := by omega
        rw [hidx₃]
        exact htrans
  have hresult := hnested n
  rw [hindex] at hresult
  exact hresult

end DirectedDistances.PaperProofs.Section5
