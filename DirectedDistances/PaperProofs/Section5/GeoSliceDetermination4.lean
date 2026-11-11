/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination3
public import DirectedDistances.PaperProofs.Section5.GeoSliceGeometricCarrier3
public import DirectedDistances.PaperProofs.Section5.GeoSliceSideContainment4
public import DirectedDistances.PaperProofs.Section5.GeoSliceSideContainmentRight2

/-! # Face carrier and determination of geodesic slices -/

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






theorem m0CutGeodesicSlice_face_successors_eq_common_side_face_successors
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    {p : (ℕ × Bool) × (ℕ × Bool) |
      (m0CutGeodesicSlice (hp := hp) P k a b hab).faceNext p.1 p.2} =
    {p : (ℕ × Bool) × (ℕ × Bool) |
      (m0GeodesicSide hp (P (k - 1)) .right).faceNext p.1 p.2 ∧
        (m0GeodesicSide hp (P k) .left).faceNext p.1 p.2} := by
  ext p
  exact m0CutGeodesicSlice_faceNext_iff (hp := hp) P k a b hab p.1 p.2

/- theorem m0CutGeodesicSlice_face_identification {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face) :
    the source predicate that F is a face of M₀,∞ lying between the finite
    segments P_{x_{k-1}}([1, θ_k^-]) and P_{x_k}([1, θ_k]) iff F is represented
    by the face-successor relation of
      m0CutGeodesicSlice (hp := hp) P k a b hab.

The source predicate on the left is not currently defined in Lean. The
candidate carrier supplies `faceNext` by intersecting the two whole-side
relations, as proved above, but no available declaration proves that this
intersection selects exactly the faces enclosed by the two finite segments.
Consequently this equivalence is not stated as a Lean proposition or assumed
identification, so work stops here. -/

end DirectedDistances.PaperProofs.Section5
