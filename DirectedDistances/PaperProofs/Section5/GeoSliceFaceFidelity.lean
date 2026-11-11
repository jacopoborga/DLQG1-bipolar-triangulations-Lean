/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceCarrierFidelity
public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice
public import DirectedDistances.PaperProofs.Section5.BoundaryGeodesicSideGluing

/-! # Face fidelity at the common tail of a geodesic slice -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: a retained face has only one of the two open-side
labels of a cut geodesic. This records exclusivity using the geometric face
classification. -/
theorem m0Geodesic_face_open_side_exclusive {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hleft : F.val ⊆ m0GeodesicSideOpenRegion hp P .left)
    (hright : F.val ⊆ m0GeodesicSideOpenRegion hp P .right) :
    False := by
  obtain ⟨s, _, huniq⟩ := m0GeodesicFace_exactly_one hp P F hFR
  have hright' := huniq .right hright
  have hleft' := huniq .left hleft
  have hbad : (ThinMapSide.right : ThinMapSide) = .left := hright'.trans hleft'.symm
  cases hbad

/-- Helper toward Lemma 5.6: a retained face bordering the forward dart of a
geodesic edge lies in its actual open left side. This is the forward mirror of
`m0Geodesic_reverse_seam_face_right`. -/
theorem m0Geodesic_forward_seam_face_left
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (P.codePath.edge i, false)) F) :
    F.val ⊆ m0GeodesicSideOpenRegion hp P .left := by
  exact boundaryGluing_forward_seam_face_left W h k longest hp P i F hFR (by
    simpa only [m0GeodesicSeam] using hb)

/-- Helper toward Lemma 5.6: no retained `faceNext` on a geodesic side's left
carrier can use a reverse seam dart, since its incident face lies on the open
right side. -/
theorem m0GeodesicSide_reverse_seam_faceNext_not_left {longest : Bool} {k : ℤ}
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) (e : ℕ × Bool) :
    ¬ (m0GeodesicSide hp P .left).faceNext (P.codePath.edge i, true) e := by
  intro hnext
  change ((∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (P.codePath.edge i, true)) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp P .left) ∧
      kmswInfFaceSucc (shiftedStream W 0) (H.1 0) (P.codePath.edge i, true) = e) at hnext
  obtain ⟨⟨F, hb, hleft⟩, _⟩ := hnext
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := by
    intro z hz
    have hz' : z ∈ m0GeodesicLeftOpen hp P := by
      simpa only [m0GeodesicSideOpenRegion] using hleft hz
    exact (m0GeodesicLeftOpen_subset hp P hz').1
  have hright := m0Geodesic_reverse_seam_face_right hp P i F hFR hb
  exact m0Geodesic_face_open_side_exclusive P F hFR hleft hright

/-- Helper toward Lemma 5.6: no retained `faceNext` on a geodesic side's right
carrier can use a forward seam dart, since its incident face lies on the open
left side. -/
theorem m0GeodesicSide_forward_seam_faceNext_not_right {longest : Bool} {k : ℤ}
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) (e : ℕ × Bool) :
    ¬ (m0GeodesicSide hp P .right).faceNext (P.codePath.edge i, false) e := by
  intro hnext
  change ((∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (P.codePath.edge i, false)) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp P .right) ∧
      kmswInfFaceSucc (shiftedStream W 0) (H.1 0) (P.codePath.edge i, false) = e) at hnext
  obtain ⟨⟨F, hb, hright⟩, _⟩ := hnext
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := by
    change F.val ⊆ m0GeodesicAmbientRegion W H h ∩
      (closure (m0GeodesicLeftOpen hp P))ᶜ at hright
    intro z hz
    exact (hright hz).1
  have hleft := m0Geodesic_forward_seam_face_left hp P i F hFR hb
  exact m0Geodesic_face_open_side_exclusive P F hFR hleft hright

/-- Helper toward Lemma 5.6: a retained face bordering either dart of a common
tail edge is not in the right/left open-side intersection defining the slice.
The aligned tail is identified as the same whole-plane edge on both paths. -/
theorem m0CutGeodesicSlice_common_tail_face_not_retained {longest : Bool}
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b n : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (isReverse : Bool)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 ((P (k - 1)).codePath.edge (a + n), isReverse)) F) :
    ¬ (F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left) := by
  have htail := hab.1 n
  have hedge := wholePlaneEdgeι_injective W 0 htail
  have hdart : wholePlaneDartι W 0 ((P (k - 1)).codePath.edge (a + n), isReverse) =
      wholePlaneDartι W 0 ((P k).codePath.edge (b + n), isReverse) :=
    congrArg (fun e => wholePlaneDartι W 0 (e, isReverse)) hedge
  cases isReverse with
  | true =>
      have hb' : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 ((P k).codePath.edge (b + n), true)) F := by
        rw [← hdart]
        exact hb
      have hright := m0Geodesic_reverse_seam_face_right hp (P k) (b + n) F hFR hb'
      intro hret
      exact m0Geodesic_face_open_side_exclusive (P k) F hFR hret.2 hright
  | false =>
      have hleft := m0Geodesic_forward_seam_face_left hp (P (k - 1)) (a + n) F hFR hb
      intro hret
      exact m0Geodesic_face_open_side_exclusive (P (k - 1)) F hFR hleft hret.1

/-- Helper toward Lemma 5.6: no `faceNext` pair of the slice has a dart on
the aligned common tail, in either orientation. -/
theorem m0CutGeodesicSlice_common_tail_faceNext_false {longest : Bool}
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b n : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (isReverse : Bool) (e : ℕ × Bool) :
    ¬ (m0CutGeodesicSlice (hp := hp) P k a b hab).faceNext
      ((P (k - 1)).codePath.edge (a + n), isReverse) e := by
  have htail := hab.1 n
  have hedge := wholePlaneEdgeι_injective W 0 htail
  have hdart : wholePlaneDartι W 0 ((P (k - 1)).codePath.edge (a + n), isReverse) =
      wholePlaneDartι W 0 ((P k).codePath.edge (b + n), isReverse) :=
    congrArg (fun edge => wholePlaneDartι W 0 (edge, isReverse)) hedge
  have hfaces := (m0CutGeodesicSlice_faceNext_iff (hp := hp) P k a b hab
    ((P (k - 1)).codePath.edge (a + n), isReverse) e).mp
  cases isReverse with
  | true =>
      intro hnext
      have hside := hfaces hnext
      have hcurrent : (m0GeodesicSide hp (P k) .left).faceNext
          ((P k).codePath.edge (b + n), true) e := by
        rw [← hedge]
        exact hside.2
      exact m0GeodesicSide_reverse_seam_faceNext_not_left hp (P k) (b + n) e hcurrent
  | false =>
      intro hnext
      have hside := hfaces hnext
      exact m0GeodesicSide_forward_seam_faceNext_not_right hp (P (k - 1))
        (a + n) e hside.1

































end DirectedDistances.PaperProofs.Section5
