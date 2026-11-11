/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect2






public section

namespace DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: at a strict point of a drawn segment,
one small left half-disk lies in exactly the face bordered by the forward
dart, and the right half-disk lies in exactly the face bordered by its reverse.
The radius works for both sides. This is geometric side identification; it
does not assert that a winding-based `LeftAtOn` witness selects the left side. -/
theorem exists_unique_oriented_halfDisc_faces_of_openSegment
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) {p : ℂ}
    (hp : p ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧
      (∃! F : P.Face,
        Polyline.leftHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
          ⊆ F.val ∧ P.dartBorders d F) ∧
      (∃! F : P.Face,
        Polyline.rightHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
          ⊆ F.val ∧ P.dartBorders (flip d) F) := by
  obtain ⟨r, hr, hleft, hright, _⟩ :=
    exists_openSegment_halfDiscs_face_classification P hfinite d hi hp
  have hleftUnique : ∃! F : P.Face,
      Polyline.leftHalfDisc p
          ((P.arc d).point (i + 1) - (P.arc d).point i) r ⊆ F.val ∧
        P.dartBorders d F := by
    obtain ⟨F, hF, hFuniq⟩ :=
      P.dartBorders_existsUnique_of_locallyFiniteVertexImage32 hfinite d
    refine ⟨F, ⟨(hleft F).2 hF, hF⟩, ?_⟩
    intro G hG
    exact hFuniq G hG.2
  have hrightUnique : ∃! F : P.Face,
      Polyline.rightHalfDisc p
          ((P.arc d).point (i + 1) - (P.arc d).point i) r ⊆ F.val ∧
        P.dartBorders (flip d) F := by
    obtain ⟨F, hF, hFuniq⟩ :=
      P.dartBorders_existsUnique_of_locallyFiniteVertexImage32 hfinite (flip d)
    refine ⟨F, ⟨(hright F).2 hF, hF⟩, ?_⟩
    intro G hG
    exact hFuniq G hG.2
  exact ⟨r, hr, hleftUnique, hrightUnique⟩























































































end DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk
