/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlanePastGlueM0Restriction
public import DirectedDistances.PlanarMap.PLDrawingFaceTransfer

/-! not a paper result. -/

public section
namespace DirectedDistances.KMSW.WholePlaneGlueFaceOrbits

open DirectedDistances.PlanarMap WholePlanePastGlueData

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0)
  (monotone_family_all w0)
local notation "wp" => kmswPastCode W
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "Pt" => WholePlanePastGlueData.pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hp H

/-- correspondence); not a paper result. Every bounded run-zero face is preserved
with its exact dart-border relation in the glued drawing. -/
theorem glueFaceOrbits_runZero_dartBorders (d : ℕ × Bool)
    (F0 : (P0).Face) (hF0 : ¬ (P0).IsUnbounded F0) :
    ∃ F : (G).Face, F.val = F0.val ∧
      ((G).dartBorders (wholePlaneDartι W 0 d) F ↔ (P0).dartBorders d F0) := by
  obtain ⟨F, hF⟩ :=
    WholePlanePastGlueM0Restriction.bounded_face_is_glued_face W h0 hp H F0 hF0
  have harc : (G).arc (wholePlaneDartι W 0 d) = (P0).arc d :=
    WholePlanePastGlueM0Restriction.restrict_arc W h0 hp H d
  exact ⟨F, hF,
    PLDrawing.dartBorders_congr P0 G F0 F harc hF⟩

/-- correspondence); not a paper result. An off-seam past dart has exactly the same
dart-border relation as its transferred past-drawing face. -/
theorem glueFaceOrbits_past_dartBorders_transfer (d : ℕ × Bool)
    (hv : ∀ k : ℤ, kmswLimitDartVertex wp d ≠ boundaryVertex wp hp k)
    (Fp : (Pp).Face)
    (hFp : ¬ (Pp).IsUnbounded Fp) :
    ∃ FpT : (Pt).Face, ∃ F : (G).Face,
      FpT.val = T '' Fp.val ∧ F.val = T '' Fp.val ∧
        ((G).dartBorders (kmswPastDart W d) F ↔ (Pt).dartBorders d FpT) := by
  obtain ⟨_, hfaces, _⟩ := PLDrawing.face_image_of_transfer Pp T Pt
      (WholePlanePastGlueData.pastDrawing_pos W h0 hp H)
      (fun e => (WholePlanePastGlueData.pastDrawing_arc W h0 hp H e).1)
  obtain ⟨FpT, hFpT⟩ := hfaces Fp
  obtain ⟨z, _, hzG, hcomp⟩ :=
    WholePlanePastGlueFacesLower.glued_component_of_past_boundedFace
      W h0 hp H Fp hFp
  have hzImage : z ∉ (G).image := by
    rw [WholePlanePastGlueDrawing.glueDrawing_image]
    exact hzG
  let F : (G).Face :=
    ⟨connectedComponentIn (G).imageᶜ z, z, hzImage, rfl⟩
  have hF : F.val = T '' Fp.val := by
    change connectedComponentIn (G).imageᶜ z = T '' Fp.val
    rw [WholePlanePastGlueDrawing.glueDrawing_image]
    exact hcomp
  have hd : ¬ kmswPastSeamEdge W d.1 := by
    intro hs
    obtain ⟨j, hseam⟩ := kmswPastSeamEdge_image_boundary W h0 d.1 hs
    have hmatch : kmswPastEdge W (boundaryOuterEdge wp hp (-j)) =
        wholePlaneEdgeι W 0 (boundaryOuterEdge w0 h0 j) := by
      simpa only [neg_neg] using kmswPastEdge_seam_match_neg W h0 hp (-j)
    have he : d.1 = boundaryOuterEdge wp hp (-j) :=
      kmswPastEdge_injective W (hseam.trans hmatch.symm)
    cases hb : d.2
    · apply hv (-j)
      simpa [kmswLimitDartVertex, hb, he] using
        (boundaryOuterEdge_endpoints wp hp (-j)).1
    · apply hv (-j + 1)
      simpa [kmswLimitDartVertex, hb, he] using
        ((boundaryOuterEdge_endpoints wp hp (-j)).2.1)
  have harc : (G).arc (kmswPastDart W d) = (Pt).arc d :=
    WholePlanePastGlueData.gluedArc_past W h0 hp H d hd
  have hborder :=
    PLDrawing.dartBorders_congr Pt G FpT F harc (hF.trans hFpT.symm)
  exact ⟨FpT, F, hFpT, hF, hborder⟩

end DirectedDistances.KMSW.WholePlaneGlueFaceOrbits
