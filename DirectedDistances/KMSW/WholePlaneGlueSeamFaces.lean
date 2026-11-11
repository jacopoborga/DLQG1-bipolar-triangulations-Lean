/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlaneGlueFaceOrbits
import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsIff

/-! not a paper result. -/

public section
namespace DirectedDistances.KMSW.WholePlaneGlueSeamFaces

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
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hp H

/-- not a paper result. A run-zero creation dart borders a glued face. -/
theorem glueSeamFaces_runZero_creation_dartBorders (d : ℕ × Bool)
    (j : TriangleCreationTime w0) (hd : d ∈ stageTriangleDartList w0 j) :
    ∃ F : (G).Face, (G).dartBorders (wholePlaneDartι W 0 d) F := by
  let F0 : (P0).Face := capFace w0 ((And.left H) 0) j
  have hF0 : ¬ (P0).IsUnbounded F0 := by
    exact capFace_isBounded_face w0 ((And.left H) 0) j
  have hdF0 : (P0).dartBorders d F0 :=
    (cap_border_iff w0 ((And.left H) 0) j d).2 hd
  obtain ⟨F, _, hborder⟩ :=
    WholePlaneGlueFaceOrbits.glueFaceOrbits_runZero_dartBorders
      W h0 hp H d F0 hF0
  exact ⟨F, hborder.mpr hdF0⟩

/-- not a paper result. A glued dart borders at most one glued face. -/
theorem glueSeamFaces_dartBorders_unique (D : WholePlaneDart W)
    (F F' : (G).Face) (hF : (G).dartBorders D F)
    (hF' : (G).dartBorders D F') : F = F' := by
  obtain ⟨delta1, hdelta1, hmem1⟩ := hF
  obtain ⟨delta2, hdelta2, hmem2⟩ := hF'
  let t := min delta1 delta2 / 2
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have ht1 : t < delta1 := by
    have hmin := min_le_left delta1 delta2
    dsimp [t]
    linarith
  have ht2 : t < delta2 := by
    have hmin := min_le_right delta1 delta2
    dsimp [t]
    linarith
  apply (G).faces_eq_of_mem
  · exact hmem1 t t ht ht1 ht ht1
  · exact hmem2 t t ht ht2 ht ht2

/-- not a paper result. A run-zero creation dart borders exactly one glued face. -/
theorem glueSeamFaces_runZero_creation_dartBorders_unique (d : ℕ × Bool)
    (j : TriangleCreationTime w0) (hd : d ∈ stageTriangleDartList w0 j) :
    ∃! F : (G).Face, (G).dartBorders (wholePlaneDartι W 0 d) F := by
  obtain ⟨F, hF⟩ := glueSeamFaces_runZero_creation_dartBorders W h0 hp H d j hd
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  exact glueSeamFaces_dartBorders_unique W h0 hp H _ F' F hF' hF

/-- not a paper result. The past dart paired with a run-zero outer seam dart borders
a bounded creation face in the original past drawing. -/
theorem glueSeamFaces_past_outer_dart_has_bounded_sourceFace (k : ℤ) :
    ∃ Fp : (Pp).Face, ∃ F : (G).Face,
      ¬ (Pp).IsUnbounded Fp ∧
      (Pp).dartBorders (boundaryOuterEdge wp hp (-k), false) Fp ∧
      F.val = T '' Fp.val ∧
      wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 k) =
        kmswPastDart W (boundaryOuterEdge wp hp (-k), false) := by
  let d : ℕ × Bool := (boundaryOuterEdge wp hp (-k), false)
  have hnot : ¬ (kmswInfFaceSucc wp (past_finiteIncidence W H)).SameCycle
      futureMapOuterDart d := by
    intro hcycle
    obtain ⟨j, hj, _⟩ :=
      (futureMap_outerOrbit_iff_existsUnique wp (past_finiteIncidence W H) hp d).mp hcycle
    have hb := congrArg Prod.snd hj
    simp only [d, futureMapBoundaryDart] at hb
    cases hb
  have horbit := DirectedDistances.KMSW.dart_outer_or_creation
    wp (past_finiteIncidence W H) hp d
  obtain ⟨⟨j, hd⟩, _⟩ := horbit.resolve_left (fun h => hnot h.1)
  let Fp : (Pp).Face := capFace wp (past_finiteIncidence W H) j
  have hFp : ¬ (Pp).IsUnbounded Fp :=
    capFace_isBounded_face wp (past_finiteIncidence W H) j
  have hdFp : (Pp).dartBorders d Fp :=
    (cap_border_iff wp (past_finiteIncidence W H) j d).2 hd
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
  exact ⟨Fp, F, hFp, hdFp, hF,
    (DirectedDistances.KMSW.wholePlaneDart_runZero_outer_splice
      W H (past_finiteIncidence W H) hp h0 k).1⟩

/-- not a paper result. Any face bordered by a run-zero outer seam dart is a transferred
past face. -/
theorem glueSeamFaces_runZero_outer_borderedFace_isPast (k : ℤ) (F : (G).Face)
    (hF : (G).dartBorders
      (wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 k)) F) :
    ∃ Fp : (Pp).Face, ¬ (Pp).IsUnbounded Fp ∧ F.val = T '' Fp.val := by
  rcases WholePlanePastGlueDrawing.glueDrawing_faces W h0 hp H F with
    ⟨F0, hF0, hval⟩ | ⟨Fp, hFp, hval⟩
  · have harc :
        (G).arc (wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 k)) =
          (P0).arc (futureMapBoundaryDart w0 h0 k) :=
      WholePlanePastGlueM0Restriction.restrict_arc W h0 hp H
        (futureMapBoundaryDart w0 h0 k)
    have hborder :=
      PLDrawing.dartBorders_congr P0 G F0 F harc hval
    have hF0border :
        (P0).dartBorders (futureMapBoundaryDart w0 h0 k) F0 := hborder.mp hF
    have houter :
        (kmswInfFaceSucc w0 ((And.left H) 0)).SameCycle futureMapOuterDart
          (futureMapBoundaryDart w0 h0 k) := by
      exact (futureMap_outerOrbit_iff_existsUnique w0 ((And.left H) 0) h0
        (futureMapBoundaryDart w0 h0 k)).2
          ⟨k, rfl, fun j hj =>
            (futureMapBoundaryDart_injective w0 h0 hj).symm⟩
    obtain ⟨U, hU, _, hUborder, _, _, _⟩ :=
      monotoneFamilyDrawing_realized_boundary_twoSided w0 ((And.left H) 0) h0
    have hUdart : (P0).dartBorders (futureMapBoundaryDart w0 h0 k) U :=
      (hUborder (futureMapBoundaryDart w0 h0 k)).2 houter
    have hEq := DirectedDistances.KMSW.dart_border_face_unique
      w0 ((And.left H) 0) (futureMapBoundaryDart w0 h0 k) F0 U hF0border hUdart
    exact (hF0 (hEq ▸ hU)).elim
  · exact ⟨Fp, hFp, hval⟩

end DirectedDistances.KMSW.WholePlaneGlueSeamFaces
