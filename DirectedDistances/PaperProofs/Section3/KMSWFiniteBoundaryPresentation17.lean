/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation14

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: a realization has exactly the same drawing
image as the plane drawing obtained from its stage PL drawing. -/
theorem kmswStageFiniteBoundaryPresentation17_realization_image_eq
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    (Drawing M).image = P.toPlaneGraphDrawing.image := by
  let P' : PLDrawing (StageDart (kmswStage w n).nextEdge)
      (Fin (kmswStage w n).nextVertex) (edgeFlip _) (stageRot w n)
      (stageVertex w n) := P
  rcases hreal with ⟨hpos, _, harc, _, _⟩
  change M.toPlaneMapWithMissing.pos = P'.pos at hpos
  change ∀ d, Set.range (M.toPlaneMapWithMissing.arc d.1) =
    Set.range (P'.arc d).toPath at harc
  rw [P'.toPlaneGraphDrawing_image]
  change Set.range M.toPlaneMapWithMissing.pos ∪
      ⋃ e, Set.range (M.toPlaneMapWithMissing.arc e) = P'.image
  ext z
  constructor
  · intro hz
    rcases hz with hz | hz
    · left
      rw [hpos] at hz
      exact hz
    · right
      rcases Set.mem_iUnion.mp hz with ⟨e, he⟩
      have he' : z ∈ (P'.arc (e, false)).image := by
        rw [← Polyline.range_toPath]
        rw [← harc (e, false)]
        exact he
      exact ⟨(e, false), he'⟩
  · intro hz
    change z ∈ Set.range P'.pos ∪ {z | ∃ d, z ∈ (P'.arc d).image} at hz
    rcases hz with hz | ⟨⟨e, b⟩, he⟩
    · left
      rw [hpos]
      exact hz
    · right
      apply Set.mem_iUnion.mpr
      refine ⟨e, ?_⟩
      cases b with
      | false =>
          rw [harc (e, false), Polyline.range_toPath]
          exact he
      | true =>
          have he' : z ∈ (P'.arc (e, false)).image := by
            have hflip : (P'.arc (e, true)).image =
                (P'.arc (e, false)).image := by
              simpa [edgeFlip] using P'.arc_image_flip (e, false)
            exact hflip ▸ he
          rw [harc (e, false), Polyline.range_toPath]
          exact he'

/-- Helper toward Definition 3.2: realized and stage drawings have the same
complementary face carrier. -/
theorem kmswStageFiniteBoundaryPresentation17_face_carrier_eq
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    (Drawing M).Face = P.toPlaneGraphDrawing.Face := by
  have himage := kmswStageFiniteBoundaryPresentation17_realization_image_eq
    w n P M hreal
  unfold PlaneGraphDrawing.Face
  rw [himage]































































































































end DirectedDistances.PaperProofs.Section3

end
