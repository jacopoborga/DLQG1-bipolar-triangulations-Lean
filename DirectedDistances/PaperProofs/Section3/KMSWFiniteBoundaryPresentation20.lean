/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation16
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation17

/- The present outer runs inherit their external winding-side witnesses from the -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: each present UL run dart has the map's
forward orientation and an external left-face witness, and each present LR
run dart has the reverse orientation and an external right-face witness. -/
theorem kmswStageFiniteBoundaryPresentation20_present_run_side_witnesses
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    (∀ i : Fin (kmswStageULDartRun w n).length,
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing
          ((kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts i).1,
        ((kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts i).2 =
          M.forward ⟨((kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts i).1, hp⟩ ∧
        ∃ F : (Drawing M).Face,
          (Drawing M).IsExternal F ∧
            LeftOf M F ⟨((kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts i).1, hp⟩) ∧
    (∀ i : Fin (kmswStageLRDartRun w n).length,
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing
          ((kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts i).1,
        ((kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts i).2 =
          !(M.forward ⟨((kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts i).1, hp⟩) ∧
        ∃ F : (Drawing M).Face,
          (Drawing M).IsExternal F ∧
            RightOf M F ⟨((kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts i).1, hp⟩) := by
  constructor
  · have hUL := kmswStageFiniteBoundaryPresentation16_upperLeft_ok
      w n P U hU hborder M J hreal
    have hUL' := (ULOkInf_iff
      (kmswStageFiniteBoundaryPresentation w n M J)).mp hUL
    intro i
    exact hUL'.1 i
  · have hLR := kmswStageFiniteBoundaryPresentation16_lowerRight_ok
      w n P U hU hborder M J hreal
    have hLR' := (LROkInf_iff
      (kmswStageFiniteBoundaryPresentation w n M J)).mp hLR
    intro i
    exact hLR'.1 i

/-- Helper toward Definition 3.2: every present outer stage dart occurs in
the UL or LR run and inherits the corresponding external map-side witness. -/
theorem kmswStageFiniteBoundaryPresentation20_present_outer_dart_witness
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (d : StageDart (kmswStage w n).nextEdge)
    (houter : (kmswStageDirectedMap w n).IsOuter d)
    (hp : ¬ M.toPlaneMapWithMissing.missing d.1) :
    (∃ i : Fin (kmswStageULDartRun w n).length,
      (kmswStageULDartRun w n)[i.val]'i.isLt = d ∧
      ∃ hp' : ¬ M.toPlaneMapWithMissing.missing
          ((kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts i).1,
        ((kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts i).2 =
          M.forward ⟨((kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts i).1, hp'⟩ ∧
        ∃ F : (Drawing M).Face,
          (Drawing M).IsExternal F ∧
            LeftOf M F ⟨((kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts i).1, hp'⟩) ∨
    (∃ i : Fin (kmswStageLRDartRun w n).length,
      (kmswStageLRDartRun w n)[i.val]'i.isLt = d ∧
      ∃ hp' : ¬ M.toPlaneMapWithMissing.missing
          ((kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts i).1,
        ((kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts i).2 =
          !(M.forward ⟨((kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts i).1, hp'⟩) ∧
        ∃ F : (Drawing M).Face,
          (Drawing M).IsExternal F ∧
            RightOf M F ⟨((kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts i).1, hp'⟩) := by
  have hside := kmswStageFiniteBoundaryPresentation20_present_run_side_witnesses
    w n P U hU hborder M J hreal
  rcases kmswStage_finite_outer_dart_run_partition w n d houter with
    hUL | hUR | hLR | hLL
  · have hmem : d ∈ kmswStageULDartRun w n := by
      simpa [kmswStageULDartsFinset] using hUL.1
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
    let i : Fin (kmswStageULDartRun w n).length := ⟨k, hk⟩
    refine Or.inl ⟨i, ?_, hside.1 i⟩
    simpa [i] using hget
  · have hmissStage :=
      ((kmswStageURDartsFinset_map_mem w n d).mp hUR.1).1
    have hmissMap : M.toPlaneMapWithMissing.missing d.1 := by
      rw [hreal.2.2.2.1 d.1]
      exact hmissStage
    exact (hp hmissMap).elim
  · have hmem : d ∈ kmswStageLRDartRun w n := by
      simpa [kmswStageLRDartsFinset] using hLR.1
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
    let i : Fin (kmswStageLRDartRun w n).length := ⟨k, hk⟩
    refine Or.inr ⟨i, ?_, hside.2 i⟩
    simpa [i] using hget
  · have hmissStage :=
      ((kmswStageLLDartsFinset_map_mem w n d).mp hLL.1).1
    have hmissMap : M.toPlaneMapWithMissing.missing d.1 := by
      rw [hreal.2.2.2.1 d.1]
      exact hmissStage
    exact (hp hmissMap).elim










































































































































end DirectedDistances.PaperProofs.Section3

end
