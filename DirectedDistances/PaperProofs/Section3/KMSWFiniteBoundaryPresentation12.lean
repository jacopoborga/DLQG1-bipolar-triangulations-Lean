/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation11
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation3
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation4

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the supplied stage exterior-face
characterization is exactly the four-run dart coverage for the finite
presentation. -/
theorem kmswStageFiniteBoundaryPresentation12_dart_coverage
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hunique : ∀ F : P.Face, P.IsUnbounded F → F = U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (U' : P.Face) (hU' : P.IsUnbounded U') :
    ∀ d, P.dartBorders d U' ↔ ∃ i : InfiniteBoundaryDartIndex
      (kmswStageFiniteBoundaryPresentation w n M J),
      InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) i = d := by
  let Q := kmswStageFiniteBoundaryPresentation w n M J
  have hsplit : stageOuterWord w n =
      kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n := by
    simp [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
      kmswStageLRDartRun, kmswStageLLDartRun]
  have hmemUL : ∀ i : Fin (kmswStageULDartRun w n).length,
      (kmswStageULDartRun w n)[i.val]'i.isLt ∈ stageOuterWord w n := by
    intro i
    simpa [hsplit] using List.getElem_mem i.isLt
  have hmemUR : ∀ i : Fin (kmswStageURDartRun w n).length,
      (kmswStageURDartRun w n)[i.val]'i.isLt ∈ stageOuterWord w n := by
    intro i
    simpa [hsplit] using List.getElem_mem i.isLt
  have hmemLR : ∀ i : Fin (kmswStageLRDartRun w n).length,
      (kmswStageLRDartRun w n)[i.val]'i.isLt ∈ stageOuterWord w n := by
    intro i
    simpa [hsplit] using List.getElem_mem i.isLt
  have hmemLL : ∀ i : Fin (kmswStageLLDartRun w n).length,
      (kmswStageLLDartRun w n)[i.val]'i.isLt ∈ stageOuterWord w n := by
    intro i
    simpa [hsplit] using List.getElem_mem i.isLt
  intro d
  constructor
  · intro hd
    have hEq : U' = U := hunique U' hU'
    subst U'
    have hout := (hborder d).1 hd
    have hpart := kmswStage_finite_outer_dart_run_partition w n d hout
    rcases hpart with hUL | hUR | hLR | hLL
    · have hm : d ∈ kmswStageULDartRun w n := by
        simpa [kmswStageULDartsFinset] using hUL.1
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hm
      refine ⟨.upperLeft ⟨i, hi⟩, ?_⟩
      simp only [InfiniteBoundaryDartIndex.dart_eq,
        kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide]
      exact hget
    · have hm : d ∈ kmswStageURDartRun w n := by
        simpa [kmswStageURDartsFinset] using hUR.1
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hm
      refine ⟨.upperRight ⟨i, hi⟩, ?_⟩
      simp only [InfiniteBoundaryDartIndex.dart_eq,
        kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide]
      exact hget
    · have hm : d ∈ kmswStageLRDartRun w n := by
        simpa [kmswStageLRDartsFinset] using hLR.1
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hm
      refine ⟨.lowerRight ⟨i, hi⟩, ?_⟩
      simp only [InfiniteBoundaryDartIndex.dart_eq,
        kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide]
      exact hget
    · have hm : d ∈ kmswStageLLDartRun w n := by
        simpa [kmswStageLLDartsFinset] using hLL.1
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hm
      refine ⟨.lowerLeft ⟨i, hi⟩, ?_⟩
      simp only [InfiniteBoundaryDartIndex.dart_eq,
        kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide]
      exact hget
  · rintro ⟨i, hi⟩
    have hEq : U' = U := hunique U' hU'
    subst U'
    have hout : (kmswStageDirectedMap w n).IsOuter d := by
      rw [← hi]
      cases i with
      | upperLeft j =>
          simp only [InfiniteBoundaryDartIndex.dart_eq,
            kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide,
            Function.Embedding.coeFn_mk]
          exact (kmsw_stage_outer_face_exact w n _).2 (hmemUL j)
      | upperRight j =>
          simp only [InfiniteBoundaryDartIndex.dart_eq,
            kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide,
            Function.Embedding.coeFn_mk]
          exact (kmsw_stage_outer_face_exact w n _).2 (hmemUR j)
      | lowerRight j =>
          simp only [InfiniteBoundaryDartIndex.dart_eq,
            kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide,
            Function.Embedding.coeFn_mk]
          exact (kmsw_stage_outer_face_exact w n _).2 (hmemLR j)
      | lowerLeft j =>
          simp only [InfiniteBoundaryDartIndex.dart_eq,
            kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide,
            Function.Embedding.coeFn_mk]
          exact (kmsw_stage_outer_face_exact w n _).2 (hmemLL j)
    exact (hborder d).2 hout

/-- Helper toward Definition 3.2: the finite KMSW package with its stage
dart-coverage premise discharged by the exact outer-word partition. The
remaining package premises retain their exact Presentation11 binders. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses5
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (hU : P.IsUnbounded U)
      (hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    (∀ U : P.Face, P.IsUnbounded U →
      IsGeometricExternalFaceSucc P U
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      ULOkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      UROkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LROkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LLOkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M
        (kmswStageFiniteBoundaryPresentation w n M J).upperLeft) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M
        (kmswStageFiniteBoundaryPresentation w n M J).lowerRight) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge)),
      ∀ (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      FiniteBoundaryPositionOrder4 (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
      RequiredFiniteBoundaryJoinEndpointLabels7
        (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
      (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (Fin (kmswStage w n).nextEdge × Bool))
      (G : PLDrawing (Fin (kmswStage w n).nextEdge × Bool)
        (Fin (kmswStage w n).nextVertex) (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial M)) (U : G.Face)
      (S : Fin (kmswStage w n).nextEdge × Bool → Fin (kmswStage w n).nextEdge × Bool),
      kmsw_stage_map_realization32 w n P M ∧
      B = kmswStageFiniteBoundaryPresentationWithJunctions w n M J ∧
      G.image = P.image ∧ IsBoundEdges32 M B G U S := by
  obtain ⟨P, U, hU, hunique, hborder⟩ :=
    DirectedDistances.PaperProofs.Section5.kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter
      w n
  refine ⟨P, U, hU, hborder, ?_⟩
  intro hgeom hboundary hUL hUR hLR hLL hsimpleUL hsimpleLR hposition hjoin
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  have hreal : kmsw_stage_map_realization32 w n P M :=
    kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
  have hlabelsUL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperLeft :=
    kmswStageFiniteBoundaryPresentation10_upperLeft_endpointLabels w n P U hU hborder
  have hlabelsUR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperRight :=
    kmswStageFiniteBoundaryPresentation10_upperRight_endpointLabels w n P U hU hborder
  have hlabelsLR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerRight :=
    kmswStageFiniteBoundaryPresentation10_lowerRight_endpointLabels w n P U hU hborder
  have hlabelsLL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft :=
    kmswStageFiniteBoundaryPresentation10_lowerLeft_endpointLabels w n P U hU hborder
  have htransport :
      ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft :=
    ⟨M, J, hreal, hlabelsUL, hlabelsUR, hlabelsLR, hlabelsLL⟩
  exact exists_kmswStage_bound_edges32_of_open_clauses3 w n P htransport
    (fun M J U' hreal' _hU' d =>
      kmswStageFiniteBoundaryPresentation12_dart_coverage
        w n P U hunique hborder M J U' _hU' d)
    hgeom hboundary hUL hUR hLR hLL hsimpleUL hsimpleLR hposition hjoin

/-! ## Retained premise status

| Presentation11 premise | Status in this file |
| --- | --- |
| `h_stage_dart_coverage` | DISCHARGED by `kmswStageFiniteBoundaryPresentation12_dart_coverage`; uses the exact stage outer-word partition and `hborder`. |
| `h_stage_geometric_successor` | OPEN; `kmswStageFiniteBoundaryPresentation4_geometric_run_successors` proves within-run successors, but not the four cyclic run transitions. |
| `h_stage_boundary_order` | OPEN; `kmswStage_finite_outer_dart_run_partition` proves the outer dart set, but not external-frontier edge equality and multiplicity for arbitrary realized `M`. |
| `h_stage_upperLeft_orientation` | OPEN; the stage UL bridge and `hreal` give present-edge orientation, but not `LeftOf` the external face in `Drawing M`. |
| `h_stage_upperRight_missing_run` | OPEN; `kmswStage_finite_missing_run_darts` proves pointwise missingness, while `UROkInf` also requires all consecutive endpoint joins. |
| `h_stage_lowerRight_orientation` | OPEN; the stage LR bridge and `hreal` give present-edge orientation, but not `RightOf` the external face in `Drawing M`. |
| `h_stage_lowerLeft_missing_run` | OPEN; `kmswStage_finite_missing_run_darts` proves pointwise missingness, while `LLOkInf` also requires all consecutive endpoint joins. |
| `h_stage_upperLeft_simple` | OPEN; `kmswStage_finite_run_nodup` and `kmswStageFiniteBoundaryPresentation_dart_injective` give dart injectivity, not vertex-occurrence injectivity. |
| `h_stage_lowerRight_simple` | OPEN; `kmswStage_finite_run_nodup` and `kmswStageFiniteBoundaryPresentation_dart_injective` give dart injectivity, not vertex-occurrence injectivity. |
| `h_stage_finite_position_order` | OPEN; `kmswStage_finite_boundary_positionOrder3` gives `BoundaryPositionOrder3`, while v4 also needs the geometric cyclic successor and side cut. |

The exact open conclusions below all have common binders `(w : ℕ → Fin 3)`
`(n : ℕ)` and the selected `(P : StageDrawing w n)`, `(U : P.Face)`,
`(hU : P.IsUnbounded U)`, and `hborder : ∀ d, P.dartBorders d U ↔
(kmswStageDirectedMap w n).IsOuter d`. For arbitrary
`(M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
(Fin (kmswStage w n).nextEdge))` and
`(J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))`, put
`Q := kmswStageFiniteBoundaryPresentation w n M J` and
`S := fun d => (stageRot w n).symm (d.1, !d.2)`. Their exact residual
binders are:

* `∀ U' : P.Face, P.IsUnbounded U' → IsGeometricExternalFaceSucc P U' S`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → IsBoundaryOrderOfInf M Q`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → ULOkInf Q`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → UROkInf Q`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → LROkInf Q`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → LLOkInf Q`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M Q.upperLeft`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M Q.lowerRight`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → FiniteBoundaryPositionOrder4 Q S`.
* `∀ M J, kmsw_stage_map_realization32 w n P M → BoundarySideEndpointLabels M Q.upperLeft →
  BoundarySideEndpointLabels M Q.upperRight → BoundarySideEndpointLabels M Q.lowerRight →
  BoundarySideEndpointLabels M Q.lowerLeft → RequiredFiniteBoundaryJoinEndpointLabels7 Q S`.

Three routes were inspected for each open group. For geometric succession,
the four within-run lemmas, the complete stage outer-word permutation, and
the exact outer-dart partition, the realization's arc-range equations, and
the external-face criterion do not provide the required correspondence
between external faces of `P` and `Drawing M`. For orientations, exact dart
tags, the realization's `forward` clause, and the stage face-successor
geometry still leave the `LeftOf`/`RightOf` facts in `Drawing M`. For the
missing runs, `kmswStage_finite_missing_run_darts`, the boundary-chain
invariant transferred by endpoint identities, and the rotation successor
each address missingness or adjacency separately, not the complete side
predicate on the arbitrary realization binder. For simplicity, run nodup,
dart-index injectivity, and endpoint-label identities do not establish
injectivity of all side vertex occurrences. For position order, the proved
`BoundaryPositionOrder3`, the four-run word offsets, and the rotation
successor leave the required simultaneous cyclic cut and within-side next
equivalence. For the cyclic join, (1) Presentation4's within-run
`stageRot` and transferred endpoint identities does not identify labels on
skipped empty sides; (3) the split cyclic word `UL ++ UR ++ LR ++ LL` still
requires classifying equal dart occurrences across the four runs. No premise
was added to the target. -/

end DirectedDistances.PaperProofs.Section3
