/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation18
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation19

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

private theorem kmswStageFiniteBoundaryPresentation22_terminal_actual
    {V E : Type*} {M : DirectedPlaneMapWithMissing V E}
    (B : InfiniteBoundarySide V E) (hB : BoundarySideEndpointLabels M B)
    (v : V) (hv : B.terminalVertex? = some v) (i : B.Index)
    (hnext : B.next i = none) :
    boundaryDartTerminal M (B.darts i) = v :=
  (hB.2.1 v hv).2 i hnext

private theorem kmswStageFiniteBoundaryPresentation22_initial_actual_of_first
    {V E : Type*} {M : DirectedPlaneMapWithMissing V E}
    (B : InfiniteBoundarySide V E) (hB : BoundarySideEndpointLabels M B)
    (v : V) (hv : B.initialVertex? = some v) (i : B.Index)
    (hfirst : ∀ j, B.next j ≠ some i) :
    boundaryDartInitial M (B.darts i) = v :=
  (hB.1 v hv).2 i hfirst

/-- Helper toward Definition 3.2: the two present sides are nonempty, so the
v7 join-label predicate reduces exactly to its v4 closing-junction clause. -/
theorem kmswStageFiniteBoundaryPresentation22_join_labels_iff_core
    (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    RequiredFiniteBoundaryJoinEndpointLabels7
        (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2)) ↔
      RequiredFiniteBoundaryJoinEndpointLabels4
        (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2)) := by
  have hpresent := kmswStageFiniteBoundaryPresentation13_present_sides_nonempty w n M J
  unfold RequiredFiniteBoundaryJoinEndpointLabels7
  constructor
  · intro h
    exact h.1 hpresent
  · intro h
    exact ⟨fun _ => h, fun hnot => (hnot hpresent).elim⟩

/-- Helper toward Definition 3.2: if UR is empty, its retained initial and
terminal labels agree by the realized geometric corner equality. -/
theorem kmswStageFiniteBoundaryPresentation22_upperRight_empty_labels
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hempty : (kmswStage w n).UR = []) :
    (kmswStageFiniteBoundaryPresentation w n M
      (kmswStageFiniteBoundaryPresentation5Junctions w n)).upperRight.initialVertex? =
    (kmswStageFiniteBoundaryPresentation w n M
      (kmswStageFiniteBoundaryPresentation5Junctions w n)).upperRight.terminalVertex? := by
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  let Q := kmswStageFiniteBoundaryPresentation w n M J
  have hlabels := kmswStageFiniteBoundaryPresentation5_junction_labels w n M
  have hcorner := kmswStageFiniteBoundaryPresentation18_upperRight_empty_corner_eq
    w n P M hreal hempty
  change Q.upperRight.initialVertex? = Q.upperRight.terminalVertex?
  calc
    Q.upperRight.initialVertex? = some J.upperLeftUpperRight := hlabels.2.2.1
    _ = some J.upperRightLowerRight := congrArg some hcorner
    _ = Q.upperRight.terminalVertex? := hlabels.2.2.2.1.symm

/-- Helper toward Definition 3.2: if LL is empty, its retained initial and
terminal labels agree by the realized geometric corner equality. -/
theorem kmswStageFiniteBoundaryPresentation22_lowerLeft_empty_labels
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hempty : (kmswStage w n).LL = []) :
    (kmswStageFiniteBoundaryPresentation w n M
      (kmswStageFiniteBoundaryPresentation5Junctions w n)).lowerLeft.initialVertex? =
    (kmswStageFiniteBoundaryPresentation w n M
      (kmswStageFiniteBoundaryPresentation5Junctions w n)).lowerLeft.terminalVertex? := by
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  let Q := kmswStageFiniteBoundaryPresentation w n M J
  have hlabels := kmswStageFiniteBoundaryPresentation5_junction_labels w n M
  have hcorner := kmswStageFiniteBoundaryPresentation18_lowerLeft_empty_corner_eq
    w n P M hreal hempty
  change Q.lowerLeft.initialVertex? = Q.lowerLeft.terminalVertex?
  calc
    Q.lowerLeft.initialVertex? = some J.lowerRightLowerLeft :=
      hlabels.2.2.2.2.2.2.1
    _ = some J.lowerLeftUpperLeft := congrArg some hcorner
    _ = Q.lowerLeft.terminalVertex? := hlabels.2.2.2.2.2.2.2.symm

/-- Helper toward Definition 3.2: when UR is empty, the terminal UL dart
joins the initial LR dart through the identified geometric corner. -/
theorem kmswStageFiniteBoundaryPresentation22_upperLeft_lowerRight_skip
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hempty : (kmswStage w n).UR = []) :
    boundaryDartTerminal M ((kmswStageULDartRun w n).getLast
      (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) =
    boundaryDartInitial M ((kmswStageLRDartRun w n).head
      (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) := by
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  have hcorner := kmswStageFiniteBoundaryPresentation18_upperRight_empty_corner_eq
    w n P M hreal hempty
  have hUL := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have hLR := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  calc
    boundaryDartTerminal M ((kmswStageULDartRun w n).getLast hUL) =
        stageVertex w n (edgeFlip _ ((kmswStageULDartRun w n).getLast hUL)) :=
      kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal _
    _ = J.upperLeftUpperRight :=
      (kmswStageFiniteBoundaryPresentation5_upperLeftUpperRight w n).symm
    _ = J.upperRightLowerRight := congrArg id hcorner
    _ = stageVertex w n ((kmswStageLRDartRun w n).head hLR) :=
      kmswStageFiniteBoundaryPresentation5_upperRightLowerRight w n
    _ = boundaryDartInitial M ((kmswStageLRDartRun w n).head hLR) :=
      (kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal _).symm

/-- Helper toward Definition 3.2: when LL is empty, the terminal LR dart
joins the initial UL dart through the identified geometric corner. -/
theorem kmswStageFiniteBoundaryPresentation22_lowerRight_upperLeft_skip
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hempty : (kmswStage w n).LL = []) :
    boundaryDartTerminal M ((kmswStageLRDartRun w n).getLast
      (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) =
    boundaryDartInitial M ((kmswStageULDartRun w n).head
      (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) := by
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  have hcorner := kmswStageFiniteBoundaryPresentation18_lowerLeft_empty_corner_eq
    w n P M hreal hempty
  have hUL := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have hLR := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  calc
    boundaryDartTerminal M ((kmswStageLRDartRun w n).getLast hLR) =
        stageVertex w n (edgeFlip _ ((kmswStageLRDartRun w n).getLast hLR)) :=
      kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal _
    _ = J.lowerRightLowerLeft :=
      (kmswStageFiniteBoundaryPresentation5_lowerRightLowerLeft w n).symm
    _ = J.lowerLeftUpperLeft := congrArg id hcorner
    _ = stageVertex w n ((kmswStageULDartRun w n).head hUL) :=
      kmswStageFiniteBoundaryPresentation5_lowerLeftUpperLeft w n
    _ = boundaryDartInitial M ((kmswStageULDartRun w n).head hUL) :=
      (kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal _).symm

/-- Helper toward Definition 3.2: endpoint validity and the realized geometric
successor identify the current terminal mark and the actual successor's
initial vertex. Its retained initial mark still requires proving that its
index is first on its side. -/
theorem kmswStageFiniteBoundaryPresentation22_join_endpoint_marks
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hUL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperLeft)
    (hUR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperRight)
    (hLR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerRight)
    (hLL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft) :
    ∀ i j : InfiniteBoundaryDartIndex
        (kmswStageFiniteBoundaryPresentation w n M J),
      (fun d => (stageRot w n).symm (d.1, !d.2))
          (InfiniteBoundaryDartIndex.dart _ i) = InfiniteBoundaryDartIndex.dart _ j →
      sideNext (kmswStageFiniteBoundaryPresentation w n M J) i = none →
      let v := boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart _ i)
      sideTerminalVertex? (kmswStageFiniteBoundaryPresentation w n M J)
          (sideTag (kmswStageFiniteBoundaryPresentation w n M J) i) = some v ∧
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart _ j) = v := by
  let Q := kmswStageFiniteBoundaryPresentation w n M J
  have hJ := kmswStage_finite_boundary_junction_labels w n M J
  have hterminal : ∀ i : InfiniteBoundaryDartIndex Q,
      sideNext Q i = none →
      sideTerminalVertex? Q (sideTag Q i) =
        some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i)) := by
    intro i hi
    cases i with
    | upperLeft ii =>
      have hnext : Q.upperLeft.next ii = none := by simpa [sideNext] using hi
      have hactual := kmswStageFiniteBoundaryPresentation22_terminal_actual
        Q.upperLeft hUL J.upperLeftUpperRight hJ.2.1 ii hnext
      calc
        sideTerminalVertex? Q (sideTag Q (.upperLeft ii)) =
            some J.upperLeftUpperRight := by
          simpa [sideTerminalVertex?, sideTag] using hJ.2.1
        _ = some (boundaryDartTerminal M
            (InfiniteBoundaryDartIndex.dart Q (.upperLeft ii))) := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using congrArg some hactual.symm
    | upperRight ii =>
      have hnext : Q.upperRight.next ii = none := by simpa [sideNext] using hi
      have hactual := kmswStageFiniteBoundaryPresentation22_terminal_actual
        Q.upperRight hUR J.upperRightLowerRight hJ.2.2.2.1 ii hnext
      calc
        sideTerminalVertex? Q (sideTag Q (.upperRight ii)) =
            some J.upperRightLowerRight := by
          simpa [sideTerminalVertex?, sideTag] using hJ.2.2.2.1
        _ = some (boundaryDartTerminal M
            (InfiniteBoundaryDartIndex.dart Q (.upperRight ii))) := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using congrArg some hactual.symm
    | lowerRight ii =>
      have hnext : Q.lowerRight.next ii = none := by simpa [sideNext] using hi
      have hactual := kmswStageFiniteBoundaryPresentation22_terminal_actual
        Q.lowerRight hLR J.lowerRightLowerLeft hJ.2.2.2.2.2.1 ii hnext
      calc
        sideTerminalVertex? Q (sideTag Q (.lowerRight ii)) =
            some J.lowerRightLowerLeft := by
          simpa [sideTerminalVertex?, sideTag] using hJ.2.2.2.2.2.1
        _ = some (boundaryDartTerminal M
            (InfiniteBoundaryDartIndex.dart Q (.lowerRight ii))) := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using congrArg some hactual.symm
    | lowerLeft ii =>
      have hnext : Q.lowerLeft.next ii = none := by simpa [sideNext] using hi
      have hactual := kmswStageFiniteBoundaryPresentation22_terminal_actual
        Q.lowerLeft hLL J.lowerLeftUpperLeft hJ.2.2.2.2.2.2.2 ii hnext
      calc
        sideTerminalVertex? Q (sideTag Q (.lowerLeft ii)) =
            some J.lowerLeftUpperLeft := by
          simpa [sideTerminalVertex?, sideTag] using hJ.2.2.2.2.2.2.2
        _ = some (boundaryDartTerminal M
            (InfiniteBoundaryDartIndex.dart Q (.lowerLeft ii))) := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using congrArg some hactual.symm
  intro i j hsucc hnext
  have hgeo := kmswStageFiniteBoundaryPresentation13_geometric_join
    w n P M hreal (InfiniteBoundaryDartIndex.dart Q i)
  have hgeo' : boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i) =
      boundaryDartInitial M
        ((fun d => (stageRot w n).symm (d.1, !d.2))
          (InfiniteBoundaryDartIndex.dart Q i)) := by
    simpa [edgeFlip] using hgeo
  change boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i) =
    boundaryDartInitial M
      ((fun d => (stageRot w n).symm (d.1, !d.2))
        (InfiniteBoundaryDartIndex.dart Q i)) at hgeo'
  rw [hsucc] at hgeo'
  change sideTerminalVertex? Q (sideTag Q i) =
      some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i)) ∧
    boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j) =
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i)
  exact ⟨hterminal i hnext, hgeo'.symm⟩

/-- Helper toward Definition 3.2: if the successor's index is first on its
side, endpoint validity turns the actual endpoint equality into both retained
side marks. -/
theorem kmswStageFiniteBoundaryPresentation22_join_marks_of_first
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hUL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperLeft)
    (hUR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperRight)
    (hLR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerRight)
    (hLL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft) :
    ∀ i j : InfiniteBoundaryDartIndex
        (kmswStageFiniteBoundaryPresentation w n M J),
      (fun d => (stageRot w n).symm (d.1, !d.2))
          (InfiniteBoundaryDartIndex.dart _ i) = InfiniteBoundaryDartIndex.dart _ j →
      sideNext (kmswStageFiniteBoundaryPresentation w n M J) i = none →
      (∀ k, sideNext (kmswStageFiniteBoundaryPresentation w n M J) k ≠ some j) →
      let v := boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart _ i)
      sideTerminalVertex? (kmswStageFiniteBoundaryPresentation w n M J)
          (sideTag (kmswStageFiniteBoundaryPresentation w n M J) i) = some v ∧
        sideInitialVertex? (kmswStageFiniteBoundaryPresentation w n M J)
          (sideTag (kmswStageFiniteBoundaryPresentation w n M J) j) = some v := by
  let Q := kmswStageFiniteBoundaryPresentation w n M J
  have hJ := kmswStage_finite_boundary_junction_labels w n M J
  have hinitial : ∀ j : InfiniteBoundaryDartIndex Q,
      (∀ k, sideNext Q k ≠ some j) →
      sideInitialVertex? Q (sideTag Q j) =
        some (boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j)) := by
    intro j hfirst
    cases j with
    | upperLeft jj =>
      have hsidefirst : ∀ k, Q.upperLeft.next k ≠ some jj := by
        intro k hk
        apply hfirst (.upperLeft k)
        simp [sideNext, hk]
      have hactual := kmswStageFiniteBoundaryPresentation22_initial_actual_of_first
        Q.upperLeft hUL J.lowerLeftUpperLeft hJ.1 jj hsidefirst
      calc
        sideInitialVertex? Q (sideTag Q (.upperLeft jj)) =
            some J.lowerLeftUpperLeft := by
          simpa [sideInitialVertex?, sideTag] using hJ.1
        _ = some (boundaryDartInitial M
            (InfiniteBoundaryDartIndex.dart Q (.upperLeft jj))) := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using congrArg some hactual.symm
    | upperRight jj =>
      have hsidefirst : ∀ k, Q.upperRight.next k ≠ some jj := by
        intro k hk
        apply hfirst (.upperRight k)
        simp [sideNext, hk]
      have hactual := kmswStageFiniteBoundaryPresentation22_initial_actual_of_first
        Q.upperRight hUR J.upperLeftUpperRight hJ.2.2.1 jj hsidefirst
      calc
        sideInitialVertex? Q (sideTag Q (.upperRight jj)) =
            some J.upperLeftUpperRight := by
          simpa [sideInitialVertex?, sideTag] using hJ.2.2.1
        _ = some (boundaryDartInitial M
            (InfiniteBoundaryDartIndex.dart Q (.upperRight jj))) := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using congrArg some hactual.symm
    | lowerRight jj =>
      have hsidefirst : ∀ k, Q.lowerRight.next k ≠ some jj := by
        intro k hk
        apply hfirst (.lowerRight k)
        simp [sideNext, hk]
      have hactual := kmswStageFiniteBoundaryPresentation22_initial_actual_of_first
        Q.lowerRight hLR J.upperRightLowerRight hJ.2.2.2.2.1 jj hsidefirst
      calc
        sideInitialVertex? Q (sideTag Q (.lowerRight jj)) =
            some J.upperRightLowerRight := by
          simpa [sideInitialVertex?, sideTag] using hJ.2.2.2.2.1
        _ = some (boundaryDartInitial M
            (InfiniteBoundaryDartIndex.dart Q (.lowerRight jj))) := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using congrArg some hactual.symm
    | lowerLeft jj =>
      have hsidefirst : ∀ k, Q.lowerLeft.next k ≠ some jj := by
        intro k hk
        apply hfirst (.lowerLeft k)
        simp [sideNext, hk]
      have hactual := kmswStageFiniteBoundaryPresentation22_initial_actual_of_first
        Q.lowerLeft hLL J.lowerRightLowerLeft hJ.2.2.2.2.2.2.1 jj hsidefirst
      calc
        sideInitialVertex? Q (sideTag Q (.lowerLeft jj)) =
            some J.lowerRightLowerLeft := by
          simpa [sideInitialVertex?, sideTag] using hJ.2.2.2.2.2.2.1
        _ = some (boundaryDartInitial M
            (InfiniteBoundaryDartIndex.dart Q (.lowerLeft jj))) := by
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using congrArg some hactual.symm
  intro i j hsucc hnext hfirst
  have hends := kmswStageFiniteBoundaryPresentation22_join_endpoint_marks
    w n P M J hreal hUL hUR hLR hLL i j hsucc hnext
  change sideTerminalVertex? Q (sideTag Q i) =
      some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i)) ∧
    sideInitialVertex? Q (sideTag Q j) =
      some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i))
  exact ⟨hends.1, by
    calc
      sideInitialVertex? Q (sideTag Q j) =
          some (boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q j)) :=
        hinitial j hfirst
      _ = some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q i)) :=
        congrArg some hends.2⟩

/-- Helper toward Definition 3.2: when UR is nonempty, the terminal UL dart
joins the initial UR dart in the realized map. -/
theorem kmswStageFiniteBoundaryPresentation22_upperLeft_upperRight_join
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hUR : kmswStageURDartRun w n ≠ []) :
    boundaryDartTerminal M ((kmswStageULDartRun w n).getLast
      (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) =
    boundaryDartInitial M ((kmswStageURDartRun w n).head hUR) := by
  have hUL := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have htail : kmswStageURDartRun w n ++ kmswStageLRDartRun w n ++
      kmswStageLLDartRun w n ≠ [] := by
    exact List.append_ne_nil_of_left_ne_nil
      (List.append_ne_nil_of_left_ne_nil hUR (kmswStageLRDartRun w n))
      (kmswStageLLDartRun w n)
  have hh := (kmswStageFiniteBoundaryPresentation14_four_run_handoffs w n).1
    hUL htail
  have hh' : (stageRot w n).symm
      (edgeFlip _ ((kmswStageULDartRun w n).getLast hUL)) =
      (kmswStageURDartRun w n).head hUR := by
    simpa only [List.append_assoc, List.head_append_of_ne_nil hUR] using hh
  have hj := kmswStageFiniteBoundaryPresentation13_geometric_join
    w n P M hreal ((kmswStageULDartRun w n).getLast hUL)
  have hj' : boundaryDartTerminal M ((kmswStageULDartRun w n).getLast hUL) =
      boundaryDartInitial M ((stageRot w n).symm
        (edgeFlip _ ((kmswStageULDartRun w n).getLast hUL))) := by
    simpa [edgeFlip] using hj
  rw [hh'] at hj'
  exact hj'

/-- Helper toward Definition 3.2: the terminal UR dart joins the initial LR
dart in the realized map. -/
theorem kmswStageFiniteBoundaryPresentation22_upperRight_lowerRight_join
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hUR : kmswStageURDartRun w n ≠ []) :
    boundaryDartTerminal M ((kmswStageURDartRun w n).getLast hUR) =
    boundaryDartInitial M ((kmswStageLRDartRun w n).head
      (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) := by
  have hLR := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  have htail : kmswStageLRDartRun w n ++ kmswStageLLDartRun w n ++
      kmswStageULDartRun w n ≠ [] := by
    exact List.append_ne_nil_of_left_ne_nil
      (List.append_ne_nil_of_left_ne_nil hLR (kmswStageLLDartRun w n))
      (kmswStageULDartRun w n)
  have hh := (kmswStageFiniteBoundaryPresentation14_four_run_handoffs w n).2.1
    hUR htail
  have hh' : (stageRot w n).symm
      (edgeFlip _ ((kmswStageURDartRun w n).getLast hUR)) =
      (kmswStageLRDartRun w n).head hLR := by
    simpa only [List.append_assoc, List.head_append_of_ne_nil hLR] using hh
  have hj := kmswStageFiniteBoundaryPresentation13_geometric_join
    w n P M hreal ((kmswStageURDartRun w n).getLast hUR)
  have hj' : boundaryDartTerminal M ((kmswStageURDartRun w n).getLast hUR) =
      boundaryDartInitial M ((stageRot w n).symm
        (edgeFlip _ ((kmswStageURDartRun w n).getLast hUR))) := by
    simpa [edgeFlip] using hj
  rw [hh'] at hj'
  exact hj'

/-- Helper toward Definition 3.2: when LL is nonempty, the terminal LR dart
joins the initial LL dart in the realized map. -/
theorem kmswStageFiniteBoundaryPresentation22_lowerRight_lowerLeft_join
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hLL : kmswStageLLDartRun w n ≠ []) :
    boundaryDartTerminal M ((kmswStageLRDartRun w n).getLast
      (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) =
    boundaryDartInitial M ((kmswStageLLDartRun w n).head hLL) := by
  have hLR := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  have htail : kmswStageLLDartRun w n ++ kmswStageULDartRun w n ++
      kmswStageURDartRun w n ≠ [] := by
    exact List.append_ne_nil_of_left_ne_nil
      (List.append_ne_nil_of_left_ne_nil hLL (kmswStageULDartRun w n))
      (kmswStageURDartRun w n)
  have hh := (kmswStageFiniteBoundaryPresentation14_four_run_handoffs w n).2.2.1
    hLR htail
  have hh' : (stageRot w n).symm
      (edgeFlip _ ((kmswStageLRDartRun w n).getLast hLR)) =
      (kmswStageLLDartRun w n).head hLL := by
    simpa only [List.append_assoc, List.head_append_of_ne_nil hLL] using hh
  have hj := kmswStageFiniteBoundaryPresentation13_geometric_join
    w n P M hreal ((kmswStageLRDartRun w n).getLast hLR)
  have hj' : boundaryDartTerminal M ((kmswStageLRDartRun w n).getLast hLR) =
      boundaryDartInitial M ((stageRot w n).symm
        (edgeFlip _ ((kmswStageLRDartRun w n).getLast hLR))) := by
    simpa [edgeFlip] using hj
  rw [hh'] at hj'
  exact hj'

/-- Helper toward Definition 3.2: the terminal LL dart joins the initial UL
dart in the realized map. -/
theorem kmswStageFiniteBoundaryPresentation22_lowerLeft_upperLeft_join
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hLL : kmswStageLLDartRun w n ≠ []) :
    boundaryDartTerminal M ((kmswStageLLDartRun w n).getLast hLL) =
    boundaryDartInitial M ((kmswStageULDartRun w n).head
      (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) := by
  have hUL := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have htail : kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
      kmswStageLRDartRun w n ≠ [] := by
    exact List.append_ne_nil_of_left_ne_nil
      (List.append_ne_nil_of_left_ne_nil hUL (kmswStageURDartRun w n))
      (kmswStageLRDartRun w n)
  have hh := (kmswStageFiniteBoundaryPresentation14_four_run_handoffs w n).2.2.2
    hLL htail
  have hh' : (stageRot w n).symm
      (edgeFlip _ ((kmswStageLLDartRun w n).getLast hLL)) =
      (kmswStageULDartRun w n).head hUL := by
    simpa only [List.append_assoc, List.head_append_of_ne_nil hUL] using hh
  have hj := kmswStageFiniteBoundaryPresentation13_geometric_join
    w n P M hreal ((kmswStageLLDartRun w n).getLast hLL)
  have hj' : boundaryDartTerminal M ((kmswStageLLDartRun w n).getLast hLL) =
      boundaryDartInitial M ((stageRot w n).symm
        (edgeFlip _ ((kmswStageLLDartRun w n).getLast hLL))) := by
    simpa [edgeFlip] using hj
  rw [hh'] at hj'
  exact hj'































































































end DirectedDistances.PaperProofs.Section3

end
