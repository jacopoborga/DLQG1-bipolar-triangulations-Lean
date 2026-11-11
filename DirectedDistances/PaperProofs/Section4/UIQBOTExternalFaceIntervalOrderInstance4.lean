/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceIntervalOrderInstance3
import all DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry2

/-! # Labeled UIQBOT external-face interval-order instance, continued

Helpers toward Definition 3.2. This file records the concrete external-face
construction and the successor clause that follows from its coverage. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter

/-- Helper toward Definition 3.2: the transported KMSW drawing has the
labeled canonical external-dart coverage and the successor induced by its
rotation. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_constructedExternalFace
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
    ∃ (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)
        ℕ (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : G.Face),
      G.IsUnbounded U ∧
        (∀ d, G.dartBorders d U ↔
          ∃ i : InfiniteBoundaryDartIndex P,
            InfiniteBoundaryDartIndex.dart P i = d) ∧
        IsGeometricExternalFaceSucc G U
          (fun d => e (kmswInfFaceSucc w hfin (e.symm d))) ∧
        IsGeometricExternalFaceSucc G U (fun d => rot.symm (d.1, !d.2)) := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  obtain ⟨G, U, hUnbounded, hBorder, hSucc⟩ :=
    uiqbotCanonicalQuotientDrawing_externalFace w hfin htrans hR hL0
  refine ⟨G, U, hUnbounded, ?_, hSucc, ?_⟩
  · intro d
    rw [hBorder d]
    simpa only [uiqbotCanonicalBoundaryDartEquiv, Equiv.symm_symm] using
      uiqbotCanonicalBoundaryPresentationLabeledX_externalDartCoverage
        w hfin htrans hR hL0 d
  · refine ⟨hUnbounded, ?_⟩
    intro d hd
    obtain ⟨_, hSucc⟩ := hSucc
    obtain ⟨hrot, hnext⟩ := hSucc d hd
    refine ⟨rfl, ?_⟩
    change G.dartBorders (rot.symm (d.1, !d.2)) U
    rw [← hrot]
    exact hnext

/-- Helper toward Definition 3.2: every labeled boundary dart has a successor
among the labeled boundary darts on the constructed external face. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_constructedSuccessorExists
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
    ∀ i : InfiniteBoundaryDartIndex P,
      ∃ j : InfiniteBoundaryDartIndex P,
        rot.symm ((InfiniteBoundaryDartIndex.dart P i).1,
            !(InfiniteBoundaryDartIndex.dart P i).2) =
          InfiniteBoundaryDartIndex.dart P j := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  obtain ⟨G, U, _, hBorder, _, hSucc⟩ :=
    uiqbotCanonicalBoundaryPresentationLabeledX_constructedExternalFace
      w hfin htrans hR hL0
  intro i
  let d := InfiniteBoundaryDartIndex.dart P i
  have hd : G.dartBorders d U := (hBorder d).2 ⟨i, rfl⟩
  obtain ⟨hrot, hnext⟩ := hSucc.2 d hd
  obtain ⟨j, hj⟩ := (hBorder (rot.symm (d.1, !d.2))).1 (hrot ▸ hnext)
  exact ⟨j, hj.symm⟩

/-- Helper toward Definition 3.2: the constructed rotation sends each upper-left
boundary dart to the next upper-left dart. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_constructedUpperLeftStep
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
    ∀ i : ℕ,
    rot.symm ((P.upperLeft.darts i).1, !(P.upperLeft.darts i).2) =
        P.upperLeft.darts (i + 1) := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let D := uiqbotPresentationDrawing w hfin
  let iota := kmswGeometricEdgeEquiv w hfin D
  let f := uiqbotKMSWQuotientDartEquiv D iota
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  obtain ⟨G, U, _, hBorder, hface⟩ :=
    uiqbotCanonicalBoundaryPresentationLabeledX_constructedExternalFace
      w hfin htrans hR hL0
  rcases uiqbotKMSWPresentation_externalBoundarySteps w hfin htrans hR hL0 with
    ⟨_, _, _, hsteps⟩
  have hUL (n : ℕ) : f (P.upperLeft.darts n) =
      (kmswLeftBoundaryEdge w n, false) := by
    change f (iota (kmswLeftBoundaryEdge w n),
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).forward
        ⟨iota (kmswLeftBoundaryEdge w n), by simp [uiqbotMapWithNoMissing]⟩) = _
    exact uiqbotKMSWQuotientDartEquiv_directed D iota
      (kmswLeftBoundaryEdge w n)
  have heq (n : ℕ) : e.symm (P.upperLeft.darts n) =
      (kmswLeftBoundaryEdge w n, false) := by
    change f (P.upperLeft.darts n) = _
    exact hUL n
  have hUL' (n : ℕ) : e (kmswLeftBoundaryEdge w n, false) =
      P.upperLeft.darts n := by
    calc
      e (kmswLeftBoundaryEdge w n, false) =
          e (e.symm (P.upperLeft.darts n)) := congrArg e (heq n).symm
      _ = P.upperLeft.darts n := e.apply_symm_apply _
  intro i
  have hborder : G.dartBorders (P.upperLeft.darts i) U := by
    exact (hBorder (P.upperLeft.darts i)).2 ⟨.upperLeft i, by
      simp only [P, InfiniteBoundaryDartIndex.dart_eq]⟩
  obtain ⟨hrot, _⟩ := hface.1.2 (P.upperLeft.darts i) hborder
  calc
    rot.symm ((P.upperLeft.darts i).1, !(P.upperLeft.darts i).2) =
        e (kmswInfFaceSucc w hfin (e.symm (P.upperLeft.darts i))) := hrot.symm
    _ = e (kmswLeftBoundaryEdge w (i + 1), false) := by
      rw [heq i, (hsteps.1 i).2.1]
    _ = P.upperLeft.darts (i + 1) := hUL' (i + 1)

/-- Helper toward Definition 3.2: the constructed rotation sends each lower-right
dart after index zero to the preceding lower-right dart. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_constructedLowerRightStep
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
    ∀ i : ℕ,
      rot.symm ((P.lowerRight.darts (i + 1)).1,
          !(P.lowerRight.darts (i + 1)).2) =
        P.lowerRight.darts i := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let D := uiqbotPresentationDrawing w hfin
  let iota := kmswGeometricEdgeEquiv w hfin D
  let f := uiqbotKMSWQuotientDartEquiv D iota
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  obtain ⟨G, U, _, hBorder, hfaces⟩ :=
    uiqbotCanonicalBoundaryPresentationLabeledX_constructedExternalFace
      w hfin htrans hR hL0
  rcases uiqbotKMSWPresentation_externalBoundarySteps w hfin htrans hR hL0 with
    ⟨_, _, _, hsteps⟩
  have hLR (n : ℕ) : f (P.lowerRight.darts n) =
      (kmswRightBoundaryEdge w n, true) := by
    change f (iota (kmswRightBoundaryEdge w n),
      !(uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).forward
        ⟨iota (kmswRightBoundaryEdge w n), by simp [uiqbotMapWithNoMissing]⟩) = _
    simpa [uiqbotMapWithNoMissing, uiqbotPresentationDirectedMapX] using
      uiqbotKMSWQuotientDartEquiv_reverseDirected D iota
        (kmswRightBoundaryEdge w n)
  have heq (n : ℕ) : e.symm (P.lowerRight.darts n) =
      (kmswRightBoundaryEdge w n, true) := by
    change f (P.lowerRight.darts n) = _
    exact hLR n
  have hLR' (n : ℕ) : e (kmswRightBoundaryEdge w n, true) =
      P.lowerRight.darts n := by
    calc
      e (kmswRightBoundaryEdge w n, true) =
          e (e.symm (P.lowerRight.darts n)) := congrArg e (heq n).symm
      _ = P.lowerRight.darts n := e.apply_symm_apply _
  intro i
  have hborder : G.dartBorders (P.lowerRight.darts (i + 1)) U := by
    exact (hBorder (P.lowerRight.darts (i + 1))).2 ⟨.lowerRight (i + 1), by
      simp only [P, InfiniteBoundaryDartIndex.dart_eq]⟩
  have hcode : e.symm (P.lowerRight.darts (i + 1)) =
      (kmswRightBoundaryEdge w (i + 1), true) := by
    exact heq (i + 1)
  obtain ⟨hrot, _⟩ := hfaces.1.2 (P.lowerRight.darts (i + 1)) hborder
  calc
    rot.symm ((P.lowerRight.darts (i + 1)).1,
        !(P.lowerRight.darts (i + 1)).2) =
        e (kmswInfFaceSucc w hfin (e.symm (P.lowerRight.darts (i + 1)))) :=
      hrot.symm
    _ = e (kmswRightBoundaryEdge w i, true) := by
      rw [hcode, (hsteps.2.1 i).2.1]
    _ = P.lowerRight.darts i := hLR' i

/-- Helper toward Definition 3.2: every within-side successor of the labeled
presentation agrees with the constructed geometric rotation. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_constructedWithinSideSuccessor
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
    ∀ i j : InfiniteBoundaryDartIndex P, sideNext P i = some j →
      rot.symm ((InfiniteBoundaryDartIndex.dart P i).1,
          !(InfiniteBoundaryDartIndex.dart P i).2) =
        InfiniteBoundaryDartIndex.dart P j := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  intro i j hnext
  cases i with
  | upperLeft i =>
      cases j with
      | upperLeft j =>
          change ℕ at i
          change ℕ at j
          have hni : P.upperLeft.next i = some (i + 1) := rfl
          have hside : sideNext P (.upperLeft i) =
              some (.upperLeft (i + 1)) := by simp [sideNext, hni, Option.map]
          rw [hside] at hnext
          have hj : j = i + 1 := by
            injection hnext with hidx
            injection hidx with hj
            exact hj.symm
          subst j
          simpa only [InfiniteBoundaryDartIndex.dart_eq] using
            uiqbotCanonicalBoundaryPresentationLabeledX_constructedUpperLeftStep
              w hfin htrans hR hL0 i
      | upperRight j => cases j
      | lowerRight j => simp [sideNext] at hnext
      | lowerLeft j => cases j
  | upperRight i => cases i
  | lowerRight i =>
      change ℕ at i
      cases i with
      | zero =>
          simp [sideNext, uiqbotCanonicalBoundaryPresentationLabeledX,
            uiqbotCanonicalBoundaryPresentationX,
            uiqbotDefinition32Presentation] at hnext
      | succ i =>
          change ℕ at i
          cases j with
          | upperLeft j => simp [sideNext] at hnext
          | upperRight j => cases j
          | lowerRight j =>
              change ℕ at j
              have hni : P.lowerRight.next (i + 1) = some i := rfl
              have hside : sideNext P (.lowerRight (i + 1)) =
              some (.lowerRight i) := by simp [sideNext, hni, Option.map]
              rw [hside] at hnext
              have hj : j = i := by
                injection hnext with hidx
                injection hidx with hj
                exact hj.symm
              subst j
              simpa only [InfiniteBoundaryDartIndex.dart_eq] using
                uiqbotCanonicalBoundaryPresentationLabeledX_constructedLowerRightStep
                  w hfin htrans hR hL0 i
          | lowerLeft j => cases j
  | lowerLeft i => cases i




































































end DirectedDistances.PaperProofs.Section4

end

