/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceIntervalOrderInstance4

/-! # Labeled UIQBOT external-face interval-order instance, continued

Helpers toward Definition 3.2. This file transports the KMSW boundary-step
equations to endpoint joins of the labeled canonical presentation. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter

/-- Helper toward Definition 3.2: a geometric rotation successor begins at the
terminal vertex of its incoming dart. -/
theorem boundaryDartTerminal_eq_of_PLDrawing_successor
    {V : Type*} {E : Type*} (M : DirectedPlaneMapWithMissing V E)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (d e : E × Bool)
    (hsucc : rot.symm (d.1, !d.2) = e) :
    boundaryDartTerminal M d = boundaryDartInitial M e := by
  have hvertex := G.vert_rotation (rot.symm (d.1, !d.2))
  rw [Equiv.apply_symm_apply] at hvertex
  calc
    boundaryDartTerminal M d = boundaryDartInitial M (d.1, !d.2) := by
      rw [boundaryDartTerminal_eq, boundaryDartInitial_eq]
      cases d.2 <;> rfl
    _ = boundaryDartInitial M (rot.symm (d.1, !d.2)) := hvertex
    _ = boundaryDartInitial M e := congrArg (boundaryDartInitial M) hsucc

/-- Helper toward Definition 3.2: every supplied within-side step of the
labeled canonical presentation joins the incoming dart's terminal vertex to
the outgoing dart's initial vertex. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_constructedWithinSideEndpointJoin
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    ∀ i j : InfiniteBoundaryDartIndex P, sideNext P i = some j →
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j) := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  obtain ⟨G, _U, _hUnbounded, _hBorder, _hKMSWSucc, _hRotationSucc⟩ :=
    uiqbotCanonicalBoundaryPresentationLabeledX_constructedExternalFace
      w hfin htrans hR hL0
  intro i j hnext
  have hrotation :=
    uiqbotCanonicalBoundaryPresentationLabeledX_constructedWithinSideSuccessor
      w hfin htrans hR hL0 i j hnext
  exact boundaryDartTerminal_eq_of_PLDrawing_successor _ G
    (InfiniteBoundaryDartIndex.dart P i)
    (InfiniteBoundaryDartIndex.dart P j) hrotation

/-- Helper toward Definition 3.2: the full indexed-dart map of the canonical
labeled presentation is injective, using its side embeddings and UL/LR
disjointness. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_dartInjective
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    Function.Injective (InfiniteBoundaryDartIndex.dart P) := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  intro i j hij
  cases i with
  | upperLeft i =>
      cases j with
      | upperLeft j =>
          apply congrArg InfiniteBoundaryDartIndex.upperLeft
          exact P.upperLeft.darts.injective (by
            simpa only [InfiniteBoundaryDartIndex.dart_eq] using hij)
      | upperRight j => cases j
      | lowerRight j =>
          exact False.elim
            ((uiqbotCanonicalBoundaryPresentationLabeledX_upperLeft_ne_lowerRight_dart
              w hfin htrans hR hL0 i j) (by
                simpa only [InfiniteBoundaryDartIndex.dart_eq] using hij))
      | lowerLeft j => cases j
  | upperRight i => cases i
  | lowerRight i =>
      cases j with
      | upperLeft j =>
          exact False.elim
            ((uiqbotCanonicalBoundaryPresentationLabeledX_upperLeft_ne_lowerRight_dart
              w hfin htrans hR hL0 j i).symm (by
                simpa only [InfiniteBoundaryDartIndex.dart_eq] using hij))
      | upperRight j => cases j
      | lowerRight j =>
          apply congrArg InfiniteBoundaryDartIndex.lowerRight
          exact P.lowerRight.darts.injective (by
            simpa only [InfiniteBoundaryDartIndex.dart_eq] using hij)
      | lowerLeft j => cases j
  | lowerLeft i => cases i






































































end DirectedDistances.PaperProofs.Section4

end
