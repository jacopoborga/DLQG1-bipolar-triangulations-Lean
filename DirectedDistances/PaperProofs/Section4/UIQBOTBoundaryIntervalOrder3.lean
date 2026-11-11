/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTBoundaryIntervalOrder2
public import DirectedDistances.PlanarMap.UIQBOTQuotientDartDrawingTransport

/-! This continuation uses the representative-adjusted quotient dart equivalence.
The UIQBOT presentation has nonempty UL and LR sides and empty UR and LL
sides. The transported KMSW successor has the root junction LR(0) → UL(0)
on the quotient-geometric-edge dart carrier. Identifying this successor with
the canonical presentation darts requires the directed-orientation field of
the map, which is opaque in the imported interface. For an LR-to-UL
presentation join, the v3 skipped-LL clause asks for the join vertex at both
ends of LL, while the constructor supplies neither label. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: nonempty sides of the canonical UIQBOT
infinite boundary. -/
theorem uiqbotCanonicalBoundaryPresentation_nonemptySides
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    Nonempty (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0).upperLeft.Index ∧
      Nonempty (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0).lowerRight.Index := by
  constructor
  · exact ⟨(uiqbotCanonicalUpperLeftIndexEquiv w hfin htrans hR hL0).symm 0⟩
  · exact ⟨(uiqbotCanonicalLowerRightIndexEquiv w hfin htrans hR hL0).symm 0⟩

/-- Helper toward Definition 3.2: both missing-side index types in the
canonical UIQBOT boundary are empty. -/
theorem uiqbotCanonicalBoundaryPresentation_emptySides
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    IsEmpty (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0).upperRight.Index ∧
      IsEmpty (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0).lowerLeft.Index := by
  rw [uiqbotCanonicalBoundaryPresentation_eq]
  change IsEmpty Empty ∧ IsEmpty Empty
  exact ⟨inferInstance, inferInstance⟩











































/-- Helper toward Definition 3.2: the generic four-side constructor advances
UL by one natural index. -/
theorem uiqbotDefinition32Presentation_upperLeftNext
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) (i : ℕ) :
    sideNext (uiqbotDefinition32Presentation w htrans hR hL0 M iota)
      (.upperLeft i) = some (.upperLeft (i + 1)) := by
  simp [sideNext, uiqbotDefinition32Presentation]

/-- Helper toward Definition 3.2: the generic four-side constructor traverses
LR in decreasing natural-index order. -/
theorem uiqbotDefinition32Presentation_lowerRightNext
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) (i : ℕ) :
    sideNext (uiqbotDefinition32Presentation w htrans hR hL0 M iota)
      (.lowerRight (i + 1)) = some (.lowerRight i) := by
  simp [sideNext, uiqbotDefinition32Presentation]

/-- Helper toward Definition 3.2: LR index zero is the finite end of the
reverse-traversed lower-right side. -/
theorem uiqbotDefinition32Presentation_lowerRightRootNext
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) :
    sideNext (uiqbotDefinition32Presentation w htrans hR hL0 M iota)
      (.lowerRight (0 : ℕ)) = none := by
  simp [sideNext, uiqbotDefinition32Presentation]

/-- Helper toward Definition 3.2: the constructor supplies no lower-left
endpoint labels. -/
theorem uiqbotDefinition32Presentation_lowerLeftLabels_absent
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) :
    let P := uiqbotDefinition32Presentation w htrans hR hL0 M iota
    P.lowerLeft.initialVertex? = none ∧ P.lowerLeft.terminalVertex? = none := by
  simp [uiqbotDefinition32Presentation]

/-- Helper toward Definition 3.2: conjugate the KMSW face successor to the
canonical quotient-geometric-edge dart carrier. -/
noncomputable def uiqbotCanonicalBoundaryDartExternalSucc
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool →
      (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool :=
  fun d =>
    (uiqbotTransportRotation
      (uiqbotKMSWQuotientDartEquiv (uiqbotPresentationDrawing w hfin)
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)))
      (kmswInfRot w hfin)).symm (d.1, !d.2)

/-- Helper toward Definition 3.2: this successor agrees with the transported
KMSW external-face successor on every quotient dart. -/
theorem uiqbotCanonicalBoundaryDartExternalSucc_transport
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) :
    uiqbotCanonicalBoundaryDartExternalSucc w hfin d =
      (uiqbotKMSWQuotientDartEquiv (uiqbotPresentationDrawing w hfin)
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).symm
        (kmswInfFaceSucc w hfin
          (uiqbotKMSWQuotientDartEquiv (uiqbotPresentationDrawing w hfin)
            (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)) d)) := by
  exact uiqbotTransportRotation_geometricSucc
    (uiqbotKMSWQuotientDartEquiv (uiqbotPresentationDrawing w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)))
    (kmswInfRot w hfin) (fun d => (d.1, !d.2)) (fun d => (d.1, !d.2))
    (uiqbotKMSWQuotientDartEquiv_flip (uiqbotPresentationDrawing w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)) ·) d

/-- Helper toward Definition 3.2: the canonical transported successor joins
the terminal LR root dart to the initial UL root dart. -/
theorem uiqbotCanonicalBoundaryDartExternalSucc_rootJunction
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL0 : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    uiqbotCanonicalBoundaryDartExternalSucc w hfin
        ((uiqbotKMSWQuotientDartEquiv (uiqbotPresentationDrawing w hfin)
          (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).symm
          (kmswRightBoundaryEdge w 0, true)) =
      (uiqbotKMSWQuotientDartEquiv (uiqbotPresentationDrawing w hfin)
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).symm
        (kmswLeftBoundaryEdge w 0, false) := by
  rw [uiqbotCanonicalBoundaryDartExternalSucc_transport]
  simp only [Equiv.apply_symm_apply]
  rw [kmswInfFaceSucc_junction w hfin (stageOuterWord_faceSucc w) hL0 htrans hR]





















































































end DirectedDistances.PaperProofs.Section4

end
