/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation2
public import DirectedDistances.PaperProofs.SourceResults.UIQBOTDefinitionV2
public import DirectedDistances.PlanarMap.GeneralPlaneMapExternalBoundary
public import DirectedDistances.PlanarMap.GeneralPlaneMapFiniteExternalFace
public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceMultiplicity
public import DirectedDistances.KMSW.KMSWConstructedGeometricEdgeEquiv
public import DirectedDistances.PaperProofs.Section4.UIQBOTBoundaryIntervalOrder6

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

/-- Helper toward Definition 3.2: the canonical directed-map structure on
the KMSW realization drawing, with its body exposed for endpoint proofs. -/
@[expose] noncomputable def uiqbotPresentationDirectedMapX (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    DirectedPlaneMap ℕ (uiqbotPresentationDrawing w hfin).GeometricEdge where
  toPlaneGraphDrawing := (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing
  forward := fun q => !q.out.2

/-- Helper toward Definition 3.2: the canonical four-side data on the KMSW
directed realization, with the constructor body exposed. -/
@[expose] noncomputable def uiqbotCanonicalBoundaryPresentationX
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :=
  uiqbotDefinition32Presentation w htrans hR hL0
    (uiqbotPresentationDirectedMapX w hfin)
    (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))

/-- Helper toward Definition 3.2: the exposed canonical upper-left index is
the constructor's natural-number index. -/
@[expose] noncomputable def uiqbotCanonicalUpperLeftIndexEquivX
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0).upperLeft.Index ≃ ℕ := by
  change ℕ ≃ ℕ
  exact Equiv.refl ℕ

/-- Helper toward Definition 3.2: the exposed canonical lower-right index is
the constructor's natural-number index. -/
@[expose] noncomputable def uiqbotCanonicalLowerRightIndexEquivX
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0).lowerRight.Index ≃ ℕ := by
  change ℕ ≃ ℕ
  exact Equiv.refl ℕ

/-- Helper toward Definition 3.2: label the degenerate lower-left side of the
exposed canonical UIQBOT presentation at the terminal vertex of LR(0). -/
@[expose] noncomputable def uiqbotCanonicalBoundaryPresentationLabeledX
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    InfiniteBoundaryPresentation M := by
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let v := boundaryDartTerminal M (P.lowerRight.darts
    ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0))
  exact { P with lowerLeft := { P.lowerLeft with
    initialVertex? := some v
    terminalVertex? := some v } }

/-- Helper toward Definition 3.2: the exposed labeled presentation changes
only the two lower-left endpoint labels. -/
theorem uiqbotCanonicalBoundaryPresentationLabeled_otherFieldsX
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    Q.upperLeft = P.upperLeft ∧ Q.upperRight = P.upperRight ∧
      Q.lowerRight = P.lowerRight ∧ Q.lowerLeft.Index = P.lowerLeft.Index ∧
      Q.lowerLeft.darts = P.lowerLeft.darts ∧ Q.lowerLeft.next = P.lowerLeft.next := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩⟩

/-- Helper toward Definition 3.2: the exposed lower-left labels both equal
the terminal vertex of LR(0). -/
theorem uiqbotCanonicalBoundaryPresentationLabeled_rootLabelsX
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    Q.lowerLeft.initialVertex? = some (boundaryDartTerminal M (P.lowerRight.darts
      ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0))) ∧
      Q.lowerLeft.terminalVertex? = some (boundaryDartTerminal M (P.lowerRight.darts
        ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0))) := by
  exact ⟨rfl, rfl⟩

/-- Helper toward Definition 3.2: the labeled exposed UL index is the
constructor's natural-number index. -/
@[expose] noncomputable def uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.Index ≃ ℕ := by
  change ℕ ≃ ℕ
  exact Equiv.refl ℕ

/-- Helper toward Definition 3.2: the labeled exposed LR index is the
constructor's natural-number index. -/
@[expose] noncomputable def uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.Index ≃ ℕ := by
  change ℕ ≃ ℕ
  exact Equiv.refl ℕ

/-- Helper toward Definition 3.2: the endpoint of the exposed LR(0) dart
equals the initial endpoint of the exposed UL(0) dart. -/
theorem uiqbotCanonicalBoundaryPresentationX_rootJunction
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    boundaryDartTerminal M (P.lowerRight.darts
      ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0)) =
      boundaryDartInitial M (P.upperLeft.darts
        ((uiqbotCanonicalUpperLeftIndexEquivX w hfin htrans hR hL0).symm 0)) := by
  let M0 := uiqbotPresentationDirectedMapX w hfin
  let iota := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
  let M := uiqbotMapWithNoMissing M0
  have hcompat (e : ℕ) : M0.tail (iota e) = edgeWest w e ∧
      M0.head (iota e) = edgeEast w e := by
    have hiota : iota e = Quotient.mk (uiqbotPresentationDrawing w hfin).edgeSetoid (e, false) :=
      kmswGeometricEdgeEquiv_apply w hfin (uiqbotPresentationDrawing w hfin) e
    have htail (q : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
        M0.tail q = (if !q.out.2 then kmswLimitDartVertex w q.out
          else kmswLimitDartVertex w (q.out.1, !q.out.2)) := by rfl
    have hhead (q : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
        M0.head q = (if !q.out.2 then kmswLimitDartVertex w (q.out.1, !q.out.2)
          else kmswLimitDartVertex w q.out) := by rfl
    rw [hiota, htail, hhead]
    obtain hout | hout := (uiqbotPresentationDrawing w hfin).geometricEdge_out_mk (e, false)
    · rw [hout]
      simp [kmswLimitDartVertex, edgeWest, edgeEast]
    · rw [hout]
      simp [kmswLimitDartVertex, edgeWest, edgeEast]
  have hmiss (e : ℕ) : ¬ M.toPlaneMapWithMissing.missing (iota e) := by
    simp [M, uiqbotMapWithNoMissing]
  have hLRterm (e : ℕ) :
      boundaryDartTerminal M (iota e, !M.forward ⟨iota e, hmiss e⟩) = edgeWest w e := by
    by_cases hf : M0.forward (iota e)
    · simpa [boundaryDartTerminal_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using hcompat e |>.1
    · simpa [boundaryDartTerminal_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using hcompat e |>.1
  have hULinitial (e : ℕ) :
      boundaryDartInitial M (iota e, M.forward ⟨iota e, hmiss e⟩) = edgeWest w e := by
    by_cases hf : M0.forward (iota e)
    · simpa [boundaryDartInitial_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using hcompat e |>.1
    · simpa [boundaryDartInitial_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using hcompat e |>.1
  change boundaryDartTerminal M (iota (kmswRightBoundaryEdge w 0),
      !M.forward ⟨iota (kmswRightBoundaryEdge w 0), by simp [M, uiqbotMapWithNoMissing]⟩) =
    boundaryDartInitial M (iota (kmswLeftBoundaryEdge w 0),
      M.forward ⟨iota (kmswLeftBoundaryEdge w 0), by simp [M, uiqbotMapWithNoMissing]⟩)
  rw [hLRterm, hULinitial]
  exact uiqbotRootBoundaryEdges_sameWestEndpoint w hfin htrans hR hL0

/-- Helper toward Definition 3.2: the transported successor joins the exposed
presentation's LR(0) dart to its UL(0) dart. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_rootSuccessor
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    uiqbotCanonicalBoundaryDartExternalSucc w hfin
      (P.lowerRight.darts
        ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0)) =
      P.upperLeft.darts
        ((uiqbotCanonicalUpperLeftIndexEquivX w hfin htrans hR hL0).symm 0) := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  change uiqbotCanonicalBoundaryDartExternalSucc w hfin
      (P.lowerRight.darts
        ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0)) =
      P.upperLeft.darts
        ((uiqbotCanonicalUpperLeftIndexEquivX w hfin htrans hR hL0).symm 0)
  let D := uiqbotPresentationDrawing w hfin
  let iota := kmswGeometricEdgeEquiv w hfin D
  let f := uiqbotKMSWQuotientDartEquiv D iota
  have hUL : f (P.upperLeft.darts
      ((uiqbotCanonicalUpperLeftIndexEquivX w hfin htrans hR hL0).symm 0)) =
      (kmswLeftBoundaryEdge w 0, false) := by
    change f (iota (kmswLeftBoundaryEdge w 0),
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).forward
        ⟨iota (kmswLeftBoundaryEdge w 0), by simp [uiqbotMapWithNoMissing]⟩) = _
    exact uiqbotKMSWQuotientDartEquiv_directed D iota (kmswLeftBoundaryEdge w 0)
  have hLR : f (P.lowerRight.darts
      ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0)) =
      (kmswRightBoundaryEdge w 0, true) := by
    change f (iota (kmswRightBoundaryEdge w 0),
      !(uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).forward
        ⟨iota (kmswRightBoundaryEdge w 0), by simp [uiqbotMapWithNoMissing]⟩) = _
    simpa [uiqbotMapWithNoMissing, uiqbotPresentationDirectedMapX] using
      uiqbotKMSWQuotientDartEquiv_reverseDirected D iota
        (kmswRightBoundaryEdge w 0)
  have hsource : P.lowerRight.darts
      ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0) =
      f.symm (kmswRightBoundaryEdge w 0, true) := by
    apply f.injective
    simp [hLR]
  calc
    uiqbotCanonicalBoundaryDartExternalSucc w hfin
        (P.lowerRight.darts
          ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0)) =
        uiqbotCanonicalBoundaryDartExternalSucc w hfin
          (f.symm (kmswRightBoundaryEdge w 0, true)) := by rw [hsource]
    _ = f.symm (kmswLeftBoundaryEdge w 0, false) := by
      simpa [f, D, iota] using
        uiqbotCanonicalBoundaryDartExternalSucc_rootJunction w hfin hL0 htrans hR
    _ = P.upperLeft.darts
        ((uiqbotCanonicalUpperLeftIndexEquivX w hfin htrans hR hL0).symm 0) := by
      simpa [hUL] using
        (Equiv.symm_apply_apply f (P.upperLeft.darts
          ((uiqbotCanonicalUpperLeftIndexEquivX w hfin htrans hR hL0).symm 0)))















































































































































































end DirectedDistances.PaperProofs.Section4
end

