/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPositionOrder2
public import DirectedDistances.PaperProofs.Section4.UIQBOTIntervalOrder3Clauses
public import DirectedDistances.PaperProofs.Section4.UIQBOTJoinEndpointLabels
public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry2
public import DirectedDistances.PaperProofs.Section4.UIQBOTOkInf
public import DirectedDistances.PaperProofs.Section4.UIQBOTSideSimplicity2
public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder7

/-! # UIQBOT infinite external-face interval-order instance

infinite branch of `IsExternalFaceIntervalOrder7` at
`DirectedDistances/PlanarMap/ExternalFaceIntervalOrder7.lean:133–143` has
three top-level conjuncts. The first two are proved below; the third is
equivalent to the v3 instance, whose exact remaining open clauses are recorded
at the end of this file.

The nested v3 clause map is:

* `IsBoundaryOrderOfInf`: `UIQBOTExternalFaceGeometry.lean:123`.
* `G.dartBorders` iff the boundary-index image: open on the quotient carrier;
  the transported `limitExternalDart` classification is at
  `UIQBOTExternalFaceGeometry2.lean:391`.
* `IsGeometricExternalFaceSucc`: `UIQBOTExternalFaceGeometry2.lean:391`.
* Within-side successor plus endpoint joins, total successor existence, and
  converse successor classification: open.
* `ULOkInf`, `UROkInf`, `LROkInf`, `LLOkInf`: `UIQBOTOkInf.lean:271`,
  `UIQBOTIntervalOrder2Clauses.lean:21`, `UIQBOTOkInf.lean:305`, and
  `UIQBOTIntervalOrder2Clauses.lean:37`, respectively.
* UL/LR simplicity: `UIQBOTSideSimplicity2.lean:421` and `:466`.
* UL/UR/LR/LL endpoint labels:
  `UIQBOTIntervalOrder3Clauses.lean:21`,
  `UIQBOTIntervalOrder2Clauses.lean:79`,
  `UIQBOTIntervalOrder3Clauses.lean:97`, and
  `UIQBOTIntervalOrder2Clauses.lean:98`, respectively.
* `BoundaryJoinEndpointLabels`: `UIQBOTJoinEndpointLabels.lean:225`.
* `BoundaryPositionOrder3`: `UIQBOTPositionOrder2.lean:262`.
* `RequiredBoundaryJoinEndpointLabels`:
  `UIQBOTPresentationExposed7.lean:23`.

All supplied UIQBOT clauses use the labeled X carrier. Older
`uiqbotCanonicalBoundaryPresentation` declarations use the non-X directed-map
carrier and are not substituted for these.

premise is introduced here. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter

/-- Helper toward Definition 3.2: the external dart set of the canonical
labeled X presentation is infinite, witnessed by its upper-left ray. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_externalBoundaryInfinite
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ¬ (externalBoundaryDartSet4 M).Finite := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  have hmap : IsBoundaryOrderOfInf M P := by
    simpa only [P, M] using
      uiqbotLabeledPresentationX_isBoundaryOrderOfInf w hfin htrans hR hL0
  let e := uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0
  let ray : ℕ ↪ P.upperLeft.Index := ⟨e.symm, e.symm.injective⟩
  exact externalBoundaryDartSet4_infinite_of_upperLeft_ray hmap ray

/-- Helper toward Definition 3.2: package the canonical labeled X boundary
with no retained finite-junction data. -/
@[expose] noncomputable def uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    BoundaryPresentationWithJunctions M := by
  exact ⟨uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0,
    none⟩

/-- Helper toward Definition 3.2: the canonical labeled X wrapper has no
finite junction marks. -/
@[simp] theorem uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions_none
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions
      w hfin htrans hR hL0).finiteJunctions? = none := rfl

/-- Helper toward Definition 3.2: for the canonical labeled X wrapper, the
v7 predicate is equivalent to its v3 infinite-boundary clause. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_externalFaceIntervalOrder7_iff
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {rot : Equiv.Perm ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)}
    (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) ℕ
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial
        (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))))
    (U : G.Face)
    (S : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool →
      (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let B := uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions
      w hfin htrans hR hL0
    IsExternalFaceIntervalOrder7 M B G U S ↔
      IsExternalFaceIntervalOrder3 M P G U S := by
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let B := uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions
    w hfin htrans hR hL0
  change IsExternalFaceIntervalOrder7 M B G U S ↔
    IsExternalFaceIntervalOrder3 M P G U S
  have hInfinite : ¬ (externalBoundaryDartSet4 M).Finite := by
    simpa only [M] using
      uiqbotCanonicalBoundaryPresentationLabeledX_externalBoundaryInfinite
        w hfin htrans hR hL0
  rw [IsExternalFaceIntervalOrder7.infinite_iff hInfinite]
  simp [P, B, uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions]









































end DirectedDistances.PaperProofs.Section4

end
