/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation4

/-! # UIQBOT frontier-set presentation -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open Filter
open unitInterval

/-- Helper toward Definition 3.2: the canonical presentation lists exactly
the geometric edges on the external frontier. -/
theorem uiqbotCanonicalBoundaryPresentation_frontierSet
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    ∀ e : (uiqbotPresentationDrawing w hfin).GeometricEdge,
      (∃ i : InfiniteBoundaryDartIndex
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0),
        (InfiniteBoundaryDartIndex.dart
          (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e) ↔
      ExternalFrontierEdge
        (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)) e := by
  let iota := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
  let M := uiqbotPresentationDirectedMap w hfin
  let M0 := uiqbotMapWithNoMissing M
  have hdrawing :
      Drawing M0 = (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing := by
    calc
      Drawing M0 = M.toPlaneGraphDrawing := uiqbotMapWithNoMissing_drawing_eq M
      _ = (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing :=
        uiqbotPresentationDirectedMap_toPlaneGraphDrawing w hfin
  have harcFun (e : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
      (M0.toPlaneMapWithMissing.arc e : I → ℂ) =
        ((uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc e : I → ℂ) := by
    change ((Drawing M0).arc e : I → ℂ) =
      ((uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc e : I → ℂ)
    exact congrArg (fun D : PlaneGraphDrawing ℕ
      (uiqbotPresentationDrawing w hfin).GeometricEdge => (D.arc e : I → ℂ)) hdrawing
  have harcRange (e : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
      Set.range (M0.toPlaneMapWithMissing.arc e) =
        Set.range ((uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc e) := by
    change Set.range (fun t : I => M0.toPlaneMapWithMissing.arc e t) =
      Set.range (fun t : I => (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc e t)
    rw [harcFun e]
  have hfront (e : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
      ExternalFrontierEdge M0 e ↔
        (∃ i, e = iota (kmswLeftBoundaryEdge w i)) ∨
          (∃ i, e = iota (kmswRightBoundaryEdge w i)) := by
    constructor
    · intro he
      have hface := (externalFrontierEdge_iff M0 e).mp he
      rw [hdrawing, ← iota.apply_symm_apply e, harcRange] at hface
      have hstreams :=
        uiqbotCanonicalBoundaryPresentation_externalFrontierStream
          w hfin htrans hR hL0 (iota.symm e)
      rcases hstreams.mp hface with hleft | hright
      · rcases hleft with ⟨i, hi⟩
        left
        refine ⟨i, ?_⟩
        calc
          e = iota (iota.symm e) := (iota.apply_symm_apply e).symm
          _ = iota (kmswLeftBoundaryEdge w i) := congrArg iota hi
      · rcases hright with ⟨i, hi⟩
        right
        refine ⟨i, ?_⟩
        calc
          e = iota (iota.symm e) := (iota.apply_symm_apply e).symm
          _ = iota (kmswRightBoundaryEdge w i) := congrArg iota hi
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · have hindex : iota.symm e = kmswLeftBoundaryEdge w i := by
          apply iota.injective
          calc
            iota (iota.symm e) = e := iota.apply_symm_apply e
            _ = iota (kmswLeftBoundaryEdge w i) := hi
        have hstreams :=
          uiqbotCanonicalBoundaryPresentation_externalFrontierStream
            w hfin htrans hR hL0 (iota.symm e)
        have hface := hstreams.mpr (Or.inl ⟨i, hindex⟩)
        rw [iota.apply_symm_apply e, ← harcRange e, ← hdrawing] at hface
        exact (externalFrontierEdge_iff M0 e).mpr hface
      · have hindex : iota.symm e = kmswRightBoundaryEdge w i := by
          apply iota.injective
          calc
            iota (iota.symm e) = e := iota.apply_symm_apply e
            _ = iota (kmswRightBoundaryEdge w i) := hi
        have hstreams :=
          uiqbotCanonicalBoundaryPresentation_externalFrontierStream
            w hfin htrans hR hL0 (iota.symm e)
        have hface := hstreams.mpr (Or.inr ⟨i, hindex⟩)
        rw [iota.apply_symm_apply e, ← harcRange e, ← hdrawing] at hface
        exact (externalFrontierEdge_iff M0 e).mpr hface
  have hocc (e : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
      (∃ i : InfiniteBoundaryDartIndex
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0),
        (InfiniteBoundaryDartIndex.dart
          (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e) ↔
      ((∃ n, e = iota (kmswLeftBoundaryEdge w n)) ∨
        (∃ n, e = iota (kmswRightBoundaryEdge w n))) := by
    rw [uiqbotCanonicalBoundaryPresentation_eq w hfin htrans hR hL0]
    rw [uiqbotDefinition32Presentation_eq]
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | upperLeft n =>
          rw [InfiniteBoundaryDartIndex.dart_eq] at hi
          change iota (kmswLeftBoundaryEdge w n) = e at hi
          exact Or.inl ⟨n, hi.symm⟩
      | upperRight n => cases n
      | lowerRight n =>
          rw [InfiniteBoundaryDartIndex.dart_eq] at hi
          change iota (kmswRightBoundaryEdge w n) = e at hi
          exact Or.inr ⟨n, hi.symm⟩
      | lowerLeft n => cases n
    · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
      · refine ⟨InfiniteBoundaryDartIndex.upperLeft n, ?_⟩
        rw [InfiniteBoundaryDartIndex.dart_eq]
        change iota (kmswLeftBoundaryEdge w n) = e
        exact hn.symm
      · refine ⟨InfiniteBoundaryDartIndex.lowerRight n, ?_⟩
        rw [InfiniteBoundaryDartIndex.dart_eq]
        change iota (kmswRightBoundaryEdge w n) = e
        exact hn.symm
  have hstream (e : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
      ((∃ n, e = iota (kmswLeftBoundaryEdge w n)) ∨
        (∃ n, e = iota (kmswRightBoundaryEdge w n))) ↔
      ExternalFrontierEdge
        (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)) e := by
    constructor
    · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
      · have hh := (hfront e).2 (Or.inl ⟨n, hn⟩)
        simpa [hn] using hh
      · have hh := (hfront e).2 (Or.inr ⟨n, hn⟩)
        simpa [hn] using hh
    · intro he
      rcases (hfront e).1 he with hleft | hright
      · rcases hleft with ⟨n, hn⟩
        left
        exact ⟨n, hn⟩
      · rcases hright with ⟨n, hn⟩
        right
        exact ⟨n, hn⟩
  intro e
  exact (hocc e).trans (hstream e)

/-- Helper toward Definition 3.2: given edge occurrences at the specified
boundary dart indices, the edge is present and has an external-face frontier
witness. -/
theorem uiqbotCanonicalBoundaryPresentation_repeatedEdge_externalFrontierFaces
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : (uiqbotPresentationDrawing w hfin).GeometricEdge)
    (i j : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0)) :
    (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e →
    (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j).1 = e →
    ∃ _hp : ¬ (uiqbotMapWithNoMissing
        (uiqbotPresentationDirectedMap w hfin)).toPlaneMapWithMissing.missing e,
      ∃ F G : PlaneGraphDrawing.Face
          (Drawing (uiqbotMapWithNoMissing
            (uiqbotPresentationDirectedMap w hfin))),
        (Drawing (uiqbotMapWithNoMissing
          (uiqbotPresentationDirectedMap w hfin))).IsExternal F ∧
        (Drawing (uiqbotMapWithNoMissing
          (uiqbotPresentationDirectedMap w hfin))).IsExternal G ∧
        Set.range ((uiqbotMapWithNoMissing
          (uiqbotPresentationDirectedMap w hfin)).toPlaneMapWithMissing.arc e) ⊆
            frontier F.val ∧
        Set.range ((uiqbotMapWithNoMissing
          (uiqbotPresentationDirectedMap w hfin)).toPlaneMapWithMissing.arc e) ⊆
            frontier G.val := by
  intro hi hj
  have hext : ExternalFrontierEdge
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)) e :=
    (uiqbotCanonicalBoundaryPresentation_frontierSet
      w hfin htrans hR hL0 e).mp ⟨i, hi⟩
  obtain ⟨F, hFext, hFfront⟩ :=
    (externalFrontierEdge_iff
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)) e).mp hext
  have hp : ¬ (uiqbotMapWithNoMissing
      (uiqbotPresentationDirectedMap w hfin)).toPlaneMapWithMissing.missing e := by
    rw [uiqbotMapWithNoMissing_missing_eq]
    exact not_false
  exact ⟨hp, F, F, hFext, hFext, hFfront, hFfront⟩









































end DirectedDistances.PaperProofs.Section4

end
