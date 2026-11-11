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

/-! # UIQBOT boundary frontier classification -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

abbrev uiqbotPresentationDrawing (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :=
  monotoneFamilyDrawing w hfin (monotone_family_all w)

/-- The canonical directed-map structure on the KMSW realization drawing. -/
noncomputable def uiqbotPresentationDirectedMap (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    DirectedPlaneMap ℕ (uiqbotPresentationDrawing w hfin).GeometricEdge where
  toPlaneGraphDrawing := (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing
  forward := fun q => !q.out.2

/-- The canonical four-side data on the KMSW directed realization. -/
noncomputable def uiqbotCanonicalBoundaryPresentation (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :=
  uiqbotDefinition32Presentation w htrans hR hL0
    (uiqbotPresentationDirectedMap w hfin)
    (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))

/-- Helper toward Definition 3.2: every dart of a KMSW edge outside the two
boundary streams borders a bounded triangular face. -/
theorem uiqbot_nonBoundary_dart_borders_internal_triangle
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : ℕ) (hleft : ¬ IsLeftBoundaryEdge w e)
    (hright : ¬ IsRightBoundaryEdge w e) :
    ∀ b : Bool, ∀ F : (uiqbotPresentationDrawing w hfin).Face,
      (uiqbotPresentationDrawing w hfin).dartBorders (e, b) F →
      ¬ (uiqbotPresentationDrawing w hfin).IsUnbounded F ∧
        ∃ j : TriangleCreationTime w,
          ∀ d : ℕ × Bool,
            (uiqbotPresentationDrawing w hfin).dartBorders d F ↔
              d ∈ stageTriangleDartList w j := by
  let P := uiqbotPresentationDrawing w hfin
  obtain ⟨U, hU, hUunique, hUborder⟩ :=
    monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
  have hnotOuter (b : Bool) : ¬ limitExternalDart w (e, b) := by
    intro hext
    rcases (limitExternalDart_iff w htrans hR hL0 (e, b)).mp hext with
      ⟨i, hi⟩ | ⟨i, hi⟩
    · apply hleft
      apply (isLeftBoundaryEdge_iff w htrans e).2
      exact ⟨i, congrArg Prod.fst hi⟩
    · apply hright
      apply (isRightBoundaryEdge_iff w hR e).2
      exact ⟨i, congrArg Prod.fst hi⟩
  intro b F hborder
  have hbounded : ¬ P.IsUnbounded F := by
    intro hF
    have hFU : F = U := hUunique F hF
    have hborderU : P.dartBorders (e, b) U := hFU ▸ hborder
    exact hnotOuter b ((hUborder (e, b)).1 hborderU)
  exact ⟨hbounded,
    uiqbotDrawing_bounded_face_triangle w hfin htrans hR hL0 F hbounded⟩

/-- Helper toward Definition 3.2: an edge outside both KMSW boundary streams
cannot lie on the frontier of an external face. -/
theorem uiqbot_nonBoundary_edge_not_externalFrontier
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : ℕ) (hleft : ¬ IsLeftBoundaryEdge w e)
    (hright : ¬ IsRightBoundaryEdge w e) :
    ¬ ∃ F : (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.Face,
      (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.IsExternal F ∧
        Set.range ((uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc
          (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e))
          ⊆ frontier F.val := by
  let P := uiqbotPresentationDrawing w hfin
  obtain ⟨U, hU, hUunique, hUborder⟩ :=
    monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
  have hnotOuter (d : ℕ × Bool) (hd : (d.1 = e)) :
      ¬ limitExternalDart w d := by
    intro hext
    rcases (limitExternalDart_iff w htrans hR hL0 d).mp hext with
      ⟨i, hi⟩ | ⟨i, hi⟩
    · apply hleft
      apply (isLeftBoundaryEdge_iff w htrans e).2
      exact ⟨i, hd ▸ congrArg Prod.fst hi⟩
    · apply hright
      apply (isRightBoundaryEdge_iff w hR e).2
      exact ⟨i, hd ▸ congrArg Prod.fst hi⟩
  rintro ⟨F, hFext, hfront⟩
  let K : P.toPlaneGraphDrawing.Face := F
  let K' : P.Face := P.toPlaneGraphDrawingFaceEquiv K
  have hKUnbounded : P.IsUnbounded K' :=
    (P.toPlaneGraphDrawing_isExternal_iff F).mp hFext
  have hKU : K' = U := hUunique K' hKUnbounded
  have hcl : P.toPlaneGraphDrawing.openArc
      (kmswGeometricEdgeEquiv w hfin P e) ⊆ closure K'.val := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    change P.toPlaneGraphDrawing.arc
      (kmswGeometricEdgeEquiv w hfin P e) t ∈ closure K.val
    have hzfront : P.toPlaneGraphDrawing.arc
        (kmswGeometricEdgeEquiv w hfin P e) t ∈ frontier F.val := by
      apply hfront
      exact ⟨t, rfl⟩
    exact frontier_subset_closure hzfront
  have hq := kmswGeometricEdgeEquiv_apply w hfin P e
  rcases (P).openArc_subset_closure_iff_bordering_dart
      (kmswLimitDartVertex_surjective w hfin)
      (kmswGeometricEdgeEquiv w hfin P e) K |>.mp hcl with hd | hd
  · have hout := P.geometricEdge_out_mk (e, false)
    rcases hout with hout | hout
    · have hd' : P.dartBorders (e, false) U := by
        rw [hq, hout] at hd
        rw [← hKU]
        exact hd
      exact hnotOuter (e, false) rfl ((hUborder (e, false)).1 hd')
    · have hd' : P.dartBorders (e, true) U := by
        rw [hq, hout] at hd
        rw [← hKU]
        exact hd
      exact hnotOuter (e, true) rfl ((hUborder (e, true)).1 hd')
  · have hout := P.geometricEdge_out_mk (e, false)
    rcases hout with hout | hout
    · have hd' : P.dartBorders (e, true) U := by
        rw [hq, hout] at hd
        simp only [Bool.not_false] at hd
        rw [← hKU]
        exact hd
      exact hnotOuter (e, true) rfl ((hUborder (e, true)).1 hd')
    · have hd' : P.dartBorders (e, false) U := by
        rw [hq, hout] at hd
        simp only [Bool.not_true] at hd
        rw [← hKU]
        exact hd
      exact hnotOuter (e, false) rfl ((hUborder (e, false)).1 hd')

/-- Helper toward Definition 3.2: every KMSW left or right boundary edge is
on the frontier of the unique unbounded face. -/
theorem uiqbot_boundary_edges_externalFrontier
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (∀ i, ∃ F : (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.Face,
      (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.IsExternal F ∧
        Set.range ((uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc
          (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
            (kmswLeftBoundaryEdge w i))) ⊆ frontier F.val) ∧
    (∀ i, ∃ F : (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.Face,
      (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.IsExternal F ∧
        Set.range ((uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc
          (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
            (kmswRightBoundaryEdge w i))) ⊆ frontier F.val) := by
  let P := uiqbotPresentationDrawing w hfin
  obtain ⟨U, hU, _, hUborder⟩ :=
    monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
  have hfrontier_of_border (e : ℕ) (d : ℕ × Bool)
      (he : kmswGeometricEdgeEquiv w hfin P e = Quotient.mk P.edgeSetoid d)
      (hd : P.dartBorders d U) :
      ∃ F : P.toPlaneGraphDrawing.Face,
        P.toPlaneGraphDrawing.IsExternal F ∧
          Set.range (P.toPlaneGraphDrawing.arc
            (kmswGeometricEdgeEquiv w hfin P e)) ⊆ frontier F.val := by
    let F : P.toPlaneGraphDrawing.Face :=
      P.toPlaneGraphDrawingFaceEquiv.symm U
    have hFext : P.toPlaneGraphDrawing.IsExternal F :=
      (P.toPlaneGraphDrawing_isExternal_iff F).2 (by simpa [F] using hU)
    have hclU : Set.range (P.toPlaneGraphDrawing.arc
        (kmswGeometricEdgeEquiv w hfin P e)) ⊆ closure F.val := by
      rw [he, P.toPlaneGraphDrawing_arc_range d]
      simpa only [show F.val = U.val from rfl] using P.dartBorders_arc_subset_closure
        (kmswLimitDartVertex_surjective w hfin) d U hd
    have hfront : Set.range (P.toPlaneGraphDrawing.arc
        (kmswGeometricEdgeEquiv w hfin P e)) ⊆ frontier F.val :=
      (P.toPlaneGraphDrawing.range_subset_closure_iff_frontier_of_face_complement
        F (kmswGeometricEdgeEquiv w hfin P e)).mp hclU
    exact ⟨F, hFext, hfront⟩
  constructor
  · intro i
    refine hfrontier_of_border (kmswLeftBoundaryEdge w i)
      (kmswLeftBoundaryEdge w i, false)
      (kmswGeometricEdgeEquiv_apply w hfin P _) ?_
    exact (hUborder _).2
      ((limitExternalDart_iff w htrans hR hL0 _).2 (Or.inl ⟨i, rfl⟩))
  · intro i
    refine hfrontier_of_border (kmswRightBoundaryEdge w i)
      (kmswRightBoundaryEdge w i, true) ?_ ?_
    · rw [kmswGeometricEdgeEquiv_apply]
      exact (P.geometricEdge_flip (kmswRightBoundaryEdge w i, false)).symm
    · exact (hUborder _).2
        ((limitExternalDart_iff w htrans hR hL0 _).2 (Or.inr ⟨i, rfl⟩))

/-- Helper toward Definition 3.2: each canonical left and right boundary
edge satisfies `ExternalFrontierEdge` for the no-missing UIQBOT map. -/
theorem uiqbot_boundary_edges_are_externalFrontierEdge
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j : ℕ, 0 ≤ L w j) :
    (∀ i, ExternalFrontierEdge
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
        (kmswLeftBoundaryEdge w i))) ∧
    (∀ i, ExternalFrontierEdge
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
        (kmswRightBoundaryEdge w i))) := by
  have hfront := uiqbot_boundary_edges_externalFrontier w hfin htrans hR hL0
  let M0 := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)
  have hdrawing : Drawing M0 = (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing :=
    uiqbotMapWithNoMissing_drawing_eq (uiqbotPresentationDirectedMap w hfin)
  constructor
  · intro i
    apply (externalFrontierEdge_iff M0 _).2
    rw [hdrawing]
    exact hfront.1 i
  · intro i
    apply (externalFrontierEdge_iff M0 _).2
    rw [hdrawing]
    exact hfront.2 i

/-- Helper toward Definition 3.2: the canonical external frontier consists
exactly of the KMSW left and right boundary edge streams. -/
theorem uiqbot_externalFrontier_iff_boundaryStream
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : ℕ) :
    (∃ F : (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.Face,
      (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.IsExternal F ∧
        Set.range ((uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc
          (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e))
          ⊆ frontier F.val) ↔
      (∃ i, e = kmswLeftBoundaryEdge w i) ∨
      (∃ i, e = kmswRightBoundaryEdge w i) := by
  constructor
  · intro hfront
    by_cases hleft : IsLeftBoundaryEdge w e
    · obtain ⟨i, hi⟩ := (isLeftBoundaryEdge_iff w htrans e).mp hleft
      exact Or.inl ⟨i, hi⟩
    · by_cases hright : IsRightBoundaryEdge w e
      · obtain ⟨i, hi⟩ := (isRightBoundaryEdge_iff w hR e).mp hright
        exact Or.inr ⟨i, hi⟩
      · exact False.elim ((uiqbot_nonBoundary_edge_not_externalFrontier
          w hfin htrans hR hL0 e hleft hright) hfront)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (uiqbot_boundary_edges_externalFrontier w hfin htrans hR hL0).1 i
    · exact (uiqbot_boundary_edges_externalFrontier w hfin htrans hR hL0).2 i

/-- Helper toward Definition 3.2: the two injective KMSW boundary streams
give at most two occurrences of any geometric edge in the supplied index sum. -/
theorem uiqbot_boundaryPresentation_edge_occurs_at_most_twice
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : (uiqbotPresentationDrawing w hfin).GeometricEdge)
    (i j k : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0)) :
    (InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e →
    (InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j).1 = e →
    (InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) k).1 = e →
    i = j ∨ i = k ∨ j = k := by
  let P := uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0
  let iota := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
  have hleftInj : Function.Injective (kmswLeftBoundaryEdge w) :=
    (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).1
  have hrightInj : Function.Injective (kmswRightBoundaryEdge w) :=
    (kmswRightBoundary_infinite_present_path w hL0 hR).1
  have hUL (n : ℕ) : (P.upperLeft.darts n).1 = iota (kmswLeftBoundaryEdge w n) := rfl
  have hLR (n : ℕ) : (P.lowerRight.darts n).1 = iota (kmswRightBoundaryEdge w n) := rfl
  have hUR : ∀ x : P.upperRight.Index, False := by
    intro x
    dsimp [P, uiqbotCanonicalBoundaryPresentation, uiqbotDefinition32Presentation] at x
    exact isEmptyElim x
  have hLL : ∀ x : P.lowerLeft.Index, False := by
    intro x
    dsimp [P, uiqbotCanonicalBoundaryPresentation, uiqbotDefinition32Presentation] at x
    exact isEmptyElim x
  intro hi hj hk
  cases i with
  | upperLeft i =>
    cases j with
    | upperLeft j =>
      have hei := hi
      have hej := hj
      rw [InfiniteBoundaryDartIndex.dart_eq] at hei hej
      change (P.upperLeft.darts i).1 = e at hei
      change (P.upperLeft.darts j).1 = e at hej
      rw [hUL i] at hei
      rw [hUL j] at hej
      have hidx : i = j := hleftInj (iota.injective (hei.trans hej.symm))
      exact Or.inl (congrArg InfiniteBoundaryDartIndex.upperLeft hidx)
    | lowerRight j =>
      cases k with
      | upperLeft k =>
        have hei := hi
        have hek := hk
        rw [InfiniteBoundaryDartIndex.dart_eq] at hei hek
        change (P.upperLeft.darts i).1 = e at hei
        change (P.upperLeft.darts k).1 = e at hek
        rw [hUL i] at hei
        rw [hUL k] at hek
        have hidx : i = k := hleftInj (iota.injective (hei.trans hek.symm))
        exact Or.inr (Or.inl (congrArg InfiniteBoundaryDartIndex.upperLeft hidx))
      | lowerRight k =>
        have hej := hj
        have hek := hk
        rw [InfiniteBoundaryDartIndex.dart_eq] at hej hek
        change (P.lowerRight.darts j).1 = e at hej
        change (P.lowerRight.darts k).1 = e at hek
        rw [hLR j] at hej
        rw [hLR k] at hek
        have hidx : j = k := hrightInj (iota.injective (hej.trans hek.symm))
        exact Or.inr (Or.inr (congrArg InfiniteBoundaryDartIndex.lowerRight hidx))
      | upperRight k => exact False.elim (hUR k)
      | lowerLeft k => exact False.elim (hLL k)
    | upperRight j => exact False.elim (hUR j)
    | lowerLeft j => exact False.elim (hLL j)
  | lowerRight i =>
    cases j with
    | upperLeft j =>
      cases k with
      | upperLeft k =>
        have hej := hj
        have hek := hk
        rw [InfiniteBoundaryDartIndex.dart_eq] at hej hek
        change (P.upperLeft.darts j).1 = e at hej
        change (P.upperLeft.darts k).1 = e at hek
        rw [hUL j] at hej
        rw [hUL k] at hek
        have hidx : j = k := hleftInj (iota.injective (hej.trans hek.symm))
        exact Or.inr (Or.inr (congrArg InfiniteBoundaryDartIndex.upperLeft hidx))
      | lowerRight k =>
        have hei := hi
        have hek := hk
        rw [InfiniteBoundaryDartIndex.dart_eq] at hei hek
        change (P.lowerRight.darts i).1 = e at hei
        change (P.lowerRight.darts k).1 = e at hek
        rw [hLR i] at hei
        rw [hLR k] at hek
        have hidx : i = k := hrightInj (iota.injective (hei.trans hek.symm))
        exact Or.inr (Or.inl (congrArg InfiniteBoundaryDartIndex.lowerRight hidx))
      | upperRight k => exact False.elim (hUR k)
      | lowerLeft k => exact False.elim (hLL k)
    | lowerRight j =>
      have hei := hi
      have hej := hj
      rw [InfiniteBoundaryDartIndex.dart_eq] at hei hej
      change (P.lowerRight.darts i).1 = e at hei
      change (P.lowerRight.darts j).1 = e at hej
      rw [hLR i] at hei
      rw [hLR j] at hej
      have hidx : i = j := hrightInj (iota.injective (hei.trans hej.symm))
      exact Or.inl (congrArg InfiniteBoundaryDartIndex.lowerRight hidx)
    | upperRight j => exact False.elim (hUR j)
    | lowerLeft j => exact False.elim (hLL j)
  | upperRight i => exact False.elim (hUR i)
  | lowerLeft i => exact False.elim (hLL i)

/-- Helper toward Definition 3.2: two distinct occurrences of one geometric
edge come from opposite present streams and carry opposite darts. -/
theorem uiqbot_boundaryPresentation_repeat_has_both_darts
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : (uiqbotPresentationDrawing w hfin).GeometricEdge)
    (i j : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0)) :
    i ≠ j →
    (InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e →
    (InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j).1 = e →
    ∃ b c : Bool, b ≠ c ∧
      InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i = (e, b) ∧
      InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j = (e, c) := by
  let M := uiqbotPresentationDirectedMap w hfin
  let M0 := uiqbotMapWithNoMissing M
  let P := uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0
  let iota := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
  have hleftInj : Function.Injective (kmswLeftBoundaryEdge w) :=
    (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).1
  have hrightInj : Function.Injective (kmswRightBoundaryEdge w) :=
    (kmswRightBoundary_infinite_present_path w hL0 hR).1
  have hUL (n : ℕ) : P.upperLeft.darts n =
      (iota (kmswLeftBoundaryEdge w n),
        M0.forward ⟨iota (kmswLeftBoundaryEdge w n), by
          simp [M0, uiqbotMapWithNoMissing]⟩) := by rfl
  have hLR (n : ℕ) : P.lowerRight.darts n =
      (iota (kmswRightBoundaryEdge w n),
        !(M0.forward ⟨iota (kmswRightBoundaryEdge w n), by
          simp [M0, uiqbotMapWithNoMissing]⟩)) := by rfl
  have hUR : ∀ x : P.upperRight.Index, False := by
    intro x
    dsimp [P, uiqbotCanonicalBoundaryPresentation, uiqbotDefinition32Presentation] at x
    exact isEmptyElim x
  have hLL : ∀ x : P.lowerLeft.Index, False := by
    intro x
    dsimp [P, uiqbotCanonicalBoundaryPresentation, uiqbotDefinition32Presentation] at x
    exact isEmptyElim x
  intro hne h1 h2
  cases i with
  | upperLeft i =>
    cases j with
    | upperLeft j =>
      have h1' := h1
      have h2' := h2
      rw [InfiniteBoundaryDartIndex.dart_eq] at h1' h2'
      change (P.upperLeft.darts i).1 = e at h1'
      change (P.upperLeft.darts j).1 = e at h2'
      rw [hUL i] at h1'
      rw [hUL j] at h2'
      have hij : i = j := hleftInj (iota.injective (h1'.trans h2'.symm))
      exact False.elim (hne (congrArg InfiniteBoundaryDartIndex.upperLeft hij))
    | lowerRight j =>
      have h1' := h1
      have h2' := h2
      rw [InfiniteBoundaryDartIndex.dart_eq] at h1' h2'
      change (P.upperLeft.darts i).1 = e at h1'
      change (P.lowerRight.darts j).1 = e at h2'
      rw [hUL i] at h1'
      rw [hLR j] at h2'
      have hlabels : kmswLeftBoundaryEdge w i = kmswRightBoundaryEdge w j :=
        iota.injective (h1'.trans h2'.symm)
      refine ⟨(P.upperLeft.darts i).2, (P.lowerRight.darts j).2, ?_, ?_, ?_⟩
      · rw [hUL i, hLR j, hlabels]
        cases hv : M0.forward ⟨iota (kmswLeftBoundaryEdge w i), by
          simp [M0, uiqbotMapWithNoMissing]⟩ <;> simp [hv]
      · rw [InfiniteBoundaryDartIndex.dart_eq, hUL i]
        exact Prod.ext h1' rfl
      · rw [InfiniteBoundaryDartIndex.dart_eq, hLR j]
        exact Prod.ext h2' rfl
    | upperRight j => exact False.elim (hUR j)
    | lowerLeft j => exact False.elim (hLL j)
  | lowerRight i =>
    cases j with
    | upperLeft j =>
      have h1' := h1
      have h2' := h2
      rw [InfiniteBoundaryDartIndex.dart_eq] at h1' h2'
      change (P.lowerRight.darts i).1 = e at h1'
      change (P.upperLeft.darts j).1 = e at h2'
      rw [hLR i] at h1'
      rw [hUL j] at h2'
      have hlabels : kmswLeftBoundaryEdge w j = kmswRightBoundaryEdge w i :=
        iota.injective (h2'.trans h1'.symm)
      refine ⟨(P.lowerRight.darts i).2, (P.upperLeft.darts j).2, ?_, ?_, ?_⟩
      · rw [hLR i, hUL j, hlabels]
        cases hv : M0.forward ⟨iota (kmswRightBoundaryEdge w i), by
          simp [M0, uiqbotMapWithNoMissing]⟩ <;> simp [hv]
      · rw [InfiniteBoundaryDartIndex.dart_eq, hLR i]
        exact Prod.ext h1' rfl
      · rw [InfiniteBoundaryDartIndex.dart_eq, hUL j]
        exact Prod.ext h2' rfl
    | lowerRight j =>
      have h1' := h1
      have h2' := h2
      rw [InfiniteBoundaryDartIndex.dart_eq] at h1' h2'
      change (P.lowerRight.darts i).1 = e at h1'
      change (P.lowerRight.darts j).1 = e at h2'
      rw [hLR i] at h1'
      rw [hLR j] at h2'
      have hij : i = j := hrightInj (iota.injective (h1'.trans h2'.symm))
      exact False.elim (hne (congrArg InfiniteBoundaryDartIndex.lowerRight hij))
    | upperRight j => exact False.elim (hUR j)
    | lowerLeft j => exact False.elim (hLL j)
  | upperRight i => exact False.elim (hUR i)
  | lowerLeft i => exact False.elim (hLL i)

/-- Helper toward Definition 3.2: the canonical directed map is drawn by the
KMSW realization drawing. -/
theorem uiqbotPresentationDirectedMap_toPlaneGraphDrawing (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    (uiqbotPresentationDirectedMap w hfin).toPlaneGraphDrawing =
      (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing := by
  unfold uiqbotPresentationDirectedMap
  rfl

/-- Helper toward Definition 3.2: the canonical presentation is the generic
constructor applied to the canonical directed map and edge equivalence. -/
theorem uiqbotCanonicalBoundaryPresentation_eq (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0 =
      uiqbotDefinition32Presentation w htrans hR hL0
        (uiqbotPresentationDirectedMap w hfin)
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)) := by
  unfold uiqbotCanonicalBoundaryPresentation
  rfl

























end DirectedDistances.PaperProofs.Section4

end
