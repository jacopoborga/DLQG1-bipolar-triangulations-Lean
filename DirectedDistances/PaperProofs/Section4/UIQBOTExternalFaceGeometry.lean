/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTJoinEndpointLabels
public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder
public import DirectedDistances.KMSW.MonotoneOuterWitness
import all DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation3
import all DirectedDistances.PlanarMap.InfiniteBoundaryPresentationData

/-! # UIQBOT external-face geometry

results identify the existing KMSW limit drawing and its unbounded face. They
do not assert a transported drawing on the UIQBOT geometric-edge carrier. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open Filter

/-- Helper toward Definition 3.2: the KMSW limit drawing has a unique
unbounded face with persistent external darts, and its code successor is the
geometric external-face successor. -/
theorem uiqbotKMSWPresentation_geometricExternalFaceSucc
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
        (kmswInfRot w hfin) (kmswLimitDartVertex w) :=
      monotoneFamilyDrawing w hfin (monotone_family_all w)
    ∃ U : G.Face, G.IsUnbounded U ∧
      (∀ F : G.Face, G.IsUnbounded F → F = U) ∧
      (∀ d, G.dartBorders d U ↔ limitExternalDart w d) ∧
      IsGeometricExternalFaceSucc G U (kmswInfFaceSucc w hfin) := by
  let G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w) :=
    monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨U, hUnbounded, hUnique, hBorder⟩ :=
    monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
  exact ⟨U, hUnbounded, hUnique, hBorder,
    kmswInfFaceSucc_isGeometricExternalFaceSucc w hfin G U hUnbounded hBorder
      htrans hR hL0⟩

/-- Helper toward Definition 3.2: the left and right KMSW boundary rays and
their root junction are successive darts of the external face. -/
theorem uiqbotKMSWPresentation_externalBoundarySteps
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
        (kmswInfRot w hfin) (kmswLimitDartVertex w) :=
      monotoneFamilyDrawing w hfin (monotone_family_all w)
    ∃ U : G.Face, G.IsUnbounded U ∧
      (∀ d, G.dartBorders d U ↔ limitExternalDart w d) ∧
      ((∀ i, G.dartBorders (kmswLeftBoundaryEdge w i, false) U ∧
          kmswInfFaceSucc w hfin (kmswLeftBoundaryEdge w i, false) =
            (kmswLeftBoundaryEdge w (i + 1), false) ∧
          G.dartBorders (kmswLeftBoundaryEdge w (i + 1), false) U) ∧
       (∀ i, G.dartBorders (kmswRightBoundaryEdge w (i + 1), true) U ∧
          kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w (i + 1), true) =
            (kmswRightBoundaryEdge w i, true) ∧
          G.dartBorders (kmswRightBoundaryEdge w i, true) U) ∧
       (G.dartBorders (kmswRightBoundaryEdge w 0, true) U ∧
          kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w 0, true) =
            (kmswLeftBoundaryEdge w 0, false) ∧
          G.dartBorders (kmswLeftBoundaryEdge w 0, false) U)) := by
  let G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w) :=
    monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨U, hUnbounded, _, hBorder⟩ :=
    monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
  exact ⟨U, hUnbounded, hBorder,
    kmswInfFaceSucc_geometric_boundarySteps w hfin G U hUnbounded hBorder
      htrans hR hL0⟩

/-- Helper toward Definition 3.2: the labeled UIQBOT presentation carries the
proved endpoint-label predicate at its external-successor joins. -/
theorem uiqbotLabeledPresentation_boundaryJoinEndpointLabels
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    BoundaryJoinEndpointLabels P (uiqbotCanonicalBoundaryDartExternalSucc w hfin) :=
  uiqbotCanonicalBoundaryPresentationLabeledX_BoundaryJoinEndpointLabels
    w hfin htrans hR hL0

/-- Helper toward Definition 3.2: the exposed canonical presentation has the
set-level external-frontier and multiplicity clauses. -/
theorem uiqbotCanonicalPresentationX_isBoundaryOrderOfInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    IsBoundaryOrderOfInf M P := by
  simpa [uiqbotPresentationDirectedMapX, uiqbotCanonicalBoundaryPresentationX,
    uiqbotCanonicalBoundaryPresentation, uiqbotPresentationDirectedMap] using
      uiqbotCanonicalBoundaryPresentation_isBoundaryOrderOfInf
        w hfin htrans hR hL0

/-- Helper toward Definition 3.2: changing the optional labels on the empty
lower-left side preserves the canonical set-level boundary-order clauses. -/
theorem uiqbotLabeledPresentationX_isBoundaryOrderOfInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    IsBoundaryOrderOfInf M P := by
  let P₀ := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  have hbase : IsBoundaryOrderOfInf M P₀ :=
    uiqbotCanonicalPresentationX_isBoundaryOrderOfInf w hfin htrans hR hL0
  obtain ⟨hul, hur, hlr, _hllIndex, hllDarts, _hllNext⟩ :=
    uiqbotCanonicalBoundaryPresentationLabeled_otherFieldsX
      w hfin htrans hR hL0
  let e : InfiniteBoundaryDartIndex P ≃ InfiniteBoundaryDartIndex P₀ := {
    toFun := fun i => match i with
      | .upperLeft i => .upperLeft i
      | .upperRight i => .upperRight i
      | .lowerRight i => .lowerRight i
      | .lowerLeft i => .lowerLeft i
    invFun := fun i => match i with
      | .upperLeft i => .upperLeft i
      | .upperRight i => .upperRight i
      | .lowerRight i => .lowerRight i
      | .lowerLeft i => .lowerLeft i
    left_inv := by intro i; cases i <;> rfl
    right_inv := by intro i; cases i <;> rfl }
  have hdart (i : InfiniteBoundaryDartIndex P) :
      InfiniteBoundaryDartIndex.dart P i =
        InfiniteBoundaryDartIndex.dart P₀ (e i) := by
    cases i with
    | upperLeft i => cases hul; rfl
    | upperRight i => cases hur; rfl
    | lowerRight i => cases hlr; rfl
    | lowerLeft i => exact congrArg (fun ds => ds i) hllDarts
  have hfront := (IsBoundaryOrderOfInf_iff P₀).mp hbase
  apply (IsBoundaryOrderOfInf_iff P).mpr
  rcases hfront with ⟨hfront, hthree, htwo⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    constructor
    · rintro ⟨i, hi⟩
      apply (hfront edge).mp
      exact ⟨e i, by rw [← hdart i]; exact hi⟩
    · intro hi
      obtain ⟨i, hi⟩ := (hfront edge).mpr hi
      refine ⟨e.symm i, ?_⟩
      rw [hdart]
      simpa using hi
  · intro edge i j k hi hj hk
    have hi' : (InfiniteBoundaryDartIndex.dart P₀ (e i)).1 = edge := by
      rw [← hdart i]; exact hi
    have hj' : (InfiniteBoundaryDartIndex.dart P₀ (e j)).1 = edge := by
      rw [← hdart j]; exact hj
    have hk' : (InfiniteBoundaryDartIndex.dart P₀ (e k)).1 = edge := by
      rw [← hdart k]; exact hk
    rcases hthree edge (e i) (e j) (e k) hi' hj' hk' with h | h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (Or.inl (e.injective h))
    · exact Or.inr (Or.inr (e.injective h))
  · intro edge i j hij hi hj
    have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hi' : (InfiniteBoundaryDartIndex.dart P₀ (e i)).1 = edge := by
      rw [← hdart i]; exact hi
    have hj' : (InfiniteBoundaryDartIndex.dart P₀ (e j)).1 = edge := by
      rw [← hdart j]; exact hj
    exact htwo edge (e i) (e j) hne hi' hj'






















































end DirectedDistances.PaperProofs.Section4

end
