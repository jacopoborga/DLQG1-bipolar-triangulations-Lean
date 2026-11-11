/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation10
import all DirectedDistances.PlanarMap.InfiniteBoundaryPresentationData
import all DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation3
import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport
import DirectedDistances.PlanarMap.Definition32OrientedSideTransport2






public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Definition 3.2: the canonical edge equivalence preserves
both directed endpoints, including when the quotient selects the flipped dart. -/
private theorem uiqbotPresentation11_compatibility
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    ∀ e, (uiqbotPresentationDirectedMap w hfin).tail
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e) =
      edgeWest w e ∧
      (uiqbotPresentationDirectedMap w hfin).head
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e) =
      edgeEast w e := by
  let P := uiqbotPresentationDrawing w hfin
  intro e
  have htail (q : P.GeometricEdge) :
      (uiqbotPresentationDirectedMap w hfin).tail q =
        (if !q.out.2 then kmswLimitDartVertex w q.out
          else kmswLimitDartVertex w (q.out.1, !q.out.2)) := by
    unfold uiqbotPresentationDirectedMap
    rfl
  have hhead (q : P.GeometricEdge) :
      (uiqbotPresentationDirectedMap w hfin).head q =
        (if !q.out.2 then kmswLimitDartVertex w (q.out.1, !q.out.2)
          else kmswLimitDartVertex w q.out) := by
    unfold uiqbotPresentationDirectedMap
    rfl
  rw [htail, hhead, kmswGeometricEdgeEquiv_apply]
  obtain hout | hout := P.geometricEdge_out_mk (e, false)
  · rw [hout]
    simp [kmswLimitDartVertex, edgeWest, edgeEast]
  · rw [hout]
    simp [kmswLimitDartVertex, edgeWest, edgeEast]

/-- Helper toward Definition 3.2: external PL border tests on either
orientation of the representative give the directed left or right side. -/
private theorem uiqbotPresentation11_side
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (U : (uiqbotPresentationDrawing w hfin).Face)
    (e : ℕ) (b : Bool)
    (hb : (uiqbotPresentationDrawing w hfin).dartBorders (e, b) U) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)
    let q := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e
    let F : (Drawing M).Face :=
      (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawingFaceEquiv.symm U
    if b then RightOf M F ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩
      else LeftOf M F ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ := by
  let P := uiqbotPresentationDrawing w hfin
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)
  let q := kmswGeometricEdgeEquiv w hfin P e
  let F : (Drawing M).Face := P.toPlaneGraphDrawingFaceEquiv.symm U
  have hout : q.out = (e, false) ∨ q.out = (e, true) := by
    dsimp only [q]
    rw [kmswGeometricEdgeEquiv_apply]
    exact P.geometricEdge_out_mk (e, false)
  have hf : M.forward ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ = !q.out.2 := by
    change (uiqbotPresentationDirectedMap w hfin).forward q = _
    unfold uiqbotPresentationDirectedMap
    rfl
  have hleft (hd : P.dartBorders q.out U) :
      ∀ s, LeftAtOn F.val ((Drawing M).arc q) s := by
    intro s
    exact (P.toPlaneGraphDrawing_leftAtOn_iff q F s).mpr
      (P.dartBorders_toPath_leftAtOn (kmswLimitDartVertex_surjective w hfin)
        q.out U hd s)
  have hright (hd : P.dartBorders (q.out.1, !q.out.2) U) :
      ∀ s, RightAtOn F.val ((Drawing M).arc q) s := by
    intro s
    exact (P.toPlaneGraphDrawing_rightAtOn_iff q F s).mpr
      (P.dartBorders_flip_toPath_rightAtOn (kmswLimitDartVertex_surjective w hfin)
        q.out U hd s)
  cases b with
  | false =>
    change LeftOf M F _
    intro s
    change LeftAtOn F.val (orientedArc M _) s
    have hc := orientedArc_coe M ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩
    rcases hout with hout | hout
    · have hforward : M.forward ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ = true := by
        rw [hf, hout]; rfl
      rw [ite_eq_left hforward] at hc
      exact (leftAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        (hleft (by simpa only [hout] using hb) s)
    · have hforward : M.forward ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ ≠ true := by
        rw [hf, hout]; exact Bool.false_ne_true
      rw [ite_eq_right hforward] at hc
      exact (leftAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        ((forall_leftAtOn_symm_iff F.val ((Drawing M).arc q)).mpr
          (hright (by simpa only [hout, Bool.not_true] using hb)) s)
  | true =>
    change RightOf M F _
    intro s
    change RightAtOn F.val (orientedArc M _) s
    have hc := orientedArc_coe M ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩
    rcases hout with hout | hout
    · have hforward : M.forward ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ = true := by
        rw [hf, hout]; rfl
      rw [ite_eq_left hforward] at hc
      exact (rightAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        (hright (by simpa only [hout, Bool.not_false] using hb) s)
    · have hforward : M.forward ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ ≠ true := by
        rw [hf, hout]; exact Bool.false_ne_true
      rw [ite_eq_right hforward] at hc
      exact (rightAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        ((forall_rightAtOn_symm_iff F.val ((Drawing M).arc q)).mpr
          (hleft (by simpa only [hout] using hb)) s)

/-- Helper toward Definition 3.2: the canonical upper-left stream consists
of present forward edges with an external face on the directed left, and
consecutive darts join. -/
theorem uiqbotCanonicalBoundaryPresentation_ulOkInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    ULOkInf (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) := by
  rw [uiqbotCanonicalBoundaryPresentation_eq]
  unfold ULOkInf
  constructor
  · intro i
    refine ⟨by change ¬ False; exact not_false, rfl, ?_⟩
    let P := uiqbotPresentationDrawing w hfin
    obtain ⟨U, hU, _, hUborder⟩ :=
      monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
    let F := P.toPlaneGraphDrawingFaceEquiv.symm U
    refine ⟨F, ?_, ?_⟩
    · exact (P.toPlaneGraphDrawing_isExternal_iff F).mpr
        (by simpa only [F, Equiv.apply_symm_apply] using hU)
    · exact uiqbotPresentation11_side w hfin U (kmswLeftBoundaryEdge w i) false
        ((hUborder _).mpr ((limitExternalDart_iff w htrans hR hL0 _).mpr
          (Or.inl ⟨i, rfl⟩)))
  · exact (uiqbotDefinition32Presentation_joinClauses w htrans hR hL0
      (uiqbotPresentationDirectedMap w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))
      (uiqbotPresentation11_compatibility w hfin)).1

/-- Helper toward Definition 3.2: the canonical lower-right stream consists
of present reverse-traversed edges with an external face on the directed
right, and consecutive darts join. -/
theorem uiqbotCanonicalBoundaryPresentation_lrOkInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    LROkInf (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) := by
  rw [uiqbotCanonicalBoundaryPresentation_eq]
  unfold LROkInf
  constructor
  · intro i
    refine ⟨by change ¬ False; exact not_false, rfl, ?_⟩
    let P := uiqbotPresentationDrawing w hfin
    obtain ⟨U, hU, _, hUborder⟩ :=
      monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
    let F := P.toPlaneGraphDrawingFaceEquiv.symm U
    refine ⟨F, ?_, ?_⟩
    · exact (P.toPlaneGraphDrawing_isExternal_iff F).mpr
        (by simpa only [F, Equiv.apply_symm_apply] using hU)
    · exact uiqbotPresentation11_side w hfin U (kmswRightBoundaryEdge w i) true
        ((hUborder _).mpr ((limitExternalDart_iff w htrans hR hL0 _).mpr
          (Or.inr ⟨i, rfl⟩)))
  · exact (uiqbotDefinition32Presentation_joinClauses w htrans hR hL0
      (uiqbotPresentationDirectedMap w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))
      (uiqbotPresentation11_compatibility w hfin)).2

/-- Helper toward Definition 3.2: the canonical presentation satisfies both
present-side predicates together with the set-level boundary-order predicate.
The cyclic interval-order requirement remains separate. -/
theorem uiqbotCanonicalBoundaryPresentation_sideClauses_and_boundaryOrder
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    ULOkInf (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) ∧
      LROkInf (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) ∧
      IsBoundaryOrderOfInf
        (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) := by
  exact ⟨uiqbotCanonicalBoundaryPresentation_ulOkInf w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentation_lrOkInf w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentation_isBoundaryOrderOfInf w hfin htrans hR hL0⟩

end DirectedDistances.PaperProofs.Section4
end
