/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry2
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Sides
public import DirectedDistances.PlanarMap.Definition32OrientedSideTransport2

/-! # UIQBOT present-side predicates toward Definition 3.2

The canonical quotient drawing has incident darts at every vertex. Its
external-dart classification therefore gives the winding-side tests on every
open dart parameter. The canonical `X` presentation's present-side clauses
then reuse the checked map-drawing characterization. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Definition 3.2: the UIQBOT KMSW drawing has a surjective
vertex map, since every vertex is incident to a geometric edge. -/
theorem uiqbotPresentationDrawing_vert_surjective
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    Function.Surjective (kmswLimitDartVertex w) :=
  kmswLimitDartVertex_surjective w hfin

/-- Helper toward Definition 3.2: the transported UIQBOT quotient drawing
has a surjective vertex map. The canonical dart equivalence identifies its
incidences with those of the KMSW drawing. -/
theorem uiqbotCanonicalQuotientDrawing_vert_surjective
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    Function.Surjective (boundaryDartInitial
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))) := by
  intro v
  obtain ⟨d, hd⟩ := uiqbotPresentationDrawing_vert_surjective w hfin v
  refine ⟨uiqbotCanonicalBoundaryDartEquiv w hfin d, ?_⟩
  rw [uiqbotCanonicalBoundaryDartEquiv_initialVertex]
  exact hd

/-- Helper toward Definition 3.2: the exposed `X` directed map has the
west-to-east endpoint identification used by the canonical side joins. -/
private theorem uiqbotPresentationX_compatibility
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    ∀ e, (uiqbotPresentationDirectedMapX w hfin).tail
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e) =
      edgeWest w e ∧
      (uiqbotPresentationDirectedMapX w hfin).head
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e) =
      edgeEast w e := by
  let P := uiqbotPresentationDrawing w hfin
  intro e
  have htail (q : P.GeometricEdge) :
      (uiqbotPresentationDirectedMapX w hfin).tail q =
        (if !q.out.2 then kmswLimitDartVertex w q.out
          else kmswLimitDartVertex w (q.out.1, !q.out.2)) := by
    change (if (uiqbotPresentationDirectedMapX w hfin).forward q then
      (uiqbotPresentationDirectedMapX w hfin).src q else
        (uiqbotPresentationDirectedMapX w hfin).tgt q) = _
    rfl
  have hhead (q : P.GeometricEdge) :
      (uiqbotPresentationDirectedMapX w hfin).head q =
        (if !q.out.2 then kmswLimitDartVertex w (q.out.1, !q.out.2)
          else kmswLimitDartVertex w q.out) := by
    change (if (uiqbotPresentationDirectedMapX w hfin).forward q then
      (uiqbotPresentationDirectedMapX w hfin).tgt q else
        (uiqbotPresentationDirectedMapX w hfin).src q) = _
    rfl
  rw [htail, hhead, kmswGeometricEdgeEquiv_apply]
  obtain hout | hout := P.geometricEdge_out_mk (e, false)
  · rw [hout]
    simp [kmswLimitDartVertex, edgeWest, edgeEast]
  · rw [hout]
    simp [kmswLimitDartVertex, edgeWest, edgeEast]

/-- Helper toward Definition 3.2: an external border in the KMSW drawing
gives the corresponding directed left or right winding-side predicate on the
general `toPlaneGraphDrawing` carrier of the exposed `X` map. -/
private theorem uiqbotPresentationX_side
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (U : (uiqbotPresentationDrawing w hfin).Face)
    (e : ℕ) (b : Bool)
    (hb : (uiqbotPresentationDrawing w hfin).dartBorders (e, b) U) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let q := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e
    let F : (Drawing M).Face :=
      (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawingFaceEquiv.symm U
    if b then RightOf M F ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩
      else LeftOf M F ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ := by
  let P := uiqbotPresentationDrawing w hfin
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let q := kmswGeometricEdgeEquiv w hfin P e
  let F : (Drawing M).Face := P.toPlaneGraphDrawingFaceEquiv.symm U
  have hout : q.out = (e, false) ∨ q.out = (e, true) := by
    dsimp only [q]
    rw [kmswGeometricEdgeEquiv_apply]
    exact P.geometricEdge_out_mk (e, false)
  have hf : M.forward ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ = !q.out.2 := by
    change (uiqbotPresentationDirectedMapX w hfin).forward q = _
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
        rw [hf, hout]
        rfl
      rw [ite_eq_left hforward] at hc
      exact (leftAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        (hleft (by simpa only [hout] using hb) s)
    · have hforward : M.forward ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ ≠ true := by
        rw [hf, hout]
        exact Bool.false_ne_true
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
        rw [hf, hout]
        rfl
      rw [ite_eq_left hforward] at hc
      exact (rightAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        (hright (by simpa only [hout, Bool.not_false] using hb) s)
    · have hforward : M.forward ⟨q, by simp [M, uiqbotMapWithNoMissing]⟩ ≠ true := by
        rw [hf, hout]
        exact Bool.false_ne_true
      rw [ite_eq_right hforward] at hc
      exact (rightAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        ((forall_rightAtOn_symm_iff F.val ((Drawing M).arc q)).mpr
          (hleft (by simpa only [hout] using hb)) s)

/-- Helper toward Definition 3.2: the transported quotient drawing's
unbounded face is the same subset of the plane as the KMSW external face.
The retained image equality makes this identification explicit for transfer
to the map's `toPlaneGraphDrawing`. -/
theorem uiqbotCanonicalQuotientDrawing_externalFace_transport
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    ∃ (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)
        ℕ (fun d => (d.1, !d.2))
        (uiqbotTransportRotation e.symm (kmswInfRot w hfin))
        (boundaryDartInitial
          (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))))
      (U : G.Face) (U₀ : (uiqbotPresentationDrawing w hfin).Face),
      G.IsUnbounded U ∧ U.val = U₀.val ∧
        (∀ d, G.dartBorders d U ↔
          limitExternalDart w (e.symm d)) ∧
        (∀ d, (uiqbotPresentationDrawing w hfin).dartBorders d U₀ ↔
          limitExternalDart w d) := by
  dsimp only
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  let P := uiqbotPresentationDrawing w hfin
  let G₀ : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w) := P
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  obtain ⟨U₀, hUnbounded₀, _hUnique₀, hBorder₀, _hSucc₀⟩ :=
    uiqbotKMSWPresentation_geometricExternalFaceSucc
      w hfin htrans hR hL0
  have hflip (d : ℕ × Bool) : ((e d).1, !(e d).2) =
      e (d.1, !d.2) := by
    exact (uiqbotCanonicalBoundaryDartEquiv_flip w hfin d).symm
  have hrotation (d : ℕ × Bool) : rot (e d) =
      e (kmswInfRot w hfin d) :=
    uiqbotCanonicalBoundaryDartEquiv_rotation w hfin d
  obtain ⟨G, himage, hface⟩ := plDrawing_transport
    (D := ℕ × Bool)
    (D' := P.GeometricEdge × Bool)
    (V := ℕ)
    (flip := fun d : ℕ × Bool => (d.1, !d.2))
    (rot := kmswInfRot w hfin) (vert := kmswLimitDartVertex w)
    (flip' := fun d : P.GeometricEdge × Bool => (d.1, !d.2))
    (rot' := rot) (vert' := boundaryDartInitial M)
    e hflip hrotation
    (uiqbotCanonicalBoundaryDartEquiv_initialVertex w hfin) G₀
  obtain ⟨U, hUval, hBorders⟩ := hface U₀
  have hUnbounded : G.IsUnbounded U := by
    intro R
    obtain ⟨z, hz, hr⟩ := hUnbounded₀ R
    exact ⟨z, hUval ▸ hz, hr⟩
  have hBorder (d : P.GeometricEdge × Bool) :
      G.dartBorders d U ↔ limitExternalDart w (e.symm d) := by
    simpa only [Equiv.apply_symm_apply] using
      (hBorders (e.symm d)).trans (hBorder₀ (e.symm d))
  exact ⟨G, U, U₀, hUnbounded, hUval, hBorder, hBorder₀⟩

/-- Helper toward Definition 3.2: external darts of the transported
UIQBOT drawing satisfy the left winding-side test along every open parameter;
the reversed border darts satisfy the right test. -/
theorem uiqbotCanonicalQuotientDrawing_externalFace_sideTests
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ∃ (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)
        ℕ (fun d => (d.1, !d.2))
        (uiqbotTransportRotation e.symm (kmswInfRot w hfin))
        (boundaryDartInitial M)) (U : G.Face),
      G.IsUnbounded U ∧
        (∀ d, limitExternalDart w (e.symm d) →
          ∀ s : {t : I // t ∈ openParams},
            LeftAtOn U.val (G.arc d).toPath s) ∧
        (∀ d, limitExternalDart w (e.symm (d.1, !d.2)) →
          ∀ s : {t : I // t ∈ openParams},
            RightAtOn U.val (G.arc d).toPath s) := by
  dsimp only
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  obtain ⟨G, U, _U₀, hUnbounded, _hUval, hBorder, _hBorder₀⟩ :=
    uiqbotCanonicalQuotientDrawing_externalFace_transport w hfin htrans hR hL0
  refine ⟨G, U, hUnbounded, ?_, ?_⟩
  · intro d hd s
    exact G.dartBorders_toPath_leftAtOn
      (uiqbotCanonicalQuotientDrawing_vert_surjective w hfin) d U
      ((hBorder d).2 hd) s
  · intro d hd s
    exact G.dartBorders_flip_toPath_rightAtOn
      (uiqbotCanonicalQuotientDrawing_vert_surjective w hfin) d U
      ((hBorder (d.1, !d.2)).2 hd) s

/-- Helper toward Definition 3.2: the canonical labeled `X` presentation
satisfies the upper-left present-side predicate with its exact source binders. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_ULOkInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    ULOkInf (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) := by
  rw [ULOkInf_iff]
  constructor
  · intro i
    refine ⟨by simp [uiqbotMapWithNoMissing], rfl, ?_⟩
    let P := uiqbotPresentationDrawing w hfin
    obtain ⟨G, U, U₀, hUnbounded, hUval, _hBorders, hBorder₀⟩ :=
      uiqbotCanonicalQuotientDrawing_externalFace_transport
        w hfin htrans hR hL0
    have hU₀ : P.IsUnbounded U₀ := by
      intro R
      obtain ⟨z, hz, hr⟩ := hUnbounded R
      exact ⟨z, hUval ▸ hz, hr⟩
    let F := P.toPlaneGraphDrawingFaceEquiv.symm U₀
    refine ⟨F, ?_, ?_⟩
    · exact (P.toPlaneGraphDrawing_isExternal_iff F).mpr
        (by simpa only [F, Equiv.apply_symm_apply] using hU₀)
    · exact uiqbotPresentationX_side w hfin U₀ (kmswLeftBoundaryEdge w i) false
        ((hBorder₀ _).mpr ((limitExternalDart_iff w htrans hR hL0 _).mpr
          (Or.inl ⟨i, rfl⟩)))
  · exact (uiqbotDefinition32Presentation_joinClauses w htrans hR hL0
      (uiqbotPresentationDirectedMapX w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))
      (uiqbotPresentationX_compatibility w hfin)).1

/-- Helper toward Definition 3.2: the canonical labeled `X` presentation
satisfies the lower-right present-side predicate with its exact source binders. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_LROkInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    LROkInf (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) := by
  rw [LROkInf_iff]
  constructor
  · intro i
    refine ⟨by simp [uiqbotMapWithNoMissing], ?_, ?_⟩
    · rfl
    · let P := uiqbotPresentationDrawing w hfin
      obtain ⟨G, U, U₀, hUnbounded, hUval, _hBorders, hBorder₀⟩ :=
        uiqbotCanonicalQuotientDrawing_externalFace_transport
          w hfin htrans hR hL0
      have hU₀ : P.IsUnbounded U₀ := by
        intro R
        obtain ⟨z, hz, hr⟩ := hUnbounded R
        exact ⟨z, hUval ▸ hz, hr⟩
      let F := P.toPlaneGraphDrawingFaceEquiv.symm U₀
      refine ⟨F, ?_, ?_⟩
      · exact (P.toPlaneGraphDrawing_isExternal_iff F).mpr
          (by simpa only [F, Equiv.apply_symm_apply] using hU₀)
      · exact uiqbotPresentationX_side w hfin U₀ (kmswRightBoundaryEdge w i) true
          ((hBorder₀ _).mpr ((limitExternalDart_iff w htrans hR hL0 _).mpr
            (Or.inr ⟨i, rfl⟩)))
  · exact (uiqbotDefinition32Presentation_joinClauses w htrans hR hL0
      (uiqbotPresentationDirectedMapX w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))
      (uiqbotPresentationX_compatibility w hfin)).2

end DirectedDistances.PaperProofs.Section4
end
