/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation6
public import DirectedDistances.PlanarMap.PLDrawingWindingSides18
import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport
import DirectedDistances.PlanarMap.Definition32OrientedSideTransport2

/-! # Repeated boundary incidences -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

/-- Helper toward Definition 3.2: an injective path parametrizes its range
homeomorphically. -/
def injectivePathRangeHomeomorph {x y : ℂ} (γ : Path x y)
    (hγ : Function.Injective γ) : I ≃ₜ Set.range γ := by
  let f : I → Set.range γ := fun t => ⟨γ t, Set.mem_range_self t⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      exact hγ (congrArg Subtype.val h)
    · rintro ⟨z, t, rfl⟩
      exact ⟨t, rfl⟩
  exact (Equiv.ofBijective f hf).toHomeomorphOfContinuousClosed
    (γ.continuous.subtype_mk _) (γ.continuous.subtype_mk _).isClosedMap

/-- Helper toward Definition 3.2: simple paths with the same endpoints
and range differ by an endpoint-fixing interval homeomorphism. -/
theorem exists_reparam_of_injective_range_eq {x y : ℂ} (γ δ : Path x y)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hrange : Set.range γ = Set.range δ) :
    ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧ ∀ t, γ (φ t) = δ t := by
  let G := injectivePathRangeHomeomorph γ hγ
  let H := injectivePathRangeHomeomorph δ hδ
  let φ := H.trans ((Homeomorph.setCongr hrange.symm).trans G.symm)
  have heq (t : I) : γ (φ t) = δ t := by
    have h := G.apply_symm_apply ((Homeomorph.setCongr hrange.symm) (H t))
    exact congrArg Subtype.val h
  refine ⟨φ, ?_, ?_, heq⟩
  · apply hγ
    simpa only [Path.source] using heq 0
  · apply hγ
    simpa only [Path.target] using heq 1

/-- Helper toward Definition 3.2: simultaneous left-side tests depend only
on the oriented simple arc, independently of its speed. -/
theorem forall_leftAtOn_of_injective_range_eq {x y : ℂ} (F : Set ℂ)
    (γ δ : Path x y) (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hrange : Set.range γ = Set.range δ) :
    (∀ s, LeftAtOn F γ s) ↔ ∀ s, LeftAtOn F δ s := by
  obtain ⟨φ, h0, h1, heq⟩ := exists_reparam_of_injective_range_eq γ δ hγ hδ hrange
  have hc (s : {t : I // t ∈ openParams}) :
      LeftAtOn F (γ.reparam φ φ.continuous h0 h1) s ↔ LeftAtOn F δ s :=
    leftAtOn_congr_fun F _ δ s heq
  exact (forall_leftAtOn_reparam_iff F γ φ h0 h1).symm.trans
    (forall_congr' hc)

namespace PLDrawing

/-- Helper toward Definition 3.2: reversing the dart gives right-side
tests on the original arc, with its actual recursive parameter schedule. -/
theorem dartBorders_flip_toPath_rightAtOn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders (flip d) F)
    (s : {t : I // t ∈ openParams}) :
    RightAtOn F.val (P.arc d).toPath s := by
  have hx : (P.arc (flip d)).finish = (P.arc d).start := by
    rw [P.arc_finish, P.flip_involutive, P.arc_start]
  have hy : (P.arc (flip d)).start = (P.arc d).finish := by
    rw [P.arc_start, P.arc_finish]
  let δ := (P.arc (flip d)).toPath.cast hy.symm hx.symm
  have hδ : Function.Injective δ :=
    (P.arc (flip d)).toPath_injective (P.arc_length _) (P.arc_simple _)
  have hγ : Function.Injective (P.arc d).toPath.symm := by
    exact ((P.arc d).toPath_injective (P.arc_length _) (P.arc_simple _)).comp
      unitInterval.symmHomeomorph.injective
  have hr : Set.range δ = Set.range (P.arc d).toPath.symm := by
    change Set.range (P.arc (flip d)).toPath = _
    rw [Path.symm_range, Polyline.range_toPath, Polyline.range_toPath, P.arc_image_flip]
  have hleft : ∀ t, LeftAtOn F.val δ t := by
    intro t
    exact (leftAtOn_cast_iff F.val _ hy.symm hx.symm t).mpr
      (P.dartBorders_toPath_leftAtOn hvert (flip d) F hborder t)
  have hs : ∀ t, LeftAtOn F.val (P.arc d).toPath.symm t :=
    (forall_leftAtOn_of_injective_range_eq F.val δ _ hδ hγ hr).mp hleft
  exact (forall_leftAtOn_symm_iff F.val (P.arc d).toPath).mp hs s

end PLDrawing

end DirectedDistances.PlanarMap

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Definition 3.2: a repeated boundary edge occurs in each
of the two present boundary streams. -/
theorem uiqbotCanonicalBoundaryPresentation_repeatedEdge_bothStreams
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : (uiqbotPresentationDrawing w hfin).GeometricEdge)
    (i j : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0))
    (hne : i ≠ j)
    (hi : (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e)
    (hj : (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j).1 = e) :
    ∃ n m,
      kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
        (kmswLeftBoundaryEdge w n) = e ∧
      kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
        (kmswRightBoundaryEdge w m) = e := by
  revert hne hi hj
  revert i j
  rw [uiqbotCanonicalBoundaryPresentation_eq]
  intro i j hne hi hj
  let B := uiqbotDefinition32Presentation w htrans hR hL0
    (uiqbotPresentationDirectedMap w hfin)
    (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))
  let iota := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
  have hUR : ∀ x : B.upperRight.Index, False := by
    intro x
    dsimp [B, uiqbotDefinition32Presentation] at x
    exact isEmptyElim x
  have hLL : ∀ x : B.lowerLeft.Index, False := by
    intro x
    dsimp [B, uiqbotDefinition32Presentation] at x
    exact isEmptyElim x
  have hleftInj := (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).1
  have hrightInj := (kmswRightBoundary_infinite_present_path w hL0 hR).1
  cases i with
  | upperLeft n =>
    cases j with
    | upperLeft m =>
      rw [InfiniteBoundaryDartIndex.dart_eq] at hi hj
      change iota (kmswLeftBoundaryEdge w n) = e at hi
      change iota (kmswLeftBoundaryEdge w m) = e at hj
      exact (hne (congrArg InfiniteBoundaryDartIndex.upperLeft
        (hleftInj (iota.injective (hi.trans hj.symm))))).elim
    | lowerRight m =>
      rw [InfiniteBoundaryDartIndex.dart_eq] at hi hj
      exact ⟨n, m, hi, hj⟩
    | upperRight m => exact (hUR m).elim
    | lowerLeft m => exact (hLL m).elim
  | lowerRight m =>
    cases j with
    | upperLeft n =>
      rw [InfiniteBoundaryDartIndex.dart_eq] at hi hj
      exact ⟨n, m, hj, hi⟩
    | lowerRight n =>
      rw [InfiniteBoundaryDartIndex.dart_eq] at hi hj
      change iota (kmswRightBoundaryEdge w m) = e at hi
      change iota (kmswRightBoundaryEdge w n) = e at hj
      exact (hne (congrArg InfiniteBoundaryDartIndex.lowerRight
        (hrightInj (iota.injective (hi.trans hj.symm))))).elim
    | upperRight n => exact (hUR n).elim
    | lowerLeft n => exact (hLL n).elim
  | upperRight n => exact (hUR n).elim
  | lowerLeft n => exact (hLL n).elim

/-- Helper toward Definition 3.2: both sides of a repeated stored edge
touch the same external face, before reading the directed orientation. -/
theorem uiqbotCanonicalBoundaryPresentation_repeatedEdge_storedSides
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : (uiqbotPresentationDrawing w hfin).GeometricEdge)
    (i j : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0))
    (hne : i ≠ j)
    (hi : (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e)
    (hj : (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j).1 = e) :
    ∃ F : (Drawing (uiqbotMapWithNoMissing
        (uiqbotPresentationDirectedMap w hfin))).Face,
      (Drawing (uiqbotMapWithNoMissing
        (uiqbotPresentationDirectedMap w hfin))).IsExternal F ∧
      (∀ s, LeftAtOn F.val ((Drawing (uiqbotMapWithNoMissing
        (uiqbotPresentationDirectedMap w hfin))).arc e) s) ∧
      (∀ s, RightAtOn F.val ((Drawing (uiqbotMapWithNoMissing
        (uiqbotPresentationDirectedMap w hfin))).arc e) s) := by
  let P := uiqbotPresentationDrawing w hfin
  obtain ⟨n, m, hl, hr⟩ :=
    uiqbotCanonicalBoundaryPresentation_repeatedEdge_bothStreams
      w hfin htrans hR hL0 e i j hne hi hj
  have hlabels : kmswLeftBoundaryEdge w n = kmswRightBoundaryEdge w m :=
    (kmswGeometricEdgeEquiv w hfin P).injective (hl.trans hr.symm)
  obtain ⟨U, hU, _, hUborder⟩ :=
    monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
  have hfalse : P.dartBorders (kmswLeftBoundaryEdge w n, false) U :=
    (hUborder _).mpr ((limitExternalDart_iff w htrans hR hL0 _).mpr
      (Or.inl ⟨n, rfl⟩))
  have htrue : P.dartBorders (kmswLeftBoundaryEdge w n, true) U := by
    rw [hlabels]
    exact (hUborder _).mpr ((limitExternalDart_iff w htrans hR hL0 _).mpr
      (Or.inr ⟨m, rfl⟩))
  have hout : e.out = (kmswLeftBoundaryEdge w n, false) ∨
      e.out = (kmswLeftBoundaryEdge w n, true) := by
    rw [← hl, kmswGeometricEdgeEquiv_apply]
    exact P.geometricEdge_out_mk (kmswLeftBoundaryEdge w n, false)
  have hd : P.dartBorders e.out U := by
    rcases hout with h | h
    · simpa only [h] using hfalse
    · simpa only [h] using htrue
  have hflip : P.dartBorders (e.out.1, !e.out.2) U := by
    rcases hout with h | h
    · simpa only [h, Bool.not_false] using htrue
    · simpa only [h, Bool.not_true] using hfalse
  let F := P.toPlaneGraphDrawingFaceEquiv.symm U
  have hF : P.toPlaneGraphDrawing.IsExternal F :=
    (P.toPlaneGraphDrawing_isExternal_iff F).mpr
      (by simpa only [F, Equiv.apply_symm_apply] using hU)
  have hleft : ∀ s, LeftAtOn F.val (P.toPlaneGraphDrawing.arc e) s := by
    intro s
    exact (P.toPlaneGraphDrawing_leftAtOn_iff e F s).mpr
      (P.dartBorders_toPath_leftAtOn (kmswLimitDartVertex_surjective w hfin) e.out U hd s)
  have hright : ∀ s, RightAtOn F.val (P.toPlaneGraphDrawing.arc e) s := by
    intro s
    exact (P.toPlaneGraphDrawing_rightAtOn_iff e F s).mpr
      (P.dartBorders_flip_toPath_rightAtOn
        (kmswLimitDartVertex_surjective w hfin) e.out U hflip s)
  have hdrawing : Drawing (uiqbotMapWithNoMissing
      (uiqbotPresentationDirectedMap w hfin)) = P.toPlaneGraphDrawing :=
    (uiqbotMapWithNoMissing_drawing_eq _).trans
      (uiqbotPresentationDirectedMap_toPlaneGraphDrawing w hfin)
  rw [hdrawing]
  exact ⟨F, hF, hleft, hright⟩

/-- Helper toward Definition 3.2: repeated boundary occurrences give both
external winding-side incidences of the present oriented edge. -/
theorem uiqbotCanonicalBoundaryPresentation_repeatedEdgeIncidences
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
    ∃ hp : ¬ (uiqbotMapWithNoMissing
        (uiqbotPresentationDirectedMap w hfin)).toPlaneMapWithMissing.missing e,
      ∃ F G : PlaneGraphDrawing.Face
          (Drawing (uiqbotMapWithNoMissing
            (uiqbotPresentationDirectedMap w hfin))),
        (Drawing (uiqbotMapWithNoMissing
          (uiqbotPresentationDirectedMap w hfin))).IsExternal F ∧
        (Drawing (uiqbotMapWithNoMissing
          (uiqbotPresentationDirectedMap w hfin))).IsExternal G ∧
        LeftOf (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))
          F ⟨e, hp⟩ ∧
        RightOf (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))
          G ⟨e, hp⟩ := by
  intro hne hi hj
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)
  obtain ⟨F, hF, hleft, hright⟩ :=
    uiqbotCanonicalBoundaryPresentation_repeatedEdge_storedSides
      w hfin htrans hR hL0 e i j hne hi hj
  have hp : ¬ M.toPlaneMapWithMissing.missing e := by
    rw [uiqbotMapWithNoMissing_missing_eq]
    exact not_false
  have hL : LeftOf M F ⟨e, hp⟩ := by
    intro s
    change LeftAtOn F.val (orientedArc M ⟨e, hp⟩) s
    have hc := orientedArc_coe M ⟨e, hp⟩
    by_cases hf : M.forward ⟨e, hp⟩ = true
    · rw [ite_eq_left hf] at hc
      exact (leftAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr (hleft s)
    · rw [ite_eq_right hf] at hc
      exact (leftAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        ((forall_leftAtOn_symm_iff F.val ((Drawing M).arc e)).mpr hright s)
  have hRside : RightOf M F ⟨e, hp⟩ := by
    intro s
    change RightAtOn F.val (orientedArc M ⟨e, hp⟩) s
    have hc := orientedArc_coe M ⟨e, hp⟩
    by_cases hf : M.forward ⟨e, hp⟩ = true
    · rw [ite_eq_left hf] at hc
      exact (rightAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr (hright s)
    · rw [ite_eq_right hf] at hc
      exact (rightAtOn_congr_fun F.val _ _ s (congrFun hc)).mpr
        ((forall_rightAtOn_symm_iff F.val ((Drawing M).arc e)).mpr hleft s)
  exact ⟨hp, F, F, hF, hF, hL, hRside⟩

end DirectedDistances.PaperProofs.Section4

end
