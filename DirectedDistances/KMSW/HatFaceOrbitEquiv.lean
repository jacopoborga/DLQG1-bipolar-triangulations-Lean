/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.HatDeletedGeometryVertical
public import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsFull

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! # Hatted face orbits and realized faces

Supporting results for the unprimed half of Lemma 5.13 (`lem-quad-kmsw`).
The finite creation orbits and the single exterior orbit are identified with
actual complementary components of the reachable restricted drawing. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology



@[expose] def hatFaceSetoid (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) : Setoid (ℕ × Bool) where
  r := (kmswInfFaceSucc (hatCodes w h) (hatCodes_finiteIncidence w h hfin)).SameCycle
  iseqv := ⟨Equiv.Perm.SameCycle.refl _, Equiv.Perm.SameCycle.symm,
    Equiv.Perm.SameCycle.trans⟩



@[expose] def HatFaceOrbit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) := Quotient (hatFaceSetoid w h hfin)



private theorem hat_border_face_unique {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F G : P.Face) (d : D) (hF : P.dartBorders d F) (hG : P.dartBorders d G) :
    F = G := by
  obtain ⟨a, ha, hF⟩ := hF
  obtain ⟨b, hb, hG⟩ := hG
  let t := min a b / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t < a := by
    have := min_le_left a b
    dsimp [t]
    linarith
  have htb : t < b := by
    have := min_le_right a b
    dsimp [t]
    linarith
  exact P.faces_eq_of_mem (hF t t ht hta ht hta) (hG t t ht htb ht htb)



private theorem hat_creation_east_eq_iff (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    edgeEast w (stageTriangleRecord w j).1 =
      edgeEast w (stageTriangleRecord w j).2.1 ↔ w j.val = 0 := by
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  have hb := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
  rw [← (edge_endpoints_eq w hb.1).2, ← (edge_endpoints_eq w hb.2.1).2]
  have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
  have hne := ne_of_lt ha
  have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by
    omega
  have hv := (kmswStage_endpoints_lt_nextVertex w j.val _ ha).2
  rcases j.property with h0 | h1
  · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, h0, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, hp, State.addEdge, hne, hne']
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, h1, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge, hne, hne', ne_of_lt hv]



private theorem hat_creation_oriented_mem (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (d : ℕ × Bool) :
    d ∈ triangleOrientedDarts w (stageTriangleRecord w j) ↔
      d ∈ stageTriangleDartList w j := by
  have he := hat_creation_east_eq_iff w j
  rcases j.property with h0 | h1
  · have hh := he.mpr h0
    unfold triangleOrientedDarts
    rw [ite_eq_left hh]
    cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp only [stageTriangleDartList, stageTriangleDartTriple,
        stageTriangleRecord, h0, ↓reduceIte, hp,
        List.mem_cons, List.not_mem_nil, or_false]
    all_goals tauto
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    have hh := mt he.mp h0
    unfold triangleOrientedDarts
    rw [ite_eq_right hh]
    simp only [stageTriangleDartList, stageTriangleDartTriple,
      stageTriangleRecord, h0, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false]




theorem hatFiniteFaceOrbit_border_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc (hatCodes w h)
      (hatCodes_finiteIncidence w h hfin)).SameCycle d e}.Finite) :
    ∃ G : PlaneFaces (hatRealizedDrawing w hfin), ∀ e,
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h e) G.val ↔
        (kmswInfFaceSucc (hatCodes w h)
          (hatCodes_finiteIncidence w h hfin)).SameCycle d e := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  let H := hatLimitDartEquiv w h
  let u := hatCodes w h
  obtain ⟨j, k, i, F, G, horbit, _, hk, _, hi, hF, hG, hb⟩ :=
    hatFiniteFaceOrbit_realized w h hfin d hfinite
  refine ⟨G, fun e => ⟨?_, hb e⟩⟩
  intro he
  have heF : P.dartBorders (H e).val F.val :=
    dartBorders_transport Q P G.val F.val (H e) (H e).val hG.symm rfl he
  let i' := (stageTriangleRecord_fin_index w k).choose
  have hi' := (stageTriangleRecord_fin_index w k).choose_spec
  have hcaps := monotone_cap_region_eq w
    (familyG w (monotone_family_all w) (k.val + 1))
    (familyG w (monotone_family_all w) (k.val + 1)) i i'
    (hi.trans hi'.symm) (fun _ _ => rfl)
  have hFcap : F.val = capFace w hfin k :=
    Subtype.ext (hF.trans (hcaps.trans (capFace_spec w hfin k).1.symm))
  have hmem : (H e).val ∈ triangleOrientedDarts w (stageTriangleRecord w k) :=
    (hat_creation_oriented_mem w k _).mpr
      ((cap_border_iff w hfin k _).mp (hFcap ▸ heF))
  obtain ⟨i0, hi0⟩ := stageTriangleRecord_fin_index u j
  let t : HatLocalTri w h := ⟨stageTriangleRecord u j, j.val + 1,
    hi0 ▸ List.get_mem _ i0⟩
  have hmap := hatLimit_triangleOrientedDarts w h t
  change (triangleOrientedDarts u (stageTriangleRecord u j)).map
      (fun a => (H a).val) = triangleOrientedDarts w
        (hatLimitEdgeMap w h (stageTriangleRecord u j).1,
          hatLimitEdgeMap w h (stageTriangleRecord u j).2.1,
          hatLimitEdgeMap w h (stageTriangleRecord u j).2.2) at hmap
  rw [← hk] at hmap
  rw [← hmap] at hmem
  obtain ⟨a, ha, hae⟩ := List.mem_map.mp hmem
  have hae' : a = e := H.injective (Subtype.ext hae)
  rw [hae'] at ha
  exact (horbit e).mpr ((hat_creation_oriented_mem u j e).mp ha)




theorem hatFaceOrbit_iff_common_face (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w)
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop)
    (d e : ℕ × Bool) :
    (kmswInfFaceSucc (hatCodes w h)
      (hatCodes_finiteIncidence w h hfin)).SameCycle d e ↔
      ∃ F : (hatRealizedDrawing w hfin).Face,
        (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F ∧
        (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h e) F := by
  classical
  let Q := hatRealizedDrawing w hfin
  let H := hatLimitDartEquiv w h
  let f := kmswInfFaceSucc (hatCodes w h) (hatCodes_finiteIncidence w h hfin)
  by_cases hfinite : {a | f.SameCycle d a}.Finite
  · obtain ⟨G, hG⟩ := hatFiniteFaceOrbit_border_iff w h hfin d hfinite
    have hdG := (hG d).mpr (Equiv.Perm.SameCycle.refl f d)
    constructor
    · intro hde
      exact ⟨G.val, hdG, (hG e).mpr hde⟩
    · rintro ⟨F, hdF, heF⟩
      have hFG := hat_border_face_unique Q F G.val (H d) hdF hdG
      exact (hG e).mp (hFG ▸ heF)
  · have hdext : limitExternalDart (hatCodes w h) d := by
      by_contra hd
      exact hfinite ((finiteFaceOrbit_iff_not_external _ _ d).mpr hd)
    obtain ⟨U, _, _, hb, ho⟩ := hatUnboundedFaceIdentificationGoal_holds w h hfin htrans
    have hdU := (hb d).mpr hdext
    have hrootd := (ho d).mp hdext
    constructor
    · intro hde
      exact ⟨U, hdU, (hb e).mpr ((ho e).mpr (hrootd.trans hde))⟩
    · rintro ⟨F, hdF, heF⟩
      have hFU := hat_border_face_unique Q F U (H d) hdF hdU
      exact hrootd.symm.trans ((ho e).mp ((hb e).mp (hFU ▸ heF)))



theorem hatDart_borders_unique (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w)
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop)
    (d : ℕ × Bool) :
    ∃! F : (hatRealizedDrawing w hfin).Face,
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F := by
  obtain ⟨F, hdF, _⟩ := (hatFaceOrbit_iff_common_face w h hfin htrans d d).mp
    (Equiv.Perm.SameCycle.refl _ _)
  exact ⟨F, hdF, fun G hdG =>
    hat_border_face_unique _ G F (hatLimitDartEquiv w h d) hdG hdF⟩




theorem hatRealizedFace_bordered (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w)
    (F : (hatRealizedDrawing w hfin).Face) :
    ∃ d : ℕ × Bool,
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F := by
  classical
  let Q := hatRealizedDrawing w hfin
  by_cases hF : Q.IsUnbounded F
  · obtain ⟨U, _, huniq, hroot⟩ := hatRealizedFaces_unbounded_unique w h hfin
    exact ⟨futureMapOuterDart, (huniq F hF).symm ▸ hroot⟩
  · change ¬ ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖ at hF
    push Not at hF
    obtain ⟨R, hR⟩ := hF
    have hbounded : Bornology.IsBounded F.val := by
      apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
      exact ⟨R, fun z hz => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hR z hz⟩
    obtain ⟨d, hd, _⟩ := hatBoundedFaceFiniteBorderGoal_of_flowLineHits
      w h hfin ⟨F, hbounded⟩
    exact ⟨d, hd⟩

variable (w : ℕ → Fin 3) (h : HasFlowLineHits w)
  (hfin : hatLimitFiniteIncidence w)
  (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop)



@[expose] noncomputable def hatDartFace (d : ℕ × Bool) :
    (hatRealizedDrawing w hfin).Face :=
  (hatDart_borders_unique w h hfin htrans d).exists.choose



theorem hatDartFace_eq_iff (d : ℕ × Bool) (F : (hatRealizedDrawing w hfin).Face) :
    hatDartFace w h hfin htrans d = F ↔
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F := by
  have hd : (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d)
      (hatDartFace w h hfin htrans d) :=
    (hatDart_borders_unique w h hfin htrans d).exists.choose_spec
  exact ⟨fun he => he ▸ hd, fun hF =>
    hat_border_face_unique _ _ F (hatLimitDartEquiv w h d) hd hF⟩



theorem hatDartFace_eq_of_sameCycle (d e : ℕ × Bool)
    (hde : (kmswInfFaceSucc (hatCodes w h)
      (hatCodes_finiteIncidence w h hfin)).SameCycle d e) :
    hatDartFace w h hfin htrans d = hatDartFace w h hfin htrans e := by
  obtain ⟨F, hd, he⟩ := (hatFaceOrbit_iff_common_face w h hfin htrans d e).mp hde
  exact ((hatDartFace_eq_iff w h hfin htrans d F).mpr hd).trans
    ((hatDartFace_eq_iff w h hfin htrans e F).mpr he).symm



@[expose] noncomputable def hatOrbitFace :
    HatFaceOrbit w h hfin → (hatRealizedDrawing w hfin).Face :=
  Quotient.lift (hatDartFace w h hfin htrans)
    (hatDartFace_eq_of_sameCycle w h hfin htrans)



theorem hatOrbitFace_bijective : Function.Bijective (hatOrbitFace w h hfin htrans) := by
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro d e heq
    apply Quotient.sound
    apply (hatFaceOrbit_iff_common_face w h hfin htrans d e).mpr
    refine ⟨hatDartFace w h hfin htrans d,
      (hatDartFace_eq_iff w h hfin htrans d _).mp rfl, ?_⟩
    exact (hatDartFace_eq_iff w h hfin htrans e _).mp heq.symm
  · intro F
    obtain ⟨d, hd⟩ := hatRealizedFace_bordered w h hfin F
    exact ⟨Quotient.mk _ d, (hatDartFace_eq_iff w h hfin htrans d F).mpr hd⟩



@[expose] noncomputable def hatFaceOrbitEquiv :
    HatFaceOrbit w h hfin ≃ (hatRealizedDrawing w hfin).Face :=
  Equiv.ofBijective (hatOrbitFace w h hfin htrans)
    (hatOrbitFace_bijective w h hfin htrans)



theorem hatFaceOrbitEquiv_eq_iff (d : ℕ × Bool)
    (F : (hatRealizedDrawing w hfin).Face) :
    hatFaceOrbitEquiv w h hfin htrans (Quotient.mk _ d) = F ↔
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F :=
  hatDartFace_eq_iff w h hfin htrans d F



theorem dartBorders_hatFaceOrbitEquiv_iff (d : ℕ × Bool) (q : HatFaceOrbit w h hfin) :
    (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d)
      (hatFaceOrbitEquiv w h hfin htrans q) ↔ Quotient.mk _ d = q := by
  rw [← hatFaceOrbitEquiv_eq_iff]
  exact (hatFaceOrbitEquiv w h hfin htrans).injective.eq_iff



theorem hatRealizedFace_unique_orbit
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop) (F : (hatRealizedDrawing w hfin).Face) :
    ∃! q : HatFaceOrbit w h hfin, ∀ d,
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F ↔
        Quotient.mk _ d = q := by
  let E := hatFaceOrbitEquiv w h hfin htrans
  have hc (d : ℕ × Bool) :
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F ↔
        Quotient.mk _ d = E.symm F := by
    simpa only [E, Equiv.apply_symm_apply] using
      dartBorders_hatFaceOrbitEquiv_iff w h hfin htrans d (E.symm F)
  refine ⟨E.symm F, hc, ?_⟩
  intro q hq
  obtain ⟨d, hd⟩ := hatRealizedFace_bordered w h hfin F
  exact ((hq d).mp hd).symm.trans ((hc d).mp hd)



theorem hatFaceOrbit_unique_face
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop) (q : HatFaceOrbit w h hfin) :
    ∃! F : (hatRealizedDrawing w hfin).Face, ∀ d,
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F ↔
        Quotient.mk _ d = q := by
  refine Quotient.inductionOn q ?_
  intro d
  refine ⟨hatFaceOrbitEquiv w h hfin htrans (Quotient.mk _ d),
    fun e => dartBorders_hatFaceOrbitEquiv_iff w h hfin htrans e _, ?_⟩
  intro G hG
  exact hat_border_face_unique _ G _ (hatLimitDartEquiv w h d)
    ((hG d).mpr rfl)
    ((dartBorders_hatFaceOrbitEquiv_iff w h hfin htrans d _).mpr rfl)



theorem hatFaceOrbitEquiv_isUnbounded_iff (q : HatFaceOrbit w h hfin) :
    (hatRealizedDrawing w hfin).IsUnbounded (hatFaceOrbitEquiv w h hfin htrans q) ↔
      q = Quotient.mk _ futureMapOuterDart := by
  obtain ⟨U, hU, huniq, hb, ho⟩ := hatUnboundedFaceIdentificationGoal_holds w h hfin htrans
  have hr : hatFaceOrbitEquiv w h hfin htrans (Quotient.mk _ futureMapOuterDart) = U :=
    (hatFaceOrbitEquiv_eq_iff w h hfin htrans _ U).mpr
      ((hb _).mpr ((ho _).mpr (Equiv.Perm.SameCycle.refl _ _)))
  constructor
  · intro hq
    exact (hatFaceOrbitEquiv w h hfin htrans).injective ((huniq _ hq).trans hr.symm)
  · intro hq
    rw [hq, hr]
    exact hU



theorem hatFaceOrbitEquiv_exterior_border (d : ℕ × Bool) :
    (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d)
      (hatFaceOrbitEquiv w h hfin htrans (Quotient.mk _ futureMapOuterDart)) ↔
      limitExternalDart (hatCodes w h) d := by
  obtain ⟨U, _, _, hb, ho⟩ := hatUnboundedFaceIdentificationGoal_holds w h hfin htrans
  have hr : hatFaceOrbitEquiv w h hfin htrans (Quotient.mk _ futureMapOuterDart) = U :=
    (hatFaceOrbitEquiv_eq_iff w h hfin htrans _ U).mpr
      ((hb _).mpr ((ho _).mpr (Equiv.Perm.SameCycle.refl _ _)))
  rw [hr]
  exact hb d






theorem hatRootedMapIdentification
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := hatRealizedDrawing w hfin
    let S := {d : ℕ × Bool | MhatGeometricEdge w d.1}
    ∃ (H : (ℕ × Bool) ≃ {d : ℕ × Bool // MhatGeometricEdge w d.1})
      (F : HatFaceOrbit w h hfin ≃ Q.Face),
      (∀ d, (H d).val = (hatLimitEdgeMap w h d.1, d.2)) ∧
      (H futureMapRootDart).val = futureMapRootDart ∧
      (∀ d, (H (futureMapEdgeInv d)).val = futureMapEdgeInv (H d).val) ∧
      (∀ d, futureMapMissing (hatCodes w h) d ↔ futureMapMissing w (H d).val) ∧
      (∀ d, futureMapTail (hatCodes w h) d ↔ futureMapTail w (H d).val) ∧
      (∀ e, edgeWest w (hatLimitEdgeMap w h e) =
          hatLimitVertexMap w h (edgeWest (hatCodes w h) e) ∧
        edgeEast w (hatLimitEdgeMap w h e) =
          hatLimitVertexMap w h (edgeEast (hatCodes w h) e)) ∧
      (∀ d, H (kmswInfRot (hatCodes w h) (hatCodes_finiteIncidence w h hfin) d) =
        drawingFirstReturnPerm P S (H d)) ∧
      (∀ d, H (kmswInfFaceSucc (hatCodes w h) (hatCodes_finiteIncidence w h hfin) d) =
        (drawingFirstReturnPerm P S).symm (restrictedFlip P S (fun _ => Iff.rfl) (H d))) ∧
      (∀ d q, Q.dartBorders (H d) (F q) ↔ Quotient.mk _ d = q) ∧
      (∀ q, Q.IsUnbounded (F q) ↔ q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, Q.dartBorders (H d) (F (Quotient.mk _ futureMapOuterDart)) ↔
        limitExternalDart (hatCodes w h) d) := by
  refine ⟨hatLimitDartEquiv w h, hatFaceOrbitEquiv w h hfin htrans,
    hatLimitDartEquiv_apply w h, hatLimitDartMap_root w h,
    hatLimitDartMap_edgeInv w h, hatLimitDartMap_missing w h,
    hatLimitDartMap_tail w h, ?_, hatLimitDartEquiv_rotation w h hfin,
    hatLimitDartEquiv_faceSuccessor w h hfin,
    dartBorders_hatFaceOrbitEquiv_iff w h hfin htrans,
    hatFaceOrbitEquiv_isUnbounded_iff w h hfin htrans,
    hatFaceOrbitEquiv_exterior_border w h hfin htrans⟩
  intro e
  exact hatExplicitEdgeEquiv_incidence w h ⟨e, hatCodes_edge_present w h e⟩






theorem iidCodes_ae_hatRootedMapIdentification :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w),
        (hatDeletedGeometryPathToAmbientExteriorGoal w hfin ∧
          hatDeletedGeometryRootFaceConnectivityGoal w h hfin ∧
          hatBoundedFaceDeletedGeometryExclusionGoal w hfin ∧
          hatUnboundedFaceResidualGoal w h hfin ∧
          hatUnboundedFaceIdentificationGoal w h hfin ∧
          hatBoundedFaceFiniteBorderGoal w h hfin) ∧
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        let Q := hatRealizedDrawing w hfin
        let S := {d : ℕ × Bool | MhatGeometricEdge w d.1}
        ∃ (H : (ℕ × Bool) ≃ {d : ℕ × Bool // MhatGeometricEdge w d.1})
          (F : HatFaceOrbit w h hfin ≃ Q.Face),
          (∀ d, (H d).val = (hatLimitEdgeMap w h d.1, d.2)) ∧
          (H futureMapRootDart).val = futureMapRootDart ∧
          (∀ d, (H (futureMapEdgeInv d)).val = futureMapEdgeInv (H d).val) ∧
          (∀ d, futureMapMissing (hatCodes w h) d ↔ futureMapMissing w (H d).val) ∧
          (∀ d, futureMapTail (hatCodes w h) d ↔ futureMapTail w (H d).val) ∧
          (∀ e, edgeWest w (hatLimitEdgeMap w h e) =
              hatLimitVertexMap w h (edgeWest (hatCodes w h) e) ∧
            edgeEast w (hatLimitEdgeMap w h e) =
              hatLimitVertexMap w h (edgeEast (hatCodes w h) e)) ∧
          (∀ d, H (kmswInfRot (hatCodes w h) (hatCodes_finiteIncidence w h hfin) d) =
            drawingFirstReturnPerm P S (H d)) ∧
          (∀ d, H (kmswInfFaceSucc (hatCodes w h) (hatCodes_finiteIncidence w h hfin) d) =
            (drawingFirstReturnPerm P S).symm (restrictedFlip P S (fun _ => Iff.rfl) (H d))) ∧
          (∀ d q, Q.dartBorders (H d) (F q) ↔ Quotient.mk _ d = q) ∧
          (∀ q, Q.IsUnbounded (F q) ↔ q = Quotient.mk _ futureMapOuterDart) ∧
          (∀ d, Q.dartBorders (H d) (F (Quotient.mk _ futureMapOuterDart)) ↔
            limitExternalDart (hatCodes w h) d) := by
  filter_upwards [iidCodes_ae_hatDeletedGeometry_faceGoals,
    iidCodes_ae_hatCodes_left_transient] with ω hgoals htrans
  obtain ⟨h, hfin, hgoals⟩ := hgoals
  exact ⟨h, hfin, hgoals, hatRootedMapIdentification _ h hfin (htrans h)⟩

end DirectedDistances.KMSW
