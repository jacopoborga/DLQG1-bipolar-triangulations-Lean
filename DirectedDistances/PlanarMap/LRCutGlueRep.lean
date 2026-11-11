module

public import DirectedDistances.PlanarMap.PlanarPathGlueCutLeft
public import DirectedDistances.PlanarMap.PlanarPathGlueSeamGeometric
public import DirectedDistances.PlanarMap.LRGlueRepLen
public import DirectedDistances.PlanarMap.LRCutRepRight
public import DirectedDistances.PlanarMap.PlanarPathCutLeftHalfBaseIso
public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIsoOfRot

import all DirectedDistances.PlanarMap.PlanarPathGlueCutLeft

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PlanarMap
open Classical

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)



noncomputable def glueCutLeftBaseIso
    (hrotL : ∀ d : DL,
      glueCutLeftEquiv BL BR (BL.map.toCombinatorialMap.rot d) =
        (pathCutLeftHalfMap (glueBase BL BR) (glueSeamPathBase BL BR)).rot
          (glueCutLeftEquiv BL BR d)) :
    BipolarBoundaryBaseIso
      (pathCutLeftHalfBase (glueBase BL BR) (glueSeamPathBase BL BR)) BL := by
  apply BipolarBoundaryBaseIso.symm
  refine bipolarBoundaryBaseIsoOfRot _ _ (glueCutLeftEquiv BL BR) ?_ ?_ ?_ ?_
  · intro d
    change glueCutLeftEquiv BL BR (BL.map.toCombinatorialMap.rot d) =
      (pathCutLeftHalfMap (glueBase BL BR) (glueSeamPathBase BL BR)).rot
        (glueCutLeftEquiv BL BR d)
    exact hrotL d
  · intro d
    apply Subtype.ext
    exact glueCutLeftEquiv_edgeInv BL BR d
  · intro d
    exact glueCutLeftEquiv_tail BL BR d
  · let d := BL.leftPath.firstDart (Nat.zero_lt_of_lt BL.left_length_pos)
    have hd : d ∈ BL.leftPath.darts := List.get_mem _ _
    have ho : BL.map.IsOuter d := (BL.outerSplit.2.2.1 d).mp hd |>.2.2
    have hg : (glueCutLeftEquiv BL BR d).val ∈ (glueBase BL BR).leftPath.darts := by
      rw [glueBase_leftPath_darts]
      exact List.mem_map.mpr ⟨d, hd, by
        rw [glueCutLeftEquiv.eq_def]
        rfl⟩
    have hgo : (glueBase BL BR).map.IsOuter (glueCutLeftEquiv BL BR d).val :=
      ((glueBase BL BR).outerSplit.2.2.1 _).mp hg |>.2.2
    refine ⟨d, ho, ?_⟩
    rw [pathCutLeftHalfBase_map, pathCutLeftHalfMarked_isOuter_iff]
    exact Or.inl ⟨(glueCutLeftEquiv BL BR d).property, hgo⟩



noncomputable def glueCutRightBaseIso
    (hrotR : ∀ d : DR,
      glueCutRightEquiv BL BR (BR.map.toCombinatorialMap.rot d) =
        (pathCutRightHalfMap (glueBase BL BR) (glueSeamPathBase BL BR)).rot
          (glueCutRightEquiv BL BR d)) :
    BipolarBoundaryBaseIso
      (pathCutRightHalfBase (glueBase BL BR) (glueSeamPathBase BL BR)) BR := by
  apply BipolarBoundaryBaseIso.symm
  refine bipolarBoundaryBaseIsoOfRot _ _ (glueCutRightEquiv BL BR) ?_ ?_ ?_ ?_
  · intro d
    change glueCutRightEquiv BL BR (BR.map.toCombinatorialMap.rot d) =
      (pathCutRightHalfMap (glueBase BL BR) (glueSeamPathBase BL BR)).rot
        (glueCutRightEquiv BL BR d)
    exact hrotR d
  · intro d
    apply Subtype.ext
    exact glueCutRightEquiv_edgeInv BL BR d
  · intro d
    exact glueCutRightEquiv_tail BL BR d
  · let d := BR.rightPath.firstDart (Nat.zero_lt_of_lt BR.right_length_pos)
    let e := BR.map.toCombinatorialMap.edgeInv d
    have hd : d ∈ BR.rightPath.darts := List.get_mem _ _
    have he : e ∈ BR.rightPath.darts.reverse.map BR.map.toCombinatorialMap.edgeInv :=
      List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
    have ho : BR.map.IsOuter e :=
      (BR.outerSplit.2.2.2.1 e).mp he |>.2.2
    have hg : (glueCutRightEquiv BL BR d).val ∈ (glueBase BL BR).rightPath.darts := by
      rw [glueBase_rightPath_darts]
      exact List.mem_map.mpr ⟨d, hd, by
        rw [glueCutRightEquiv.eq_def]
        rfl⟩
    have hge : (glueCutRightEquiv BL BR e).val ∈
        (glueBase BL BR).rightPath.darts.reverse.map
          (glueBase BL BR).map.toCombinatorialMap.edgeInv := by
      exact List.mem_map.mpr ⟨_, List.mem_reverse.mpr hg,
        (glueCutRightEquiv_edgeInv BL BR d).symm⟩
    have hgo : (glueBase BL BR).map.IsOuter (glueCutRightEquiv BL BR e).val :=
      ((glueBase BL BR).outerSplit.2.2.2.1 _).mp hge |>.2.2
    refine ⟨e, ho, ?_⟩
    rw [pathCutRightHalfBase_map, pathCutRightHalfMarked_isOuter_iff]
    exact Or.inl ⟨(glueCutRightEquiv BL BR e).property, hgo⟩

private noncomputable def cutGlueRightHalfBaseIso
    {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    {ℓ r n : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')] :
    BipolarBoundaryBaseIso (pathCutRightHalfBase B P)
      (pathCutRightHalfBase B' P') := by
  let e := halfRightCongr I P P' hP'
  refine bipolarBoundaryBaseIsoOfRot _ _ e ?_ ?_ ?_ ?_
  · intro d
    simpa only [pathCutRightHalfBase_map, pathCutRightHalfMarkedMap_toHalfMap]
      using halfRightCongr_rot I P P' hP' d
  · intro d
    exact halfRightCongr_edgeInv I P P' hP' d
  · intro d
    exact halfRightCongr_tail I P P' hP' d
  · let i : Fin (cutPathRightHalf B P).darts.length :=
      ⟨0, by rw [(cutPathRightHalf B P).darts_length]
             exact pathCutRightHalf_path_length_pos B P⟩
    let d₀ : {d : D // d ∈ pathCutRightHalfDarts B P} :=
      (cutPathRightHalf B P).darts.get i
    have hdpath : d₀.val ∈ P.darts := by
      have hget : d₀.val ∈ (cutPathRightHalf B P).darts.unattach :=
        List.mem_map.mpr ⟨d₀, List.get_mem _ _, rfl⟩
      rw [cutPathRightHalf_darts] at hget
      exact hget
    have hboundary : d₀.val ∈ pathCutRightHalfBoundaryDarts B P := Or.inr hdpath
    have hboundary' : I.toEquiv d₀.val ∈ pathCutRightHalfBoundaryDarts B' P' :=
      (pathCutRightHalfBoundaryDarts_mem_iff I P P' hP' d₀.val).mp hboundary
    refine ⟨d₀, ?_, ?_⟩
    · rw [pathCutRightHalfBase_map, pathCutRightHalfMarked_isOuter_iff]
      exact hboundary
    · change (pathCutRightHalfMarkedMap B' P').IsOuter
        (halfRightCongr I P P' hP' d₀)
      exact (pathCutRightHalfMarked_isOuter_iff B' P' _).mpr hboundary'



theorem cut_glueRep {x : XDP} {a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b)
    (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x Bm)
    (hrotL : ∀ d : Fin A.dartCount,
      glueCutLeftEquiv A.B Bm.B (A.B.map.toCombinatorialMap.rot d) =
        (pathCutLeftHalfMap (glueBase A.B Bm.B) (glueSeamPathBase A.B Bm.B)).rot
          (glueCutLeftEquiv A.B Bm.B d))
    (hrotR : ∀ d : Fin Bm.dartCount,
      glueCutRightEquiv A.B Bm.B (Bm.B.map.toCombinatorialMap.rot d) =
        (pathCutRightHalfMap (glueBase A.B Bm.B) (glueSeamPathBase A.B Bm.B)).rot
          (glueCutRightEquiv A.B Bm.B d)) :
    Nonempty (BipolarBoundaryBaseIso
      (cutLRep (glueRep A Bm) (glueRep_len A Bm hA hB)).2.B A.B) ∧
    Nonempty (BipolarBoundaryBaseIso
      (cutRRep (glueRep A Bm) (glueRep_len A Bm hA hB)).2.B Bm.B) := by
  let G := glueBase A.B Bm.B
  let I : BipolarBoundaryBaseIso G (glueRep A Bm).B :=
    G.transportIso (Fintype.equivFin (GlueDart A.B Bm.B))
  let S := glueSeamPathBase A.B Bm.B
  let P := selectedGeodesicOfLen (glueRep A Bm).B x (glueRep_len A Bm hA hB)
  have hP : P.darts = S.darts.map I.toEquiv := by
    rw [selectedGeodesicOfLen_glueRep_darts A Bm hA hB]
    exact BipolarBoundaryBaseIso.mapPath_darts I S
  let L := pathCutLeftHalfBase (glueRep A Bm).B P
  let R := pathCutRightHalfBase (glueRep A Bm).B P
  have JL : BipolarBoundaryBaseIso L (pathCutLeftHalfBase G S) :=
    (pathCutLeftHalfBaseIso I S P hP).symm
  have JR : BipolarBoundaryBaseIso R (pathCutRightHalfBase G S) :=
    (cutGlueRightHalfBaseIso I S P hP).symm
  constructor
  · exact ⟨(L.transportIso (Fintype.equivFin _)).symm.trans
      (JL.trans (glueCutLeftBaseIso A.B Bm.B hrotL))⟩
  · exact ⟨(R.transportIso (Fintype.equivFin _)).symm.trans
      (JR.trans (glueCutRightBaseIso A.B Bm.B hrotR))⟩

end DirectedDistances.PlanarMap
