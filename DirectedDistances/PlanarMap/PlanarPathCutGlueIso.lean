module

public import DirectedDistances.PlanarMap.PlanarPathCutLeftHalfBase
public import DirectedDistances.PlanarMap.PlanarPathCutRightHalfBase
public import DirectedDistances.PlanarMap.PlanarPathGlueRep
public import DirectedDistances.PlanarMap.LRCutRepRight
public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIsoOfRot

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

open Classical

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
variable (B : BipolarTriangulationWithBoundaryBase D ℓ r)
variable (P : SimpleDirectedDartPath B.map B.source B.sink n)
variable [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
variable [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]



local instance cutGlueSubtypeBEq {S : D → Prop} : BEq {d // S d} := instBEqOfDecidableEq

omit [Fintype D] [DecidableEq D] in
private theorem mem_unattach_iff {S : D → Prop} (xs : List {d // S d})
    (d : {d // S d}) : d ∈ xs ↔ d.val ∈ xs.unattach := by
  change d ∈ xs ↔ d.val ∈ xs.map Subtype.val
  constructor
  · intro h
    exact List.mem_map.mpr ⟨d, h, rfl⟩
  · intro h
    obtain ⟨e, he, hed⟩ := List.mem_map.mp h
    exact (Subtype.ext hed : e = d) ▸ he

omit [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] in
private theorem left_cut_mem (d : {d // d ∈ pathCutLeftHalfDarts B P}) :
    d ∈ (pathCutLeftHalfBase B P).rightPath.darts ↔ d.val ∈ P.darts := by
  rw [mem_unattach_iff, pathCutLeftHalfBase_rightPath_darts_unattach]

omit [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] in
private theorem right_cut_mem (d : {d // d ∈ pathCutRightHalfDarts B P}) :
    d ∈ (pathCutRightHalfBase B P).leftPath.darts ↔ d.val ∈ P.darts := by
  rw [mem_unattach_iff, pathCutRightHalfBase_leftPath_darts_unattach]

omit [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] in
private theorem left_edgeInv_val (d : {d // d ∈ pathCutLeftHalfDarts B P}) :
    ((pathCutLeftHalfBase B P).map.edgeInv d).val = B.map.edgeInv d.val :=
  (pathCutLeftHalf_embedding_fields B P).2.1 d

omit [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] in
private theorem right_edgeInv_val (d : {d // d ∈ pathCutRightHalfDarts B P}) :
    ((pathCutRightHalfBase B P).map.edgeInv d).val = B.map.edgeInv d.val :=
  (pathCutRightHalf_embedding_fields B P).2.1 d

omit [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
  [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] in
private theorem path_tail {d : D} (h : d ∈ P.darts) : B.map.tail d := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp h
  exact (P.edge_step i).2.1



@[expose] def cutGlueDartMap :
    GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P) → D
  | .inl d => d.val.val
  | .inr d => d.val.val

 
theorem cutGlueDartMap_bijective : Function.Bijective (cutGlueDartMap B P) := by
  constructor
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) hab
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext hab))
    · change a.val = b.val at hab
      have hseam : a.val ∈ pathCutSeamDarts B P := by
        rw [← pathCut_halves_inter_eq_seam B P]
        exact ⟨a.property, hab ▸ b.property⟩
      rcases hseam with hf | hr
      · exact False.elim (hb ((right_cut_mem B P b).mpr (hab ▸ hf)))
      · apply False.elim
        apply ha
        apply (left_cut_mem B P _).mpr
        rw [left_edgeInv_val]
        exact hr
    · change a.val = b.val at hab
      have hseam : a.val ∈ pathCutSeamDarts B P := by
        rw [← pathCut_halves_inter_eq_seam B P]
        exact ⟨hab ▸ b.property, a.property⟩
      rcases hseam with hf | hr
      · exact False.elim (ha ((right_cut_mem B P a).mpr hf))
      · apply False.elim
        apply hb
        apply (left_cut_mem B P _).mpr
        rw [left_edgeInv_val, ← hab]
        exact hr
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext hab))
  · intro d
    by_cases hf : d ∈ P.darts
    · have hl : d ∈ pathCutLeftHalfDarts B P := Or.inr (Or.inl hf)
      refine ⟨.inl ⟨⟨d, hl⟩, ?_⟩, rfl⟩
      intro hi
      have hr := (left_cut_mem B P _).mp hi
      rw [left_edgeInv_val] at hr
      exact ((B.map.tail_iff d (B.noMissingDarts d)).mp
        (path_tail B P hf)) (path_tail B P hr)
    · by_cases hr : B.map.edgeInv d ∈ P.darts
      · have hright : d ∈ pathCutRightHalfDarts B P := Or.inr (Or.inr hr)
        exact ⟨.inr ⟨⟨d, hright⟩, fun h => hf ((right_cut_mem B P _).mp h)⟩, rfl⟩
      · rcases pathCut_halves_cover B P d with hl | hright
        · refine ⟨.inl ⟨⟨d, hl⟩, ?_⟩, rfl⟩
          intro hi
          apply hr
          have h := (left_cut_mem B P _).mp hi
          rwa [left_edgeInv_val] at h
        · exact ⟨.inr ⟨⟨d, hright⟩, fun h => hf ((right_cut_mem B P _).mp h)⟩, rfl⟩

 
@[expose] noncomputable def cutGlueDartEquiv :
    GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P) ≃ D :=
  Equiv.ofBijective (cutGlueDartMap B P) (cutGlueDartMap_bijective B P)

 
@[simp] theorem cutGlueDartEquiv_inl
    (d : {d : {d // d ∈ pathCutLeftHalfDarts B P} //
      (pathCutLeftHalfBase B P).map.edgeInv d ∉
        (pathCutLeftHalfBase B P).rightPath.darts}) :
    cutGlueDartEquiv B P (.inl d) = d.val.val := rfl

 
@[simp] theorem cutGlueDartEquiv_inr
    (d : {d : {d // d ∈ pathCutRightHalfDarts B P} //
      d ∉ (pathCutRightHalfBase B P).leftPath.darts}) :
    cutGlueDartEquiv B P (.inr d) = d.val.val := rfl

omit [Fintype D] [DecidableEq D] in
private theorem unattach_get_val {S : D → Prop} (xs : List {d // S d})
    (ys : List D) (h : xs.unattach = ys) (i : Fin xs.length) :
    (xs.get i).val = ys[i.val]'(by rw [← h, List.length_unattach]; exact i.isLt) := by
  have ho := congrArg (fun zs : List D => zs[i.val]?) h
  simp only [List.getElem?_unattach] at ho
  rw [List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem (by rw [← h, List.length_unattach]; exact i.isLt)] at ho
  exact Option.some.inj ho

private theorem seam_get_val (i : Fin n) :
    ((pathCutLeftHalfBase B P).rightPath.darts.get
      ⟨i.val, by rw [(pathCutLeftHalfBase B P).rightPath.darts_length]; exact i.isLt⟩).val =
    ((pathCutRightHalfBase B P).leftPath.darts.get
      ⟨i.val, by rw [(pathCutRightHalfBase B P).leftPath.darts_length]; exact i.isLt⟩).val := by
  rw [unattach_get_val _ _ (pathCutLeftHalfBase_rightPath_darts_unattach B P),
    unattach_get_val _ _ (pathCutRightHalfBase_leftPath_darts_unattach B P)]

omit [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] in
private theorem forward_left_kept
    (a : {d // d ∈ pathCutLeftHalfDarts B P}) (ha : a.val ∈ P.darts) :
    (pathCutLeftHalfBase B P).map.edgeInv a ∉
      (pathCutLeftHalfBase B P).rightPath.darts := by
  intro h
  have hi := (left_cut_mem B P _).mp h
  rw [left_edgeInv_val] at hi
  exact ((B.map.tail_iff _ (B.noMissingDarts _)).mp
    (path_tail B P ha)) (path_tail B P hi)

private theorem cutGlue_identify_inr
    (b : {d // d ∈ pathCutRightHalfDarts B P}) :
    cutGlueDartEquiv B P
      (glueIdentify (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P) (.inr b)) = b.val := by
  let BL := pathCutLeftHalfBase B P
  let BR := pathCutRightHalfBase B P
  by_cases hb : b ∈ BR.leftPath.darts
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hb
    let j : Fin n := ⟨i.val, by simpa only [BR.leftPath.darts_length] using i.isLt⟩
    let a := BL.rightPath.darts.get
      ⟨j.val, by rw [BL.rightPath.darts_length]; exact j.isLt⟩
    have hv : a.val = b.val := by
      exact (seam_get_val B P j).trans (congrArg Subtype.val hi)
    have ha : a.val ∈ P.darts :=
      (left_cut_mem B P a).mp (List.get_mem _ _)
    have hseam := glueIdentify_seam BL BR j
    have hr : BR.leftPath.darts.get
        ⟨j.val, by rw [BR.leftPath.darts_length]; exact j.isLt⟩ = b := hi
    rw [hr] at hseam
    rw [← hseam, glueIdentify_inl_kept BL BR ⟨a, forward_left_kept B P a ha⟩]
    exact hv
  · rw [glueIdentify_inr_kept BL BR ⟨b, hb⟩]
    rfl

private theorem cutGlue_identify_inl
    (a : {d // d ∈ pathCutLeftHalfDarts B P}) :
    cutGlueDartEquiv B P
      (glueIdentify (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P) (.inl a)) = a.val := by
  let BL := pathCutLeftHalfBase B P
  let BR := pathCutRightHalfBase B P
  by_cases ha : BL.map.edgeInv a ∈ BL.rightPath.darts
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    let j : Fin n := ⟨i.val, by simpa only [BL.rightPath.darts_length] using i.isLt⟩
    let b := BR.leftPath.darts.get
      ⟨j.val, by rw [BR.leftPath.darts_length]; exact j.isLt⟩
    have hv : B.map.edgeInv a.val = b.val := by
      rw [← left_edgeInv_val B P a]
      exact (congrArg Subtype.val hi).symm.trans (seam_get_val B P j)
    have hb : b.val ∈ P.darts :=
      (right_cut_mem B P b).mp (List.get_mem _ _)
    have hkeep : BR.map.edgeInv b ∉ BR.leftPath.darts := by
      intro h
      have h' := (right_cut_mem B P _).mp h
      rw [right_edgeInv_val] at h'
      exact ((B.map.tail_iff _ (B.noMissingDarts _)).mp
        (path_tail B P hb)) (path_tail B P h')
    have hseam := congrArg (glueEdgeInv BL BR) (glueIdentify_seam BL BR j)
    rw [glueEdgeInv_identify, glueEdgeInv_identify] at hseam
    change glueIdentify BL BR (.inl (BL.map.edgeInv (BL.rightPath.darts.get _))) =
      glueIdentify BL BR (.inr (BR.map.edgeInv b)) at hseam
    have hl : BL.rightPath.darts.get
        ⟨j.val, by rw [BL.rightPath.darts_length]; exact j.isLt⟩ = BL.map.edgeInv a := hi
    rw [hl, BL.map.edgeInv_invol] at hseam
    rw [hseam, glueIdentify_inr_kept BL BR ⟨BR.map.edgeInv b, hkeep⟩]
    change (BR.map.edgeInv b).val = a.val
    rw [right_edgeInv_val, ← hv, B.map.edgeInv_invol]
  · rw [glueIdentify_inl_kept BL BR ⟨a, ha⟩]
    rfl

 
theorem cutGlueDartEquiv_edgeInv
    (g : GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)) :
    cutGlueDartEquiv B P
      (glueEdgeInv (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P) g) =
      B.map.edgeInv (cutGlueDartEquiv B P g) := by
  let BL := pathCutLeftHalfBase B P
  let BR := pathCutRightHalfBase B P
  rcases g with a | b
  · rw [← glueIdentify_inl_kept BL BR a, glueEdgeInv_identify]
    change cutGlueDartEquiv B P (glueIdentify BL BR (.inl (BL.map.edgeInv a.val))) = _
    rw [cutGlue_identify_inl, left_edgeInv_val, cutGlue_identify_inl]
  · rw [← glueIdentify_inr_kept BL BR b, glueEdgeInv_identify]
    change cutGlueDartEquiv B P (glueIdentify BL BR (.inr (BR.map.edgeInv b.val))) = _
    rw [cutGlue_identify_inr, right_edgeInv_val, cutGlue_identify_inr]

 
theorem cutGlueDartEquiv_tail
    (g : GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)) :
    B.map.tail (cutGlueDartEquiv B P g) ↔
      glueTail (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P) g := by
  rcases g with a | b
  · exact ((pathCutLeftHalf_embedding_fields B P).2.2.1 a.val).symm
  · exact ((pathCutRightHalf_embedding_fields B P).2.2.1 b.val).symm

 
theorem cutGlueDartEquiv_missing
    (g : GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)) :
    B.map.missing (cutGlueDartEquiv B P g) ↔
      (glueBase (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)).map.missing g := by
  exact iff_of_false (B.noMissingDarts _) ((glueBase (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)).noMissingDarts g)



theorem cutGlueDartEquiv_outerDarts :
    (glueOuterDarts (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)).map
      (cutGlueDartEquiv B P) = canonicalOuterBoundaryDarts B := by
  simp only [glueOuterDarts, List.map_append, List.map_map, Function.comp_def,
    cutGlue_identify_inl, cutGlue_identify_inr, right_edgeInv_val]
  have hl := pathCutLeftHalfBase_leftPath_darts_unattach B P
  have hr := pathCutRightHalfBase_rightPath_darts_unattach B P
  change (pathCutLeftHalfBase B P).leftPath.darts.unattach ++
    (pathCutRightHalfBase B P).rightPath.darts.reverse.map
      (fun d => B.map.edgeInv d.val) = _
  rw [hl]
  change B.leftPath.darts ++ (pathCutRightHalfBase B P).rightPath.darts.reverse.map
    (B.map.edgeInv ∘ Subtype.val) = _
  rw [← List.map_map, List.map_reverse]
  change B.leftPath.darts ++
    (pathCutRightHalfBase B P).rightPath.darts.unattach.reverse.map B.map.edgeInv = _
  rw [hr]
  rfl

private theorem cutGlue_formPerm
    (g : GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P))
    (hg : g ∈ glueOuterDarts (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)) :
    cutGlueDartEquiv B P
      ((glueOuterDarts (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)).formPerm g) =
      (canonicalOuterBoundaryDarts B).formPerm (cutGlueDartEquiv B P g) := by
  let xs := glueOuterDarts (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)
  let e := cutGlueDartEquiv B P
  have hxs : xs.Nodup := by
    simpa only [glueOuterWord_letters] using
      (glueOuterWord (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)).nodup
  have hxs' : (xs.map e).Nodup := hxs.map e.injective
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have himap : i < (xs.map e).length := by simpa only [List.length_map] using hi
  have hmap : (xs.map e)[i]'himap = e xs[i] := by simp only [List.getElem_map]
  rw [← cutGlueDartEquiv_outerDarts B P]
  change e (xs.formPerm xs[i]) = (xs.map e).formPerm (e xs[i])
  rw [← hmap, List.formPerm_apply_getElem _ hxs' i himap,
    List.formPerm_apply_getElem _ hxs i hi]
  simp only [List.getElem_map, List.length_map]

private theorem cutGlue_faceSucc_outer
    (g : GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P))
    (hg : B.map.IsOuter (cutGlueDartEquiv B P g)) :
    cutGlueDartEquiv B P
      ((glueCombinatorialMap (pathCutLeftHalfBase B P)
        (pathCutRightHalfBase B P)).faceSucc g) =
      B.map.toCombinatorialMap.faceSucc (cutGlueDartEquiv B P g) := by
  let BL := pathCutLeftHalfBase B P
  let BR := pathCutRightHalfBase B P
  have he : cutGlueDartEquiv B P g ∈ canonicalOuterBoundaryDarts B := by
    have hw := B.outerSplit.1.2.1 _ hg
    simpa only [canonicalOuterBoundaryDarts, List.append_nil] using
      B.outerSplit.2.1.mem_iff.mp hw
  rw [← cutGlueDartEquiv_outerDarts B P] at he
  obtain ⟨g', hg', hgg'⟩ := List.mem_map.mp he
  have hgg : g' = g := (cutGlueDartEquiv B P).injective hgg'
  subst g'
  have hface := (glue_isOuterCycle BL BR).2.2 g (by
    rwa [glueOuterWord_letters])
  rw [glueDirectedMap_toCombinatorialMap, glueOuterWord_letters] at hface
  rw [hface, canonicalOuterBoundaryDarts_faceSucc_eq_formPerm B hg]
  exact cutGlue_formPerm B P g hg'

 
theorem cutGlueDartEquiv_faceSucc
    (g : GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)) :
    cutGlueDartEquiv B P
      ((glueCombinatorialMap (pathCutLeftHalfBase B P)
        (pathCutRightHalfBase B P)).faceSucc g) =
      B.map.toCombinatorialMap.faceSucc (cutGlueDartEquiv B P g) := by
  let BL := pathCutLeftHalfBase B P
  let BR := pathCutRightHalfBase B P
  by_cases ho : B.map.IsOuter (cutGlueDartEquiv B P g)
  · exact cutGlue_faceSucc_outer B P g ho
  rcases g with a | b
  · have hnb : a.val.val ∉ pathCutLeftHalfBoundaryDarts B P := by
      rintro (⟨_, hout⟩ | ⟨p, hp, he⟩)
      · exact ho hout
      · apply a.property
        apply (left_cut_mem B P _).mpr
        rw [left_edgeInv_val, he, B.map.edgeInv_invol]
        exact hp
    have hi : ¬ BL.map.IsOuter a.val := by
      intro h
      exact hnb ((pathCutLeftHalfMarked_isOuter_iff B P _).mp h)
    have hf := pathCutLeftHalf_faceSucc_eq_base_of_mem B P a.val.property
      ((pathCutLeftHalf_inner_face_contained B P a.val.property hnb).2 _
        Equiv.Perm.SameCycle.rfl.apply_right).1
    rw [← glueIdentify_inl_kept BL BR a, glue_faceSucc_left_inner BL BR _ hi,
      cutGlue_identify_inl, cutGlue_identify_inl]
    exact hf
  · have hnb : b.val.val ∉ pathCutRightHalfBoundaryDarts B P := by
      rintro (⟨_, hout⟩ | hp)
      · exact ho hout
      · exact b.property ((right_cut_mem B P _).mpr hp)
    have hi : ¬ BR.map.IsOuter b.val := by
      intro h
      exact hnb ((pathCutRightHalfMarked_isOuter_iff B P _).mp h)
    have hf := pathCutRightHalf_faceSucc_eq_base_of_mem B P b.val.property
      ((pathCutRightHalf_inner_face_contained B P b.val.property hnb).2 _
        Equiv.Perm.SameCycle.rfl.apply_right).1
    rw [← glueIdentify_inr_kept BL BR b, glue_faceSucc_right_inner BL BR _ hi,
      cutGlue_identify_inr, cutGlue_identify_inr]
    exact hf

 
theorem cutGlueDartEquiv_rot
    (g : GlueDart (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)) :
    cutGlueDartEquiv B P
      ((glueCombinatorialMap (pathCutLeftHalfBase B P)
        (pathCutRightHalfBase B P)).rot g) =
      B.map.rot (cutGlueDartEquiv B P g) := by
  apply B.map.rot.symm.injective
  rw [Equiv.symm_apply_apply]
  have h := cutGlueDartEquiv_faceSucc B P
    (glueEdgeInv (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)
      ((glueCombinatorialMap (pathCutLeftHalfBase B P)
        (pathCutRightHalfBase B P)).rot g))
  simpa only [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
    glueCombinatorialMap_edgeInv, cutGlueDartEquiv_edgeInv, glueEdgeInv_invol,
    B.map.edgeInv_invol, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using h.symm



@[expose] noncomputable def cutGlueBaseIso :
    BipolarBoundaryBaseIso
      (glueBase (pathCutLeftHalfBase B P) (pathCutRightHalfBase B P)) B := by
  let BL := pathCutLeftHalfBase B P
  let BR := pathCutRightHalfBase B P
  apply bipolarBoundaryBaseIsoOfRot (glueBase BL BR) B (cutGlueDartEquiv B P)
  · intro g
    simpa only [glueBase_map, glueDirectedMap_toCombinatorialMap] using
      cutGlueDartEquiv_rot B P g
  · intro g
    simpa only [glueBase_map, glueDirectedMap_toCombinatorialMap,
      glueCombinatorialMap_edgeInv] using cutGlueDartEquiv_edgeInv B P g
  · intro g
    simpa only [glueBase_map, glueDirectedMap_tail] using cutGlueDartEquiv_tail B P g
  · refine ⟨(glueDirectedMap BL BR).outer, ?_, ?_⟩
    · change Equiv.Perm.SameCycle _ _ _
      exact Equiv.Perm.SameCycle.rfl
    · have hm := (glue_isOuterCycle BL BR).2.1 (glueDirectedMap BL BR).outer
        Equiv.Perm.SameCycle.rfl
      rw [glueOuterWord_letters] at hm
      have he : cutGlueDartEquiv B P (glueDirectedMap BL BR).outer ∈
          (glueOuterDarts BL BR).map (cutGlueDartEquiv B P) :=
        List.mem_map.mpr ⟨_, hm, rfl⟩
      rw [cutGlueDartEquiv_outerDarts] at he
      exact canonicalOuterBoundaryDarts_mem_isOuter B he

end DirectedDistances.PlanarMap

namespace DirectedDistances.PlanarMap

open Classical

attribute [local instance] cutGlueSubtypeBEq




theorem glueRep_cutRep_iso {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    Nonempty (BipolarBoundaryBaseIso
      (glueRep (cutLRep R hR).2 (cutRRep R hR).2).B R.B) := by
  let P := selectedGeodesicOfLen R.B x hR
  let BL := pathCutLeftHalfBase R.B P
  let BR := pathCutRightHalfBase R.B P
  let IL : BipolarBoundaryBaseIso (cutLRep R hR).2.B BL :=
    (BL.transportIso (Fintype.equivFin _)).symm
  let IR : BipolarBoundaryBaseIso (cutRRep R hR).2.B BR :=
    (BR.transportIso (Fintype.equivFin _)).symm
  let G := glueBase (cutLRep R hR).2.B (cutRRep R hR).2.B
  let I : BipolarBoundaryBaseIso G R.B :=
    (glueBaseIso IL IR).trans (cutGlueBaseIso R.B P)
  let e := Fintype.equivFin (GlueDart (cutLRep R hR).2.B (cutRRep R hR).2.B)
  change Nonempty (BipolarBoundaryBaseIso (G.transport e) R.B)
  exact ⟨(G.transportIso e).symm.trans I⟩

end DirectedDistances.PlanarMap
