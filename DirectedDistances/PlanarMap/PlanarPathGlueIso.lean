module

public import DirectedDistances.PlanarMap.PlanarPathGlue
public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIso

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

variable {DL DR DL' DR' : Type*}
  [Fintype DL] [DecidableEq DL] [Fintype DR] [DecidableEq DR]
  [Fintype DL'] [DecidableEq DL'] [Fintype DR'] [DecidableEq DR']
  {ℓ s r : ℕ}
  {BL : BipolarTriangulationWithBoundaryBase DL ℓ s}
  {BR : BipolarTriangulationWithBoundaryBase DR s r}
  {BL' : BipolarTriangulationWithBoundaryBase DL' ℓ s}
  {BR' : BipolarTriangulationWithBoundaryBase DR' s r}

private theorem mem_map_equiv {A A' : Type*} (e : A ≃ A')
    (l : List A) (l' : List A') (h : l.map e = l') (d : A) :
    e d ∈ l' ↔ d ∈ l := by
  rw [← h]
  simp only [List.mem_map, e.injective.eq_iff, exists_eq_right]

 
theorem glueDartCongr_left_kept_iff (I : BipolarBoundaryBaseIso BL BL') (d : DL) :
    BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts ↔
      BL'.map.toCombinatorialMap.edgeInv (I.toEquiv d) ∉ BL'.rightPath.darts := by
  rw [← I.edgeInv_comm]
  exact not_congr (mem_map_equiv I.toEquiv _ _ I.rightDarts _).symm

 
theorem glueDartCongr_right_kept_iff (J : BipolarBoundaryBaseIso BR BR') (d : DR) :
    d ∉ BR.leftPath.darts ↔ J.toEquiv d ∉ BR'.leftPath.darts :=
  not_congr (mem_map_equiv J.toEquiv _ _ J.leftDarts d).symm

 
@[expose] noncomputable def glueDartCongr
    (I : BipolarBoundaryBaseIso BL BL') (J : BipolarBoundaryBaseIso BR BR') :
    GlueDart BL BR ≃ GlueDart BL' BR' :=
  Equiv.sumCongr (I.toEquiv.subtypeEquiv (glueDartCongr_left_kept_iff I))
    (J.toEquiv.subtypeEquiv (glueDartCongr_right_kept_iff J))

private theorem path_opposite_not_mem {D : Type*} [Fintype D] [DecidableEq D]
    {l k n : ℕ} (B : BipolarTriangulationWithBoundaryBase D l k)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ P.darts) : B.map.toCombinatorialMap.edgeInv d ∉ P.darts := by
  have ht {a : D} (ha : a ∈ P.darts) : B.map.tail a := by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact (P.edge_step i).2.1
  exact fun h => (B.map.tail_iff d (B.noMissingDarts d)).mp (ht hd) (ht h)

private theorem map_get {A A' : Type*} (e : A → A')
    (l : List A) (l' : List A') (h : l.map e = l')
    (i : ℕ) (hi : i < l.length) (hi' : i < l'.length) :
    e (l.get ⟨i, hi⟩) = l'.get ⟨i, hi'⟩ := by
  subst l'
  simp

private theorem identify_opposite_seam (i : Fin s) :
    glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv
      (BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩))) =
    glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv
      (BR.leftPath.darts.get ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩))) := by
  have h := congrArg (glueEdgeInv BL BR) (glueIdentify_seam BL BR i)
  simpa only [glueEdgeInv_identify, Sum.map_inl, Sum.map_inr] using h

private theorem congr_identify_kept_left (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : DL)
    (hd : BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts) :
    glueDartCongr I J (glueIdentify BL BR (.inl d)) =
      glueIdentify BL' BR' (.inl (I.toEquiv d)) := by
  rw [glueIdentify_inl_kept BL BR ⟨d, hd⟩,
    glueIdentify_inl_kept BL' BR' ⟨I.toEquiv d, (glueDartCongr_left_kept_iff I d).mp hd⟩]
  rfl

private theorem congr_identify_kept_right (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : DR) (hd : d ∉ BR.leftPath.darts) :
    glueDartCongr I J (glueIdentify BL BR (.inr d)) =
      glueIdentify BL' BR' (.inr (J.toEquiv d)) := by
  rw [glueIdentify_inr_kept BL BR ⟨d, hd⟩,
    glueIdentify_inr_kept BL' BR' ⟨J.toEquiv d, (glueDartCongr_right_kept_iff J d).mp hd⟩]
  rfl



theorem glueDartCongr_identify (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (x : DL ⊕ DR) :
    glueDartCongr I J (glueIdentify BL BR x) =
      glueIdentify BL' BR' (Sum.map I.toEquiv J.toEquiv x) := by
  rcases x with d | d
  · by_cases hd : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
      let j : Fin s := ⟨i.val, by simpa [BL.rightPath.darts_length] using i.isLt⟩
      have he : d = BL.map.toCombinatorialMap.edgeInv
          (BL.rightPath.darts.get ⟨j.val, by rw [BL.rightPath.darts_length]; exact j.isLt⟩) := by
        simpa only [BL.map.toCombinatorialMap.edgeInv_invol] using
          (congrArg BL.map.toCombinatorialMap.edgeInv hi).symm
      rw [he, identify_opposite_seam j]
      rw [congr_identify_kept_right I J _
        (path_opposite_not_mem BR BR.leftPath (List.get_mem _ _))]
      simp only [Sum.map_inl, I.edgeInv_comm, J.edgeInv_comm]
      rw [map_get I.toEquiv _ _ I.rightDarts, map_get J.toEquiv _ _ J.leftDarts]
      exact (identify_opposite_seam (BL := BL') (BR := BR') j).symm
    · exact congr_identify_kept_left I J d hd
  · by_cases hd : d ∈ BR.leftPath.darts
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
      let j : Fin s := ⟨i.val, by simpa [BR.leftPath.darts_length] using i.isLt⟩
      have he : d = BR.leftPath.darts.get
          ⟨j.val, by rw [BR.leftPath.darts_length]; exact j.isLt⟩ := hi.symm
      rw [he, ← glueIdentify_seam BL BR j]
      rw [congr_identify_kept_left I J _
        (path_opposite_not_mem BL BL.rightPath (List.get_mem _ _))]
      simp only [Sum.map_inr]
      rw [map_get I.toEquiv _ _ I.rightDarts, map_get J.toEquiv _ _ J.leftDarts]
      exact glueIdentify_seam BL' BR' j
    · exact congr_identify_kept_right I J d hd

 
theorem glueDartCongr_edgeInv (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : GlueDart BL BR) :
    glueDartCongr I J (glueEdgeInv BL BR d) =
      glueEdgeInv BL' BR' (glueDartCongr I J d) := by
  obtain ⟨x, rfl⟩ := glueIdentify_surjective BL BR d
  rw [glueEdgeInv_identify, glueDartCongr_identify,
    glueDartCongr_identify, glueEdgeInv_identify]
  congr 1
  cases x <;> simp only [Sum.map_inl, Sum.map_inr, I.edgeInv_comm, J.edgeInv_comm]

 
theorem glueDartCongr_tail (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : GlueDart BL BR) :
    glueTail BL' BR' (glueDartCongr I J d) ↔ glueTail BL BR d := by
  rcases d with a | a
  · exact I.tail_iff a.val
  · exact J.tail_iff a.val

 
theorem glueDartCongr_missing (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : GlueDart BL BR) :
    (glueDirectedMap BL' BR').missing (glueDartCongr I J d) ↔
      (glueDirectedMap BL BR).missing d := by
  exact iff_of_false (glueDirectedMap_noMissing BL' BR' _)
    (glueDirectedMap_noMissing BL BR _)

 
theorem glueDartCongr_outerDarts (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') :
    (glueOuterDarts BL BR).map (glueDartCongr I J) = glueOuterDarts BL' BR' := by
  simp only [glueOuterDarts, List.map_append, List.map_map]
  rw [← I.leftDarts, ← J.rightDarts, ← List.map_reverse]
  simp only [List.map_map]
  congr 1
  · apply List.map_congr_left
    intro d _
    exact glueDartCongr_identify I J (.inl d)
  · apply List.map_congr_left
    intro d _
    simpa only [Function.comp_apply, Sum.map_inr, J.edgeInv_comm] using
      glueDartCongr_identify I J (.inr (BR.map.toCombinatorialMap.edgeInv d))

 
theorem glueDartCongr_outerWord (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') :
    (glueOuterWord BL BR).letters.map (glueDartCongr I J) =
      (glueOuterWord BL' BR').letters := by
  rw [glueOuterWord_letters, glueOuterWord_letters]
  exact glueDartCongr_outerDarts I J

 
theorem glueDartCongr_isOuter (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : GlueDart BL BR) :
    (glueDirectedMap BL' BR').IsOuter (glueDartCongr I J d) ↔
      (glueDirectedMap BL BR).IsOuter d := by
  have h := mem_map_equiv (glueDartCongr I J) _ _ (glueDartCongr_outerWord I J) d
  exact (mem_iff_isOuter _ _ (glue_isOuterCycle BL' BR') _).symm.trans
    (h.trans (mem_iff_isOuter _ _ (glue_isOuterCycle BL BR) _))

 
theorem glueDartCongr_outer (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') :
    glueDartCongr I J (glueDirectedMap BL BR).outer =
      (glueDirectedMap BL' BR').outer := by
  rw [glueDirectedMap_outer, glueDirectedMap_outer, glueDartCongr_identify]
  apply congrArg (glueIdentify BL' BR')
  apply congrArg Sum.inl
  exact map_get I.toEquiv _ _ I.leftDarts 0 _ _

 
theorem glueDartCongr_refl :
    glueDartCongr (BipolarBoundaryBaseIso.refl BL) (BipolarBoundaryBaseIso.refl BR) =
      Equiv.refl (GlueDart BL BR) := by
  apply Equiv.ext
  rintro (a | a) <;> rfl

private theorem formPerm_equiv {A A' : Type*} [DecidableEq A] [DecidableEq A']
    (e : A ≃ A') (xs : List A) (hxs : xs.Nodup) (x : A) (hx : x ∈ xs) :
    e (xs.formPerm x) = (xs.map e).formPerm (e x) := by
  have hxs' : (xs.map e).Nodup := hxs.map e.injective
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have himap : i < (xs.map e).length := by simpa using hi
  have hmap : (xs.map e)[i]'himap = e xs[i] := by simp
  rw [← hmap, List.formPerm_apply_getElem _ hxs' i himap,
    List.formPerm_apply_getElem _ hxs i hi]
  simp

private theorem retained_left_outer_mem
    (a : {d : DL // BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts})
    (ha : BL.map.IsOuter a.val) : Sum.inl a ∈ glueOuterDarts BL BR := by
  have hm := BL.outerSplit.2.1.mem_iff.mp (BL.outerSplit.1.2.1 _ ha)
  simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse] at hm
  rcases hm with h | ⟨b, hb, heq⟩
  · rw [← glueIdentify_inl_kept BL BR a]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a.val, h, rfl⟩)
  · exact (a.property (by rw [← heq, BL.map.toCombinatorialMap.edgeInv_invol]; exact hb)).elim

private theorem retained_right_outer_mem (a : {d : DR // d ∉ BR.leftPath.darts})
    (ha : BR.map.IsOuter a.val) : Sum.inr a ∈ glueOuterDarts BL BR := by
  have hm := BR.outerSplit.2.1.mem_iff.mp (BR.outerSplit.1.2.1 _ ha)
  simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse] at hm
  rcases hm with h | ⟨b, hb, heq⟩
  · exact (a.property h).elim
  · rw [← glueIdentify_inr_kept BL BR a]
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨b, List.mem_reverse.mpr hb,
      congrArg (fun d => glueIdentify BL BR (.inr d)) heq⟩

private theorem glued_face_outer (d : GlueDart BL BR) (hd : d ∈ glueOuterDarts BL BR) :
    (glueCombinatorialMap BL BR).faceSucc d = (glueOuterDarts BL BR).formPerm d := by
  have h := (glue_isOuterCycle BL BR).2.2 d (by rwa [glueOuterWord_letters])
  simpa only [glueDirectedMap_toCombinatorialMap, glueOuterWord_letters] using h

private theorem congr_face_outer (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : GlueDart BL BR)
    (hd : d ∈ glueOuterDarts BL BR) :
    glueDartCongr I J ((glueCombinatorialMap BL BR).faceSucc d) =
      (glueCombinatorialMap BL' BR').faceSucc (glueDartCongr I J d) := by
  have hd' : glueDartCongr I J d ∈ glueOuterDarts BL' BR' := by
    rw [← glueDartCongr_outerDarts I J]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [glued_face_outer d hd, glued_face_outer _ hd']
  rw [← glueDartCongr_outerDarts I J]
  exact formPerm_equiv _ _ (by
    simpa only [← glueOuterWord_letters] using (glueOuterWord BL BR).nodup) d hd



theorem glueDartCongr_faceSucc (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : GlueDart BL BR) :
    glueDartCongr I J ((glueCombinatorialMap BL BR).faceSucc d) =
      (glueCombinatorialMap BL' BR').faceSucc (glueDartCongr I J d) := by
  rcases d with a | a
  · by_cases ha : BL.map.IsOuter a.val
    · exact congr_face_outer I J _ (retained_left_outer_mem a ha)
    · have ha' : ¬ BL'.map.IsOuter (I.toEquiv a.val) :=
        fun h => ha ((I.outer_iff _).mp h)
      have hleft : glueDartCongr I J (Sum.inl a) =
          glueIdentify BL' BR' (.inl (I.toEquiv a.val)) := by
        rw [← glueIdentify_inl_kept BL BR a]
        exact glueDartCongr_identify I J (.inl a.val)
      rw [hleft, glue_faceSucc_left_inner _ _ _ ha']
      rw [← glueIdentify_inl_kept BL BR a, glue_faceSucc_left_inner _ _ _ ha,
        glueDartCongr_identify]
      simp only [Sum.map_inl, I.faceSucc_comm]
  · by_cases ha : BR.map.IsOuter a.val
    · exact congr_face_outer I J _ (retained_right_outer_mem a ha)
    · have ha' : ¬ BR'.map.IsOuter (J.toEquiv a.val) :=
        fun h => ha ((J.outer_iff _).mp h)
      have hright : glueDartCongr I J (Sum.inr a) =
          glueIdentify BL' BR' (.inr (J.toEquiv a.val)) := by
        rw [← glueIdentify_inr_kept BL BR a]
        exact glueDartCongr_identify I J (.inr a.val)
      rw [hright, glue_faceSucc_right_inner _ _ _ ha']
      rw [← glueIdentify_inr_kept BL BR a, glue_faceSucc_right_inner _ _ _ ha,
        glueDartCongr_identify]
      simp only [Sum.map_inr, J.faceSucc_comm]



theorem glueDartCongr_rot (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') (d : GlueDart BL BR) :
    glueDartCongr I J ((glueCombinatorialMap BL BR).rot d) =
      (glueCombinatorialMap BL' BR').rot (glueDartCongr I J d) := by
  apply (glueCombinatorialMap BL' BR').rot.symm.injective
  rw [Equiv.symm_apply_apply]
  have h := glueDartCongr_faceSucc I J
    (glueEdgeInv BL BR ((glueCombinatorialMap BL BR).rot d))
  simpa only [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
    glueCombinatorialMap_edgeInv, glueDartCongr_edgeInv, glueEdgeInv_invol,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply] using h.symm

 
theorem glueDartCongr_symm (I : BipolarBoundaryBaseIso BL BL')
    (J : BipolarBoundaryBaseIso BR BR') :
    (glueDartCongr I J).symm = glueDartCongr I.symm J.symm := by
  apply Equiv.ext
  rintro (a | a) <;> rfl

 
theorem glueDartCongr_trans
    {DL'' DR'' : Type*} [Fintype DL''] [DecidableEq DL'']
    [Fintype DR''] [DecidableEq DR'']
    {BL'' : BipolarTriangulationWithBoundaryBase DL'' ℓ s}
    {BR'' : BipolarTriangulationWithBoundaryBase DR'' s r}
    (I : BipolarBoundaryBaseIso BL BL') (J : BipolarBoundaryBaseIso BR BR')
    (I' : BipolarBoundaryBaseIso BL' BL'') (J' : BipolarBoundaryBaseIso BR' BR'') :
    (glueDartCongr I J).trans (glueDartCongr I' J') =
      glueDartCongr (I.trans I') (J.trans J') := by
  apply Equiv.ext
  rintro (a | a) <;> rfl

end DirectedDistances.PlanarMap
