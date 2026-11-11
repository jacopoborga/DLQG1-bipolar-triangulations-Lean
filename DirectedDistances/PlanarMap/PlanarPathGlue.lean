module

public import DirectedDistances.PlanarMap.GeneralBipolarBoundary
public import DirectedDistances.PlanarMap.CombinatorialMap

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}

private theorem glue_path_nodup {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) : P.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hv := (P.edge_step i).2.2.1.trans
    ((congrArg (dartTailVertex M) hij).trans (P.edge_step j).2.2.1.symm)
  exact Fin.ext (congrArg (fun q : Fin P.vertices.length => q.val) (P.vertices_nodup.get_inj_iff.mp hv))

private theorem glue_path_tail {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) {d : D} (hd : d ∈ P.darts) :
    M.tail d := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact (P.edge_step i).2.1

private theorem glue_path_opposite_not_mem {D : Type*} [Fintype D] [DecidableEq D]
    {l k n : ℕ} (B : BipolarTriangulationWithBoundaryBase D l k)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ P.darts) : B.map.toCombinatorialMap.edgeInv d ∉ P.darts := by
  exact (B.map.tail_iff d (B.noMissingDarts d)).mp (glue_path_tail P hd) ∘
    (fun h => glue_path_tail P h)

private noncomputable def glue_path_equiv {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) : Fin n ≃ {d : D // d ∈ P.darts} :=
  Equiv.ofBijective (fun i => ⟨P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩,
    List.get_mem _ _⟩) (by
      constructor
      · intro i j hij
        have h := (glue_path_nodup P).get_inj_iff.mp (congrArg Subtype.val hij)
        exact Fin.ext (congrArg (fun q : Fin P.darts.length => q.val) h)
      · rintro ⟨d, hd⟩
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
        refine ⟨⟨i.val, by simpa [P.darts_length] using i.isLt⟩, ?_⟩
        exact Subtype.ext hi)

variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)



abbrev GlueDart :=
  {d : DL // BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts} ⊕
    {d : DR // d ∉ BR.leftPath.darts}

private noncomputable def glue_seam_equiv :
    {d : DL // d ∈ BL.rightPath.darts} ≃ {d : DR // d ∈ BR.leftPath.darts} :=
  (glue_path_equiv BL.rightPath).symm.trans (glue_path_equiv BR.leftPath)



noncomputable def glueIdentify : DL ⊕ DR → GlueDart BL BR
  | .inl d => if h : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts then
      .inr ⟨BR.map.toCombinatorialMap.edgeInv (glue_seam_equiv BL BR ⟨_, h⟩).val,
        glue_path_opposite_not_mem BR BR.leftPath (glue_seam_equiv BL BR ⟨_, h⟩).property⟩
    else .inl ⟨d, h⟩
  | .inr d => if h : d ∈ BR.leftPath.darts then
      .inl ⟨((glue_seam_equiv BL BR).symm ⟨d, h⟩).val,
        glue_path_opposite_not_mem BL BL.rightPath
          ((glue_seam_equiv BL BR).symm ⟨d, h⟩).property⟩
    else .inr ⟨d, h⟩



theorem glueIdentify_surjective : Function.Surjective (glueIdentify BL BR) := by
  rintro (⟨d, hd⟩ | ⟨d, hd⟩)
  · exact ⟨.inl d, by simp only [glueIdentify, dite_eq_right hd]⟩
  · exact ⟨.inr d, by simp only [glueIdentify, dite_eq_right hd]⟩

private noncomputable def glue_flip : GlueDart BL BR → GlueDart BL BR
  | .inl d => glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv d.val))
  | .inr d => glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d.val))

private theorem glue_flip_invol : Function.Involutive (glue_flip BL BR) := by
  rintro (⟨d, hd⟩ | ⟨d, hd⟩)
  · by_cases h : d ∈ BL.rightPath.darts
    · simp [glue_flip, glueIdentify, BL.map.toCombinatorialMap.edgeInv_invol,
        BR.map.toCombinatorialMap.edgeInv_invol, h,
        (glue_seam_equiv BL BR ⟨d, h⟩).property]
    · simp [glue_flip, glueIdentify, BL.map.toCombinatorialMap.edgeInv_invol,
        h, hd]
  · by_cases h : BR.map.toCombinatorialMap.edgeInv d ∈ BR.leftPath.darts
    · simp [glue_flip, glueIdentify, BL.map.toCombinatorialMap.edgeInv_invol,
        BR.map.toCombinatorialMap.edgeInv_invol, h,
        ((glue_seam_equiv BL BR).symm ⟨BR.map.toCombinatorialMap.edgeInv d, h⟩).property]
    · simp [glue_flip, glueIdentify, BR.map.toCombinatorialMap.edgeInv_invol,
        h, hd]

private theorem glue_flip_ne (d : GlueDart BL BR) : glue_flip BL BR d ≠ d := by
  rcases d with ⟨d, hd⟩ | ⟨d, hd⟩
  · by_cases h : d ∈ BL.rightPath.darts
    · simp [glue_flip, glueIdentify, BL.map.toCombinatorialMap.edgeInv_invol, h]
    · intro heq
      have hv := congrArg (fun x => match x with
        | Sum.inl a => a.val
        | Sum.inr _ => d) heq
      exact BL.map.toCombinatorialMap.edgeInv_ne d (by
        simpa [glue_flip, glueIdentify, BL.map.toCombinatorialMap.edgeInv_invol, h] using hv)
  · by_cases h : BR.map.toCombinatorialMap.edgeInv d ∈ BR.leftPath.darts
    · simp [glue_flip, glueIdentify, h]
    · intro heq
      have hv := congrArg (fun x => match x with
        | Sum.inl _ => d
        | Sum.inr a => a.val) heq
      exact BR.map.toCombinatorialMap.edgeInv_ne d (by
        simpa [glue_flip, glueIdentify, h] using hv)



noncomputable def glueEdgeInv : Equiv.Perm (GlueDart BL BR) where
  toFun := glue_flip BL BR
  invFun := glue_flip BL BR
  left_inv := glue_flip_invol BL BR
  right_inv := glue_flip_invol BL BR

 
theorem glueEdgeInv_invol (d : GlueDart BL BR) :
    glueEdgeInv BL BR (glueEdgeInv BL BR d) = d := glue_flip_invol BL BR d

 
theorem glueEdgeInv_ne (d : GlueDart BL BR) : glueEdgeInv BL BR d ≠ d :=
  glue_flip_ne BL BR d

private def glue_inner_perm {D : Type*} [Fintype D] [DecidableEq D]
    {l k : ℕ} (B : BipolarTriangulationWithBoundaryBase D l k) : Equiv.Perm D :=
  B.outerWord.letters.formPerm.symm * B.map.toCombinatorialMap.faceSucc

private theorem glue_inner_perm_outer {D : Type*} [Fintype D] [DecidableEq D]
    {l k : ℕ} (B : BipolarTriangulationWithBoundaryBase D l k) {d : D}
    (hd : B.map.IsOuter d) : glue_inner_perm B d = d := by
  have hm := B.outerSplit.1.2.1 d hd
  change B.outerWord.letters.formPerm.symm (B.map.toCombinatorialMap.faceSucc d) = d
  rw [B.outerSplit.1.2.2 d hm]
  exact B.outerWord.letters.formPerm.symm_apply_apply d

private theorem glue_inner_perm_inner {D : Type*} [Fintype D] [DecidableEq D]
    {l k : ℕ} (B : BipolarTriangulationWithBoundaryBase D l k) {d : D}
    (hd : ¬ B.map.IsOuter d) :
    glue_inner_perm B d = B.map.toCombinatorialMap.faceSucc d := by
  have hn : B.map.toCombinatorialMap.faceSucc d ∉ B.outerWord.letters := by
    intro hm
    exact hd (Equiv.Perm.sameCycle_apply_right.mp (B.outerSplit.1.1 _ hm))
  change B.outerWord.letters.formPerm.symm (B.map.toCombinatorialMap.faceSucc d) = _
  apply B.outerWord.letters.formPerm.injective
  rw [Equiv.apply_symm_apply, List.formPerm_apply_of_notMem hn]

private theorem glue_left_drop_outer {d : DL}
    (hd : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts) :
    BL.map.IsOuter d := by
  apply BL.outerSplit.1.1 d
  apply BL.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse]
  right
  exact ⟨BL.map.toCombinatorialMap.edgeInv d, hd,
    BL.map.toCombinatorialMap.edgeInv_invol d⟩

private theorem glue_right_drop_outer {d : DR} (hd : d ∈ BR.leftPath.darts) :
    BR.map.IsOuter d := by
  apply BR.outerSplit.1.1 d
  apply BR.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append]
  exact Or.inl hd

private theorem glue_preserves_compl {D : Type*} (f : Equiv.Perm D) (p : D → Prop)
    (h : ∀ d, p d → f d = d) (d : D) : ¬ p (f d) ↔ ¬ p d := by
  constructor
  · intro hn hp
    exact hn ((h d hp).symm ▸ hp)
  · intro hn hp
    have heq : f d = d := f.injective (h (f d) hp)
    exact hn (heq ▸ hp)

private noncomputable def glue_inner_retained : Equiv.Perm (GlueDart BL BR) :=
  Equiv.sumCongr
    ((glue_inner_perm BL).subtypePerm
      (glue_preserves_compl _ _ (fun _ hd =>
        glue_inner_perm_outer BL (glue_left_drop_outer BL hd))))
    ((glue_inner_perm BR).subtypePerm
      (glue_preserves_compl _ _ (fun _ hd =>
        glue_inner_perm_outer BR (glue_right_drop_outer BR hd))))



@[expose] noncomputable def glueOuterDarts : List (GlueDart BL BR) :=
  BL.leftPath.darts.map (fun d => glueIdentify BL BR (.inl d)) ++
    BR.rightPath.darts.reverse.map (fun d =>
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d)))

private noncomputable def glue_face_perm : Equiv.Perm (GlueDart BL BR) :=
  (glueOuterDarts BL BR).formPerm * glue_inner_retained BL BR



noncomputable def glueCombinatorialMap : CombinatorialMap (GlueDart BL BR) where
  edgeInv := glueEdgeInv BL BR
  edgeInv_invol := glueEdgeInv_invol BL BR
  edgeInv_ne := glueEdgeInv_ne BL BR
  rot := glueEdgeInv BL BR * (glue_face_perm BL BR)⁻¹

 
theorem glueCombinatorialMap_edgeInv :
    (glueCombinatorialMap BL BR).edgeInv = glueEdgeInv BL BR := by
  simp only [glueCombinatorialMap]

private theorem glue_faceSucc : (glueCombinatorialMap BL BR).faceSucc =
    glue_face_perm BL BR := by
  change (glueEdgeInv BL BR * (glue_face_perm BL BR)⁻¹)⁻¹ * glueEdgeInv BL BR = _
  rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

private theorem glue_left_removed_card :
    Fintype.card {d : DL // BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts} = s := by
  calc
    _ = Fintype.card {d : DL // d ∈ BL.rightPath.darts} :=
      Fintype.card_congr (BL.map.toCombinatorialMap.edgeInv.subtypeEquiv (fun _ => Iff.rfl))
    _ = Fintype.card (Fin s) := (Fintype.card_congr (glue_path_equiv BL.rightPath)).symm
    _ = s := Fintype.card_fin s

private theorem glue_right_removed_card :
    Fintype.card {d : DR // d ∈ BR.leftPath.darts} = s := by
  exact (Fintype.card_congr (glue_path_equiv BR.leftPath)).symm.trans (Fintype.card_fin s)

private theorem glue_card_balance : Fintype.card (GlueDart BL BR) + 2 * s =
    Fintype.card DL + Fintype.card DR := by
  have hL := Fintype.card_subtype_le
    (fun d : DL => BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts)
  have hR := Fintype.card_subtype_le (fun d : DR => d ∈ BR.leftPath.darts)
  rw [glue_left_removed_card BL] at hL
  rw [glue_right_removed_card BR] at hR
  change Fintype.card (_ ⊕ _) + 2 * s = _
  rw [Fintype.card_sum, Fintype.card_subtype_compl, Fintype.card_subtype_compl,
    glue_left_removed_card BL, glue_right_removed_card BR]
  omega

 
theorem card_glueDart : Fintype.card (GlueDart BL BR) =
    Fintype.card DL + Fintype.card DR - 2 * s := by
  have h := glue_card_balance BL BR
  omega

 
theorem numEdges_glueCombinatorialMap :
    (glueCombinatorialMap BL BR).numEdges + s =
      BL.map.toCombinatorialMap.numEdges + BR.map.toCombinatorialMap.numEdges := by
  have h := glue_card_balance BL BR
  have hG := (glueCombinatorialMap BL BR).two_mul_numEdges
  have hL := BL.map.toCombinatorialMap.two_mul_numEdges
  have hR := BR.map.toCombinatorialMap.two_mul_numEdges
  omega



@[expose] def glueTail : GlueDart BL BR → Prop
  | .inl d => BL.map.tail d.val
  | .inr d => BR.map.tail d.val

private theorem glue_tail_flip (d : GlueDart BL BR) :
    glueTail BL BR d ↔ ¬ glueTail BL BR (glueEdgeInv BL BR d) := by
  change glueTail BL BR d ↔ ¬ glueTail BL BR (glue_flip BL BR d)
  rcases d with ⟨d, hd⟩ | ⟨d, hd⟩
  · by_cases h : d ∈ BL.rightPath.darts
    · have hL := glue_path_tail BL.rightPath h
      have hR := (BR.map.tail_iff _ (BR.noMissingDarts _)).mp
        (glue_path_tail BR.leftPath (glue_seam_equiv BL BR ⟨d, h⟩).property)
      simpa [glueTail, glue_flip, glueIdentify,
        BL.map.toCombinatorialMap.edgeInv_invol, h, hL] using hR
    · simpa [glueTail, glue_flip, glueIdentify,
        BL.map.toCombinatorialMap.edgeInv_invol, h] using
        (BL.map.tail_iff d (BL.noMissingDarts d))
  · by_cases h : BR.map.toCombinatorialMap.edgeInv d ∈ BR.leftPath.darts
    · have hR := (BR.map.tail_iff _ (BR.noMissingDarts _)).mp
        (glue_path_tail BR.leftPath h)
      have hnR : ¬ BR.map.tail d := by
        simpa only [BR.map.toCombinatorialMap.edgeInv_invol] using hR
      have hL := glue_path_tail BL.rightPath
        ((glue_seam_equiv BL BR).symm ⟨BR.map.toCombinatorialMap.edgeInv d, h⟩).property
      simp [glueTail, glue_flip, glueIdentify, h, hnR, hL]
    · simpa [glueTail, glue_flip, glueIdentify, h] using
        (BR.map.tail_iff d (BR.noMissingDarts d))



noncomputable def glueDirectedMap : DirectedMapWithMissing (GlueDart BL BR) where
  toCombinatorialMap := glueCombinatorialMap BL BR
  missing := fun _ => False
  missing_edgeInv := fun _ => Iff.rfl
  tail := glueTail BL BR
  tail_iff := fun d _ => glue_tail_flip BL BR d
  tail_missing := fun _ h => h.elim
  outer := glueIdentify BL BR (.inl (BL.leftPath.firstDart (by have := BL.left_length_pos; omega)))
  missing_outer := fun _ h => h.elim

 
theorem glueDirectedMap_tail (d : GlueDart BL BR) :
    (glueDirectedMap BL BR).tail d ↔ glueTail BL BR d := by
  simp only [glueDirectedMap]

 
theorem glueDirectedMap_noMissing (d : GlueDart BL BR) :
    ¬ (glueDirectedMap BL BR).missing d := by
  simp only [glueDirectedMap, not_false_eq_true]

private theorem glue_left_tail_kept {d : DL} (hd : BL.map.tail d) :
    BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts := by
  intro h
  exact (BL.map.tail_iff d (BL.noMissingDarts d)).mp hd (glue_path_tail BL.rightPath h)

private theorem glue_right_nontail_kept {d : DR} (hd : ¬ BR.map.tail d) :
    d ∉ BR.leftPath.darts := fun h => hd (glue_path_tail BR.leftPath h)

private theorem glue_right_boundary_kept {d : DR} (hd : d ∈ BR.rightPath.darts) :
    BR.map.toCombinatorialMap.edgeInv d ∉ BR.leftPath.darts :=
  glue_right_nontail_kept BR ((BR.map.tail_iff d (BR.noMissingDarts d)).mp
    (glue_path_tail BR.rightPath hd))

private theorem glue_left_boundary_outer {d : DL} (hd : d ∈ BL.leftPath.darts) :
    BL.map.IsOuter d := by
  apply BL.outerSplit.1.1 d
  apply BL.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append]
  exact Or.inl hd

private theorem glue_right_boundary_outer {d : DR} (hd : d ∈ BR.rightPath.darts) :
    BR.map.IsOuter (BR.map.toCombinatorialMap.edgeInv d) := by
  apply BR.outerSplit.1.1
  apply BR.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse]
  exact Or.inr ⟨d, hd, rfl⟩

private def glue_original_outer : GlueDart BL BR → Prop
  | .inl a => BL.map.IsOuter a.val
  | .inr a => BR.map.IsOuter a.val

private theorem glue_outer_original (d : GlueDart BL BR) (hd : d ∈ glueOuterDarts BL BR) :
    glue_original_outer BL BR d := by
  simp only [glueOuterDarts, List.mem_append, List.mem_map] at hd
  rcases hd with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · simp only [glue_original_outer, glueIdentify, dite_eq_right (glue_left_tail_kept BL (glue_path_tail BL.leftPath ha))]
    exact glue_left_boundary_outer BL ha
  · have ha' := List.mem_reverse.mp ha
    simp only [glue_original_outer, glueIdentify, dite_eq_right (glue_right_boundary_kept BR ha')]
    exact glue_right_boundary_outer BR ha'

private theorem glue_inner_retained_outer (d : GlueDart BL BR)
    (hd : glue_original_outer BL BR d) : glue_inner_retained BL BR d = d := by
  rcases d with a | a
  · change Sum.inl ⟨glue_inner_perm BL a.val, _⟩ = Sum.inl a
    apply congrArg Sum.inl
    exact Subtype.ext (glue_inner_perm_outer BL hd)
  · change Sum.inr ⟨glue_inner_perm BR a.val, _⟩ = Sum.inr a
    apply congrArg Sum.inr
    exact Subtype.ext (glue_inner_perm_outer BR hd)

private theorem glue_outer_fixed {d : GlueDart BL BR} (hd : d ∈ glueOuterDarts BL BR) :
    glue_inner_retained BL BR d = d :=
  glue_inner_retained_outer BL BR d (glue_outer_original BL BR d hd)

private theorem glue_outer_nodup : (glueOuterDarts BL BR).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.Nodup.map_on _ (glue_path_nodup BL.leftPath)
    intro a ha b hb hab
    simp only [glueIdentify,
      dite_eq_right (glue_left_tail_kept BL (glue_path_tail BL.leftPath ha)),
      dite_eq_right (glue_left_tail_kept BL (glue_path_tail BL.leftPath hb)),
      Sum.inl.injEq, Subtype.mk.injEq] at hab
    exact hab
  · apply List.Nodup.map_on _ (List.nodup_reverse.mpr (glue_path_nodup BR.rightPath))
    intro a ha b hb hab
    have ha' := List.mem_reverse.mp ha
    have hb' := List.mem_reverse.mp hb
    simp only [glueIdentify,
      dite_eq_right (glue_right_boundary_kept BR ha'),
      dite_eq_right (glue_right_boundary_kept BR hb'),
      Sum.inr.injEq, Subtype.mk.injEq] at hab
    exact BR.map.toCombinatorialMap.edgeInv.injective hab
  · intro d hdL hdR
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hdL
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp hdR
    simp only [glueIdentify,
      dite_eq_right (glue_left_tail_kept BL (glue_path_tail BL.leftPath ha)),
      dite_eq_right (glue_right_boundary_kept BR (List.mem_reverse.mp hb)),
      reduceCtorEq] at heq

private theorem glue_left_inner_kept {d : DL} (hd : ¬ BL.map.IsOuter d) :
    BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts :=
  fun h => hd (glue_left_drop_outer BL h)

private theorem glue_right_inner_kept {d : DR} (hd : ¬ BR.map.IsOuter d) :
    d ∉ BR.leftPath.darts := fun h => hd (glue_right_drop_outer BR h)



theorem glue_faceSucc_left_inner (d : DL) (hd : ¬ BL.map.IsOuter d) :
    (glueCombinatorialMap BL BR).faceSucc (glueIdentify BL BR (.inl d)) =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.faceSucc d)) := by
  have hs : ¬ BL.map.IsOuter (BL.map.toCombinatorialMap.faceSucc d) :=
    fun h => hd (Equiv.Perm.sameCycle_apply_right.mp h)
  rw [glue_faceSucc]
  simp only [glue_face_perm, Equiv.Perm.mul_apply, glueIdentify,
    dite_eq_right (glue_left_inner_kept BL hd),
    dite_eq_right (glue_left_inner_kept BL hs)]
  have hi : glue_inner_retained BL BR (.inl ⟨d, glue_left_inner_kept BL hd⟩) =
      .inl ⟨BL.map.toCombinatorialMap.faceSucc d, glue_left_inner_kept BL hs⟩ := by
    apply congrArg Sum.inl
    exact Subtype.ext (glue_inner_perm_inner BL hd)
  rw [hi]
  apply List.formPerm_apply_of_notMem
  intro hm
  exact hs (glue_outer_original BL BR _ hm)



theorem glue_faceSucc_right_inner (d : DR) (hd : ¬ BR.map.IsOuter d) :
    (glueCombinatorialMap BL BR).faceSucc (glueIdentify BL BR (.inr d)) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.faceSucc d)) := by
  have hs : ¬ BR.map.IsOuter (BR.map.toCombinatorialMap.faceSucc d) :=
    fun h => hd (Equiv.Perm.sameCycle_apply_right.mp h)
  rw [glue_faceSucc]
  simp only [glue_face_perm, Equiv.Perm.mul_apply, glueIdentify,
    dite_eq_right (glue_right_inner_kept BR hd),
    dite_eq_right (glue_right_inner_kept BR hs)]
  have hi : glue_inner_retained BL BR (.inr ⟨d, glue_right_inner_kept BR hd⟩) =
      .inr ⟨BR.map.toCombinatorialMap.faceSucc d, glue_right_inner_kept BR hs⟩ := by
    apply congrArg Sum.inr
    exact Subtype.ext (glue_inner_perm_inner BR hd)
  rw [hi]
  apply List.formPerm_apply_of_notMem
  intro hm
  exact hs (glue_outer_original BL BR _ hm)

private theorem glue_outer_face_agrees {d : GlueDart BL BR}
    (hd : d ∈ glueOuterDarts BL BR) :
    (glueCombinatorialMap BL BR).faceSucc d = (glueOuterDarts BL BR).formPerm d := by
  rw [glue_faceSucc]
  change (glueOuterDarts BL BR).formPerm (glue_inner_retained BL BR d) = _
  rw [glue_outer_fixed BL BR hd]

private theorem glue_outer_root_mem :
    (glueDirectedMap BL BR).outer ∈ glueOuterDarts BL BR := by
  simp only [glueDirectedMap, glueOuterDarts]
  apply List.mem_append.mpr
  left
  apply List.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  exact List.get_mem _ _

private theorem glue_outer_nonempty : glueOuterDarts BL BR ≠ [] := by
  intro h
  have hm := glue_outer_root_mem BL BR
  rw [h] at hm
  exact List.not_mem_nil hm



noncomputable def glueOuterWord : NonemptyWord (GlueDart BL BR) where
  letters := glueOuterDarts BL BR
  nonempty := glue_outer_nonempty BL BR
  nodup := glue_outer_nodup BL BR

 
theorem glueOuterWord_letters : (glueOuterWord BL BR).letters = glueOuterDarts BL BR := by
  simp only [glueOuterWord]

private theorem glue_outer_formPerm_pow_mem (n : ℕ) {d : GlueDart BL BR}
    (hd : d ∈ glueOuterDarts BL BR) :
    ((glueOuterDarts BL BR).formPerm ^ n) d ∈ glueOuterDarts BL BR := by
  induction n with
  | zero => simpa only [pow_zero, Equiv.Perm.one_apply] using hd
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact List.formPerm_apply_mem_of_mem ih

private theorem glue_outer_face_pow (n : ℕ) {d : GlueDart BL BR}
    (hd : d ∈ glueOuterDarts BL BR) :
    ((glueCombinatorialMap BL BR).faceSucc ^ n) d =
      ((glueOuterDarts BL BR).formPerm ^ n) d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    exact glue_outer_face_agrees BL BR (glue_outer_formPerm_pow_mem BL BR n hd)

private theorem glue_outer_cycle_iff (d : GlueDart BL BR) :
    (glueCombinatorialMap BL BR).faceSucc.SameCycle (glueDirectedMap BL BR).outer d ↔
      d ∈ glueOuterDarts BL BR := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn, glue_outer_face_pow BL BR n (glue_outer_root_mem BL BR)]
    exact glue_outer_formPerm_pow_mem BL BR n (glue_outer_root_mem BL BR)
  · intro hd
    have hc := (glue_outer_nodup BL BR).isCycleOn_formPerm.2
      (glue_outer_root_mem BL BR) hd
    obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, glue_outer_face_pow BL BR n (glue_outer_root_mem BL BR)]
    exact hn




theorem glue_isOuterCycle : IsOuterCycle (glueDirectedMap BL BR) (glueOuterWord BL BR) := by
  have hface : (glueDirectedMap BL BR).toCombinatorialMap = glueCombinatorialMap BL BR := by
    simp only [glueDirectedMap]
  have hout (d : GlueDart BL BR) :
      (glueDirectedMap BL BR).IsOuter d ↔ d ∈ glueOuterDarts BL BR := by
    simpa only [DirectedMapWithMissing.IsOuter, CombinatorialMap.IsOuter, hface]
      using glue_outer_cycle_iff BL BR d
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact (hout d).mpr ((glueOuterWord_letters BL BR) ▸ hd)
  · intro d hd
    rw [glueOuterWord_letters]
    exact (hout d).mp hd
  · intro d hd
    rw [hface, glueOuterWord_letters]
    exact glue_outer_face_agrees BL BR ((glueOuterWord_letters BL BR) ▸ hd)

 
theorem glueIdentify_inl_kept
    (d : {d : DL // BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts}) :
    glueIdentify BL BR (.inl d.val) = .inl d := by
  simp only [glueIdentify, dite_eq_right d.property]

 
theorem glueIdentify_inr_kept (d : {d : DR // d ∉ BR.leftPath.darts}) :
    glueIdentify BL BR (.inr d.val) = .inr d := by
  simp only [glueIdentify, dite_eq_right d.property]

private theorem glue_seam_get (i : Fin s) :
    glue_seam_equiv BL BR
      ⟨BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩,
        List.get_mem _ _⟩ =
      ⟨BR.leftPath.darts.get ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩,
        List.get_mem _ _⟩ := by
  change (glue_path_equiv BR.leftPath)
    ((glue_path_equiv BL.rightPath).symm ((glue_path_equiv BL.rightPath) i)) =
      (glue_path_equiv BR.leftPath) i
  rw [Equiv.symm_apply_apply]



theorem glueIdentify_seam (i : Fin s) :
    glueIdentify BL BR (.inl (BL.rightPath.darts.get
      ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩)) =
    glueIdentify BL BR (.inr (BR.leftPath.darts.get
      ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩)) := by
  have hL : BL.map.toCombinatorialMap.edgeInv (BL.rightPath.darts.get
      ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩) ∉ BL.rightPath.darts :=
    glue_path_opposite_not_mem BL BL.rightPath (List.get_mem _ _)
  have hR : BR.leftPath.darts.get
      ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩ ∈ BR.leftPath.darts :=
    List.get_mem _ _
  simp only [glueIdentify, dite_eq_right hL, dite_eq_left hR]
  apply congrArg Sum.inl
  apply Subtype.ext
  have h := congrArg (fun a => ((glue_seam_equiv BL BR).symm a).val) (glue_seam_get BL BR i)
  simpa only [Equiv.symm_apply_apply] using h



theorem glueEdgeInv_identify (d : DL ⊕ DR) :
    glueEdgeInv BL BR (glueIdentify BL BR d) =
      glueIdentify BL BR (d.map BL.map.toCombinatorialMap.edgeInv BR.map.toCombinatorialMap.edgeInv) := by
  change glue_flip BL BR (glueIdentify BL BR d) = _
  rcases d with d | d
  · by_cases h : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts
    · have hR := (glue_seam_equiv BL BR ⟨_, h⟩).property
      have hnL := glue_path_opposite_not_mem BL BL.rightPath h
      simp only [BL.map.toCombinatorialMap.edgeInv_invol] at hnL
      simp [glueIdentify, glue_flip, h, hR, hnL,
        BL.map.toCombinatorialMap.edgeInv_invol, BR.map.toCombinatorialMap.edgeInv_invol]
    · simp only [glueIdentify, dite_eq_right h, glue_flip, Sum.map_inl]
  · by_cases h : d ∈ BR.leftPath.darts
    · have hL := ((glue_seam_equiv BL BR).symm ⟨d, h⟩).property
      have hnR := glue_path_opposite_not_mem BR BR.leftPath h
      simp [glueIdentify, glue_flip, h, hL, hnR,
        BL.map.toCombinatorialMap.edgeInv_invol]
    · simp only [glueIdentify, dite_eq_right h, glue_flip, Sum.map_inr]

 
theorem glueDirectedMap_toCombinatorialMap :
    (glueDirectedMap BL BR).toCombinatorialMap = glueCombinatorialMap BL BR := by
  simp only [glueDirectedMap]

 
theorem glueDirectedMap_outer : (glueDirectedMap BL BR).outer =
    glueIdentify BL BR (.inl (BL.leftPath.firstDart (by have := BL.left_length_pos; omega))) := by
  simp only [glueDirectedMap]

 
theorem glueTail_iff_edgeInv (d : GlueDart BL BR) :
    glueTail BL BR d ↔ ¬ glueTail BL BR (glueEdgeInv BL BR d) :=
  glue_tail_flip BL BR d

end DirectedDistances.PlanarMap
