module

public import DirectedDistances.PlanarMap.PlanarPathGlueCutRight
public import DirectedDistances.PlanarMap.PlanarPathGlueCutLeft
public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

attribute [local instance] Classical.propDecidable

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)

private theorem glueCutRot_faceSucc {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (d : D) : M.rot (M.faceSucc d) = M.edgeInv d := by
  change M.rot (M.rot.symm (M.edgeInv d)) = M.edgeInv d
  exact M.rot.apply_symm_apply _

private def glue_right_cut_corner (i : Fin (s + 1)) : DR :=
  if hi : i.val = 0 then
    BR.map.toCombinatorialMap.faceSucc (BR.map.toCombinatorialMap.edgeInv
      (BR.rightPath.firstDart (by have := BR.right_length_pos; omega)))
  else BR.map.toCombinatorialMap.faceSucc
    (BR.leftPath.darts.get ⟨i.val - 1, by rw [BR.leftPath.darts_length]; omega⟩)

private theorem glue_right_cut_corner_vertex (i : Fin (s + 1)) :
    dartTailVertex BR.map (glue_right_cut_corner BR i) =
      dartTailVertex BR.map (glueRightSeamVertexDart BR i) := by
  unfold glue_right_cut_corner
  split
  · rename_i hi
    have hv : dartTailVertex BR.map
        (BR.map.toCombinatorialMap.faceSucc (BR.map.toCombinatorialMap.edgeInv
          (BR.rightPath.firstDart (by have := BR.right_length_pos; omega)))) =
        dartTailVertex BR.map
          (BR.rightPath.firstDart (by have := BR.right_length_pos; omega)) := by
      apply Quotient.sound
      apply Equiv.Perm.sameCycle_apply_left.mp
      rw [glueCutRot_faceSucc, BR.map.toCombinatorialMap.edgeInv_invol]
    rw [hv, glueRightSeamVertexDart_vertex]
    have hs := (BR.rightPath.edge_step ⟨0, by
      rw [BR.rightPath.darts_length]; have := BR.right_length_pos; omega⟩).2.2.1.symm
    exact hs.trans (BR.rightPath.start_vertex.trans (by simpa only [hi] using
      BR.leftPath.start_vertex.symm))
  · rename_i hi
    have hv : dartTailVertex BR.map
        (BR.map.toCombinatorialMap.faceSucc
          (BR.leftPath.darts.get ⟨i.val - 1, by rw [BR.leftPath.darts_length]; omega⟩)) =
        dartHeadVertex BR.map
          (BR.leftPath.darts.get ⟨i.val - 1, by rw [BR.leftPath.darts_length]; omega⟩) := by
      apply Quotient.sound
      apply Equiv.Perm.sameCycle_apply_left.mp
      rw [glueCutRot_faceSucc]
    rw [hv, glueRightSeamVertexDart_vertex]
    have hs := (BR.leftPath.edge_step ⟨i.val - 1, by
      rw [BR.leftPath.darts_length]; omega⟩).2.2.2.symm
    have hadd : i.val - 1 + 1 = i.val := by omega
    simpa only [hadd] using hs

private theorem glue_right_cut_corner_unique (x y : DR)
    (hx : ∃ i, x = glue_right_cut_corner BR i)
    (hy : ∃ i, y = glue_right_cut_corner BR i)
    (hxy : BR.map.toCombinatorialMap.rot.SameCycle x y) : x = y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hv : dartTailVertex BR.map (glue_right_cut_corner BR i) =
      dartTailVertex BR.map (glue_right_cut_corner BR j) := Quotient.sound hxy
  rw [glue_right_cut_corner_vertex, glue_right_cut_corner_vertex] at hv
  have hij := (glueRightSeamVertexDart_sameCycle_iff BR i j).mp (Quotient.exact hv)
  rw [hij]

private theorem glue_rot_right_except_cut (d : DR)
    (hd : ¬ ∃ i, d = glue_right_cut_corner BR i) :
    (glueCombinatorialMap BL BR).rot (glueIdentify BL BR (.inr d)) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot d)) := by
  let e := BR.map.toCombinatorialMap.faceSucc.symm d
  have hed : BR.map.toCombinatorialMap.faceSucc e = d :=
    BR.map.toCombinatorialMap.faceSucc.apply_symm_apply d
  by_cases he : BR.map.IsOuter e
  · have hm := BR.outerSplit.2.1.mem_iff.mp (BR.outerSplit.1.2.1 e he)
    simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse] at hm
    rcases hm with hm | ⟨a, ha, hae⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      have hjs : j.val < s := by simpa only [BR.leftPath.darts_length] using j.isLt
      exfalso
      apply hd
      refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
      simp only [glue_right_cut_corner, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceDIte, Nat.add_sub_cancel]
      rw [← hed, ← hj]
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
      have hjr : j.val < r := by simpa only [BR.rightPath.darts_length] using j.isLt
      by_cases hjzero : j.val = 0
      · exfalso
        apply hd
        refine ⟨⟨0, by omega⟩, ?_⟩
        simp only [glue_right_cut_corner, ↓reduceDIte]
        rw [← hed, ← hae, ← hj]
        congr 3
        exact Fin.ext hjzero
      · have hsucc := outerFace_rightPath_successor BR (j.val - 1) (by omega)
        have hadd : j.val - 1 + 1 = j.val := by omega
        simp only [hadd] at hsucc
        have hdeq : d = BR.map.toCombinatorialMap.edgeInv
            (BR.rightPath.darts.get ⟨j.val - 1, by
              simpa only [BR.rightPath.darts_length] using (show j.val - 1 < r by omega)⟩) := by
          rw [← hed, ← hae, ← hj]
          exact hsucc
        have hrot : BR.map.toCombinatorialMap.rot d = BR.rightPath.darts.get j := by
          rw [← hed, glueCutRot_faceSucc, ← hae, ← hj,
            BR.map.toCombinatorialMap.edgeInv_invol]
        rw [hrot, hdeq]
        simpa only [hadd] using glue_rot_right_boundary_corner BL BR (j.val - 1) (by omega)
  · rw [← hed, glue_rot_right_inner_corner BL BR e he, glueCutRot_faceSucc]

private theorem glue_rot_iterate_tailVertex (n : ℕ) (g : GlueDart BL BR) :
    dartTailVertex (glueBase BL BR).map
        (((glueBase BL BR).map.toCombinatorialMap.rot :
          GlueDart BL BR → GlueDart BL BR)^[n] g) =
      dartTailVertex (glueBase BL BR).map g := by
  have hrot (x : GlueDart BL BR) :
      dartTailVertex (glueBase BL BR).map
          ((glueBase BL BR).map.toCombinatorialMap.rot x) =
        dartTailVertex (glueBase BL BR).map x := by
    apply Quotient.sound
    exact Equiv.Perm.SameCycle.rfl.apply_left
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hrot ((glueBase BL BR).map.toCombinatorialMap.rot^[n] g)).trans (ih g)

private def glue_left_cut_corner (i : Fin (s + 1)) : DL :=
  if hi : i.val < s then
    BL.map.toCombinatorialMap.faceSucc (BL.map.toCombinatorialMap.edgeInv
      (BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact hi⟩))
  else BL.map.toCombinatorialMap.faceSucc
    (BL.leftPath.darts.get ⟨ℓ - 1, by
      rw [BL.leftPath.darts_length]; have := BL.left_length_pos; omega⟩)

private theorem glue_left_cut_corner_vertex (i : Fin (s + 1)) :
    dartTailVertex BL.map (glue_left_cut_corner BL i) =
      dartTailVertex BL.map (glueLeftSeamVertexDart BL i) := by
  unfold glue_left_cut_corner
  split
  · rename_i hi
    apply Quotient.sound
    apply Equiv.Perm.sameCycle_apply_left.mp
    rw [glueCutRot_faceSucc, BL.map.toCombinatorialMap.edgeInv_invol]
    simpa only [glueLeftSeamVertexDart, dite_eq_left hi] using
      (Equiv.Perm.SameCycle.refl BL.map.toCombinatorialMap.rot
        (BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact hi⟩))
  · rename_i hi
    have his : i.val = s := by omega
    have hrot : dartTailVertex BL.map
        (BL.map.toCombinatorialMap.faceSucc
          (BL.leftPath.darts.get ⟨ℓ - 1, by
            rw [BL.leftPath.darts_length]; have := BL.left_length_pos; omega⟩)) =
        dartHeadVertex BL.map
          (BL.leftPath.darts.get ⟨ℓ - 1, by
            rw [BL.leftPath.darts_length]; have := BL.left_length_pos; omega⟩) := by
      apply Quotient.sound
      apply Equiv.Perm.sameCycle_apply_left.mp
      rw [glueCutRot_faceSucc]
    rw [hrot, glueLeftSeamVertexDart_vertex]
    have hv := (BL.leftPath.edge_step ⟨ℓ - 1, by
      rw [BL.leftPath.darts_length]; have := BL.left_length_pos; omega⟩).2.2.2.symm
    have hlast : ℓ - 1 + 1 = ℓ := by have := BL.left_length_pos; omega
    simp only [hlast] at hv
    exact hv.trans (BL.leftPath.end_vertex.trans (by simpa only [his] using
      BL.rightPath.end_vertex.symm))

private theorem glue_left_cut_corner_unique (x y : DL)
    (hx : ∃ i, x = glue_left_cut_corner BL i)
    (hy : ∃ i, y = glue_left_cut_corner BL i)
    (hxy : BL.map.toCombinatorialMap.rot.SameCycle x y) : x = y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hv : dartTailVertex BL.map (glue_left_cut_corner BL i) =
      dartTailVertex BL.map (glue_left_cut_corner BL j) := Quotient.sound hxy
  rw [glue_left_cut_corner_vertex, glue_left_cut_corner_vertex] at hv
  have hij := (glueLeftSeamVertexDart_sameCycle_iff BL i j).mp (Quotient.exact hv)
  rw [hij]

private theorem glue_rot_left_except_cut (d : DL)
    (hd : ¬ ∃ i, d = glue_left_cut_corner BL i) :
    (glueCombinatorialMap BL BR).rot (glueIdentify BL BR (.inl d)) =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot d)) := by
  let e := BL.map.toCombinatorialMap.faceSucc.symm d
  have hed : BL.map.toCombinatorialMap.faceSucc e = d :=
    BL.map.toCombinatorialMap.faceSucc.apply_symm_apply d
  by_cases he : BL.map.IsOuter e
  · have hm := BL.outerSplit.2.1.mem_iff.mp (BL.outerSplit.1.2.1 e he)
    simp only [List.append_nil, List.mem_append, List.mem_map, List.mem_reverse] at hm
    rcases hm with hm | ⟨a, ha, hae⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      have hjl : j.val < ℓ := by simpa only [BL.leftPath.darts_length] using j.isLt
      by_cases hjlast : j.val + 1 < ℓ
      · have hsucc := outerFace_leftPath_successor BL j.val hjlast
        have heq : e = BL.leftPath.darts.get j := hj.symm
        have hdeq : d = BL.leftPath.darts.get
            ⟨j.val + 1, by simpa only [BL.leftPath.darts_length] using hjlast⟩ := by
          rw [← hed, heq]
          exact hsucc
        have hr := glue_rot_left_boundary_corner BL BR j.val hjlast
        have hrot : BL.map.toCombinatorialMap.rot d =
            BL.map.toCombinatorialMap.edgeInv (BL.leftPath.darts.get j) := by
          rw [← hed, glueCutRot_faceSucc, heq]
        rw [hrot, hdeq]
        exact hr
      · exfalso
        apply hd
        refine ⟨⟨s, by omega⟩, ?_⟩
        simp only [glue_left_cut_corner, Nat.lt_irrefl, ↓reduceDIte]
        rw [← hed, ← hj]
        congr 2
        apply Fin.ext
        dsimp
        omega
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
      have hjs : j.val < s := by simpa only [BL.rightPath.darts_length] using j.isLt
      exfalso
      apply hd
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      rw [glue_left_cut_corner, dite_eq_left hjs, ← hed, ← hae, ← hj]
  · rw [← hed, glue_rot_left_inner_corner BL BR e he, glueCutRot_faceSucc]



theorem glueCutRight_rot_of_inner (d : DR) (hd : ¬ BR.map.IsOuter d) :
    (pathCutRightHalfMap (glueBase BL BR) (glueSeamPath BL BR)).rot
        ⟨glueIdentify BL BR (.inr d), glueIdentify_inr_mem_rightHalf BL BR d⟩ =
      ⟨glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot d)),
        glueIdentify_inr_mem_rightHalf BL BR _⟩ := by
  classical
  let S := pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR)
  let σ := (glueBase BL BR).map.toCombinatorialMap.rot
  let x : {d : GlueDart BL BR // d ∈ S} :=
    ⟨glueIdentify BL BR (.inr d), glueIdentify_inr_mem_rightHalf BL BR d⟩
  have hrot : σ x.1 = glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot d)) := by
    change (glueBase BL BR).map.toCombinatorialMap.rot
      (glueIdentify BL BR (.inr d)) = _
    rw [glueBase_map, glueDirectedMap_toCombinatorialMap]
    exact glue_rot_right_of_inner BL BR d hd
  have hmem : σ x.1 ∈ S := by
    rw [hrot]
    exact glueIdentify_inr_mem_rightHalf BL BR _
  have hfirst := firstReturnPerm_apply_of_mem σ S x hmem
  apply Subtype.ext
  change (firstReturnPerm σ S x).1 = _
  rw [hfirst]
  exact hrot



theorem glueCutRight_rot (d : DR) :
    (pathCutRightHalfMap (glueBase BL BR) (glueSeamPath BL BR)).rot
        ⟨glueIdentify BL BR (.inr d), glueIdentify_inr_mem_rightHalf BL BR d⟩ =
      ⟨glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot d)),
        glueIdentify_inr_mem_rightHalf BL BR _⟩ := by
  classical
  let S := pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR)
  let σ := (glueBase BL BR).map.toCombinatorialMap.rot
  let E : DR ≃ S := Equiv.ofBijective
    (fun e => ⟨glueIdentify BL BR (.inr e), glueIdentify_inr_mem_rightHalf BL BR e⟩)
    ⟨(fun e f h => glueIdentify_inr_injective BL BR (congrArg Subtype.val h)),
      (fun x => by
        obtain ⟨e, he⟩ := (glueIdentify_inr_image_iff BL BR x.1).mp x.2
        exact ⟨e, Subtype.ext he⟩)⟩
  have hE_val (e : DR) : (E e).1 = glueIdentify BL BR (.inr e) := rfl
  let q : Equiv.Perm DR := (E.trans (firstReturnPerm σ S)).trans E.symm
  have hq_action (e : DR) (he : ¬ ∃ i, e = glue_right_cut_corner BR i) :
      q e = BR.map.toCombinatorialMap.rot e := by
    change E.symm (firstReturnPerm σ S (E e)) = _
    apply E.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    have hnext : σ (glueIdentify BL BR (.inr e)) =
        glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot e)) := by
      change (glueBase BL BR).map.toCombinatorialMap.rot
        (glueIdentify BL BR (.inr e)) = _
      rw [glueBase_map, glueDirectedMap_toCombinatorialMap]
      exact glue_rot_right_except_cut BL BR e he
    have hmem : σ (E e).1 ∈ S := by
      change σ (glueIdentify BL BR (.inr e)) ∈ S
      rw [hnext]
      exact glueIdentify_inr_mem_rightHalf BL BR _
    change (firstReturnPerm σ S (E e)).1 =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot e))
    rw [firstReturnPerm_apply_of_mem σ S (E e) hmem]
    exact hnext
  have hq_all : ∀ e : DR, q e = BR.map.toCombinatorialMap.rot e := by
    intro e
    by_cases he : ∃ i, e = glue_right_cut_corner BR i
    · by_contra hne
      obtain ⟨d, hd⟩ := q.surjective (BR.map.toCombinatorialMap.rot e)
      have hde : d ≠ e := by
        intro h
        subst d
        exact hne hd
      by_cases hdcut : ∃ j, d = glue_right_cut_corner BR j
      · obtain ⟨i, hi⟩ := he
        obtain ⟨j, hj⟩ := hdcut
        let x := E d
        let k := firstReturnTime σ S x
        have hsub : firstReturnPerm σ S x = E (BR.map.toCombinatorialMap.rot e) := by
          calc
            firstReturnPerm σ S x = E (q d) := by
              simp [q, x, E, Equiv.trans_apply, Equiv.apply_symm_apply]
            _ = E (BR.map.toCombinatorialMap.rot e) := congrArg E hd
        have hret : (σ : GlueDart BL BR → GlueDart BL BR)^[k]
            (glueIdentify BL BR (.inr d)) =
              glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot e)) := by
          calc
            _ = (firstReturnPerm σ S x).1 :=
              (firstReturn_characterization σ S x).1
            _ = (E (BR.map.toCombinatorialMap.rot e)).1 :=
              congrArg Subtype.val hsub
        have htail :
            dartTailVertex (glueBase BL BR).map
                (glueIdentify BL BR (.inr d)) =
              dartTailVertex (glueBase BL BR).map
                (glueIdentify BL BR (.inr e)) := by
          calc
            _ = dartTailVertex (glueBase BL BR).map
                (((σ : GlueDart BL BR → GlueDart BL BR)^[k])
                  (glueIdentify BL BR (.inr d))) :=
                    (glue_rot_iterate_tailVertex BL BR k _).symm
            _ = dartTailVertex (glueBase BL BR).map
                (glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot e))) :=
                  congrArg (dartTailVertex (glueBase BL BR).map) hret
            _ = dartTailVertex (glueBase BL BR).map
                (glueIdentify BL BR (.inr e)) := by
                  apply Quotient.sound
                  rw [glueBase_map, glueDirectedMap_toCombinatorialMap]
                  exact glueIdentify_right_sameCycle BL BR _ _
                    (Equiv.Perm.SameCycle.rfl.apply_left)
        have hv : glueVertexMap BL BR (.inr (dartTailVertex BR.map d)) =
            glueVertexMap BL BR (.inr (dartTailVertex BR.map e)) := by
          have hclass := htail
          change Quotient.mk (Equiv.Perm.SameCycle.setoid
              ((glueBase BL BR).map.toCombinatorialMap.rot))
                (glueIdentify BL BR (.inr d)) =
            Quotient.mk (Equiv.Perm.SameCycle.setoid
              ((glueBase BL BR).map.toCombinatorialMap.rot))
                (glueIdentify BL BR (.inr e)) at hclass
          rw [glueBase_map, glueDirectedMap_toCombinatorialMap] at hclass
          simpa [glueVertexMap, vertexClass, dartTailVertex] using hclass
        have hcycle : BR.map.toCombinatorialMap.rot.SameCycle d e :=
          Quotient.exact (glueVertexMap_right_injective BL BR hv)
        have hde' := glue_right_cut_corner_unique BR d e
          ⟨j, hj⟩ ⟨i, hi⟩ hcycle
        exact hde hde'
      · have hact := hq_action d hdcut
        have hrot : BR.map.toCombinatorialMap.rot d =
            BR.map.toCombinatorialMap.rot e := hact.symm.trans hd
        exact hde (BR.map.toCombinatorialMap.rot.injective hrot)
    · exact hq_action e he
  have hqd := hq_all d
  apply Subtype.ext
  change (firstReturnPerm σ S (E d)).1 =
    glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.rot d))
  have hv := congrArg Subtype.val (congrArg E hqd)
  have hv' : (firstReturnPerm σ S (E d)).1 = (E (BR.map.toCombinatorialMap.rot d)).1 := by
    simpa [q, Equiv.trans_apply, Equiv.apply_symm_apply] using hv
  rw [hE_val (BR.map.toCombinatorialMap.rot d)] at hv'
  have hEd : E d =
      ⟨glueIdentify BL BR (.inr d), glueIdentify_inr_mem_rightHalf BL BR d⟩ := by
    apply Subtype.ext
    exact hE_val d
  rw [hEd] at hv'
  change (firstReturnPerm σ S
      ⟨glueIdentify BL BR (.inr d), glueIdentify_inr_mem_rightHalf BL BR d⟩).1 = _
  exact hv'



theorem glueCutLeft_rot_of_inner (d : DL) (hd : ¬ BL.map.IsOuter d) :
    (pathCutLeftHalfMap (glueBase BL BR) (glueSeamPath BL BR)).rot
        ⟨glueIdentify BL BR (.inl d), glueIdentify_inl_mem_leftHalf BL BR d⟩ =
      ⟨glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot d)),
        glueIdentify_inl_mem_leftHalf BL BR _⟩ := by
  classical
  let S := pathCutLeftHalfDarts (glueBase BL BR) (glueSeamPath BL BR)
  let σ := (glueBase BL BR).map.toCombinatorialMap.rot
  let x : {d : GlueDart BL BR // d ∈ S} :=
    ⟨glueIdentify BL BR (.inl d), glueIdentify_inl_mem_leftHalf BL BR d⟩
  have hrot : σ x.1 = glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot d)) := by
    change (glueBase BL BR).map.toCombinatorialMap.rot
      (glueIdentify BL BR (.inl d)) = _
    rw [glueBase_map, glueDirectedMap_toCombinatorialMap]
    exact glue_rot_left_of_inner BL BR d hd
  have hmem : σ x.1 ∈ S := by
    rw [hrot]
    exact glueIdentify_inl_mem_leftHalf BL BR _
  have hfirst := firstReturnPerm_apply_of_mem σ S x hmem
  apply Subtype.ext
  change (firstReturnPerm σ S x).1 = _
  rw [hfirst]
  exact hrot



theorem glueCutLeft_rot (d : DL) :
    (pathCutLeftHalfMap (glueBase BL BR) (glueSeamPath BL BR)).rot
        ⟨glueIdentify BL BR (.inl d), glueIdentify_inl_mem_leftHalf BL BR d⟩ =
      ⟨glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot d)),
        glueIdentify_inl_mem_leftHalf BL BR _⟩ := by
  classical
  let S := pathCutLeftHalfDarts (glueBase BL BR) (glueSeamPath BL BR)
  let σ := (glueBase BL BR).map.toCombinatorialMap.rot
  let E : DL ≃ S := Equiv.ofBijective
    (fun e => ⟨glueIdentify BL BR (.inl e), glueIdentify_inl_mem_leftHalf BL BR e⟩)
    ⟨(fun e f h => glueIdentify_inl_injective BL BR (congrArg Subtype.val h)),
      (fun x => by
        obtain ⟨e, he⟩ := (glueIdentify_inl_image_iff BL BR x.1).mp x.2
        exact ⟨e, Subtype.ext he⟩)⟩
  let q : Equiv.Perm DL := (E.trans (firstReturnPerm σ S)).trans E.symm
  have hE_val (e : DL) : (E e).1 = glueIdentify BL BR (.inl e) := rfl
  have hq_action (e : DL) (he : ¬ ∃ i, e = glue_left_cut_corner BL i) :
      q e = BL.map.toCombinatorialMap.rot e := by
    change E.symm (firstReturnPerm σ S (E e)) = _
    apply E.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    have hnext : σ (glueIdentify BL BR (.inl e)) =
        glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot e)) := by
      change (glueBase BL BR).map.toCombinatorialMap.rot
        (glueIdentify BL BR (.inl e)) = _
      rw [glueBase_map, glueDirectedMap_toCombinatorialMap]
      exact glue_rot_left_except_cut BL BR e he
    have hmem : σ (E e).1 ∈ S := by
      change σ (glueIdentify BL BR (.inl e)) ∈ S
      rw [hnext]
      exact glueIdentify_inl_mem_leftHalf BL BR _
    change (firstReturnPerm σ S (E e)).1 =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot e))
    rw [firstReturnPerm_apply_of_mem σ S (E e) hmem]
    exact hnext
  have hq_all : ∀ e : DL, q e = BL.map.toCombinatorialMap.rot e := by
    intro e
    by_cases he : ∃ i, e = glue_left_cut_corner BL i
    · by_contra hne
      obtain ⟨d, hd⟩ := q.surjective (BL.map.toCombinatorialMap.rot e)
      have hde : d ≠ e := by
        intro h
        subst d
        exact hne hd
      by_cases hdcut : ∃ j, d = glue_left_cut_corner BL j
      · obtain ⟨i, hi⟩ := he
        obtain ⟨j, hj⟩ := hdcut
        let x := E d
        let k := firstReturnTime σ S x
        have hsub : firstReturnPerm σ S x = E (BL.map.toCombinatorialMap.rot e) := by
          calc
            firstReturnPerm σ S x = E (q d) := by
              simp [q, x, E, Equiv.trans_apply, Equiv.apply_symm_apply]
            _ = E (BL.map.toCombinatorialMap.rot e) := congrArg E hd
        have hret : (σ : GlueDart BL BR → GlueDart BL BR)^[k]
            (glueIdentify BL BR (.inl d)) =
              glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot e)) := by
          calc
            _ = (firstReturnPerm σ S x).1 :=
              (firstReturn_characterization σ S x).1
            _ = (E (BL.map.toCombinatorialMap.rot e)).1 :=
              congrArg Subtype.val hsub
        have htail :
            dartTailVertex (glueBase BL BR).map
                (glueIdentify BL BR (.inl d)) =
              dartTailVertex (glueBase BL BR).map
                (glueIdentify BL BR (.inl e)) := by
          calc
            _ = dartTailVertex (glueBase BL BR).map
                (((σ : GlueDart BL BR → GlueDart BL BR)^[k])
                  (glueIdentify BL BR (.inl d))) :=
                    (glue_rot_iterate_tailVertex BL BR k _).symm
            _ = dartTailVertex (glueBase BL BR).map
                (glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot e))) :=
                  congrArg (dartTailVertex (glueBase BL BR).map) hret
            _ = dartTailVertex (glueBase BL BR).map
                (glueIdentify BL BR (.inl e)) := by
                  apply Quotient.sound
                  rw [glueBase_map, glueDirectedMap_toCombinatorialMap]
                  exact glueIdentify_left_sameCycle BL BR _ _
                    (Equiv.Perm.SameCycle.rfl.apply_left)
        have hv : glueVertexMap BL BR (.inl (dartTailVertex BL.map d)) =
            glueVertexMap BL BR (.inl (dartTailVertex BL.map e)) := by
          have hclass := htail
          change Quotient.mk (Equiv.Perm.SameCycle.setoid
              ((glueBase BL BR).map.toCombinatorialMap.rot))
                (glueIdentify BL BR (.inl d)) =
            Quotient.mk (Equiv.Perm.SameCycle.setoid
              ((glueBase BL BR).map.toCombinatorialMap.rot))
                (glueIdentify BL BR (.inl e)) at hclass
          rw [glueBase_map, glueDirectedMap_toCombinatorialMap] at hclass
          simpa [glueVertexMap, vertexClass, dartTailVertex] using hclass
        have hcycle : BL.map.toCombinatorialMap.rot.SameCycle d e :=
          Quotient.exact (glueVertexMap_left_injective BL BR hv)
        have hde' := glue_left_cut_corner_unique BL d e
          ⟨j, hj⟩ ⟨i, hi⟩ hcycle
        exact hde hde'
      · have hact := hq_action d hdcut
        have hrot : BL.map.toCombinatorialMap.rot d =
            BL.map.toCombinatorialMap.rot e := hact.symm.trans hd
        exact hde (BL.map.toCombinatorialMap.rot.injective hrot)
    · exact hq_action e he
  have hqd := hq_all d
  apply Subtype.ext
  change (firstReturnPerm σ S (E d)).1 =
    glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.rot d))
  have hv := congrArg Subtype.val (congrArg E hqd)
  have hv' : (firstReturnPerm σ S (E d)).1 = (E (BL.map.toCombinatorialMap.rot d)).1 := by
    simpa [q, Equiv.trans_apply, Equiv.apply_symm_apply] using hv
  rw [hE_val (BL.map.toCombinatorialMap.rot d)] at hv'
  have hEd : E d =
      ⟨glueIdentify BL BR (.inl d), glueIdentify_inl_mem_leftHalf BL BR d⟩ := by
    apply Subtype.ext
    exact hE_val d
  rw [hEd] at hv'
  exact hv'

end DirectedDistances.PlanarMap
