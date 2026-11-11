module

public import DirectedDistances.PlanarMap.PlanarPathGlueGeodesic
public import DirectedDistances.PlanarMap.PlanarPathGlueBasePackage
public import DirectedDistances.PlanarMap.PlanarPathCutRightBase
public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap
public import DirectedDistances.PlanarMap.PlanarPathCutSeparation
public import DirectedDistances.PlanarMap.PlanarPathCutHalves

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PlanarMap

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)

private theorem glueCutRight_path_darts_nodup {D : Type*} [Fintype D]
    [DecidableEq D] {M : DirectedMapWithMissing D} {a b : MapVertex M}
    {n : ℕ} (P : SimpleDirectedDartPath M a b n) : P.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hv := (P.edge_step i).2.2.1.trans
    ((congrArg (dartTailVertex M) hij).trans (P.edge_step j).2.2.1.symm)
  exact Fin.ext (congrArg (fun q : Fin P.vertices.length => q.val)
    (P.vertices_nodup.get_inj_iff.mp hv))

private theorem glueCutRight_path_opposite_not_mem {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ P.darts) : B.map.toCombinatorialMap.edgeInv d ∉ P.darts := by
  have htail : B.map.tail d := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    rw [← hi]
    exact (P.edge_step i).2.1
  intro hflip
  have hflipTail : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hflip
    rw [← hi]
    exact (P.edge_step i).2.1
  exact ((B.map.tail_iff d (B.noMissingDarts d)).mp htail) hflipTail

private theorem glueCutRight_tail_not_rightPath {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (ht : B.map.tail d) : B.map.toCombinatorialMap.edgeInv d ∉ B.rightPath.darts := by
  intro h
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
  exact (B.map.tail_iff d (B.noMissingDarts d)).mp ht
    (hi ▸ (B.rightPath.edge_step i).2.1)

private theorem glueCutRight_leftPath_outer {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ B.leftPath.darts) : B.map.IsOuter d := by
  apply B.outerSplit.1.1 d
  apply B.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append]
  exact Or.inl hd

private theorem glueCutRight_leftDarts_self_subset_path {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ pathCutLeftDarts B B.leftPath) : d ∈ B.leftPath.darts := by
  obtain ⟨a, ha, hreach⟩ := hd
  have haPath : a ∈ B.leftPath.darts := by
    rcases ha with ha | ha
    · exact (mem_pathCutLeftOuterArc_iff B a).mp ha
    · exact ha
  induction hreach with
  | refl => exact haPath
  | @tail b c hreach hstep ih =>
      change (c = B.map.toCombinatorialMap.faceSucc b ∧
          (¬ B.map.IsOuter b ∨
            (b ∈ pathCutLeftOuterArc B ∧ c ∈ pathCutLeftOuterArc B))) ∨
        (c = B.map.toCombinatorialMap.edgeInv b ∧
          b ∉ pathCutSeamDarts B B.leftPath) at hstep
      rcases hstep with ⟨hEq, hface⟩ | ⟨_hEq, hseam⟩
      · rcases hface with hinner | ⟨_houter, hnext⟩
        · exact False.elim (hinner (glueCutRight_leftPath_outer B ih))
        · exact (mem_pathCutLeftOuterArc_iff B c).mp hnext
      · exact False.elim (hseam (Or.inl ih))

private theorem glueCutRight_self_leftPath_half_univ {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    d ∈ pathCutRightHalfDarts B B.leftPath := by
  rcases pathCut_halves_cover B B.leftPath d with hleft | hright
  · change d ∈ pathCutLeftDarts B B.leftPath ∨
      d ∈ pathCutSeamDarts B B.leftPath at hleft
    rcases hleft with hleft | hseam
    · exact Or.inr (Or.inl (glueCutRight_leftDarts_self_subset_path B hleft))
    · exact Or.inr hseam
  · change d ∈ pathCutRightDarts B B.leftPath ∪
      pathCutSeamDarts B B.leftPath at hright
    exact hright

private theorem glueCutRight_inr_inner_not_outer {d : DR}
    (hinner : ¬ BR.map.IsOuter d) :
    ¬ (glueBase BL BR).map.IsOuter (glueIdentify BL BR (.inr d)) := by
  intro hout
  have hcycleRoot : (glueCombinatorialMap BL BR).faceSucc.SameCycle
      (glueIdentify BL BR (.inr d))
      (glueIdentify BL BR (.inl
        (BL.leftPath.firstDart (by have := BL.left_length_pos; omega)))) := by
    change (glueDirectedMap BL BR).toCombinatorialMap.IsOuter
      (glueDirectedMap BL BR).outer (glueIdentify BL BR (.inr d)) at hout
    rw [glueDirectedMap_toCombinatorialMap,
      glueDirectedMap_outer] at hout
    exact hout.symm
  have hcycle : (glueCombinatorialMap BL BR).faceSucc.SameCycle
      (glueIdentify BL BR (.inr d)) ((glueBase BL BR).map.outer) := by
    simpa only [glueBase_map, glueDirectedMap_outer] using hcycleRoot
  obtain ⟨e, hde, heq⟩ :=
    (glue_right_inner_face_cycle BL BR d hinner ((glueBase BL BR).map.outer)).mp hcycle
  have heinner : ¬ BR.map.IsOuter e := by
    intro heouter
    exact hinner (hde.trans heouter.symm).symm
  have hekeep : e ∉ BR.leftPath.darts := by
    intro hePath
    exact heinner (glueCutRight_leftPath_outer BR hePath)
  have hfirst :
      BL.leftPath.firstDart (by have := BL.left_length_pos; omega) ∈ BL.leftPath.darts := by
    dsimp [SimpleDirectedDartPath.firstDart]
    exact List.get_mem _ _
  have hfirstTail : BL.map.tail
      (BL.leftPath.firstDart (by have := BL.left_length_pos; omega)) := by
    dsimp [SimpleDirectedDartPath.firstDart]
    exact (BL.leftPath.edge_step ⟨0, by
      rw [BL.leftPath.darts_length]
      have := BL.left_length_pos
      omega⟩).2.1
  have hfirstKeep := glueCutRight_tail_not_rightPath BL hfirstTail
  have houterEq : glueIdentify BL BR (.inr e) =
      glueIdentify BL BR (.inl
        (BL.leftPath.firstDart (by have := BL.left_length_pos; omega))) := by
    simpa only [glueBase_map, glueDirectedMap_outer] using heq
  rw [glueIdentify_inr_kept BL BR ⟨e, hekeep⟩,
    glueIdentify_inl_kept BL BR ⟨_, hfirstKeep⟩] at houterEq
  cases houterEq

private theorem glueCutRight_outerArc_image {d : DR}
    (hd : d ∈ pathCutRightOuterArc BR) :
    glueIdentify BL BR (.inr d) ∈ pathCutRightOuterArc (glueBase BL BR) := by
  obtain ⟨p, hp, hpd⟩ := List.mem_map.mp
    ((mem_pathCutRightOuterArc_iff BR d).mp hd)
  have hp' : p ∈ BR.rightPath.darts.reverse := hp
  have hrightPath : glueIdentify BL BR (.inr p) ∈
      (glueBase BL BR).rightPath.darts.reverse := by
    rw [glueBase_rightPath_darts]
    apply List.mem_reverse.mpr
    rw [List.mem_map]
    exact ⟨p, List.mem_reverse.mp hp', rfl⟩
  apply (mem_pathCutRightOuterArc_iff (glueBase BL BR) _).2
  rw [List.mem_map]
  refine ⟨glueIdentify BL BR (.inr p), hrightPath, ?_⟩
  have hedge : (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inr p)) = glueIdentify BL BR
        (.inr (BR.map.toCombinatorialMap.edgeInv p)) := by
    rw [glueBase_map, glueDirectedMap_toCombinatorialMap,
      glueCombinatorialMap_edgeInv]
    exact glueEdgeInv_identify BL BR (.inr p)
  rw [← hpd]
  exact hedge

private theorem glueCutRight_edgeInv_identify (d : DR) :
    (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inr d)) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d)) := by
  rw [glueBase_map, glueDirectedMap_toCombinatorialMap,
    glueCombinatorialMap_edgeInv]
  exact glueEdgeInv_identify BL BR (.inr d)

private theorem glueCutRight_seamPath_dart_inl {g : GlueDart BL BR}
    (hg : g ∈ (glueSeamPath BL BR).darts) : ∃ a, g = Sum.inl a := by
  rw [glueSeamPath_darts] at hg
  obtain ⟨d, hd, hgd⟩ := List.mem_map.mp hg
  have hkeep := glueCutRight_path_opposite_not_mem BL BL.rightPath hd
  refine ⟨⟨d, hkeep⟩, ?_⟩
  rw [← hgd, glueIdentify_inl_kept BL BR ⟨d, hkeep⟩]

private theorem glueCutRight_source_notSeam_to_glue_notSeam {d : DR}
    (hd : d ∉ pathCutSeamDarts BR BR.leftPath) :
    glueIdentify BL BR (.inr d) ∉
      pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR) := by
  change ¬ (d ∈ BR.leftPath.darts ∨
    BR.map.toCombinatorialMap.edgeInv d ∈ BR.leftPath.darts) at hd
  have hparts := not_or.mp hd
  have hg : glueIdentify BL BR (.inr d) = .inr ⟨d, hparts.1⟩ :=
    glueIdentify_inr_kept BL BR ⟨d, hparts.1⟩
  have he : glueIdentify BL BR
      (.inr (BR.map.toCombinatorialMap.edgeInv d)) =
      .inr ⟨BR.map.toCombinatorialMap.edgeInv d, hparts.2⟩ :=
    glueIdentify_inr_kept BL BR ⟨_, hparts.2⟩
  intro hseam
  change glueIdentify BL BR (.inr d) ∈ (glueSeamPath BL BR).darts ∨
    (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inr d)) ∈ (glueSeamPath BL BR).darts at hseam
  rcases hseam with hpath | hflip
  · obtain ⟨a, ha⟩ := glueCutRight_seamPath_dart_inl BL BR hpath
    rw [hg] at ha
    cases ha
  · rw [glueCutRight_edgeInv_identify BL BR] at hflip
    obtain ⟨a, ha⟩ := glueCutRight_seamPath_dart_inl BL BR hflip
    rw [he] at ha
    cases ha

private theorem glueCutRight_inr_seam_inl {d : DR}
    (hd : d ∈ BR.leftPath.darts) :
    ∃ a : {d : DL // BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts},
      glueIdentify BL BR (.inr d) = Sum.inl a := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hi' : i.val < s := by simpa [BR.leftPath.darts_length] using i.isLt
  let i' : Fin s := ⟨i.val, hi'⟩
  let bi : Fin BL.rightPath.darts.length := ⟨i'.val, by
    rw [BL.rightPath.darts_length]
    exact i'.isLt⟩
  have hbi : BL.rightPath.darts.get bi =
      BL.rightPath.darts.get ⟨i'.val, by
        rw [BL.rightPath.darts_length]
        exact i'.isLt⟩ := rfl
  have hri : BR.leftPath.darts.get ⟨i'.val, by
      rw [BR.leftPath.darts_length]
      exact i'.isLt⟩ = BR.leftPath.darts.get i :=
    congrArg _ (Fin.ext rfl)
  have hkeep := glueCutRight_path_opposite_not_mem BL BL.rightPath
    (List.get_mem _ bi)
  refine ⟨⟨BL.rightPath.darts.get bi, hkeep⟩, ?_⟩
  calc
    glueIdentify BL BR (.inr d) =
        glueIdentify BL BR (.inr (BR.leftPath.darts.get i)) :=
          congrArg (fun x => glueIdentify BL BR (.inr x)) hi.symm
    _ = glueIdentify BL BR (.inl (BL.rightPath.darts.get bi)) := by
          rw [← hri]
          simpa [bi] using (glueIdentify_seam BL BR i').symm
    _ = Sum.inl ⟨BL.rightPath.darts.get bi, hkeep⟩ :=
          glueIdentify_inl_kept BL BR ⟨_, hkeep⟩

private theorem glueCutRight_inr_seamPath_mem {d : DR}
    (hd : d ∈ BR.leftPath.darts) :
    glueIdentify BL BR (.inr d) ∈ (glueSeamPath BL BR).darts := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hi' : i.val < s := by simpa [BR.leftPath.darts_length] using i.isLt
  let i' : Fin s := ⟨i.val, hi'⟩
  let bi : Fin BL.rightPath.darts.length := ⟨i'.val, by
    rw [BL.rightPath.darts_length]
    exact i'.isLt⟩
  let ci : Fin BR.leftPath.darts.length := ⟨i'.val, by
    rw [BR.leftPath.darts_length]
    exact i'.isLt⟩
  have hci : BR.leftPath.darts.get ci = BR.leftPath.darts.get i :=
    congrArg _ (Fin.ext rfl)
  rw [glueSeamPath_darts]
  apply List.mem_map.mpr
  refine ⟨BL.rightPath.darts.get bi, List.get_mem _ bi, ?_⟩
  calc
    glueIdentify BL BR (.inl (BL.rightPath.darts.get bi)) =
        glueIdentify BL BR (.inr (BR.leftPath.darts.get ci)) := by
          simpa [bi, ci] using glueIdentify_seam BL BR i'
    _ = glueIdentify BL BR (.inr (BR.leftPath.darts.get i)) := by rw [hci]
    _ = glueIdentify BL BR (.inr d) :=
          congrArg (fun x => glueIdentify BL BR (.inr x)) hi

private theorem glueCutRight_inr_sourceSeam_mem_half {d : DR}
    (hd : d ∈ pathCutSeamDarts BR BR.leftPath) :
    glueIdentify BL BR (.inr d) ∈
      pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR) := by
  change d ∈ BR.leftPath.darts ∨
    BR.map.toCombinatorialMap.edgeInv d ∈ BR.leftPath.darts at hd
  rcases hd with hd | hd
  · change glueIdentify BL BR (.inr d) ∈
      pathCutRightDarts (glueBase BL BR) (glueSeamPath BL BR) ∪
        pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR)
    exact Or.inr (Or.inl (glueCutRight_inr_seamPath_mem BL BR hd))
  · have hpath := glueCutRight_inr_seamPath_mem BL BR hd
    have hflip :
        (glueBase BL BR).map.toCombinatorialMap.edgeInv
          (glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d))) =
        glueIdentify BL BR (.inr d) := by
      calc
        (glueBase BL BR).map.toCombinatorialMap.edgeInv
            (glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d))) =
          glueEdgeInv BL BR
            (glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d))) := by
              rw [glueBase_map, glueDirectedMap_toCombinatorialMap,
                glueCombinatorialMap_edgeInv]
        _ = glueIdentify BL BR
            (.inr (BR.map.toCombinatorialMap.edgeInv
              (BR.map.toCombinatorialMap.edgeInv d))) :=
              glueEdgeInv_identify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d))
        _ = glueIdentify BL BR (.inr d) := by
              rw [BR.map.toCombinatorialMap.edgeInv_invol]
    have hmem := pathCutRightHalf_edgeInv_mem (glueBase BL BR)
      (glueSeamPath BL BR) (Or.inr (Or.inl hpath))
    simpa only [hflip] using hmem

private theorem glueCutRight_sourceRightDarts_mem {d : DR}
    (hd : d ∈ pathCutRightDarts BR BR.leftPath) :
    glueIdentify BL BR (.inr d) ∈
      pathCutRightDarts (glueBase BL BR) (glueSeamPath BL BR) := by
  obtain ⟨a, ha, hreach⟩ := hd
  have hstart : glueIdentify BL BR (.inr a) ∈
      pathCutRightDarts (glueBase BL BR) (glueSeamPath BL BR) := by
    change a ∈ pathCutRightOuterArc BR ∨
      ∃ p ∈ BR.leftPath.darts,
        a = BR.map.toCombinatorialMap.edgeInv p at ha
    rcases ha with houter | ⟨p, hp, hap⟩
    · exact ⟨glueIdentify BL BR (.inr a), Or.inl
        (glueCutRight_outerArc_image BL BR houter), Relation.ReflTransGen.refl⟩
    · have hpath := glueCutRight_inr_seamPath_mem BL BR hp
      have hflip := pathCut_pathDart_flip_mem_right (glueBase BL BR)
        (glueSeamPath BL BR) hpath
      have hedge := glueCutRight_edgeInv_identify BL BR p
      rw [hedge] at hflip
      rw [hap]
      exact hflip
  induction hreach with
  | refl => exact hstart
  | @tail b c hreach hstep ih =>
      change (c = BR.map.toCombinatorialMap.faceSucc b ∧
          (¬ BR.map.IsOuter b ∨
            (b ∈ pathCutRightOuterArc BR ∧ c ∈ pathCutRightOuterArc BR))) ∨
        (c = BR.map.toCombinatorialMap.edgeInv b ∧
          b ∉ pathCutSeamDarts BR BR.leftPath) at hstep
      rcases hstep with ⟨hEq, hface⟩ | ⟨hEq, hseam⟩
      · rcases hface with hinner | ⟨_houter, houterNext⟩
        · have hinnerG := glueCutRight_inr_inner_not_outer BL BR hinner
          have hfaceG :
              (glueBase BL BR).map.toCombinatorialMap.faceSucc
                (glueIdentify BL BR (.inr b)) = glueIdentify BL BR (.inr c) := by
            rw [glueBase_map, glueDirectedMap_toCombinatorialMap,
              glue_faceSucc_right_inner BL BR b hinner]
            exact congrArg (fun x => glueIdentify BL BR (.inr x)) hEq.symm
          have hnext := pathCutRight_faceSucc_mem_of_inner (glueBase BL BR)
            (glueSeamPath BL BR) ih hinnerG
          rw [hfaceG] at hnext
          exact hnext
        · exact ⟨glueIdentify BL BR (.inr c), Or.inl
            (glueCutRight_outerArc_image BL BR houterNext),
            Relation.ReflTransGen.refl⟩
      · have hnotSeam := glueCutRight_source_notSeam_to_glue_notSeam BL BR hseam
        have hnext := pathCutRight_edgeInv_mem (glueBase BL BR)
          (glueSeamPath BL BR) ih hnotSeam
        rw [glueCutRight_edgeInv_identify BL BR, ← hEq] at hnext
        exact hnext



theorem glueIdentify_inr_mem_rightHalf (d : DR) :
    glueIdentify BL BR (.inr d) ∈
      pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR) := by
  have hall := glueCutRight_self_leftPath_half_univ BR d
  change d ∈ pathCutRightDarts BR BR.leftPath ∨
    d ∈ pathCutSeamDarts BR BR.leftPath at hall
  rcases hall with hright | hseam
  · exact Or.inl (glueCutRight_sourceRightDarts_mem BL BR hright)
  · exact glueCutRight_inr_sourceSeam_mem_half BL BR hseam



theorem glueIdentify_inr_injective :
    Function.Injective (fun d : DR => glueIdentify BL BR (.inr d)) := by
  intro d e h
  change glueIdentify BL BR (.inr d) = glueIdentify BL BR (.inr e) at h
  by_cases hd : d ∈ BR.leftPath.darts
  · by_cases he : e ∈ BR.leftPath.darts
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
      have hi' : i.val < s := by simpa [BR.leftPath.darts_length] using i.isLt
      have hj' : j.val < s := by simpa [BR.leftPath.darts_length] using j.isLt
      let i' : Fin s := ⟨i.val, hi'⟩
      let j' : Fin s := ⟨j.val, hj'⟩
      let bi : Fin BL.rightPath.darts.length := ⟨i'.val, by
        rw [BL.rightPath.darts_length]
        exact i'.isLt⟩
      let bj : Fin BL.rightPath.darts.length := ⟨j'.val, by
        rw [BL.rightPath.darts_length]
        exact j'.isLt⟩
      let ci : Fin BR.leftPath.darts.length := ⟨i'.val, by
        rw [BR.leftPath.darts_length]
        exact i'.isLt⟩
      let cj : Fin BR.leftPath.darts.length := ⟨j'.val, by
        rw [BR.leftPath.darts_length]
        exact j'.isLt⟩
      have hseam := glueIdentify_seam BL BR i'
      have hseam' := glueIdentify_seam BL BR j'
      have hci : BR.leftPath.darts.get ci = BR.leftPath.darts.get i :=
        congrArg _ (Fin.ext rfl)
      have hcj : BR.leftPath.darts.get cj = BR.leftPath.darts.get j :=
        congrArg _ (Fin.ext rfl)
      rw [hi.symm, hj.symm] at h
      rw [← hci, ← hcj] at h
      have hleft : glueIdentify BL BR (.inl
          (BL.rightPath.darts.get bi)) = glueIdentify BL BR (.inl
          (BL.rightPath.darts.get bj)) := by
        calc
          glueIdentify BL BR (.inl (BL.rightPath.darts.get bi)) =
              glueIdentify BL BR (.inr (BR.leftPath.darts.get ci)) := by
                simpa [bi, ci] using hseam
          _ = glueIdentify BL BR (.inr (BR.leftPath.darts.get j)) := by
                rw [← hcj]
                exact h
          _ = glueIdentify BL BR (.inl (BL.rightPath.darts.get bj)) := by
                simpa [bj, cj] using hseam'.symm
      have hiKeep := glueCutRight_path_opposite_not_mem BL BL.rightPath
        (List.get_mem _ bi)
      have hjKeep := glueCutRight_path_opposite_not_mem BL BL.rightPath
        (List.get_mem _ bj)
      rw [glueIdentify_inl_kept BL BR ⟨_, hiKeep⟩,
        glueIdentify_inl_kept BL BR ⟨_, hjKeep⟩] at hleft
      have hget : BL.rightPath.darts.get bi = BL.rightPath.darts.get bj :=
        congrArg Subtype.val (Sum.inl.inj hleft)
      have hbij : bi = bj :=
        (glueCutRight_path_darts_nodup BL.rightPath).get_inj_iff.mp hget
      have hij : i = j := Fin.ext (by
        have hv := congrArg Fin.val hbij
        simpa [bi, bj, i', j'] using hv)
      have hde : BR.leftPath.darts.get i = BR.leftPath.darts.get j :=
        congrArg (fun k : Fin BR.leftPath.darts.length =>
          BR.leftPath.darts.get k) hij
      exact hi.symm.trans (hde.trans hj)
    · obtain ⟨a, ha⟩ := glueCutRight_inr_seam_inl BL BR hd
      have hb := glueIdentify_inr_kept BL BR ⟨e, he⟩
      rw [ha, hb] at h
      cases h
  · by_cases he : e ∈ BR.leftPath.darts
    · obtain ⟨a, ha⟩ := glueCutRight_inr_seam_inl BL BR he
      have hb := glueIdentify_inr_kept BL BR ⟨d, hd⟩
      rw [ha, hb] at h
      cases h
    · rw [glueIdentify_inr_kept BL BR ⟨d, hd⟩,
        glueIdentify_inr_kept BL BR ⟨e, he⟩] at h
      exact congrArg Subtype.val (Sum.inr.inj h)



theorem glueIdentify_inr_edgeInv (d : DR) :
    glueEdgeInv BL BR (glueIdentify BL BR (.inr d)) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d)) := by
  rw [glueEdgeInv_identify]
  rfl



theorem glueTail_identify_inr (d : DR) :
    glueTail BL BR (glueIdentify BL BR (.inr d)) ↔ BR.map.tail d := by
  by_cases hd : d ∈ BR.leftPath.darts
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    have hi' : i.val < s := by simpa [BR.leftPath.darts_length] using i.isLt
    let i' : Fin s := ⟨i.val, hi'⟩
    let bi : Fin BL.rightPath.darts.length := ⟨i'.val, by
      rw [BL.rightPath.darts_length]
      exact i'.isLt⟩
    let ci : Fin BR.leftPath.darts.length := ⟨i'.val, by
      rw [BR.leftPath.darts_length]
      exact i'.isLt⟩
    have hci : BR.leftPath.darts.get ci = BR.leftPath.darts.get i :=
      congrArg _ (Fin.ext rfl)
    have heq : glueIdentify BL BR (.inr d) =
        glueIdentify BL BR (.inl (BL.rightPath.darts.get bi)) := by
      calc
        glueIdentify BL BR (.inr d) =
            glueIdentify BL BR (.inr (BR.leftPath.darts.get i)) :=
              congrArg (fun x => glueIdentify BL BR (.inr x)) hi.symm
        _ = glueIdentify BL BR (.inr (BR.leftPath.darts.get ci)) := by rw [hci]
        _ = glueIdentify BL BR (.inl (BL.rightPath.darts.get bi)) := by
              simpa [bi, ci] using (glueIdentify_seam BL BR i').symm
    have hkeep := glueCutRight_path_opposite_not_mem BL BL.rightPath
      (List.get_mem _ bi)
    have htL : BL.map.tail (BL.rightPath.darts.get bi) :=
      (BL.rightPath.edge_step bi).2.1
    have htR : BR.map.tail d := by
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
      rw [← hj]
      exact (BR.leftPath.edge_step j).2.1
    constructor
    · intro _
      exact htR
    · intro _
      rw [heq, glueIdentify_inl_kept BL BR ⟨_, hkeep⟩]
      exact htL
  · rw [glueIdentify_inr_kept BL BR ⟨d, hd⟩]
    rfl

end DirectedDistances.PlanarMap
