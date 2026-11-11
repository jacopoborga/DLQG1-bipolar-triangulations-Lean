module

public import DirectedDistances.PlanarMap.PlanarPathGlueGeodesic
public import DirectedDistances.PlanarMap.PlanarPathGlueBasePackage
public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap
public import DirectedDistances.PlanarMap.PlanarPathCutSeparation
public import DirectedDistances.PlanarMap.PlanarPathCutHalves
public import DirectedDistances.PlanarMap.PlanarPathCutLeftmostRegion
public import DirectedDistances.PlanarMap.PlanarPathGlueCutRight

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PlanarMap

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)

private def glueCutLeftSide : GlueDart BL BR → Bool
  | .inl _ => true
  | .inr _ => false

private theorem glueCutLeft_leftBoundary_keep (d : DL)
    (hd : d ∈ BL.leftPath.darts) :
    BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts := by
  intro hflip
  have hl : d ∈ pathCutLeftOuterArc BL :=
    (mem_pathCutLeftOuterArc_iff BL d).2 hd
  have hr : d ∈ pathCutRightOuterArc BL := by
    rw [mem_pathCutRightOuterArc_iff]
    apply List.mem_map.mpr
    refine ⟨BL.map.toCombinatorialMap.edgeInv d,
      List.mem_reverse.mpr hflip, ?_⟩
    exact BL.map.toCombinatorialMap.edgeInv_invol d
  exact (Set.disjoint_left.mp (pathCut_outerArcs_disjoint BL) hl hr)

private theorem glueCutLeft_rightBoundary_keep (d : DR)
    (hd : d ∈ BR.rightPath.darts) :
    BR.map.toCombinatorialMap.edgeInv d ∉ BR.leftPath.darts := by
  intro hflip
  have hl : BR.map.toCombinatorialMap.edgeInv d ∈ pathCutLeftOuterArc BR :=
    (mem_pathCutLeftOuterArc_iff BR _).2 hflip
  have hr : BR.map.toCombinatorialMap.edgeInv d ∈ pathCutRightOuterArc BR := by
    rw [mem_pathCutRightOuterArc_iff]
    exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
  exact (Set.disjoint_left.mp (pathCut_outerArcs_disjoint BR) hl hr)

private theorem glueCutLeft_path_darts_nodup {D : Type*} [Fintype D]
    [DecidableEq D] {M : DirectedMapWithMissing D} {a b : MapVertex M}
    {n : ℕ} (P : SimpleDirectedDartPath M a b n) : P.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hv := (P.edge_step i).2.2.1.trans
    ((congrArg (dartTailVertex M) hij).trans (P.edge_step j).2.2.1.symm)
  exact Fin.ext (congrArg (fun q : Fin P.vertices.length => q.val)
    (P.vertices_nodup.get_inj_iff.mp hv))

private theorem glueCutLeft_path_opposite_not_mem {D : Type*} [Fintype D]
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

private theorem glueCutLeft_leftPath_outer {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ B.leftPath.darts) : B.map.IsOuter d := by
  apply B.outerSplit.1.1 d
  apply B.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append]
  exact Or.inl hd

private theorem glueCutLeft_leftSeeds_colored (d : GlueDart BL BR)
    (hd : d ∈ pathCutLeftSeeds (glueBase BL BR) (glueSeamPath BL BR)) :
    glueCutLeftSide BL BR d = true := by
  rcases hd with hd | hd
  · have hpath : d ∈ (glueBase BL BR).leftPath.darts :=
      (mem_pathCutLeftOuterArc_iff (glueBase BL BR) d).mp hd
    rw [glueBase_leftPath_darts] at hpath
    obtain ⟨a, ha, hda⟩ := List.mem_map.mp hpath
    have hk := glueCutLeft_leftBoundary_keep BL a ha
    rw [← hda, glueIdentify_inl_kept BL BR ⟨a, hk⟩]
    rfl
  · have hpath : d ∈ (glueSeamPath BL BR).darts := hd
    rw [glueSeamPath_darts] at hpath
    obtain ⟨a, ha, hda⟩ := List.mem_map.mp hpath
    have hk := glueCutLeft_path_opposite_not_mem BL BL.rightPath ha
    rw [← hda, glueIdentify_inl_kept BL BR ⟨a, hk⟩]
    rfl

private theorem glueCutLeft_rightOuterArc_colored (d : GlueDart BL BR)
    (hd : d ∈ pathCutRightOuterArc (glueBase BL BR)) :
    glueCutLeftSide BL BR d = false := by
  have hpath : d ∈ (glueBase BL BR).rightPath.darts.reverse.map
      (glueBase BL BR).map.toCombinatorialMap.edgeInv :=
    (mem_pathCutRightOuterArc_iff (glueBase BL BR) d).mp hd
  rw [glueBase_rightPath_darts] at hpath
  obtain ⟨a, ha, hda⟩ := List.mem_map.mp hpath
  obtain ⟨b, hb, hba⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  have hflip : glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv b)) = d := by
    calc
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv b)) =
          (glueBase BL BR).map.toCombinatorialMap.edgeInv
            (glueIdentify BL BR (.inr b)) := by
              rw [glueBase_map, glueDirectedMap_toCombinatorialMap,
                glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
              rfl
      _ = (glueBase BL BR).map.toCombinatorialMap.edgeInv a := by rw [hba]
      _ = d := hda
  have hk := glueCutLeft_rightBoundary_keep BR b hb
  rw [← hflip, glueIdentify_inr_kept BL BR ⟨_, hk⟩]
  rfl

private theorem glueIdentify_inl_reverse_seam (d : DL)
    (hd : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts) :
    ∃ i : Fin s,
      d = BL.map.toCombinatorialMap.edgeInv
          (BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩) ∧
      glueIdentify BL BR (.inl d) =
        glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv
          (BR.leftPath.darts.get ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩))) := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
  have hj' : j.val < s := by simpa [BL.rightPath.darts_length] using j.isLt
  let i : Fin s := ⟨j.val, hj'⟩
  let bi : Fin BL.rightPath.darts.length := ⟨i.val, by
    rw [BL.rightPath.darts_length]
    exact i.isLt⟩
  let ci : Fin BR.leftPath.darts.length := ⟨i.val, by
    rw [BR.leftPath.darts_length]
    exact i.isLt⟩
  have hget : BL.rightPath.darts.get bi = BL.map.toCombinatorialMap.edgeInv d := by
    simpa [bi, i] using hj
  have hflip := congrArg (glueEdgeInv BL BR) (glueIdentify_seam BL BR i)
  rw [glueEdgeInv_identify, glueEdgeInv_identify] at hflip
  simp only [Sum.map_inl, Sum.map_inr] at hflip
  have hdi : d = BL.map.toCombinatorialMap.edgeInv
      (BL.rightPath.darts.get bi) := by
    have hh := congrArg BL.map.toCombinatorialMap.edgeInv hget
    rw [BL.map.toCombinatorialMap.edgeInv_invol] at hh
    exact hh.symm
  refine ⟨i, hdi, ?_⟩
  rw [hdi]
  exact hflip



theorem glueIdentify_inl_injective :
    Function.Injective (fun d : DL => glueIdentify BL BR (.inl d)) := by
  intro d e h
  change glueIdentify BL BR (.inl d) = glueIdentify BL BR (.inl e) at h
  by_cases hd : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts
  · by_cases he : BL.map.toCombinatorialMap.edgeInv e ∈ BL.rightPath.darts
    · obtain ⟨i, hdi, hdi'⟩ := glueIdentify_inl_reverse_seam BL BR d hd
      obtain ⟨j, hei, hei'⟩ := glueIdentify_inl_reverse_seam BL BR e he
      have hrev : glueIdentify BL BR
          (.inr (BR.map.toCombinatorialMap.edgeInv
            (BR.leftPath.darts.get ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩))) =
          glueIdentify BL BR
          (.inr (BR.map.toCombinatorialMap.edgeInv
            (BR.leftPath.darts.get ⟨j.val, by rw [BR.leftPath.darts_length]; exact j.isLt⟩))) := by
        rw [hdi', hei'] at h
        exact h
      have hflip := congrArg (glueEdgeInv BL BR) hrev
      rw [glueEdgeInv_identify, glueEdgeInv_identify] at hflip
      simp only [Sum.map_inr, BR.map.toCombinatorialMap.edgeInv_invol] at hflip
      have hseamI := glueIdentify_seam BL BR i
      have hseamJ := glueIdentify_seam BL BR j
      have hleft : glueIdentify BL BR (.inl
          (BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩)) =
          glueIdentify BL BR (.inl
          (BL.rightPath.darts.get ⟨j.val, by rw [BL.rightPath.darts_length]; exact j.isLt⟩)) := by
        calc
          _ = glueIdentify BL BR (.inr
                (BR.leftPath.darts.get ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩)) := hseamI
          _ = glueIdentify BL BR (.inr
                (BR.leftPath.darts.get ⟨j.val, by rw [BR.leftPath.darts_length]; exact j.isLt⟩)) := hflip
          _ = _ := hseamJ.symm
      have hiKeep := glueCutLeft_path_opposite_not_mem BL BL.rightPath
        (List.get_mem _ (⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩))
      have hjKeep := glueCutLeft_path_opposite_not_mem BL BL.rightPath
        (List.get_mem _ (⟨j.val, by rw [BL.rightPath.darts_length]; exact j.isLt⟩))
      rw [glueIdentify_inl_kept BL BR ⟨_, hiKeep⟩,
        glueIdentify_inl_kept BL BR ⟨_, hjKeep⟩] at hleft
      have hget : BL.rightPath.darts.get
          ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩ =
          BL.rightPath.darts.get
          ⟨j.val, by rw [BL.rightPath.darts_length]; exact j.isLt⟩ :=
        congrArg Subtype.val (Sum.inl.inj hleft)
      have hij : i = j := Fin.ext (by
        have hval := congrArg Fin.val
          ((glueCutLeft_path_darts_nodup BL.rightPath).get_inj_iff.mp hget)
        exact hval)
      rw [hdi, hei]
      have hpaths : BL.rightPath.darts.get
          ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩ =
          BL.rightPath.darts.get
          ⟨j.val, by rw [BL.rightPath.darts_length]; exact j.isLt⟩ :=
        congrArg (fun k : Fin s => BL.rightPath.darts.get
          ⟨k.val, by rw [BL.rightPath.darts_length]; exact k.isLt⟩) hij
      exact congrArg BL.map.toCombinatorialMap.edgeInv hpaths
    · obtain ⟨i, _, hi⟩ := glueIdentify_inl_reverse_seam BL BR d hd
      let qi : Fin BR.leftPath.darts.length := ⟨i.val, by
        rw [BR.leftPath.darts_length]
        exact i.isLt⟩
      have hq := glueCutLeft_path_opposite_not_mem BR BR.leftPath
        (List.get_mem _ qi)
      have hleft : glueIdentify BL BR (.inl d) =
          Sum.inr ⟨BR.map.toCombinatorialMap.edgeInv (BR.leftPath.darts.get qi), hq⟩ := by
        rw [glueIdentify_inr_kept BL BR ⟨_, hq⟩] at hi
        exact hi
      have hright : glueIdentify BL BR (.inl e) =
          Sum.inl ⟨e, he⟩ := glueIdentify_inl_kept BL BR ⟨e, he⟩
      rw [hleft, hright] at h
      cases h
  · by_cases he : BL.map.toCombinatorialMap.edgeInv e ∈ BL.rightPath.darts
    · obtain ⟨i, _, hi⟩ := glueIdentify_inl_reverse_seam BL BR e he
      let qi : Fin BR.leftPath.darts.length := ⟨i.val, by
        rw [BR.leftPath.darts_length]
        exact i.isLt⟩
      have hq := glueCutLeft_path_opposite_not_mem BR BR.leftPath
        (List.get_mem _ qi)
      have hleft : glueIdentify BL BR (.inl e) =
          Sum.inr ⟨BR.map.toCombinatorialMap.edgeInv (BR.leftPath.darts.get qi), hq⟩ := by
        rw [glueIdentify_inr_kept BL BR ⟨_, hq⟩] at hi
        exact hi
      have hright : glueIdentify BL BR (.inl d) =
          Sum.inl ⟨d, hd⟩ := glueIdentify_inl_kept BL BR ⟨d, hd⟩
      rw [hleft, hright] at h
      cases h
    · rw [glueIdentify_inl_kept BL BR ⟨d, hd⟩,
        glueIdentify_inl_kept BL BR ⟨e, he⟩] at h
      exact congrArg Subtype.val (Sum.inl.inj h)

private theorem glueIdentify_inl_reverse_seam_mem_leftHalf (d : DL)
    (hd : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts) :
    glueIdentify BL BR (.inl d) ∈
      pathCutLeftHalfDarts (glueBase BL BR) (glueSeamPath BL BR) := by
  obtain ⟨i, hdi, _⟩ := glueIdentify_inl_reverse_seam BL BR d hd
  let bi : Fin BL.rightPath.darts.length := ⟨i.val, by
    rw [BL.rightPath.darts_length]
    exact i.isLt⟩
  have hp : glueIdentify BL BR (.inl (BL.rightPath.darts.get bi)) ∈
      (glueSeamPath BL BR).darts := by
    rw [glueSeamPath_darts]
    exact List.mem_map.mpr ⟨BL.rightPath.darts.get bi, List.get_mem _ _, rfl⟩
  have hinv : (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inl d)) =
        glueIdentify BL BR (.inl (BL.rightPath.darts.get bi)) := by
    rw [glueBase_map, glueDirectedMap_toCombinatorialMap,
      glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
    simp only [Sum.map_inl]
    rw [hdi, BL.map.toCombinatorialMap.edgeInv_invol]
  change glueIdentify BL BR (.inl d) ∈
      pathCutLeftDarts (glueBase BL BR) (glueSeamPath BL BR) ∪
        pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR)
  right
  change glueIdentify BL BR (.inl d) ∈ (glueSeamPath BL BR).darts ∨
    (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inl d)) ∈ (glueSeamPath BL BR).darts
  exact Or.inr (hinv ▸ hp)

private theorem glueIdentify_inl_forward_seam_mem_leftHalf (d : DL)
    (hd : d ∈ BL.rightPath.darts) :
    glueIdentify BL BR (.inl d) ∈
      pathCutLeftHalfDarts (glueBase BL BR) (glueSeamPath BL BR) := by
  have hp : glueIdentify BL BR (.inl d) ∈ (glueSeamPath BL BR).darts := by
    rw [glueSeamPath_darts]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  change glueIdentify BL BR (.inl d) ∈
      pathCutLeftDarts (glueBase BL BR) (glueSeamPath BL BR) ∪
        pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR)
  right
  change glueIdentify BL BR (.inl d) ∈ (glueSeamPath BL BR).darts ∨
    (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inl d)) ∈ (glueSeamPath BL BR).darts
  exact Or.inl hp

private theorem glueCutLeft_inr_leftPath_mem_seam {d : DR}
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

private theorem glueCutLeft_edgeInv_identify_inl (d : DL) :
    (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inl d)) =
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv d)) := by
  rw [glueBase_map, glueDirectedMap_toCombinatorialMap,
    glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl

private theorem glueCutLeft_edgeInv_identify_inr (d : DR) :
    (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inr d)) =
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d)) := by
  rw [glueBase_map, glueDirectedMap_toCombinatorialMap,
    glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl

private theorem glueCutLeft_outerArc_image {d : DR}
    (hd : d ∈ pathCutRightOuterArc BR) :
    glueIdentify BL BR (.inr d) ∈ pathCutRightOuterArc (glueBase BL BR) := by
  obtain ⟨p, hp, hpd⟩ := List.mem_map.mp
    ((mem_pathCutRightOuterArc_iff BR d).mp hd)
  have hpath : glueIdentify BL BR (.inr p) ∈
      (glueBase BL BR).rightPath.darts.reverse := by
    rw [glueBase_rightPath_darts]
    apply List.mem_reverse.mpr
    rw [List.mem_map]
    exact ⟨p, List.mem_reverse.mp hp, rfl⟩
  apply (mem_pathCutRightOuterArc_iff (glueBase BL BR) _).2
  rw [List.mem_map]
  refine ⟨glueIdentify BL BR (.inr p), hpath, ?_⟩
  have hedge : (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inr p)) = glueIdentify BL BR
        (.inr (BR.map.toCombinatorialMap.edgeInv p)) := by
    exact glueCutLeft_edgeInv_identify_inr BL BR p
  rw [← hpd]
  exact hedge

private theorem glueCutLeft_rightOuterArc_outer {D : Type*} [Fintype D]
    [DecidableEq D] {a b : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D a b) {d : D}
    (hd : d ∈ pathCutRightOuterArc B) : B.map.IsOuter d := by
  apply B.outerSplit.1.1 d
  apply B.outerSplit.2.1.mem_iff.mpr
  rw [mem_pathCutRightOuterArc_iff B d] at hd
  simp only [List.append_nil, List.mem_append]
  exact Or.inr hd

private theorem glueCutLeft_edgeInv_side_of_notSeam {g : GlueDart BL BR}
    (hseam : g ∉ pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR)) :
    glueCutLeftSide BL BR
        ((glueBase BL BR).map.toCombinatorialMap.edgeInv g) =
      glueCutLeftSide BL BR g := by
  change ¬ (g ∈ (glueSeamPath BL BR).darts ∨
    (glueBase BL BR).map.toCombinatorialMap.edgeInv g ∈
      (glueSeamPath BL BR).darts) at hseam
  rcases g with ⟨d, hd⟩ | ⟨d, hd⟩
  · have hkeep : glueIdentify BL BR (.inl d) = .inl ⟨d, hd⟩ :=
      glueIdentify_inl_kept BL BR ⟨d, hd⟩
    have hnot := not_or.mp hseam
    have hdPath : d ∉ BL.rightPath.darts := by
      intro h
      apply hnot.1
      rw [← hkeep, glueSeamPath_darts]
      exact List.mem_map.mpr ⟨d, h, rfl⟩
    have hkeepInv : BL.map.toCombinatorialMap.edgeInv d ∉
        BL.rightPath.darts := by
      intro h
      apply hnot.2
      rw [← hkeep, glueCutLeft_edgeInv_identify_inl,
        glueSeamPath_darts]
      exact List.mem_map.mpr ⟨BL.map.toCombinatorialMap.edgeInv d, h, rfl⟩
    have hkeepInv' : BL.map.toCombinatorialMap.edgeInv
        (BL.map.toCombinatorialMap.edgeInv d) ∉ BL.rightPath.darts := by
      rw [BL.map.toCombinatorialMap.edgeInv_invol]
      exact hdPath
    have hEdge : (glueBase BL BR).map.toCombinatorialMap.edgeInv
        (.inl ⟨d, hd⟩) = .inl ⟨BL.map.toCombinatorialMap.edgeInv d, hkeepInv'⟩ := by
      rw [← hkeep, glueCutLeft_edgeInv_identify_inl,
        glueIdentify_inl_kept BL BR ⟨_, hkeepInv'⟩]
    rw [hEdge]
    rfl
  · have hkeep : glueIdentify BL BR (.inr d) = .inr ⟨d, hd⟩ :=
      glueIdentify_inr_kept BL BR ⟨d, hd⟩
    have hnot := not_or.mp hseam
    have hdInvPath : BR.map.toCombinatorialMap.edgeInv d ∉
        BR.leftPath.darts := by
      intro h
      apply hnot.2
      rw [← hkeep, glueCutLeft_edgeInv_identify_inr]
      exact glueCutLeft_inr_leftPath_mem_seam BL BR h
    have hEdge : (glueBase BL BR).map.toCombinatorialMap.edgeInv
        (.inr ⟨d, hd⟩) = .inr ⟨BR.map.toCombinatorialMap.edgeInv d, hdInvPath⟩ := by
      rw [← hkeep, glueCutLeft_edgeInv_identify_inr,
        glueIdentify_inr_kept BL BR ⟨_, hdInvPath⟩]
    rw [hEdge]
    rfl

private theorem glueCutLeft_rightSeed_colored (g : GlueDart BL BR)
    (hg : g ∈ pathCutRightSeeds (glueBase BL BR) (glueSeamPath BL BR)) :
    glueCutLeftSide BL BR g = false := by
  change g ∈ pathCutRightOuterArc (glueBase BL BR) ∨
    ∃ p ∈ (glueSeamPath BL BR).darts,
      g = (glueBase BL BR).map.toCombinatorialMap.edgeInv p at hg
  rcases hg with houter | ⟨p, hp, hgp⟩
  · exact glueCutLeft_rightOuterArc_colored BL BR g houter
  · rw [glueSeamPath_darts] at hp
    obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hp
    have hflip : (glueBase BL BR).map.toCombinatorialMap.edgeInv
        (glueIdentify BL BR (.inl a)) =
          glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv a)) :=
      glueCutLeft_edgeInv_identify_inl BL BR a
    have heq : g = glueIdentify BL BR
        (.inl (BL.map.toCombinatorialMap.edgeInv a)) := by
      rw [hgp, ← hpa, hflip]
    obtain ⟨i, _, hrev⟩ := glueIdentify_inl_reverse_seam BL BR
      (BL.map.toCombinatorialMap.edgeInv a) (by
        rw [BL.map.toCombinatorialMap.edgeInv_invol]
        exact ha)
    rw [heq, hrev]
    have hkeep : BR.map.toCombinatorialMap.edgeInv
        (BR.leftPath.darts.get ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩) ∉
          BR.leftPath.darts :=
      glueCutLeft_path_opposite_not_mem BR BR.leftPath (List.get_mem _ _)
    rw [glueIdentify_inr_kept BL BR ⟨_, hkeep⟩]
    rfl

private theorem glueCutLeft_rightDarts_colored (g : GlueDart BL BR)
    (hg : g ∈ pathCutRightDarts (glueBase BL BR) (glueSeamPath BL BR)) :
    glueCutLeftSide BL BR g = false := by
  obtain ⟨a, ha, hreach⟩ := hg
  have hstart := glueCutLeft_rightSeed_colored BL BR a ha
  induction hreach with
  | refl => exact hstart
  | @tail b c hreach hstep ih =>
      change (c = (glueBase BL BR).map.toCombinatorialMap.faceSucc b ∧
          (¬ (glueBase BL BR).map.IsOuter b ∨
            (b ∈ pathCutRightOuterArc (glueBase BL BR) ∧
              c ∈ pathCutRightOuterArc (glueBase BL BR)))) ∨
        (c = (glueBase BL BR).map.toCombinatorialMap.edgeInv b ∧
          b ∉ pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR)) at hstep
      rcases hstep with ⟨hEq, hface⟩ | ⟨hEq, hnotSeam⟩
      · rcases hface with hinner | ⟨_houter, hcouter⟩
        · cases b with
          | inl d =>
              change true = false at ih
              cases ih
          | inr d =>
              have hkeep : glueIdentify BL BR (.inr d.val) = .inr d :=
                glueIdentify_inr_kept BL BR d
              have hglueInner : ¬ (glueBase BL BR).map.IsOuter
                  (glueIdentify BL BR (.inr d.val)) := by
                simpa only [← hkeep] using hinner
              have hsourceInner : ¬ BR.map.IsOuter d.val := by
                intro hout
                have hword : d.val ∈ BR.outerWord.letters :=
                  (mem_iff_isOuter BR.map BR.outerWord BR.outerSplit.1 d.val).mpr hout
                have hbound := BR.outerSplit.2.1.mem_iff.mp hword
                have hbound' : d.val ∈ BR.leftPath.darts ∨
                    d.val ∈ BR.rightPath.darts.reverse.map
                      BR.map.toCombinatorialMap.edgeInv := by
                  simpa only [List.append_nil, List.mem_append] using hbound
                have hparts : d.val ∈ BR.leftPath.darts ∨
                    d.val ∈ pathCutRightOuterArc BR := by
                  rcases hbound' with hl | hr
                  · exact Or.inl hl
                  · exact Or.inr ((mem_pathCutRightOuterArc_iff BR d.val).2 hr)
                have hright : d.val ∈ pathCutRightOuterArc BR :=
                  hparts.resolve_left d.property
                have hrightG := glueCutLeft_outerArc_image BL BR hright
                have houterG : (glueBase BL BR).map.IsOuter
                    (glueIdentify BL BR (.inr d.val)) :=
                  glueCutLeft_rightOuterArc_outer (glueBase BL BR) hrightG
                exact hglueInner houterG
              have hSuccInner : ¬ BR.map.IsOuter
                  (BR.map.toCombinatorialMap.faceSucc d.val) := by
                intro hout
                exact hsourceInner
                  (Equiv.Perm.sameCycle_apply_right.mp hout)
              have hSuccKeep : BR.map.toCombinatorialMap.faceSucc d.val ∉
                  BR.leftPath.darts := by
                intro hpath
                exact hSuccInner (glueCutLeft_leftPath_outer BR hpath)
              have hfaceG : (glueBase BL BR).map.toCombinatorialMap.faceSucc
                  (.inr d) = glueIdentify BL BR (.inr
                    (BR.map.toCombinatorialMap.faceSucc d.val)) := by
                rw [← hkeep, glueBase_map, glueDirectedMap_toCombinatorialMap,
                  glue_faceSucc_right_inner BL BR d.val hsourceInner]
              rw [hEq, hfaceG,
                glueIdentify_inr_kept BL BR ⟨_, hSuccKeep⟩]
              rfl
        · exact glueCutLeft_rightOuterArc_colored BL BR c hcouter
      · rw [hEq]
        exact glueCutLeft_edgeInv_side_of_notSeam BL BR hnotSeam ▸ ih



theorem glueIdentify_inl_mem_leftHalf (d : DL) :
    glueIdentify BL BR (.inl d) ∈
      pathCutLeftHalfDarts (glueBase BL BR) (glueSeamPath BL BR) := by
  by_cases hd : d ∈ BL.rightPath.darts
  · exact glueIdentify_inl_forward_seam_mem_leftHalf BL BR d hd
  · by_cases hdi : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts
    · exact glueIdentify_inl_reverse_seam_mem_leftHalf BL BR d hdi
    · have hkeep : glueIdentify BL BR (.inl d) =
        .inl ⟨d, hdi⟩ := glueIdentify_inl_kept BL BR ⟨d, hdi⟩
      have hcover := pathCut_halves_cover (glueBase BL BR)
        (glueSeamPath BL BR) (glueIdentify BL BR (.inl d))
      rcases hcover with hleft | hright
      · exact hleft
      · change glueIdentify BL BR (.inl d) ∈
          pathCutRightDarts (glueBase BL BR) (glueSeamPath BL BR) ∪
            pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR) at hright
        rcases hright with hright | hseam
        · have hfalse := glueCutLeft_rightDarts_colored BL BR
            (glueIdentify BL BR (.inl d)) hright
          rw [hkeep] at hfalse
          cases hfalse
        · change glueIdentify BL BR (.inl d) ∈
            pathCutLeftDarts (glueBase BL BR) (glueSeamPath BL BR) ∪
              pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR)
          exact Or.inr hseam

private theorem glueCutLeft_seam_mem_inl_image {g : GlueDart BL BR}
    (hg : g ∈ pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR)) :
    ∃ d : DL, glueIdentify BL BR (.inl d) = g := by
  change g ∈ (glueSeamPath BL BR).darts ∨
    (glueBase BL BR).map.toCombinatorialMap.edgeInv g ∈
      (glueSeamPath BL BR).darts at hg
  rcases hg with hp | hp
  · rw [glueSeamPath_darts] at hp
    obtain ⟨d, hd, hgd⟩ := List.mem_map.mp hp
    exact ⟨d, hgd⟩
  · rw [glueSeamPath_darts] at hp
    obtain ⟨d, hd, hpd⟩ := List.mem_map.mp hp
    refine ⟨BL.map.toCombinatorialMap.edgeInv d, ?_⟩
    calc
      glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv d)) =
          (glueBase BL BR).map.toCombinatorialMap.edgeInv
            (glueIdentify BL BR (.inl d)) :=
              (glueCutLeft_edgeInv_identify_inl BL BR d).symm
      _ = (glueBase BL BR).map.toCombinatorialMap.edgeInv
            ((glueBase BL BR).map.toCombinatorialMap.edgeInv g) :=
              congrArg ((glueBase BL BR).map.toCombinatorialMap.edgeInv) hpd
      _ = g := (glueBase BL BR).map.toCombinatorialMap.edgeInv_invol g



theorem glueIdentify_inl_image_iff (g : GlueDart BL BR) :
    g ∈ pathCutLeftHalfDarts (glueBase BL BR) (glueSeamPath BL BR) ↔
      ∃ d : DL, glueIdentify BL BR (.inl d) = g := by
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := glueIdentify_surjective BL BR g
    rcases x with d | d
    · exact ⟨d, hx⟩
    · have hright := glueIdentify_inr_mem_rightHalf BL BR d
      rw [hx] at hright
      have hseam : g ∈ pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR) := by
        have hboth : g ∈ pathCutLeftHalfDarts (glueBase BL BR)
              (glueSeamPath BL BR) ∩
            pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR) :=
          ⟨hg, hright⟩
        have hinter := pathCut_halves_inter_eq_seam
          (glueBase BL BR) (glueSeamPath BL BR)
        exact hinter ▸ hboth
      exact glueCutLeft_seam_mem_inl_image BL BR hseam
  · rintro ⟨d, rfl⟩
    exact glueIdentify_inl_mem_leftHalf BL BR d

private theorem glueCutLeft_inl_leftSeam_image {d : DL}
    (hd : d ∈ BL.rightPath.darts) :
    ∃ e : DR, glueIdentify BL BR (.inl d) = glueIdentify BL BR (.inr e) := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hi' : i.val < s := by simpa [BL.rightPath.darts_length] using i.isLt
  let i' : Fin s := ⟨i.val, hi'⟩
  let bi : Fin BL.rightPath.darts.length := ⟨i'.val, by
    rw [BL.rightPath.darts_length]
    exact i'.isLt⟩
  let ci : Fin BR.leftPath.darts.length := ⟨i'.val, by
    rw [BR.leftPath.darts_length]
    exact i'.isLt⟩
  have hbi : BL.rightPath.darts.get bi = BL.rightPath.darts.get i :=
    congrArg _ (Fin.ext rfl)
  refine ⟨BR.leftPath.darts.get ci, ?_⟩
  calc
    glueIdentify BL BR (.inl d) =
        glueIdentify BL BR (.inl (BL.rightPath.darts.get bi)) :=
          congrArg (fun x => glueIdentify BL BR (.inl x)) (hi.symm.trans hbi.symm)
    _ = glueIdentify BL BR (.inr (BR.leftPath.darts.get ci)) := by
          simpa [bi, ci] using glueIdentify_seam BL BR i'

private theorem glueCutLeft_seam_mem_inr_image {g : GlueDart BL BR}
    (hg : g ∈ pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR)) :
    ∃ d : DR, glueIdentify BL BR (.inr d) = g := by
  change g ∈ (glueSeamPath BL BR).darts ∨
    (glueBase BL BR).map.toCombinatorialMap.edgeInv g ∈
      (glueSeamPath BL BR).darts at hg
  rcases hg with hp | hp
  · rw [glueSeamPath_darts] at hp
    obtain ⟨a, ha, hga⟩ := List.mem_map.mp hp
    obtain ⟨b, hbridge⟩ := glueCutLeft_inl_leftSeam_image BL BR ha
    exact ⟨b, hbridge.symm.trans hga⟩
  · rw [glueSeamPath_darts] at hp
    obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hp
    obtain ⟨b, hbridge⟩ := glueCutLeft_inl_leftSeam_image BL BR ha
    refine ⟨BR.map.toCombinatorialMap.edgeInv b, ?_⟩
    calc
      glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv b)) =
          (glueBase BL BR).map.toCombinatorialMap.edgeInv
            (glueIdentify BL BR (.inr b)) :=
              (glueCutLeft_edgeInv_identify_inr BL BR b).symm
      _ = (glueBase BL BR).map.toCombinatorialMap.edgeInv
            ((glueBase BL BR).map.toCombinatorialMap.edgeInv g) := by
              rw [← hbridge, ← hpa]
      _ = g := (glueBase BL BR).map.toCombinatorialMap.edgeInv_invol g



theorem glueIdentify_inr_image_iff (g : GlueDart BL BR) :
    g ∈ pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR) ↔
      ∃ d : DR, glueIdentify BL BR (.inr d) = g := by
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := glueIdentify_surjective BL BR g
    rcases x with d | d
    · have hleft := glueIdentify_inl_mem_leftHalf BL BR d
      rw [hx] at hleft
      have hseam : g ∈ pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR) := by
        have hboth : g ∈ pathCutLeftHalfDarts (glueBase BL BR)
              (glueSeamPath BL BR) ∩
            pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR) :=
          ⟨hleft, hg⟩
        have hinter := pathCut_halves_inter_eq_seam
          (glueBase BL BR) (glueSeamPath BL BR)
        exact hinter ▸ hboth
      exact glueCutLeft_seam_mem_inr_image BL BR hseam
    · exact ⟨d, hx⟩
  · rintro ⟨d, rfl⟩
    exact glueIdentify_inr_mem_rightHalf BL BR d



theorem glueIdentify_images_inter_subset_seam :
    {g : GlueDart BL BR | ∃ d : DL, glueIdentify BL BR (.inl d) = g} ∩
      {g : GlueDart BL BR | ∃ d : DR, glueIdentify BL BR (.inr d) = g} ⊆
        pathCutSeamDarts (glueBase BL BR) (glueSeamPath BL BR) := by
  intro g hg
  have hleft := (glueIdentify_inl_image_iff BL BR g).2 hg.1
  have hright := (glueIdentify_inr_image_iff BL BR g).2 hg.2
  have hboth : g ∈ pathCutLeftHalfDarts (glueBase BL BR)
        (glueSeamPath BL BR) ∩
      pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR) :=
    ⟨hleft, hright⟩
  have hinter := pathCut_halves_inter_eq_seam
    (glueBase BL BR) (glueSeamPath BL BR)
  exact hinter ▸ hboth



noncomputable def glueCutLeftEquiv : DL ≃
    {g : GlueDart BL BR //
      g ∈ pathCutLeftHalfDarts (glueBase BL BR) (glueSeamPath BL BR)} :=
  Equiv.ofBijective
    (fun d => ⟨glueIdentify BL BR (.inl d), glueIdentify_inl_mem_leftHalf BL BR d⟩)
    ⟨(fun d e h => glueIdentify_inl_injective BL BR
        (congrArg Subtype.val h)),
      (fun g => by
        obtain ⟨d, hd⟩ := (glueIdentify_inl_image_iff BL BR g.1).mp g.2
        exact ⟨d, Subtype.ext hd⟩)⟩



noncomputable def glueCutRightEquiv : DR ≃
    {g : GlueDart BL BR //
      g ∈ pathCutRightHalfDarts (glueBase BL BR) (glueSeamPath BL BR)} :=
  Equiv.ofBijective
    (fun d => ⟨glueIdentify BL BR (.inr d), glueIdentify_inr_mem_rightHalf BL BR d⟩)
    ⟨(fun d e h => glueIdentify_inr_injective BL BR
        (congrArg Subtype.val h)),
      (fun g => by
        obtain ⟨d, hd⟩ := (glueIdentify_inr_image_iff BL BR g.1).mp g.2
        exact ⟨d, Subtype.ext hd⟩)⟩



theorem glueCutLeftEquiv_edgeInv (d : DL) :
    (glueCutLeftEquiv BL BR (BL.map.toCombinatorialMap.edgeInv d)).val =
      (glueBase BL BR).map.toCombinatorialMap.edgeInv
        (glueCutLeftEquiv BL BR d).val := by
  change glueIdentify BL BR (.inl (BL.map.toCombinatorialMap.edgeInv d)) =
    (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inl d))
  exact (glueCutLeft_edgeInv_identify_inl BL BR d).symm



theorem glueCutRightEquiv_edgeInv (d : DR) :
    (glueCutRightEquiv BL BR (BR.map.toCombinatorialMap.edgeInv d)).val =
      (glueBase BL BR).map.toCombinatorialMap.edgeInv
        (glueCutRightEquiv BL BR d).val := by
  change glueIdentify BL BR (.inr (BR.map.toCombinatorialMap.edgeInv d)) =
    (glueBase BL BR).map.toCombinatorialMap.edgeInv
      (glueIdentify BL BR (.inr d))
  exact (glueCutLeft_edgeInv_identify_inr BL BR d).symm

private theorem glueTail_identify_inl (d : DL) :
    glueTail BL BR (glueIdentify BL BR (.inl d)) ↔ BL.map.tail d := by
  by_cases hd : BL.map.toCombinatorialMap.edgeInv d ∈ BL.rightPath.darts
  · obtain ⟨i, hdi, hglue⟩ := glueIdentify_inl_reverse_seam BL BR d hd
    let bi : Fin BL.rightPath.darts.length := ⟨i.val, by
      rw [BL.rightPath.darts_length]
      exact i.isLt⟩
    let ci : Fin BR.leftPath.darts.length := ⟨i.val, by
      rw [BR.leftPath.darts_length]
      exact i.isLt⟩
    have htL : BL.map.tail (BL.rightPath.darts.get bi) :=
      (BL.rightPath.edge_step bi).2.1
    have htR : BR.map.tail
        (BR.leftPath.darts.get ci) := (BR.leftPath.edge_step ci).2.1
    have hnotL : ¬ BL.map.tail d := by
      intro ht
      have hnot := (BL.map.tail_iff d (BL.noMissingDarts d)).mp ht
      apply hnot
      rw [hdi, BL.map.toCombinatorialMap.edgeInv_invol]
      exact htL
    have hnotR : ¬ BR.map.tail
        (BR.map.toCombinatorialMap.edgeInv (BR.leftPath.darts.get ci)) := by
      intro ht
      have hnot := (BR.map.tail_iff
        (BR.map.toCombinatorialMap.edgeInv (BR.leftPath.darts.get ci))
        (BR.noMissingDarts _)).mp ht
      apply hnot
      rw [BR.map.toCombinatorialMap.edgeInv_invol]
      exact htR
    rw [hglue, glueTail_identify_inr]
    exact ⟨fun ht => (hnotR ht).elim,
      fun ht => (hnotL ht).elim⟩
  · rw [glueIdentify_inl_kept BL BR ⟨d, hd⟩]
    rfl



theorem glueCutLeftEquiv_tail (d : DL) :
    (glueBase BL BR).map.tail (glueCutLeftEquiv BL BR d).val ↔
      BL.map.tail d := by
  change (glueDirectedMap BL BR).tail
      (glueIdentify BL BR (.inl d)) ↔ BL.map.tail d
  rw [glueDirectedMap_tail]
  exact glueTail_identify_inl BL BR d



theorem glueCutRightEquiv_tail (d : DR) :
    (glueBase BL BR).map.tail (glueCutRightEquiv BL BR d).val ↔
      BR.map.tail d := by
  change (glueDirectedMap BL BR).tail
      (glueIdentify BL BR (.inr d)) ↔ BR.map.tail d
  rw [glueDirectedMap_tail]
  exact glueTail_identify_inr BL BR d


end DirectedDistances.PlanarMap
