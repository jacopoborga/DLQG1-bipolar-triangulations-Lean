/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutSeparation

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

/-! # Edge-closed halves of a planar path cut

paper result. The reachable left and right dart sets orient the two sides of
the cut, while both closed halves include every dart of the path seam. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

private theorem pathCutHalf_simplePath_darts_nodup
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) : P.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hi := P.edge_step i
  have hj := P.edge_step j
  have hiLt : i.val < k := by simpa [P.darts_length] using i.isLt
  have hjLt : j.val < k := by simpa [P.darts_length] using j.isLt
  let vi : Fin P.vertices.length :=
    ⟨i.val, by rw [P.vertices_length]; omega⟩
  let vj : Fin P.vertices.length :=
    ⟨j.val, by rw [P.vertices_length]; omega⟩
  have hv : P.vertices.get vi = P.vertices.get vj := by
    calc
      P.vertices.get vi = dartTailVertex M (P.darts.get i) := hi.2.2.1
      _ = dartTailVertex M (P.darts.get j) := congrArg (dartTailVertex M) hij
      _ = P.vertices.get vj := hj.2.2.1.symm
  have hidx := P.vertices_nodup.get_inj_iff.mp hv
  exact Fin.ext (congrArg (fun q : Fin P.vertices.length => q.val) hidx)

private theorem pathCutHalf_simplePath_tail_of_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ P.darts) :
    M.tail d := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact (P.edge_step i).2.1

private theorem pathCutHalf_pathDart_flip_not_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ P.darts) : B.map.toCombinatorialMap.edgeInv d ∉ P.darts := by
  intro hinv
  have htail := pathCutHalf_simplePath_tail_of_mem P hd
  have htailInv := pathCutHalf_simplePath_tail_of_mem P hinv
  have hnot := (B.map.tail_iff d (B.noMissingDarts d)).mp htail
  exact hnot htailInv




theorem pathCutSeamDarts_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    letI : DecidablePred (fun d : D => d ∈ pathCutSeamDarts B P) :=
      Classical.decPred _
    Fintype.card {d : D // d ∈ pathCutSeamDarts B P} = 2 * n := by
  classical
  let darts := P.darts.toFinset
  let reverseDarts := darts.image B.map.toCombinatorialMap.edgeInv
  have hseam : Finset.univ.filter (fun d : D => d ∈ pathCutSeamDarts B P) =
      darts ∪ reverseDarts := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      darts, reverseDarts, Finset.mem_image, List.mem_toFinset]
    change (d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts) ↔
      d ∈ P.darts ∨ ∃ p ∈ P.darts, B.map.toCombinatorialMap.edgeInv p = d
    constructor
    · rintro (hd | hd)
      · exact Or.inl hd
      · exact Or.inr ⟨B.map.toCombinatorialMap.edgeInv d, hd,
          B.map.toCombinatorialMap.edgeInv_invol d⟩
    · rintro (hd | ⟨p, hp, heq⟩)
      · exact Or.inl hd
      · right
        rw [← heq, B.map.toCombinatorialMap.edgeInv_invol]
        exact hp
  have hdisj : Disjoint darts reverseDarts := by
    apply Finset.disjoint_left.mpr
    intro d hd hrev
    obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp hrev
    have hp' : p ∈ P.darts := by simpa [darts] using hp
    have hd' : d ∈ P.darts := by simpa [darts] using hd
    have hnot := pathCutHalf_pathDart_flip_not_mem B P hp'
    apply hnot
    exact hpd.symm ▸ hd'
  have hcardDarts : darts.card = n := by
    dsimp [darts]
    rw [List.toFinset_card_of_nodup (pathCutHalf_simplePath_darts_nodup P),
      P.darts_length]
  have hcardReverse : reverseDarts.card = n := by
    rw [Finset.card_image_of_injective]
    · exact hcardDarts
    · exact B.map.toCombinatorialMap.edgeInv.injective
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun d : D => d ∈ pathCutSeamDarts B P)).card = 2 * n
  rw [hseam, Finset.card_union_of_disjoint hdisj, hcardDarts, hcardReverse]
  omega




@[expose] def pathCutLeftHalfDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  pathCutLeftDarts B P ∪ pathCutSeamDarts B P




@[expose] def pathCutRightHalfDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  pathCutRightDarts B P ∪ pathCutSeamDarts B P




@[expose] def pathCutLeftHalfEdges
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    Set (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :=
  {q | ∃ d, d ∈ pathCutLeftHalfDarts B P ∧
    edgeClass B.map.toCombinatorialMap d = q}




@[expose] def pathCutRightHalfEdges
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    Set (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :=
  {q | ∃ d, d ∈ pathCutRightHalfDarts B P ∧
    edgeClass B.map.toCombinatorialMap d = q}




@[expose] def pathCutSeamEdges
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    Set (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :=
  {q | ∃ d, d ∈ pathCutSeamDarts B P ∧
    edgeClass B.map.toCombinatorialMap d = q}




theorem pathCutLeftHalf_edgeInv_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ pathCutLeftHalfDarts B P) :
    B.map.toCombinatorialMap.edgeInv d ∈ pathCutLeftHalfDarts B P := by
  change d ∈ pathCutLeftDarts B P ∪ pathCutSeamDarts B P at hd
  change B.map.toCombinatorialMap.edgeInv d ∈
    pathCutLeftDarts B P ∪ pathCutSeamDarts B P
  rcases hd with hleft | hseam
  · by_cases hseam : d ∈ pathCutSeamDarts B P
    · exact Or.inr ((pathCutSeamDarts_edgeInv_iff B P d).2 hseam)
    · exact Or.inl (pathCutLeft_edgeInv_mem B P hleft hseam)
  · exact Or.inr ((pathCutSeamDarts_edgeInv_iff B P d).2 hseam)




theorem pathCutRightHalf_edgeInv_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ pathCutRightHalfDarts B P) :
    B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightHalfDarts B P := by
  change d ∈ pathCutRightDarts B P ∪ pathCutSeamDarts B P at hd
  change B.map.toCombinatorialMap.edgeInv d ∈
    pathCutRightDarts B P ∪ pathCutSeamDarts B P
  rcases hd with hright | hseam
  · by_cases hseam : d ∈ pathCutSeamDarts B P
    · exact Or.inr ((pathCutSeamDarts_edgeInv_iff B P d).2 hseam)
    · exact Or.inl (pathCutRight_edgeInv_mem B P hright hseam)
  · exact Or.inr ((pathCutSeamDarts_edgeInv_iff B P d).2 hseam)




theorem pathCut_halves_cover
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D) :
    d ∈ pathCutLeftHalfDarts B P ∨ d ∈ pathCutRightHalfDarts B P := by
  rcases pathCut_darts_cover B P d with hleft | hright
  · exact Or.inl (Or.inl hleft)
  · exact Or.inr (Or.inl hright)




theorem pathCut_halves_inter_eq_seam
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    pathCutLeftHalfDarts B P ∩ pathCutRightHalfDarts B P =
      pathCutSeamDarts B P := by
  apply Set.ext
  intro d
  change (d ∈ pathCutLeftDarts B P ∪ pathCutSeamDarts B P) ∧
    (d ∈ pathCutRightDarts B P ∪ pathCutSeamDarts B P) ↔
      d ∈ pathCutSeamDarts B P
  constructor
  · rintro ⟨hleft, hright⟩
    by_cases hseam : d ∈ pathCutSeamDarts B P
    · exact hseam
    · rcases hleft with hleft | hleftSeam
      · rcases hright with hright | hrightSeam
        · have hdis := Set.disjoint_left.mp (pathCut_offSeam_disjoint B P)
          exact (hdis ⟨hleft, hseam⟩ ⟨hright, hseam⟩).elim
        · exact (hseam hrightSeam).elim
      · exact (hseam hleftSeam).elim
  · intro hseam
    exact ⟨Or.inr hseam, Or.inr hseam⟩

private theorem pathCut_halves_edge_inter_eq_seamEdges
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    pathCutLeftHalfEdges B P ∩ pathCutRightHalfEdges B P =
      pathCutSeamEdges B P := by
  apply Set.ext
  intro q
  change ((∃ d, d ∈ pathCutLeftHalfDarts B P ∧
      edgeClass B.map.toCombinatorialMap d = q) ∧
    ∃ e, e ∈ pathCutRightHalfDarts B P ∧
      edgeClass B.map.toCombinatorialMap e = q) ↔
    ∃ d, d ∈ pathCutSeamDarts B P ∧ edgeClass B.map.toCombinatorialMap d = q
  constructor
  · rintro ⟨⟨d, hdL, hqL⟩, ⟨e, heR, hqR⟩⟩
    have hrel : B.map.toCombinatorialMap.edgeInv.SameCycle d e :=
      Quotient.exact (hqL.trans hqR.symm)
    rcases (CombinatorialMap.edgeInv_sameCycle_iff
        B.map.toCombinatorialMap d e).mp hrel with hde | hde
    · have heL : d ∈ pathCutRightHalfDarts B P := by simpa [hde] using heR
      have hdSeam : d ∈ pathCutSeamDarts B P := by
        rw [← pathCut_halves_inter_eq_seam B P]
        exact ⟨hdL, heL⟩
      exact ⟨d, hdSeam, hqL⟩
    · have hdR : d ∈ pathCutRightHalfDarts B P := by
        have hflip := pathCutRightHalf_edgeInv_mem B P heR
        simpa [hde, B.map.toCombinatorialMap.edgeInv_invol] using hflip
      have hdSeam : d ∈ pathCutSeamDarts B P := by
        rw [← pathCut_halves_inter_eq_seam B P]
        exact ⟨hdL, hdR⟩
      exact ⟨d, hdSeam, hqL⟩
  · rintro ⟨d, hdSeam, hq⟩
    exact ⟨⟨d, Or.inr hdSeam, hq⟩, ⟨d, Or.inr hdSeam, hq⟩⟩

private theorem pathCutHalf_edgeClass_injOn_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    Set.InjOn (edgeClass B.map.toCombinatorialMap)
      (↑(P.darts.toFinset) : Set D) := by
  intro d hd e he hclass
  have hd' : d ∈ P.darts := by simpa using hd
  have he' : e ∈ P.darts := by simpa using he
  have hrel : B.map.toCombinatorialMap.edgeInv.SameCycle d e :=
    Quotient.exact hclass
  rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap d e).mp
      hrel with hde | hde
  · exact hde.symm
  · have hnot := pathCutHalf_pathDart_flip_not_mem B P hd'
    exact False.elim (hnot (hde ▸ he'))

private theorem pathCut_seamEdges_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    letI : DecidableRel (Equiv.Perm.SameCycle
      B.map.toCombinatorialMap.edgeInv) := Classical.decRel _
    letI : Fintype (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :=
      Quotient.fintype _
    letI : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutSeamEdges B P) := Classical.decPred _
    (Finset.univ.filter (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutSeamEdges B P)).card = n := by
  classical
  let M := B.map.toCombinatorialMap
  let pathEdges : Finset (CombinatorialMap.EdgeQuotient M) :=
    P.darts.toFinset.image (edgeClass M)
  let seamEdges : Finset (CombinatorialMap.EdgeQuotient M) :=
    Finset.univ.filter (fun q => q ∈ pathCutSeamEdges B P)
  have hseamEdges : seamEdges = pathEdges := by
    ext q
    simp only [seamEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      pathEdges, Finset.mem_image, List.mem_toFinset]
    change (∃ d, (d ∈ P.darts ∨ M.edgeInv d ∈ P.darts) ∧
        edgeClass M d = q) ↔
      ∃ d ∈ P.darts, edgeClass M d = q
    constructor
    · rintro ⟨d, hd | hd, hq⟩
      · exact ⟨d, hd, hq⟩
      · refine ⟨M.edgeInv d, hd, ?_⟩
        have hclass : edgeClass M (M.edgeInv d) = edgeClass M d := by
          apply Quotient.sound
          exact (CombinatorialMap.edgeInv_sameCycle_iff M (M.edgeInv d) d).2
            (Or.inr (M.edgeInv_invol d).symm)
        exact hclass.trans hq
    · rintro ⟨d, hd, hq⟩
      exact ⟨d, Or.inl hd, hq⟩
  have hcardPath : pathEdges.card = n := by
    dsimp [pathEdges]
    rw [Finset.card_image_iff.mpr (pathCutHalf_edgeClass_injOn_path B P),
      List.toFinset_card_of_nodup (pathCutHalf_simplePath_darts_nodup P),
      P.darts_length]
  have hcardSeam : seamEdges.card = n := by rw [hseamEdges, hcardPath]
  simpa [seamEdges] using hcardSeam





theorem pathCutHalves_edge_card_sum
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    letI : DecidableRel (Equiv.Perm.SameCycle
      B.map.toCombinatorialMap.edgeInv) := Classical.decRel _
    letI : Fintype (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :=
      Quotient.fintype _
    letI : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutLeftHalfEdges B P) := Classical.decPred _
    letI : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutRightHalfEdges B P) := Classical.decPred _
    (Finset.univ.filter (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutLeftHalfEdges B P)).card +
      (Finset.univ.filter (fun q : CombinatorialMap.EdgeQuotient
        B.map.toCombinatorialMap => q ∈ pathCutRightHalfEdges B P)).card =
      B.map.toCombinatorialMap.numEdges + n := by
  classical
  let M := B.map.toCombinatorialMap
  let L : Finset (CombinatorialMap.EdgeQuotient M) := Finset.univ.filter
    (fun q => q ∈ pathCutLeftHalfEdges B P)
  let R : Finset (CombinatorialMap.EdgeQuotient M) := Finset.univ.filter
    (fun q => q ∈ pathCutRightHalfEdges B P)
  let S : Finset (CombinatorialMap.EdgeQuotient M) := Finset.univ.filter
    (fun q => q ∈ pathCutSeamEdges B P)
  have hUnion : L ∪ R = Finset.univ := by
    ext q
    simp only [L, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      R]
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨d, rfl⟩ := Quotient.exists_rep q
      rcases pathCut_halves_cover B P d with hleft | hright
      · exact Or.inl ⟨d, hleft, rfl⟩
      · exact Or.inr ⟨d, hright, rfl⟩
  have hInter : L ∩ R = S := by
    ext q
    simp only [L, R, S, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and]
    have h := congrArg (fun T : Set (CombinatorialMap.EdgeQuotient M) => q ∈ T)
      (pathCut_halves_edge_inter_eq_seamEdges B P)
    exact Iff.of_eq h
  have hcardS : S.card = n := by
    simpa [S, M] using pathCut_seamEdges_card B P
  calc
    (Finset.univ.filter (fun q : CombinatorialMap.EdgeQuotient M =>
        q ∈ pathCutLeftHalfEdges B P)).card +
      (Finset.univ.filter (fun q : CombinatorialMap.EdgeQuotient M =>
        q ∈ pathCutRightHalfEdges B P)).card = L.card + R.card := by
      rfl
    _ = (L ∪ R).card + (L ∩ R).card := by rw [Finset.card_union_add_card_inter]
    _ = B.map.toCombinatorialMap.numEdges + n := by
      rw [hUnion, hInter, Finset.card_univ, hcardS]
      rfl





theorem pathCutHalves_card_sum
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    letI : DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P) :=
      Classical.decPred _
    letI : DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P) :=
      Classical.decPred _
    Fintype.card {d : D // d ∈ pathCutLeftHalfDarts B P} +
        Fintype.card {d : D // d ∈ pathCutRightHalfDarts B P} =
      Fintype.card D + 2 * n := by
  classical
  let L : Finset D := Finset.univ.filter
    (fun d => d ∈ pathCutLeftHalfDarts B P)
  let R : Finset D := Finset.univ.filter
    (fun d => d ∈ pathCutRightHalfDarts B P)
  let S : Finset D := Finset.univ.filter
    (fun d => d ∈ pathCutSeamDarts B P)
  have hUnion : L ∪ R = Finset.univ := by
    ext d
    simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact pathCut_halves_cover B P d
  have hInter : L ∩ R = S := by
    ext d
    simp only [L, R, S, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact (pathCut_halves_inter_eq_seam B P).symm ▸ Iff.rfl
  have hcardL : Fintype.card {d : D // d ∈ pathCutLeftHalfDarts B P} = L.card := by
    rw [Fintype.card_subtype]
  have hcardR : Fintype.card {d : D // d ∈ pathCutRightHalfDarts B P} = R.card := by
    rw [Fintype.card_subtype]
  have hcardS :
      letI : DecidablePred (fun d : D => d ∈ pathCutSeamDarts B P) :=
        Classical.decPred _
      S.card = 2 * n := by
    have hsub : Fintype.card {d : D // d ∈ pathCutSeamDarts B P} = S.card := by
      rw [Fintype.card_subtype]
    calc
      S.card = Fintype.card {d : D // d ∈ pathCutSeamDarts B P} := hsub.symm
      _ = 2 * n := pathCutSeamDarts_card B P
  calc
    Fintype.card {d : D // d ∈ pathCutLeftHalfDarts B P} +
        Fintype.card {d : D // d ∈ pathCutRightHalfDarts B P} = L.card + R.card := by
      rw [hcardL, hcardR]
    _ = (L ∪ R).card + (L ∩ R).card := by rw [Finset.card_union_add_card_inter]
    _ = Fintype.card D + 2 * n := by
      rw [hUnion, hInter, Finset.card_univ, hcardS]

end DirectedDistances.PlanarMap
