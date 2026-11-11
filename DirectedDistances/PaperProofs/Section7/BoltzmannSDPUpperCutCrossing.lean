module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperStrictCrossing
public import DirectedDistances.PlanarMap.PlanarPathCutNoStrictLeft

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/

/-! First contact with a complete cut, with the outer-boundary incoming-corner
obligation isolated below. The OPEN proposition is defined, never asserted.
This file does not claim Lemma 7.13 or boundary-path intersection is proved. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW DirectedDistances.PlanarMap

attribute [local instance 1100] presentDartQuiver

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {l r n : ℕ}




theorem boltzmannSdpUpper_offCut_all_left
    (B : BipolarTriangulationWithBoundaryBase D l r)
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∉ C.vertices)
    {a : D} (ha : a ∈ pathCutLeftDarts B C)
    (hav : dartTailVertex B.map a = v) :
    ∀ d : D, dartTailVertex B.map d = v → d ∈ pathCutLeftDarts B C := by
  rcases pathCut_vertex_darts_one_sided B C hv with hleft | hright
  · exact hleft
  · have hseam : a ∉ pathCutSeamDarts B C := by
      intro h
      exact hv (hav ▸ pathCutSeamDarts_tailVertex_mem B C h)
    exact (Set.disjoint_left.mp (pathCut_offSeam_disjoint B C)
      ⟨ha, hseam⟩ ⟨hright a hav, hseam⟩).elim





theorem boltzmannSdpUpper_firstCutContact
    (B : BipolarTriangulationWithBoundaryBase D l r)
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {s : MapVertex B.map} {m : ℕ}
    (Q : SimpleDirectedDartPath B.map s B.sink m)
    (hs : s ∉ C.vertices)
    (hleft : ∀ d : D, dartTailVertex B.map d = s → d ∈ pathCutLeftDarts B C) :
    ∃ d ∈ Q.darts,
      d ∈ pathCutLeftDarts B C \ pathCutSeamDarts B C ∧
      dartTailVertex B.map d ∉ C.vertices ∧ dartHeadVertex B.map d ∈ C.vertices := by
  classical
  have hex : ∃ a : ℕ, ∃ ha : a < Q.vertices.length,
      Q.vertices.get ⟨a, ha⟩ ∈ C.vertices := by
    refine ⟨m, by rw [Q.vertices_length]; omega, ?_⟩
    rw [Q.end_vertex]
    simpa only [C.end_vertex] using List.get_mem C.vertices
      ⟨n, by rw [C.vertices_length]; omega⟩
  let a := Nat.find hex
  obtain ⟨ha, hcontact⟩ := Nat.find_spec hex
  have hbefore (b : ℕ) (hb : b < a) (hbv : b < Q.vertices.length) :
      Q.vertices.get ⟨b, hbv⟩ ∉ C.vertices := by
    intro h
    exact Nat.find_min hex hb ⟨hbv, h⟩
  have ha0 : 0 < a := by
    by_contra h
    have hz : a = 0 := by omega
    have heq : Q.vertices.get ⟨a, ha⟩ = s := by
      simpa only [hz] using Q.start_vertex
    exact hs (heq ▸ hcontact)
  have hwalk : ∀ (b : ℕ) (hb : b < a), ∀ d : D,
      dartTailVertex B.map d = Q.vertices.get ⟨b, by omega⟩ →
        d ∈ pathCutLeftDarts B C := by
    intro b
    induction b with
    | zero =>
      intro hb d hd
      exact hleft d (hd.trans Q.start_vertex)
    | succ b ih =>
      intro hb d hd
      have hbD : b < Q.darts.length := by
        have hqv := Q.vertices_length
        have hqd := Q.darts_length
        omega
      let e := Q.darts.get ⟨b, hbD⟩
      have he := Q.edge_step ⟨b, hbD⟩
      have heL : e ∈ pathCutLeftDarts B C := ih (by omega) e he.2.2.1.symm
      have heN : e ∉ pathCutSeamDarts B C := by
        intro h
        exact hbefore b (by omega) (by omega)
          (he.2.2.1 ▸ pathCutSeamDarts_tailVertex_mem B C h)
      have hflip := pathCutLeft_edgeInv_mem B C heL heN
      have hflipV : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv e) =
          Q.vertices.get ⟨b + 1, by omega⟩ := he.2.2.2.symm
      exact boltzmannSdpUpper_offCut_all_left B C
        (hbefore (b + 1) hb (by omega)) hflip hflipV d hd
  have haD : a - 1 < Q.darts.length := by
    have hqv := Q.vertices_length
    have hqd := Q.darts_length
    omega
  let d := Q.darts.get ⟨a - 1, haD⟩
  have hd := Q.edge_step ⟨a - 1, haD⟩
  have hv : dartHeadVertex B.map d = Q.vertices.get ⟨a, ha⟩ := by
    simpa only [Nat.sub_add_cancel ha0] using hd.2.2.2.symm
  have ht : dartTailVertex B.map d ∉ C.vertices := by
    rw [← hd.2.2.1]
    exact hbefore (a - 1) (by omega) (by omega)
  refine ⟨d, List.get_mem _ _, ⟨hwalk (a - 1) (by omega) d hd.2.2.1.symm, ?_⟩,
    ht, hv.symm ▸ hcontact⟩
  intro h
  exact ht (pathCutSeamDarts_tailVertex_mem B C h)






@[expose] def boltzmannSdpUpper_outerIncomingCorner_OPEN : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D], ∀ l r n : ℕ,
    ∀ B : BipolarTriangulationWithBoundaryBase D l r,
      ∀ C : SimpleDirectedDartPath B.map B.source B.sink n,
        ∀ a : D, a ∈ C.darts → a ∈ B.leftPath.darts →
          ∀ d : D, B.map.tail d → dartHeadVertex B.map d = dartHeadVertex B.map a →
            d ∉ pathCutLeftDarts B C \ pathCutSeamDarts B C




private theorem cutCrossing_not_mem_drop {V : Type*} (L : List V) (hL : L.Nodup)
    (i : Fin L.length) (j : ℕ) (hij : i.val < j) : L.get i ∉ L.drop j := by
  intro h
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp h
  have hkj : j + k.val < L.length := by
    have := k.isLt
    simp only [List.length_drop] at this
    omega
  have heq : L.get ⟨j + k.val, hkj⟩ = L.get i := by
    simpa only [List.get_eq_getElem, List.getElem_drop] using hk
  have hval : j + k.val = i.val := congrArg Fin.val (hL.get_inj_iff.mp heq)
  omega




private theorem cutCrossing_incoming_of_mem {M : DirectedMapWithMissing D}
    {s t v : MapVertex M} {a : ℕ} (P : SimpleDirectedDartPath M s t a)
    (hv : v ∈ P.vertices) (hne : v ≠ s) :
    ∃ d ∈ P.darts, dartHeadVertex M d = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hil : i.val ≤ a := by
    have := i.isLt
    have := P.vertices_length
    omega
  have hi0 : 0 < i.val := by
    by_contra h
    have hz : i.val = 0 := by omega
    have hs : P.vertices.get i = s := by
      have heq : i = ⟨0, by rw [P.vertices_length]; omega⟩ := Fin.ext hz
      rw [heq, P.start_vertex]
    exact hne (hi.symm.trans hs)
  let j : Fin P.darts.length := ⟨i.val - 1, by rw [P.darts_length]; omega⟩
  have hj := P.edge_step j
  have hidx : (⟨j.val + 1, by rw [P.vertices_length]; dsimp [j]; omega⟩ :
      Fin P.vertices.length) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  refine ⟨P.darts.get j, List.get_mem _ _, ?_⟩
  rw [hidx] at hj
  exact hj.2.2.2.symm.trans hi





theorem boltzmannSdpUpper_boundaryExtension_lists
    (B : BipolarTriangulationWithBoundaryBase D l r) (j : Fin (l + 1))
    {a : ℕ} (P : SimpleDirectedDartPath B.map B.source
      (B.leftPath.vertices.get ⟨j.val, by rw [B.leftPath.vertices_length]; exact j.isLt⟩)
      a) :
    (P.appendAcyclic B.map B.acyclic (B.leftPath.suffix j)).darts =
        P.darts ++ B.leftPath.darts.drop j.val ∧
      (P.appendAcyclic B.map B.acyclic (B.leftPath.suffix j)).vertices =
        P.vertices.take a ++ B.leftPath.vertices.drop j.val := by
  constructor
  · rw [SimpleDirectedDartPath.appendAcyclic_darts, B.leftPath.suffix_darts]
  · change P.vertices.take a ++ (B.leftPath.suffix j).vertices = _
    rw [B.leftPath.suffix_vertices]






theorem boltzmannSdpUpper_outerIncomingCorner_reduction :
    boltzmannSdpUpper_outerIncomingCorner_OPEN →
      boltzmannSdpUpper_completeCutCrossing_OPEN := by
  intro hcorner
  apply boltzmannSdpUpper_strictBoundaryPathIntersection_iff_completeCut.mp
  intro r q i j _hi _hj _hi0 hij _hjL p z
  classical
  let B := q.1.2.2.out.B
  obtain ⟨P, hP⟩ := boltzmannSdpUpper_presentPath_exists_simple B.map B.acyclic p
  obtain ⟨Q, hQ⟩ := boltzmannSdpUpper_presentPath_exists_simple B.map B.acyclic z
  change SimpleDirectedDartPath B.map B.source
    (B.leftPath.vertices.get ⟨j.val, by rw [B.leftPath.vertices_length]; exact j.isLt⟩)
    p.length at P
  let R := B.leftPath.suffix j
  let C := P.appendAcyclic B.map B.acyclic R
  have hCd : C.darts = P.darts ++ B.leftPath.darts.drop j.val :=
    (boltzmannSdpUpper_boundaryExtension_lists B j P).1
  have hCv : C.vertices = P.vertices.take p.length ++ B.leftPath.vertices.drop j.val :=
    (boltzmannSdpUpper_boundaryExtension_lists B j P).2
  by_contra hmeet
  have hdisjoint : ∀ v, v ∈ P.vertices → v ∉ Q.vertices := by
    intro v hv hvQ
    exact hmeet ⟨v, hP ▸ hv, hQ ▸ hvQ⟩
  have hs : boltzmannSdpUpper_leftVertex q i ∉ C.vertices := by
    rw [hCv, List.mem_append]
    rintro (hpref | hsuffix)
    · exact hdisjoint _ (List.mem_of_mem_take hpref)
        (by simpa only [Q.start_vertex] using
          (List.get_mem Q.vertices ⟨0, by rw [Q.vertices_length]; omega⟩))
    · exact cutCrossing_not_mem_drop B.leftPath.vertices B.leftPath.vertices_nodup
        ⟨i.val, by rw [B.leftPath.vertices_length]; exact i.isLt⟩ j.val hij hsuffix
  have hiL : i.val < q.1.1 := by omega
  let a : Fin B.leftPath.darts.length := ⟨i.val, by
    rw [B.leftPath.darts_length]
    exact hiL⟩
  have ha : B.leftPath.darts.get a ∈ pathCutLeftDarts B C := by
    refine ⟨B.leftPath.darts.get a, Or.inl ?_, Relation.ReflTransGen.refl⟩
    exact (mem_pathCutLeftOuterArc_iff B _).mpr (List.get_mem _ _)
  have hav : dartTailVertex B.map (B.leftPath.darts.get a) =
      boltzmannSdpUpper_leftVertex q i := (B.leftPath.edge_step a).2.2.1.symm
  have hleft := boltzmannSdpUpper_offCut_all_left B C hs ha hav
  obtain ⟨d, hdQ, hdleft, hdt, hdh⟩ :=
    boltzmannSdpUpper_firstCutContact B C Q hs hleft
  have hdNotP : dartHeadVertex B.map d ∉ P.vertices := by
    intro h
    apply hdisjoint _ h
    obtain ⟨u, hu⟩ := List.mem_iff_get.mp hdQ
    have hstep := Q.edge_step u
    rw [← hu, ← hstep.2.2.2]
    exact List.get_mem _ _
  have hdR : dartHeadVertex B.map d ∈ R.vertices := by
    rw [hCv, List.mem_append] at hdh
    rcases hdh with hpref | hsuffix
    · exact (hdNotP (List.mem_of_mem_take hpref)).elim
    · simpa only [R, B.leftPath.suffix_vertices] using hsuffix
  have hdStart : dartHeadVertex B.map d ≠
      B.leftPath.vertices.get ⟨j.val, by rw [B.leftPath.vertices_length]; exact j.isLt⟩ := by
    intro h
    apply hdNotP
    rw [h]
    simpa only [P.end_vertex] using List.get_mem P.vertices
      ⟨p.length, by rw [P.vertices_length]; omega⟩
  obtain ⟨e, heR, heHead⟩ := cutCrossing_incoming_of_mem R hdR hdStart
  have heDrop : e ∈ B.leftPath.darts.drop j.val := by
    simpa only [R, B.leftPath.suffix_darts] using heR
  have heL : e ∈ B.leftPath.darts := by
    exact List.mem_of_mem_drop heDrop
  have heC : e ∈ C.darts := by
    rw [hCd, List.mem_append]
    exact Or.inr heDrop
  obtain ⟨u, hu⟩ := List.mem_iff_get.mp hdQ
  have hdTail : B.map.tail d := hu ▸ (Q.edge_step u).2.1
  exact hcorner _ _ _ _ B C e heC heL d hdTail heHead.symm hdleft






theorem boltzmannSdpUpper_outerIncomingCorner_boundaryReduction :
    boltzmannSdpUpper_outerIncomingCorner_OPEN →
      boltzmannSdpUpper_boundaryPathIntersection :=
  fun h => boltzmannSdpUpper_boundaryPathIntersection_iff_completeCut.mpr
    (boltzmannSdpUpper_outerIncomingCorner_reduction h)

end DirectedDistances.PaperProofs.Section7
