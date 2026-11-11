module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperCutCrossing
public import DirectedDistances.PlanarMap.BipolarCanonicalTrees

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/

/-! The outer incoming corner excludes strict-left entry, including at the sink.
The boundary intersection consequence is a helper, not Lemma 7.13 itself. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {l r n : ℕ}




private theorem outerCorner_incoming_unique
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {a b : D}
    (ha : a ∈ P.darts) (hb : b ∈ P.darts)
    (h : dartHeadVertex M a = dartHeadVertex M b) : a = b := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hb
  have hi := P.edge_step i
  have hj := P.edge_step j
  have he := hi.2.2.2.trans (h.trans hj.2.2.2.symm)
  have he' := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp he)
  have hij : i.val = j.val := by dsimp at he'; omega
  exact congrArg P.darts.get (Fin.ext hij)




private theorem outerCorner_tail_of_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {a : D} (ha : a ∈ P.darts) :
    M.tail a := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
  exact (P.edge_step i).2.1




private theorem outerCorner_iterate_vertex
    (B : BipolarTriangulationWithBoundaryBase D l r) (q : D) (j : ℕ) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot.symm^[j] q) =
      dartTailVertex B.map q := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact vertexRotationCycle_successor_mem B _ ⟨_, ih⟩





private theorem outerCorner_incoming_rotation
    (B : BipolarTriangulationWithBoundaryBase D l r) {a d : D}
    (ha : a ∈ B.leftPath.darts) (hd : B.map.tail d)
    (hhead : dartHeadVertex B.map d = dartHeadVertex B.map a) :
    ∃ k : ℕ,
      B.map.toCombinatorialMap.rot.symm^[k]
          (B.map.toCombinatorialMap.edgeInv d) = B.map.toCombinatorialMap.edgeInv a ∧
      (∀ j, j ≤ k → ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm^[j]
        (B.map.toCombinatorialMap.edgeInv d))) ∧
      ∀ j, j < k → B.map.toCombinatorialMap.rot.symm^[j]
        (B.map.toCombinatorialMap.edgeInv d) ≠ B.map.toCombinatorialMap.edgeInv a := by
  classical
  let M := B.map.toCombinatorialMap
  let p : Equiv.Perm D := M.rot.symm
  let v := dartHeadVertex B.map a
  let x := M.edgeInv d
  let y := M.edgeInv a
  have hat : B.map.tail a := outerCorner_tail_of_mem B.leftPath ha
  have hxv : dartTailVertex B.map x = v := hhead
  have hyv : dartTailVertex B.map y = v := rfl
  have hsource : v ≠ B.source := by
    intro h
    exact B.isSource ⟨dartTailVertex B.map a, a, B.noMissingDarts a,
      hat, rfl, h⟩
  have hcycle : p.SameCycle x y := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hxv.trans hyv.symm)
  have hex : ∃ k : ℕ, p^[k] x = y := by
    obtain ⟨k, _, hk⟩ := hcycle.exists_pow_eq'
    exact ⟨k, by simpa only [Equiv.Perm.iterate_eq_pow] using hk⟩
  let k := Nat.find hex
  have hk : p^[k] x = y := Nat.find_spec hex
  have hbefore (j : ℕ) (hj : j < k) : p^[j] x ≠ y := Nat.find_min hex hj
  have hvertex (j : ℕ) : dartTailVertex B.map (p^[j] x) = v :=
    (outerCorner_iterate_vertex B x j).trans hxv
  have hstay (q : D) (hqv : dartTailVertex B.map q = v)
      (hqt : ¬ B.map.tail q) (hqne : q ≠ y) : ¬ B.map.tail (p q) := by
    by_cases ht : v = B.sink
    · intro htail
      have hqnext := vertexRotationCycle_successor_mem B v ⟨q, hqv⟩
      exact B.isSink ⟨dartHeadVertex B.map (p q), p q, B.noMissingDarts _,
        htail, hqnext.trans ht, rfl⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
      have hil : i.val < l := by simpa only [B.leftPath.darts_length] using i.isLt
      have hin : i.val + 1 < l := by
        by_contra hbound
        have heq : i.val + 1 = l := by omega
        have hstep := (B.leftPath.edge_step i).2.2.2
        have he : dartHeadVertex B.map a = B.sink := by
          rw [hi] at hstep
          simpa only [heq, B.leftPath.end_vertex] using hstep.symm
        exact ht he
      have hynext : B.map.tail (p y) := by
        change B.map.tail (M.faceSucc a)
        rw [← hi]
        rw [show M.faceSucc (B.leftPath.darts.get i) =
          B.leftPath.darts[i.val + 1]'(by
            simpa only [B.leftPath.darts_length] using hin) from
            outerFace_leftPath_successor B i.val hin]
        exact outerCorner_tail_of_mem B.leftPath (List.getElem_mem _)
      obtain ⟨li, ro, hliV, hliN, hroV, hroT, hliNext, hroNext,
        hstayIn, hstayOut, hunique, huniqueOut⟩ := incoming_block B v hsource ht
      have hyli : y = li := hunique y hyv
        ((B.map.tail_iff a (B.noMissingDarts a)).mp hat) hynext
      exact hstayIn q hqv hqt (fun he => hqne (he.trans hyli.symm))
  have hincoming : ∀ j, j ≤ k → ¬ B.map.tail (p^[j] x) := by
    intro j
    induction j with
    | zero => intro _; exact (B.map.tail_iff d (B.noMissingDarts d)).mp hd
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply']
      exact hstay _ (hvertex j) (ih (by omega)) (hbefore j (by omega))
  exact ⟨k, hk, hincoming, hbefore⟩





theorem boltzmannSdpUpper_outerIncomingCorner_base
    (B : BipolarTriangulationWithBoundaryBase D l r)
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {a : D} (haC : a ∈ C.darts) (haL : a ∈ B.leftPath.darts)
    {d : D} (hd : B.map.tail d)
    (hhead : dartHeadVertex B.map d = dartHeadVertex B.map a) :
    d ∉ pathCutLeftDarts B C \ pathCutSeamDarts B C := by
  classical
  intro hleft
  let M := B.map.toCombinatorialMap
  let p : Equiv.Perm D := M.rot.symm
  let x := M.edgeInv d
  let y := M.edgeInv a
  obtain ⟨k, hk, hincoming, hbefore⟩ :=
    outerCorner_incoming_rotation B haL hd hhead
  obtain ⟨side, hL, hR, hface, hedge⟩ := pathCut_exists_side_coloring B C
  have hstep (j : ℕ) (hj : j < k) : side (p (p^[j] x)) = side (p^[j] x) := by
    let q := p^[j] x
    have hqt : ¬ B.map.tail q := hincoming j (by omega)
    have hqne : q ≠ y := hbefore j hj
    have hqv : dartTailVertex B.map q = dartHeadVertex B.map a :=
      (outerCorner_iterate_vertex B x j).trans hhead
    have hforward : B.map.tail (M.edgeInv q) := by
      by_contra h
      exact hqt ((B.map.tail_iff q (B.noMissingDarts q)).mpr h)
    have hqhead : dartHeadVertex B.map (M.edgeInv q) = dartHeadVertex B.map a := by
      change dartTailVertex B.map (M.edgeInv (M.edgeInv q)) = _
      rw [M.edgeInv_invol]
      exact hqv
    have hnotSeam : q ∉ pathCutSeamDarts B C := by
      rintro (h | h)
      · exact hqt (outerCorner_tail_of_mem C h)
      · have he := outerCorner_incoming_unique C h haC hqhead
        have he' := congrArg M.edgeInv he
        rw [M.edgeInv_invol] at he'
        exact hqne he'
    have hinner : ¬ B.map.IsOuter (M.edgeInv q) := by
      intro hout
      rcases (isOuter_iff_mem_outerArcs B _).mp hout with h | h
      · have he := outerCorner_incoming_unique B.leftPath
          ((mem_pathCutLeftOuterArc_iff B _).mp h) haL hqhead
        have he' := congrArg M.edgeInv he
        rw [M.edgeInv_invol] at he'
        exact hqne he'
      · exact h.2.1 hforward
    exact pathCutSide_eq_rotSymm_of_inner_offSeam B C side hface hedge q
      hinner hnotSeam
  have hscan : ∀ j, j ≤ k → side (p^[j] x) = side x := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply']
      exact (hstep j (by omega)).trans (ih (by omega))
  have hright : side y = false := hR y (Or.inr ⟨a, haC, rfl⟩)
  have hx : side x = false := by
    have he := hscan k le_rfl
    rw [hk] at he
    exact he.symm.trans hright
  have hdcolor : side d = true :=
    (pathCutLeft_mem_iff_side_true_of_sideColoring B C side hL hR hface hedge d).mp
      hleft.1
  have he := hedge d hleft.2
  change side x = side d at he
  rw [hx, hdcolor] at he
  cases he




theorem boltzmannSdpUpper_outerIncomingCorner :
    boltzmannSdpUpper_outerIncomingCorner_OPEN := by
  intro D _ _ l r n B C a haC haL d hd hhead
  exact boltzmannSdpUpper_outerIncomingCorner_base B C haC haL hd hhead




theorem boltzmannSdpUpper_completeCutCrossing :
    boltzmannSdpUpper_completeCutCrossing_OPEN :=
  boltzmannSdpUpper_outerIncomingCorner_reduction boltzmannSdpUpper_outerIncomingCorner




theorem boltzmannSdpUpper_boundaryPathIntersection_proved :
    boltzmannSdpUpper_boundaryPathIntersection :=
  boltzmannSdpUpper_outerIncomingCorner_boundaryReduction
    boltzmannSdpUpper_outerIncomingCorner

end DirectedDistances.PaperProofs.Section7
