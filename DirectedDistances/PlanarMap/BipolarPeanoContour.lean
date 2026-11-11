module

public import DirectedDistances.PlanarMap.FiniteBipolarIncomingBlock
public import DirectedDistances.PlanarMap.BipolarParentTrees

/-! # Upper-left contour successor

Helper toward thm-kmsw (inverse KMSW / Peano path); not the paper result.
Incoming selectors are reverse darts based at their head vertex. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

/-- A forward dart cannot end at the source. Helper toward thm-kmsw
(inverse KMSW / Peano path); not the paper result -/
theorem contour_forward_head_ne_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hd : B.map.tail d) : dartHeadVertex B.map d ≠ B.source := by
  intro h
  exact B.isSource ⟨dartTailVertex B.map d, d, B.noMissingDarts d, hd, rfl, h⟩

/-- The marked source corner makes `rot` go from the first left-boundary
dart to the first right-boundary dart. Helper toward thm-kmsw (inverse KMSW / -/
theorem contour_source_rotation
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.map.toCombinatorialMap.rot
        (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) =
      B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos) := by
  have h := outerFace_sourceCorner_eq_firstLeftDart B
  rw [(corner_consecutiveDarts B _).1,
    B.map.toCombinatorialMap.edgeInv_invol] at h
  exact (congrArg B.map.toCombinatorialMap.rot h).symm.trans
    (B.map.toCombinatorialMap.rot.apply_symm_apply _)

/-- Successor in the upper-left tree contour, with nonselected incoming
edges disconnected at their head. Helper toward thm-kmsw (inverse KMSW / -/
@[expose] noncomputable def contourNext
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) : D := by
  classical
  exact if hd : B.map.tail d then
    if B.map.toCombinatorialMap.edgeInv d =
        leftmostIncoming B (dartHeadVertex B.map d) (contour_forward_head_ne_source B d hd) then
      if ht : dartHeadVertex B.map d = B.sink then
        B.map.toCombinatorialMap.edgeInv d
      else rightmostOutgoing B (dartHeadVertex B.map d) ht
    else B.map.toCombinatorialMap.edgeInv d
  else B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv d)

/-- The contour begins at the rightmost source edge. Helper toward thm-kmsw
(inverse KMSW / Peano path); not the paper result -/
@[expose] noncomputable def contourStart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : D :=
  rightmostOutgoing B B.source (bipolar_source_ne_sink B)

/-- The start is the first right-boundary dart. Helper toward thm-kmsw
(inverse KMSW / Peano path); not the paper result -/
theorem contourStart_eq_firstRightDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    contourStart B = B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos) :=
  rightmostOutgoing_source_eq_firstRightDart B

private theorem contour_rot_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot d) = dartTailVertex B.map d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.rot d).apply_left

private theorem contour_first_spec
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (hn : 0 < n) :
    M.tail (P.firstDart hn) ∧ dartTailVertex M (P.firstDart hn) = s := by
  have h := P.edge_step ⟨0, by rw [P.darts_length]; exact hn⟩
  exact ⟨h.2.1, h.2.2.1.symm.trans P.start_vertex⟩

private theorem contour_rightmost_spec
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (ht : v ≠ B.sink) :
    B.map.tail (rightmostOutgoing B v ht) ∧
      dartTailVertex B.map (rightmostOutgoing B v ht) = v := by
  classical
  by_cases hs : v = B.source
  · subst v
    rw [rightmostOutgoing_source_eq_firstRightDart]
    exact contour_first_spec B.rightPath _
  · have h := rightmostOutgoing_internal_characterization B v hs ht
    exact ⟨h.2.1, h.1⟩

private theorem contour_next_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (contourNext B d) = dartHeadVertex B.map d := by
  classical
  unfold contourNext
  split
  · split
    · split
      · rfl
      · exact (contour_rightmost_spec B _ _).2
    · rfl
  · exact contour_rot_vertex B _

private theorem contour_internal_rule
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (d : D) (hv : dartHeadVertex B.map d = v) :
    contourNext B d = (by
      classical
      exact if B.map.tail d then
        if B.map.toCombinatorialMap.edgeInv d = leftmostIncoming B v hs then
          rightmostOutgoing B v ht else B.map.toCombinatorialMap.edgeInv d
      else B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv d)) := by
  classical
  by_cases hd : B.map.tail d
  · simp only [contourNext, dite_eq_left hd, ite_eq_left hd]
    simp only [hv, dite_eq_right ht]
  · simp only [contourNext, dite_eq_right hd, ite_eq_right hd]

private theorem contour_internal_mixed
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (a b : D) (hav : dartHeadVertex B.map a = v) (hbv : dartHeadVertex B.map b = v)
    (ha : ¬ B.map.tail a) (hb : B.map.tail b) :
    contourNext B a ≠ contourNext B b := by
  classical
  have hai : B.map.tail (B.map.toCombinatorialMap.edgeInv a) := by
    by_contra h
    exact ha ((B.map.tail_iff a (B.noMissingDarts a)).2 h)
  have hbi : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv b) :=
    (B.map.tail_iff b (B.noMissingDarts b)).1 hb
  rw [contour_internal_rule B v hs ht a hav, ite_eq_right ha,
    contour_internal_rule B v hs ht b hbv, ite_eq_left hb]
  by_cases hbsel : B.map.toCombinatorialMap.edgeInv b = leftmostIncoming B v hs
  · rw [ite_eq_left hbsel]
    intro heq
    have hpred := (rightmostOutgoing_internal_characterization B v hs ht).2.2.1
    have h := congrArg B.map.toCombinatorialMap.rot.symm heq
    have heq' : B.map.toCombinatorialMap.edgeInv a =
        B.map.toCombinatorialMap.rot.symm (rightmostOutgoing B v ht) := by
      simpa only [Equiv.symm_apply_apply] using h
    exact hpred (heq' ▸ hai)
  · rw [ite_eq_right hbsel]
    intro heq
    have hvertex : dartTailVertex B.map
        (B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv a)) = v :=
      (contour_rot_vertex B _).trans hav
    have hnot : ¬ B.map.tail
        (B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv a)) :=
      heq.symm ▸ hbi
    have hprev : B.map.tail (B.map.toCombinatorialMap.rot.symm
        (B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv a))) := by
      simpa only [Equiv.symm_apply_apply] using hai
    have hsel := (leftmostIncoming_internal_characterization B v hs ht).2.2.2
      _ hvertex hnot hprev
    exact hbsel (heq.symm.trans hsel)

private theorem contour_internal_forward_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (a b : D) (hav : dartHeadVertex B.map a = v) (hbv : dartHeadVertex B.map b = v)
    (ha : B.map.tail a) (hb : B.map.tail b)
    (heq : contourNext B a = contourNext B b) : a = b := by
  classical
  have hai := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
  have hbi := (B.map.tail_iff b (B.noMissingDarts b)).1 hb
  rw [contour_internal_rule B v hs ht a hav, ite_eq_left ha,
    contour_internal_rule B v hs ht b hbv, ite_eq_left hb] at heq
  by_cases hasel : B.map.toCombinatorialMap.edgeInv a = leftmostIncoming B v hs
  · rw [ite_eq_left hasel] at heq
    by_cases hbsel : B.map.toCombinatorialMap.edgeInv b = leftmostIncoming B v hs
    · exact B.map.toCombinatorialMap.edgeInv.injective (hasel.trans hbsel.symm)
    · rw [ite_eq_right hbsel] at heq
      exact False.elim (hbi (heq ▸ (contour_rightmost_spec B v ht).1))
  · rw [ite_eq_right hasel] at heq
    by_cases hbsel : B.map.toCombinatorialMap.edgeInv b = leftmostIncoming B v hs
    · rw [ite_eq_left hbsel] at heq
      exact False.elim (hai (heq.symm ▸ (contour_rightmost_spec B v ht).1))
    · rw [ite_eq_right hbsel] at heq
      exact B.map.toCombinatorialMap.edgeInv.injective heq

/-- The upper-left contour successor is injective on the original dart
carrier, including dangling ends. Helper toward thm-kmsw (inverse KMSW / -/
theorem contourNext_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Function.Injective (contourNext B) := by
  classical
  intro a b heq
  have hv : dartHeadVertex B.map a = dartHeadVertex B.map b :=
    (contour_next_vertex B a).symm.trans
      ((congrArg (dartTailVertex B.map) heq).trans (contour_next_vertex B b))
  by_cases hs : dartHeadVertex B.map a = B.source
  · have ha : ¬ B.map.tail a := fun ha => contour_forward_head_ne_source B a ha hs
    have hb : ¬ B.map.tail b := fun hb =>
      contour_forward_head_ne_source B b hb (hv.symm.trans hs)
    simp only [contourNext, dite_eq_right ha, dite_eq_right hb] at heq
    exact B.map.toCombinatorialMap.edgeInv.injective
      (B.map.toCombinatorialMap.rot.injective heq)
  · by_cases ht : dartHeadVertex B.map a = B.sink
    · have hall (d : D) (hd : dartHeadVertex B.map d = B.sink) : B.map.tail d := by
        by_contra h
        have hi : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
          by_contra hi
          exact h ((B.map.tail_iff d (B.noMissingDarts d)).2 hi)
        exact B.isSink ⟨dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv d),
          B.map.toCombinatorialMap.edgeInv d, B.noMissingDarts _, hi, hd, rfl⟩
      have ha := hall a ht
      have hb := hall b (hv.symm.trans ht)
      have hnext (d : D) (hd : B.map.tail d) (hdt : dartHeadVertex B.map d = B.sink) :
          contourNext B d = B.map.toCombinatorialMap.edgeInv d := by
        simp only [contourNext, dite_eq_left hd, dite_eq_left hdt, ite_self]
      rw [hnext a ha ht, hnext b hb (hv.symm.trans ht)] at heq
      exact B.map.toCombinatorialMap.edgeInv.injective heq
    · by_cases ha : B.map.tail a
      · by_cases hb : B.map.tail b
        · exact contour_internal_forward_injective B _ hs ht a b rfl hv.symm ha hb heq
        · exact False.elim (contour_internal_mixed B _ hs ht b a hv.symm rfl hb ha heq.symm)
      · by_cases hb : B.map.tail b
        · exact False.elim (contour_internal_mixed B _ hs ht a b rfl hv.symm ha hb heq)
        · simp only [contourNext, dite_eq_right ha, dite_eq_right hb] at heq
          exact B.map.toCombinatorialMap.edgeInv.injective
            (B.map.toCombinatorialMap.rot.injective heq)

/-- The actual upper-left contour permutation of darts. Helper toward
thm-kmsw (inverse KMSW / Peano path); not the paper result -/
@[expose] noncomputable def contourPerm
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : Equiv.Perm D :=
  Equiv.ofBijective (contourNext B)
    ⟨contourNext_injective B, Finite.surjective_of_injective (contourNext_injective B)⟩

private theorem contour_next_sameCycle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    (contourPerm B).SameCycle d (contourNext B d) := by
  exact (Equiv.Perm.SameCycle.refl (contourPerm B) d).apply_right

private theorem contour_outgoing_exit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (hlocal : ∀ q, dartTailVertex B.map q = v → B.map.tail q →
      (contourPerm B).SameCycle q (B.map.toCombinatorialMap.rot q))
    (q : D) (hqv : dartTailVertex B.map q = v) (hq : B.map.tail q) :
    (contourPerm B).SameCycle q (leftmostIncoming B v hs) := by
  classical
  have hli := leftmostIncoming_internal_characterization B v hs ht
  have hrot : B.map.toCombinatorialMap.rot.SameCycle q (leftmostIncoming B v hs) :=
    Quotient.exact (hqv.trans hli.1.symm)
  obtain ⟨n, hn⟩ := hrot.exists_nat_pow_eq
  have hsegment : ∀ n q, dartTailVertex B.map q = v → B.map.tail q →
      (B.map.toCombinatorialMap.rot ^ n) q = leftmostIncoming B v hs →
      (contourPerm B).SameCycle q (leftmostIncoming B v hs) := by
    intro n
    induction n with
    | zero =>
      intro q _ hq heq
      have heq' : q = leftmostIncoming B v hs := heq
      exact False.elim (hli.2.1 (heq' ▸ hq))
    | succ n ih =>
      intro q hqv hq heq
      have hstep := hlocal q hqv hq
      have hnextv := (contour_rot_vertex B q).trans hqv
      by_cases hnext : B.map.tail (B.map.toCombinatorialMap.rot q)
      · have hend : (B.map.toCombinatorialMap.rot ^ n)
            (B.map.toCombinatorialMap.rot q) = leftmostIncoming B v hs := by
          simpa only [pow_succ, Equiv.Perm.mul_apply] using heq
        exact hstep.trans (ih _ hnextv hnext hend)
      · have hpred : B.map.tail (B.map.toCombinatorialMap.rot.symm
            (B.map.toCombinatorialMap.rot q)) := by
          simpa only [Equiv.symm_apply_apply] using hq
        have heq' := hli.2.2.2 _ hnextv hnext hpred
        exact heq' ▸ hstep
  exact hsegment n q hqv hq hn

/-- A forward child dart and its return dart lie in the same contour
cycle. Helper toward thm-kmsw (inverse KMSW / Peano path); not the paper
the subtree excursion; it does not assert the full segment membership law. -/
theorem contour_forward_return_sameCycle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (d : D) (hd : B.map.tail d) :
    (contourPerm B).SameCycle d (B.map.toCombinatorialMap.edgeInv d) := by
  classical
  suffices h : ∀ v (d : D), dartHeadVertex B.map d = v → B.map.tail d →
      (contourPerm B).SameCycle d (B.map.toCombinatorialMap.edgeInv d) from h _ d rfl hd
  intro v
  induction v using (reverseDirectedReach_wellFounded B).induction with
  | h v ih =>
    intro d hdv hd
    have hs : v ≠ B.source := hdv ▸ contour_forward_head_ne_source B d hd
    by_cases hsel : B.map.toCombinatorialMap.edgeInv d = leftmostIncoming B v hs
    · by_cases ht : v = B.sink
      · have hnext : contourNext B d = B.map.toCombinatorialMap.edgeInv d := by
          simp only [contourNext, dite_eq_left hd, hdv, dite_eq_left ht, ite_self]
        exact hnext ▸ contour_next_sameCycle B d
      · have hnext : contourNext B d = rightmostOutgoing B v ht := by
          rw [contour_internal_rule B v hs ht d hdv, ite_eq_left hd, ite_eq_left hsel]
        have hlocal : ∀ q, dartTailVertex B.map q = v → B.map.tail q →
            (contourPerm B).SameCycle q (B.map.toCombinatorialMap.rot q) := by
          intro q hqv hq
          have hstep : B.map.directedStep v (dartHeadVertex B.map q) :=
            ⟨q, B.noMissingDarts q, hq, hqv, rfl⟩
          have hchild := ih (dartHeadVertex B.map q) (Relation.TransGen.single hstep)
            q rfl hq
          have hnot := (B.map.tail_iff q (B.noMissingDarts q)).1 hq
          have hreturn : contourNext B (B.map.toCombinatorialMap.edgeInv q) =
              B.map.toCombinatorialMap.rot q := by
            simp only [contourNext, dite_eq_right hnot, B.map.toCombinatorialMap.edgeInv_invol]
          exact hchild.trans (hreturn ▸ contour_next_sameCycle B _)
        have hexit := contour_outgoing_exit B v hs ht hlocal
          (rightmostOutgoing B v ht) (contour_rightmost_spec B v ht).2
          (contour_rightmost_spec B v ht).1
        exact (hnext ▸ contour_next_sameCycle B d).trans (hsel.symm ▸ hexit)
    · have hnext : contourNext B d = B.map.toCombinatorialMap.edgeInv d := by
        simp only [contourNext, dite_eq_left hd, hdv, ite_eq_right hsel]
      exact hnext ▸ contour_next_sameCycle B d

private theorem contour_inverse_forward
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hd : ¬ B.map.tail d) : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
  by_contra h
  exact hd ((B.map.tail_iff d (B.noMissingDarts d)).2 h)

private theorem contour_outgoing_rotation
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (q : D) (hq : B.map.tail q) :
    (contourPerm B).SameCycle q (B.map.toCombinatorialMap.rot q) := by
  have hnot := (B.map.tail_iff q (B.noMissingDarts q)).1 hq
  have hnext : contourNext B (B.map.toCombinatorialMap.edgeInv q) =
      B.map.toCombinatorialMap.rot q := by
    simp only [contourNext, dite_eq_right hnot, B.map.toCombinatorialMap.edgeInv_invol]
  exact (contour_forward_return_sameCycle B q hq).trans
    (hnext ▸ contour_next_sameCycle B _)

private theorem contour_source_sameCycle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (q : D)
    (hqv : dartTailVertex B.map q = B.source) :
    (contourPerm B).SameCycle (contourStart B) q := by
  have hstartv : dartTailVertex B.map (contourStart B) = B.source :=
    (contour_rightmost_spec B B.source (bipolar_source_ne_sink B)).2
  have hrot : B.map.toCombinatorialMap.rot.SameCycle (contourStart B) q :=
    Quotient.exact (hstartv.trans hqv.symm)
  obtain ⟨n, hn⟩ := hrot.exists_nat_pow_eq
  have hpow : ∀ n, (contourPerm B).SameCycle (contourStart B)
      ((B.map.toCombinatorialMap.rot ^ n) (contourStart B)) := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
      have hvertex : dartTailVertex B.map
          ((B.map.toCombinatorialMap.rot ^ n) (contourStart B)) = B.source := by
        apply Eq.trans _ hstartv
        apply Quotient.sound
        exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.rot
          (contourStart B)).pow_left
      have htail := tail_of_dartTailVertex_eq_source B _ hvertex
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (contour_outgoing_rotation B _ htail)
  exact hn ▸ hpow n

/-- Every dart belongs to the contour cycle starting at the first right
boundary edge. Helper toward thm-kmsw (inverse KMSW / Peano path); not the -/
theorem contour_sameCycle_start
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    (contourPerm B).SameCycle (contourStart B) d := by
  classical
  have hforward : ∀ v (q : D), dartTailVertex B.map q = v → B.map.tail q →
      (contourPerm B).SameCycle (contourStart B) q := by
    intro v
    induction v using (directedReach_wellFounded B).induction with
    | h v ih =>
      intro q hqv hq
      by_cases hs : v = B.source
      · exact contour_source_sameCycle B q (hqv.trans hs)
      · have ht : v ≠ B.sink := by
          intro h
          exact B.isSink ⟨dartHeadVertex B.map q, q, B.noMissingDarts q, hq,
            hqv.trans h, rfl⟩
        have hli := leftmostIncoming_internal_characterization B v hs ht
        let e := B.map.toCombinatorialMap.edgeInv (leftmostIncoming B v hs)
        have he : B.map.tail e := contour_inverse_forward B _ hli.2.1
        have hev : dartHeadVertex B.map e = v := by
          simpa only [e, dartHeadVertex, dartTailVertex,
            B.map.toCombinatorialMap.edgeInv_invol] using hli.1
        have hstep : B.map.directedStep (dartTailVertex B.map e) v :=
          ⟨e, B.noMissingDarts e, he, rfl, hev⟩
        have hparent := ih (dartTailVertex B.map e) (Relation.TransGen.single hstep) e rfl he
        have hreturn : (contourPerm B).SameCycle e (leftmostIncoming B v hs) := by
          simpa only [e, B.map.toCombinatorialMap.edgeInv_invol] using
            contour_forward_return_sameCycle B e he
        have hexit := contour_outgoing_exit B v hs ht
          (fun a _ ha => contour_outgoing_rotation B a ha) q hqv hq
        exact (hparent.trans hreturn).trans hexit.symm
  by_cases hd : B.map.tail d
  · exact hforward _ d rfl hd
  · have hi := contour_inverse_forward B d hd
    have h := (hforward _ _ rfl hi).trans
      (contour_forward_return_sameCycle B _ hi)
    simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h

private theorem contour_isCycleOn
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (contourPerm B).IsCycleOn (Finset.univ : Finset D) := by
  refine ⟨?_, ?_⟩
  · simpa only [Finset.coe_univ] using Set.bijOn_univ.mpr (contourPerm B).bijective
  · intro x _ y _
    exact (contour_sameCycle_start B x).symm.trans (contour_sameCycle_start B y)

/-- The forward darts in one full contour, in their first-visit order.
Helper toward thm-kmsw (inverse KMSW / Peano path); not the paper result -/
@[expose] noncomputable def firstVisitOrder
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : List D := by
  classical
  exact (List.ofFn fun i : Fin (Fintype.card D) =>
    (contourPerm B ^ i.val) (contourStart B)).filter (fun d => B.map.tail d)

/-- No edge is first visited twice. Helper toward thm-kmsw (inverse KMSW / -/
theorem firstVisitOrder_nodup
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : (firstVisitOrder B).Nodup := by
  classical
  apply List.Nodup.filter
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.ext
  apply (contour_isCycleOn B).injOn_pow_apply (Finset.mem_univ (contourStart B))
  · simpa only [Finset.card_univ, Set.mem_Iio] using i.isLt
  · simpa only [Finset.card_univ, Set.mem_Iio] using j.isLt
  · exact hij

/-- Membership in the order is exactly being a forward dart, so every
geometric edge occurs. Helper toward thm-kmsw (inverse KMSW / Peano path); -/
theorem mem_firstVisitOrder_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    d ∈ firstVisitOrder B ↔ B.map.tail d := by
  classical
  simp only [firstVisitOrder, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hd
    refine ⟨?_, hd⟩
    obtain ⟨n, hn, heq⟩ := (contour_isCycleOn B).exists_pow_eq
      (Finset.mem_univ (contourStart B)) (Finset.mem_univ d)
    rw [List.mem_ofFn']
    exact ⟨⟨n, by simpa only [Finset.card_univ] using hn⟩, heq⟩

private theorem contour_forward_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card {d : D // B.map.tail d} = B.map.toCombinatorialMap.numEdges := by
  classical
  let f : {d : D // B.map.tail d} →
      CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap :=
    fun d => Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.edgeInv) d.1
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have horbit : B.map.toCombinatorialMap.edgeInv.SameCycle a.1 b.1 := Quotient.exact hab
      rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap _ _).1
        horbit with h | h
      · exact Subtype.ext h.symm
      · exact False.elim ((B.map.tail_iff a.1 (B.noMissingDarts _)).1 a.2 (h ▸ b.2))
    · intro q
      induction q using Quotient.inductionOn with
      | h d =>
        by_cases hd : B.map.tail d
        · exact ⟨⟨d, hd⟩, rfl⟩
        · refine ⟨⟨B.map.toCombinatorialMap.edgeInv d, contour_inverse_forward B d hd⟩, ?_⟩
          apply Quotient.sound
          exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.edgeInv d).apply_left
  exact (Nat.card_congr (Equiv.ofBijective f hf)).trans Nat.card_eq_fintype_card

/-- The first-visit order has exactly as many entries as geometric edges.
Helper toward thm-kmsw (inverse KMSW / Peano path); not the paper result -/
theorem firstVisitOrder_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (firstVisitOrder B).length = B.map.toCombinatorialMap.numEdges := by
  classical
  have hset : (firstVisitOrder B).toFinset = Finset.univ.filter (fun d => B.map.tail d) := by
    ext d
    simp only [List.mem_toFinset, mem_firstVisitOrder_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
  calc
    (firstVisitOrder B).length = (firstVisitOrder B).toFinset.card :=
      (List.toFinset_card_of_nodup (firstVisitOrder_nodup B)).symm
    _ = Fintype.card {d : D // B.map.tail d} := by
      rw [hset, Fintype.card_subtype]
    _ = Nat.card {d : D // B.map.tail d} := Nat.card_eq_fintype_card.symm
    _ = B.map.toCombinatorialMap.numEdges := contour_forward_card B

/-- The source edge denoted `λ_{j+1}`, indexed from zero. Helper toward
thm-kmsw (inverse KMSW / Peano path); not the paper result -/
@[expose] noncomputable def peanoEdge
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (j : Fin B.map.toCombinatorialMap.numEdges) : D :=
  (firstVisitOrder B).get ⟨j.val, by rw [firstVisitOrder_length]; exact j.isLt⟩

/-- Every indexed first-visit edge is forward. Helper toward thm-kmsw
(inverse KMSW / Peano path); not the paper result -/
theorem peanoEdge_forward
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (j : Fin B.map.toCombinatorialMap.numEdges) : B.map.tail (peanoEdge B j) := by
  apply (mem_firstVisitOrder_iff B _).1
  exact List.get_mem _ _

/-- The positive edge count needed for the endpoint indices. Helper toward
thm-kmsw (inverse KMSW / Peano path); not the paper result -/
theorem contour_numEdges_pos
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    0 < B.map.toCombinatorialMap.numEdges := by
  have hmem : contourStart B ∈ firstVisitOrder B :=
    (mem_firstVisitOrder_iff B _).2
      (contour_rightmost_spec B B.source (bipolar_source_ne_sink B)).1
  have hpos : 0 < (firstVisitOrder B).length := List.length_pos_of_mem hmem
  simpa only [firstVisitOrder_length] using hpos

private theorem contour_order_cons
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ∃ xs, firstVisitOrder B = contourStart B :: xs := by
  classical
  have htail : B.map.tail (contourStart B) :=
    (contour_rightmost_spec B B.source (bipolar_source_ne_sink B)).1
  have hpos : 0 < Fintype.card D := Fintype.card_pos_iff.mpr ⟨contourStart B⟩
  have hcard : Fintype.card D = (Fintype.card D - 1) + 1 := by omega
  unfold firstVisitOrder
  rw [hcard, List.ofFn_succ]
  simp only [Fin.val_zero, pow_zero, Equiv.Perm.one_apply, List.filter_cons,
    decide_eq_true htail, ite_true]
  exact ⟨_, rfl⟩

/-- The first edge is the first right-boundary edge. Helper toward
thm-kmsw (inverse KMSW / Peano path); not the paper result -/
theorem peanoEdge_zero
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    peanoEdge B ⟨0, contour_numEdges_pos B⟩ =
      B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos) := by
  obtain ⟨xs, hxs⟩ := contour_order_cons B
  have hfirst : peanoEdge B ⟨0, contour_numEdges_pos B⟩ = contourStart B := by
    simp only [peanoEdge, List.get_eq_getElem, hxs, List.getElem_cons_zero]
  exact hfirst.trans (contourStart_eq_firstRightDart B)

private def contourLeftDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : Fin ℓ) : D :=
  B.leftPath.darts.get ⟨i.val, by rw [B.leftPath.darts_length]; exact i.isLt⟩

private theorem contour_left_forward
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : Fin ℓ) :
    B.map.tail (contourLeftDart B i) :=
  (B.leftPath.edge_step ⟨i.val, by rw [B.leftPath.darts_length]; exact i.isLt⟩).2.1

private theorem contour_left_face_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ) (hi : i + 1 < ℓ) :
    B.map.toCombinatorialMap.faceSucc (contourLeftDart B ⟨i, by omega⟩) =
      contourLeftDart B ⟨i + 1, hi⟩ := by
  classical
  let xs := B.leftPath.darts ++
    B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv
  have hnodup : xs.Nodup := by
    simpa only [xs, List.append_nil] using
      B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup
  have hlen : xs.length = ℓ + r := by
    simp only [xs, List.length_append, List.length_map, List.length_reverse,
      B.leftPath.darts_length, B.rightPath.darts_length]
  have hxi : i < xs.length := by rw [hlen]; omega
  have hxi' : i + 1 < xs.length := by rw [hlen]; omega
  have hcurrent : xs[i] = contourLeftDart B ⟨i, by omega⟩ := by
    rw [List.getElem_append_left (show i < B.leftPath.darts.length by
      rw [B.leftPath.darts_length]; omega)]
    rfl
  have hnext : xs[i + 1] = contourLeftDart B ⟨i + 1, hi⟩ := by
    rw [List.getElem_append_left (show i + 1 < B.leftPath.darts.length by
      rw [B.leftPath.darts_length]; exact hi)]
    rfl
  have hmem : xs[i] ∈ B.outerWord.letters :=
    B.outerSplit.2.1.perm.mem_iff.mpr (by
      simpa only [xs, List.append_nil] using List.getElem_mem hxi)
  have hperm : B.outerWord.letters.formPerm = xs.formPerm := by
    simpa only [xs, List.append_nil] using
      List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1
  have hface := B.outerSplit.1.2.2 xs[i] hmem
  rw [hperm] at hface
  have hsucc := List.formPerm_apply_getElem xs hnodup i hxi
  have hsucc' : xs.formPerm xs[i] = xs[i + 1] := by
    simpa only [Nat.mod_eq_of_lt hxi'] using hsucc
  rw [← hcurrent, hface, hsucc', hnext]

private theorem contour_left_reverse_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ) (hi : i + 1 < ℓ) :
    contourNext B (B.map.toCombinatorialMap.edgeInv (contourLeftDart B ⟨i + 1, hi⟩)) =
      B.map.toCombinatorialMap.edgeInv (contourLeftDart B ⟨i, by omega⟩) := by
  have hnot := (B.map.tail_iff _ (B.noMissingDarts _)).1
    (contour_left_forward B ⟨i + 1, hi⟩)
  simp only [contourNext, dite_eq_right hnot, B.map.toCombinatorialMap.edgeInv_invol]
  have h := contour_left_face_step B i hi
  rw [(corner_consecutiveDarts B _).1] at h
  exact (congrArg B.map.toCombinatorialMap.rot h).symm.trans
    (B.map.toCombinatorialMap.rot.apply_symm_apply _)

private theorem contour_inverse_left_boundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ) (hi : i < ℓ) :
    ((contourPerm B).symm ^ (i + 1)) (contourStart B) =
      B.map.toCombinatorialMap.edgeInv (contourLeftDart B ⟨i, hi⟩) := by
  induction i with
  | zero =>
    have hnot := (B.map.tail_iff _ (B.noMissingDarts _)).1
      (contour_left_forward B ⟨0, hi⟩)
    have hnext : contourNext B
        (B.map.toCombinatorialMap.edgeInv (contourLeftDart B ⟨0, hi⟩)) = contourStart B := by
      simp only [contourNext, dite_eq_right hnot, B.map.toCombinatorialMap.edgeInv_invol]
      exact (contour_source_rotation B).trans (contourStart_eq_firstRightDart B).symm
    exact (contourPerm B).symm_apply_eq.mpr hnext.symm
  | succ i ih =>
    have hprev := ih (by omega)
    have hnext := contour_left_reverse_step B i hi
    change contourPerm B _ = _ at hnext
    change ((contourPerm B).symm ^ (i + 1 + 1)) (contourStart B) = _
    rw [pow_succ', Equiv.Perm.mul_apply, hprev]
    exact (contourPerm B).symm_apply_eq.mpr hnext.symm

private theorem contour_last_left_head
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    dartHeadVertex B.map
      (contourLeftDart B ⟨ℓ - 1, by have := B.left_length_pos; omega⟩) = B.sink := by
  have hpos := B.left_length_pos
  have h := B.leftPath.edge_step ⟨ℓ - 1, by rw [B.leftPath.darts_length]; omega⟩
  have hidx : ℓ - 1 + 1 = ℓ := by omega
  have hv : B.leftPath.vertices.get ⟨ℓ - 1 + 1, by
      rw [B.leftPath.vertices_length]; omega⟩ = B.sink := by
    simpa only [hidx] using B.leftPath.end_vertex
  exact h.2.2.2.symm.trans hv

private theorem contour_inverse_last_left
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ((contourPerm B).symm ^ (ℓ + 1)) (contourStart B) =
      pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos) := by
  have hpos := B.left_length_pos
  let last := contourLeftDart B ⟨ℓ - 1, by omega⟩
  have hd : B.map.tail last := contour_left_forward B _
  have hdt : dartHeadVertex B.map last = B.sink := contour_last_left_head B
  have hnext : contourNext B last = B.map.toCombinatorialMap.edgeInv last := by
    simp only [contourNext, dite_eq_left hd, dite_eq_left hdt, ite_self]
  have hprev := contour_inverse_left_boundary B (ℓ - 1) (by omega)
  have hidx : ℓ - 1 + 1 = ℓ := by omega
  rw [hidx] at hprev
  rw [pow_succ', Equiv.Perm.mul_apply, hprev]
  exact (contourPerm B).symm_apply_eq.mpr hnext.symm

private theorem contour_card_gt_left
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : ℓ < Fintype.card D := by
  classical
  have hm : 0 < Fintype.card D := Fintype.card_pos_iff.mpr ⟨contourStart B⟩
  by_contra h
  have hi : Fintype.card D - 1 < ℓ := by omega
  have hrev := contour_inverse_left_boundary B (Fintype.card D - 1) hi
  have hidx : Fintype.card D - 1 + 1 = Fintype.card D := by omega
  rw [hidx] at hrev
  have hperiod := (contour_isCycleOn B).inv.pow_card_apply
    (Finset.mem_univ (contourStart B))
  simp only [Finset.card_univ] at hperiod
  change ((contourPerm B).symm ^ Fintype.card D) (contourStart B) = contourStart B at hperiod
  rw [hperiod] at hrev
  have hnot := (B.map.tail_iff _ (B.noMissingDarts _)).1 (contour_left_forward B ⟨_, hi⟩)
  exact hnot (hrev ▸ (contour_rightmost_spec B B.source (bipolar_source_ne_sink B)).1)

private theorem contour_reverse_orbit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (List.ofFn fun i : Fin (Fintype.card D) =>
      (contourPerm B ^ i.val) (contourStart B)).reverse =
    List.ofFn (fun i : Fin (Fintype.card D) =>
      ((contourPerm B).symm ^ (i.val + 1)) (contourStart B)) := by
  apply List.ext_getElem
  · simp only [List.length_reverse, List.length_ofFn]
  · intro i hi _
    have him : i < Fintype.card D := by
      simpa only [List.length_reverse, List.length_ofFn] using hi
    rw [List.getElem_reverse]
    simp only [List.length_ofFn, List.getElem_ofFn]
    have hperiod : contourPerm B ^ Fintype.card D = 1 := by
      ext d
      exact (contour_isCycleOn B).pow_card_apply (Finset.mem_univ d)
    have hsum : Fintype.card D - 1 - i + (i + 1) = Fintype.card D := by omega
    have hp : contourPerm B ^ (Fintype.card D - 1 - i) =
        (contourPerm B ^ (i + 1))⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← pow_add, hsum, hperiod]
    have hinv : (contourPerm B).symm ^ (i + 1) = (contourPerm B ^ (i + 1))⁻¹ :=
      inv_pow (contourPerm B) (i + 1)
    rw [hp, hinv]

private theorem contour_order_last
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (firstVisitOrder B).getLast? =
      some (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) := by
  classical
  rw [List.getLast?_eq_head?_reverse, firstVisitOrder, ← List.filter_reverse,
    contour_reverse_orbit, List.head?_filter]
  apply List.find?_ofFn_eq_some.mpr
  refine ⟨decide_eq_true (contour_left_forward B
    ⟨ℓ - 1, by have := B.left_length_pos; omega⟩),
    ⟨⟨ℓ, contour_card_gt_left B⟩, contour_inverse_last_left B, ?_⟩⟩
  intro j hj
  have hjl : j.val < ℓ := hj
  rw [contour_inverse_left_boundary B j.val hjl]
  intro h
  exact (B.map.tail_iff _ (B.noMissingDarts _)).1
    (contour_left_forward B ⟨j.val, hjl⟩) (of_decide_eq_true h)

/-- The final first-visit edge is the last left-boundary edge. Helper
toward thm-kmsw (inverse KMSW / Peano path); not the paper result -/
theorem peanoEdge_last
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    peanoEdge B ⟨B.map.toCombinatorialMap.numEdges - 1, by
      have := contour_numEdges_pos B; omega⟩ =
      pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos) := by
  have hne : firstVisitOrder B ≠ [] := by
    intro h
    have hp := contour_numEdges_pos B
    rw [← firstVisitOrder_length, h] at hp
    exact Nat.not_lt_zero _ hp
  have hlast := (List.getLast_eq_iff_getLast?_eq_some hne).2 (contour_order_last B)
  simpa only [peanoEdge, List.get_eq_getElem, List.getLast_eq_getElem,
    firstVisitOrder_length] using hlast

end DirectedDistances.PlanarMap
