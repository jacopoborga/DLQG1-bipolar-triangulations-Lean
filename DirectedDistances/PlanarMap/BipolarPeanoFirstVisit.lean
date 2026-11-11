module

public import DirectedDistances.PlanarMap.BipolarPeanoContour
public import DirectedDistances.PlanarMap.BipolarCanonicalTrees

/-! # First visits in the upper-left contour

Helpers toward the inverse direction of `thm-kmsw`; not the paper result -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

/-- One full orbit of the upper-left contour, starting from the source corner.
Helper toward the inverse direction of `thm-kmsw`; not the paper result -/
@[expose] noncomputable def contourOrbit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : List D :=
  List.ofFn fun i : Fin (Fintype.card D) =>
    (contourPerm B ^ i.val) (contourStart B)

private theorem contour_isCycleOn
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (contourPerm B).IsCycleOn (Finset.univ : Finset D) := by
  refine ⟨?_, ?_⟩
  · simpa only [Finset.coe_univ] using Set.bijOn_univ.mpr (contourPerm B).bijective
  · intro x _ y _
    exact (contour_sameCycle_start B x).symm.trans (contour_sameCycle_start B y)

/-- The contour orbit has no repeated darts. Helper toward the inverse
direction of `thm-kmsw`; not the paper result -/
theorem contourOrbit_nodup
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (contourOrbit B).Nodup := by
  classical
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.ext
  apply (contour_isCycleOn B).injOn_pow_apply (Finset.mem_univ (contourStart B))
  · simpa only [Finset.card_univ, Set.mem_Iio] using i.isLt
  · simpa only [Finset.card_univ, Set.mem_Iio] using j.isLt
  · exact hij

/-- The orbit contains one position for each dart. Helper toward the inverse
direction of `thm-kmsw`; not the paper result -/
theorem contourOrbit_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (contourOrbit B).length = Fintype.card D := by
  simp [contourOrbit]

/-- One contour step advances one position in the full cyclic orbit. Helper
toward the inverse direction of `thm-kmsw`; not the paper result -/
theorem contourOrbit_get_next
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (i : Fin (Fintype.card D)) :
    contourNext B
        ((contourOrbit B)[i.val]'(by
          rw [contourOrbit_length]
          exact i.isLt)) =
      (contourOrbit B)[(i.val + 1) % Fintype.card D]'
        (by
          rw [contourOrbit_length]
          exact Nat.mod_lt _ (Fintype.card_pos_iff.mpr ⟨contourStart B⟩)) := by
  classical
  simp only [contourOrbit, List.getElem_ofFn]
  change ((contourPerm B) * (contourPerm B ^ i.val)) (contourStart B) = _
  by_cases hlt : i.val + 1 < Fintype.card D
  · have hmod : (i.val + 1) % Fintype.card D = i.val + 1 :=
      Nat.mod_eq_of_lt hlt
    rw [hmod]
    rw [← pow_succ']
  · have hi : i.val + 1 = Fintype.card D := by
      omega
    have hmod : (i.val + 1) % Fintype.card D = 0 := by
      rw [hi, Nat.mod_self]
    rw [hmod, ← pow_succ', hi]
    have hperiod := (contour_isCycleOn B).pow_card_apply
      (Finset.mem_univ (contourStart B))
    simpa only [Finset.card_univ, pow_zero, Equiv.Perm.one_apply] using hperiod

/-- Every dart occurs in one full contour orbit. Helper toward the inverse
direction of `thm-kmsw`; not the paper result -/
theorem mem_contourOrbit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    d ∈ contourOrbit B := by
  classical
  unfold contourOrbit
  rw [List.mem_ofFn']
  obtain ⟨n, hn, heq⟩ := (contour_isCycleOn B).exists_pow_eq
    (Finset.mem_univ (contourStart B)) (Finset.mem_univ d)
  exact ⟨⟨n, by simpa only [Finset.card_univ] using hn⟩, heq⟩

/-- The zero-based position of a dart in the contour orbit. Helper toward the
inverse direction of `thm-kmsw`; not the paper result -/
@[expose] noncomputable def contourPosition
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    Fin (contourOrbit B).length :=
  ⟨(contourOrbit B).idxOf d,
    List.idxOf_lt_length_iff.mpr (mem_contourOrbit B d)⟩

/-- Reading the contour orbit at a dart's position returns that dart. Helper
toward the inverse direction of `thm-kmsw`; not the paper result -/
theorem contourOrbit_get_contourPosition
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    (contourOrbit B).get (contourPosition B d) = d := by
  exact List.idxOf_get (contourPosition B d).isLt

/-- The position of a contour successor is the next cyclic position. Helper
toward the inverse direction of `thm-kmsw`; not the paper result -/
theorem contourPosition_next
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    (contourPosition B (contourNext B d)).val =
      ((contourPosition B d).val + 1) % (contourOrbit B).length := by
  classical
  let p := contourPosition B d
  let i : Fin (Fintype.card D) :=
    ⟨p.val, by rw [← contourOrbit_length]; exact p.isLt⟩
  have hget : (contourOrbit B)[p.val]'p.isLt = d := by
    simpa only [List.get_eq_getElem] using contourOrbit_get_contourPosition B d
  have hstep := contourOrbit_get_next B i
  change contourNext B ((contourOrbit B)[p.val]'p.isLt) = _ at hstep
  have hstep' : contourNext B d =
      (contourOrbit B)[(i.val + 1) % Fintype.card D]'
        (by rw [contourOrbit_length]
            exact Nat.mod_lt _ (Fintype.card_pos_iff.mpr ⟨contourStart B⟩)) := by
    simpa only [hget] using hstep
  let q : Fin (contourOrbit B).length :=
    ⟨(i.val + 1) % Fintype.card D, by
      rw [contourOrbit_length]
      exact Nat.mod_lt _ (Fintype.card_pos_iff.mpr ⟨contourStart B⟩)⟩
  have hidx := List.get_idxOf (contourOrbit_nodup B) q
  change (contourOrbit B).idxOf (contourNext B d) =
      ((contourPosition B d).val + 1) % (contourOrbit B).length
  rw [hstep']
  simpa only [List.get_eq_getElem, q, i, p, contourOrbit_length] using hidx

/-- The initial contour position is the source corner. Helper toward the
inverse direction of `thm-kmsw`; not the paper result -/
theorem contourOrbit_get_zero
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (contourOrbit B).get
      ⟨0, by
        rw [contourOrbit_length]
        exact Fintype.card_pos_iff.mpr ⟨contourStart B⟩⟩ = contourStart B := by
  simp [contourOrbit]

/-- A dart at contour position zero is the starting corner. Helper toward the
inverse direction of `thm-kmsw`; not the paper result -/
theorem contourPosition_zero_eq_start
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hzero : (contourPosition B d).val = 0) :
    d = contourStart B := by
  have hpos : contourPosition B d =
      ⟨0, by
        rw [contourOrbit_length]
        exact Fintype.card_pos_iff.mpr ⟨contourStart B⟩⟩ := Fin.ext hzero
  calc
    d = (contourOrbit B).get (contourPosition B d) :=
      (contourOrbit_get_contourPosition B d).symm
    _ = (contourOrbit B).get
          ⟨0, by
            rw [contourOrbit_length]
            exact Fintype.card_pos_iff.mpr ⟨contourStart B⟩⟩ :=
      congrArg (fun i => (contourOrbit B).get i) hpos
    _ = contourStart B := contourOrbit_get_zero B

/-- A contour step that does not wrap to the starting corner advances its
numeric position. Helper toward the inverse direction of `thm-kmsw`; not the -/
theorem contourPosition_step_lt_of_next_ne_start
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hnext : contourNext B d ≠ contourStart B) :
    (contourPosition B d).val + 1 < (contourOrbit B).length := by
  by_contra hlt
  have heq : (contourPosition B d).val + 1 = (contourOrbit B).length := by
    have hpos := (contourPosition B d).isLt
    omega
  have hzero : (contourPosition B (contourNext B d)).val = 0 := by
    rw [contourPosition_next, heq, Nat.mod_self]
  exact hnext (contourPosition_zero_eq_start B _ hzero)

/-- The initial contour dart is forward and based at the source. Helper
toward the inverse direction of `thm-kmsw`; not the paper result -/
theorem contourStart_tail_at_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.map.tail (contourStart B) ∧
      dartTailVertex B.map (contourStart B) = B.source := by
  rw [contourStart_eq_firstRightDart]
  have hstep := B.rightPath.edge_step
    ⟨0, by rw [B.rightPath.darts_length]; exact Nat.zero_lt_of_lt B.right_length_pos⟩
  exact ⟨hstep.2.1,
    (hstep.2.2.1).symm.trans B.rightPath.start_vertex⟩

private theorem contour_rot_sameVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot d) =
      dartTailVertex B.map d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.rot d).apply_left

private theorem contour_rot_pow_sameVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) (n : ℕ) :
    dartTailVertex B.map
        ((B.map.toCombinatorialMap.rot ^ n) d) = dartTailVertex B.map d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact (contour_rot_sameVertex B _).trans ih

/-- If the contour immediately reverses a forward dart, its forward visit
precedes its reverse. Helper toward the inverse direction of `thm-kmsw`; not -/
theorem contourPosition_forward_immediate_return
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hd : B.map.tail d)
    (hnext : contourNext B d = B.map.toCombinatorialMap.edgeInv d) :
    (contourPosition B d).val <
      (contourPosition B (B.map.toCombinatorialMap.edgeInv d)).val := by
  have hposNext : (contourPosition B (B.map.toCombinatorialMap.edgeInv d)).val =
      ((contourPosition B d).val + 1) % (contourOrbit B).length := by
    rw [← hnext]
    exact contourPosition_next B d
  have hlt : (contourPosition B d).val + 1 < (contourOrbit B).length := by
    by_contra h
    have heq : (contourPosition B d).val + 1 = (contourOrbit B).length := by
      have hpos := (contourPosition B d).isLt
      omega
    have hposInv : (contourPosition B (B.map.toCombinatorialMap.edgeInv d)).val = 0 := by
      rw [hposNext, heq, Nat.mod_self]
    have hzero : contourPosition B (B.map.toCombinatorialMap.edgeInv d) =
        ⟨0, by
          rw [contourOrbit_length]
          exact Fintype.card_pos_iff.mpr ⟨contourStart B⟩⟩ := Fin.ext hposInv
    have hEdgeInvStart : B.map.toCombinatorialMap.edgeInv d = contourStart B := by
      calc
        B.map.toCombinatorialMap.edgeInv d =
            (contourOrbit B).get
              (contourPosition B (B.map.toCombinatorialMap.edgeInv d)) :=
          (contourOrbit_get_contourPosition B _).symm
        _ = (contourOrbit B).get
              ⟨0, by
                rw [contourOrbit_length]
                exact Fintype.card_pos_iff.mpr ⟨contourStart B⟩⟩ :=
          congrArg (fun i => (contourOrbit B).get i) hzero
        _ = contourStart B := contourOrbit_get_zero B
    have hdInvNot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv d) :=
      (B.map.tail_iff d (B.noMissingDarts d)).1 hd
    have hstartTail : B.map.tail (contourStart B) := by
      rw [contourStart_eq_firstRightDart]
      have hstep := B.rightPath.edge_step
        ⟨0, by rw [B.rightPath.darts_length]; exact Nat.zero_lt_of_lt B.right_length_pos⟩
      exact hstep.2.1
    exact hdInvNot (hEdgeInvStart.symm ▸ hstartTail)
  rw [hposNext, Nat.mod_eq_of_lt hlt]
  omega

private theorem contour_outgoing_rotation_position
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvSource : v ≠ B.source)
    (hchild : ∀ w, B.map.directedStep v w → ∀ d,
      dartHeadVertex B.map d = w → B.map.tail d →
        (contourPosition B d).val <
          (contourPosition B (B.map.toCombinatorialMap.edgeInv d)).val)
    (q : D) (hq : B.map.tail q) (hqv : dartTailVertex B.map q = v) :
    (contourPosition B q).val <
      (contourPosition B (B.map.toCombinatorialMap.rot q)).val := by
  let w := dartHeadVertex B.map q
  have hwSource : w ≠ B.source := contour_forward_head_ne_source B q hq
  have hreturn : (contourPosition B q).val <
      (contourPosition B (B.map.toCombinatorialMap.edgeInv q)).val := by
    by_cases hwSink : w = B.sink
    · apply contourPosition_forward_immediate_return B q hq
      unfold contourNext
      rw [dite_eq_left hq]
      change dartHeadVertex B.map q = B.sink at hwSink
      simp [hwSink]
    · have htW : w ≠ B.sink := hwSink
      by_cases hselected : B.map.toCombinatorialMap.edgeInv q =
          leftmostIncoming B w hwSource
      · have hstep : B.map.directedStep v w :=
          ⟨q, B.noMissingDarts q, hq, hqv, rfl⟩
        exact hchild w hstep q rfl hq
      · apply contourPosition_forward_immediate_return B q hq
        unfold contourNext
        rw [dite_eq_left hq]
        change ¬ B.map.toCombinatorialMap.edgeInv q =
          leftmostIncoming B (dartHeadVertex B.map q)
            (contour_forward_head_ne_source B q hq) at hselected
        simp [hselected]
  have hbackNext : contourNext B (B.map.toCombinatorialMap.edgeInv q) =
      B.map.toCombinatorialMap.rot q := by
    have hnot := (B.map.tail_iff q (B.noMissingDarts q)).1 hq
    simp [contourNext, hnot, B.map.toCombinatorialMap.edgeInv_invol]
  have hrotNeStart : B.map.toCombinatorialMap.rot q ≠ contourStart B := by
    intro heq
    have hv := congrArg (dartTailVertex B.map) heq
    rw [contour_rot_sameVertex B q, hqv,
      (contourStart_tail_at_source B).2] at hv
    exact hvSource hv
  have hnextLt := contourPosition_step_lt_of_next_ne_start B
    (B.map.toCombinatorialMap.edgeInv q) (by rw [hbackNext]; exact hrotNeStart)
  have hposRot : (contourPosition B (B.map.toCombinatorialMap.rot q)).val =
      (contourPosition B (B.map.toCombinatorialMap.edgeInv q)).val + 1 := by
    rw [← hbackNext, contourPosition_next]
    exact Nat.mod_eq_of_lt hnextLt
  rw [hposRot]
  omega

/-- Every forward dart occurs before its reverse in the upper-left contour.
Helper toward thm-kmsw's inverse direction; not the paper result -/
theorem firstVisitOrder_forward_first
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hd : B.map.tail d) :
    (contourPosition B d).val <
      (contourPosition B (B.map.toCombinatorialMap.edgeInv d)).val := by
  classical
  suffices h : ∀ v (d : D), dartHeadVertex B.map d = v → B.map.tail d →
      (contourPosition B d).val <
        (contourPosition B (B.map.toCombinatorialMap.edgeInv d)).val from
    h _ d rfl hd
  intro v
  induction v using (reverseDirectedReach_wellFounded B).induction with
  | h v ih =>
    intro d hdv hd
    have hs : v ≠ B.source := hdv ▸ contour_forward_head_ne_source B d hd
    by_cases hsel : B.map.toCombinatorialMap.edgeInv d = leftmostIncoming B v hs
    · by_cases ht : v = B.sink
      · have hnext : contourNext B d = B.map.toCombinatorialMap.edgeInv d := by
          simp only [contourNext, dite_eq_left hd, hdv, dite_eq_left ht, ite_self]
        exact contourPosition_forward_immediate_return B d hd hnext
      · have hnext : contourNext B d = rightmostOutgoing B v ht := by
          simp only [contourNext, dite_eq_left hd, hdv, ite_eq_left hsel,
            dite_eq_right ht]
        have hchild : ∀ w, B.map.directedStep v w → ∀ q,
            dartHeadVertex B.map q = w → B.map.tail q →
              (contourPosition B q).val <
                (contourPosition B (B.map.toCombinatorialMap.edgeInv q)).val := by
          intro w hstep q hqv hq
          exact ih w (Relation.TransGen.single hstep) q hqv hq
        have hlocal : ∀ q, dartTailVertex B.map q = v → B.map.tail q →
            (contourPosition B q).val <
              (contourPosition B (B.map.toCombinatorialMap.rot q)).val := by
          intro q hqv hq
          exact contour_outgoing_rotation_position B v hs hchild q hq hqv
        have hli := leftmostIncoming_internal_characterization B v hs ht
        have hright : B.map.tail (rightmostOutgoing B v ht) ∧
            dartTailVertex B.map (rightmostOutgoing B v ht) = v := by
          obtain ⟨hbase, htail, _, _⟩ :=
            rightmostOutgoing_internal_characterization B v hs ht
          exact ⟨htail, hbase⟩
        have hrot : B.map.toCombinatorialMap.rot.SameCycle
            (rightmostOutgoing B v ht)
            (leftmostIncoming B v hs) :=
          Quotient.exact (hright.2.trans hli.1.symm)
        obtain ⟨n, hn⟩ := hrot.exists_nat_pow_eq
        have hsegment : ∀ n q, dartTailVertex B.map q = v → B.map.tail q →
            (B.map.toCombinatorialMap.rot ^ n) q = leftmostIncoming B v hs →
              (contourPosition B q).val <
                (contourPosition B (leftmostIncoming B v hs)).val := by
          intro n
          induction n with
          | zero =>
              intro q _ hq heq
              have : q = leftmostIncoming B v hs := heq
              exact False.elim (hli.2.1 (this ▸ hq))
          | succ n ihseg =>
              intro q hqv hq heq
              have hstep := hlocal q hqv hq
              have hnextv := (contour_rot_sameVertex B q).trans hqv
              by_cases hnext : B.map.tail (B.map.toCombinatorialMap.rot q)
              · have hend : (B.map.toCombinatorialMap.rot ^ n)
                    (B.map.toCombinatorialMap.rot q) = leftmostIncoming B v hs := by
                  simpa only [pow_succ, Equiv.Perm.mul_apply] using heq
                exact hstep.trans (ihseg _ hnextv hnext hend)
              · have hreturn : B.map.toCombinatorialMap.rot q =
                    leftmostIncoming B v hs :=
                  hli.2.2.2 _ hnextv hnext (by simpa using hq)
                rw [hreturn] at hstep
                exact hstep
        have hposition := hsegment n (rightmostOutgoing B v ht)
          hright.2 hright.1 hn
        have hnextNeStart : contourNext B d ≠ contourStart B := by
          intro heq
          have hv : v = B.source := by
            calc
              v = dartTailVertex B.map (rightmostOutgoing B v ht) := hright.2.symm
              _ = dartTailVertex B.map (contourStart B) :=
                congrArg (dartTailVertex B.map) (hnext.symm.trans heq)
              _ = B.source := (contourStart_tail_at_source B).2
          exact hs hv
        have hstepPos := contourPosition_step_lt_of_next_ne_start B d hnextNeStart
        have hrightPos : (contourPosition B (rightmostOutgoing B v ht)).val =
            (contourPosition B d).val + 1 := by
          rw [← hnext, contourPosition_next]
          exact Nat.mod_eq_of_lt hstepPos
        rw [← hsel] at hposition
        omega
    · have hnext : contourNext B d = B.map.toCombinatorialMap.edgeInv d := by
        simp only [contourNext, dite_eq_left hd, hdv, ite_eq_right hsel]
      exact contourPosition_forward_immediate_return B d hd hnext

/-- Indexed Peano edges occur in increasing order of their first contour
visits. Helper toward thm-kmsw's inverse direction; not the paper result -/
theorem peanoEdge_increasing_firstVisit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (j k : Fin B.map.toCombinatorialMap.numEdges) (hjk : j.val < k.val) :
    (contourPosition B (peanoEdge B j)).val <
      (contourPosition B (peanoEdge B k)).val := by
  classical
  let R : D → D → Prop := fun d e =>
    (contourPosition B d).val < (contourPosition B e).val
  have horbit : (contourOrbit B).Pairwise R := by
    rw [List.pairwise_iff_getElem]
    intro i k hi hk hik
    have hpi : (contourPosition B ((contourOrbit B)[i]'hi)).val = i := by
      change (contourOrbit B).idxOf ((contourOrbit B)[i]'hi) = i
      exact List.get_idxOf (contourOrbit_nodup B)
        ⟨i, by simpa only [contourOrbit_length] using hi⟩
    have hpk : (contourPosition B ((contourOrbit B)[k]'hk)).val = k := by
      change (contourOrbit B).idxOf ((contourOrbit B)[k]'hk) = k
      exact List.get_idxOf (contourOrbit_nodup B)
        ⟨k, by simpa only [contourOrbit_length] using hk⟩
    change (contourPosition B ((contourOrbit B)[i]'hi)).val <
      (contourPosition B ((contourOrbit B)[k]'hk)).val
    rw [hpi, hpk]
    exact hik
  have hfiltered : (firstVisitOrder B).Pairwise R := by
    unfold firstVisitOrder
    exact List.Pairwise.filter (fun d => B.map.tail d) horbit
  have hj' : j.val < (firstVisitOrder B).length := by
    rw [firstVisitOrder_length]
    exact j.isLt
  have hk' : k.val < (firstVisitOrder B).length := by
    rw [firstVisitOrder_length]
    exact k.isLt
  have h := hfiltered.rel_getElem_of_lt hj' hk' hjk
  simpa only [R, peanoEdge, List.get_eq_getElem] using h
end DirectedDistances.PlanarMap
