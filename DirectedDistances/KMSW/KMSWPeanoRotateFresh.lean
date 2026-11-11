module

public import DirectedDistances.KMSW.KMSWPeanoPrefixRotate
public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantSteps
public import DirectedDistances.PlanarMap.BipolarPeanoFirstVisit
public import DirectedDistances.PlanarMap.BipolarPeanoContour
public import DirectedDistances.PlanarMap.BipolarPeanoConfiguration




public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

/-- Rotation preserves the tail vertex of a dart. -/
theorem fresh_rot_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot d) = dartTailVertex B.map d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.rot d).apply_left

private theorem fresh_face_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d) = dartHeadVertex B.map d := by
  apply Quotient.sound
  exact ⟨1, by simp [CombinatorialMap.faceSucc]⟩

private theorem fresh_inverse_forward
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hd : ¬ B.map.tail d) : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
  by_contra h
  exact hd ((B.map.tail_iff d (B.noMissingDarts d)).2 h)

private theorem fresh_reverse_next
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) (hd : B.map.tail d) :
    contourNext B (B.map.toCombinatorialMap.edgeInv d) = B.map.toCombinatorialMap.rot d := by
  simp only [contourNext, dite_eq_right ((B.map.tail_iff d (B.noMissingDarts d)).1 hd),
    B.map.toCombinatorialMap.edgeInv_invol]

private theorem fresh_position_next
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hnext : contourNext B d ≠ contourStart B) :
    (contourPosition B d).val < (contourPosition B (contourNext B d)).val := by
  rw [contourPosition_next,
    Nat.mod_eq_of_lt (contourPosition_step_lt_of_next_ne_start B d hnext)]
  omega

private theorem fresh_inner_rot_ne_start
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hi : ¬ B.map.IsOuter d) : B.map.toCombinatorialMap.rot d ≠ contourStart B := by
  intro he
  have hcorner := contour_source_rotation B
  rw [← contourStart_eq_firstRightDart B, ← he] at hcorner
  have hd := B.map.toCombinatorialMap.rot.injective hcorner
  have hm : B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) ∈ B.leftPath.darts :=
    List.get_mem _ _
  exact hi (hd ▸ ((B.outerSplit.2.2.1 _).mp hm).2.2)

private theorem fresh_outer_forward_selected
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (a : D)
    (ha : B.map.tail a) (ho : B.map.IsOuter a) :
    B.map.toCombinatorialMap.edgeInv a = leftmostIncoming B
      (dartHeadVertex B.map a) (contour_forward_head_ne_source B a ha) := by
  classical
  have hmem : a ∈ B.leftPath.darts := (B.outerSplit.2.2.1 a).mpr
    ⟨B.noMissingDarts a, ha, ho⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hmem
  let a := B.leftPath.darts.get i
  change B.map.tail a at ha
  have hi : i.val < ℓ := by simpa only [B.leftPath.darts_length] using i.isLt
  have hhead := (B.leftPath.edge_step i).2.2.2
  have hs := contour_forward_head_ne_source B a ha
  have hp := canonicalULSelector_leftPath_edge B (i.val + 1) (by omega) (by omega)
  rw [canonicalULSelector_val] at hp
  have hp' : B.map.toCombinatorialMap.edgeInv
      (leftmostIncoming B (dartHeadVertex B.map a) hs) = a := by
    simpa only [a, hhead, Nat.add_sub_cancel, List.get_eq_getElem] using hp
  have h := congrArg B.map.toCombinatorialMap.edgeInv hp'
  simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h.symm

private theorem fresh_incoming_corner_inner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d e : D)
    (hd : B.map.tail d) (he : B.map.tail e)
    (ht : dartHeadVertex B.map d ≠ B.sink)
    (hc : B.map.toCombinatorialMap.faceSucc d = B.map.toCombinatorialMap.edgeInv e) :
    ¬ B.map.IsOuter d := by
  intro ho
  have hs := contour_forward_head_ne_source B d hd
  have hsel := fresh_outer_forward_selected B d hd ho
  have hf := (leftmostIncoming_internal_characterization B _ hs ht).2.2.1
  rw [← hsel] at hf
  change B.map.tail (B.map.toCombinatorialMap.faceSucc d) at hf
  rw [hc] at hf
  exact (B.map.tail_iff e (B.noMissingDarts e)).1 he hf

private theorem fresh_inner_face_next_inner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hi : ¬ B.map.IsOuter d) : ¬ B.map.IsOuter (B.map.toCombinatorialMap.faceSucc d) := by
  intro ho
  exact hi (ho.trans (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.faceSucc d).apply_left)

private theorem fresh_outgoing_rotation_lt
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (hs : v ≠ B.source) (d : D) (hd : B.map.tail d)
    (hv : dartTailVertex B.map d = v) :
    (contourPosition B d).val <
      (contourPosition B (B.map.toCombinatorialMap.rot d)).val := by
  have hn : contourNext B (B.map.toCombinatorialMap.edgeInv d) ≠ contourStart B := by
    rw [fresh_reverse_next B d hd]
    intro he
    exact hs (hv.symm.trans ((fresh_rot_vertex B d).symm.trans
      ((congrArg (dartTailVertex B.map) he).trans (contourStart_tail_at_source B).2)))
  have h := fresh_position_next B _ hn
  rw [fresh_reverse_next B d hd] at h
  exact (firstVisitOrder_forward_first B d hd).trans h

private theorem fresh_outgoing_min
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (hs : v ≠ B.source) (ht : v ≠ B.sink) (e : D)
    (he : B.map.tail e) (hev : dartTailVertex B.map e = v) :
    (contourPosition B (rightmostOutgoing B v ht)).val ≤ (contourPosition B e).val := by
  let ρ : Equiv.Perm D := B.map.toCombinatorialMap.rot
  have hr := rightmostOutgoing_internal_characterization B v hs ht
  have hcycle : Equiv.Perm.SameCycle (ρ⁻¹) e (rightmostOutgoing B v ht) :=
    Equiv.Perm.sameCycle_inv.mpr (Quotient.exact (hev.trans hr.1.symm))
  obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
  suffices h : ∀ n q, B.map.tail q → dartTailVertex B.map q = v →
      (ρ.symm ^ n) q = rightmostOutgoing B v ht →
      (contourPosition B (rightmostOutgoing B v ht)).val ≤ (contourPosition B q).val from
    h n e he hev hn
  intro n
  induction n with
  | zero =>
      intro q _ _ hq
      have hq' : q = rightmostOutgoing B v ht := hq
      rw [hq']
  | succ n ih =>
      intro q hq hqv hn
      by_cases hp : B.map.tail (ρ.symm q)
      · have hpv : dartTailVertex B.map (ρ.symm q) = v := by
          have h := fresh_rot_vertex B (ρ.symm q)
          simp only [ρ, Equiv.apply_symm_apply] at h
          exact h.symm.trans hqv
        have hend : (ρ.symm ^ n) (ρ.symm q) = rightmostOutgoing B v ht := by
          simpa only [pow_succ, Equiv.Perm.mul_apply] using hn
        have hlt := fresh_outgoing_rotation_lt B v hs (ρ.symm q) hp hpv
        simp only [ρ, Equiv.apply_symm_apply] at hlt
        exact (ih _ hp hpv hend).trans hlt.le
      · have heq := hr.2.2.2 q hqv hq hp
        rw [heq]

private theorem fresh_incoming_adjacent
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (ht : v ≠ B.sink)
    (hpre : ∀ u, B.map.directedStep u v → ∀ d e : D,
      B.map.tail d → B.map.tail e → dartHeadVertex B.map d = u →
      dartTailVertex B.map e = u →
      (contourPosition B d).val < (contourPosition B e).val)
    (d e : D) (hd : B.map.tail d) (he : B.map.tail e)
    (hdv : dartHeadVertex B.map d = v) (hev : dartHeadVertex B.map e = v)
    (hc : B.map.toCombinatorialMap.faceSucc d = B.map.toCombinatorialMap.edgeInv e) :
    (contourPosition B d).val < (contourPosition B e).val := by
  let ρ : Equiv.Perm D := B.map.toCombinatorialMap.rot
  let τ : Equiv.Perm D := B.map.toCombinatorialMap.edgeInv
  let x := B.map.toCombinatorialMap.faceSucc (τ e)
  have hi := fresh_incoming_corner_inner B d e hd he (hdv ▸ ht) hc
  have htri := (B.innerFacesDegreeThree d hi).1
  have hxd : B.map.toCombinatorialMap.faceSucc x = d := by
    simpa only [hc, x, τ] using htri
  have hdx : ρ d = τ x := by
    change ρ.symm (τ x) = d at hxd
    exact ρ.eq_symm_apply.mp hxd.symm
  have hxe : ρ x = e := by
    change ρ (ρ.symm (τ (τ e))) = e
    rw [Equiv.apply_symm_apply, B.map.toCombinatorialMap.edgeInv_invol]
  have hix : ¬ B.map.IsOuter x := by
    have h := fresh_inner_face_next_inner B _ (fresh_inner_face_next_inner B d hi)
    simpa only [hc, x, τ] using h
  have hstep : (contourPosition B (τ d)).val < (contourPosition B (τ x)).val := by
    have hn : contourNext B (τ d) ≠ contourStart B := by
      rw [fresh_reverse_next B d hd]
      exact fresh_inner_rot_ne_start B d hi
    have h := fresh_position_next B _ hn
    simpa only [fresh_reverse_next B d hd, hdx, τ, ρ] using h
  by_cases hx : B.map.tail x
  · have hn : contourNext B (τ x) ≠ contourStart B := by
      rw [fresh_reverse_next B x hx]
      exact fresh_inner_rot_ne_start B x hix
    have h := fresh_position_next B _ hn
    rw [fresh_reverse_next B x hx] at h
    change (contourPosition B (τ x)).val < (contourPosition B (ρ x)).val at h
    rw [hxe] at h
    exact (firstVisitOrder_forward_first B d hd).trans (hstep.trans h)
  · have hq := fresh_inverse_forward B x hx
    have hhead : dartHeadVertex B.map (τ x) = dartTailVertex B.map e := by
      simpa only [dartHeadVertex, dartTailVertex,
        B.map.toCombinatorialMap.edgeInv_invol, τ] using
        (fresh_rot_vertex B x).symm.trans (congrArg (dartTailVertex B.map) hxe)
    have hpred : B.map.directedStep (dartTailVertex B.map e) v :=
      ⟨e, B.noMissingDarts e, he, rfl, hev⟩
    exact (firstVisitOrder_forward_first B d hd).trans
      (hstep.trans (hpre _ hpred (τ x) e hq he hhead rfl))

private theorem fresh_incoming_max
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (hcorner : ∀ d e : D, B.map.tail d → B.map.tail e →
      dartHeadVertex B.map d = v → dartHeadVertex B.map e = v →
      B.map.toCombinatorialMap.faceSucc d = B.map.toCombinatorialMap.edgeInv e →
      (contourPosition B d).val < (contourPosition B e).val)
    (d : D) (hd : B.map.tail d) (hdv : dartHeadVertex B.map d = v) :
    (contourPosition B d).val ≤ (contourPosition B
      (B.map.toCombinatorialMap.edgeInv (leftmostIncoming B v hs))).val := by
  let ρ : Equiv.Perm D := B.map.toCombinatorialMap.rot
  let τ : Equiv.Perm D := B.map.toCombinatorialMap.edgeInv
  have hli := leftmostIncoming_internal_characterization B v hs ht
  have hcycle : Equiv.Perm.SameCycle (ρ⁻¹) (τ d) (leftmostIncoming B v hs) :=
    Equiv.Perm.sameCycle_inv.mpr (Quotient.exact (hdv.trans hli.1.symm))
  obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
  have hrec : ∀ n q, ¬ B.map.tail q → dartTailVertex B.map q = v →
      (ρ.symm ^ n) q = leftmostIncoming B v hs →
      (contourPosition B (τ q)).val ≤
        (contourPosition B (τ (leftmostIncoming B v hs))).val := by
    intro n
    induction n with
    | zero =>
        intro q _ _ hq
        have hq' : q = leftmostIncoming B v hs := hq
        rw [hq']
    | succ n ih =>
        intro q hq hqv hn
        have hpv : dartTailVertex B.map (ρ.symm q) = v := by
          have h := fresh_rot_vertex B (ρ.symm q)
          simp only [ρ, Equiv.apply_symm_apply] at h
          exact h.symm.trans hqv
        by_cases hp : B.map.tail (ρ.symm q)
        · have heq := hli.2.2.2 q hqv hq hp
          rw [heq]
        · have hend : (ρ.symm ^ n) (ρ.symm q) = leftmostIncoming B v hs := by
            simpa only [pow_succ, Equiv.Perm.mul_apply] using hn
          have hqhead : dartHeadVertex B.map (τ q) = v := by
            simpa only [dartHeadVertex, dartTailVertex, τ,
              B.map.toCombinatorialMap.edgeInv_invol] using hqv
          have hphead : dartHeadVertex B.map (τ (ρ.symm q)) = v := by
            simpa only [dartHeadVertex, dartTailVertex, τ,
              B.map.toCombinatorialMap.edgeInv_invol] using hpv
          have hc : B.map.toCombinatorialMap.faceSucc (τ q) = τ (τ (ρ.symm q)) := by
            change ρ.symm (τ (τ q)) = τ (τ (ρ.symm q))
            simp only [τ, B.map.toCombinatorialMap.edgeInv_invol]
          exact (hcorner (τ q) (τ (ρ.symm q)) (fresh_inverse_forward B q hq)
            (fresh_inverse_forward B _ hp) hqhead hphead hc).le.trans
              (ih _ hp hpv hend)
  have h := hrec n (τ d) ((B.map.tail_iff d (B.noMissingDarts d)).1 hd) hdv hn
  simpa only [τ, B.map.toCombinatorialMap.edgeInv_invol] using h

/-- Every forward incoming dart precedes every forward outgoing dart at the
same vertex in the contour order. -/
theorem fresh_incoming_before_outgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (d e : D) (hd : B.map.tail d) (he : B.map.tail e)
    (hdv : dartHeadVertex B.map d = v) (hev : dartTailVertex B.map e = v) :
    (contourPosition B d).val < (contourPosition B e).val := by
  revert d e
  induction v using (directedReach_wellFounded B).induction with
  | h v ih =>
      intro d e hd he hdv hev
      have hs : v ≠ B.source := hdv ▸ contour_forward_head_ne_source B d hd
      have ht : v ≠ B.sink := by
        intro hv
        exact B.isSink ⟨dartHeadVertex B.map e, e, B.noMissingDarts e, he,
          hev.trans hv, rfl⟩
      have hcorner := fresh_incoming_adjacent B v ht
        (fun u hu => ih u (Relation.TransGen.single hu))
      have hmax := fresh_incoming_max B v hs ht hcorner d hd hdv
      have hmin := fresh_outgoing_min B v hs ht e he hev
      let p := B.map.toCombinatorialMap.edgeInv (leftmostIncoming B v hs)
      have hli := leftmostIncoming_internal_characterization B v hs ht
      have hr := rightmostOutgoing_internal_characterization B v hs ht
      have hp : B.map.tail p := fresh_inverse_forward B _ hli.2.1
      have hpv : dartHeadVertex B.map p = v := by
        simpa only [p, dartHeadVertex, dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol] using hli.1
      have hsel : B.map.toCombinatorialMap.edgeInv p = leftmostIncoming B v hs :=
        B.map.toCombinatorialMap.edgeInv_invol _
      have hpt : dartHeadVertex B.map p ≠ B.sink := hpv ▸ ht
      have hn : contourNext B p = rightmostOutgoing B v ht := by
        simp only [contourNext, dite_eq_left hp, dite_eq_right hpt, hpv, hsel, ite_true]
      have hnstart : contourNext B p ≠ contourStart B := by
        rw [hn]
        intro h
        exact hs (hr.1.symm.trans
          ((congrArg (dartTailVertex B.map) h).trans (contourStart_tail_at_source B).2))
      have hmid := fresh_position_next B p hnstart
      rw [hn] at hmid
      exact hmax.trans_lt (hmid.trans_le hmin)

private theorem fresh_incoming_min
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (d : D) (hd : B.map.tail d) (hdv : dartHeadVertex B.map d = v) :
    (contourPosition B (B.map.toCombinatorialMap.edgeInv
      (rightmostIncoming B v hs))).val ≤ (contourPosition B d).val := by
  let ρ : Equiv.Perm D := B.map.toCombinatorialMap.rot
  let τ : Equiv.Perm D := B.map.toCombinatorialMap.edgeInv
  have hri := rightmostIncoming_internal_characterization B v hs ht
  have hcorner := fresh_incoming_adjacent B v ht
    (fun u _ => fresh_incoming_before_outgoing B u)
  have hcycle : ρ.SameCycle (τ d) (rightmostIncoming B v hs) :=
    Quotient.exact (hdv.trans hri.1.symm)
  obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
  have hrec : ∀ n q, ¬ B.map.tail q → dartTailVertex B.map q = v →
      (ρ ^ n) q = rightmostIncoming B v hs →
      (contourPosition B (τ (rightmostIncoming B v hs))).val ≤
        (contourPosition B (τ q)).val := by
    intro n
    induction n with
    | zero =>
        intro q _ _ hq
        have hq' : q = rightmostIncoming B v hs := hq
        rw [hq']
    | succ n ih =>
        intro q hq hqv hn
        have hpv : dartTailVertex B.map (ρ q) = v :=
          (fresh_rot_vertex B q).trans hqv
        by_cases hp : B.map.tail (ρ q)
        · have heq := hri.2.2.2 q hqv hq hp
          rw [heq]
        · have hend : (ρ ^ n) (ρ q) = rightmostIncoming B v hs := by
            simpa only [pow_succ, Equiv.Perm.mul_apply] using hn
          have hqhead : dartHeadVertex B.map (τ q) = v := by
            simpa only [dartHeadVertex, dartTailVertex, τ,
              B.map.toCombinatorialMap.edgeInv_invol] using hqv
          have hphead : dartHeadVertex B.map (τ (ρ q)) = v := by
            simpa only [dartHeadVertex, dartTailVertex, τ,
              B.map.toCombinatorialMap.edgeInv_invol] using hpv
          have hc : B.map.toCombinatorialMap.faceSucc (τ (ρ q)) = τ (τ q) := by
            change ρ.symm (τ (τ (ρ q))) = τ (τ q)
            simp only [τ, B.map.toCombinatorialMap.edgeInv_invol, Equiv.symm_apply_apply]
          exact (ih _ hp hpv hend).trans
            (hcorner (τ (ρ q)) (τ q) (fresh_inverse_forward B _ hp)
              (fresh_inverse_forward B q hq) hphead hqhead hc).le
  have h := hrec n (τ d) ((B.map.tail_iff d (B.noMissingDarts d)).1 hd) hdv hn
  simpa only [τ, B.map.toCombinatorialMap.edgeInv_invol] using h

private theorem fresh_bounce_face_reverse
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (a : D) (ha : B.map.tail a)
    (hb : contourNext B a = B.map.toCombinatorialMap.edgeInv a) :
    ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc a) := by
  classical
  intro hf
  have hs := contour_forward_head_ne_source B a ha
  have hn := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
  have ht : dartHeadVertex B.map a ≠ B.sink := by
    intro heq
    exact B.isSink ⟨dartHeadVertex B.map (B.map.toCombinatorialMap.faceSucc a),
      B.map.toCombinatorialMap.faceSucc a, B.noMissingDarts _, hf,
      (fresh_face_vertex B a).trans heq, rfl⟩
  have hsel : B.map.toCombinatorialMap.edgeInv a =
      leftmostIncoming B (dartHeadVertex B.map a) hs :=
    (leftmostIncoming_internal_characterization B _ hs ht).2.2.2 _ rfl hn hf
  have he : contourNext B a = rightmostOutgoing B (dartHeadVertex B.map a) ht := by
    simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_right ht]
  have hforward : B.map.tail (rightmostOutgoing B (dartHeadVertex B.map a) ht) := by
    rw [← canonicalLRSelector_val B _ ht]
    exact (canonicalLRSelector B _ ht).property.2.1
  rw [← he, hb] at hforward
  exact hn hforward

/-- The head of a rotate edge has no incidence with an earlier Peano edge. -/
theorem peanoEdge_rotate_head_fresh
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (j : ℕ)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate) :
    ∀ k : Fin B.map.toCombinatorialMap.numEdges, k.val ≤ j →
      dartTailVertex B.map (peanoEdge B k) ≠
        dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) ∧
      dartHeadVertex B.map (peanoEdge B k) ≠
        dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) := by
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let v := dartHeadVertex B.map b
  have ha : B.map.tail a := peanoEdge_forward B _
  have hb : B.map.tail b := peanoEdge_forward B _
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨_, _, hbounce, _, hface, _⟩ := hc
  have hthird : B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b) =
      B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a) := by
    change B.map.toCombinatorialMap.rot.symm
      (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a)) =
        B.map.toCombinatorialMap.edgeInv b at hface
    exact B.map.toCombinatorialMap.rot.eq_symm_apply.mp hface.symm
  have hq : B.map.tail
      (B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)) := by
    rw [hthird]
    exact fresh_inverse_forward B _ (fresh_bounce_face_reverse B a ha hbounce)
  have hs : v ≠ B.source := contour_forward_head_ne_source B b hb
  have ht : v ≠ B.sink := by
    intro heq
    exact B.isSink ⟨dartHeadVertex B.map
        (B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b)),
      B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.edgeInv b),
      B.noMissingDarts _, hq,
      (fresh_rot_vertex B (B.map.toCombinatorialMap.edgeInv b)).trans heq, rfl⟩
  have hri : B.map.toCombinatorialMap.edgeInv b = rightmostIncoming B v hs :=
    (rightmostIncoming_internal_characterization B v hs ht).2.2.2 _ rfl
      ((B.map.tail_iff b (B.noMissingDarts b)).1 hb) hq
  intro k hk
  have hkj : k.val < j + 1 := by omega
  have hpos := peanoEdge_increasing_firstVisit B k ⟨j + 1, hj1⟩ hkj
  change (contourPosition B (peanoEdge B k)).val < (contourPosition B b).val at hpos
  constructor
  · intro hkv
    have h := fresh_incoming_before_outgoing B v b (peanoEdge B k) hb
      (peanoEdge_forward B k) rfl hkv
    omega
  · intro hkv
    have h := fresh_incoming_min B v hs ht (peanoEdge B k) (peanoEdge_forward B k) hkv
    rw [← hri, B.map.toCombinatorialMap.edgeInv_invol] at h
    omega

end DirectedDistances.PlanarMap

namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

/-- The prefix vertex invariant supplies the freshness required by a rotate step. -/
theorem kmswPeanoPrefixInv_rotateFresh
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate) : KMSWRotateFreshVertex P hj1 := by
  intro d hd
  obtain ⟨k, hk, hv⟩ := (I.vertices_prefix
    (dartHeadVertex B.map (peanoEdge B ⟨j + 1, hj1⟩))).1 ⟨d, hd⟩
  have hfresh := peanoEdge_rotate_head_fresh B j hj1 hkind k hk
  rcases hv with hv | hv
  · exact hfresh.1 hv
  · exact hfresh.2 hv

/-- Extend a prefix embedding through a rotate step using its vertex invariant. -/
@[expose] noncomputable def kmswPeanoPrefixEmbedding_rotate_of_inv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .rotate)
    (hcode : codeExtend c j = 1) : KMSWPeanoPrefixEmbedding B c (j + 1) hj1 :=
  kmswPeanoPrefixEmbedding_rotate P hj1 hcode hkind
    (kmswPeanoPrefixInv_rotateFresh B c j hj P I hj1 hkind)

end DirectedDistances.KMSW
