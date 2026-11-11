module

public import DirectedDistances.KMSW.InfiniteRotation

/-! # Outgoing rotation arcs and sewing corners

Missing darts remain in the rotation. Only present west darts are outgoing. -/

public section
namespace DirectedDistances.KMSW

/-- An entirely marked forward rotation arc, including both endpoints -/
@[expose] def RotationArc {D : Type*} (σ : Equiv.Perm D) (p : D → Prop)
    (d e : D) : Prop :=
  ∃ k : ℕ, (σ ^ k) d = e ∧ ∀ i : ℕ, i ≤ k → p ((σ ^ i) d)

/-- Present west darts are the outgoing arrows; missing edges have no arrows -/
@[expose] def stageOutgoing (s : State) (d : StageDart s.nextEdge) : Prop :=
  d.2 = false ∧ s.present d.1.val = true

/-- Candidate strengthened induction invariant for `def-kmsw`
interval property. The second puts every UL west dart at the end of its
outgoing block, allowing a full outgoing orbit. The third says that the
active east vertex and the UR frontier have no outgoing arrows; this is the
motivation for the uniqueness lemmas below about the activated and pendant
edges. This predicate is a formulation, not an assertion that the stage
recursion preserves it. -/
@[expose] def StageOutgoingInvariant (s : State)
    (σ : Equiv.Perm (StageDart s.nextEdge)) : Prop :=
  (∀ d e, stageEndpoint s d = stageEndpoint s e →
    stageOutgoing s d → stageOutgoing s e →
    RotationArc σ (stageOutgoing s) d e ∨ RotationArc σ (stageOutgoing s) e d) ∧
  (∀ e (he : e < s.nextEdge), e ∈ s.UL →
    ∀ d, stageEndpoint s d = s.west e → stageOutgoing s d →
      RotationArc σ (stageOutgoing s) d (⟨e, he⟩, false)) ∧
  (∀ e < s.nextEdge, s.present e = true →
    s.west e ∉ CutConverse.pendingVertices s)

/-- Every present finite-stage edge has already been active -/
theorem stagePresent_exists_active (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present e = true) :
    ∃ m ≤ n, e = act w m := by
  induction n with
  | zero =>
    have he0 : e = 0 := by change e < 1 at he; omega
    exact ⟨0, le_refl _, he0⟩
  | succ n ih =>
    by_cases ha : e = act w (n + 1)
    · exact ⟨n + 1, le_refl _, ha⟩
    · by_cases hold : e < (kmswStage w n).nextEdge
      · have hpold : (kmswStage w n).present e = true := by
          change (kmswStep (kmswStage w n) (w n)).present e = true at hp
          rw [kmswStep_present_existing _ _ hold] at hp
          simpa only [show e ≠ (kmswStep (kmswStage w n) (w n)).active from ha,
            ↓reduceIte] using hp
        obtain ⟨m, hm, hme⟩ := ih hold hpold
        exact ⟨m, hm.trans (Nat.le_succ n), hme⟩
      · exfalso
        change e < (kmswStep (kmswStage w n) (w n)).nextEdge at he
        change (kmswStep (kmswStage w n) (w n)).present e = true at hp
        change e ≠ (kmswStep (kmswStage w n) (w n)).active at ha
        cases hc : kmswCodeStep (w n) with
        | down =>
          cases hr : (kmswStage w n).UR <;>
            simp only [kmswStep, hc, kmswStepOfStep, hr, State.addEdge] at he hp ha
          all_goals omega
        | left =>
          cases hl : (kmswStage w n).UL.dropLast.reverse <;>
            simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge] at he hp ha
          all_goals
            split at hp <;> simp_all only [Bool.false_eq_true] <;> omega
        | up =>
          simp only [kmswStep, hc, kmswStepOfStep, State.addEdge] at he hp ha
          split at hp
          · cases hp
          · omega



theorem stageOutgoing_frontier_empty (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present e = true) :
    (kmswStage w n).west e ∉ CutConverse.pendingVertices (kmswStage w n) := by
  obtain ⟨m, hm, rfl⟩ := stagePresent_exists_active w n e he hp
  rw [(edge_endpoints_eq w he).1]
  exact (CutConverse.frontier_history w n).2.2 m hm

/-- The pendant insertion corner is at a vertex with no outgoing arrow -/
theorem stageOutgoing_active_east_empty (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (hd : stageOutgoing (kmswStage w n) d) :
    stageEndpoint (kmswStage w n) d ≠ (kmswStage w n).east (kmswStage w n).active := by
  have h := stageOutgoing_frontier_empty w n d.1.val d.1.isLt hd.2
  simp only [CutConverse.pendingVertices, List.mem_cons, not_or] at h
  simpa only [stageEndpoint, hd.1, Bool.false_eq_true, ↓reduceIte] using h.1

/-- Every UR west vertex has no outgoing arrow before activation -/
theorem stageOutgoing_UR_west_empty (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UR) (f : ℕ)
    (hf : f < (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present f = true) :
    (kmswStage w n).west f ≠ (kmswStage w n).west e := by
  have hmem : (kmswStage w n).west e ∈
      CutConverse.pendingVertices (kmswStage w n) := by
    apply List.dropLast_subset _
    rw [← (CutConverse.frontier_history w n).1]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  intro h
  apply stageOutgoing_frontier_empty w n f hf hp
  rw [h]
  exact hmem

/-- Any present edge at stage `n + 1` whose west vertex is the west vertex of
the activated upper-right edge is that edge (`def-kmsw`, -/
theorem stageOutgoing_activation_unique (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hc : kmswCodeStep (w n) = .down)
    (hr : (kmswStage w n).UR = e :: es)
    (f : ℕ) (hf : f < (kmswStage w (n + 1)).nextEdge)
    (hp : (kmswStage w (n + 1)).present f = true)
    (hv : (kmswStage w (n + 1)).west f = (kmswStage w n).west e) : f = e := by
  by_contra hfe
  have hf' : f < (kmswStage w n).nextEdge := by
    simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hr] using hf
  have hp' : (kmswStage w n).present f = true := by
    simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hr, hfe, ↓reduceIte] using hp
  have hv' : (kmswStage w n).west f = (kmswStage w n).west e := by
    simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hr] using hv
  exact stageOutgoing_UR_west_empty w n e (by rw [hr]; exact List.mem_cons_self)
    f hf' hp' hv'

/-- Any present edge at stage `n + 1` whose west vertex is the old active east -/
theorem stageOutgoing_pendant_unique (w : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (w n) = .down) (hr : (kmswStage w n).UR = [])
    (f : ℕ) (hf : f < (kmswStage w (n + 1)).nextEdge)
    (hp : (kmswStage w (n + 1)).present f = true)
    (hv : (kmswStage w (n + 1)).west f =
      (kmswStage w n).east (kmswStage w n).active) :
    f = (kmswStage w n).nextEdge := by
  by_contra hfe
  have hf' : f < (kmswStage w n).nextEdge := by
    simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hr, State.addEdge] at hf
    omega
  have hp' : (kmswStage w n).present f = true := by
    simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hr, State.addEdge,
      hfe, ↓reduceIte] using hp
  have hv' : (kmswStage w n).west f =
      (kmswStage w n).east (kmswStage w n).active := by
    simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hr, State.addEdge,
      hfe, ↓reduceIte] using hv
  exact stageOutgoing_active_east_empty w n (⟨f, hf'⟩, false) ⟨rfl, hp'⟩ hv'

/-- A marked point has a length-zero entirely marked arc to itself -/
theorem RotationArc.refl {D : Type*} (σ : Equiv.Perm D) (p : D → Prop)
    (d : D) (hd : p d) : RotationArc σ p d d := by
  refine ⟨0, rfl, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst i
  exact hd

/-- The proposed strengthened invariant holds at the initial stage -/
theorem stageOutgoingInvariant_zero (w : ℕ → Fin 3) :
    StageOutgoingInvariant (kmswStage w 0) (stageRot w 0) := by
  let z : Fin (kmswStage w 0).nextEdge := ⟨0, by change 0 < 1; decide⟩
  have hout : ∀ d : StageDart (kmswStage w 0).nextEdge,
      stageOutgoing (kmswStage w 0) d → d = (z, false) := by
    rintro ⟨e, b⟩ ⟨hb, _⟩
    have he : e = z := Fin.ext (by have := e.isLt; change e.val < 1 at this; dsimp [z]; omega)
    cases he
    cases hb
    rfl
  refine ⟨?_, ?_, stageOutgoing_frontier_empty w 0⟩
  · intro d e _ hd he
    have heq : d = e := (hout d hd).trans (hout e he).symm
    subst e
    exact Or.inl (RotationArc.refl _ _ d hd)
  · intro e he heUL d _ hd
    have he0 : e = 0 := by simpa only [kmswStage, kmswInit, List.mem_singleton] using heUL
    have hde : d = (⟨e, he⟩, false) := by
      rw [hout d hd]
      exact Prod.ext (Fin.ext he0.symm) rfl
    rw [← hde]
    exact RotationArc.refl _ _ d hd

private theorem outgoingInvariant_activate (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hr : (kmswStage w n).UR = e :: es)
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    let s := kmswStage w n
    let t : State := { s with present := fun f => if f = e then true else s.present f
                              active := e, UL := s.UL ++ [e], UR := es }
    StageOutgoingInvariant t (stageRot w n) := by
  let s := kmswStage w n
  let t : State := { s with present := fun f => if f = e then true else s.present f
                            active := e, UL := s.UL ++ [e], UR := es }
  change StageOutgoingInvariant t (stageRot w n)
  have heUR : e ∈ s.UR := by rw [hr]; exact List.mem_cons_self
  have he : e < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr heUR)))
  let a : StageDart s.nextEdge := (⟨e, he⟩, false)
  have hend : ∀ d : StageDart s.nextEdge, stageEndpoint t d = stageEndpoint s d := by
    intro d; rfl
  have old_out : ∀ d : StageDart s.nextEdge, stageOutgoing s d → stageOutgoing t d := by
    rintro d ⟨hb, hp⟩
    refine ⟨hb, ?_⟩
    change (if d.1.val = e then true else s.present d.1.val) = true
    split
    · rfl
    · exact hp
  have out_split : ∀ d : StageDart s.nextEdge,
      stageOutgoing t d → stageOutgoing s d ∨ d = a := by
    rintro d ⟨hb, hp⟩
    by_cases hde : d.1.val = e
    · exact Or.inr (Prod.ext (Fin.ext hde) hb)
    · exact Or.inl ⟨hb, by simpa only [t, hde, ↓reduceIte] using hp⟩
  have new_out : stageOutgoing t a := ⟨rfl, by simp only [t, a, ↓reduceIte]⟩
  have only_new : ∀ d : StageDart s.nextEdge, stageOutgoing t d →
      stageEndpoint t d = s.west e → d = a := by
    intro d hd hv
    rcases out_split d hd with hold | ha
    · have hne := stageOutgoing_UR_west_empty w n e heUR d.1.val d.1.isLt hold.2
      have hw : s.west d.1.val = s.west e := by
        simpa only [hend, stageEndpoint, hold.1, Bool.false_eq_true, ↓reduceIte] using hv
      exact (hne hw).elim
    · exact ha
  have arc_old : ∀ d f : StageDart s.nextEdge,
      RotationArc (stageRot w n) (stageOutgoing s) d f →
      RotationArc (stageRot w n) (stageOutgoing t) d f := by
    rintro d f ⟨k, hk, hp⟩
    exact ⟨k, hk, fun i hi => old_out _ (hp i hi)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro d f hv hd hf
    rcases out_split d hd with hod | had
    · rcases out_split f hf with hof | haf
      · exact (hi.1 d f hv hod hof).imp (arc_old d f) (arc_old f d)
      · have hd' : d = a := only_new d hd (by rw [hv, haf]; rfl)
        subst d
        subst f
        exact Or.inl (RotationArc.refl _ _ a new_out)
    · have hf' : f = a := only_new f hf (by rw [← hv, had]; rfl)
      subst d
      subst f
      exact Or.inl (RotationArc.refl _ _ a new_out)
  · intro f hf hfUL d hv hd
    change f ∈ s.UL ++ [e] at hfUL
    rcases List.mem_append.mp hfUL with hfUL | hfe
    · have hfp : s.present f = true := (kmswStage_status w n).2.1 f hfUL
      have hdf : stageOutgoing s d := by
        rcases out_split d hd with hod | had
        · exact hod
        · have hne := stageOutgoing_UR_west_empty w n e heUR f hf hfp
          have hw : s.west e = s.west f := by
            simpa only [had, a, stageEndpoint, t, Bool.false_eq_true, ↓reduceIte] using hv
          exact (hne hw.symm).elim
      exact arc_old _ _ (hi.2.1 f hf hfUL d hv hdf)
    · have hfe' : f = e := List.mem_singleton.mp hfe
      subst f
      have hda := only_new d hd hv
      have haeq : (⟨e, hf⟩, false) = a := rfl
      rw [hda, haeq]
      exact RotationArc.refl _ _ a new_out
  · intro f hf hp hv
    have hsPending : CutConverse.pendingVertices s =
        s.east s.active :: s.east e :: es.map s.east := by
      have hr' : s.UR = e :: es := hr
      simp only [CutConverse.pendingVertices, hr', List.map_cons]
    have htPending : CutConverse.pendingVertices t = s.east e :: es.map s.east := rfl
    have hmem : s.west f ∈ s.east e :: es.map s.east := hv
    by_cases hfe : f = e
    · subst f
      have hhead : s.west e = s.east s.active := by
        have hcoh := (CutConverse.frontier_history w n).1
        change s.UR.map s.west = (CutConverse.pendingVertices s).dropLast at hcoh
        rw [hr, hsPending] at hcoh
        exact List.cons.inj hcoh |>.1
      have hnodup := (CutConverse.frontier_history w n).2.1
      rw [hsPending] at hnodup
      exact (List.nodup_cons.mp hnodup).1 (hhead ▸ hmem)
    · have hpold : s.present f = true := by
        simpa only [t, hfe, ↓reduceIte] using hp
      exact hi.2.2 f hf hpold (by rw [hsPending]; exact List.mem_cons_of_mem _ hmem)

/-- At a complete vertex every finite rotation power agrees with the limiting
rotation, including all intermediate darts (`remark-kmsw-infinite`, -/
theorem kmswInfRot_pow_eq_stage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) d)) (k : ℕ) :
    (kmswInfRot w hfin ^ k) (d.1.val, d.2) =
      (((stageRot w n ^ k) d).1.val, ((stageRot w n ^ k) d).2) := by
  have hep : ∀ j : ℕ, stageEndpoint (kmswStage w n) ((stageRot w n ^ j) d) =
      stageEndpoint (kmswStage w n) d := by
    intro j
    apply ((stageRot_sameCycle_iff_endpoint_eq w n d _).1 ?_).symm
    exact ⟨(j : ℤ), by simp⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [ih]
    exact kmswInfRot_eq_stage w hfin n ((stageRot w n ^ k) d) (by rw [hep]; exact hc)

end DirectedDistances.KMSW
