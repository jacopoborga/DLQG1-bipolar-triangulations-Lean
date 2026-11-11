module

public import DirectedDistances.KMSW.OutgoingInterval
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.RandomWalk.PitmanCodes
import DirectedDistances.KMSW.UIQBOTOrientation




























public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

/-- Horizontal nonnegativity excludes the fresh-left branch of `def-kmsw` -/
theorem kmswStage_left_not_fresh_of_L_nonneg (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (n : ℕ) (hc : kmswCodeStep (w n) = .left) :
    (kmswStage w n).UL.dropLast.reverse ≠ [] := by
  have hw : w n = 0 := by
    by_contra h0
    by_cases h1 : w n = 1 <;> simp [kmswCodeStep, h0, h1] at hc
  intro hf
  have hlen := congrArg List.length hf
  simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hlen
  have hcount := kmswStage_UL_length w n
  obtain ⟨j, _, hj⟩ := runningMin_attained (L w) n
  have hm : 0 ≤ minL w n := by
    change 0 ≤ runningMin (L w) n
    rw [hj]
    exact hL j
  have hm0 := runningMin_le (L w) n 0 (Nat.zero_le n)
  change minL w n ≤ L w 0 at hm0
  have hz : L w 0 = 0 := rfl
  have hnext := hL (n + 1)
  have hstep : L w (n + 1) = L w n +
      (lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  rw [hw, lazyTwoDimensionalStep_zero] at hstep
  omega

/-- Every Pitman code excludes the fresh-left branch, with no extra -/
theorem pitmanCode_left_not_fresh (ω : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (pitmanCode (fun i => ω (i + 1)) n) = .left) :
    (kmswStage (pitmanCode (fun i => ω (i + 1))) n).UL.dropLast.reverse ≠ [] := by
  apply kmswStage_left_not_fresh_of_L_nonneg _ ?_ n hc
  intro j
  rw [kmsw_L_eq]
  exact integrateCodes_pitmanCode_fst_nonneg _ j

/-- An outgoing stage arc at a complete vertex transfers, with every
intermediate dart, to the limiting rotation (`remark-kmsw-infinite`,
at an allocated stage, including for all intermediate darts. -/
theorem RotationArc.to_kmswInfRot (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (n : ℕ) (d e : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) d))
    (ha : RotationArc (stageRot w n) (stageOutgoing (kmswStage w n)) d e) :
    RotationArc (kmswInfRot w hfin)
      (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1)
      (d.1.val, d.2) (e.1.val, e.2) := by
  obtain ⟨k, hk, hp⟩ := ha
  refine ⟨k, ?_, ?_⟩
  · rw [kmswInfRot_pow_eq_stage w hfin n d hc k, hk]
  · intro i hi
    rw [kmswInfRot_pow_eq_stage w hfin n d hc i]
    have hout := hp i hi
    exact ⟨hout.1, n, ((stageRot w n ^ i) d).1.isLt, hout.2⟩

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

private theorem invariant_transport {s t : State} (h : s = t)
    (σ : Equiv.Perm (StageDart s.nextEdge)) (τ : Equiv.Perm (StageDart t.nextEdge))
    (hr : StageRotation.resize (congrArg State.nextEdge h) σ = τ)
    (hi : StageOutgoingInvariant t τ) : StageOutgoingInvariant s σ := by
  cases h
  cases hr
  exact hi

/-- Activation preserves the interval and all recorded corner invariants
is needed for this branch. -/
theorem stageOutgoingInvariant_activation (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hc : kmswCodeStep (w n) = .down)
    (hr : (kmswStage w n).UR = e :: es)
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    StageOutgoingInvariant (kmswStage w (n + 1)) (stageRot w (n + 1)) := by
  have h := outgoingInvariant_activate w n e es hr hi
  apply invariant_transport (by
    simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hr]) _ _ ?_ h
  exact StageRotation.step_activation _ _ _ _ _ hc e es hr

private theorem cast_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w (n + 1))
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) =
      stageEndpoint (kmswStage w n) d := by
  have hs := kmswStage_endpoints_stable w (Nat.le_succ n) d.1.isLt
  cases hb : d.2 <;> simp only [stageEndpoint, outerSucc_castDart, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact hs.1
  · exact hs.2

private theorem arc_step_local (w : ℕ → Fin 3) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge)
    (hnew : ∀ f, (kmswStage w n).nextEdge ≤ f →
      f < (kmswStage w (n + 1)).nextEdge →
      (kmswStage w (n + 1)).west f ≠ stageEndpoint (kmswStage w n) d ∧
      (kmswStage w (n + 1)).east f ≠ stageEndpoint (kmswStage w n) d)
    (ha : RotationArc (stageRot w n) (stageOutgoing (kmswStage w n)) d e) :
    RotationArc (stageRot w (n + 1)) (stageOutgoing (kmswStage w (n + 1)))
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d)
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) e) := by
  let C := outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
  have hep (i : ℕ) : stageEndpoint (kmswStage w n) ((stageRot w n ^ i) d) =
      stageEndpoint (kmswStage w n) d := by
    apply ((stageRot_sameCycle_iff_endpoint_eq w n d _).1 ?_).symm
    exact ⟨(i : ℤ), by simp⟩
  have hpow (i : ℕ) : (stageRot w (n + 1) ^ i) (C d) = C ((stageRot w n ^ i) d) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rw [ih]
      exact stageRot_step_local w n _ hnew _ (hep i)
  obtain ⟨k, hk, hp⟩ := ha
  refine ⟨k, ?_, ?_⟩
  · rw [hpow, hk]
  · intro i hi
    rw [hpow]
    have ho := hp i hi
    refine ⟨ho.1, ?_⟩
    change (kmswStep (kmswStage w n) (w n)).present ((stageRot w n ^ i) d).1.val = true
    rw [kmswStep_present_existing _ _ ((stageRot w n ^ i) d).1.isLt]
    split
    · rfl
    · exact ho.2

/-- Pendant insertion preserves the interval and all recorded corners -/
theorem stageOutgoingInvariant_pendant (w : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (w n) = .down) (hr : (kmswStage w n).UR = [])
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    StageOutgoingInvariant (kmswStage w (n + 1)) (stageRot w (n + 1)) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  let C := outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
  have hsize : t.nextEdge = s.nextEdge + 1 := by
    simp only [t, s, kmswStage, kmswStep, hc, kmswStepOfStep, hr, State.addEdge]
  let a : StageDart t.nextEdge := (⟨s.nextEdge, by omega⟩, false)
  have ha : stageOutgoing t a := by
    constructor
    · rfl
    · simp only [t, a, s, kmswStage, kmswStep, hc, kmswStepOfStep, hr,
        State.addEdge, ↓reduceIte]
  have hea : stageEndpoint t a = s.east s.active := by
    simp only [stageEndpoint, a, t, s, kmswStage, kmswStep, hc, kmswStepOfStep,
      hr, State.addEdge, Bool.false_eq_true, ↓reduceIte]
  have split_out (d : StageDart t.nextEdge) (hd : stageOutgoing t d) :
      (∃ x : StageDart s.nextEdge, d = C x ∧ stageOutgoing s x) ∨ d = a := by
    by_cases hold : d.1.val < s.nextEdge
    · let x : StageDart s.nextEdge := (⟨d.1.val, hold⟩, d.2)
      refine Or.inl ⟨x, rfl, hd.1, ?_⟩
      have hne : d.1.val ≠ s.nextEdge := by omega
      simpa only [t, s, kmswStage, kmswStep, hc, kmswStepOfStep, hr,
        State.addEdge, hne, ↓reduceIte] using hd.2
    · apply Or.inr
      have hb := d.1.isLt
      exact Prod.ext (Fin.ext (by dsimp [a]; omega)) hd.1
  have only_new (d : StageDart t.nextEdge) (hd : stageOutgoing t d)
      (hv : stageEndpoint t d = s.east s.active) : d = a := by
    have hw : t.west d.1.val = s.east s.active := by
      simpa only [stageEndpoint, hd.1, Bool.false_eq_true, ↓reduceIte] using hv
    exact Prod.ext (Fin.ext (stageOutgoing_pendant_unique w n hc hr
      d.1.val d.1.isLt hd.2 hw)) hd.1
  have arc_old (d e : StageDart s.nextEdge) (hd : stageOutgoing s d)
      (harc : RotationArc (stageRot w n) (stageOutgoing s) d e) :
      RotationArc (stageRot w (n + 1)) (stageOutgoing t) (C d) (C e) := by
    apply arc_step_local w n d e ?_ harc
    intro f hf hf'
    change s.nextEdge ≤ f at hf
    change f < t.nextEdge at hf'
    have hfe : f = s.nextEdge := by omega
    subst f
    have hne := stageOutgoing_active_east_empty w n d hd
    have hb := stageEndpoint_lt_nextVertex w n d
    change stageEndpoint s d < s.nextVertex at hb
    constructor
    · have hw : t.west s.nextEdge = s.east s.active := by
        simp only [t, s, kmswStage, kmswStep, hc, kmswStepOfStep, hr,
          State.addEdge, ↓reduceIte]
      rw [hw]
      exact Ne.symm hne
    · have he : t.east s.nextEdge = s.nextVertex := by
        simp only [t, s, kmswStage, kmswStep, hc, kmswStepOfStep, hr,
          State.addEdge, ↓reduceIte]
      rw [he]
      exact (ne_of_lt hb).symm
  refine ⟨?_, ?_, stageOutgoing_frontier_empty w (n + 1)⟩
  · intro d e hv hd he
    rcases split_out d hd with ⟨x, rfl, hx⟩ | rfl
    · rcases split_out e he with ⟨y, rfl, hy⟩ | rfl
      · have hv' : stageEndpoint s x = stageEndpoint s y := by
          simpa only [C, cast_endpoint] using hv
        exact (hi.1 x y hv' hx hy).imp (arc_old x y hx) (arc_old y x hy)
      · have heq := only_new (C x) hd (hv.trans hea)
        rw [heq]
        exact Or.inl (RotationArc.refl _ _ a ha)
    · have heq := only_new e he (hv.symm.trans hea)
      rw [heq]
      exact Or.inl (RotationArc.refl _ _ a ha)
  · intro f hf hfUL d hv hd
    have hmem : f ∈ s.UL ++ [s.nextEdge] := by
      simpa only [t, s, kmswStage, kmswStep, hc, kmswStepOfStep, hr, State.addEdge] using hfUL
    rcases List.mem_append.mp hmem with hfold | hfnew
    · have hfo := stageRotation_UL_bound w n f hfold
      rcases split_out d hd with ⟨x, rfl, hx⟩ | rfl
      · have hv' : stageEndpoint s x = s.west f := by
          rw [cast_endpoint] at hv
          have hs := (kmswStage_endpoints_stable w (Nat.le_succ n) hfo).1
          exact hv.trans hs
        have heq : (⟨f, hf⟩, false) = C (⟨f, hfo⟩, false) := rfl
        rw [heq]
        exact arc_old _ _ hx (hi.2.1 f hfo hfold x hv' hx)
      · have hfp : s.present f = true := (kmswStage_status w n).2.1 f hfold
        have hempty := stageOutgoing_active_east_empty w n (⟨f, hfo⟩, false) ⟨rfl, hfp⟩
        have hs := (kmswStage_endpoints_stable w (Nat.le_succ n) hfo).1
        have hbad : s.west f = s.east s.active := hs.symm.trans (hv.symm.trans hea)
        exact (hempty hbad).elim
    · have hfe := List.mem_singleton.mp hfnew
      subst f
      have hw : t.west s.nextEdge = s.east s.active := by
        simp only [t, s, kmswStage, kmswStep, hc, kmswStepOfStep, hr,
          State.addEdge, ↓reduceIte]
      have hda := only_new d hd (hv.trans hw)
      rw [hda]
      exact RotationArc.refl _ _ a ha

end DirectedDistances.KMSW
