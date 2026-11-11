module

public import DirectedDistances.KMSW.OutgoingIntervalUIQBOT
import DirectedDistances.KMSW.LocalFinitenessUpperChain

/-! # Marked rotation arcs through insertion splices -/

public section
namespace DirectedDistances.KMSW

/-- Concatenation of entirely marked rotation arcs (`def-kmsw`, -/
theorem RotationArc.trans {D : Type*} {σ : Equiv.Perm D} {p : D → Prop}
    {d e f : D} (h : RotationArc σ p d e) (h' : RotationArc σ p e f) :
    RotationArc σ p d f := by
  obtain ⟨k, hk, hp⟩ := h
  obtain ⟨l, hl, hq⟩ := h'
  refine ⟨l + k, ?_, ?_⟩
  · rw [pow_add, Equiv.Perm.mul_apply, hk, hl]
  · intro i hi
    by_cases hik : i ≤ k
    · exact hp i hik
    · have hie : i = (i - k) + k := by omega
      rw [hie, pow_add, Equiv.Perm.mul_apply, hk]
      exact hq (i - k) (by omega)

/-- Remove the initial dart of a nontrivial marked arc (`def-kmsw`, -/
theorem RotationArc.tail {D : Type*} {σ : Equiv.Perm D} {p : D → Prop}
    {d e : D} (h : RotationArc σ p d e) (hne : d ≠ e) :
    RotationArc σ p (σ d) e := by
  obtain ⟨k, hk, hp⟩ := h
  cases k with
  | zero => exact (hne hk).elim
  | succ k =>
    refine ⟨k, ?_, ?_⟩
    · simpa only [pow_succ, Equiv.Perm.mul_apply] using hk
    · intro i hi
      have h := hp (i + 1) (by omega)
      simpa only [pow_succ, Equiv.Perm.mul_apply] using h

/-- A map taking each marked successor step to a marked arc takes whole -/
theorem RotationArc.map {D E : Type*} {σ : Equiv.Perm D} {τ : Equiv.Perm E}
    {p : D → Prop} {q : E → Prop} (C : D → E)
    (hmark : ∀ d, p d → q (C d))
    (hstep : ∀ d, p d → p (σ d) → RotationArc τ q (C d) (C (σ d)))
    {d e : D} (h : RotationArc σ p d e) : RotationArc τ q (C d) (C e) := by
  obtain ⟨k, hk, hp⟩ := h
  subst e
  induction k with
  | zero => exact RotationArc.refl _ _ _ (hmark d (hp 0 (by omega)))
  | succ k ih =>
    have hfirst := ih (fun i hi => hp i (by omega))
    have hlast := hstep ((σ ^ k) d) (hp k (by omega))
      (by simpa only [pow_succ', Equiv.Perm.mul_apply] using hp (k + 1) (by omega))
    simpa only [pow_succ', Equiv.Perm.mul_apply] using hfirst.trans hlast

private theorem arc_one {D : Type*} (σ : Equiv.Perm D) (p : D → Prop)
    (d : D) (hd : p d) (he : p (σ d)) : RotationArc σ p d (σ d) := by
  refine ⟨1, by simp only [pow_one], ?_⟩
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact hd
  · simpa only [pow_one] using he

private theorem insertion_invariant {s t : State}
    {σ : Equiv.Perm (StageDart s.nextEdge)} {τ : Equiv.Perm (StageDart t.nextEdge)}
    (C : StageDart s.nextEdge → StageDart t.nextEdge) (hC : Function.Injective C)
    (a : StageDart s.nextEdge) (x : StageDart t.nextEdge)
    (hi : StageOutgoingInvariant s σ) (ha : stageOutgoing s a)
    (haUL : a.1.val ∈ s.UL) (hx : stageOutgoing t x)
    (hend : ∀ d, stageEndpoint t (C d) = stageEndpoint s d)
    (hex : stageEndpoint t x = stageEndpoint s a)
    (hmark : ∀ d, stageOutgoing s d → stageOutgoing t (C d))
    (hsplit : ∀ d, stageOutgoing t d →
      (∃ b, d = C b ∧ stageOutgoing s b) ∨ d = x)
    (hUL : ∀ f (hf : f < t.nextEdge), f ∈ t.UL →
      (∃ g : Fin s.nextEdge, g.val ∈ s.UL ∧ (g, false) ≠ a ∧
        (⟨f, hf⟩, false) = C (g, false)) ∨ (⟨f, hf⟩, false) = x)
    (hnext : τ (C a) = x)
    (harc : ∀ d e, RotationArc σ (stageOutgoing s) d e →
      RotationArc τ (stageOutgoing t) (C d) (C e))
    (hfront : ∀ e < t.nextEdge, t.present e = true →
      t.west e ∉ CutConverse.pendingVertices t) :
    StageOutgoingInvariant t τ := by
  have old_to_new (b : StageDart s.nextEdge) (hb : stageOutgoing s b)
      (hv : stageEndpoint s b = stageEndpoint s a) :
      RotationArc τ (stageOutgoing t) (C b) x := by
    have hwa : stageEndpoint s a = s.west a.1.val := by
      simp only [stageEndpoint, ha.1, Bool.false_eq_true, ↓reduceIte]
    have hba := hi.2.1 a.1.val a.1.isLt haUL b (hv.trans hwa) hb
    have hae : (⟨a.1.val, a.1.isLt⟩, false) = a := by
      exact Prod.ext rfl ha.1.symm
    rw [hae] at hba
    have hstep : RotationArc τ (stageOutgoing t) (C a) x := by
      rw [← hnext]
      exact arc_one τ _ _ (hmark a ha) (hnext ▸ hx)
    exact (harc b a hba).trans hstep
  refine ⟨?_, ?_, hfront⟩
  · intro d e hv hd he
    rcases hsplit d hd with ⟨b, rfl, hb⟩ | rfl
    · rcases hsplit e he with ⟨c, rfl, hc⟩ | rfl
      · have hv' : stageEndpoint s b = stageEndpoint s c := by
          simpa only [hend] using hv
        exact (hi.1 b c hv' hb hc).imp (harc b c) (harc c b)
      · exact Or.inl (old_to_new b hb (by rw [← hend, hv, hex]))
    · rcases hsplit e he with ⟨b, rfl, hb⟩ | rfl
      · exact Or.inr (old_to_new b hb (by rw [← hend, ← hv, hex]))
      · exact Or.inl (RotationArc.refl _ _ _ hx)
  · intro f hf hfUL d hv hd
    rcases hUL f hf hfUL with ⟨g, hgUL, hga, hfg⟩ | hfx
    · have hgv : t.west f = stageEndpoint s (g, false) := by
        calc
          t.west f = stageEndpoint t (⟨f, hf⟩, false) := rfl
          _ = stageEndpoint t (C (g, false)) := congrArg _ hfg
          _ = stageEndpoint s (g, false) := hend _
      rcases hsplit d hd with ⟨b, rfl, hb⟩ | rfl
      · rw [hfg]
        exact harc b (g, false) (hi.2.1 g.val g.isLt hgUL b
          (by rw [hend, hgv] at hv; exact hv) hb)
      · have hv' : stageEndpoint s a = s.west g.val := by
          rw [hex, hgv] at hv
          exact hv
        have hag := hi.2.1 g.val g.isLt hgUL a hv' ha
        have htail := (harc a (g, false) hag).tail
          (fun h => hga (hC h).symm)
        rw [hnext] at htail
        rw [hfg]
        exact htail
    · have hv' : stageEndpoint t d = stageEndpoint t x := by
        rw [← hfx]
        exact hv
      rw [hfx]
      rcases hsplit d hd with ⟨b, rfl, hb⟩ | rfl
      · exact old_to_new b hb (by rw [hend, hex] at hv'; exact hv')
      · exact RotationArc.refl _ _ _ hx

private theorem invariant_transport {s t : State} (h : s = t)
    (σ : Equiv.Perm (StageDart s.nextEdge)) (τ : Equiv.Perm (StageDart t.nextEdge))
    (hr : StageRotation.resize (congrArg State.nextEdge h) σ = τ)
    (hi : StageOutgoingInvariant t τ) : StageOutgoingInvariant s σ := by
  cases h
  cases hr
  exact hi

private theorem up_invariant (w : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (w n) = .up)
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    let s := kmswStage w n
    StageOutgoingInvariant (kmswStepOfStep s .up)
      (StageRotation.up s.nextEdge (stageRot w n)
        (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
        (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true)) := by
  let s := kmswStage w n
  let t := kmswStepOfStep s .up
  let σ := stageRot w n
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
  let A : StageDart s.nextEdge := (a.1, true)
  let τ := StageRotation.up s.nextEdge σ a A
  let C : StageDart s.nextEdge → StageDart t.nextEdge :=
    fun d => StageRotation.allocation s.nextEdge 2 (.inl d)
  let x : StageDart t.nextEdge := StageRotation.allocation s.nextEdge 2 (.inr (0, false))
  change StageOutgoingInvariant t τ
  have haUL : s.active ∈ s.UL := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    rw [hxs]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have ha : stageOutgoing s a := ⟨rfl, (kmswStage_status w n).2.1 _ haUL⟩
  have hx : stageOutgoing t x := by
    constructor
    · rfl
    · simp [t, x, StageRotation.allocation, kmswStepOfStep, State.addEdge]
  have hmark (d : StageDart s.nextEdge) (hd : stageOutgoing s d) :
      stageOutgoing t (C d) := by
    have h0 : d.1.val ≠ s.nextEdge := by omega
    have h1 : d.1.val ≠ s.nextEdge + 1 := by omega
    refine ⟨hd.1, ?_⟩
    change (if d.1.val = s.nextEdge + 1 then false else
      if d.1.val = s.nextEdge then true else s.present d.1.val) = true
    simpa only [h0, h1, ↓reduceIte] using hd.2
  have hsplit (d : StageDart t.nextEdge) (hd : stageOutgoing t d) :
      (∃ b, d = C b ∧ stageOutgoing s b) ∨ d = x := by
    by_cases hold : d.1.val < s.nextEdge
    · let b : StageDart s.nextEdge := (⟨d.1.val, hold⟩, d.2)
      have h0 : d.1.val ≠ s.nextEdge := by omega
      have h1 : d.1.val ≠ s.nextEdge + 1 := by omega
      exact Or.inl ⟨b, rfl, hd.1, by simpa only [t, kmswStepOfStep,
        State.addEdge, h0, h1, ↓reduceIte] using hd.2⟩
    · have hb := d.1.isLt
      change d.1.val < s.nextEdge + 2 at hb
      have hn : d.1.val ≠ s.nextEdge + 1 := by
        intro hn
        have hp := hd.2
        simp only [t, kmswStepOfStep, State.addEdge, hn, ↓reduceIte,
          Bool.false_eq_true] at hp
      exact Or.inr (Prod.ext (Fin.ext (by dsimp [x, StageRotation.allocation]; omega)) hd.1)
  have hend (d : StageDart s.nextEdge) : stageEndpoint t (C d) = stageEndpoint s d := by
    have h0 : d.1.val ≠ s.nextEdge := by omega
    have h1 : d.1.val ≠ s.nextEdge + 1 := by omega
    rcases d with ⟨de, db⟩
    simp only [stageEndpoint, t, C, StageRotation.allocation_old, kmswStepOfStep,
      State.addEdge, h0, h1, ↓reduceIte]
  have hex : stageEndpoint t x = stageEndpoint s a := by
    simp [stageEndpoint, t, x, a, StageRotation.allocation, kmswStepOfStep, State.addEdge]
  have hnext : τ (C a) = x := by
    rw [StageRotation.up_old]
    simp only [↓reduceIte]
    rfl
  have harc (d e : StageDart s.nextEdge)
      (h : RotationArc σ (stageOutgoing s) d e) :
      RotationArc τ (stageOutgoing t) (C d) (C e) := by
    apply h.map C hmark
    intro b hb hb'
    have hne : σ b ≠ A := by
      intro heq
      have := hb'.1
      rw [heq] at this
      cases this
    by_cases hba : b = a
    · subst b
      have hxx : τ x = C (σ a) := by
        have hh := (StageRotation.up_new s.nextEdge σ a A).1
        simpa only [hne, ↓reduceIte] using hh
      have hfirst : RotationArc τ (stageOutgoing t) (C a) x := by
        rw [← hnext]
        exact arc_one τ _ _ (hmark a hb) (hnext ▸ hx)
      have hsecond : RotationArc τ (stageOutgoing t) x (C (σ a)) := by
        rw [← hxx]
        exact arc_one τ _ _ hx (hxx ▸ hmark (σ a) hb')
      exact hfirst.trans hsecond
    · have hbb : τ (C b) = C (σ b) := by
        rw [StageRotation.up_old]
        simp only [hba, hne, ↓reduceIte]
        rfl
      rw [← hbb]
      exact arc_one τ _ _ (hmark b hb) (hbb ▸ hmark (σ b) hb')
  apply insertion_invariant C (fun d e h =>
    Sum.inl_injective ((StageRotation.allocation s.nextEdge 2).injective h)) a x hi ha
    haUL hx hend hex hmark hsplit ?_ hnext harc ?_
  · intro f hf hfUL
    change f ∈ s.UL.dropLast ++ [s.nextEdge] at hfUL
    rcases List.mem_append.mp hfUL with hfold | hfnew
    · have hfo := stageRotation_UL_bound w n f (List.dropLast_subset _ hfold)
      refine Or.inl ⟨⟨f, hfo⟩, List.dropLast_subset _ hfold, ?_, rfl⟩
      intro heq
      have hfa : f = s.active := congrArg (fun d => d.1.val) heq
      have hnd : s.UL.Nodup := by
        rw [kmswStage_UL_eq]
        exact (List.Nodup.filter _ List.nodup_range).map (CutConverse.act_injective w)
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
      change s.UL = xs ++ [s.active] at hxs
      have hnot : s.active ∉ xs := by
        rw [hxs] at hnd
        intro hmem
        exact (List.disjoint_of_nodup_append hnd) hmem (List.mem_singleton_self _)
      have hmem : f ∈ xs := by simpa only [hxs, List.dropLast_concat] using hfold
      exact hnot (hfa ▸ hmem)
    · have hfe := List.mem_singleton.mp hfnew
      exact Or.inr (Prod.ext (Fin.ext (by dsimp [x, StageRotation.allocation]; exact hfe)) rfl)
  · have ht : kmswStage w (n + 1) = t := by
      simp only [kmswStage, kmswStep, hc]
      rfl
    exact ht ▸ stageOutgoing_frontier_empty w (n + 1)

/-- Up insertion preserves the outgoing interval and the UL sewing corner -/
theorem stageOutgoingInvariant_up (w : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (w n) = .up)
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    StageOutgoingInvariant (kmswStage w (n + 1)) (stageRot w (n + 1)) := by
  apply invariant_transport (by simp only [kmswStage, kmswStep, hc]) _ _ ?_
    (up_invariant w n hc hi)
  exact StageRotation.step_up _ _ _ _ _ hc

private theorem left_existing_invariant (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : kmswCodeStep (w n) = .left)
    (hl : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    let s := kmswStage w n
    let he := stageRotation_UL_bound w n e (List.dropLast_subset _
      (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
    let t := { s.addEdge (s.west e) (s.east s.active) true with
      active := s.nextEdge, triangles := s.triangles ++ [(s.active, s.nextEdge, e)],
      UL := es.reverse ++ [s.nextEdge] }
    StageOutgoingInvariant t (StageRotation.leftExisting s.nextEdge (stageRot w n)
      (⟨e, he⟩, false) (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true)) := by
  let s := kmswStage w n
  have heUL : e ∈ s.UL := List.dropLast_subset _
    (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self))
  have he := stageRotation_UL_bound w n e heUL
  let t : State := { s.addEdge (s.west e) (s.east s.active) true with
    active := s.nextEdge, triangles := s.triangles ++ [(s.active, s.nextEdge, e)],
    UL := es.reverse ++ [s.nextEdge] }
  let σ := stageRot w n
  let a : StageDart s.nextEdge := (⟨e, he⟩, false)
  let A : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true)
  let τ := StageRotation.leftExisting s.nextEdge σ a A
  let C : StageDart s.nextEdge → StageDart t.nextEdge :=
    fun d => StageRotation.allocation s.nextEdge 1 (.inl d)
  let x : StageDart t.nextEdge := StageRotation.allocation s.nextEdge 1 (.inr (0, false))
  change StageOutgoingInvariant t τ
  have ha : stageOutgoing s a := ⟨rfl, (kmswStage_status w n).2.1 _ heUL⟩
  have hx : stageOutgoing t x := by
    constructor
    · rfl
    · simp [t, x, StageRotation.allocation, State.addEdge]
  have hmark (d : StageDart s.nextEdge) (hd : stageOutgoing s d) :
      stageOutgoing t (C d) := by
    have h0 : d.1.val ≠ s.nextEdge := by omega
    refine ⟨hd.1, ?_⟩
    change (if d.1.val = s.nextEdge then true else s.present d.1.val) = true
    simpa only [h0, ↓reduceIte] using hd.2
  have hsplit (d : StageDart t.nextEdge) (hd : stageOutgoing t d) :
      (∃ b, d = C b ∧ stageOutgoing s b) ∨ d = x := by
    by_cases hold : d.1.val < s.nextEdge
    · let b : StageDart s.nextEdge := (⟨d.1.val, hold⟩, d.2)
      have h0 : d.1.val ≠ s.nextEdge := by omega
      exact Or.inl ⟨b, rfl, hd.1, by simpa only [t,
        State.addEdge, h0, ↓reduceIte] using hd.2⟩
    · have hb := d.1.isLt
      change d.1.val < s.nextEdge + 1 at hb
      exact Or.inr (Prod.ext (Fin.ext (by dsimp [x, StageRotation.allocation]; omega)) hd.1)
  have hend (d : StageDart s.nextEdge) : stageEndpoint t (C d) = stageEndpoint s d := by
    have h0 : d.1.val ≠ s.nextEdge := by omega
    rcases d with ⟨de, db⟩
    simp only [stageEndpoint, t, C, StageRotation.allocation_old,
      State.addEdge, h0, ↓reduceIte]
  have hex : stageEndpoint t x = stageEndpoint s a := by
    simp [stageEndpoint, t, x, a, StageRotation.allocation, State.addEdge]
  have hnext : τ (C a) = x := by
    rw [StageRotation.leftExisting_old]
    simp only [↓reduceIte]
    rfl
  have harc (d f : StageDart s.nextEdge)
      (h : RotationArc σ (stageOutgoing s) d f) :
      RotationArc τ (stageOutgoing t) (C d) (C f) := by
    apply h.map C hmark
    intro b hb hb'
    have hne : σ b ≠ A := by
      intro heq
      have := hb'.1
      rw [heq] at this
      cases this
    by_cases hba : b = a
    · subst b
      have hxx : τ x = C (σ a) := by
        have hh := (StageRotation.leftExisting_new s.nextEdge σ a A).1
        simpa only [hne, ↓reduceIte] using hh
      have hfirst : RotationArc τ (stageOutgoing t) (C a) x := by
        rw [← hnext]
        exact arc_one τ _ _ (hmark a hb) (hnext ▸ hx)
      have hsecond : RotationArc τ (stageOutgoing t) x (C (σ a)) := by
        rw [← hxx]
        exact arc_one τ _ _ hx (hxx ▸ hmark (σ a) hb')
      exact hfirst.trans hsecond
    · have hbb : τ (C b) = C (σ b) := by
        rw [StageRotation.leftExisting_old]
        simp only [hba, hne, ↓reduceIte]
        rfl
      rw [← hbb]
      exact arc_one τ _ _ (hmark b hb) (hbb ▸ hmark (σ b) hb')
  apply insertion_invariant C (fun d f h =>
    Sum.inl_injective ((StageRotation.allocation s.nextEdge 1).injective h)) a x hi ha
    heUL hx hend hex hmark hsplit ?_ hnext harc ?_
  · intro f hf hfUL
    change f ∈ es.reverse ++ [s.nextEdge] at hfUL
    rcases List.mem_append.mp hfUL with hfold | hfnew
    · have hfes : f ∈ es := List.mem_reverse.mp hfold
      have hfoUL : f ∈ s.UL := List.dropLast_subset _ (List.mem_reverse.mp
        (by rw [hl]; exact List.mem_cons_of_mem _ hfes))
      have hfo := stageRotation_UL_bound w n f hfoUL
      refine Or.inl ⟨⟨f, hfo⟩, hfoUL, ?_, rfl⟩
      intro heq
      have hfe : f = e := congrArg (fun d => d.1.val) heq
      have hnd : s.UL.Nodup := by
        rw [kmswStage_UL_eq]
        exact (List.Nodup.filter _ List.nodup_range).map (CutConverse.act_injective w)
      have hdnd := List.nodup_reverse.mpr (hnd.sublist (List.dropLast_sublist _))
      change s.UL.dropLast.reverse = e :: es at hl
      rw [hl] at hdnd
      exact (List.nodup_cons.mp hdnd).1 (hfe ▸ hfes)
    · have hfe := List.mem_singleton.mp hfnew
      exact Or.inr (Prod.ext (Fin.ext (by dsimp [x, StageRotation.allocation]; exact hfe)) rfl)
  · have ht : kmswStage w (n + 1) = t := by
      simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hl]
      rfl
    exact ht ▸ stageOutgoing_frontier_empty w (n + 1)

/-- Left insertion at the nearest existing UL predecessor preserves the
outgoing interval and sewing corners (`def-kmsw`, -/
theorem stageOutgoingInvariant_left_existing (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hc : kmswCodeStep (w n) = .left)
    (hl : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    StageOutgoingInvariant (kmswStage w (n + 1)) (stageRot w (n + 1)) := by
  apply invariant_transport (by simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hl])
    _ _ ?_ (left_existing_invariant w n e es hc hl hi)
  exact StageRotation.step_leftExisting _ _ _ _ _ hc e es hl

/-- Horizontal nonnegativity excludes only the fresh-left case; the other
four branches establish the all-stage invariant for `def-kmsw` -/
theorem stageOutgoingInvariant_of_L_nonneg (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (n : ℕ) :
    StageOutgoingInvariant (kmswStage w n) (stageRot w n) := by
  induction n with
  | zero => exact stageOutgoingInvariant_zero w
  | succ n hi =>
    cases hc : kmswCodeStep (w n) with
    | up => exact stageOutgoingInvariant_up w n hc hi
    | down =>
      cases hr : (kmswStage w n).UR with
      | nil => exact stageOutgoingInvariant_pendant w n hc hr hi
      | cons e es => exact stageOutgoingInvariant_activation w n e es hc hr hi
    | left =>
      cases hl : (kmswStage w n).UL.dropLast.reverse with
      | nil => exact (kmswStage_left_not_fresh_of_L_nonneg w hL n hc hl).elim
      | cons e es => exact stageOutgoingInvariant_left_existing w n e es hc hl hi

/-- At a complete vertex the outgoing interval transfers to the limiting -/
theorem kmswInfRot_outgoing_interval_at_complete (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (n : ℕ) (d e : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) d))
    (hv : stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) e)
    (hd : stageOutgoing (kmswStage w n) d) (he : stageOutgoing (kmswStage w n) e) :
    RotationArc (kmswInfRot w hfin)
      (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1)
      (d.1.val, d.2) (e.1.val, e.2) ∨
    RotationArc (kmswInfRot w hfin)
      (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1)
      (e.1.val, e.2) (d.1.val, d.2) := by
  rcases (stageOutgoingInvariant_of_L_nonneg w hL n).1 d e hv hd he with h | h
  · exact Or.inl (h.to_kmswInfRot w hfin n d e hc)
  · exact Or.inr (h.to_kmswInfRot w hfin n e d (hv ▸ hc))

private theorem exists_complete_stage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v : ℕ) : ∃ N, kmswVertexComplete w N v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hmem : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)} :=
    ⟨e, kmsw_edge_allocated_by_self w e, he⟩
  exact (hB hmem).trans_lt (kmsw_edge_allocated_by_self w B)

/-- Present outgoing edge IDs at a common vertex form a single marked
interval of the limiting rotation (`remark-kmsw-infinite`,
condition used to exclude the fresh-left branch. -/
theorem kmswInfRot_outgoing_interval (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (e f : ℕ) (hv : edgeWest w e = edgeWest w f)
    (he : EdgePresent w e) (hf : EdgePresent w f) :
    RotationArc (kmswInfRot w hfin)
      (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1) (e, false) (f, false) ∨
    RotationArc (kmswInfRot w hfin)
      (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1) (f, false) (e, false) := by
  obtain ⟨N, hN⟩ := exists_complete_stage w hfin (edgeWest w e)
  obtain ⟨Ne, hNe⟩ := he.eventually_present
  obtain ⟨Nf, hNf⟩ := hf.eventually_present
  let n := max N (max Ne Nf)
  have hNn : N ≤ n := le_max_left _ _
  have hNen : Ne ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hNfn : Nf ≤ n := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨heb, hep⟩ := hNe n hNen
  obtain ⟨hfb, hfp⟩ := hNf n hNfn
  have hew := (edge_endpoints_eq w heb).1
  have hfw := (edge_endpoints_eq w hfb).1
  apply kmswInfRot_outgoing_interval_at_complete w hL hfin n
    (⟨e, heb⟩, false) (⟨f, hfb⟩, false) ?_ ?_ ⟨rfl, hep⟩ ⟨rfl, hfp⟩
  · change kmswVertexComplete w n ((kmswStage w n).west e)
    rw [hew]
    intro g hg
    exact (hN g hg).trans_le (kmswStage_nextEdge_mono w hNn)
  · change (kmswStage w n).west e = (kmswStage w n).west f
    exact hew.trans (hv.trans hfw.symm)

/-- Almost surely the Pitman-code realization has finite geometric incidence
and its present outgoing darts form one interval at every vertex. This
discharges the internal horizontal condition using Pitman nonnegativity -/
theorem pitmanCodes_ae_outgoing_interval :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∀ e f : ℕ, edgeWest w e = edgeWest w f → EdgePresent w e → EdgePresent w f →
        RotationArc (kmswInfRot w hfin)
          (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1) (e, false) (f, false) ∨
        RotationArc (kmswInfRot w hfin)
          (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1) (f, false) (e, false) := by
  filter_upwards [pitmanCodes_ae_finite_incident_edges] with ω hfin
  let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
  have hL : ∀ j, 0 ≤ L w j := by
    intro j
    rw [RandomWalk.kmsw_L_eq]
    exact RandomWalk.integrateCodes_pitmanCode_fst_nonneg _ j
  exact ⟨hfin, kmswInfRot_outgoing_interval w hL hfin⟩

end DirectedDistances.KMSW
