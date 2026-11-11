module

public import DirectedDistances.KMSW.OutgoingIntervalSplices
import DirectedDistances.KMSW.LocalFinitenessIID

/-! # Fresh-left outgoing intervals -/

public section
namespace DirectedDistances.KMSW

private theorem arc_one {D : Type*} (σ : Equiv.Perm D) (p : D → Prop)
    (d : D) (hd : p d) (he : p (σ d)) : RotationArc σ p d (σ d) := by
  refine ⟨1, by simp only [pow_one], ?_⟩
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact hd
  · simpa only [pow_one] using he

private theorem common_end {D : Type*} {σ : Equiv.Perm D} {p : D → Prop}
    {d e a : D} (h : RotationArc σ p d a) (h' : RotationArc σ p e a) :
    RotationArc σ p d e ∨ RotationArc σ p e d := by
  obtain ⟨k, hk, hp⟩ := h
  obtain ⟨l, hl, hq⟩ := h'
  have suffix {b c : D} {i j : ℕ} (hij : i ≤ j)
      (hb : (σ ^ i) b = a) (hc : (σ ^ j) c = a)
      (hm : ∀ t, t ≤ j → p ((σ ^ t) c)) : RotationArc σ p c b := by
    refine ⟨j - i, ?_, fun t ht => hm t (by omega)⟩
    apply (σ ^ i).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, show i + (j - i) = j by omega, hc, hb]
  rcases le_total k l with hkl | hlk
  · exact Or.inr (suffix hkl hk hl hq)
  · exact Or.inl (suffix hlk hl hk hp)

private theorem map_stopping {D E : Type*} {σ : Equiv.Perm D} {τ : Equiv.Perm E}
    {p : D → Prop} {q : E → Prop} (C : D → E) (a : D)
    (hmark : ∀ d, p d → q (C d))
    (hstep : ∀ d, d ≠ a → p d → p (σ d) → τ (C d) = C (σ d))
    {d : D} (h : RotationArc σ p d a) : RotationArc τ q (C d) (C a) := by
  obtain ⟨k, hk, hp⟩ := h
  induction k generalizing d with
  | zero =>
    have hda : d = a := hk
    subst d
    exact RotationArc.refl _ _ _ (hmark a (hp 0 (by omega)))
  | succ k ih =>
    by_cases hda : d = a
    · subst d
      exact RotationArc.refl _ _ _ (hmark a (hp 0 (by omega)))
    · have hd := hp 0 (by omega)
      have hn : p (σ d) := by simpa only [pow_one] using hp 1 (by omega)
      have ht : RotationArc τ q (C (σ d)) (C a) := ih
        (by simpa only [pow_succ, Equiv.Perm.mul_apply] using hk)
        (fun i hi => by simpa only [pow_succ, Equiv.Perm.mul_apply] using hp (i + 1) (by omega))
      have hs := hstep d hda hd hn
      have hfirst := arc_one τ q (C d) (hmark d hd) (hs ▸ hmark (σ d) hn)
      rw [hs] at hfirst
      exact hfirst.trans ht

private theorem invariant_transport {s t : State} (h : s = t)
    (σ : Equiv.Perm (StageDart s.nextEdge)) (τ : Equiv.Perm (StageDart t.nextEdge))
    (hr : StageRotation.resize (congrArg State.nextEdge h) σ = τ)
    (hi : StageOutgoingInvariant t τ) : StageOutgoingInvariant s σ := by
  cases h
  cases hr
  exact hi

private theorem left_fresh_invariant (w : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (w n) = .left)
    (hl : (kmswStage w n).UL.dropLast.reverse = [])
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    let s := kmswStage w n
    let t := { (s.addEdge s.nextVertex (s.east s.active) true).addEdge
        s.nextVertex (s.west s.active) false with
      nextVertex := s.nextVertex + 1, active := s.nextEdge,
      triangles := s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)],
      UL := [s.nextEdge], LL := (s.nextEdge + 1) :: s.LL }
    StageOutgoingInvariant t (StageRotation.leftFresh s.nextEdge (stageRot w n)
      (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
      (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true)) := by
  let s := kmswStage w n
  let t : State := { (s.addEdge s.nextVertex (s.east s.active) true).addEdge
        s.nextVertex (s.west s.active) false with
      nextVertex := s.nextVertex + 1, active := s.nextEdge,
      triangles := s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)],
      UL := [s.nextEdge], LL := (s.nextEdge + 1) :: s.LL }
  let σ := stageRot w n
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
  let A : StageDart s.nextEdge := (a.1, true)
  let τ := StageRotation.leftFresh s.nextEdge σ a A
  let C : StageDart s.nextEdge → StageDart t.nextEdge :=
    fun d => StageRotation.allocation s.nextEdge 2 (.inl d)
  let x : StageDart t.nextEdge := StageRotation.allocation s.nextEdge 2 (.inr (0, false))
  change StageOutgoingInvariant t τ
  have hmark (d : StageDart s.nextEdge) (hd : stageOutgoing s d) :
      stageOutgoing t (C d) := by
    have h0 : d.1.val ≠ s.nextEdge := by omega
    have h1 : d.1.val ≠ s.nextEdge + 1 := by omega
    refine ⟨hd.1, ?_⟩
    change (if d.1.val = s.nextEdge + 1 then false else
      if d.1.val = s.nextEdge then true else s.present d.1.val) = true
    simpa only [h0, h1, ↓reduceIte] using hd.2
  have hx : stageOutgoing t x := by
    constructor
    · rfl
    · simp [t, x, StageRotation.allocation, State.addEdge]
  have hsplit (d : StageDart t.nextEdge) (hd : stageOutgoing t d) :
      (∃ b, d = C b ∧ stageOutgoing s b) ∨ d = x := by
    by_cases hold : d.1.val < s.nextEdge
    · let b : StageDart s.nextEdge := (⟨d.1.val, hold⟩, d.2)
      have h0 : d.1.val ≠ s.nextEdge := by omega
      have h1 : d.1.val ≠ s.nextEdge + 1 := by omega
      exact Or.inl ⟨b, rfl, hd.1, by simpa only [t, State.addEdge,
        h0, h1, ↓reduceIte] using hd.2⟩
    · have hb := d.1.isLt
      change d.1.val < s.nextEdge + 1 + 1 at hb
      have hn : d.1.val ≠ s.nextEdge + 1 := by
        intro hn
        have hp := hd.2
        simp only [t, State.addEdge, hn, ↓reduceIte, Bool.false_eq_true] at hp
      exact Or.inr (Prod.ext (Fin.ext (by dsimp [x, StageRotation.allocation]; omega)) hd.1)
  have hend (d : StageDart s.nextEdge) : stageEndpoint t (C d) = stageEndpoint s d := by
    have h0 : d.1.val ≠ s.nextEdge := by omega
    have h1 : d.1.val ≠ s.nextEdge + 1 := by omega
    rcases d with ⟨de, db⟩
    simp only [stageEndpoint, t, C, StageRotation.allocation_old,
      State.addEdge, h0, h1, ↓reduceIte]
  have hex : stageEndpoint t x = s.nextVertex := by
    simp [stageEndpoint, t, x, StageRotation.allocation, State.addEdge]
  have hne (b : StageDart s.nextEdge) : stageEndpoint t (C b) ≠ stageEndpoint t x := by
    rw [hend, hex]
    exact Nat.ne_of_lt (stageEndpoint_lt_nextVertex w n b)
  have hstep (b : StageDart s.nextEdge) (hba : b ≠ a)
      (_hb : stageOutgoing s b) (hn : stageOutgoing s (σ b)) : τ (C b) = C (σ b) := by
    have hnA : σ b ≠ A := by
      intro heq
      have hh := hn.1
      rw [heq] at hh
      cases hh
    rw [StageRotation.leftFresh_old]
    simp only [hba, hnA, ↓reduceIte]
    rfl
  have hpow (b : StageDart s.nextEdge) (j : ℕ) :
      stageEndpoint s ((σ ^ j) b) = stageEndpoint s b := by
    apply ((stageRot_sameCycle_iff_endpoint_eq w n b _).1 ?_).symm
    exact ⟨(j : ℤ), by simp [σ]⟩
  have harc_away (b c : StageDart s.nextEdge)
      (hb : stageEndpoint s b ≠ stageEndpoint s a)
      (h : RotationArc σ (stageOutgoing s) b c) :
      RotationArc τ (stageOutgoing t) (C b) (C c) := by
    obtain ⟨k, hk, hp⟩ := h
    have hiter : ∀ j, j ≤ k → (τ ^ j) (C b) = C ((σ ^ j) b) := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
        have hjk : j ≤ k := by omega
        rw [pow_succ', Equiv.Perm.mul_apply, ih hjk]
        have hja : (σ ^ j) b ≠ a := by
          intro heq
          exact hb ((hpow b j).symm.trans (congrArg (stageEndpoint s) heq))
        rw [hstep _ hja (hp j hjk)
          (by simpa only [pow_succ', Equiv.Perm.mul_apply] using hp (j + 1) hj)]
        simp only [pow_succ', Equiv.Perm.mul_apply]
        rfl
    refine ⟨k, (hiter k (le_refl k)).trans (congrArg C hk), ?_⟩
    intro j hj
    rw [hiter j hj]
    exact hmark _ (hp j hj)
  have haUL : s.active ∈ s.UL := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    rw [hxs]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hto (b : StageDart s.nextEdge) (hb : stageOutgoing s b)
      (hv : stageEndpoint s b = stageEndpoint s a) :
      RotationArc τ (stageOutgoing t) (C b) (C a) := by
    apply map_stopping C a hmark hstep
    exact hi.2.1 s.active a.1.isLt haUL b hv hb
  have honly (d : StageDart t.nextEdge) (hd : stageOutgoing t d)
      (hv : stageEndpoint t d = stageEndpoint t x) : d = x := by
    rcases hsplit d hd with ⟨b, rfl, _⟩ | h
    · exact (hne b hv).elim
    · exact h
  refine ⟨?_, ?_, ?_⟩
  · intro d e hv hd he
    rcases hsplit d hd with ⟨b, rfl, hb⟩ | rfl
    · rcases hsplit e he with ⟨c, rfl, hcc⟩ | rfl
      · have hv' : stageEndpoint s b = stageEndpoint s c := by simpa only [hend] using hv
        by_cases hba : stageEndpoint s b = stageEndpoint s a
        · exact common_end (hto b hb hba) (hto c hcc (hv'.symm.trans hba))
        · exact (hi.1 b c hv' hb hcc).imp (harc_away b c hba)
            (harc_away c b (fun h => hba (hv'.trans h)))
      · exact (hne b hv).elim
    · have heq := honly e he hv.symm
      subst e
      exact Or.inl (RotationArc.refl _ _ _ hx)
  · intro f hf hfUL d hv hd
    have hfe : f = s.nextEdge := List.mem_singleton.mp hfUL
    have hfx : (⟨f, hf⟩, false) = x := Prod.ext (Fin.ext hfe) rfl
    have hdx : d = x := honly d hd (by rw [hex]; simpa [t, State.addEdge, hfe] using hv)
    rw [hdx, hfx]
    exact RotationArc.refl _ _ _ hx
  · have ht : kmswStage w (n + 1) = t := by
      simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hl]
      rfl
    exact ht ▸ stageOutgoing_frontier_empty w (n + 1)

/-- Fresh-left sewing preserves the outgoing interval and UL corners -/
theorem stageOutgoingInvariant_left_fresh (w : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (w n) = .left)
    (hl : (kmswStage w n).UL.dropLast.reverse = [])
    (hi : StageOutgoingInvariant (kmswStage w n) (stageRot w n)) :
    StageOutgoingInvariant (kmswStage w (n + 1)) (stageRot w (n + 1)) := by
  apply invariant_transport (by simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hl])
    _ _ ?_ (left_fresh_invariant w n hc hl hi)
  exact StageRotation.step_leftFresh _ _ _ _ _ hc hl

/-- Every code has the finite-stage outgoing interval and UL sewing corners -/
theorem stageOutgoingInvariant_all (w : ℕ → Fin 3) (n : ℕ) :
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
      | nil => exact stageOutgoingInvariant_left_fresh w n hc hl hi
      | cons e es => exact stageOutgoingInvariant_left_existing w n e es hc hl hi

private theorem outgoing_at_complete (w : ℕ → Fin 3)
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
  rcases (stageOutgoingInvariant_all w n).1 d e hv hd he with h | h
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

/-- For every locally finite code, present outgoing darts at a common vertex
form one marked interval of the limiting rotation (`remark-kmsw-infinite`, -/
theorem kmswInfRot_outgoing_interval_all (w : ℕ → Fin 3)
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
  apply outgoing_at_complete w hfin n
    (⟨e, heb⟩, false) (⟨f, hfb⟩, false) ?_ ?_ ⟨rfl, hep⟩ ⟨rfl, hfp⟩
  · change kmswVertexComplete w n ((kmswStage w n).west e)
    rw [hew]
    intro g hg
    exact (hN g hg).trans_le (kmswStage_nextEdge_mono w hNn)
  · change (kmswStage w n).west e = (kmswStage w n).west f
    exact hew.trans (hv.trans hfw.symm)

/-- Almost surely every vertex of the iid-code map has finite geometric
incidence and its present outgoing darts form one interval. This uses the -/
theorem iidCodes_ae_outgoing_interval :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∀ e f : ℕ, edgeWest w e = edgeWest w f → EdgePresent w e → EdgePresent w f →
        RotationArc (kmswInfRot w hfin)
          (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1) (e, false) (f, false) ∨
        RotationArc (kmswInfRot w hfin)
          (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1) (f, false) (e, false) := by
  filter_upwards [iidCodes_ae_finite_incident_edges] with ω hfin
  exact ⟨hfin, kmswInfRot_outgoing_interval_all (fun i => ω (i + 1)) hfin⟩

end DirectedDistances.KMSW
