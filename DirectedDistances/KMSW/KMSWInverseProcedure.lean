module

public import DirectedDistances.KMSW.KMSWInversePeel
import DirectedDistances.KMSW.OutgoingInterval

/-! Supporting lemmas for paper labels `def-kmsw`, `defn:KMSW-inv` (see CORRESPONDENCE.md). -/

/-! # Structural signals for inverse KMSW steps

The source inverse (`defn:KMSW-inv`, lines 194–202) uses contour heights.
Here all signals use geometric darts, rather than allocation labels.

`lastCode_of_iso` proves last-letter recovery at every positive stage.
`peelCode` is an exclusive, isomorphism-invariant classifier. The previous
active dart is recovered for left, up, and pendant down steps. No additional
boundary labelling is needed for these results.

The predecessor-map isomorphism is not constructed here. Its remaining
obligation is to restrict the dart equivalence to the retained darts, undo
the rotation splice or activation, and verify the predecessor outer-face
orbit. Thus general prefix injectivity is not asserted; only its one-step
base case is proved. These are helper results, not a bijection theorem. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- A present incoming edge meets the root tail vertex (`def-kmsw`, -/
@[expose] def RootedDirectedMapWithMissing.incomingAtRootTail
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) : Prop :=
  ∃ d, ¬ M.map.missing d ∧ ¬ M.map.tail d ∧ M.map.rot.SameCycle M.root d

/-- The root is the only outgoing edge at its tail vertex (`def-kmsw`, -/
@[expose] def RootedDirectedMapWithMissing.uniqueOutgoingAtRootTail
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) : Prop :=
  ∀ d, M.map.tail d → M.map.rot.SameCycle M.root d → d = M.root

/-- The next dart counterclockwise after the root head is missing -/
@[expose] def RootedDirectedMapWithMissing.missingAfterRootHead
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) : Prop :=
  M.map.missing (M.map.rot (M.map.toCombinatorialMap.edgeInv M.root))

private theorem iso_rot_pow
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (k : ℕ) (d : D) :
    h.dartEquiv ((M.map.rot ^ k) d) = (N.map.rot ^ k) (h.dartEquiv d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [h.rot_comm, ih]

/-- Rooted isomorphisms preserve vertices as rotation cycles. -/
theorem RootedDirectedMapIso.sameVertex_iff
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (a b : D) :
    M.map.rot.SameCycle a b ↔
      N.map.rot.SameCycle (h.dartEquiv a) (h.dartEquiv b) := by
  constructor
  · rintro hab
    obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
    exact ⟨k, (iso_rot_pow h k a).symm.trans (congrArg h.dartEquiv hk)⟩
  · intro hab
    obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
    have heq : (M.map.rot ^ k) a = b := by
      apply h.dartEquiv.injective
      rw [iso_rot_pow h k a]
      exact hk
    exact ⟨k, heq⟩

/-- Incoming incidence at the root tail is independent of dart labels. -/
theorem RootedDirectedMapIso.incomingAtRootTail_iff
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) :
    M.incomingAtRootTail ↔ N.incomingAtRootTail := by
  constructor
  · rintro ⟨d, hp, ht, hv⟩
    refine ⟨h.dartEquiv d, (h.present_iff d).mp hp,
      fun hb => ht ((h.tail_iff d).mpr hb), ?_⟩
    simpa only [h.root_comm] using (h.sameVertex_iff M.root d).mp hv
  · rintro ⟨d, hp, ht, hv⟩
    obtain ⟨d, rfl⟩ := h.dartEquiv.surjective d
    refine ⟨d, (h.present_iff d).mpr hp,
      fun hb => ht ((h.tail_iff d).mp hb), ?_⟩
    apply (h.sameVertex_iff M.root d).mpr
    simpa only [h.root_comm] using hv

/-- Uniqueness of the outgoing edge at the root tail is intrinsic. -/
theorem RootedDirectedMapIso.uniqueOutgoingAtRootTail_iff
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) :
    M.uniqueOutgoingAtRootTail ↔ N.uniqueOutgoingAtRootTail := by
  constructor
  · intro hu d ht hv
    obtain ⟨d, rfl⟩ := h.dartEquiv.surjective d
    have hv' : M.map.rot.SameCycle M.root d :=
      (h.sameVertex_iff M.root d).mpr (by simpa only [h.root_comm] using hv)
    rw [hu d ((h.tail_iff d).mpr ht) hv', h.root_comm]
  · intro hu d ht hv
    apply h.dartEquiv.injective
    rw [h.root_comm]
    apply hu _ ((h.tail_iff d).mp ht)
    simpa only [h.root_comm] using (h.sameVertex_iff M.root d).mp hv

/-- The missing successor of the root head is preserved by rooted rotation
and edge-flip isomorphisms. -/
theorem RootedDirectedMapIso.missingAfterRootHead_iff
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) :
    M.missingAfterRootHead ↔ N.missingAfterRootHead := by
  have he := h.missing_iff (M.map.rot (M.map.toCombinatorialMap.edgeInv M.root))
  rw [h.rot_comm, h.edgeFlip_comm, h.root_comm] at he
  exact he



theorem kmswRootedStage_incomingAtRootTail_iff (w : ℕ → Fin 3) (n : ℕ) :
    (kmswRootedStage w n).incomingAtRootTail ↔
      ∃ e < (kmswStage w n).nextEdge, (kmswStage w n).present e = true ∧
        (kmswStage w n).east e = (kmswStage w n).west (kmswStage w n).active := by
  constructor
  · rintro ⟨⟨e, b⟩, hp, ht, hv⟩
    change ¬ (kmswStage w n).present e.val = false at hp
    change ¬ ((kmswStage w n).present e.val = true ∧ b = false) at ht
    have hp' : (kmswStage w n).present e.val = true := by
      cases hh : (kmswStage w n).present e.val <;> simp_all
    have hb : b = true := by cases b <;> simp_all
    have he := (stageRot_sameCycle_iff_endpoint_eq w n
      (kmswRootedStage w n).root (e, b)).mp hv
    refine ⟨e.val, e.isLt, hp', ?_⟩
    simpa only [stageEndpoint, kmswRootedStage, hb, Bool.false_eq_true,
      ↓reduceIte] using he.symm
  · rintro ⟨e, he, hp, hv⟩
    let d : StageDart (kmswStage w n).nextEdge := (⟨e, he⟩, true)
    refine ⟨d, ?_, ?_, ?_⟩
    · change ¬ (kmswStage w n).present e = false
      rw [hp]
      decide
    · change ¬ ((kmswStage w n).present e = true ∧ true = false)
      simp only [Bool.true_eq_false, and_false, not_false_eq_true]
    · apply (stageRot_sameCycle_iff_endpoint_eq w n _ d).mpr
      simpa only [stageEndpoint, kmswRootedStage, d, Bool.false_eq_true,
        ↓reduceIte] using hv.symm

/-- The unique outgoing signal in endpoint coordinates (`def-kmsw`, -/
theorem kmswRootedStage_uniqueOutgoingAtRootTail_iff (w : ℕ → Fin 3) (n : ℕ) :
    (kmswRootedStage w n).uniqueOutgoingAtRootTail ↔
      ∀ e < (kmswStage w n).nextEdge, (kmswStage w n).present e = true →
        (kmswStage w n).west e = (kmswStage w n).west (kmswStage w n).active →
        e = (kmswStage w n).active := by
  constructor
  · intro hu e he hp hv
    let d : StageDart (kmswStage w n).nextEdge := (⟨e, he⟩, false)
    have hd : (kmswRootedStage w n).map.tail d := ⟨hp, rfl⟩
    have hc : (kmswRootedStage w n).map.rot.SameCycle
        (kmswRootedStage w n).root d := by
      apply (stageRot_sameCycle_iff_endpoint_eq w n _ d).mpr
      simpa only [stageEndpoint, kmswRootedStage, d, Bool.false_eq_true,
        ↓reduceIte] using hv.symm
    exact congrArg (fun d => d.1.val) (hu d hd hc)
  · intro hu d ht hv
    change (kmswStage w n).present d.1.val = true ∧ d.2 = false at ht
    have he := (stageRot_sameCycle_iff_endpoint_eq w n
      (kmswRootedStage w n).root d).mp hv
    have hw : (kmswStage w n).west d.1.val =
        (kmswStage w n).west (kmswStage w n).active := by
      simpa only [stageEndpoint, kmswRootedStage, ht.2, Bool.false_eq_true,
        ↓reduceIte] using he.symm
    exact Prod.ext (Fin.ext (hu d.1.val d.1.isLt ht.1 hw)) ht.2

/-- A down step leaves exactly one outgoing edge at the new root tail -/
theorem kmswRootedStage_down_uniqueOutgoingAtRootTail
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2) :
    (kmswRootedStage w (n + 1)).uniqueOutgoingAtRootTail := by
  have hstep : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  apply (kmswRootedStage_uniqueOutgoingAtRootTail_iff w (n + 1)).mpr
  intro f hf hp hv
  cases hr : (kmswStage w n).UR with
  | nil =>
    have hv' : (kmswStage w (n + 1)).west f =
        (kmswStage w n).east (kmswStage w n).active := by
      simpa only [kmswStage, kmswStep, hstep, kmswStepOfStep, hr,
        State.addEdge, ↓reduceIte] using hv
    have he := stageOutgoing_pendant_unique w n hstep hr f hf hp hv'
    simpa only [kmswStage, kmswStep, hstep, kmswStepOfStep, hr, State.addEdge] using he
  | cons e es =>
    have hv' : (kmswStage w (n + 1)).west f = (kmswStage w n).west e := by
      simpa only [kmswStage, kmswStep, hstep, kmswStepOfStep, hr] using hv
    have he := stageOutgoing_activation_unique w n e es hstep hr f hf hp hv'
    simpa only [kmswStage, kmswStep, hstep, kmswStepOfStep, hr] using he

/-- The previous active edge enters the tail of the new down-step root -/
theorem kmswRootedStage_down_incomingAtRootTail
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2) :
    (kmswRootedStage w (n + 1)).incomingAtRootTail := by
  have hstep : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  let s := kmswStage w n
  have ha : s.active < s.nextEdge := act_lt_nextEdge w (le_refl n)
  have hp : s.present s.active = true := (kmswRootedStage w n).root_tail.1
  have hbound : s.active < (kmswStage w (n + 1)).nextEdge :=
    ha.trans_le (kmswStage_nextEdge_mono w (Nat.le_succ n))
  apply (kmswRootedStage_incomingAtRootTail_iff w (n + 1)).mpr
  refine ⟨s.active, hbound, ?_, ?_⟩
  · change (kmswStep s (w n)).present s.active = true
    rw [kmswStep_present_existing s (w n) ha]
    split
    · rfl
    · exact hp
  · have hstable := (kmswStage_endpoints_stable w (Nat.le_succ n) ha).2
    rw [hstable]
    cases hr : s.UR with
    | nil =>
      simp only [kmswStage, kmswStep, hstep, kmswStepOfStep, show (kmswStage w n).UR = [] from hr,
        State.addEdge, ↓reduceIte]
      rfl
    | cons e es =>
      have hhead := (kmswStage_boundary_chain_invariant w n).2.2.2.2.2.1 e es hr
      simpa only [kmswStage, kmswStep, hstep, kmswStepOfStep,
        show (kmswStage w n).UR = e :: es from hr] using hhead.symm

/-- An up step retains the old active outgoing edge at the root tail, so
the new active edge is not the unique outgoing edge there (`def-kmsw`, -/
theorem kmswRootedStage_up_not_uniqueOutgoingAtRootTail
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    ¬ (kmswRootedStage w (n + 1)).uniqueOutgoingAtRootTail := by
  intro hu
  have hstep : kmswCodeStep (w n) = .up := by rw [hc]; rfl
  let s := kmswStage w n
  have ha : s.active < s.nextEdge := act_lt_nextEdge w (le_refl n)
  have hp : s.present s.active = true := (kmswRootedStage w n).root_tail.1
  have h0 : s.active ≠ s.nextEdge := by omega
  have h1 : s.active ≠ s.nextEdge + 1 := by omega
  have he := (kmswRootedStage_uniqueOutgoingAtRootTail_iff w (n + 1)).mp hu s.active
    (ha.trans_le (kmswStage_nextEdge_mono w (Nat.le_succ n)))
  have hp' : (kmswStage w (n + 1)).present s.active = true := by
    change (kmswStep s (w n)).present s.active = true
    simpa only [kmswStep, hstep, kmswStepOfStep, State.addEdge, h0, h1,
      ↓reduceIte] using hp
  have hv : (kmswStage w (n + 1)).west s.active =
      (kmswStage w (n + 1)).west (kmswStage w (n + 1)).active := by
    change (kmswStep s (w n)).west s.active = (kmswStep s (w n)).west (kmswStep s (w n)).active
    simp only [kmswStep, hstep, kmswStepOfStep, State.addEdge, h0, h1,
      show s.nextEdge ≠ s.nextEdge + 1 by omega, ↓reduceIte]
  have heq := he hp' hv
  change s.active = (kmswStep s (w n)).active at heq
  simp only [kmswStep, hstep, kmswStepOfStep, State.addEdge] at heq
  omega

/-- A left step cannot have both down-step tail signals (`def-kmsw`, -/
theorem kmswRootedStage_left_not_downTailSignals
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) :
    ¬ ((kmswRootedStage w (n + 1)).incomingAtRootTail ∧
      (kmswRootedStage w (n + 1)).uniqueOutgoingAtRootTail) := by
  rintro ⟨hi, hu⟩
  have hstep : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  let s := kmswStage w n
  have ha : s.active < s.nextEdge := act_lt_nextEdge w (le_refl n)
  cases hl : s.UL.dropLast.reverse with
  | nil =>
    obtain ⟨e, he, hp, hv⟩ :=
      (kmswRootedStage_incomingAtRootTail_iff w (n + 1)).mp hi
    have hEa := (kmswStage_endpoints_lt_nextVertex w n s.active ha).2
    change s.east s.active < s.nextVertex at hEa
    change (kmswStep s (w n)).nextEdge > e at he
    change (kmswStep s (w n)).present e = true at hp
    change (kmswStep s (w n)).east e =
      (kmswStep s (w n)).west (kmswStep s (w n)).active at hv
    simp only [kmswStep, hstep, kmswStepOfStep, hl, State.addEdge] at he hp hv
    by_cases h0 : e = s.nextEdge
    · subst e
      simp only [show s.nextEdge ≠ s.nextEdge + 1 by omega, ↓reduceIte] at hv
      omega
    · by_cases h1 : e = s.nextEdge + 1
      · simp only [h1, ↓reduceIte, Bool.false_eq_true] at hp
      · have hb : e < s.nextEdge := by omega
        have hE := (kmswStage_endpoints_lt_nextVertex w n e hb).2
        change s.east e < s.nextVertex at hE
        simp only [h0, h1, show s.nextEdge ≠ s.nextEdge + 1 by omega,
          ↓reduceIte] at hv
        omega
  | cons e es =>
    have heUL : e ∈ s.UL := List.dropLast_subset _
      (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self))
    have he : e < s.nextEdge := stageRotation_UL_bound w n e heUL
    have hp : s.present e = true := (kmswStage_status w n).2.1 e heUL
    have h0 : e ≠ s.nextEdge := by omega
    have hp' : (kmswStage w (n + 1)).present e = true := by
      change (kmswStep s (w n)).present e = true
      simpa only [kmswStep, hstep, kmswStepOfStep, hl, State.addEdge, h0,
        ↓reduceIte] using hp
    have hv : (kmswStage w (n + 1)).west e =
        (kmswStage w (n + 1)).west (kmswStage w (n + 1)).active := by
      change (kmswStep s (w n)).west e = (kmswStep s (w n)).west (kmswStep s (w n)).active
      simp only [kmswStep, hstep, kmswStepOfStep, hl, State.addEdge, h0, ↓reduceIte]
    have heq := (kmswRootedStage_uniqueOutgoingAtRootTail_iff w (n + 1)).mp hu e
      (he.trans_le (kmswStage_nextEdge_mono w (Nat.le_succ n))) hp' hv
    change e = (kmswStep s (w n)).active at heq
    simp only [kmswStep, hstep, kmswStepOfStep, hl, State.addEdge] at heq
    omega

/-- An intrinsic exclusive characterization of the down code. It uses the
orientation at the root tail, including present versus missing edges -/
theorem kmswRootedStage_down_iff (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswRootedStage w (n + 1)).incomingAtRootTail ∧
      (kmswRootedStage w (n + 1)).uniqueOutgoingAtRootTail) ↔ w n = 2 := by
  constructor
  · intro h
    by_cases h0 : w n = 0
    · exact (kmswRootedStage_left_not_downTailSignals w n h0 h).elim
    · by_cases h1 : w n = 1
      · exact (kmswRootedStage_up_not_uniqueOutgoingAtRootTail w n h1 h.2).elim
      · apply Fin.ext
        have hb := (w n).isLt
        have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
        have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
        change (w n).val = 2
        omega
  · intro hc
    exact ⟨kmswRootedStage_down_incomingAtRootTail w n hc,
      kmswRootedStage_down_uniqueOutgoingAtRootTail w n hc⟩

/-- Rooted isomorphic successor stages agree on whether the last letter is -/
theorem RootedDirectedMapIso.lastCode_down_iff
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) :
    w n = 2 ↔ w' n = 2 := by
  rw [← kmswRootedStage_down_iff, ← kmswRootedStage_down_iff]
  exact and_congr h.incomingAtRootTail_iff h.uniqueOutgoingAtRootTail_iff

private theorem rot_eq_of_resize {k l : ℕ} (hs : k = l)
    (R : Equiv.Perm (StageDart k)) (σ : Equiv.Perm (StageDart l))
    (hR : StageRotation.resize hs R = σ)
    (x y : StageDart k) (x' y' : StageDart l)
    (hx : (x.1.val, x.2) = (x'.1.val, x'.2))
    (hy : (y.1.val, y.2) = (y'.1.val, y'.2)) (ht : σ x' = y') : R x = y := by
  subst hs
  have hx' : x = x' := Prod.ext (Fin.ext (congrArg Prod.fst hx))
    (congrArg (fun p : ℕ × Bool => p.2) hx)
  have hy' : y = y' := Prod.ext (Fin.ext (congrArg Prod.fst hy))
    (congrArg (fun p : ℕ × Bool => p.2) hy)
  change R = σ at hR
  rw [hR, hx', hy']
  exact ht

/-- The up-step head is immediately followed in rotation by its new missing -/
theorem kmswRootedStage_up_missingAfterRootHead
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (kmswRootedStage w (n + 1)).missingAfterRootHead := by
  let s := kmswStage w n
  have hstep : kmswCodeStep (w n) = .up := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
    simp only [kmswStage, kmswStep, hstep, kmswStepOfStep, State.addEdge]
    rfl
  have hd : s.nextEdge + 1 < (kmswStage w (n + 1)).nextEdge := by omega
  let d : StageDart (kmswStage w (n + 1)).nextEdge := (⟨s.nextEdge + 1, hd⟩, false)
  have hr := StageRotation.step_up s (act_lt_nextEdge w (le_refl n))
    (stageRotation_UL_bound w n) (stageRot w n) (w n) hstep
  have ht := (StageRotation.up_new s.nextEdge (stageRot w n)
    (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
    (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true)).2.2.1
  have he : stageRot w (n + 1)
      (edgeFlip _ (kmswRootedStage w (n + 1)).root) = d := by
    apply rot_eq_of_resize hs _ _ hr _ d _ _ ?_ ?_ ht
    · simp only [edgeFlip, kmswRootedStage, kmswStage, kmswStep, hstep,
        kmswStepOfStep, State.addEdge, StageRotation.allocation]
      rfl
    · rfl
  change (kmswStage w (n + 1)).present
    (stageRot w (n + 1) (edgeFlip _ (kmswRootedStage w (n + 1)).root)).1.val = false
  rw [he]
  change (kmswStep s (w n)).present (s.nextEdge + 1) = false
  simp only [kmswStep, hstep, kmswStepOfStep, State.addEdge, ↓reduceIte]

/-- A left-step root head is followed by the old active head, a present -/
theorem kmswRootedStage_left_head_rotation
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) :
    stageRot w (n + 1) (edgeFlip _ (kmswRootedStage w (n + 1)).root) =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (edgeFlip _ (kmswRootedStage w n).root) := by
  let s := kmswStage w n
  have hstep : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  have ha : s.active < s.nextEdge := act_lt_nextEdge w (le_refl n)
  have ha' : s.active < (kmswStage w (n + 1)).nextEdge :=
    ha.trans_le (kmswStage_nextEdge_mono w (Nat.le_succ n))
  let d : StageDart (kmswStage w (n + 1)).nextEdge := (⟨s.active, ha'⟩, true)
  have he : stageRot w (n + 1)
      (edgeFlip _ (kmswRootedStage w (n + 1)).root) = d := by
    cases hl : s.UL.dropLast.reverse with
    | nil =>
      have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
        change (kmswStep s (w n)).nextEdge = _
        simp only [kmswStep, hstep, kmswStepOfStep, hl, State.addEdge]
      have hr := StageRotation.step_leftFresh s ha (stageRotation_UL_bound w n)
        (stageRot w n) (w n) hstep hl
      have ht := (StageRotation.leftFresh_new s.nextEdge (stageRot w n)
        (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true)).2.1
      apply rot_eq_of_resize hs _ _ hr _ d _ _ ?_ ?_ ht
      · change ((kmswStep s (w n)).active, true) = (s.nextEdge + 0, true)
        simp only [kmswStep, hstep, kmswStepOfStep, hl, State.addEdge, Nat.add_zero]
      · rfl
    | cons e es =>
      have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 1 := by
        change (kmswStep s (w n)).nextEdge = _
        simp only [kmswStep, hstep, kmswStepOfStep, hl, State.addEdge]
      have hr := StageRotation.step_leftExisting s ha (stageRotation_UL_bound w n)
        (stageRot w n) (w n) hstep e es hl
      have heBound : e < s.nextEdge := stageRotation_UL_bound w n e
        (List.dropLast_subset _ (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
      have ht := (StageRotation.leftExisting_new s.nextEdge (stageRot w n)
        (⟨e, heBound⟩, false) (⟨s.active, ha⟩, true)).2
      apply rot_eq_of_resize hs _ _ hr _ d _ _ ?_ ?_ ht
      · change ((kmswStep s (w n)).active, true) = (s.nextEdge + 0, true)
        simp only [kmswStep, hstep, kmswStepOfStep, hl, State.addEdge, Nat.add_zero]
      · rfl
  exact he

/-- A left-step root head has a present rotation successor (`def-kmsw`, -/
theorem kmswRootedStage_left_not_missingAfterRootHead
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) :
    ¬ (kmswRootedStage w (n + 1)).missingAfterRootHead := by
  let s := kmswStage w n
  have ha : s.active < s.nextEdge := act_lt_nextEdge w (le_refl n)
  have he := kmswRootedStage_left_head_rotation w n hc
  intro hm
  change (kmswStage w (n + 1)).present
    (stageRot w (n + 1) (edgeFlip _ (kmswRootedStage w (n + 1)).root)).1.val = false at hm
  rw [he] at hm
  have hp : s.present s.active = true := (kmswRootedStage w n).root_tail.1
  change (kmswStep s (w n)).present s.active = false at hm
  rw [kmswStep_present_existing s (w n) ha] at hm
  split at hm
  · cases hm
  · rw [hp] at hm
    cases hm

private theorem code_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  have hb := c.isLt
  have hv : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  rcases hv with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- The last code is determined by the rooted directed map with missing
edges, without retaining allocation labels (`def-kmsw`, -/
theorem lastCode_of_iso (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) : w n = w' n := by
  have hd := RootedDirectedMapIso.lastCode_down_iff w w' n h
  have hm := h.missingAfterRootHead_iff
  rcases code_cases (w n) with h0 | h1 | h2
  · rcases code_cases (w' n) with h0' | h1' | h2'
    · exact h0.trans h0'.symm
    · exact (kmswRootedStage_left_not_missingAfterRootHead w n h0
        (hm.mpr (kmswRootedStage_up_missingAfterRootHead w' n h1'))).elim
    · have he := (hd.mpr h2').symm.trans h0
      have hne : (2 : Fin 3) ≠ 0 := by decide
      exact (hne he).elim
  · rcases code_cases (w' n) with h0' | h1' | h2'
    · exact (kmswRootedStage_left_not_missingAfterRootHead w' n h0'
        (hm.mp (kmswRootedStage_up_missingAfterRootHead w n h1))).elim
    · exact h1.trans h1'.symm
    · have he := (hd.mpr h2').symm.trans h1
      have hne : (2 : Fin 3) ≠ 1 := by decide
      exact (hne he).elim
  · exact h2.trans (hd.mp h2).symm

/-- The candidate previous active dart selected by the three local inverse
does not perform edge deletion and does not assert that an arbitrary rooted
map is a KMSW stage. -/
@[expose] def RootedDirectedMapWithMissing.previousActiveDart
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) (c : Fin 3) : D :=
  if c = 2 then M.map.toCombinatorialMap.edgeInv (M.map.rot M.root)
  else if c = 1 then M.map.rot.symm M.root
  else M.map.toCombinatorialMap.edgeInv
    (M.map.rot (M.map.toCombinatorialMap.edgeInv M.root))

private theorem iso_rot_symm
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (d : D) :
    h.dartEquiv (M.map.rot.symm d) = N.map.rot.symm (h.dartEquiv d) := by
  apply N.map.rot.injective
  rw [← h.rot_comm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Every candidate previous active dart is intrinsic under rooted -/
theorem RootedDirectedMapIso.previousActiveDart_comm
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (c : Fin 3) :
    h.dartEquiv (M.previousActiveDart c) = N.previousActiveDart c := by
  unfold RootedDirectedMapWithMissing.previousActiveDart
  split_ifs with h2 h1
  · rw [h.edgeFlip_comm, h.rot_comm, h.root_comm]
  · rw [iso_rot_symm, h.root_comm]
  · rw [h.edgeFlip_comm, h.rot_comm, h.edgeFlip_comm, h.root_comm]

/-- After a left step the local inverse recovers the previous active dart
as a geometric dart in the larger map (`def-kmsw`, -/
theorem kmswRootedStage_left_previousActiveDart
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) :
    (kmswRootedStage w (n + 1)).previousActiveDart 0 =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root := by
  change edgeFlip _ (stageRot w (n + 1)
    (edgeFlip _ (kmswRootedStage w (n + 1)).root)) = _
  rw [kmswRootedStage_left_head_rotation w n hc]
  rfl

/-- After an up step the previous active dart immediately precedes the -/
theorem kmswRootedStage_up_previousActiveDart
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (kmswRootedStage w (n + 1)).previousActiveDart 1 =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root := by
  let s := kmswStage w n
  have ha : s.active < s.nextEdge := act_lt_nextEdge w (le_refl n)
  have hstep : kmswCodeStep (w n) = .up := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
    change (kmswStep s (w n)).nextEdge = _
    simp only [kmswStep, hstep, kmswStepOfStep, State.addEdge]
  have hr := StageRotation.step_up s ha (stageRotation_UL_bound w n)
    (stageRot w n) (w n) hstep
  have ht := StageRotation.up_old s.nextEdge (stageRot w n)
    (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true) (⟨s.active, ha⟩, false)
  rw [ite_eq_left rfl] at ht
  have he : stageRot w (n + 1)
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root) = (kmswRootedStage w (n + 1)).root := by
    apply rot_eq_of_resize hs _ _ hr _ _ _ _ ?_ ?_ ht
    · rfl
    · change ((kmswStep s (w n)).active, false) = (s.nextEdge + 0, false)
      simp only [kmswStep, hstep, kmswStepOfStep, State.addEdge, Nat.add_zero]
  change (stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root = _
  apply (stageRot w (n + 1)).injective
  rw [Equiv.apply_symm_apply, he]

/-- In the pendant down branch the next rotation dart after the root is -/
theorem kmswRootedStage_down_pendant_previousActiveDart
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) :
    (kmswRootedStage w (n + 1)).previousActiveDart 2 =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root := by
  let s := kmswStage w n
  have hr0 : s.UR = [] := hUR
  have ha : s.active < s.nextEdge := act_lt_nextEdge w (le_refl n)
  have hstep : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 1 := by
    change (kmswStep s (w n)).nextEdge = _
    simp only [kmswStep, hstep, kmswStepOfStep, hr0, State.addEdge]
  have hr := StageRotation.step_pendant s ha (stageRotation_UL_bound w n)
    (stageRot w n) (w n) hstep hUR
  have ht := (StageRotation.pendant_new s.nextEdge (stageRot w n)
    (⟨s.active, ha⟩, true)).1
  have he : stageRot w (n + 1) (kmswRootedStage w (n + 1)).root =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (edgeFlip _ (kmswRootedStage w n).root) := by
    apply rot_eq_of_resize hs _ _ hr _ _ _ _ ?_ ?_ ht
    · change ((kmswStep s (w n)).active, false) = (s.nextEdge + 0, false)
      simp only [kmswStep, hstep, kmswStepOfStep, hr0, State.addEdge, Nat.add_zero]
    · rfl
  change edgeFlip _ (stageRot w (n + 1) (kmswRootedStage w (n + 1)).root) = _
  rw [he]
  rfl

/-- For either triangle-creation branch, an isomorphism already sends the
embedded previous active dart to its counterpart. Edge deletion and the
predecessor outer-face verification remain separate (`def-kmsw`, -/
theorem RootedDirectedMapIso.predecessorRoot_comm_of_not_down
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n ≠ 2) :
    h.dartEquiv
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root) =
      outerSucc_castDart (kmswStage_nextEdge_mono w' (Nat.le_succ n))
        (kmswRootedStage w' n).root := by
  have heq := lastCode_of_iso w w' n h
  rcases code_cases (w n) with h0 | h1 | h2
  · have h0' : w' n = 0 := heq.symm.trans h0
    rw [← kmswRootedStage_left_previousActiveDart w n h0,
      h.previousActiveDart_comm,
      kmswRootedStage_left_previousActiveDart w' n h0']
  · have h1' : w' n = 1 := heq.symm.trans h1
    rw [← kmswRootedStage_up_previousActiveDart w n h1,
      h.previousActiveDart_comm,
      kmswRootedStage_up_previousActiveDart w' n h1']
  · exact (hc h2).elim

/-- Injectivity of the one-step prefix, the first nonempty base case for -/
theorem kmswRootedStage_one_prefix_injective (w w' : ℕ → Fin 3)
    (h : RootedDirectedMapIso (kmswRootedStage w 1) (kmswRootedStage w' 1)) :
    ∀ i < 1, w i = w' i := by
  intro i hi
  have he : i = 0 := by omega
  subst i
  exact lastCode_of_iso w w' 0 h

/-- The intrinsic last-step classifier: down has both tail signals; among
the other two branches, up has the missing head successor (`def-kmsw`,
it does not delete any edges. -/
@[expose] noncomputable def RootedDirectedMapWithMissing.peelCode
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) : Fin 3 := by
  classical
  exact if M.incomingAtRootTail ∧ M.uniqueOutgoingAtRootTail then 2
    else if M.missingAfterRootHead then 1 else 0

/-- The intrinsic root classifier recovers every last code, at every -/
theorem kmswRootedStage_peelCode (w : ℕ → Fin 3) (n : ℕ) :
    (kmswRootedStage w (n + 1)).peelCode = w n := by
  classical
  unfold RootedDirectedMapWithMissing.peelCode
  rcases code_cases (w n) with h0 | h1 | h2
  · rw [ite_eq_right (kmswRootedStage_left_not_downTailSignals w n h0),
      ite_eq_right (kmswRootedStage_left_not_missingAfterRootHead w n h0), h0]
  · have hn : ¬ ((kmswRootedStage w (n + 1)).incomingAtRootTail ∧
        (kmswRootedStage w (n + 1)).uniqueOutgoingAtRootTail) :=
      fun hh => kmswRootedStage_up_not_uniqueOutgoingAtRootTail w n h1 hh.2
    rw [ite_eq_right hn, ite_eq_left (kmswRootedStage_up_missingAfterRootHead w n h1), h1]
  · rw [ite_eq_left ((kmswRootedStage_down_iff w n).mpr h2), h2]

/-- The complete last-step classifier is preserved by rooted map -/
theorem RootedDirectedMapIso.peelCode_eq
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) : M.peelCode = N.peelCode := by
  classical
  unfold RootedDirectedMapWithMissing.peelCode
  rw [h.incomingAtRootTail_iff, h.uniqueOutgoingAtRootTail_iff,
    h.missingAfterRootHead_iff]

end DirectedDistances.KMSW
