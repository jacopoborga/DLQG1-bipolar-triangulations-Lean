module

public import DirectedDistances.KMSW.KMSWInverseInjective

/-! # Left-step deletion and inverse KMSW helpers


The two down branches are distinguished intrinsically by the root head's
rotation. Left-step deletion restricts the successor dart equivalence to the
old darts and bypasses the inserted darts in rotation. Consequently every
successor isomorphism has a predecessor isomorphism, and `prefixCodes_of_iso`
recovers all letters strictly before the given stage.

Scope: injectivity half only: rooted isomorphism of stage-n maps of arbitrary
code words implies equal codes below n. Not proved: surjectivity, bijectivity
of thm-kmsw, final-stage identification as a missing-edge-free bipolar
triangulation, unrooted-to-rooted isomorphism, uniformity. Letters correspond -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- A missing upper-right edge cannot have a singleton head rotation:
otherwise both its darts would be on the outer boundary, contrary to the
The contradiction comes from `e ∈ LR` (present versus missing) or `e ∈ LL`
(disjoint from `UR`). -/
theorem stageRot_UR_head_ne (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) (he : e.val ∈ (kmswStage w n).UR) :
    stageRot w n (e, true) ≠ (e, true) := by
  intro hf
  have hw : (e, false) ∈ stageOuterWord w n :=
    (stageOuterWord_mem_iff w n _).mpr (Or.inl ⟨rfl, Or.inr he⟩)
  have hs := stageOuterWord_faceSucc w n (e, false) hw
  have hface : (kmswMap w n).faceSucc (e, false) = (e, true) := by
    change (stageRot w n).symm (e, true) = (e, true)
    exact (Equiv.symm_apply_eq _).mpr hf.symm
  rw [hface] at hs
  have hm : (e, true) ∈ stageOuterWord w n := by
    rw [hs]
    exact List.formPerm_apply_mem_of_mem hw
  have hm := (stageOuterWord_mem_iff w n _).mp hm
  have hmissing := ((kmswStage_status w n).1 e.val e.isLt).mpr (Or.inl he)
  rcases hm with ⟨hbad, _⟩ | ⟨_, hLR | hLL⟩
  · cases hbad
  · have hp := (kmswStage_status w n).2.2.1 e.val hLR
    rw [hp] at hmissing
    cases hmissing
  · exact (kmswStage_status w n).2.2.2.2.2 e.val he hLL

private theorem dart_val_injective (k : ℕ) :
    Function.Injective (fun d : StageDart k => (d.1.val, d.2)) := by
  intro x y h
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (congrArg (fun d : ℕ × Bool => d.2) h)

private theorem fixed_of_resize {k l : ℕ} (hs : l = k)
    (R : Equiv.Perm (StageDart l)) (σ : Equiv.Perm (StageDart k))
    (hR : StageRotation.resize hs R = σ)
    (x : StageDart l) (y : StageDart k)
    (hxy : (x.1.val, x.2) = (y.1.val, y.2)) (hx : R x = x) : σ y = y := by
  subst l
  change R = σ at hR
  have he := dart_val_injective k hxy
  rw [hR, he] at hx
  exact hx

/-- An activation-down head is not a singleton vertex rotation, unlike a -/
theorem kmswRootedStage_activation_head_ne (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hc : w n = 2) (hUR : (kmswStage w n).UR = e :: es) :
    stageRot w (n + 1) (edgeFlip _ (kmswRootedStage w (n + 1)).root) ≠
      edgeFlip _ (kmswRootedStage w (n + 1)).root := by
  intro hf
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr (by rw [hUR]; simp))))
  have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge := by
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR]
  have hr := StageRotation.step_activation (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n)
    (stageRot w n) (w n) ht e es hUR
  have hh := fixed_of_resize hs _ _ hr
    (edgeFlip _ (kmswRootedStage w (n + 1)).root) (⟨e, he⟩, true) ?_ hf
  · exact stageRot_UR_head_ne w n ⟨e, he⟩ (by rw [hUR]; simp) hh
  · change ((kmswStage w (n + 1)).active, !false) = (e, true)
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR, Bool.not_false]

private theorem head_fixed_iff {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) :
    M.map.rot (M.map.toCombinatorialMap.edgeInv M.root) =
        M.map.toCombinatorialMap.edgeInv M.root ↔
      N.map.rot (N.map.toCombinatorialMap.edgeInv N.root) =
        N.map.toCombinatorialMap.edgeInv N.root := by
  have he : h.dartEquiv (M.map.toCombinatorialMap.edgeInv M.root) =
      N.map.toCombinatorialMap.edgeInv N.root := by rw [h.edgeFlip_comm, h.root_comm]
  constructor
  · intro hf
    have hh := congrArg h.dartEquiv hf
    rw [h.rot_comm, he] at hh
    exact hh
  · intro hf
    apply h.dartEquiv.injective
    rw [h.rot_comm, he, hf]

/-- A successor isomorphism cannot mix activation-down and pendant-down:
the root head has fixed rotation exactly in the pendant case -/
theorem RootedDirectedMapIso.down_pendant_iff
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 2) :
    (kmswStage w n).UR = [] ↔ (kmswStage w' n).UR = [] := by
  have hc' : w' n = 2 := (lastCode_of_iso w w' n h).symm.trans hc
  have hh := head_fixed_iff h
  constructor
  · intro hUR
    have hf := hh.mp (kmswRootedStage_pendant_head_fixed w n hc hUR)
    cases hUR' : (kmswStage w' n).UR with
    | nil => rfl
    | cons e es => exact (kmswRootedStage_activation_head_ne w' n e es hc' hUR' hf).elim
  · intro hUR'
    have hf := hh.mpr (kmswRootedStage_pendant_head_fixed w' n hc' hUR')
    cases hUR : (kmswStage w n).UR with
    | nil => rfl
    | cons e es => exact (kmswRootedStage_activation_head_ne w n e es hc hUR hf).elim

/-- Both down cases admit an intrinsic predecessor isomorphism -/
def RootedDirectedMapIso.predecessor_down
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 2) :
    RootedDirectedMapIso (kmswRootedStage w n) (kmswRootedStage w' n) := by
  have hm := h.down_pendant_iff w w' n hc
  cases hUR : (kmswStage w n).UR with
  | nil => exact h.predecessor_pendant w w' n hc hUR (hm.mp hUR)
  | cons e es =>
    cases hUR' : (kmswStage w' n).UR with
    | nil =>
      have hh := hm.mpr hUR'
      rw [hUR] at hh
      cases hh
    | cons e' es' => exact h.predecessor_activation w w' n e e' es es' hc hUR hUR'

private theorem rot_eq_of_resize {k l : ℕ} (hs : k = l)
    (R : Equiv.Perm (StageDart k)) (σ : Equiv.Perm (StageDart l))
    (hR : StageRotation.resize hs R = σ)
    (x y : StageDart k) (x' y' : StageDart l)
    (hx : (x.1.val, x.2) = (x'.1.val, x'.2))
    (hy : (y.1.val, y.2) = (y'.1.val, y'.2)) (ht : σ x' = y') : R x = y := by
  subst hs
  have hx' := dart_val_injective _ hx
  have hy' := dart_val_injective _ hy
  change R = σ at hR
  rw [hR, hx', hy']
  exact ht


private theorem sameEdge_darts {k : ℕ} (d a : StageDart k) :
    (d = a ∨ d = edgeFlip k a) ↔ d.1.val = a.1.val := by
  rcases d with ⟨d, b⟩
  rcases a with ⟨a, c⟩
  simp only [edgeFlip_apply, Prod.mk.injEq, Fin.ext_iff]
  cases b <;> cases c <;> simp


private theorem left_root_val (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) :
    (kmswRootedStage w (n + 1)).root.1.val = (kmswStage w n).nextEdge := by
  have ht : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  cases hl : (kmswStage w n).UL.dropLast.reverse with
  | nil => simp only [kmswRootedStage, kmswStage, kmswStep, ht, kmswStepOfStep, hl,
      State.addEdge]
  | cons e es => simp only [kmswRootedStage, kmswStage, kmswStep, ht, kmswStepOfStep, hl,
      State.addEdge]

private theorem left_beforeRoot_existing (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hc : w n = 0)
    (hl : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    ((stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root).1.val = e := by
  let s := kmswStage w n
  have hls : s.UL.dropLast.reverse = e :: es := hl
  have ht : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  have he : e < s.nextEdge := stageRotation_UL_bound w n e
    (List.dropLast_subset _ (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 1 := by
    change (kmswStep s (w n)).nextEdge = _
    simp only [kmswStep, ht, kmswStepOfStep, hls, State.addEdge]
  let x : StageDart (kmswStage w (n + 1)).nextEdge :=
    (⟨e, by omega⟩, false)
  have hr := StageRotation.step_leftExisting s (act_lt_nextEdge w (le_refl n))
    (stageRotation_UL_bound w n) (stageRot w n) (w n) ht e es hl
  have hn := StageRotation.leftExisting_old s.nextEdge (stageRot w n)
    (⟨e, he⟩, false) (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true) (⟨e, he⟩, false)
  simp only [↓reduceIte] at hn
  have hx : stageRot w (n + 1) x = (kmswRootedStage w (n + 1)).root := by
    apply rot_eq_of_resize hs _ _ hr x _ _ _ rfl ?_ hn
    change ((kmswRootedStage w (n + 1)).root.1.val, false) = (s.nextEdge + 0, false)
    rw [left_root_val w n hc]
    rfl
  have hi : (stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root = x :=
    (Equiv.symm_apply_eq _).mpr hx.symm
  exact congrArg (fun d => d.1.val) hi

private theorem left_beforeRoot_fresh (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hl : (kmswStage w n).UL.dropLast.reverse = []) :
    ((stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root).1.val =
      (kmswStage w n).nextEdge + 1 := by
  let s := kmswStage w n
  have hls : s.UL.dropLast.reverse = [] := hl
  have ht : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
    change (kmswStep s (w n)).nextEdge = _
    simp only [kmswStep, ht, kmswStepOfStep, hls, State.addEdge]
  let x : StageDart (kmswStage w (n + 1)).nextEdge :=
    (⟨s.nextEdge + 1, by omega⟩, false)
  have hr := StageRotation.step_leftFresh s (act_lt_nextEdge w (le_refl n))
    (stageRotation_UL_bound w n) (stageRot w n) (w n) ht hl
  have hn := (StageRotation.leftFresh_new s.nextEdge (stageRot w n)
    (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
    (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true)).2.2.2
  have hx : stageRot w (n + 1) x = (kmswRootedStage w (n + 1)).root := by
    apply rot_eq_of_resize hs _ _ hr x _ _ _ rfl ?_ hn
    change ((kmswRootedStage w (n + 1)).root.1.val, false) = (s.nextEdge + 0, false)
    rw [left_root_val w n hc]
    rfl
  have hi : (stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root = x :=
    (Equiv.symm_apply_eq _).mpr hx.symm
  exact congrArg (fun d => d.1.val) hi

private theorem stage_left_present (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    (kmswStage w (n + 1)).present e = (kmswStage w n).present e := by
  have ht : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  have h0 : e ≠ (kmswStage w n).nextEdge := by omega
  have h1 : e ≠ (kmswStage w n).nextEdge + 1 := by omega
  cases hl : (kmswStage w n).UL.dropLast.reverse with
  | nil => simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hl, State.addEdge,
      h0, h1, ↓reduceIte]
  | cons f fs => simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hl, State.addEdge,
      h0, ↓reduceIte]

/-- A left step has a fresh west vertex exactly when the dart immediately
before the root in rotation is missing (`def-kmsw`, -/
theorem kmswRootedStage_left_missingBeforeRoot_iff (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) :
    (kmswRootedStage w (n + 1)).map.missing
        ((stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root) ↔
      (kmswStage w n).UL.dropLast.reverse = [] := by
  cases hl : (kmswStage w n).UL.dropLast.reverse with
  | nil =>
    simp only [iff_true]
    change (kmswStage w (n + 1)).present
      ((stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root).1.val = false
    rw [left_beforeRoot_fresh w n hc hl]
    have ht : kmswCodeStep (w n) = .left := by rw [hc]; rfl
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hl, State.addEdge, ↓reduceIte]
  | cons e es =>
    simp only [List.cons_ne_nil, iff_false]
    change ¬ (kmswStage w (n + 1)).present
      ((stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root).1.val = false
    rw [left_beforeRoot_existing w n e es hc hl]
    have hm : e ∈ (kmswStage w n).UL :=
      List.dropLast_subset _ (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self))
    have he := stageRotation_UL_bound w n e hm
    rw [stage_left_present w n hc e he, (kmswStage_status w n).2.1 e hm]
    decide

private def leftCreated {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) (d : D) : Prop :=
  (d = M.root ∨ d = M.map.toCombinatorialMap.edgeInv M.root) ∨
    (M.map.missing (M.map.rot.symm M.root) ∧
      (d = M.map.rot.symm M.root ∨
        d = M.map.toCombinatorialMap.edgeInv (M.map.rot.symm M.root)))

private theorem leftCreated_comm {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (d : D) :
    leftCreated M d ↔ leftCreated N (h.dartEquiv d) := by
  have hs : h.dartEquiv (M.map.rot.symm M.root) = N.map.rot.symm N.root := by
    apply N.map.rot.injective
    rw [← h.rot_comm, Equiv.apply_symm_apply, h.root_comm, Equiv.apply_symm_apply]
  have he : h.dartEquiv (M.map.toCombinatorialMap.edgeInv M.root) =
      N.map.toCombinatorialMap.edgeInv N.root := by rw [h.edgeFlip_comm, h.root_comm]
  have ht : h.dartEquiv (M.map.toCombinatorialMap.edgeInv (M.map.rot.symm M.root)) =
      N.map.toCombinatorialMap.edgeInv (N.map.rot.symm N.root) := by
    rw [h.edgeFlip_comm, hs]
  unfold leftCreated
  rw [← ht, ← he, ← hs, ← h.root_comm, ← h.missing_iff,
    h.dartEquiv.injective.eq_iff, h.dartEquiv.injective.eq_iff,
    h.dartEquiv.injective.eq_iff, h.dartEquiv.injective.eq_iff]

private theorem leftCreated_iff (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    leftCreated (kmswRootedStage w (n + 1)) d ↔
      (kmswStage w n).nextEdge ≤ d.1.val := by
  unfold leftCreated
  change ((d = _ ∨ d = edgeFlip _ _) ∨
    (_ ∧ (d = _ ∨ d = edgeFlip _ _))) ↔ _
  rw [sameEdge_darts, sameEdge_darts, left_root_val w n hc]
  change (d.1.val = (kmswStage w n).nextEdge ∨
    (kmswRootedStage w (n + 1)).map.missing
      ((stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root) ∧
    d.1.val = ((stageRot w (n + 1)).symm (kmswRootedStage w (n + 1)).root).1.val) ↔ _
  rw [kmswRootedStage_left_missingBeforeRoot_iff w n hc]
  have ht : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  have hd := d.1.isLt
  cases hl : (kmswStage w n).UL.dropLast.reverse with
  | nil =>
    rw [left_beforeRoot_fresh w n hc hl]
    simp only [true_and]
    have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 := by
      simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hl, State.addEdge]
    omega
  | cons e es =>
    simp only [List.cons_ne_nil, false_and, or_false]
    have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 := by
      simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hl, State.addEdge]
    omega

/-- A successor isomorphism preserves precisely the old darts in either -/
theorem RootedDirectedMapIso.left_surviving_iff
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 0)
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    d.1.val < (kmswStage w n).nextEdge ↔
      (h.dartEquiv d).1.val < (kmswStage w' n).nextEdge := by
  have hc' : w' n = 0 := (lastCode_of_iso w w' n h).symm.trans hc
  have hh := leftCreated_comm h d
  rw [leftCreated_iff w n hc, leftCreated_iff w' n hc'] at hh
  omega

/-- The successor equivalence restricted to surviving old darts in either -/
@[expose] def RootedDirectedMapIso.predecessorDartEquiv_left
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 0) :
    StageDart (kmswStage w n).nextEdge ≃ StageDart (kmswStage w' n).nextEdge :=
  ((survivingDartEquiv (kmswStage_nextEdge_mono w (Nat.le_succ n))).trans
    (h.dartEquiv.subtypeEquiv (h.left_surviving_iff w w' n hc))).trans
    (survivingDartEquiv (kmswStage_nextEdge_mono w' (Nat.le_succ n))).symm

/-- The left-step restriction agrees with the original equivalence on all -/
theorem RootedDirectedMapIso.predecessorDartEquiv_left_comm
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 0)
    (d : StageDart (kmswStage w n).nextEdge) :
    outerSucc_castDart (kmswStage_nextEdge_mono w' (Nat.le_succ n))
      (h.predecessorDartEquiv_left w w' n hc d) =
      h.dartEquiv (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) := rfl

private def castDartEquiv {k l : ℕ} (h : k = l) : StageDart k ≃ StageDart l :=
  Equiv.prodCongr (finCongr h) (Equiv.refl Bool)


private def skipTwo {D : Type*} (σ : D → D) (p : D → Prop) [DecidablePred p]
    (d : D) : D :=
  if p (σ d) then σ d else if p (σ (σ d)) then σ (σ d) else σ (σ (σ d))


private theorem leftExisting_skip (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (a A d : StageDart k) :
    StageRotation.allocation k 1 (.inl (σ d)) =
      skipTwo (StageRotation.leftExisting k σ a A) (fun x => x.1.val < k)
        (StageRotation.allocation k 1 (.inl d)) := by
  have hn := StageRotation.leftExisting_new k σ a A
  have hold : ∀ x : StageDart k,
      (StageRotation.allocation k 1 (.inl x)).1.val < k := fun x => x.1.isLt
  have hx : ¬ (StageRotation.allocation k 1 (.inr (0, false))).1.val < k := by
    change ¬ k + 0 < k; omega
  have hy : ¬ (StageRotation.allocation k 1 (.inr (0, true))).1.val < k := by
    change ¬ k + 0 < k; omega
  by_cases hda : d = a
  · subst d
    by_cases hA : σ a = A
    · simp only [skipTwo, StageRotation.leftExisting_old, ↓reduceIte, hx, hn.1, hA,
        hy, hn.2]
    · simp only [skipTwo, StageRotation.leftExisting_old, ↓reduceIte, hx, hn.1, hA,
        hold]
  · by_cases hA : σ d = A
    · simp only [skipTwo, StageRotation.leftExisting_old, hda, hA, ↓reduceIte, hy,
        hn.2, hold]
    · simp only [skipTwo, StageRotation.leftExisting_old, hda, hA, ↓reduceIte, hold]


private theorem leftFresh_skip (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (a A d : StageDart k) :
    StageRotation.allocation k 2 (.inl (σ d)) =
      skipTwo (StageRotation.leftFresh k σ a A) (fun x => x.1.val < k)
        (StageRotation.allocation k 2 (.inl d)) := by
  have hn := StageRotation.leftFresh_new k σ a A
  have hold : ∀ x : StageDart k,
      (StageRotation.allocation k 2 (.inl x)).1.val < k := fun x => x.1.isLt
  have hx : ¬ (StageRotation.allocation k 2 (.inr (1, true))).1.val < k := by
    change ¬ k + 1 < k; omega
  have hy : ¬ (StageRotation.allocation k 2 (.inr (0, true))).1.val < k := by
    change ¬ k + 0 < k; omega
  by_cases hda : d = a
  · subst d
    by_cases hA : σ a = A
    · simp only [skipTwo, StageRotation.leftFresh_old, ↓reduceIte, hx, hn.1, hA,
        hy, hn.2.1]
    · simp only [skipTwo, StageRotation.leftFresh_old, ↓reduceIte, hx, hn.1, hA,
        hold]
  · by_cases hA : σ d = A
    · simp only [skipTwo, StageRotation.leftFresh_old, hda, hA, ↓reduceIte, hy,
        hn.2.1, hold]
    · simp only [skipTwo, StageRotation.leftFresh_old, hda, hA, ↓reduceIte, hold]


private theorem skip_resize {k l r : ℕ} (hs : l = k + r)
    (σ : Equiv.Perm (StageDart k)) (R : Equiv.Perm (StageDart l))
    (ρ : Equiv.Perm (StageDart (k + r))) (d : StageDart k)
    (hR : StageRotation.resize hs R = ρ)
    (hσ : StageRotation.allocation k r (.inl (σ d)) =
      skipTwo ρ (fun x => x.1.val < k) (StageRotation.allocation k r (.inl d))) :
    castDartEquiv hs.symm (StageRotation.allocation k r (.inl (σ d))) =
      skipTwo R (fun x => x.1.val < k)
        (castDartEquiv hs.symm (StageRotation.allocation k r (.inl d))) := by
  subst l
  change R = ρ at hR
  rw [hR]
  exact hσ

private theorem stage_left_skip (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (d : StageDart (kmswStage w n).nextEdge) :
    outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) (stageRot w n d) =
      skipTwo (stageRot w (n + 1)) (fun x => x.1.val < (kmswStage w n).nextEdge)
        (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) := by
  have ht : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  cases hl : (kmswStage w n).UL.dropLast.reverse with
  | nil =>
    have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 := by
      simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hl, State.addEdge]
    have hr := StageRotation.step_leftFresh (kmswStage w n)
      (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n)
      (stageRot w n) (w n) ht hl
    exact skip_resize hs (stageRot w n) (stageRot w (n + 1)) _ d hr
      (leftFresh_skip (kmswStage w n).nextEdge (stageRot w n) _ _ d)
  | cons e es =>
    have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 := by
      simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hl, State.addEdge]
    have hr := StageRotation.step_leftExisting (kmswStage w n)
      (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n)
      (stageRot w n) (w n) ht e es hl
    exact skip_resize hs (stageRot w n) (stageRot w (n + 1)) _ d hr
      (leftExisting_skip (kmswStage w n).nextEdge (stageRot w n) _ _ d)

private theorem skipTwo_comm {D E : Type*} (f : D → E) (σ : D → D) (τ : E → E)
    (p : D → Prop) (q : E → Prop) [DecidablePred p] [DecidablePred q]
    (hr : ∀ d, f (σ d) = τ (f d)) (hp : ∀ d, p d ↔ q (f d)) (d : D) :
    f (skipTwo σ p d) = skipTwo τ q (f d) := by
  simp only [skipTwo, ← hr, ← hp]
  split_ifs <;> rfl


private theorem castDart_injective {k l : ℕ} (h : k ≤ l) :
    Function.Injective (outerSucc_castDart h) := by
  intro d e he
  apply dart_val_injective k
  exact congrArg (fun d : StageDart l => (d.1.val, d.2)) he


/-- Rotation transport after deleting the inserted left-step darts -/
theorem RootedDirectedMapIso.predecessorDartEquiv_left_rot
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 0)
    (d : StageDart (kmswStage w n).nextEdge) :
    h.predecessorDartEquiv_left w w' n hc (stageRot w n d) =
      stageRot w' n (h.predecessorDartEquiv_left w w' n hc d) := by
  have hc' : w' n = 0 := (lastCode_of_iso w w' n h).symm.trans hc
  apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
  rw [h.predecessorDartEquiv_left_comm w w' n hc, stage_left_skip w n hc,
    stage_left_skip w' n hc']
  have hr : ∀ x, h.dartEquiv (stageRot w (n + 1) x) =
      stageRot w' (n + 1) (h.dartEquiv x) := h.rot_comm
  rw [skipTwo_comm h.dartEquiv _ _
      (fun x => x.1.val < (kmswStage w n).nextEdge)
      (fun x => x.1.val < (kmswStage w' n).nextEdge) hr (h.left_surviving_iff w w' n hc),
    h.predecessorDartEquiv_left_comm w w' n hc]


private theorem sameCycle_transport {D E : Type*} [Finite D] [Finite E]
    (f : D ≃ E) (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (hc : ∀ d, f (σ d) = τ (f d)) (a b : D) :
    σ.SameCycle a b ↔ τ.SameCycle (f a) (f b) := by
  have hp : ∀ k : ℕ, ∀ d, f ((σ ^ k) d) = (τ ^ k) (f d) := by
    intro k d
    induction k with
    | zero => rfl
    | succ k ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hc] using congrArg τ ih
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, (hp k a).symm.trans (congrArg f hk)⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, f.injective ((hp k a).trans hk)⟩


private theorem outer_transport_of_root {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (M : RootedDirectedMapWithMissing D) (N : RootedDirectedMapWithMissing E)
    (f : D ≃ E) (hr : ∀ d, f (M.map.rot d) = N.map.rot (f d))
    (he : ∀ d, f (M.map.toCombinatorialMap.edgeInv d) =
      N.map.toCombinatorialMap.edgeInv (f d)) (hroot : f M.root = N.root)
    (hM : M.map.IsOuter M.root) (hN : N.map.IsOuter N.root) (d : D) :
    M.map.IsOuter d ↔ N.map.IsOuter (f d) := by
  have hface : ∀ x, f (M.map.toCombinatorialMap.faceSucc x) =
      N.map.toCombinatorialMap.faceSucc (f x) := by
    intro x
    apply N.map.rot.injective
    change N.map.rot (f (M.map.rot.symm (M.map.toCombinatorialMap.edgeInv x))) =
      N.map.rot (N.map.rot.symm (N.map.toCombinatorialMap.edgeInv (f x)))
    rw [← hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply, he]
  have ht := sameCycle_transport f M.map.toCombinatorialMap.faceSucc
    N.map.toCombinatorialMap.faceSucc hface M.root d
  rw [hroot] at ht
  change M.map.toCombinatorialMap.faceSucc.SameCycle M.map.outer d ↔
    N.map.toCombinatorialMap.faceSucc.SameCycle N.map.outer (f d)
  exact ⟨fun hd => hN.trans (ht.mp (hM.symm.trans hd)),
    fun hd => hM.trans (ht.mpr (hN.symm.trans hd))⟩


private theorem castLE_edgeFlip {k l : ℕ} (h : k ≤ l) (d : StageDart k) :
    outerSucc_castDart h (edgeFlip k d) = edgeFlip l (outerSucc_castDart h d) := rfl


/-- Delete the created root edge and, in the fresh-left case, its new
missing companion; bypass their darts and recover the predecessor map -/
def RootedDirectedMapIso.predecessor_left
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 0) :
    RootedDirectedMapIso (kmswRootedStage w n) (kmswRootedStage w' n) := by
  have hc' : w' n = 0 := (lastCode_of_iso w w' n h).symm.trans hc
  let f := h.predecessorDartEquiv_left w w' n hc
  let E := outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
  let E' := outerSucc_castDart (kmswStage_nextEdge_mono w' (Nat.le_succ n))
  have hf : ∀ d, E' (f d) = h.dartEquiv (E d) :=
    h.predecessorDartEquiv_left_comm w w' n hc
  dsimp only [E, E'] at hf
  have hr : ∀ d, f (stageRot w n d) = stageRot w' n (f d) :=
    h.predecessorDartEquiv_left_rot w w' n hc
  have he : ∀ d, f (edgeFlip _ d) = edgeFlip _ (f d) := by
    intro d
    apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
    have hh : ∀ x, h.dartEquiv (edgeFlip _ x) = edgeFlip _ (h.dartEquiv x) :=
      h.edgeFlip_comm
    rw [hf, castLE_edgeFlip, hh, ← hf, castLE_edgeFlip]
  have hroot : f (kmswRootedStage w n).root = (kmswRootedStage w' n).root := by
    apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
    rw [hf]
    exact h.predecessorRoot_comm w w' n
  have hm : ∀ d, (kmswRootedStage w n).map.missing d ↔
      (kmswRootedStage w' n).map.missing (f d) := by
    intro d
    have hh := h.missing_iff (E d)
    rw [← hf] at hh
    change (kmswStage w (n + 1)).present d.1.val = false ↔
      (kmswStage w' (n + 1)).present (f d).1.val = false at hh
    rw [stage_left_present w n hc _ d.1.isLt,
      stage_left_present w' n hc' _ (f d).1.isLt] at hh
    exact hh
  have ht : ∀ d, (kmswRootedStage w n).map.tail d ↔
      (kmswRootedStage w' n).map.tail (f d) := by
    intro d
    have hh := h.tail_iff (E d)
    rw [← hf] at hh
    change ((kmswStage w (n + 1)).present d.1.val = true ∧ d.2 = false) ↔
      ((kmswStage w' (n + 1)).present (f d).1.val = true ∧ (f d).2 = false) at hh
    rw [stage_left_present w n hc _ d.1.isLt,
      stage_left_present w' n hc' _ (f d).1.isLt] at hh
    exact hh
  exact {
    dartEquiv := f
    rot_comm := hr
    edgeFlip_comm := he
    missing_iff := hm
    present_iff := fun d => not_congr (hm d)
    tail_iff := ht
    outer_iff := outer_transport_of_root _ _ f hr he hroot
      (kmswRootedStage_root_isOuter w n) (kmswRootedStage_root_isOuter w' n)
    root_comm := hroot }


/-- Any successor-stage isomorphism induces an isomorphism of predecessor
stages, in all construction branches (`def-kmsw`, -/
def RootedDirectedMapIso.predecessor
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) :
    RootedDirectedMapIso (kmswRootedStage w n) (kmswRootedStage w' n) := by
  by_cases h0 : w n = 0
  · exact h.predecessor_left w w' n h0
  by_cases h1 : w n = 1
  · exact h.predecessor_up w w' n h1
  have h2 : w n = 2 := by
    apply Fin.ext
    have hlt := (w n).isLt
    have hn0 : (w n).val ≠ 0 := fun hh => h0 (Fin.ext hh)
    have hn1 : (w n).val ≠ 1 := fun hh => h1 (Fin.ext hh)
    change (w n).val = 2
    omega
  exact h.predecessor_down w w' n h2

/-- Isomorphic rooted directed stages have identical code prefixes, proved
by repeatedly taking predecessor isomorphisms (`def-kmsw`,

This does not implement defn:KMSW-inv; it is iterated predecessor peeling.
Injectivity half of thm-kmsw only. -/
theorem prefixCodes_of_iso (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w n) (kmswRootedStage w' n)) :
    ∀ i < n, w i = w' i := by
  revert h
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    by_cases hin : i < n
    · exact ih (h.predecessor w w' n) i hin
    · have hei : i = n := by omega
      subst i
      exact lastCode_of_iso w w' n h

end DirectedDistances.KMSW
