module

public import DirectedDistances.KMSW.BoundaryRecordsUL
public import DirectedDistances.PlanarMap.CombinatorialMap
public import DirectedDistances.PlanarMap.PermutationSplice

/-! # KMSW stage rotations

Fresh darts are first added as a disjoint summand, then transported to their
creation-order edge IDs. West/east darts are geometric endpoints, including
for missing edges. This file constructs raw combinatorial maps; it does not
assert planarity or identify their vertex quotients with the state vertex IDs. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- `false` is west and `true` is east. -/
abbrev StageDart (k : ℕ) := Fin k × Bool

/-- Opposite dart of the same geometric edge (`def-kmsw`, -/
@[expose] def edgeFlip (k : ℕ) : Equiv.Perm (StageDart k) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl

/-- Dartwise edge involution table (`def-kmsw`, -/
theorem edgeFlip_apply (k : ℕ) (e : Fin k) (b : Bool) :
    edgeFlip k (e, b) = (e, !b) := rfl

/-- Geometric endpoint represented by a stage dart (`def-kmsw`, -/
@[expose] def stageEndpoint (s : State) (d : StageDart s.nextEdge) : ℕ :=
  if d.2 then s.east d.1.val else s.west d.1.val

namespace StageRotation

/-- Old IDs stay unchanged; fresh ID `j` becomes `k+j`. -/
@[expose] def allocation (k r : ℕ) : StageDart k ⊕ StageDart r ≃ StageDart (k + r) where
  toFun
    | .inl (e, b) => (⟨e.val, by omega⟩, b)
    | .inr (e, b) => (⟨k + e.val, by omega⟩, b)
  invFun d := if h : d.1.val < k then .inl (⟨d.1.val, h⟩, d.2)
    else .inr (⟨d.1.val - k, by have := d.1.isLt; omega⟩, d.2)
  left_inv := by
    rintro (⟨e, b⟩ | ⟨e, b⟩)
    · simp only [e.isLt, ↓reduceDIte]
    · simp only [show ¬ k + e.val < k by omega, ↓reduceDIte]
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Fin.ext
        dsimp only
        omega
      · rfl
  right_inv := by
    rintro ⟨e, b⟩
    dsimp only
    by_cases h : e.val < k
    · simp only [h, ↓reduceDIte]
    · simp only [h, ↓reduceDIte]
      apply Prod.ext
      · apply Fin.ext
        dsimp only
        omega
      · rfl

/-- Old-ID evaluation under allocation (`def-kmsw`, -/
theorem allocation_old (k r : ℕ) (e : Fin k) (b : Bool) :
    allocation k r (.inl (e, b)) = (⟨e.val, by omega⟩, b) := rfl

/-- Fresh-ID evaluation under allocation (`def-kmsw`, -/
theorem allocation_new (k r : ℕ) (e : Fin r) (b : Bool) :
    allocation k r (.inr (e, b)) = (⟨k + e.val, by omega⟩, b) := rfl

/-- Two rotation insertions on disjoint old/fresh summands (`def-kmsw`, -/
@[expose] def pairSplice {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F) :
    Equiv.Perm (D ⊕ F) :=
  insertBefore (insertAfter (Equiv.sumCongr σ τ) (.inl a) (.inr x)) (.inl b) (.inr y)

private theorem pairSplice_old {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F)
    (hx : τ x = x) (hxy : x ≠ y) (d : D) :
    pairSplice σ τ a b x y (.inl d) =
      if d = a then .inr x else if σ d = b then .inr y else .inl (σ d) := by
  by_cases hda : d = a
  · subst d
    simp [pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hx, hxy]
  · by_cases hdb : σ d = b <;>
      simp [pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hda, hdb]

private theorem pairSplice_x {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F) :
    pairSplice σ τ a b x y (.inr x) =
      if σ a = b then .inr y else .inl (σ a) := by
  by_cases hab : σ a = b <;>
    simp [pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hab]

private theorem pairSplice_y {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F)
    (hy : τ y = y) (hyx : y ≠ x) :
    pairSplice σ τ a b x y (.inr y) = .inl b := by
  simp [pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hy, hyx]

private theorem pairSplice_other {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y z : F)
    (hzx : z ≠ x) (hτzy : τ z ≠ y) :
    pairSplice σ τ a b x y (.inr z) = .inr (τ z) := by
  simp [pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hzx, hτzy]

/-- Pendant update: insert the new west dart before the active east dart; -/
@[expose] def pendant (k : ℕ) (σ : Equiv.Perm (StageDart k)) (A : StageDart k) :
    Equiv.Perm (StageDart (k + 1)) :=
  (allocation k 1).permCongr
    (insertBefore (Equiv.sumCongr σ (Equiv.refl _)) (.inl A) (.inr (0, false)))

/-- Existing-predecessor left update (`def-kmsw`, -/
@[expose] def leftExisting (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (e A : StageDart k) : Equiv.Perm (StageDart (k + 1)) :=
  (allocation k 1).permCongr
    (pairSplice σ (Equiv.refl _) e A (0, false) (0, true))

/-- Fresh-left update: the two new west darts form a two-cycle -/
@[expose] def leftFresh (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (a A : StageDart k) : Equiv.Perm (StageDart (k + 2)) :=
  (allocation k 2).permCongr
    (pairSplice σ (Equiv.swap (0, false) (1, false)) a A (1, true) (0, true))

/-- Up update: new active east and new missing west form a two-cycle -/
@[expose] def up (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (a A : StageDart k) : Equiv.Perm (StageDart (k + 2)) :=
  (allocation k 2).permCongr
    (pairSplice σ (Equiv.swap (0, true) (1, false)) a A (0, false) (1, true))

/-- Complete old-dart pendant table (`def-kmsw`, -/
theorem pendant_old (k : ℕ) (σ : Equiv.Perm (StageDart k)) (A d : StageDart k) :
    pendant k σ A (allocation k 1 (.inl d)) =
      allocation k 1 (if σ d = A then .inr (0, false) else .inl (σ d)) := by
  by_cases h : σ d = A <;>
    simp [pendant, insertBefore, Equiv.swap_apply_def, h]

/-- Both fresh pendant successors (`def-kmsw`, -/
theorem pendant_new (k : ℕ) (σ : Equiv.Perm (StageDart k)) (A : StageDart k) :
    pendant k σ A (allocation k 1 (.inr (0, false))) = allocation k 1 (.inl A) ∧
    pendant k σ A (allocation k 1 (.inr (0, true))) =
      allocation k 1 (.inr (0, true)) := by
  constructor <;> simp [pendant, insertBefore, Equiv.swap_apply_def]

/-- Complete old-dart table for an existing-predecessor left step -/
theorem leftExisting_old (k : ℕ) (σ : Equiv.Perm (StageDart k)) (e A d : StageDart k) :
    leftExisting k σ e A (allocation k 1 (.inl d)) =
      allocation k 1 (if d = e then .inr (0, false)
        else if σ d = A then .inr (0, true) else .inl (σ d)) := by
  simp only [leftExisting, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [pairSplice_old σ (Equiv.refl _) e A (0, false) (0, true) rfl (by decide)]

/-- Both fresh successors for an existing-predecessor left step -/
theorem leftExisting_new (k : ℕ) (σ : Equiv.Perm (StageDart k)) (e A : StageDart k) :
    leftExisting k σ e A (allocation k 1 (.inr (0, false))) =
      allocation k 1 (if σ e = A then .inr (0, true) else .inl (σ e)) ∧
    leftExisting k σ e A (allocation k 1 (.inr (0, true))) = allocation k 1 (.inl A) := by
  simp only [leftExisting, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  constructor
  · rw [pairSplice_x]
  · rw [pairSplice_y σ (Equiv.refl _) e A (0, false) (0, true) rfl (by decide)]

/-- Complete old-dart table for a fresh-left step (`def-kmsw`, -/
theorem leftFresh_old (k : ℕ) (σ : Equiv.Perm (StageDart k)) (a A d : StageDart k) :
    leftFresh k σ a A (allocation k 2 (.inl d)) =
      allocation k 2 (if d = a then .inr (1, true)
        else if σ d = A then .inr (0, true) else .inl (σ d)) := by
  simp only [leftFresh, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [pairSplice_old σ _ a A (1, true) (0, true) (by decide) (by decide)]

/-- All four fresh successors for a fresh-left step (`def-kmsw`, -/
theorem leftFresh_new (k : ℕ) (σ : Equiv.Perm (StageDart k)) (a A : StageDart k) :
    leftFresh k σ a A (allocation k 2 (.inr (1, true))) =
      allocation k 2 (if σ a = A then .inr (0, true) else .inl (σ a)) ∧
    leftFresh k σ a A (allocation k 2 (.inr (0, true))) = allocation k 2 (.inl A) ∧
    leftFresh k σ a A (allocation k 2 (.inr (0, false))) =
      allocation k 2 (.inr (1, false)) ∧
    leftFresh k σ a A (allocation k 2 (.inr (1, false))) =
      allocation k 2 (.inr (0, false)) := by
  simp only [leftFresh, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pairSplice_x]
  · rw [pairSplice_y σ _ a A (1, true) (0, true) (by decide) (by decide)]
  · rw [pairSplice_other σ _ a A (1, true) (0, true) (0, false) (by decide) (by decide)]
    rfl
  · rw [pairSplice_other σ _ a A (1, true) (0, true) (1, false) (by decide) (by decide)]
    rfl

/-- Complete old-dart table for an up step (`def-kmsw`, -/
theorem up_old (k : ℕ) (σ : Equiv.Perm (StageDart k)) (a A d : StageDart k) :
    up k σ a A (allocation k 2 (.inl d)) =
      allocation k 2 (if d = a then .inr (0, false)
        else if σ d = A then .inr (1, true) else .inl (σ d)) := by
  simp only [up, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [pairSplice_old σ _ a A (0, false) (1, true) (by decide) (by decide)]

/-- All four fresh successors for an up step (`def-kmsw`, -/
theorem up_new (k : ℕ) (σ : Equiv.Perm (StageDart k)) (a A : StageDart k) :
    up k σ a A (allocation k 2 (.inr (0, false))) =
      allocation k 2 (if σ a = A then .inr (1, true) else .inl (σ a)) ∧
    up k σ a A (allocation k 2 (.inr (1, true))) = allocation k 2 (.inl A) ∧
    up k σ a A (allocation k 2 (.inr (0, true))) =
      allocation k 2 (.inr (1, false)) ∧
    up k σ a A (allocation k 2 (.inr (1, false))) =
      allocation k 2 (.inr (0, true)) := by
  simp only [up, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pairSplice_x]
  · rw [pairSplice_y σ _ a A (0, false) (1, true) (by decide) (by decide)]
  · rw [pairSplice_other σ _ a A (0, false) (1, true) (0, true) (by decide) (by decide)]
    rfl
  · rw [pairSplice_other σ _ a A (0, false) (1, true) (1, false) (by decide) (by decide)]
    rfl

/-- Transport rotations across an equality of allocation sizes (`def-kmsw`, -/
@[expose] def resize {k l : ℕ} (h : k = l) (σ : Equiv.Perm (StageDart k)) :
    Equiv.Perm (StageDart l) := h ▸ σ

private theorem resize_resize {k l m : ℕ} (h : k = l) (h' : l = m)
    (σ : Equiv.Perm (StageDart k)) : resize h' (resize h σ) = resize (h.trans h') σ := by
  cases h
  cases h'
  rfl

private theorem resize_self {k : ℕ} (h : k = k) (σ : Equiv.Perm (StageDart k)) :
    resize h σ = σ := rfl

/-- One rotation update, using only allocated active/upper-left IDs -/
@[expose] def step (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3) : Equiv.Perm (StageDart (kmswStep s c).nextEdge) :=
  match hc : kmswCodeStep c with
  | .down => match hr : s.UR with
    | [] => resize (by simp only [kmswStep, hc, kmswStepOfStep, hr, State.addEdge])
        (pendant s.nextEdge σ (⟨s.active, ha⟩, true))
    | _ :: _ => resize (by simp only [kmswStep, hc, kmswStepOfStep, hr]) σ
  | .left => match hl : s.UL.dropLast.reverse with
    | [] => resize (by simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
        (leftFresh s.nextEdge σ (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true))
    | e :: es =>
      have he : e < s.nextEdge := hu e (List.dropLast_subset _
        (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
      resize (by simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
        (leftExisting s.nextEdge σ (⟨e, he⟩, false) (⟨s.active, ha⟩, true))
  | .up => resize (by simp only [kmswStep, hc, kmswStepOfStep, State.addEdge])
      (up s.nextEdge σ (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true))

/-- Activation changes no rotation successors (`def-kmsw`, -/
theorem step_activation (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3) (hc : kmswCodeStep c = .down) (e : ℕ) (es : List ℕ)
    (hr : s.UR = e :: es) :
    resize (by simp only [kmswStep, hc, kmswStepOfStep, hr]) (step s ha hu σ c) = σ := by
  unfold step
  split
  next hc' =>
    split
    next hr' => cases hr.symm.trans hr'
    next head tail hr' => simp only [resize_resize, resize_self]
  next hc' => cases hc.symm.trans hc'
  next hc' => cases hc.symm.trans hc'

/-- Pendant branch of the rotation recursion (`def-kmsw`, -/
theorem step_pendant (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3) (hc : kmswCodeStep c = .down) (hr : s.UR = []) :
    resize (by simp only [kmswStep, hc, kmswStepOfStep, hr, State.addEdge])
      (step s ha hu σ c) = pendant s.nextEdge σ (⟨s.active, ha⟩, true) := by
  unfold step
  split
  next hc' =>
    split
    next hr' => simp only [resize_resize, resize_self]
    next head tail hr' => cases hr.symm.trans hr'
  next hc' => cases hc.symm.trans hc'
  next hc' => cases hc.symm.trans hc'

/-- Left branch with a predecessor (`def-kmsw`, -/
theorem step_leftExisting (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3) (hc : kmswCodeStep c = .left) (e : ℕ) (es : List ℕ)
    (hl : s.UL.dropLast.reverse = e :: es) :
    resize (by simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
      (step s ha hu σ c) = leftExisting s.nextEdge σ
        (⟨e, hu e (List.dropLast_subset _
          (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))⟩, false)
        (⟨s.active, ha⟩, true) := by
  unfold step
  split
  next hc' => cases hc.symm.trans hc'
  next hc' =>
    split
    next hl' => cases hl.symm.trans hl'
    next head tail hl' =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj (hl.symm.trans hl')
      simp only [resize_resize, resize_self]
  next hc' => cases hc.symm.trans hc'

/-- `leftFresh_old/new` give all successors. -/
theorem step_leftFresh (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3) (hc : kmswCodeStep c = .left) (hl : s.UL.dropLast.reverse = []) :
    resize (by simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
      (step s ha hu σ c) =
      leftFresh s.nextEdge σ (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true) := by
  unfold step
  split
  next hc' => cases hc.symm.trans hc'
  next hc' =>
    split
    next hl' => simp only [resize_resize, resize_self]
    next head tail hl' => cases hl.symm.trans hl'
  next hc' => cases hc.symm.trans hc'

/-- `up_old/new` give all successors. -/
theorem step_up (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3) (hc : kmswCodeStep c = .up) :
    resize (by simp only [kmswStep, hc, kmswStepOfStep, State.addEdge])
      (step s ha hu σ c) =
      up s.nextEdge σ (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true) := by
  unfold step
  split
  next hc' => cases hc.symm.trans hc'
  next hc' => cases hc.symm.trans hc'
  next hc' => simp only [resize_resize, resize_self]

end StageRotation

/-- Upper-left IDs used by the rotation recursion are allocated (`def-kmsw`, -/
theorem stageRotation_UL_bound (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e ∈ (kmswStage w n).UL, e < (kmswStage w n).nextEdge := by
  intro e he
  rw [kmswStage_UL_eq] at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  have hm' : m < n + 1 := List.mem_range.mp (List.mem_filter.mp hm).1
  exact act_lt_nextEdge w (by omega)

/-- Recursive rotation system of `def-kmsw`, -/
@[expose] def stageRot (w : ℕ → Fin 3) :
    (n : ℕ) → Equiv.Perm (StageDart (kmswStage w n).nextEdge)
  | 0 => 1
  | n + 1 => StageRotation.step (kmswStage w n)
      (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n) (w n)

/-- Initial singleton vertex rotations (`def-kmsw`, -/
theorem stageRot_zero (w : ℕ → Fin 3) : stageRot w 0 = 1 := rfl

/-- Recursion equation; the five `StageRotation.step_*` lemmas select its
branch, and the old/new tables evaluate every dart (`def-kmsw`, -/
theorem stageRot_succ (w : ℕ → Fin 3) (n : ℕ) :
    stageRot w (n + 1) = StageRotation.step (kmswStage w n)
      (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n) (w n) := rfl

/-- Raw combinatorial map at each stage of `def-kmsw`, -/
@[expose] def kmswMap (w : ℕ → Fin 3) (n : ℕ) :
    PlanarMap.CombinatorialMap (StageDart (kmswStage w n).nextEdge) where
  edgeInv := edgeFlip _
  edgeInv_invol := by rintro ⟨e, b⟩; cases b <;> rfl
  edgeInv_ne := by
    rintro ⟨e, b⟩ h
    have hb := congrArg Prod.snd h
    cases b <;> cases hb
  rot := stageRot w n

/-- The bundled map has precisely the constructed rotation (`def-kmsw`, -/
theorem kmswMap_rot (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMap w n).rot = stageRot w n := rfl

/-- The bundled map keeps each geometric edge's two darts paired (`def-kmsw`, -/
theorem kmswMap_edgeInv (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMap w n).edgeInv = edgeFlip (kmswStage w n).nextEdge := rfl

end DirectedDistances.KMSW
