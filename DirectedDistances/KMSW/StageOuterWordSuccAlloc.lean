/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageOuterWord

import DirectedDistances.KMSW.StageOuterWordSucc

/-! # Outer-word successor at allocated KMSW steps

The up and empty-upper-right down steps preserve the face-successor
description of the ordered outer word (`def-kmsw`, -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem outerSuccAlloc_dartVal_injective (k : ℕ) :
    Function.Injective (fun d : StageDart k => (d.1.val, d.2)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h₁, h₂⟩
  cases Fin.ext h₁
  cases h₂
  rfl

private theorem outerSuccAlloc_formPerm_apply_mem_eq_next (α : Type*) [DecidableEq α]
    (l : List α) (hl : l.Nodup) (x : α) (hx : x ∈ l) :
    l.formPerm x = l.next x hx := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem _ hl, List.formPerm_apply_getElem _ hl]

private theorem outerSuccAlloc_faceSucc_eq_of_rot {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (d x : D) (h : M.rot x = M.edgeInv d) :
    M.faceSucc d = x := by
  change M.rot.symm (M.edgeInv d) = x
  rw [← h, M.rot.symm_apply_apply]

private theorem outerSuccAlloc_faceSucc_transport {k l : ℕ} (h : k ≤ l)
    (M : CombinatorialMap (StageDart k)) (N : CombinatorialMap (StageDart l))
    (oldWord : List (StageDart k)) (newWord : List (StageDart l))
    (hprev : ∀ d ∈ oldWord, M.faceSucc d = oldWord.formPerm d)
    (d : StageDart k) (hd : d ∈ oldWord)
    (hform : newWord.formPerm (outerSucc_castDart h d) =
      outerSucc_castDart h (oldWord.formPerm d))
    (hrot : N.rot (outerSucc_castDart h (M.faceSucc d)) =
      outerSucc_castDart h (M.rot (M.faceSucc d)))
    (hedge : N.edgeInv (outerSucc_castDart h d) = outerSucc_castDart h (M.edgeInv d)) :
    N.faceSucc (outerSucc_castDart h d) = newWord.formPerm (outerSucc_castDart h d) := by
  calc
    N.faceSucc (outerSucc_castDart h d) = outerSucc_castDart h (M.faceSucc d) :=
      outerSucc_faceSucc_castLE_of_local h M N d hrot hedge
    _ = outerSucc_castDart h (oldWord.formPerm d) := congrArg _ (hprev d hd)
    _ = newWord.formPerm (outerSucc_castDart h d) := hform.symm

private theorem outerSuccAlloc_edgeInv_cast {w : ℕ → Fin 3} {n : ℕ}
    (h : (kmswStage w n).nextEdge ≤ (kmswStage w (n + 1)).nextEdge)
    (d : StageDart (kmswStage w n).nextEdge) :
    (kmswMap w (n + 1)).edgeInv (outerSucc_castDart h d) =
      outerSucc_castDart h ((kmswMap w n).edgeInv d) := by
  rw [kmswMap_edgeInv, kmswMap_edgeInv]
  cases d with
  | mk e b => cases b <;> rfl

private theorem outerSuccAlloc_rot_faceSucc {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (d : D) :
    M.rot (M.faceSucc d) = M.edgeInv d := by
  change M.rot (M.rot.symm (M.edgeInv d)) = M.edgeInv d
  exact M.rot.apply_symm_apply _

private theorem outerSuccAlloc_dropLast_append_of_ne_nil {α : Type*}
    (xs ys : List α) (hys : ys ≠ []) :
    (xs ++ ys).dropLast = xs ++ ys.dropLast := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => exact (hys rfl).elim
    | cons y ys =>
      have hnonempty : xs ++ y :: ys ≠ [] := by simp
      change (x :: (xs ++ (y :: ys))).dropLast = x :: (xs ++ (y :: ys).dropLast)
      rw [List.dropLast_cons_of_ne_nil hnonempty, ih (y :: ys) (by simp)]

private theorem outerSuccAlloc_next_prepend {α : Type*} [DecidableEq α] (pref tail : List α)
    (htail : tail ≠ []) (x : α) (hx : x ∈ tail.dropLast)
    (hdisj : ∀ y ∈ pref, x ≠ y) :
    (pref ++ tail).next x (List.mem_append_right _ (List.mem_of_mem_dropLast hx)) =
      tail.next x (List.mem_of_mem_dropLast hx) := by
  induction pref with
  | nil => rfl
  | cons y pref ih =>
    have hmem : x ∈ (pref ++ tail).dropLast := by
      rw [outerSuccAlloc_dropLast_append_of_ne_nil pref tail htail]
      exact List.mem_append_right _ hx
    have hxy : x ≠ y := hdisj y (List.mem_cons_self ..)
    change (y :: (pref ++ tail)).next x _ = tail.next x _
    rw [List.next_cons_eq_next_of_mem_dropLast (l := pref ++ tail) (x := x) hmem y hxy]
    exact ih (fun z hz => hdisj z (List.mem_cons_of_mem _ hz))

private theorem outerSuccAlloc_formPerm_tail_internal {α : Type*} [DecidableEq α]
    (pref tail : List α) (htail : tail ≠ []) (x : α) (hx : x ∈ tail.dropLast)
    (hnd : (pref ++ tail).Nodup) :
    (pref ++ tail).formPerm x = tail.next x (List.mem_of_mem_dropLast hx) := by
  rw [outerSuccAlloc_formPerm_apply_mem_eq_next _ _ hnd _
    (List.mem_append_right _ (List.mem_of_mem_dropLast hx))]
  exact outerSuccAlloc_next_prepend pref tail htail x hx (by
    intro y hy
    have hdisj := List.disjoint_of_nodup_append hnd
    intro hxy
    subst y
    exact (List.disjoint_left.mp hdisj) hy (List.mem_of_mem_dropLast hx))

private theorem outerSuccAlloc_formPerm_tail_last {α : Type*} [DecidableEq α]
    (pref tail : List α) (hpref : pref ≠ []) (htail : tail ≠ [])
    (hnd : (pref ++ tail).Nodup) :
    (pref ++ tail).formPerm (tail.getLast htail) = pref.head hpref := by
  have hwhole : pref ++ tail ≠ [] := by simp [htail]
  have hlast : (pref ++ tail).getLast hwhole = tail.getLast htail :=
    List.getLast_append_of_right_ne_nil pref tail htail
  have hnext := List.next_getLast_eq_head (pref ++ tail) hwhole hnd
  have hmem : tail.getLast htail ∈ pref ++ tail := List.mem_append_right _ (List.getLast_mem htail)
  rw [outerSuccAlloc_formPerm_apply_mem_eq_next _ _ hnd _ hmem]
  have hhead : (pref ++ tail).head hwhole = pref.head hpref := by simp [hpref]
  simpa only [hlast, hhead] using hnext

private theorem outerSuccAlloc_formPerm_anchor {α : Type*} [DecidableEq α]
    (a : α) (tail : List α) (htail : tail ≠ []) (hnd : (a :: tail).Nodup) :
    (a :: tail).formPerm a = tail.head htail := by
  have hx : a ∈ a :: tail := List.mem_cons_self
  have hlen : 1 < (a :: tail).length := by
    cases tail with
    | nil => exact (htail rfl).elim
    | cons b bs => simp
  have h := List.formPerm_apply_lt_getElem (a :: tail) hnd 0 (by omega)
  have h0 : 0 < tail.length := List.length_pos_iff.mpr htail
  have hhead : tail[0]'h0 = tail.head htail := by
    cases tail with
    | nil => exact (htail rfl).elim
    | cons b bs => rfl
  simpa [hhead] using h

private theorem outerSuccAlloc_formPerm_up_head {α : Type*} [DecidableEq α]
    (p q : α) (tail : List α) (htail : tail ≠ [])
    (hnd : (p :: q :: tail).Nodup) :
    (p :: q :: tail).formPerm p = q ∧
      (p :: q :: tail).formPerm q = tail.head htail := by
  have hp : p ∈ p :: q :: tail := List.mem_cons_self
  have hq : q ∈ p :: q :: tail := by simp
  constructor
  · exact List.formPerm_apply_head _ _ _ hnd
  · have hlen : 2 < (p :: q :: tail).length := by
      cases tail with
      | nil => exact (htail rfl).elim
      | cons b bs => simp
    have h := List.formPerm_apply_lt_getElem (p :: q :: tail) hnd 1 (by omega)
    have h0 : 0 < tail.length := List.length_pos_iff.mpr htail
    have hhead : tail[0]'h0 = tail.head htail := by
      cases tail with
      | nil => exact (htail rfl).elim
      | cons b bs => rfl
    simpa [hhead] using h

private theorem outerSuccAlloc_formPerm_pendant_head {α : Type*} [DecidableEq α]
    (a p q : α) (tail : List α) (htail : tail ≠ [])
    (hnd : (a :: p :: q :: tail).Nodup) :
    (a :: p :: q :: tail).formPerm a = p ∧
      (a :: p :: q :: tail).formPerm p = q ∧
      (a :: p :: q :: tail).formPerm q = tail.head htail := by
  have ha : a ∈ a :: p :: q :: tail := List.mem_cons_self
  have hp : p ∈ a :: p :: q :: tail := by simp
  have hq : q ∈ a :: p :: q :: tail := by simp
  refine ⟨?_, ?_, ?_⟩
  · have hlen : 1 < (a :: p :: q :: tail).length := by
      cases tail with
      | nil => simp
      | cons b bs => simp
    have h := List.formPerm_apply_lt_getElem (a :: p :: q :: tail) hnd 0 (by omega)
    simpa using h
  · have hlen : 2 < (a :: p :: q :: tail).length := by
      cases tail with
      | nil => simp
      | cons b bs => simp
    have h := List.formPerm_apply_lt_getElem (a :: p :: q :: tail) hnd 1 (by omega)
    simpa using h
  · have hlen : 3 < (a :: p :: q :: tail).length := by
      cases tail with
      | nil => exact (htail rfl).elim
      | cons b bs => simp
    have h := List.formPerm_apply_lt_getElem (a :: p :: q :: tail) hnd 2 (by omega)
    have h0 : 0 < tail.length := List.length_pos_iff.mpr htail
    have hhead : tail[0]'h0 = tail.head htail := by
      cases tail with
      | nil => exact (htail rfl).elim
      | cons b bs => rfl
    simpa [hhead] using h

private theorem outerSuccAlloc_formPerm_tail_up {α : Type*} [DecidableEq α]
    (a p q : α) (tail : List α) (htail : tail ≠ [])
    (hold : (a :: tail).Nodup) (hnew : (p :: q :: tail).Nodup)
    (x : α) (hx : x ∈ tail) :
    (p :: q :: tail).formPerm x =
      if x = tail.getLast htail then p else (a :: tail).formPerm x := by
  by_cases hlast : x = tail.getLast htail
  · subst x
    change ([p, q] ++ tail).formPerm (tail.getLast htail) =
      if tail.getLast htail = tail.getLast htail then p else
        ([a] ++ tail).formPerm (tail.getLast htail)
    have hp := outerSuccAlloc_formPerm_tail_last [p, q] tail (by simp) htail hnew
    have ha := outerSuccAlloc_formPerm_tail_last [a] tail (by simp) htail hold
    rw [hp, ha]
    simp
  · have hdrop : x ∈ tail.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hx hlast
    change ([p, q] ++ tail).formPerm x =
      if x = tail.getLast htail then p else ([a] ++ tail).formPerm x
    simp only [ite_eq_right hlast]
    have hp := outerSuccAlloc_formPerm_tail_internal [p, q] tail htail x hdrop hnew
    have ha := outerSuccAlloc_formPerm_tail_internal [a] tail htail x hdrop hold
    simpa using hp.trans ha.symm

private theorem outerSuccAlloc_formPerm_tail_pendant {α : Type*} [DecidableEq α]
    (a p q : α) (tail : List α) (htail : tail ≠ [])
    (hold : (a :: tail).Nodup) (hnew : (a :: p :: q :: tail).Nodup)
    (x : α) (hx : x ∈ tail) :
    (a :: p :: q :: tail).formPerm x = (a :: tail).formPerm x := by
  by_cases hlast : x = tail.getLast htail
  · subst x
    have hp := outerSuccAlloc_formPerm_tail_last [a, p, q] tail (by simp) htail hnew
    have ha := outerSuccAlloc_formPerm_tail_last [a] tail (by simp) htail hold
    change ([a, p, q] ++ tail).formPerm (tail.getLast htail) =
      ([a] ++ tail).formPerm (tail.getLast htail)
    rw [hp, ha]
    simp
  · have hdrop : x ∈ tail.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hx hlast
    change ([a, p, q] ++ tail).formPerm x = _
    have hp := outerSuccAlloc_formPerm_tail_internal [a, p, q] tail htail x hdrop hnew
    have ha := outerSuccAlloc_formPerm_tail_internal [a] tail htail x hdrop hold
    calc
      (a :: p :: q :: tail).formPerm x = tail.next x (List.mem_of_mem_dropLast hdrop) := by
        simpa using hp
      _ = (a :: tail).formPerm x := by simpa using ha.symm

private theorem outerSuccAlloc_formPerm_map_injective {α β : Type*} [DecidableEq α]
    [DecidableEq β] (f : α → β) (hf : Function.Injective f) (l : List α)
    (hl : l.Nodup) (x : α) (hx : x ∈ l) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  have hl' : (l.map f).Nodup := hl.map hf
  have hmem : f x ∈ l.map f := List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [outerSuccAlloc_formPerm_apply_mem_eq_next _ _ hl' _ hmem,
    outerSuccAlloc_formPerm_apply_mem_eq_next _ _ hl _ hx]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have himap : i < (l.map f).length := by simpa using hi
  have hmap : (l.map f)[i]'himap = f l[i] := by simp
  have hnextmap := List.next_getElem (l.map f) hl' i himap
  have hnextmap' : (l.map f).next (f l[i]) hmem =
      (l.map f)[(i + 1) % (l.map f).length]'(Nat.mod_lt _ (i.zero_le.trans_lt himap)) := by
    simpa only [hmap] using hnextmap
  rw [hnextmap', List.next_getElem _ hl i hi]
  simp

private def outerSuccAlloc_castLE {k l : ℕ} (h : k ≤ l) (d : StageDart k) :
    StageDart l := (d.1.castLE h, d.2)

private def outerSuccAlloc_castEq {k l : ℕ} (h : k = l) (d : StageDart k) :
    StageDart l := h ▸ d

private theorem outerSuccAlloc_resize_apply {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) (d : StageDart l) :
    StageRotation.resize h σ d =
      outerSuccAlloc_castEq h (σ (outerSuccAlloc_castEq h.symm d)) := by
  cases h
  rfl

private theorem outerSuccAlloc_castLE_eq_castEq {k l : ℕ} (h : k = l)
    (hle : k ≤ l) (d : StageDart k) :
    outerSuccAlloc_castLE hle d = outerSuccAlloc_castEq h d := by
  cases h
  simp [outerSuccAlloc_castLE, outerSuccAlloc_castEq]

private theorem outerSuccAlloc_castLE_val {k l : ℕ} (h : k ≤ l)
    (d : StageDart k) :
    ((outerSuccAlloc_castLE h d).1.val, (outerSuccAlloc_castLE h d).2) = (d.1.val, d.2) := by
  simp [outerSuccAlloc_castLE]

private theorem outerSuccAlloc_castLE_injective {k l : ℕ} (h : k ≤ l) :
    Function.Injective (outerSuccAlloc_castLE h : StageDart k → StageDart l) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ hxy
  have hx : x = y := Fin.castLE_injective h (congrArg Prod.fst hxy)
  have hb : b = c := congrArg Prod.snd hxy
  cases hx
  cases hb
  rfl

private theorem outerSuccAlloc_castDart_injective {k l : ℕ} (h : k ≤ l) :
    Function.Injective (outerSucc_castDart h : StageDart k → StageDart l) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ hxy
  have hx : x = y := Fin.castLE_injective h (congrArg Prod.fst hxy)
  have hb : b = c := congrArg Prod.snd hxy
  cases hx
  cases hb
  rfl

private theorem outerSuccAlloc_castDart_val {k l : ℕ} (h : k ≤ l)
    (d : StageDart k) :
    ((outerSucc_castDart h d).1.val, (outerSucc_castDart h d).2) = (d.1.val, d.2) := by
  cases d with
  | mk e b => simp [outerSucc_castDart]

private theorem outerSuccAlloc_castWord_val {k l : ℕ} (h : k ≤ l)
    (xs : List (StageDart k)) :
    (xs.map (outerSucc_castDart h)).map (fun d => (d.1.val, d.2)) =
      xs.map (fun d => (d.1.val, d.2)) := by
  induction xs with
  | nil => rfl
  | cons d ds ih =>
    have hhead : ((outerSucc_castDart h d).1.val, (outerSucc_castDart h d).2) =
        (d.1.val, d.2) := by
      simp [outerSucc_castDart]
    simp only [List.map_cons, hhead, ih]

private theorem outerSuccAlloc_resize_proof_irrel {k l : ℕ} (h h' : k = l)
    (σ : Equiv.Perm (StageDart k)) : StageRotation.resize h σ = StageRotation.resize h' σ := by
  cases h
  cases h'
  rfl

private theorem outerSuccAlloc_resize_resize {k l m : ℕ} (h : k = l) (h' : l = m)
    (σ : Equiv.Perm (StageDart k)) :
    StageRotation.resize h' (StageRotation.resize h σ) =
      StageRotation.resize (h.trans h') σ := by
  cases h
  cases h'
  rfl

private theorem outerSuccAlloc_resize_self {k : ℕ} (h : k = k)
    (σ : Equiv.Perm (StageDart k)) : StageRotation.resize h σ = σ := by
  cases h
  rfl

private theorem outerSuccAlloc_resize_eq_apply {k l : ℕ} (h : k = l)
    (ρ : Equiv.Perm (StageDart k)) (σ : Equiv.Perm (StageDart l))
    (hρ : StageRotation.resize h ρ = σ) (x : StageDart l) :
    ρ (outerSuccAlloc_castEq h.symm x) = outerSuccAlloc_castEq h.symm (σ x) := by
  cases h
  have hpoint := congrArg (fun p : Equiv.Perm (StageDart k) => p x) hρ
  simpa [StageRotation.resize, outerSuccAlloc_castEq] using hpoint

private theorem outerSuccAlloc_castEq_symm_old {k l : ℕ} (hs : l = k + 2)
    (h : k ≤ l) (d : StageDart k) :
    outerSuccAlloc_castEq hs.symm
        (outerSucc_castDart (by omega : k ≤ k + 2) d) = outerSucc_castDart h d := by
  cases hs
  simp [outerSuccAlloc_castEq, outerSucc_castDart]

private theorem outerSuccAlloc_castEq_symm_allocation_old {k l : ℕ}
    (hs : l = k + 2) (h : k ≤ l) (d : StageDart k) :
    outerSuccAlloc_castEq hs.symm (StageRotation.allocation k 2 (.inl d)) =
      outerSucc_castDart h d := by
  rw [outerSucc_allocation_old k 2 (by omega)]
  exact outerSuccAlloc_castEq_symm_old hs h d

private theorem outerSuccAlloc_castEq_symm_allocation_new {k l : ℕ}
    (hs : l = k + 2) (e : Fin 2) (b : Bool) :
    outerSuccAlloc_castEq hs.symm (StageRotation.allocation k 2 (.inr (e, b))) =
      (⟨k + e.val, by omega⟩, b) := by
  rw [StageRotation.allocation_new]
  cases hs
  simp [outerSuccAlloc_castEq]

private theorem outerSuccAlloc_castEq_symm_allocation_new_one {k l : ℕ}
    (hs : l = k + 1) (e : Fin 1) (b : Bool) :
    outerSuccAlloc_castEq hs.symm (StageRotation.allocation k 1 (.inr (e, b))) =
      (⟨k + e.val, by omega⟩, b) := by
  rw [StageRotation.allocation_new]
  cases hs
  simp [outerSuccAlloc_castEq]

private theorem outerSuccAlloc_castEq_symm_old_one {k l : ℕ} (hs : l = k + 1)
    (h : k ≤ l) (d : StageDart k) :
    outerSuccAlloc_castEq hs.symm
        (outerSucc_castDart (by omega : k ≤ k + 1) d) = outerSucc_castDart h d := by
  cases hs
  simp [outerSuccAlloc_castEq, outerSucc_castDart]

private theorem outerSuccAlloc_castEq_symm_allocation_old_one {k l : ℕ}
    (hs : l = k + 1) (h : k ≤ l) (d : StageDart k) :
    outerSuccAlloc_castEq hs.symm (StageRotation.allocation k 1 (.inl d)) =
      outerSucc_castDart h d := by
  rw [outerSucc_allocation_old k 1 (by omega)]
  exact outerSuccAlloc_castEq_symm_old_one hs h d

private theorem outerSuccAlloc_up_rot_old {k l : ℕ} (hs : l = k + 2)
    (h : k ≤ l) (ρ : Equiv.Perm (StageDart l)) (σ : Equiv.Perm (StageDart k))
    (a A d : StageDart k)
    (hresize : StageRotation.resize hs ρ = StageRotation.up k σ a A) :
    ρ (outerSucc_castDart h d) =
      if d = a then
        outerSuccAlloc_castEq hs.symm (StageRotation.allocation k 2 (.inr (0, false)))
      else if σ d = A then
        outerSuccAlloc_castEq hs.symm (StageRotation.allocation k 2 (.inr (1, true)))
      else outerSucc_castDart h (σ d) := by
  have hpoint := outerSuccAlloc_resize_eq_apply hs ρ (StageRotation.up k σ a A)
    hresize (StageRotation.allocation k 2 (.inl d))
  rw [outerSuccAlloc_castEq_symm_allocation_old hs h d,
    StageRotation.up_old] at hpoint
  by_cases hd : d = a
  · subst d
    simpa [outerSuccAlloc_castEq_symm_allocation_new] using hpoint
  · by_cases hσ : σ d = A
    · simpa [hd, hσ, outerSuccAlloc_castEq_symm_allocation_new] using hpoint
    · simp only [ite_eq_right hd, ite_eq_right hσ] at hpoint
      rw [outerSuccAlloc_castEq_symm_allocation_old hs h (σ d)] at hpoint
      simpa [hd, hσ] using hpoint

private theorem outerSuccAlloc_pendant_rot_old {k l : ℕ} (hs : l = k + 1)
    (h : k ≤ l) (ρ : Equiv.Perm (StageDart l)) (σ : Equiv.Perm (StageDart k))
    (A d : StageDart k)
    (hresize : StageRotation.resize hs ρ = StageRotation.pendant k σ A) :
    ρ (outerSucc_castDart h d) =
      if σ d = A then
        outerSuccAlloc_castEq hs.symm (StageRotation.allocation k 1 (.inr (0, false)))
      else outerSucc_castDart h (σ d) := by
  have hpoint := outerSuccAlloc_resize_eq_apply hs ρ (StageRotation.pendant k σ A)
    hresize (StageRotation.allocation k 1 (.inl d))
  rw [outerSuccAlloc_castEq_symm_allocation_old_one hs h d,
    StageRotation.pendant_old] at hpoint
  by_cases hσ : σ d = A
  · simp [hσ] at hpoint ⊢
    exact hpoint
  · simp only [ite_eq_right hσ] at hpoint
    rw [outerSuccAlloc_castEq_symm_allocation_old_one hs h (σ d)] at hpoint
    simpa [hσ] using hpoint

private theorem outerSuccAlloc_UL_last (w : ℕ → Fin 3) (n : ℕ) :
    let s := kmswStage w n
    s.UL.dropLast ++ [s.active] = s.UL := by
  dsimp only
  let s := kmswStage w n
  have hne : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last w n).1
  have hlast : s.UL.getLast hne = s.active := by
    have h := (kmswStage_UL_nonempty_active_last w n).2
    change s.UL.getLast? = some s.active at h
    rw [List.getLast?_eq_getLast_of_ne_nil hne] at h
    exact Option.some.inj h
  rw [← hlast]
  exact List.dropLast_append_getLast hne

private theorem outerSuccAlloc_allocation_old (k r : ℕ) (d : StageDart k) :
    StageRotation.allocation k r (.inl d) = outerSuccAlloc_castLE (by omega) d := by
  apply Prod.ext
  · apply Fin.ext
    rfl
  · rfl

private theorem outerSuccAlloc_allocation_new (k r : ℕ) (e : Fin r) (b : Bool) :
    StageRotation.allocation k r (.inr (e, b)) = (⟨k + e.val, by omega⟩, b) :=
  StageRotation.allocation_new k r e b

private def outerSuccAlloc_ulPrefix (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  exact stageDarts s s.UL.dropLast false (fun e he =>
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      have he' : e ∈ s.UL := List.mem_of_mem_dropLast he
      simp only [List.mem_append]
      tauto))

private def outerSuccAlloc_urRun (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  exact stageDarts s s.UR false (fun e he =>
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      tauto))

private def outerSuccAlloc_lrRun (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  exact stageDarts s s.LR.reverse true (fun e he =>
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      have he' := List.mem_reverse.mp he
      simp only [List.mem_append]
      tauto))

private def outerSuccAlloc_llRun (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  exact stageDarts s s.LL.reverse true (fun e he =>
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      have he' := List.mem_reverse.mp he
      simp only [List.mem_append]
      tauto))

private def outerSuccAlloc_wordTail (w : ℕ → Fin 3) (n : ℕ) :=
  outerSuccAlloc_urRun w n ++ outerSuccAlloc_lrRun w n ++ outerSuccAlloc_llRun w n

private def outerSuccAlloc_activeWest (w : ℕ → Fin 3) (n : ℕ) :
    StageDart (kmswStage w n).nextEdge :=
  ((⟨(kmswStage w n).active, act_lt_nextEdge w (le_refl n)⟩), false)

private theorem outerSuccAlloc_ulPrefix_val (w : ℕ → Fin 3) (n : ℕ) :
    (outerSuccAlloc_ulPrefix w n).map (fun d => (d.1.val, d.2)) =
      ((kmswStage w n).UL.dropLast.map fun e => (e, false)) := by
  unfold outerSuccAlloc_ulPrefix
  exact stageDarts_val _ _ _ _

private theorem outerSuccAlloc_urRun_val (w : ℕ → Fin 3) (n : ℕ) :
    (outerSuccAlloc_urRun w n).map (fun d => (d.1.val, d.2)) =
      ((kmswStage w n).UR.map fun e => (e, false)) := by
  unfold outerSuccAlloc_urRun
  exact stageDarts_val _ _ _ _

private theorem outerSuccAlloc_lrRun_val (w : ℕ → Fin 3) (n : ℕ) :
    (outerSuccAlloc_lrRun w n).map (fun d => (d.1.val, d.2)) =
      ((kmswStage w n).LR.reverse.map fun e => (e, true)) := by
  unfold outerSuccAlloc_lrRun
  exact stageDarts_val _ _ _ _

private theorem outerSuccAlloc_llRun_val (w : ℕ → Fin 3) (n : ℕ) :
    (outerSuccAlloc_llRun w n).map (fun d => (d.1.val, d.2)) =
      ((kmswStage w n).LL.reverse.map fun e => (e, true)) := by
  unfold outerSuccAlloc_llRun
  exact stageDarts_val _ _ _ _

private theorem outerSuccAlloc_wordTail_val (w : ℕ → Fin 3) (n : ℕ) :
    (outerSuccAlloc_wordTail w n).map (fun d => (d.1.val, d.2)) =
      (((kmswStage w n).UR.map fun e => (e, false)) ++
        ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
        ((kmswStage w n).LL.reverse.map fun e => (e, true))) := by
  simp only [outerSuccAlloc_wordTail, List.map_append, outerSuccAlloc_urRun_val,
    outerSuccAlloc_lrRun_val, outerSuccAlloc_llRun_val]

private theorem outerSuccAlloc_stageDarts_ne_nil (s : State) (es : List ℕ)
    (side : Bool) (hes : ∀ e ∈ es, e < s.nextEdge) (hne : es ≠ []) :
    stageDarts s es side hes ≠ [] := by
  cases es with
  | nil => exact (hne rfl).elim
  | cons e es => simp [stageDarts]

private theorem outerSuccAlloc_wordTail_ne_nil (w : ℕ → Fin 3) (n : ℕ) :
    outerSuccAlloc_wordTail w n ≠ [] := by
  have hLR : (kmswStage w n).LR.reverse ≠ [] := by
    simpa using (kmswStage_LR_nonempty w n)
  have hlr : outerSuccAlloc_lrRun w n ≠ [] := by
    apply outerSuccAlloc_stageDarts_ne_nil
    · intro e he
      exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        have he' := List.mem_reverse.mp he
        simp only [List.mem_append]
        tauto)
    exact hLR
  simp [outerSuccAlloc_wordTail, hlr]

private theorem outerSuccAlloc_stageWord_split (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWord w n =
        outerSuccAlloc_ulPrefix w n ++
          (outerSuccAlloc_activeWest w n :: outerSuccAlloc_wordTail w n) := by
  apply (List.map_injective_iff.mpr (outerSuccAlloc_dartVal_injective _))
  calc
    (stageOuterWord w n).map (fun d => (d.1.val, d.2)) = stageOuterWordVal w n := rfl
    _ = ((kmswStage w n).UL.map fun e => (e, false)) ++
        ((kmswStage w n).UR.map fun e => (e, false)) ++
        ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
        ((kmswStage w n).LL.reverse.map fun e => (e, true)) :=
      stageOuterWordVal_eq_runs w n
    _ = (outerSuccAlloc_ulPrefix w n ++
        (outerSuccAlloc_activeWest w n :: outerSuccAlloc_wordTail w n)).map
          (fun d => (d.1.val, d.2)) := by
      have hUL : (kmswStage w n).UL.dropLast ++ [(kmswStage w n).active] =
          (kmswStage w n).UL := by
        simpa only using outerSuccAlloc_UL_last w n
      have hULMap : ((kmswStage w n).UL.map fun e => (e, false)) =
          ((kmswStage w n).UL.dropLast.map fun e => (e, false)) ++
            [((kmswStage w n).active, false)] := by
        have h := congrArg (fun xs : List ℕ => xs.map fun e => (e, false)) hUL
        simpa only [List.map_append, List.map_cons, List.map_nil] using h.symm
      simp only [List.map_append, List.map_cons, outerSuccAlloc_ulPrefix_val,
        outerSuccAlloc_wordTail_val]
      rw [hULMap]
      simp only [outerSuccAlloc_activeWest, List.cons_append, List.nil_append,
        List.append_assoc]

/-- Value form of the up-step splice in the outer word. The old active west
entry is replaced by the newly allocated west entries (`def-kmsw`, -/
theorem outerSuccAlloc_up_wordVal (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    stageOuterWordVal w (n + 1) =
      (((kmswStage w n).UL.dropLast.map fun e => (e, false)) ++
          [((kmswStage w n).nextEdge, false), ((kmswStage w n).nextEdge + 1, false)]) ++
        (((kmswStage w n).UR.map fun e => (e, false)) ++
          ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
          ((kmswStage w n).LL.reverse.map fun e => (e, true))) := by
  let s := kmswStage w n
  have hstep : kmswStage w (n + 1) = kmswStepOfStep s .up := by
    simp [s, kmswStage, kmswStep, kmswCodeStep, hc]
  rw [stageOuterWordVal_eq_runs w (n + 1), hstep]
  simp [s, kmswStepOfStep, State.addEdge, List.map_append, List.append_assoc]

/-- Value form of the pendant-step splice in the outer word when `UR` is
empty. The new edge's west and east entries follow the active west entry -/
theorem outerSuccAlloc_pendant_wordVal (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    stageOuterWordVal w (n + 1) =
      (((kmswStage w n).UL.map fun e => (e, false)) ++
          [((kmswStage w n).nextEdge, false), ((kmswStage w n).nextEdge, true)]) ++
        (((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
          ((kmswStage w n).LL.reverse.map fun e => (e, true))) := by
  let s := kmswStage w n
  have hstep : kmswStage w (n + 1) = kmswStepOfStep s .down := by
    simp [s, kmswStage, kmswStep, kmswCodeStep, hc]
  rw [stageOuterWordVal_eq_runs w (n + 1), hstep]
  simp [s, kmswStepOfStep, hUR, State.addEdge, List.map_append, List.append_assoc]

/-- An up step preserves the face-successor description of the outer word.
The two newly allocated west darts replace the old active west dart -/
theorem stageOuterWord_faceSucc_up (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (hprev : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) :
    ∀ d ∈ stageOuterWord w (n + 1),
      (kmswMap w (n + 1)).faceSucc d = (stageOuterWord w (n + 1)).formPerm d := by
  let s := kmswStage w n
  let k := s.nextEdge
  let M := kmswMap w n
  let N := kmswMap w (n + 1)
  let oldWord := stageOuterWord w n
  let newWord := stageOuterWord w (n + 1)
  let pref := outerSuccAlloc_ulPrefix w n
  let tail := outerSuccAlloc_wordTail w n
  let a : StageDart k := outerSuccAlloc_activeWest w n
  let A : StageDart k := (a.1, true)
  have hcode : kmswCodeStep (w n) = .up := by
    rw [hc]
    decide
  have hstep : kmswStage w (n + 1) = kmswStepOfStep s .up := by
    simp [s, kmswStage, kmswStep, kmswCodeStep, hc]
  have hsize : (kmswStage w (n + 1)).nextEdge = k + 2 := by
    rw [hstep]
    simp [k, kmswStepOfStep, State.addEdge]
  have hcast : k ≤ (kmswStage w (n + 1)).nextEdge := by omega
  let castD := outerSucc_castDart hcast
  let a' := castD a
  let P' := pref.map castD
  let T' := tail.map castD
  let p : StageDart (kmswStage w (n + 1)).nextEdge := ((⟨k, by omega⟩), false)
  let q : StageDart (kmswStage w (n + 1)).nextEdge := ((⟨k + 1, by omega⟩), false)
  let cyc := T' ++ P'
  let newList := P' ++ (p :: q :: T')
  have hsplit : oldWord = pref ++ (a :: tail) := by
    change stageOuterWord w n =
      outerSuccAlloc_ulPrefix w n ++
        (outerSuccAlloc_activeWest w n :: outerSuccAlloc_wordTail w n)
    exact outerSuccAlloc_stageWord_split w n
  have hnewWord : newWord = newList := by
    apply (List.map_injective_iff.mpr (outerSuccAlloc_dartVal_injective _))
    calc
      (stageOuterWord w (n + 1)).map (fun d => (d.1.val, d.2)) =
          stageOuterWordVal w (n + 1) := rfl
      _ = (((kmswStage w n).UL.dropLast.map fun e => (e, false)) ++
          [((kmswStage w n).nextEdge, false), ((kmswStage w n).nextEdge + 1, false)]) ++
          (((kmswStage w n).UR.map fun e => (e, false)) ++
            ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
            ((kmswStage w n).LL.reverse.map fun e => (e, true))) :=
        outerSuccAlloc_up_wordVal w n hc
      _ = newList.map (fun d => (d.1.val, d.2)) := by
        have hPval : P'.map (fun d => (d.1.val, d.2)) =
            (pref.map fun d => (d.1.val, d.2)) := by
          dsimp [P']
          exact outerSuccAlloc_castWord_val hcast pref
        have hPval' : P'.map (fun d => (d.1.val, d.2)) =
            ((kmswStage w n).UL.dropLast.map fun e => (e, false)) := by
          calc
            P'.map (fun d => (d.1.val, d.2)) = pref.map (fun d => (d.1.val, d.2)) := hPval
            _ = _ := outerSuccAlloc_ulPrefix_val w n
        have hTval : T'.map (fun d => (d.1.val, d.2)) =
            (((kmswStage w n).UR.map fun e => (e, false)) ++
              ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
              ((kmswStage w n).LL.reverse.map fun e => (e, true))) := by
          dsimp [T']
          calc
            (tail.map castD).map (fun d => (d.1.val, d.2)) =
                tail.map (fun d => (d.1.val, d.2)) := outerSuccAlloc_castWord_val hcast tail
            _ = _ := outerSuccAlloc_wordTail_val w n
        simp only [newList, List.map_append, List.map_cons, hPval', hTval]
        simp [p, q, k, s, List.append_assoc]
  have hcastSplit : oldWord.map castD = P' ++ (a' :: T') := by
    have h := congrArg (fun xs : List (StageDart k) => xs.map castD) hsplit
    simpa only [List.map_append, List.map_cons, List.map_nil] using h
  have htail : tail ≠ [] := outerSuccAlloc_wordTail_ne_nil w n
  have htailCast : T' ≠ [] := by
    cases ht : tail with
    | nil => exact False.elim (htail ht)
    | cons t ts => simp [T', ht]
  have hcyc : cyc ≠ [] := by
    intro hnil
    simp [cyc, List.append_eq_nil_iff] at hnil
    exact htailCast hnil.1
  have hOldCastNodup : (oldWord.map castD).Nodup :=
    (stageOuterWord_nodup w n).map (outerSuccAlloc_castDart_injective hcast)
  have hNewListNodup : newList.Nodup := by
    rw [← hnewWord]
    exact stageOuterWord_nodup w (n + 1)
  have hOldRotate : (oldWord.map castD).rotate P'.length = a' :: cyc := by
    calc
      (oldWord.map castD).rotate P'.length = (P' ++ (a' :: T')).rotate P'.length := by
        rw [hcastSplit]
      _ = (a' :: T') ++ P' := List.rotate_append_length_eq P' (a' :: T')
      _ = a' :: cyc := by simp [cyc, List.cons_append]
  have hNewRotate : newList.rotate P'.length = p :: q :: cyc := by
    calc
      newList.rotate P'.length = (P' ++ (p :: q :: T')).rotate P'.length := rfl
      _ = (p :: q :: T') ++ P' := List.rotate_append_length_eq P' (p :: q :: T')
      _ = p :: q :: cyc := by simp [cyc, List.cons_append]
  have hOldRotateNodup : (a' :: cyc).Nodup := by
    rw [← hOldRotate]
    simpa using hOldCastNodup
  have hNewRotateNodup : (p :: q :: cyc).Nodup := by
    rw [← hNewRotate]
    simpa using hNewListNodup
  have hOldForm : (a' :: cyc).formPerm = (oldWord.map castD).formPerm := by
    rw [← hOldRotate]
    exact List.formPerm_rotate (oldWord.map castD) hOldCastNodup P'.length
  have hNewForm : (p :: q :: cyc).formPerm = newWord.formPerm := by
    calc
      (p :: q :: cyc).formPerm = newList.formPerm := by
        rw [← hNewRotate]
        exact List.formPerm_rotate newList hNewListNodup P'.length
      _ = newWord.formPerm := by rw [← hnewWord]
  have hOldPred : (oldWord.map castD).formPerm (cyc.getLast hcyc) = a' := by
    rw [← hOldForm]
    simpa using outerSuccAlloc_formPerm_tail_last [a'] cyc (by simp) hcyc
      hOldRotateNodup
  have hAnchorNotCyc : a' ∉ cyc := (List.nodup_cons.mp hOldRotateNodup).1
  have hAedge : M.edgeInv a = A := by
    simp [M, a, A, outerSuccAlloc_activeWest, kmswMap_edgeInv, edgeFlip]
  have haOldMem : a ∈ oldWord := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hAnchorForm : (oldWord.map castD).formPerm a' = cyc.head hcyc := by
    calc
      (oldWord.map castD).formPerm a' = (a' :: cyc).formPerm a' := by
        rw [← hOldForm]
      _ = cyc.head hcyc := outerSuccAlloc_formPerm_anchor a' cyc hcyc hOldRotateNodup
  have hMapAnchor := outerSuccAlloc_formPerm_map_injective castD
    (outerSuccAlloc_castDart_injective hcast) oldWord (stageOuterWord_nodup w n) a haOldMem
  have hActiveSucc : M.faceSucc a = tail.head htail := by
    have hcastSucc : castD (M.faceSucc a) = cyc.head hcyc := by
      calc
        castD (M.faceSucc a) = castD (oldWord.formPerm a) := congrArg castD (hprev a haOldMem)
        _ = (oldWord.map castD).formPerm a' := hMapAnchor.symm
        _ = cyc.head hcyc := hAnchorForm
    have hhead : cyc.head hcyc = castD (tail.head htail) := by
            simp [cyc, T', tail, List.head_append_of_ne_nil, htailCast]
    have := (outerSuccAlloc_castDart_injective hcast) (hcastSucc.trans hhead)
    exact this
  have hRotTail : M.rot (tail.head htail) = A := by
    have h := outerSuccAlloc_rot_faceSucc M a
    rw [hActiveSucc] at h
    exact h.trans hAedge
  have hRotResizeStage :
      StageRotation.resize hsize (stageRot w (n + 1)) =
        StageRotation.up k (stageRot w n) a A := by
    rw [stageRot_succ]
    convert StageRotation.step_up s (act_lt_nextEdge w (le_refl n))
      (stageRotation_UL_bound w n) (stageRot w n) (w n) hcode using 1
    · exact outerSuccAlloc_resize_proof_irrel _ _ _
    · simp [k, s, a, A, outerSuccAlloc_activeWest]
  have hRotResize : StageRotation.resize hsize N.rot = StageRotation.up k M.rot a A := by
    change StageRotation.resize hsize (stageRot w (n + 1)) =
      StageRotation.up k (stageRot w n) a A
    simpa [k, s, a, A, outerSuccAlloc_activeWest] using hRotResizeStage
  have hTailUp (x : StageDart (kmswStage w (n + 1)).nextEdge) (hx : x ∈ cyc) :
      newWord.formPerm x =
        if x = cyc.getLast hcyc then p else (oldWord.map castD).formPerm x := by
    calc
      newWord.formPerm x = (p :: q :: cyc).formPerm x := by rw [hNewForm]
      _ = if x = cyc.getLast hcyc then p else (a' :: cyc).formPerm x :=
        outerSuccAlloc_formPerm_tail_up a' p q cyc hcyc hOldRotateNodup
          hNewRotateNodup x hx
      _ = if x = cyc.getLast hcyc then p else (oldWord.map castD).formPerm x := by
        rw [hOldForm]
  intro d hd
  have hdList : d ∈ newList := by
    rw [← hnewWord]
    exact hd
  change d ∈ newList at hdList
  rcases List.mem_append.mp hdList with hP | hrest
  · obtain ⟨dold, hdold, hEq⟩ := List.mem_map.mp hP
    have hEq' : d = castD dold := hEq.symm
    subst d
    have hxCyc : castD dold ∈ cyc := by
      simp only [cyc, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨dold, hdold, rfl⟩)
    have hdoldMem : dold ∈ oldWord := by
      rw [hsplit]
      exact List.mem_append_left _ hdold
    have hMapForm := outerSuccAlloc_formPerm_map_injective castD
      (outerSuccAlloc_castDart_injective hcast) oldWord (stageOuterWord_nodup w n)
      dold hdoldMem
    by_cases hlast : castD dold = cyc.getLast hcyc
    · have hOldA : oldWord.formPerm dold = a := by
        apply (outerSuccAlloc_castDart_injective hcast)
        calc
          castD (oldWord.formPerm dold) = (oldWord.map castD).formPerm (castD dold) := hMapForm.symm
          _ = (oldWord.map castD).formPerm (cyc.getLast hcyc) := by rw [hlast]
          _ = a' := hOldPred
          _ = castD a := rfl
      have hFace : M.faceSucc dold = a := by
        rw [hprev dold hdoldMem]
        exact hOldA
      have hda : dold ≠ a := by
        intro heq
        subst dold
        exact hAnchorNotCyc (by simpa using hxCyc)
      have hRotA : M.rot a = M.edgeInv dold := by
        have h := outerSuccAlloc_rot_faceSucc M dold
        rw [hFace] at h
        exact h
      have hSigmaA : M.rot a ≠ A := by
        intro heq
        apply hda
        apply M.edgeInv.injective
        calc
          M.edgeInv dold = M.rot a := hRotA.symm
          _ = A := heq
          _ = M.edgeInv a := hAedge.symm
      have hpEq : p = outerSuccAlloc_castEq hsize.symm
          (StageRotation.allocation k 2 (.inr (0, false))) := by
        simpa [p] using
          (outerSuccAlloc_castEq_symm_allocation_new hsize (0 : Fin 2) false).symm
      rcases StageRotation.up_new k M.rot a A with ⟨h0, h1, h2, h3⟩
      have hpoint := outerSuccAlloc_resize_eq_apply hsize N.rot
        (StageRotation.up k M.rot a A) hRotResize
        (StageRotation.allocation k 2 (.inr (0, false)))
      rw [← hpEq, h0, ite_eq_right hSigmaA,
        outerSuccAlloc_castEq_symm_allocation_old hsize hcast (M.rot a)] at hpoint
      have hRotPred : N.rot p = N.edgeInv (castD dold) := by
        calc
          N.rot p = castD (M.rot a) := hpoint
          _ = castD (M.edgeInv dold) := congrArg castD hRotA
          _ = N.edgeInv (castD dold) := (outerSuccAlloc_edgeInv_cast hcast dold).symm
      have hFacePred := outerSuccAlloc_faceSucc_eq_of_rot N (castD dold) p hRotPred
      have hFormPred : newWord.formPerm (castD dold) = p := by
        rw [← hNewForm]
        rw [outerSuccAlloc_formPerm_tail_up a' p q cyc hcyc hOldRotateNodup
              hNewRotateNodup (castD dold) hxCyc, ite_eq_left hlast]
      exact hFacePred.trans hFormPred.symm
    · have hOldFormNe : oldWord.formPerm dold ≠ a := by
        intro heq
        have hRotEq : (a' :: cyc).formPerm (castD dold) =
            (a' :: cyc).formPerm (cyc.getLast hcyc) := by
          calc
            (a' :: cyc).formPerm (castD dold) =
                (oldWord.map castD).formPerm (castD dold) := by rw [hOldForm]
            _ = castD (oldWord.formPerm dold) := hMapForm
            _ = a' := by rw [heq]
            _ = (oldWord.map castD).formPerm (cyc.getLast hcyc) := hOldPred.symm
            _ = (a' :: cyc).formPerm (cyc.getLast hcyc) := by rw [← hOldForm]
        have hEq := (a' :: cyc).formPerm.injective hRotEq
        exact hlast hEq
      have hFaceNe : M.faceSucc dold ≠ a := by
        intro heq
        apply hOldFormNe
        exact (hprev dold hdoldMem).symm.trans heq
      have hRotFace := outerSuccAlloc_rot_faceSucc M dold
      have hSigmaNe : M.rot (M.faceSucc dold) ≠ A := by
        intro heq
        have hDneqA : dold ≠ a := by
          intro hda
          subst dold
          exact hAnchorNotCyc (by simpa using hxCyc)
        apply hDneqA
        apply M.edgeInv.injective
        calc
          M.edgeInv dold = M.rot (M.faceSucc dold) := hRotFace.symm
          _ = A := heq
          _ = M.edgeInv a := hAedge.symm
      have hRotLocal : N.rot (castD (M.faceSucc dold)) =
          castD (M.rot (M.faceSucc dold)) := by
        rw [outerSuccAlloc_up_rot_old hsize hcast N.rot M.rot a A
          (M.faceSucc dold) hRotResize]
        simp only [castD, ite_eq_right hFaceNe, ite_eq_right hSigmaNe]
      have hform : newWord.formPerm (castD dold) =
          castD (oldWord.formPerm dold) := by
        calc
          newWord.formPerm (castD dold) = (p :: q :: cyc).formPerm (castD dold) := by
            rw [hNewForm]
          _ = (a' :: cyc).formPerm (castD dold) := by
            simpa [hlast] using
              (outerSuccAlloc_formPerm_tail_up a' p q cyc hcyc
                hOldRotateNodup hNewRotateNodup (castD dold) hxCyc)
          _ = (oldWord.map castD).formPerm (castD dold) := by rw [hOldForm]
          _ = castD (oldWord.formPerm dold) := hMapForm
      exact outerSuccAlloc_faceSucc_transport hcast M N oldWord newWord hprev
        dold hdoldMem hform hRotLocal (outerSuccAlloc_edgeInv_cast hcast dold)
  · rcases List.mem_cons.mp hrest with hp | hrest
    · subst d
      have hHeads := outerSuccAlloc_formPerm_up_head p q cyc hcyc hNewRotateNodup
      have hFormP : newWord.formPerm p = q := by
        rw [← hNewForm]
        exact hHeads.1
      have hqEq : q = outerSuccAlloc_castEq hsize.symm
          (StageRotation.allocation k 2 (.inr (1, false))) := by
        simpa [q] using
          (outerSuccAlloc_castEq_symm_allocation_new hsize (1 : Fin 2) false).symm
      rcases StageRotation.up_new k M.rot a A with ⟨h0, h1, h2, h3⟩
      have hpoint := outerSuccAlloc_resize_eq_apply hsize N.rot
        (StageRotation.up k M.rot a A) hRotResize
        (StageRotation.allocation k 2 (.inr (1, false)))
      rw [← hqEq, h3] at hpoint
      have heInvP : N.edgeInv p = (⟨k, by omega⟩, true) := by
        simp [N, p, kmswMap_edgeInv, edgeFlip]
      have hrotQ : N.rot q = N.edgeInv p := by
        calc
          N.rot q = outerSuccAlloc_castEq hsize.symm
              (StageRotation.allocation k 2 (.inr (0, true))) := hpoint
          _ = (⟨k, by omega⟩, true) := by
            simpa using
              (outerSuccAlloc_castEq_symm_allocation_new hsize (0 : Fin 2) true)
          _ = N.edgeInv p := heInvP.symm
      exact (outerSuccAlloc_faceSucc_eq_of_rot N p q hrotQ).trans hFormP.symm
    · rcases List.mem_cons.mp hrest with hq | htail
      · subst d
        have hHeads := outerSuccAlloc_formPerm_up_head p q cyc hcyc hNewRotateNodup
        have hFormQ : newWord.formPerm q = cyc.head hcyc := by
          rw [← hNewForm]
          exact hHeads.2
        have hTailMem : tail.head htail ∈ oldWord := by
          rw [hsplit]
          exact List.mem_append_right _ (List.mem_cons_of_mem _
            (List.head_mem htail))
        have hMapTailHead := outerSuccAlloc_formPerm_map_injective castD
          (outerSuccAlloc_castDart_injective hcast) oldWord
          (stageOuterWord_nodup w n) (tail.head htail) hTailMem
        have hTailHeadEq : cyc.head hcyc = castD (tail.head htail) := by
          simp [cyc, T', tail, List.head_append_of_ne_nil, htailCast]
        have hActiveForm : (oldWord.map castD).formPerm a' = cyc.head hcyc := hAnchorForm
        have hFaceActive : M.faceSucc a = tail.head htail := by
          have hcastFace : castD (M.faceSucc a) = castD (tail.head htail) := by
            calc
              castD (M.faceSucc a) = castD (oldWord.formPerm a) :=
                congrArg castD (hprev a haOldMem)
              _ = (oldWord.map castD).formPerm a' := hMapAnchor.symm
              _ = cyc.head hcyc := hActiveForm
              _ = castD (tail.head htail) := hTailHeadEq
          exact outerSuccAlloc_castDart_injective hcast hcastFace
        have hRotTailA := outerSuccAlloc_rot_faceSucc M a
        rw [hFaceActive] at hRotTailA
        have hRotTailA' : M.rot (tail.head htail) = A := hRotTailA.trans hAedge
        have htailCyc : castD (tail.head htail) ∈ cyc := by
          simp only [cyc, List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨tail.head htail, List.head_mem htail, rfl⟩)
        have hTailNotA : tail.head htail ≠ a := by
          intro heq
          apply hAnchorNotCyc
          simpa [heq, a', castD] using htailCyc
        have hRotTailNew : N.rot (castD (tail.head htail)) =
            outerSuccAlloc_castEq hsize.symm
              (StageRotation.allocation k 2 (.inr (1, true))) := by
          rw [outerSuccAlloc_up_rot_old hsize hcast N.rot M.rot a A
            (tail.head htail) hRotResize]
          simp [hTailNotA, hRotTailA']
        have hqInv : N.edgeInv q = outerSuccAlloc_castEq hsize.symm
            (StageRotation.allocation k 2 (.inr (1, true))) := by
          simpa [N, q, kmswMap_edgeInv, edgeFlip] using
            (outerSuccAlloc_castEq_symm_allocation_new hsize (1 : Fin 2) true).symm
        have hRotQ : N.rot (castD (tail.head htail)) = N.edgeInv q :=
          hRotTailNew.trans hqInv.symm
        have hFaceQ := outerSuccAlloc_faceSucc_eq_of_rot N q
          (castD (tail.head htail)) hRotQ
        calc
          N.faceSucc q = castD (tail.head htail) := hFaceQ
          _ = cyc.head hcyc := hTailHeadEq.symm
          _ = newWord.formPerm q := hFormQ.symm
      · obtain ⟨dold, hdold, hEq⟩ := List.mem_map.mp htail
        have hEq' : d = castD dold := hEq.symm
        subst d
        have hxCyc : castD dold ∈ cyc := by
          simp only [cyc, List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨dold, hdold, rfl⟩)
        have hdoldMem : dold ∈ oldWord := by
          rw [hsplit]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ hdold)
        have hMapForm := outerSuccAlloc_formPerm_map_injective castD
          (outerSuccAlloc_castDart_injective hcast) oldWord
          (stageOuterWord_nodup w n) dold hdoldMem
        by_cases hlast : castD dold = cyc.getLast hcyc
        · have hOldA : oldWord.formPerm dold = a := by
            apply (outerSuccAlloc_castDart_injective hcast)
            calc
              castD (oldWord.formPerm dold) = (oldWord.map castD).formPerm (castD dold) :=
                hMapForm.symm
              _ = (oldWord.map castD).formPerm (cyc.getLast hcyc) := by rw [hlast]
              _ = a' := hOldPred
              _ = castD a := rfl
          have hFace : M.faceSucc dold = a := by
            rw [hprev dold hdoldMem]
            exact hOldA
          have hFormPred : newWord.formPerm (castD dold) = p := by
            rw [← hNewForm]
            rw [outerSuccAlloc_formPerm_tail_up a' p q cyc hcyc hOldRotateNodup
              hNewRotateNodup (castD dold) hxCyc, ite_eq_left hlast]
          have hda : dold ≠ a := by
            intro heq
            subst dold
            exact hAnchorNotCyc (by simpa using hxCyc)
          have hRotA : M.rot a = M.edgeInv dold := by
            have h := outerSuccAlloc_rot_faceSucc M dold
            rw [hFace] at h
            exact h
          have hSigmaA : M.rot a ≠ A := by
            intro heq
            apply hda
            apply M.edgeInv.injective
            calc
              M.edgeInv dold = M.rot a := hRotA.symm
              _ = A := heq
              _ = M.edgeInv a := hAedge.symm
          have hpEq : p = outerSuccAlloc_castEq hsize.symm
              (StageRotation.allocation k 2 (.inr (0, false))) := by
            simpa [p] using
              (outerSuccAlloc_castEq_symm_allocation_new hsize (0 : Fin 2) false).symm
          rcases StageRotation.up_new k M.rot a A with ⟨h0, h1, h2, h3⟩
          have hpoint := outerSuccAlloc_resize_eq_apply hsize N.rot
            (StageRotation.up k M.rot a A) hRotResize
            (StageRotation.allocation k 2 (.inr (0, false)))
          rw [← hpEq, h0, ite_eq_right hSigmaA,
            outerSuccAlloc_castEq_symm_allocation_old hsize hcast (M.rot a)] at hpoint
          have hRotPred : N.rot p = N.edgeInv (castD dold) := by
            calc
              N.rot p = castD (M.rot a) := hpoint
              _ = castD (M.edgeInv dold) := congrArg castD hRotA
              _ = N.edgeInv (castD dold) := (outerSuccAlloc_edgeInv_cast hcast dold).symm
          have hFacePred := outerSuccAlloc_faceSucc_eq_of_rot N (castD dold) p hRotPred
          exact hFacePred.trans hFormPred.symm
        · have hOldFormNe : oldWord.formPerm dold ≠ a := by
            intro heq
            have hRotEq : (a' :: cyc).formPerm (castD dold) =
                (a' :: cyc).formPerm (cyc.getLast hcyc) := by
              calc
                (a' :: cyc).formPerm (castD dold) =
                    (oldWord.map castD).formPerm (castD dold) := by rw [hOldForm]
                _ = castD (oldWord.formPerm dold) := hMapForm
                _ = a' := by rw [heq]
                _ = (oldWord.map castD).formPerm (cyc.getLast hcyc) := hOldPred.symm
                _ = (a' :: cyc).formPerm (cyc.getLast hcyc) := by rw [← hOldForm]
            have hEq := (a' :: cyc).formPerm.injective hRotEq
            exact hlast hEq
          have hFaceNe : M.faceSucc dold ≠ a := by
            intro heq
            apply hOldFormNe
            exact (hprev dold hdoldMem).symm.trans heq
          have hRotFace := outerSuccAlloc_rot_faceSucc M dold
          have hSigmaNe : M.rot (M.faceSucc dold) ≠ A := by
            intro heq
            have hDneqA : dold ≠ a := by
              intro hda
              subst dold
              exact hAnchorNotCyc (by simpa using hxCyc)
            apply hDneqA
            apply M.edgeInv.injective
            calc
              M.edgeInv dold = M.rot (M.faceSucc dold) := hRotFace.symm
              _ = A := heq
              _ = M.edgeInv a := hAedge.symm
          have hRotLocal : N.rot (castD (M.faceSucc dold)) =
              castD (M.rot (M.faceSucc dold)) := by
            rw [outerSuccAlloc_up_rot_old hsize hcast N.rot M.rot a A
              (M.faceSucc dold) hRotResize]
            simp only [castD, ite_eq_right hFaceNe, ite_eq_right hSigmaNe]
          have hform : newWord.formPerm (castD dold) =
              castD (oldWord.formPerm dold) := by
            calc
              newWord.formPerm (castD dold) = (p :: q :: cyc).formPerm (castD dold) := by
                rw [hNewForm]
              _ = (a' :: cyc).formPerm (castD dold) := by
                simpa [hlast] using
                  (outerSuccAlloc_formPerm_tail_up a' p q cyc hcyc
                    hOldRotateNodup hNewRotateNodup (castD dold) hxCyc)
              _ = (oldWord.map castD).formPerm (castD dold) := by rw [hOldForm]
              _ = castD (oldWord.formPerm dold) := hMapForm
          exact outerSuccAlloc_faceSucc_transport hcast M N oldWord newWord hprev
            dold hdoldMem hform hRotLocal (outerSuccAlloc_edgeInv_cast hcast dold)

/-- An empty-upper-right down step preserves the face-successor description
of the outer word. The new edge's west and east darts follow the old active -/
theorem stageOuterWord_faceSucc_pendant (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    (hprev : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) :
    ∀ d ∈ stageOuterWord w (n + 1),
      (kmswMap w (n + 1)).faceSucc d = (stageOuterWord w (n + 1)).formPerm d := by
  let s := kmswStage w n
  let k := s.nextEdge
  let M := kmswMap w n
  let N := kmswMap w (n + 1)
  let oldWord := stageOuterWord w n
  let newWord := stageOuterWord w (n + 1)
  let pref := outerSuccAlloc_ulPrefix w n
  let tail := outerSuccAlloc_wordTail w n
  let a : StageDart k := outerSuccAlloc_activeWest w n
  let A : StageDart k := (a.1, true)
  have hcode : kmswCodeStep (w n) = .down := by
    rw [hc]
    decide
  have hstep : kmswStage w (n + 1) = kmswStepOfStep s .down := by
    simp [s, kmswStage, kmswStep, kmswCodeStep, hc]
  have hsize : (kmswStage w (n + 1)).nextEdge = k + 1 := by
    rw [hstep]
    simp [k, s, hUR, kmswStepOfStep, State.addEdge]
  have hcast : k ≤ (kmswStage w (n + 1)).nextEdge := by omega
  let castD := outerSucc_castDart hcast
  let a' := castD a
  let P' := pref.map castD
  let T' := tail.map castD
  let p : StageDart (kmswStage w (n + 1)).nextEdge := ((⟨k, by omega⟩), false)
  let q : StageDart (kmswStage w (n + 1)).nextEdge := ((⟨k, by omega⟩), true)
  have hpEq : p = outerSuccAlloc_castEq hsize.symm
      (StageRotation.allocation k 1 (.inr (0, false))) := by
    simpa [p] using
      (outerSuccAlloc_castEq_symm_allocation_new_one hsize (0 : Fin 1) false).symm
  let cyc := T' ++ P'
  let newList := P' ++ (a' :: p :: q :: T')
  have hsplit : oldWord = pref ++ (a :: tail) := by
    change stageOuterWord w n =
      outerSuccAlloc_ulPrefix w n ++
        (outerSuccAlloc_activeWest w n :: outerSuccAlloc_wordTail w n)
    exact outerSuccAlloc_stageWord_split w n
  have hnewWord : newWord = newList := by
    apply (List.map_injective_iff.mpr (outerSuccAlloc_dartVal_injective _))
    calc
      (stageOuterWord w (n + 1)).map (fun d => (d.1.val, d.2)) =
          stageOuterWordVal w (n + 1) := rfl
      _ = (((kmswStage w n).UL.map fun e => (e, false)) ++
          [((kmswStage w n).nextEdge, false), ((kmswStage w n).nextEdge, true)]) ++
          (((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
            ((kmswStage w n).LL.reverse.map fun e => (e, true))) :=
        outerSuccAlloc_pendant_wordVal w n hc hUR
      _ = newList.map (fun d => (d.1.val, d.2)) := by
        have hUL : (s.UL.dropLast ++ [s.active]) = s.UL := by
          simpa only using outerSuccAlloc_UL_last w n
        have hULMap : s.UL.map (fun e => (e, false)) =
            s.UL.dropLast.map (fun e => (e, false)) ++ [(s.active, false)] := by
          have h := congrArg (fun xs : List ℕ => xs.map fun e => (e, false)) hUL
          simpa only [List.map_append, List.map_cons, List.map_nil] using h.symm
        have hPval : P'.map (fun d => (d.1.val, d.2)) =
            s.UL.dropLast.map (fun e => (e, false)) := by
          calc
            P'.map (fun d => (d.1.val, d.2)) = pref.map (fun d => (d.1.val, d.2)) := by
              dsimp [P']
              exact outerSuccAlloc_castWord_val hcast pref
            _ = _ := outerSuccAlloc_ulPrefix_val w n
        have hTval : T'.map (fun d => (d.1.val, d.2)) =
            (s.UR.map (fun e => (e, false)) ++
              s.LR.reverse.map (fun e => (e, true)) ++
              s.LL.reverse.map (fun e => (e, true))) := by
          calc
            T'.map (fun d => (d.1.val, d.2)) = tail.map (fun d => (d.1.val, d.2)) := by
              dsimp [T']
              exact outerSuccAlloc_castWord_val hcast tail
            _ = _ := outerSuccAlloc_wordTail_val w n
        have haVal : (a'.1.val, a'.2) = (s.active, false) := by
          calc
            (a'.1.val, a'.2) = (a.1.val, a.2) := by
              exact outerSuccAlloc_castDart_val hcast a
            _ = (s.active, false) := by simp [s, a, outerSuccAlloc_activeWest]
        simp only [newList, List.map_append, List.map_cons, hPval, hTval]
        rw [hULMap, hUR]
        rw [haVal]
        simp [p, q, k, s, List.append_assoc]
  have hcastSplit : oldWord.map castD = P' ++ (a' :: T') := by
    have h := congrArg (fun xs : List (StageDart k) => xs.map castD) hsplit
    simpa only [List.map_append, List.map_cons, List.map_nil] using h
  have htail : tail ≠ [] := outerSuccAlloc_wordTail_ne_nil w n
  have htailCast : T' ≠ [] := by
    cases ht : tail with
    | nil => exact False.elim (htail ht)
    | cons t ts => simp [T', ht]
  have hcyc : cyc ≠ [] := by
    intro hnil
    simp [cyc, List.append_eq_nil_iff] at hnil
    exact htailCast hnil.1
  have hOldCastNodup : (oldWord.map castD).Nodup :=
    (stageOuterWord_nodup w n).map (outerSuccAlloc_castDart_injective hcast)
  have hNewListNodup : newList.Nodup := by
    rw [← hnewWord]
    exact stageOuterWord_nodup w (n + 1)
  have hOldRotate : (oldWord.map castD).rotate P'.length = a' :: cyc := by
    calc
      (oldWord.map castD).rotate P'.length = (P' ++ (a' :: T')).rotate P'.length := by
        rw [hcastSplit]
      _ = (a' :: T') ++ P' := List.rotate_append_length_eq P' (a' :: T')
      _ = a' :: cyc := by simp [cyc, List.cons_append]
  have hNewRotate : newList.rotate P'.length = a' :: p :: q :: cyc := by
    calc
      newList.rotate P'.length = (P' ++ (a' :: p :: q :: T')).rotate P'.length := rfl
      _ = (a' :: p :: q :: T') ++ P' := List.rotate_append_length_eq P' (a' :: p :: q :: T')
      _ = a' :: p :: q :: cyc := by simp [cyc, List.cons_append]
  have hOldRotateNodup : (a' :: cyc).Nodup := by
    rw [← hOldRotate]
    simpa using hOldCastNodup
  have hNewRotateNodup : (a' :: p :: q :: cyc).Nodup := by
    rw [← hNewRotate]
    simpa using hNewListNodup
  have hOldForm : (a' :: cyc).formPerm = (oldWord.map castD).formPerm := by
    rw [← hOldRotate]
    exact List.formPerm_rotate (oldWord.map castD) hOldCastNodup P'.length
  have hNewForm : (a' :: p :: q :: cyc).formPerm = newWord.formPerm := by
    calc
      (a' :: p :: q :: cyc).formPerm = newList.formPerm := by
        rw [← hNewRotate]
        exact List.formPerm_rotate newList hNewListNodup P'.length
      _ = newWord.formPerm := by rw [← hnewWord]
  have hAnchorNotCyc : a' ∉ cyc := (List.nodup_cons.mp hOldRotateNodup).1
  have hAedge : M.edgeInv a = A := by
    simp [M, a, A, outerSuccAlloc_activeWest, kmswMap_edgeInv, edgeFlip]
  have haOldMem : a ∈ oldWord := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hMapAnchor := outerSuccAlloc_formPerm_map_injective castD
    (outerSuccAlloc_castDart_injective hcast) oldWord (stageOuterWord_nodup w n) a haOldMem
  have hcycHead : cyc.head hcyc = castD (tail.head htail) := by
    simp [cyc, T', tail, List.head_append_of_ne_nil, htailCast]
  have hFaceActive : M.faceSucc a = tail.head htail := by
    have hAnchorForm : (oldWord.map castD).formPerm a' = cyc.head hcyc := by
      calc
        (oldWord.map castD).formPerm a' = (a' :: cyc).formPerm a' := by rw [← hOldForm]
        _ = cyc.head hcyc := outerSuccAlloc_formPerm_anchor a' cyc hcyc hOldRotateNodup
    have hcastFace : castD (M.faceSucc a) = castD (tail.head htail) := by
      calc
        castD (M.faceSucc a) = castD (oldWord.formPerm a) := congrArg castD (hprev a haOldMem)
        _ = (oldWord.map castD).formPerm a' := hMapAnchor.symm
        _ = cyc.head hcyc := hAnchorForm
        _ = castD (tail.head htail) := hcycHead
    exact outerSuccAlloc_castDart_injective hcast hcastFace
  have hRotTailA : M.rot (tail.head htail) = A := by
    have h := outerSuccAlloc_rot_faceSucc M a
    rw [hFaceActive] at h
    exact h.trans hAedge
  have hRotResizeStage :
      StageRotation.resize hsize (stageRot w (n + 1)) =
        StageRotation.pendant k (stageRot w n) A := by
    rw [stageRot_succ]
    convert StageRotation.step_pendant s (act_lt_nextEdge w (le_refl n))
      (stageRotation_UL_bound w n) (stageRot w n) (w n) hcode hUR using 1
    · exact outerSuccAlloc_resize_proof_irrel _ _ _
    · simp [k, s, A, a, outerSuccAlloc_activeWest]
  have hRotResize : StageRotation.resize hsize N.rot = StageRotation.pendant k M.rot A := by
    change StageRotation.resize hsize (stageRot w (n + 1)) =
      StageRotation.pendant k (stageRot w n) A
    simpa [k, s, A, a, outerSuccAlloc_activeWest] using hRotResizeStage
  have hTailPendant (x : StageDart (kmswStage w (n + 1)).nextEdge) (hx : x ∈ cyc) :
      newWord.formPerm x = (oldWord.map castD).formPerm x := by
    calc
      newWord.formPerm x = (a' :: p :: q :: cyc).formPerm x := by rw [hNewForm]
      _ = (a' :: cyc).formPerm x :=
        outerSuccAlloc_formPerm_tail_pendant a' p q cyc hcyc hOldRotateNodup
          hNewRotateNodup x hx
      _ = (oldWord.map castD).formPerm x := by rw [hOldForm]
  intro d hd
  have hdList : d ∈ newList := by
    rw [← hnewWord]
    exact hd
  rcases List.mem_append.mp hdList with hP | hrest
  · obtain ⟨dold, hdold, hEq⟩ := List.mem_map.mp hP
    have hEq' : d = castD dold := hEq.symm
    subst d
    have hxCyc : castD dold ∈ cyc := by
      simp only [cyc, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨dold, hdold, rfl⟩)
    have hdoldMem : dold ∈ oldWord := by
      rw [hsplit]
      exact List.mem_append_left _ hdold
    have hDneqA : dold ≠ a := by
      intro hda
      subst dold
      exact hAnchorNotCyc (by simpa using hxCyc)
    have hMapForm := outerSuccAlloc_formPerm_map_injective castD
      (outerSuccAlloc_castDart_injective hcast) oldWord (stageOuterWord_nodup w n)
      dold hdoldMem
    have hSigmaNe : M.rot (M.faceSucc dold) ≠ A := by
      intro heq
      apply hDneqA
      apply M.edgeInv.injective
      have hRotFace := outerSuccAlloc_rot_faceSucc M dold
      calc
        M.edgeInv dold = M.rot (M.faceSucc dold) := hRotFace.symm
        _ = A := heq
        _ = M.edgeInv a := hAedge.symm
    have hRotLocal : N.rot (castD (M.faceSucc dold)) = castD (M.rot (M.faceSucc dold)) := by
      rw [outerSuccAlloc_pendant_rot_old hsize hcast N.rot M.rot A
        (M.faceSucc dold) hRotResize]
      simp only [castD, ite_eq_right hSigmaNe]
    have hform : newWord.formPerm (castD dold) = castD (oldWord.formPerm dold) := by
      calc
        newWord.formPerm (castD dold) = (a' :: p :: q :: cyc).formPerm (castD dold) := by
          rw [hNewForm]
        _ = (a' :: cyc).formPerm (castD dold) :=
          outerSuccAlloc_formPerm_tail_pendant a' p q cyc hcyc hOldRotateNodup
            hNewRotateNodup (castD dold) hxCyc
        _ = (oldWord.map castD).formPerm (castD dold) := by rw [hOldForm]
        _ = castD (oldWord.formPerm dold) := hMapForm
    exact outerSuccAlloc_faceSucc_transport hcast M N oldWord newWord hprev
      dold hdoldMem hform hRotLocal (outerSuccAlloc_edgeInv_cast hcast dold)
  · rcases List.mem_cons.mp hrest with ha | hrest
    · subst d
      have hHeads := outerSuccAlloc_formPerm_pendant_head a' p q cyc hcyc hNewRotateNodup
      have hFormA : newWord.formPerm a' = p := by
        rw [← hNewForm]
        exact hHeads.1
      have hpoint := outerSuccAlloc_resize_eq_apply hsize N.rot
        (StageRotation.pendant k M.rot A) hRotResize
        (StageRotation.allocation k 1 (.inr (0, false)))
      rw [← hpEq] at hpoint
      have hpnew := (StageRotation.pendant_new k M.rot A).1
      rw [hpnew, outerSuccAlloc_castEq_symm_allocation_old_one hsize hcast A] at hpoint
      have hRotA : N.rot p = N.edgeInv a' := by
        calc
          N.rot p = castD A := hpoint
          _ = N.edgeInv a' := by
            rw [outerSuccAlloc_edgeInv_cast hcast a]
            exact congrArg castD hAedge.symm
      have hFaceA := outerSuccAlloc_faceSucc_eq_of_rot N a' p hRotA
      exact hFaceA.trans hFormA.symm
    · rcases List.mem_cons.mp hrest with hp | hrest
      · subst d
        have hHeads := outerSuccAlloc_formPerm_pendant_head a' p q cyc hcyc hNewRotateNodup
        have hFormP : newWord.formPerm p = q := by
          rw [← hNewForm]
          exact hHeads.2.1
        have hqEq : q = outerSuccAlloc_castEq hsize.symm
            (StageRotation.allocation k 1 (.inr (0, true))) := by
          simpa [q] using
            (outerSuccAlloc_castEq_symm_allocation_new_one hsize (0 : Fin 1) true).symm
        have hpoint := outerSuccAlloc_resize_eq_apply hsize N.rot
          (StageRotation.pendant k M.rot A) hRotResize
          (StageRotation.allocation k 1 (.inr (0, true)))
        rw [← hqEq] at hpoint
        have hqnew := (StageRotation.pendant_new k M.rot A).2
        rw [hqnew] at hpoint
        have heInvP : N.edgeInv p = q := by
          simp [N, p, q, kmswMap_edgeInv, edgeFlip]
        have hrotQ : N.rot q = N.edgeInv p := by
          calc
            N.rot q = outerSuccAlloc_castEq hsize.symm
                (StageRotation.allocation k 1 (.inr (0, true))) := hpoint
            _ = q := hqEq.symm
            _ = N.edgeInv p := heInvP.symm
        exact (outerSuccAlloc_faceSucc_eq_of_rot N p q hrotQ).trans hFormP.symm
      · rcases List.mem_cons.mp hrest with hq | htail
        · subst d
          have hHeads := outerSuccAlloc_formPerm_pendant_head a' p q cyc hcyc hNewRotateNodup
          have hFormQ : newWord.formPerm q = cyc.head hcyc := by
            rw [← hNewForm]
            exact hHeads.2.2
          have hTailMem : tail.head htail ∈ oldWord := by
            rw [hsplit]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.head_mem htail))
          have hMapTailHead := outerSuccAlloc_formPerm_map_injective castD
            (outerSuccAlloc_castDart_injective hcast) oldWord
            (stageOuterWord_nodup w n) (tail.head htail) hTailMem
          have hTailNotA : tail.head htail ≠ a := by
            intro heq
            have htailCyc : castD (tail.head htail) ∈ cyc := by
              simp only [cyc, List.mem_append]
              exact Or.inl (List.mem_map.mpr ⟨tail.head htail, List.head_mem htail, rfl⟩)
            apply hAnchorNotCyc
            simpa [heq, a', castD] using htailCyc
          have hRotTailA := outerSuccAlloc_rot_faceSucc M a
          rw [hFaceActive] at hRotTailA
          have hRotTailA' : M.rot (tail.head htail) = A := hRotTailA.trans hAedge
          have hTailHeadEq : cyc.head hcyc = castD (tail.head htail) := by
            simp [cyc, T', tail, List.head_append_of_ne_nil, htailCast]
          have hRotTailNew : N.rot (castD (tail.head htail)) = p := by
            rw [outerSuccAlloc_pendant_rot_old hsize hcast N.rot M.rot A
              (tail.head htail) hRotResize]
            simp [hRotTailA', hpEq]
          have hqEq : q = outerSuccAlloc_castEq hsize.symm
              (StageRotation.allocation k 1 (.inr (0, true))) := by
            simpa [q] using
              (outerSuccAlloc_castEq_symm_allocation_new_one hsize (0 : Fin 1) true).symm
          have heInvQ : N.edgeInv q = p := by
            simp [N, p, q, kmswMap_edgeInv, edgeFlip]
          have hRotQ : N.rot (castD (tail.head htail)) = N.edgeInv q :=
            hRotTailNew.trans heInvQ.symm
          have hFaceQ := outerSuccAlloc_faceSucc_eq_of_rot N q
            (castD (tail.head htail)) hRotQ
          calc
            N.faceSucc q = castD (tail.head htail) := hFaceQ
            _ = cyc.head hcyc := hTailHeadEq.symm
            _ = newWord.formPerm q := hFormQ.symm
        · obtain ⟨dold, hdold, hEq⟩ := List.mem_map.mp htail
          have hEq' : d = castD dold := hEq.symm
          subst d
          have hxCyc : castD dold ∈ cyc := by
            simp only [cyc, List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨dold, hdold, rfl⟩)
          have hdoldMem : dold ∈ oldWord := by
            rw [hsplit]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ hdold)
          have hDneqA : dold ≠ a := by
            intro hda
            subst dold
            exact hAnchorNotCyc (by simpa using hxCyc)
          have hMapForm := outerSuccAlloc_formPerm_map_injective castD
            (outerSuccAlloc_castDart_injective hcast) oldWord
            (stageOuterWord_nodup w n) dold hdoldMem
          have hSigmaNe : M.rot (M.faceSucc dold) ≠ A := by
            intro heq
            apply hDneqA
            apply M.edgeInv.injective
            have hRotFace := outerSuccAlloc_rot_faceSucc M dold
            calc
              M.edgeInv dold = M.rot (M.faceSucc dold) := hRotFace.symm
              _ = A := heq
              _ = M.edgeInv a := hAedge.symm
          have hRotLocal : N.rot (castD (M.faceSucc dold)) =
              castD (M.rot (M.faceSucc dold)) := by
            rw [outerSuccAlloc_pendant_rot_old hsize hcast N.rot M.rot A
              (M.faceSucc dold) hRotResize]
            simp only [castD, ite_eq_right hSigmaNe]
          have hform : newWord.formPerm (castD dold) =
              castD (oldWord.formPerm dold) := by
            calc
              newWord.formPerm (castD dold) =
                  (a' :: p :: q :: cyc).formPerm (castD dold) := by rw [hNewForm]
              _ = (a' :: cyc).formPerm (castD dold) :=
                outerSuccAlloc_formPerm_tail_pendant a' p q cyc hcyc
                  hOldRotateNodup hNewRotateNodup (castD dold) hxCyc
              _ = (oldWord.map castD).formPerm (castD dold) := by rw [hOldForm]
              _ = castD (oldWord.formPerm dold) := hMapForm
          exact outerSuccAlloc_faceSucc_transport hcast M N oldWord newWord hprev
            dold hdoldMem hform hRotLocal (outerSuccAlloc_edgeInv_cast hcast dold)

end DirectedDistances.KMSW
