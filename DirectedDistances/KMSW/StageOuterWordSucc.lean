/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageOuterWord

import Mathlib.Data.List.Cycle

/-! # Cyclic successor of the KMSW stage outer word

The face permutation follows the ordered four-run boundary word in -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem stageDartVal_injective (k : ℕ) :
    Function.Injective (fun d : StageDart k => (d.1.val, d.2)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h₁, h₂⟩
  cases Fin.ext h₁
  cases h₂
  rfl

private theorem formPerm_apply_mem_eq_next (α : Type*) [DecidableEq α]
    (l : List α) (hl : l.Nodup) (x : α) (hx : x ∈ l) :
    l.formPerm x = l.next x hx := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem _ hl, List.formPerm_apply_getElem _ hl]

private theorem formPerm_append_left_internal {α : Type*} [DecidableEq α]
    (p q : List α) (hnd : (p ++ q).Nodup) (x : α) (hx : x ∈ p.dropLast) :
    (p ++ q).formPerm x = p.formPerm x := by
  have hpnd : p.Nodup := hnd.of_append_left
  have hx' : x ∈ p := List.mem_of_mem_dropLast hx
  have hmem : x ∈ p ++ q := List.mem_append_left _ hx'
  rw [formPerm_apply_mem_eq_next _ _ hnd _ hmem,
    formPerm_apply_mem_eq_next _ _ hpnd _ hx']
  rw [List.next_eq_getElem hmem, List.next_eq_getElem hx']
  have hidx : (p ++ q).idxOf x = p.idxOf x := List.idxOf_append_of_mem hx'
  have hsucc : p.idxOf x + 1 < p.length := List.succ_idxOf_lt_length_of_mem_dropLast hx
  have hwhole : (p.idxOf x + 1) % (p ++ q).length = p.idxOf x + 1 :=
    Nat.mod_eq_of_lt (by simpa only [List.length_append] using hsucc.trans_le (by omega))
  have hpart : (p.idxOf x + 1) % p.length = p.idxOf x + 1 := Nat.mod_eq_of_lt hsucc
  simp only [hidx, hwhole, hpart]
  exact List.getElem_append_left (by omega)

private theorem formPerm_append_right_internal {α : Type*} [DecidableEq α]
    (p q : List α) (hnd : (p ++ q).Nodup) (x : α) (hx : x ∈ q.dropLast) :
    (p ++ q).formPerm x = q.formPerm x := by
  have hqnd : q.Nodup := hnd.of_append_right
  have hx' : x ∈ q := List.mem_of_mem_dropLast hx
  have hdisj := List.disjoint_of_nodup_append hnd
  have hxnot : x ∉ p := by
    intro hxp
    exact (List.disjoint_left.mp hdisj) hxp hx'
  have hmem : x ∈ p ++ q := List.mem_append_right _ hx'
  rw [formPerm_apply_mem_eq_next _ _ hnd _ hmem,
    formPerm_apply_mem_eq_next _ _ hqnd _ hx']
  rw [List.next_eq_getElem hmem, List.next_eq_getElem hx']
  have hidx : (p ++ q).idxOf x = p.length + q.idxOf x :=
    List.idxOf_append_of_notMem hxnot
  have hsucc : q.idxOf x + 1 < q.length := List.succ_idxOf_lt_length_of_mem_dropLast hx
  have hwhole : (p.length + q.idxOf x + 1) % (p ++ q).length =
      p.length + q.idxOf x + 1 :=
    Nat.mod_eq_of_lt (by simp only [List.length_append]; omega)
  have hmod' : (q.idxOf x + 1) % q.length = q.idxOf x + 1 := Nat.mod_eq_of_lt hsucc
  simp only [hidx, hwhole, hmod']
  rw [List.getElem_append_right (by omega)]
  congr 1; omega

private theorem formPerm_append_prefix_last {α : Type*} [DecidableEq α]
    (p q : List α) (hp : p ≠ []) (hq : q ≠ []) (hnd : (p ++ q).Nodup) :
    (p ++ q).formPerm (p.getLast hp) = q.head hq := by
  have hp0 : 0 < p.length := List.length_pos_iff.mpr hp
  have hq0 : 0 < q.length := List.length_pos_iff.mpr hq
  have hidx : p.length - 1 < (p ++ q).length := by
    rw [List.length_append]
    omega
  have hget : (p ++ q)[p.length - 1]'hidx = p.getLast hp := by
    calc
      (p ++ q)[p.length - 1]'hidx = p[p.length - 1]'(by omega) :=
        List.getElem_append_left (by omega)
      _ = p.getLast hp := by rw [← List.getLast_eq_getElem hp]
  have hnextidx : (p.length - 1 + 1) % (p ++ q).length = p.length := by
    have hsub : p.length - 1 + 1 = p.length := by omega
    rw [hsub, List.length_append]
    exact Nat.mod_eq_of_lt (by omega)
  have hpNext : p.length < (p ++ q).length := by
    rw [List.length_append]
    omega
  have hnextBase : (p ++ q)[p.length]'hpNext = q.head hq := by
    rw [List.getElem_append_right (by omega)]
    cases q with
    | nil => exact (hq rfl).elim
    | cons a q => simp [List.head]
  have hnext : (p ++ q)[(p.length - 1 + 1) % (p ++ q).length] = q.head hq := by
    simpa only [hnextidx] using hnextBase
  have hform := List.formPerm_apply_getElem (p ++ q) hnd (p.length - 1) hidx
  calc
    (p ++ q).formPerm (p.getLast hp) =
        (p ++ q).formPerm ((p ++ q)[p.length - 1]'hidx) := by rw [hget]
    _ = (p ++ q)[(p.length - 1 + 1) % (p ++ q).length] := hform
    _ = q.head hq := hnext

private theorem formPerm_append_suffix_last {α : Type*} [DecidableEq α]
    (p q : List α) (hp : p ≠ []) (hq : q ≠ []) (hnd : (p ++ q).Nodup) :
    (p ++ q).formPerm (q.getLast hq) = p.head hp := by
  have hwhole : p ++ q ≠ [] := by simp [hq]
  have hlast : (p ++ q).getLast hwhole = q.getLast hq :=
    List.getLast_append_of_right_ne_nil p q hq
  have hnext := List.next_getLast_eq_head (p ++ q) hwhole hnd
  have hmem : q.getLast hq ∈ p ++ q := List.mem_append_right _ (List.getLast_mem hq)
  rw [formPerm_apply_mem_eq_next _ _ hnd _ hmem]
  have hhead : (p ++ q).head hwhole = p.head hp := by simp [hp]
  simpa only [hlast, hhead] using hnext

private theorem faceSucc_eq_of_rot {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (d x : D) (h : M.rot x = M.edgeInv d) :
    M.faceSucc d = x := by
  change M.rot.symm (M.edgeInv d) = x
  rw [← h, M.rot.symm_apply_apply]

private def stageDartEquiv {k l : ℕ} (h : k = l) : StageDart k ≃ StageDart l :=
  h ▸ Equiv.refl (StageDart k)

private theorem stageDartEquiv_val {k l : ℕ} (h : k = l) (d : StageDart k) :
    ((stageDartEquiv h d).1.val, (stageDartEquiv h d).2) = (d.1.val, d.2) := by
  cases h
  rfl

private theorem stageDartEquiv_symm {k l : ℕ} (h : k = l) :
    (stageDartEquiv h).symm = stageDartEquiv h.symm := by
  cases h
  rfl

private theorem resize_eq_stageDartEquiv {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) :
    StageRotation.resize h σ = (stageDartEquiv h).permCongr σ := by
  cases h
  rfl

private theorem resize_proof_irrel {k l : ℕ} (h h' : k = l)
    (σ : Equiv.Perm (StageDart k)) :
    StageRotation.resize h σ = StageRotation.resize h' σ := by
  cases h
  cases h'
  rfl

private theorem edgeFlip_stageDartEquiv {k l : ℕ} (h : k = l) :
    (stageDartEquiv h).permCongr (edgeFlip k) = edgeFlip l := by
  cases h
  change (Equiv.refl (StageDart k)).permCongr (edgeFlip k) = edgeFlip k
  ext x <;> rw [Equiv.permCongr_apply] <;> simp [edgeFlip]

private theorem formPerm_map_equiv_apply {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (l : List α) (hl : l.Nodup) (x : α) (hx : x ∈ l) :
    (l.map e).formPerm (e x) = e (l.formPerm x) := by
  have hl' : (l.map e).Nodup := hl.map e.injective
  have hmem : e x ∈ l.map e := List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [formPerm_apply_mem_eq_next _ _ hl' _ hmem,
    formPerm_apply_mem_eq_next _ _ hl _ hx]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have himap : i < (l.map e).length := by simpa using hi
  have hmap : (l.map e)[i]'himap = e l[i] := by simp
  have hnextmap := List.next_getElem _ hl' i himap
  have hnextmap' : (l.map e).next (e l[i]) hmem =
      (l.map e)[(i + 1) % (l.map e).length]'(Nat.mod_lt _ (i.zero_le.trans_lt himap)) := by
    simpa only [hmap] using hnextmap
  rw [hnextmap', List.next_getElem _ hl i hi]
  simp

private theorem faceSucc_congr {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] (M : CombinatorialMap D) (N : CombinatorialMap E)
    (e : D ≃ E) (hrot : N.rot = e.permCongr M.rot)
    (hedge : N.edgeInv = e.permCongr M.edgeInv) (d : D) :
    N.faceSucc (e d) = e (M.faceSucc d) := by
  have hface : N.faceSucc = e.permCongr M.faceSucc := by
    have hrotInv : (e.permCongr M.rot).symm = e.permCongr M.rot.symm := by
      ext x
      simp [Equiv.permCongr_def]
    ext x
    simp [CombinatorialMap.faceSucc, hrot, hedge, hrotInv]
  rw [hface]
  simp

/-- Cast an old stage dart into a stage with more allocated edges. -/
@[expose] def outerSucc_castDart {k l : ℕ} (h : k ≤ l) (d : StageDart k) : StageDart l :=
  (Fin.castLE h d.1, d.2)

/-- The old summand of a stage allocation is the usual `Fin.castLE` embedding -/
theorem outerSucc_allocation_old (k r : ℕ) (h : k ≤ k + r) (d : StageDart k) :
    StageRotation.allocation k r (.inl d) = outerSucc_castDart h d := by
  rcases d with ⟨e, b⟩
  apply Prod.ext
  · exact Fin.ext rfl
  · rfl

/-- On an old dart whose predecessor rotation entry is unchanged, face
successor transports through an allocation (`def-kmsw`, -/
theorem outerSucc_faceSucc_castLE_of_local {k l : ℕ} (h : k ≤ l)
    (M : CombinatorialMap (StageDart k)) (N : CombinatorialMap (StageDart l))
    (d : StageDart k)
    (hrot : N.rot (outerSucc_castDart h (M.faceSucc d)) =
      outerSucc_castDart h (M.rot (M.faceSucc d)))
    (hedge : N.edgeInv (outerSucc_castDart h d) =
      outerSucc_castDart h (M.edgeInv d)) :
    N.faceSucc (outerSucc_castDart h d) =
      outerSucc_castDart h (M.faceSucc d) := by
  apply N.rot.injective
  change N.rot (N.rot.symm (N.edgeInv (outerSucc_castDart h d))) =
    N.rot (outerSucc_castDart h (M.faceSucc d))
  rw [N.rot.apply_symm_apply, hedge, hrot]
  congr 1
  exact (M.rot.apply_symm_apply _).symm

/-- For a duplicate-free list, `formPerm` sends a member to its cyclic next -/
theorem outerSucc_formPerm_apply_mem_eq_next {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (x : α) (hx : x ∈ l) :
    l.formPerm x = l.next x hx :=
  formPerm_apply_mem_eq_next α l hl x hx

/-- Value form of the fresh-left outer-word splice (`def-kmsw`, -/
theorem outerSucc_leftFresh_wordVal (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hl : (kmswStage w n).UL.dropLast.reverse = []) :
    stageOuterWordVal w (n + 1) =
      [((kmswStage w n).nextEdge, false)] ++
        (((kmswStage w n).UR.map fun e => (e, false)) ++
          ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
          ((kmswStage w n).LL.reverse.map fun e => (e, true))) ++
        [((kmswStage w n).nextEdge + 1, true)] := by
  let s := kmswStage w n
  have hstage : kmswStage w (n + 1) = kmswStepOfStep s .left := by
    simp [s, kmswStage, kmswStep, kmswCodeStep, hc]
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hdrop : s.UL.dropLast = [] := by
    have h := congrArg List.reverse hl
    simpa [s] using h
  have hxsDrop : xs = s.UL.dropLast := by rw [hxs]; simp
  have hxsempty : xs = [] := by rw [hxsDrop, hdrop]
  have hUL : s.UL = [s.active] := by simpa [hxsempty] using hxs
  rw [stageOuterWordVal_eq_runs w (n + 1), hstage]
  simp [s, kmswStepOfStep, hUL, State.addEdge,
    List.reverse_cons, List.map_append, List.append_assoc]

/-- Value form of the predecessor-left outer-word splice (`def-kmsw`, -/
theorem outerSucc_leftExisting_wordVal (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hc : w n = 0)
    (hl : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    stageOuterWordVal w (n + 1) =
      (((es.reverse ++ [(kmswStage w n).nextEdge]).map fun f => (f, false)) ++
        ((kmswStage w n).UR.map fun f => (f, false)) ++
        ((kmswStage w n).LR.reverse.map fun f => (f, true)) ++
        ((kmswStage w n).LL.reverse.map fun f => (f, true))) := by
  let s := kmswStage w n
  have hstage : kmswStage w (n + 1) = kmswStepOfStep s .left := by
    simp [s, kmswStage, kmswStep, kmswCodeStep, hc]
  have hdrop : s.UL.dropLast = es.reverse ++ [e] := by
    have h := congrArg List.reverse hl
    simpa only [List.reverse_cons, List.reverse_reverse] using h
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hxsS : s.UL = xs ++ [s.active] := by simpa [s] using hxs
  have hxsDrop : xs = s.UL.dropLast := by rw [hxsS]; simp
  have hUL : s.UL = es.reverse ++ [e, s.active] := by
    calc
      s.UL = xs ++ [s.active] := hxsS
      _ = s.UL.dropLast ++ [s.active] := by rw [← hxsDrop]
      _ = (es.reverse ++ [e]) ++ [s.active] := by rw [hdrop]
      _ = es.reverse ++ [e, s.active] := by simp [List.append_assoc]
  rw [stageOuterWordVal_eq_runs w (n + 1), hstage]
  simp [s, kmswStepOfStep, hUL, State.addEdge,
    List.reverse_cons, List.map_append, List.append_assoc]

/-- The activation branch preserves the exact cyclic successor relation.
The activated head of `UR` moves to the end of `UL` without changing its -/
theorem stageOuterWord_faceSucc_down_activation (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hc : w n = 2)
    (hr : (kmswStage w n).UR = e :: es)
    (hprev : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) :
    ∀ d ∈ stageOuterWord w (n + 1),
      (kmswMap w (n + 1)).faceSucc d = (stageOuterWord w (n + 1)).formPerm d := by
  let s := kmswStage w n
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge := by
    simp [s, kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hr]
  let ecast := stageDartEquiv hs.symm
  have hword : stageOuterWord w (n + 1) = (stageOuterWord w n).map ecast := by
    apply (List.map_injective_iff.mpr (stageDartVal_injective _))
    calc
      (stageOuterWord w (n + 1)).map (fun d => (d.1.val, d.2)) =
          stageOuterWordVal w (n + 1) := rfl
      _ = stageOuterWordVal w n := stageOuterWord_down_activation w n e es hc hr
      _ = (stageOuterWord w n).map (fun d => (d.1.val, d.2)) := rfl
      _ = ((stageOuterWord w n).map ecast).map (fun d => (d.1.val, d.2)) := by
        simp only [List.map_map]
        congr 1
        funext d
        exact (stageDartEquiv_val hs.symm d).symm
  have htable := StageRotation.step_activation (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) (by rw [hc]; decide) e es hr
  have hresize : StageRotation.resize hs (stageRot w (n + 1)) = stageRot w n := by
    rw [stageRot_succ]
    convert htable using 1
    exact resize_proof_irrel _ _ _
  have heinv : stageDartEquiv hs = ecast.symm := by
    exact congrArg Equiv.symm (stageDartEquiv_symm hs)
  have hrot : (kmswMap w (n + 1)).rot = ecast.permCongr (kmswMap w n).rot := by
    rw [kmswMap_rot, kmswMap_rot]
    have hresize' : ecast.symm.permCongr (stageRot w (n + 1)) = stageRot w n := by
      rw [resize_eq_stageDartEquiv hs, heinv] at hresize
      exact hresize
    have htransport := congrArg (fun σ => ecast.permCongr σ) hresize'
    calc
      stageRot w (n + 1) = ecast.permCongr (ecast.symm.permCongr (stageRot w (n + 1))) := by
        symm
        simpa only [Equiv.permCongr_symm] using
          ecast.permCongr.apply_symm_apply (stageRot w (n + 1))
      _ = ecast.permCongr (stageRot w n) := htransport
  have hedge : (kmswMap w (n + 1)).edgeInv = ecast.permCongr (kmswMap w n).edgeInv := by
    rw [kmswMap_edgeInv, kmswMap_edgeInv]
    exact (edgeFlip_stageDartEquiv hs.symm).symm
  intro d hd
  rw [hword] at hd
  obtain ⟨dold, hdold, rfl⟩ := List.mem_map.mp hd
  calc
    (kmswMap w (n + 1)).faceSucc (ecast dold) =
        ecast ((kmswMap w n).faceSucc dold) :=
          faceSucc_congr (kmswMap w n) (kmswMap w (n + 1)) ecast hrot hedge dold
    _ = ecast ((stageOuterWord w n).formPerm dold) := congrArg ecast (hprev dold hdold)
    _ = (stageOuterWord w (n + 1)).formPerm (ecast dold) := by
      rw [hword]
      exact (formPerm_map_equiv_apply ecast (stageOuterWord w n)
        (stageOuterWord_nodup w n) dold hdold).symm

/-- The initial one-edge outer word follows the face permutation -/
theorem stageOuterWord_faceSucc_zero (w : ℕ → Fin 3) :
    ∀ d ∈ stageOuterWord w 0,
      (kmswMap w 0).faceSucc d = (stageOuterWord w 0).formPerm d := by
  rintro ⟨e, b⟩ hd
  fin_cases e
  have hword : stageOuterWord w 0 =
      [((⟨0, by simp [kmswStage, kmswInit]⟩ : Fin (kmswStage w 0).nextEdge), false),
        ((⟨0, by simp [kmswStage, kmswInit]⟩ : Fin (kmswStage w 0).nextEdge), true)] := by
    apply (List.map_injective_iff.mpr (stageDartVal_injective _))
    calc
      (stageOuterWord w 0).map (fun d => (d.1.val, d.2)) =
          stageOuterWordVal w 0 := rfl
      _ = ([(0, false), (0, true)] : List (ℕ × Bool)) := by
        rw [stageOuterWordVal_eq_runs]
        simp [kmswStage, kmswInit]
      _ = ([((⟨0, by simp [kmswStage, kmswInit]⟩ : Fin (kmswStage w 0).nextEdge), false),
          ((⟨0, by simp [kmswStage, kmswInit]⟩ : Fin (kmswStage w 0).nextEdge), true)] :
          List (StageDart (kmswStage w 0).nextEdge)).map (fun d => (d.1.val, d.2)) := by
        simp
  rw [hword] at hd ⊢
  cases b <;>
    simp [kmswMap, stageRot_zero, CombinatorialMap.faceSucc, edgeFlip, List.formPerm] at hd ⊢

private theorem formPerm_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  have hl' := hl.map hf
  have hmem : f x ∈ l.map f := List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [formPerm_apply_mem_eq_next _ _ hl' _ hmem,
    formPerm_apply_mem_eq_next _ _ hl _ hx]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have himap : i < (l.map f).length := by simpa using hi
  have hmap : (l.map f)[i]'himap = f l[i] := by simp
  have hnext := List.next_getElem (l.map f) hl' i himap
  have hnext' : (l.map f).next (f l[i]) hmem =
      (l.map f)[(i + 1) % (l.map f).length]'
        (Nat.mod_lt _ (i.zero_le.trans_lt himap)) := by
    simpa only [hmap] using hnext
  rw [hnext', List.next_getElem _ hl i hi]
  simp

private theorem formPerm_cons_head {α : Type*} [DecidableEq α]
    (a : α) (r : List α) (hr : r ≠ []) (hnd : (a :: r).Nodup) :
    (a :: r).formPerm a = r.head hr := by
  cases r with
  | nil => exact (hr rfl).elim
  | cons b r => exact List.formPerm_apply_head _ _ _ hnd

private theorem pairSplice_old_table {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F)
    (hx : τ x = x) (hxy : x ≠ y) (d : D) :
    StageRotation.pairSplice σ τ a b x y (.inl d) =
      if d = a then .inr x else if σ d = b then .inr y else .inl (σ d) := by
  by_cases hda : d = a
  · subst d
    simp [StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hx, hxy]
  · by_cases hdb : σ d = b <;>
      simp [StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hda, hdb]

private theorem pairSplice_x_table {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F) :
    StageRotation.pairSplice σ τ a b x y (.inr x) =
      if σ a = b then .inr y else .inl (σ a) := by
  by_cases hab : σ a = b <;>
    simp [StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hab]

private theorem leftExisting_cycle (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (e a : StageDart k) (r : List (StageDart k)) (hr : r ≠ [])
    (hnd : (e :: a :: r).Nodup)
    (hcycle : ∀ d ∈ e :: a :: r, σ ((e :: a :: r).formPerm d) = edgeFlip k d) :
    let x : StageDart 1 := (0, false)
    let y : StageDart 1 := (0, true)
    let l : List (StageDart k ⊕ StageDart 1) := .inr x :: r.map Sum.inl
    ∀ d ∈ l, StageRotation.pairSplice σ (Equiv.refl _) e (edgeFlip k a) x y
      (l.formPerm d) = Sum.map (edgeFlip k) (edgeFlip 1) d := by
  dsimp only
  let f : StageDart k → StageDart k ⊕ StageDart 1 := Sum.inl
  let x : StageDart k ⊕ StageDart 1 := .inr (0, false)
  let l := x :: r.map f
  have hrnd : r.Nodup := hnd.of_cons.of_cons
  have hlnd : l.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp [x, f], hrnd.map Sum.inl_injective⟩
  have hrmap : r.map f ≠ [] := by simpa using hr
  have hhead := hcycle a (by simp)
  have hanchor : (e :: a :: r).formPerm a = r.head hr := by
    have h := formPerm_append_prefix_last [e, a] r (by simp) hr hnd
    simpa using h
  rw [hanchor] at hhead
  have hlast := hcycle (r.getLast hr) (by simp)
  have hlastform := formPerm_append_suffix_last [e, a] r (by simp) hr hnd
  have hlastform' : (e :: a :: r).formPerm (r.getLast hr) = e := by
    simpa using hlastform
  rw [hlastform'] at hlast
  have hehead : e ≠ r.head hr := by
    intro h
    exact hnd.notMem (List.mem_cons_of_mem _ (h ▸ List.head_mem hr))
  have hσe : σ e ≠ edgeFlip k a := by
    rw [← hhead]
    exact fun h => hehead (σ.injective h)
  intro d hd
  change d ∈ l at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · change StageRotation.pairSplice _ _ _ _ _ _ (l.formPerm x) = _
    rw [formPerm_cons_head x (r.map f) hrmap hlnd]
    have hmaphead : (r.map f).head hrmap = f (r.head hr) := by
      cases r with
      | nil => exact (hr rfl).elim
      | cons b r => rfl
    rw [hmaphead, pairSplice_old_table _ _ _ _ _ _ rfl (by decide)]
    have hne : r.head hr ≠ e := Ne.symm hehead
    simp only [hne, hhead, ↓reduceIte]
    rfl
  · obtain ⟨d, hdr, rfl⟩ := List.mem_map.mp hd
    by_cases hlastd : d = r.getLast hr
    · subst d
      have hlastnew := formPerm_append_suffix_last [x] (r.map f) (by simp) hrmap hlnd
      have hmaplast : (r.map f).getLast hrmap = f (r.getLast hr) := by
        simp [List.getLast_map]
      rw [hmaplast] at hlastnew
      change StageRotation.pairSplice _ _ _ _ _ _ (l.formPerm (f (r.getLast hr))) = _
      rw [show l.formPerm (f (r.getLast hr)) = x by simpa using hlastnew]
      rw [pairSplice_x_table]
      rw [ite_eq_right hσe, hlast]
      rfl
    · have hdrop := List.mem_dropLast_of_mem_of_ne_getLast hdr hlastd
      have hmapdrop : f d ∈ (r.map f).dropLast := by
        rw [← List.map_dropLast]
        exact List.mem_map.mpr ⟨d, hdrop, rfl⟩
      have hnew := formPerm_append_right_internal [x] (r.map f) hlnd (f d) hmapdrop
      have hold := formPerm_append_right_internal [e, a] r hnd d hdrop
      rw [formPerm_map_injective f Sum.inl_injective r hrnd d hdr, ← hold] at hnew
      change l.formPerm (f d) = f ((e :: a :: r).formPerm d) at hnew
      change (e :: a :: r).formPerm d = r.formPerm d at hold
      have hs := hcycle d (by simp [hdr])
      have hsuccmem : (e :: a :: r).formPerm d ∈ r := by
        rw [hold, formPerm_apply_mem_eq_next _ _ hrnd _ hdr, List.next_eq_getElem hdr]
        exact List.getElem_mem _
      have hsuccne : (e :: a :: r).formPerm d ≠ e := by
        intro h
        exact hnd.notMem (List.mem_cons_of_mem _ (h ▸ hsuccmem))
      have hdne : d ≠ a := by
        intro h
        exact hnd.of_cons.notMem (h ▸ hdr)
      have hsne : σ ((e :: a :: r).formPerm d) ≠ edgeFlip k a := by
        rw [hs]
        exact fun h => hdne ((edgeFlip k).injective h)
      change StageRotation.pairSplice _ _ _ _ _ _ (l.formPerm (f d)) = _
      rw [hnew, pairSplice_old_table _ _ _ _ _ _ rfl (by decide)]
      rw [ite_eq_right hsuccne, ite_eq_right hsne, hs]
      rfl

private theorem leftFresh_cycle (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (a : StageDart k) (r : List (StageDart k)) (hr : r ≠ [])
    (hnd : (a :: r).Nodup)
    (hcycle : ∀ d ∈ a :: r, σ ((a :: r).formPerm d) = edgeFlip k d) :
    let x : StageDart 2 := (0, false)
    let y : StageDart 2 := (1, true)
    let l : List (StageDart k ⊕ StageDart 2) := .inr x :: r.map Sum.inl ++ [.inr y]
    ∀ d ∈ l, StageRotation.pairSplice σ (Equiv.swap (0, false) (1, false))
      a (edgeFlip k a) y (0, true) (l.formPerm d) =
        Sum.map (edgeFlip k) (edgeFlip 2) d := by
  dsimp only
  let f : StageDart k → StageDart k ⊕ StageDart 2 := Sum.inl
  let x : StageDart k ⊕ StageDart 2 := .inr (0, false)
  let y : StageDart k ⊕ StageDart 2 := .inr (1, true)
  let l := x :: r.map f ++ [y]
  have hrnd := hnd.of_cons
  have hpnd : (x :: r.map f).Nodup := by
    exact List.nodup_cons.mpr ⟨by simp [x, f], hrnd.map Sum.inl_injective⟩
  have hlnd : l.Nodup := by
    apply hpnd.append (by simp)
    simp [x, y, f]
  have hrmap : r.map f ≠ [] := by simpa using hr
  have hhead := hcycle a (by simp)
  rw [formPerm_cons_head a r hr hnd] at hhead
  have hlast := hcycle (r.getLast hr) (by simp)
  have hlastform : (a :: r).formPerm (r.getLast hr) = a := by
    simpa using formPerm_append_suffix_last [a] r (by simp) hr hnd
  rw [hlastform] at hlast
  have hanehead : a ≠ r.head hr := by
    intro h
    exact hnd.notMem (h ▸ List.head_mem hr)
  have hσa : σ a ≠ edgeFlip k a := by
    rw [← hhead]
    exact fun h => hanehead (σ.injective h)
  have hmaplast : (r.map f).getLast hrmap = f (r.getLast hr) := by
    simp [List.getLast_map]
  intro d hd
  change d ∈ l at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · have hfirst : l.formPerm x = f (r.head hr) := by
      change (x :: (r.map f ++ [y])).formPerm x = _
      rw [formPerm_cons_head x (r.map f ++ [y]) (by simp) hlnd]
      cases r with
      | nil => exact (hr rfl).elim
      | cons b r => rfl
    change StageRotation.pairSplice _ _ _ _ _ _ (l.formPerm x) = _
    rw [hfirst, pairSplice_old_table _ _ _ _ _ _ (by decide) (by decide)]
    simp only [Ne.symm hanehead, hhead, ↓reduceIte]
    rfl
  · rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨d, hdr, rfl⟩ := List.mem_map.mp hd
      by_cases hlastd : d = r.getLast hr
      · subst d
        have hlastnew : l.formPerm (f (r.getLast hr)) = y := by
          have hp : x :: r.map f ≠ [] := by simp
          have h := formPerm_append_prefix_last (x :: r.map f) [y] hp (by simp) hlnd
          have hget : (x :: r.map f).getLast hp = f (r.getLast hr) := by
            rw [List.getLast_cons hrmap, hmaplast]
          rw [hget] at h
          exact h
        change StageRotation.pairSplice _ _ _ _ _ _ (l.formPerm (f (r.getLast hr))) = _
        rw [hlastnew, pairSplice_x_table, ite_eq_right hσa, hlast]
        rfl
      · have hdrop := List.mem_dropLast_of_mem_of_ne_getLast hdr hlastd
        have hmapdrop : f d ∈ (r.map f).dropLast := by
          rw [← List.map_dropLast]
          exact List.mem_map.mpr ⟨d, hdrop, rfl⟩
        have hpdrop : f d ∈ (x :: r.map f).dropLast := by
          rw [List.dropLast_cons_of_ne_nil hrmap]
          exact List.mem_cons_of_mem _ hmapdrop
        have hnew := formPerm_append_left_internal (x :: r.map f) [y] hlnd (f d) hpdrop
        have hmid := formPerm_append_right_internal [x] (r.map f) hpnd (f d) hmapdrop
        change (x :: r.map f).formPerm (f d) = (r.map f).formPerm (f d) at hmid
        rw [hmid, formPerm_map_injective f Sum.inl_injective r hrnd d hdr] at hnew
        have hold := formPerm_append_right_internal [a] r hnd d hdrop
        change (a :: r).formPerm d = r.formPerm d at hold
        rw [← hold] at hnew
        change l.formPerm (f d) = f ((a :: r).formPerm d) at hnew
        have hs := hcycle d (by simp [hdr])
        have hsuccmem : (a :: r).formPerm d ∈ r := by
          rw [hold]
          exact List.formPerm_apply_mem_of_mem hdr
        have hsuccne : (a :: r).formPerm d ≠ a := by
          intro h
          exact hnd.notMem (h ▸ hsuccmem)
        have hdne : d ≠ a := by
          intro h
          exact hnd.notMem (h ▸ hdr)
        have hsne : σ ((a :: r).formPerm d) ≠ edgeFlip k a := by
          rw [hs]
          exact fun h => hdne ((edgeFlip k).injective h)
        change StageRotation.pairSplice _ _ _ _ _ _ (l.formPerm (f d)) = _
        rw [hnew, pairSplice_old_table _ _ _ _ _ _ (by decide) (by decide)]
        rw [ite_eq_right hsuccne, ite_eq_right hsne, hs]
        rfl
    · have hdy : d = y := by simpa using hd
      subst d
      have hyform : l.formPerm y = x := by
        exact formPerm_append_suffix_last (x :: r.map f) [y] (by simp) (by simp) hlnd
      change StageRotation.pairSplice _ _ _ _ _ _ (l.formPerm y) = _
      rw [hyform]
      simp [x, y, StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, edgeFlip]

private theorem map_split_pair {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (p q : List β) (e a : α) (l : List α)
    (h : l.map f = p ++ f e :: f a :: q) :
    ∃ u v, l = u ++ e :: a :: v ∧ u.map f = p ∧ v.map f = q := by
  induction p generalizing l with
  | nil =>
    cases l with
    | nil => simp at h
    | cons b l =>
      obtain ⟨hb, ht⟩ := List.cons.inj h
      have hbe := hf hb
      subst b
      cases l with
      | nil => simp at ht
      | cons b l =>
        obtain ⟨hb2, ht2⟩ := List.cons.inj ht
        have hba := hf hb2
        subst b
        exact ⟨[], l, rfl, rfl, ht2⟩
  | cons b p ih =>
    cases l with
    | nil => simp at h
    | cons c l =>
      obtain ⟨hc, ht⟩ := List.cons.inj h
      obtain ⟨u, v, rfl, hu, hv⟩ := ih l ht
      exact ⟨c :: u, v, rfl, by simp [hc, hu], hv⟩

private theorem rotCycle_append_comm {D : Type*} [DecidableEq D]
    (σ : Equiv.Perm D) (flip : D → D) (p q : List D) (hnd : (p ++ q).Nodup)
    (hcycle : ∀ d ∈ p ++ q, σ ((p ++ q).formPerm d) = flip d) :
    ∀ d ∈ q ++ p, σ ((q ++ p).formPerm d) = flip d := by
  have hform := List.formPerm_eq_of_isRotated hnd (List.isRotated_append (l := p) (l' := q))
  intro d hd
  rw [← hform]
  exact hcycle d (by simpa only [List.mem_append, or_comm] using hd)

private theorem resize_allocation_val {k r N : ℕ} (hs : N = k + r)
    (d : StageDart k ⊕ StageDart r) :
    let E := (StageRotation.allocation k r).trans (stageDartEquiv hs.symm)
    ((E d).1.val, (E d).2) =
      Sum.elim (fun d => (d.1.val, d.2)) (fun d => (k + d.1.val, d.2)) d := by
  dsimp only [Equiv.trans_apply]
  rw [stageDartEquiv_val]
  cases d <;> rfl

private theorem resize_allocation_cycle {k r N : ℕ} (hs : N = k + r)
    (M : CombinatorialMap (StageDart N)) (τ : Equiv.Perm (StageDart k ⊕ StageDart r))
    (l : List (StageDart k ⊕ StageDart r)) (hnd : l.Nodup)
    (hrot : StageRotation.resize hs M.rot = (StageRotation.allocation k r).permCongr τ)
    (hedge : M.edgeInv = edgeFlip N)
    (hcycle : ∀ d ∈ l, τ (l.formPerm d) = Sum.map (edgeFlip k) (edgeFlip r) d) :
    let E := (StageRotation.allocation k r).trans (stageDartEquiv hs.symm)
    ∀ d ∈ l.map E, M.faceSucc d = (l.map E).formPerm d := by
  dsimp only
  let E := (StageRotation.allocation k r).trans (stageDartEquiv hs.symm)
  have hrotE : M.rot = E.permCongr τ := by
    cases hs
    exact hrot
  have hflip : ∀ d, M.edgeInv (E d) = E (Sum.map (edgeFlip k) (edgeFlip r) d) := by
    rw [hedge]
    intro d
    cases hs
    cases d with
    | inl d => rcases d with ⟨e, b⟩; rfl
    | inr d => rcases d with ⟨e, b⟩; rfl
  intro d hd
  obtain ⟨d, hmem, rfl⟩ := List.mem_map.mp hd
  change M.faceSucc (E d) = (l.map E).formPerm (E d)
  rw [formPerm_map_equiv_apply E l hnd d hmem]
  apply faceSucc_eq_of_rot
  rw [hrotE, Equiv.permCongr_apply, Equiv.symm_apply_apply, hcycle d hmem, hflip]

private theorem stage_rotCycle (w : ℕ → Fin 3) (n : ℕ)
    (hprev : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) :
    ∀ d ∈ stageOuterWord w n,
      stageRot w n ((stageOuterWord w n).formPerm d) = edgeFlip _ d := by
  intro d hd
  rw [← hprev d hd]
  exact (stageRot w n).apply_symm_apply _

/-- A predecessor-left step preserves the outer-face cyclic word -/
theorem stageOuterWord_faceSucc_left_pred (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hc : w n = 0)
    (hl : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (hprev : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) :
    ∀ d ∈ stageOuterWord w (n + 1),
      (kmswMap w (n + 1)).faceSucc d = (stageOuterWord w (n + 1)).formPerm d := by
  let s := kmswStage w n
  have ha := act_lt_nextEdge w (le_refl n)
  have he : e < s.nextEdge := stageRotation_UL_bound w n e
    (List.dropLast_subset _ (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
  let a : StageDart s.nextEdge := (⟨s.active, ha⟩, false)
  let ed : StageDart s.nextEdge := (⟨e, he⟩, false)
  let Q := (s.UR.map fun f => (f, false)) ++
    (s.LR.reverse.map fun f => (f, true)) ++ (s.LL.reverse.map fun f => (f, true))
  have hdrop : s.UL.dropLast = es.reverse ++ [e] := by
    have h := congrArg List.reverse hl
    simpa only [List.reverse_cons, List.reverse_reverse] using h
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hxsDrop : xs = s.UL.dropLast := by rw [hxs]; simp
  have hUL : s.UL = es.reverse ++ [e, s.active] := by
    calc
      s.UL = xs ++ [s.active] := hxs
      _ = (es.reverse ++ [e]) ++ [s.active] := by rw [hxsDrop, hdrop]
      _ = es.reverse ++ [e, s.active] := by simp [List.append_assoc]
  have hv : (stageOuterWord w n).map (fun d => (d.1.val, d.2)) =
      es.reverse.map (fun f => (f, false)) ++ (e, false) :: (s.active, false) :: Q := by
    rw [← stageOuterWordVal, stageOuterWordVal_eq_runs, hUL]
    simp [Q, s, List.map_append, List.append_assoc]
  obtain ⟨p, r, hW, hp, hrval⟩ := map_split_pair _ (stageDartVal_injective _)
    (es.reverse.map fun f => (f, false)) Q ed a (stageOuterWord w n) hv
  have hQ : Q ≠ [] := by
    intro h
    have hLR : s.LR = [] := by
      simp only [Q, List.append_eq_nil_iff, List.map_eq_nil_iff, List.reverse_eq_nil_iff] at h
      exact h.1.2
    exact kmswStage_LR_nonempty w n hLR
  have hr : r ≠ [] := by intro h; apply hQ; rw [← hrval, h]; rfl
  have hnd : (p ++ ed :: a :: r).Nodup := by rw [← hW]; exact stageOuterWord_nodup w n
  have hndrot : (ed :: a :: (r ++ p)).Nodup := List.nodup_append_comm.mp hnd
  have hcycle : ∀ d ∈ ed :: a :: (r ++ p),
      stageRot w n ((ed :: a :: (r ++ p)).formPerm d) = edgeFlip _ d := by
    exact rotCycle_append_comm _ _ p (ed :: a :: r) hnd (by
      rw [← hW]; exact stage_rotCycle w n hprev)
  let τ := StageRotation.pairSplice (stageRot w n) (Equiv.refl (StageDart 1))
    ed (edgeFlip _ a) (0, false) (0, true)
  let L : List (StageDart s.nextEdge ⊕ StageDart 1) :=
    p.map Sum.inl ++ .inr (0, false) :: r.map Sum.inl
  have hndprime : (Sum.inr (0, false) :: (r ++ p).map
      (Sum.inl : StageDart s.nextEdge → StageDart s.nextEdge ⊕ StageDart 1)).Nodup := by
    exact List.nodup_cons.mpr ⟨by simp, hndrot.of_cons.of_cons.map Sum.inl_injective⟩
  have hLnd : L.Nodup := by
    apply List.nodup_append_comm.mp
    simpa only [List.map_append, List.cons_append] using hndprime
  have hLcycle : ∀ d ∈ L, τ (L.formPerm d) = Sum.map (edgeFlip _) (edgeFlip 1) d := by
    apply rotCycle_append_comm τ _ (.inr (0, false) :: r.map Sum.inl) (p.map Sum.inl)
    · simpa only [List.map_append, List.cons_append] using hndprime
    · simpa only [List.map_append, List.cons_append] using
        leftExisting_cycle s.nextEdge (stageRot w n) ed a (r ++ p)
          (by simp [hr]) hndrot hcycle
  have hcode : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 1 := by
    simp [s, kmswStage, kmswStep, hcode, kmswStepOfStep, hl, State.addEdge]
  let E := (StageRotation.allocation s.nextEdge 1).trans (stageDartEquiv hs.symm)
  have hresize : StageRotation.resize hs (kmswMap w (n + 1)).rot =
      (StageRotation.allocation s.nextEdge 1).permCongr τ := by
    rw [kmswMap_rot, stageRot_succ]
    exact StageRotation.step_leftExisting s ha (stageRotation_UL_bound w n)
      (stageRot w n) (w n) hcode e es hl
  have hnew : stageOuterWord w (n + 1) = L.map E := by
    apply List.map_injective_iff.mpr (stageDartVal_injective _)
    change stageOuterWordVal w (n + 1) = _
    rw [outerSucc_leftExisting_wordVal w n e es hc hl, List.map_map]
    have hvals : (fun d => ((E d).1.val, (E d).2)) =
        Sum.elim (fun d => (d.1.val, d.2)) (fun d => (s.nextEdge + d.1.val, d.2)) :=
      funext (resize_allocation_val hs)
    simp only [Function.comp_def]
    rw [hvals]
    simp only [L, List.map_append, List.map_cons, List.map_map, List.map_nil,
      Sum.elim_inl, Sum.elim_inr, Function.comp_def, hp, hrval]
    simp [Q, s, List.append_assoc]
  rw [hnew]
  exact resize_allocation_cycle hs (kmswMap w (n + 1)) τ L hLnd hresize rfl hLcycle

/-- A fresh-left step preserves the outer-face cyclic word, including the -/
theorem stageOuterWord_faceSucc_left_fresh (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hl : (kmswStage w n).UL.dropLast.reverse = [])
    (hprev : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) :
    ∀ d ∈ stageOuterWord w (n + 1),
      (kmswMap w (n + 1)).faceSucc d = (stageOuterWord w (n + 1)).formPerm d := by
  let s := kmswStage w n
  have ha := act_lt_nextEdge w (le_refl n)
  let a : StageDart s.nextEdge := (⟨s.active, ha⟩, false)
  let Q := (s.UR.map fun f => (f, false)) ++
    (s.LR.reverse.map fun f => (f, true)) ++ (s.LL.reverse.map fun f => (f, true))
  have hdrop : s.UL.dropLast = [] := by
    have h := congrArg List.reverse hl
    simpa using h
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hxsDrop : xs = s.UL.dropLast := by rw [hxs]; simp
  have hUL : s.UL = [s.active] := by simpa [hxsDrop, hdrop] using hxs
  have hv : (stageOuterWord w n).map (fun d => (d.1.val, d.2)) =
      (s.active, false) :: Q := by
    rw [← stageOuterWordVal, stageOuterWordVal_eq_runs, hUL]
    simp [Q, s, List.append_assoc]
  obtain ⟨r, hW, hrval⟩ : ∃ r, stageOuterWord w n = a :: r ∧
      r.map (fun d => (d.1.val, d.2)) = Q := by
    cases hW : stageOuterWord w n with
    | nil => simp [hW] at hv
    | cons b r =>
      rw [hW] at hv
      obtain ⟨hb, ht⟩ := List.cons.inj hv
      have hba : b = a := stageDartVal_injective _ hb
      exact ⟨r, by rw [hba], ht⟩
  have hQ : Q ≠ [] := by
    intro h
    have hLR : s.LR = [] := by
      simp only [Q, List.append_eq_nil_iff, List.map_eq_nil_iff, List.reverse_eq_nil_iff] at h
      exact h.1.2
    exact kmswStage_LR_nonempty w n hLR
  have hr : r ≠ [] := by intro h; apply hQ; rw [← hrval, h]; rfl
  have hnd : (a :: r).Nodup := by rw [← hW]; exact stageOuterWord_nodup w n
  have hcycle : ∀ d ∈ a :: r,
      stageRot w n ((a :: r).formPerm d) = edgeFlip _ d := by
    rw [← hW]; exact stage_rotCycle w n hprev
  let τ : Equiv.Perm (StageDart s.nextEdge ⊕ StageDart 2) :=
    StageRotation.pairSplice (stageRot w n) (Equiv.swap (0, false) (1, false))
    a (edgeFlip _ a) (1, true) (0, true)
  let L : List (StageDart s.nextEdge ⊕ StageDart 2) :=
    .inr (0, false) :: r.map Sum.inl ++ [.inr (1, true)]
  have hLnd : L.Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp
    · apply (hnd.of_cons.map Sum.inl_injective).append (by simp)
      simp
  have hLcycle : ∀ d ∈ L, τ (L.formPerm d) = Sum.map (edgeFlip _) (edgeFlip 2) d :=
    leftFresh_cycle s.nextEdge (stageRot w n) a r hr hnd hcycle
  have hcode : kmswCodeStep (w n) = .left := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
    simp [s, kmswStage, kmswStep, hcode, kmswStepOfStep, hl, State.addEdge]
  let E := (StageRotation.allocation s.nextEdge 2).trans (stageDartEquiv hs.symm)
  have hresize : StageRotation.resize hs (kmswMap w (n + 1)).rot =
      (StageRotation.allocation s.nextEdge 2).permCongr τ := by
    rw [kmswMap_rot, stageRot_succ]
    exact StageRotation.step_leftFresh s ha (stageRotation_UL_bound w n)
      (stageRot w n) (w n) hcode hl
  have hnew : stageOuterWord w (n + 1) = L.map E := by
    apply List.map_injective_iff.mpr (stageDartVal_injective _)
    change stageOuterWordVal w (n + 1) = _
    rw [outerSucc_leftFresh_wordVal w n hc hl, List.map_map]
    have hvals : (fun d => ((E d).1.val, (E d).2)) =
        Sum.elim (fun d => (d.1.val, d.2)) (fun d => (s.nextEdge + d.1.val, d.2)) :=
      funext (resize_allocation_val hs)
    simp only [Function.comp_def]
    rw [hvals]
    simp only [L, List.map_append, List.map_cons, List.map_map, List.map_nil,
      Sum.elim_inl, Sum.elim_inr, Function.comp_def, hrval]
    rfl
  rw [hnew]
  exact resize_allocation_cycle hs (kmswMap w (n + 1)) τ L hLnd hresize rfl hLcycle

/-- Induction over all five KMSW branches. The allocating up and pendant
steps are supplied in their induction-step form (`def-kmsw`, -/
theorem stageOuterWord_faceSucc_of_branches
    (hup : ∀ (w : ℕ → Fin 3) (n : ℕ), w n = 1 →
      (∀ d ∈ stageOuterWord w n,
        (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) →
      ∀ d ∈ stageOuterWord w (n + 1),
        (kmswMap w (n + 1)).faceSucc d = (stageOuterWord w (n + 1)).formPerm d)
    (hpendant : ∀ (w : ℕ → Fin 3) (n : ℕ), w n = 2 → (kmswStage w n).UR = [] →
      (∀ d ∈ stageOuterWord w n,
        (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) →
      ∀ d ∈ stageOuterWord w (n + 1),
        (kmswMap w (n + 1)).faceSucc d = (stageOuterWord w (n + 1)).formPerm d) :
    ∀ (w : ℕ → Fin 3) (n : ℕ), ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d := by
  intro w n
  induction n with
  | zero => exact stageOuterWord_faceSucc_zero w
  | succ n ih =>
    have hc : w n = 0 ∨ w n = 1 ∨ w n = 2 := by omega
    rcases hc with hc | hc | hc
    · cases hl : (kmswStage w n).UL.dropLast.reverse with
      | nil => exact stageOuterWord_faceSucc_left_fresh w n hc hl ih
      | cons e es => exact stageOuterWord_faceSucc_left_pred w n e es hc hl ih
    · exact hup w n hc ih
    · cases hr : (kmswStage w n).UR with
      | nil => exact hpendant w n hc hr ih
      | cons e es => exact stageOuterWord_faceSucc_down_activation w n e es hc hr ih

end DirectedDistances.KMSW
