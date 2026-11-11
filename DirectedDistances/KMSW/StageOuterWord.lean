/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageRotation
public import DirectedDistances.KMSW.StageIncidence
public import DirectedDistances.PlanarMap.OuterBoundary

import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # The ordered outer word of a finite KMSW stage

The four ordered boundary runs in `def-kmsw` determine a cyclic dart word -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Lift a stage's edge-ID list to typed geometric darts. The bound is the
allocation invariant for that run (`def-kmsw`, -/
@[expose] def stageDarts (s : State) (es : List ℕ) (side : Bool)
    (hes : ∀ e ∈ es, e < s.nextEdge) : List (StageDart s.nextEdge) :=
  es.attach.map fun e => ((⟨e.1, hes e.1 e.2⟩ : Fin s.nextEdge), side)

/-- Membership in a lifted boundary run retains its source edge ID. -/
theorem stageDarts_mem (s : State) (es : List ℕ) (side : Bool)
    (hes : ∀ e ∈ es, e < s.nextEdge) (d : StageDart s.nextEdge) :
    d ∈ stageDarts s es side hes ↔
      ∃ e, ∃ he : e ∈ es, d = ((⟨e, hes e he⟩ : Fin s.nextEdge), side) := by
  constructor
  · intro hd
    rcases List.mem_map.mp hd with ⟨e, he, hde⟩
    refine ⟨e.1, e.2, ?_⟩
    exact hde.symm
  · rintro ⟨e, he, hde⟩
    apply List.mem_map.mpr
    exact ⟨⟨e, he⟩, List.mem_attach es ⟨e, he⟩, hde.symm⟩

/-- Lifting an edge list to one side preserves duplicate-freeness. -/
theorem stageDarts_nodup (s : State) (es : List ℕ) (side : Bool)
    (hes : ∀ e ∈ es, e < s.nextEdge) (hnd : es.Nodup) :
    (stageDarts s es side hes).Nodup := by
  unfold stageDarts
  apply List.Nodup.map
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun d : StageDart s.nextEdge => d.1.val) hxy
  · exact List.nodup_attach.mpr hnd

/-- The value projection of a typed run has the original edge IDs and order. -/
theorem stageDarts_val (s : State) (es : List ℕ) (side : Bool)
    (hes : ∀ e ∈ es, e < s.nextEdge) :
    (stageDarts s es side hes).map (fun d => (d.1.val, d.2)) =
      es.map fun e => (e, side) := by
  unfold stageDarts
  simp only [List.map_map]
  change (es.attach.map fun e => (e.1, side)) = es.map fun e => (e, side)
  exact List.attach_map_val (l := es) (f := fun e : ℕ => (e, side))

private theorem stageDarts_disjoint_of_edge_disjoint (s : State)
    (xs ys : List ℕ) (side : Bool)
    (hxs : ∀ e ∈ xs, e < s.nextEdge) (hys : ∀ e ∈ ys, e < s.nextEdge)
    (hdisj : List.Disjoint xs ys) :
    List.Disjoint (stageDarts s xs side hxs) (stageDarts s ys side hys) := by
  simp only [List.disjoint_left]
  intro d hd₁ hd₂
  obtain ⟨e, he, hde⟩ := (stageDarts_mem s xs side hxs d).mp hd₁
  obtain ⟨f, hf, hdf⟩ := (stageDarts_mem s ys side hys d).mp hd₂
  have hef : e = f := by
    exact congrArg (fun x : StageDart s.nextEdge => x.1.val) (hde.symm.trans hdf)
  rw [← hef] at hf
  exact (List.disjoint_left.mp hdisj) he hf

private theorem stageDarts_disjoint_of_side_ne (s : State)
    (xs ys : List ℕ) (side₁ side₂ : Bool)
    (hxs : ∀ e ∈ xs, e < s.nextEdge) (hys : ∀ e ∈ ys, e < s.nextEdge)
    (hsides : side₁ ≠ side₂) :
    List.Disjoint (stageDarts s xs side₁ hxs) (stageDarts s ys side₂ hys) := by
  simp only [List.disjoint_left]
  intro d hd₁ hd₂
  obtain ⟨e, he, hde⟩ := (stageDarts_mem s xs side₁ hxs d).mp hd₁
  obtain ⟨f, hf, hdf⟩ := (stageDarts_mem s ys side₂ hys d).mp hd₂
  have hs : side₁ = side₂ := by
    exact congrArg Prod.snd (hde.symm.trans hdf)
  exact hsides hs

private theorem stageDarts_no_common_of_side_ne (s : State)
    (xs ys : List ℕ) (side₁ side₂ : Bool)
    (hxs : ∀ e ∈ xs, e < s.nextEdge) (hys : ∀ e ∈ ys, e < s.nextEdge)
    (hsides : side₁ ≠ side₂) (d : StageDart s.nextEdge)
    (hd₁ : d ∈ stageDarts s xs side₁ hxs)
    (hd₂ : d ∈ stageDarts s ys side₂ hys) : False := by
  obtain ⟨e, he, hde⟩ := (stageDarts_mem s xs side₁ hxs d).mp hd₁
  obtain ⟨f, hf, hdf⟩ := (stageDarts_mem s ys side₂ hys d).mp hd₂
  have hs : side₁ = side₂ := congrArg Prod.snd (hde.symm.trans hdf)
  exact hsides hs

private theorem kmswStage_UL_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.Nodup := by
  rw [kmswStage_UL_eq]
  exact (List.Nodup.filter _ List.nodup_range).map
    (CutConverse.act_injective w)

private theorem kmswStage_LR_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR.Nodup := by
  rw [kmswStage_LR_eq]
  exact (List.Nodup.filter _ List.nodup_range).map
    (CutConverse.act_injective w)

private theorem kmswStage_UL_UR_disjoint (w : ℕ → Fin 3) (n : ℕ) :
    List.Disjoint (kmswStage w n).UL (kmswStage w n).UR := by
  simp only [List.disjoint_left]
  intro e heUL heUR
  have hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
    simp only [List.mem_append]
    tauto)
  have hpresent := (kmswStage_status w n).2.1 e heUL
  have hmissing := ((kmswStage_status w n).1 e hbound).mpr (Or.inl heUR)
  rw [hpresent] at hmissing
  cases hmissing

private theorem kmswStage_LR_LL_disjoint (w : ℕ → Fin 3) (n : ℕ) :
    List.Disjoint (kmswStage w n).LR (kmswStage w n).LL := by
  simp only [List.disjoint_left]
  intro e heLR heLL
  have hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
    simp only [List.mem_append]
    tauto)
  have hpresent := (kmswStage_status w n).2.2.1 e heLR
  have hmissing := ((kmswStage_status w n).1 e hbound).mpr (Or.inr heLL)
  rw [hpresent] at hmissing
  cases hmissing

/-- The cyclic outer-face word: west darts along `UL` and `UR`, then east
darts along `LR` and `LL` in reverse order (`defn:bound-edges`, -/
@[expose] def stageOuterWord (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  let hbound := (kmswStage_boundary_ids_lt_nextEdge w n).2
  exact
    stageDarts s s.UL false (fun e he => hbound e (by
      simp only [List.mem_append]
      tauto)) ++
    stageDarts s s.UR false (fun e he => hbound e (by
      simp only [List.mem_append]
      tauto)) ++
    stageDarts s s.LR.reverse true (fun e he => hbound e (by
      have he' := List.mem_reverse.mp he
      simp only [List.mem_append]
      tauto)) ++
    stageDarts s s.LL.reverse true (fun e he => hbound e (by
      have he' := List.mem_reverse.mp he
      simp only [List.mem_append]
      tauto))

private theorem stageDarts_ne_nil (s : State) (es : List ℕ) (side : Bool)
    (hes : ∀ e ∈ es, e < s.nextEdge) (hne : es ≠ []) :
    stageDarts s es side hes ≠ [] := by
  cases es with
  | nil => exact (hne rfl).elim
  | cons e es => simp [stageDarts]

/-- The outer word is nonempty because the upper-left boundary contains the -/
theorem stageOuterWord_nonempty (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWord w n ≠ [] := by
  have hUL := (kmswStage_UL_nonempty_active_last w n).1
  intro h
  simp only [stageOuterWord, List.append_eq_nil_iff] at h
  exact stageDarts_ne_nil _ _ _ _ hUL h.1.1.1

/-- The four-run outer word has no repeated dart. Opposite darts of one
edge remain distinct, while each individual boundary run is duplicate-free -/
theorem stageOuterWord_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (stageOuterWord w n).Nodup := by
  let s := kmswStage w n
  let hUL : ∀ e ∈ s.UL, e < s.nextEdge := by
    intro e he
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      tauto)
  let hUR : ∀ e ∈ s.UR, e < s.nextEdge := by
    intro e he
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      tauto)
  let hLR : ∀ e ∈ s.LR.reverse, e < s.nextEdge := by
    intro e he
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      have he' := List.mem_reverse.mp he
      simp only [List.mem_append]
      tauto)
  let hLL : ∀ e ∈ s.LL.reverse, e < s.nextEdge := by
    intro e he
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      have he' := List.mem_reverse.mp he
      simp only [List.mem_append]
      tauto)
  let ul := stageDarts s s.UL false hUL
  let ur := stageDarts s s.UR false hUR
  let lr := stageDarts s s.LR.reverse true hLR
  let ll := stageDarts s s.LL.reverse true hLL
  have hULnd : s.UL.Nodup := kmswStage_UL_nodup w n
  have hURnd : s.UR.Nodup := (kmswStage_status w n).2.2.2.1
  have hLRnd : s.LR.Nodup := kmswStage_LR_nodup w n
  have hLLnd : s.LL.Nodup := (kmswStage_status w n).2.2.2.2.1
  have hulnd : ul.Nodup := stageDarts_nodup s s.UL false hUL hULnd
  have hurnd : ur.Nodup := stageDarts_nodup s s.UR false hUR hURnd
  have hlrnd : lr.Nodup := stageDarts_nodup s s.LR.reverse true hLR
    (List.nodup_reverse.mpr hLRnd)
  have hllnd : ll.Nodup := stageDarts_nodup s s.LL.reverse true hLL
    (List.nodup_reverse.mpr hLLnd)
  have hulurdis : List.Disjoint ul ur :=
    stageDarts_disjoint_of_edge_disjoint s s.UL s.UR false hUL hUR
      (kmswStage_UL_UR_disjoint w n)
  have hlrlldis : List.Disjoint lr ll := by
    apply stageDarts_disjoint_of_edge_disjoint
    simpa only [List.disjoint_reverse_left, List.disjoint_reverse_right] using
      (kmswStage_LR_LL_disjoint w n)
  have hleft : (ul ++ ur).Nodup := hulnd.append hurnd hulurdis
  have hright : (lr ++ ll).Nodup := hlrnd.append hllnd hlrlldis
  have hcross : List.Disjoint (ul ++ ur) (lr ++ ll) := by
    simp only [List.disjoint_left, List.mem_append]
    intro d hdLeft hdRight
    rcases hdLeft with hdUL | hdUR
    · rcases hdRight with hdLR | hdLL
      · exact stageDarts_no_common_of_side_ne s s.UL s.LR.reverse false true
          hUL hLR (by decide) d hdUL hdLR
      · exact stageDarts_no_common_of_side_ne s s.UL s.LL.reverse false true
          hUL hLL (by decide) d hdUL hdLL
    · rcases hdRight with hdLR | hdLL
      · exact stageDarts_no_common_of_side_ne s s.UR s.LR.reverse false true
          hUR hLR (by decide) d hdUR hdLR
      · exact stageDarts_no_common_of_side_ne s s.UR s.LL.reverse false true
          hUR hLL (by decide) d hdUR hdLL
  have hrepr : stageOuterWord w n = (ul ++ ur) ++ (lr ++ ll) := by
    simp [stageOuterWord, ul, ur, lr, ll, s, List.append_assoc]
  rw [hrepr]
  exact hleft.append hright hcross

/-- The outer word packaged with its nonemptiness and duplicate-free proofs -/
@[expose]
def stageOuterNonemptyWord (w : ℕ → Fin 3) (n : ℕ) :
    NonemptyWord (StageDart (kmswStage w n).nextEdge) where
  letters := stageOuterWord w n
  nonempty := stageOuterWord_nonempty w n
  nodup := stageOuterWord_nodup w n

/-- The edge-ID and side coordinates of the typed outer word, used to compare
words whose stages have different dart carriers. -/
@[expose] def stageOuterWordVal (w : ℕ → Fin 3) (n : ℕ) : List (ℕ × Bool) :=
  (stageOuterWord w n).map fun d => (d.1.val, d.2)

/-- The value projection is exactly the four source edge-ID runs in their -/
theorem stageOuterWordVal_eq_runs (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWordVal w n =
      ((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false)) ++
      ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
      ((kmswStage w n).LL.reverse.map fun e => (e, true)) := by
  simp [stageOuterWordVal, stageOuterWord, stageDarts, List.map_append,
    List.map_map, List.append_assoc]

/-- Activating the head of `UR` preserves the complete cyclic word: the
newly present edge occupies the same position after it is transferred to the -/
theorem stageOuterWord_down_activation (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hr : (kmswStage w n).UR = e :: es) :
    stageOuterWordVal w (n + 1) = stageOuterWordVal w n := by
  rw [stageOuterWordVal_eq_runs, stageOuterWordVal_eq_runs]
  have hstep : kmswCodeStep (w n) = .down := by
    rw [hc]
    decide
  have hstage : kmswStage w (n + 1) = kmswStepOfStep (kmswStage w n) .down := by
    simp [kmswStage, kmswStep, hstep]
  rw [hstage]
  simp [kmswStepOfStep, hr, List.map_append, List.append_assoc]

end DirectedDistances.KMSW
