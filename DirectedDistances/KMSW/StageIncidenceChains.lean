/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageIncidence
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Ordered boundary chains in finite KMSW stages

Stage-wise incidence facts for the ordered boundary lists in `def-kmsw`, -/

public section
namespace DirectedDistances.KMSW

/-- The upper and lower bookkeeping chains have common endpoints and the UR
list is attached to the active edge (`def-kmsw`, -/
@[expose] def kmswBoundaryChainInvariant (s : State) : Prop :=
  WestEastChain s (s.UL ++ s.UR) ∧
  WestEastChain s (s.LL ++ s.LR) ∧
  boundaryStart s (s.UL ++ s.UR) = boundaryStart s (s.LL ++ s.LR) ∧
  boundaryEnd s (s.UL ++ s.UR) = boundaryEnd s (s.LL ++ s.LR) ∧
  s.LR ≠ [] ∧
  (∀ e es, s.UR = e :: es → s.west e = s.east s.active) ∧
  (∀ hLR : s.LR ≠ [], s.UR = [] → s.east s.active = s.east (s.LR.getLast hLR))

/-- The initial one-edge stage satisfies the boundary chain invariant -/
theorem kmswStage_boundary_chain_invariant_zero (w : ℕ → Fin 3) :
    kmswBoundaryChainInvariant (kmswStage w 0) := by
  simp [kmswBoundaryChainInvariant, WestEastChain, boundaryStart, boundaryEnd,
    kmswStage, kmswInit]

/-- Every allocated initial edge strictly increases the stage rank -/
theorem kmswStageRank_strict_zero (w : ℕ → Fin 3) :
    ∀ e < (kmswStage w 0).nextEdge,
      kmswStageRank w 0 ((kmswStage w 0).west e) <
        kmswStageRank w 0 ((kmswStage w 0).east e) := by
  intro e he
  have he0 : e = 0 := by
    simp [kmswStage, kmswInit] at he
    omega
  subst e
  norm_num [kmswStageRank, kmswStage, kmswInit]

/-- Activating the head of UR moves that edge to UL without changing the -/
theorem kmswStep_down_activate_boundary_invariant (s : State) (e : ℕ)
    (es : List ℕ) (hUR : s.UR = e :: es)
    (hI : kmswBoundaryChainInvariant s) :
    kmswBoundaryChainInvariant (kmswStepOfStep s .down) := by
  rcases hI with ⟨hU, hL, hs, he, hLRne, hhead, hempty⟩
  rw [hUR] at hU hs he
  change (s.UL ++ e :: es).IsChain (fun a b => s.east a = s.west b) at hU
  have hchain : (s.UL ++ [e] ++ es).IsChain (fun a b => s.east a = s.west b) := by
    simpa [List.append_assoc] using hU
  have hstart : boundaryStart s (s.UL ++ [e] ++ es) =
      boundaryStart s (s.LL ++ s.LR) := by
    simpa [List.append_assoc] using hs
  have hend : boundaryEnd s (s.UL ++ [e] ++ es) =
      boundaryEnd s (s.LL ++ s.LR) := by
    simpa [List.append_assoc] using he
  unfold kmswBoundaryChainInvariant
  simp only [kmswStepOfStep, hUR]
  refine ⟨?_, hL, ?_, ?_, hLRne, ?_, ?_⟩
  · change (s.UL ++ [e] ++ es).IsChain (fun a b => s.east a = s.west b)
    simpa [List.append_assoc] using hchain
  · simpa [boundaryStart, List.append_assoc] using hstart
  · simpa [boundaryEnd, List.append_assoc] using hend
  · intro f fs hfs
    subst es
    have hrel := hchain.rel_getLast_head_of_append
      (l₁ := s.UL ++ [e]) (l₂ := f :: fs)
      (List.append_ne_nil_of_right_ne_nil _ (by simp)) (by simp)
    simpa using hrel.symm
  · intro hLR hnil
    subst es
    have hu : boundaryEnd s (s.UL ++ [e]) = some (s.east e) := by
      change Option.map s.east (s.UL ++ [e]).getLast? = _
      rw [List.getLast?_eq_getLast_of_ne_nil
        (List.append_ne_nil_of_right_ne_nil _ (by simp))]
      rw [List.getLast_append_singleton]
      rfl
    have hl : boundaryEnd s (s.LL ++ s.LR) =
        some (s.east (s.LR.getLast hLRne)) := by
      change Option.map s.east (s.LL ++ s.LR).getLast? = _
      rw [List.getLast?_eq_getLast_of_ne_nil
        (List.append_ne_nil_of_right_ne_nil _ hLRne)]
      rw [List.getLast_append_of_right_ne_nil _ _ hLRne]
      rfl
    have he' : boundaryEnd s (s.UL ++ [e]) = boundaryEnd s (s.LL ++ s.LR) := by
      exact he
    rw [hu, hl] at he'
    exact Option.some.inj he'

private theorem chain_transfer_endpoints {s t : State} {es : List ℕ}
    (hW : ∀ e ∈ es, t.west e = s.west e)
    (hE : ∀ e ∈ es, t.east e = s.east e)
    (hc : List.IsChain (fun e f => s.east e = s.west f) es) :
    List.IsChain (fun e f => t.east e = t.west f) es := by
  apply (List.IsChain.iff_of_mem_tail_imp (R := fun e f => s.east e = s.west f)
    (S := fun e f => t.east e = t.west f) (l := es) ?_).1 hc
  intro e f he hf
  have hf' : f ∈ es := List.mem_of_mem_tail hf
  constructor <;> intro h
  · rw [hE e he, hW f hf']
    exact h
  · rw [hE e he, hW f hf'] at h
    exact h

private theorem boundaryStart_stable {s t : State} {es : List ℕ}
    (hW : ∀ e ∈ es, t.west e = s.west e) :
    boundaryStart t es = boundaryStart s es := by
  unfold boundaryStart
  cases hh : es.head? with
  | none => rfl
  | some e =>
    have heOpt : e ∈ es.head? := by simp [hh]
    have he : e ∈ es := List.mem_of_mem_head? heOpt
    simp only [Option.map_some]
    exact congrArg some (hW e he)

private theorem boundaryEnd_stable {s t : State} {es : List ℕ}
    (hE : ∀ e ∈ es, t.east e = s.east e) :
    boundaryEnd t es = boundaryEnd s es := by
  unfold boundaryEnd
  cases hh : es.getLast? with
  | none => rfl
  | some e =>
    have heOpt : e ∈ es.getLast? := by simp [hh]
    have he : e ∈ es := List.mem_of_mem_getLast? heOpt
    simp only [Option.map_some]
    exact congrArg some (hE e he)

private theorem boundaryStart_heads_eq {s : State} {xs ys : List ℕ}
    (hxs : xs ≠ []) (hys : ys ≠ [])
    (h : boundaryStart s xs = boundaryStart s ys) :
    s.west (xs.head hxs) = s.west (ys.head hys) := by
  unfold boundaryStart at h
  rw [List.head?_eq_some_head hxs, List.head?_eq_some_head hys] at h
  exact Option.some.inj h

/-- A left step with no UL predecessor adds the two fresh boundary edges and -/
theorem kmswStage_left_fresh_boundary_invariant (w : ℕ → Fin 3) (n : ℕ)
    (hw : w n = 0)
    (hfresh : (kmswStage w n).UL.dropLast.reverse = [])
    (hI : kmswBoundaryChainInvariant (kmswStage w n)) :
    kmswBoundaryChainInvariant (kmswStage w (n + 1)) := by
  let s := kmswStage w n
  let t := kmswStepOfStep s .left
  have hfreshS : s.UL.dropLast.reverse = [] := hfresh
  have hdrop : s.UL.dropLast = [] := by
    have hh := congrArg List.reverse hfreshS
    simpa using hh
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hxsS : s.UL = xs ++ [s.active] := by simpa [s] using hxs
  have hxsDrop : xs = s.UL.dropLast := by rw [hxsS]; simp
  have hxsNil : xs = [] := hxsDrop.trans hdrop
  have hULsingle : s.UL = [s.active] := by simpa [hxsNil] using hxsS
  have hULbound : ∀ f ∈ s.UL, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hURbound : ∀ f ∈ s.UR, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hLowBound : ∀ f ∈ s.LL ++ s.LR, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hOldW : ∀ f < s.nextEdge, t.west f = s.west f := by
    intro f hf
    have h0 : f ≠ s.nextEdge := by omega
    have h1 : f ≠ s.nextEdge + 1 := by omega
    simp [t, kmswStepOfStep, hfreshS, State.addEdge, h0, h1]
  have hOldE : ∀ f < s.nextEdge, t.east f = s.east f := by
    intro f hf
    have h0 : f ≠ s.nextEdge := by omega
    have h1 : f ≠ s.nextEdge + 1 := by omega
    simp [t, kmswStepOfStep, hfreshS, State.addEdge, h0, h1]
  have hNewWest : t.west s.nextEdge = s.nextVertex := by
    simp [t, kmswStepOfStep, hfreshS, State.addEdge]
  have hNewEast : t.east s.nextEdge = s.east s.active := by
    simp [t, kmswStepOfStep, hfreshS, State.addEdge]
  have hMissingWest : t.west (s.nextEdge + 1) = s.nextVertex := by
    simp [t, kmswStepOfStep, hfreshS, State.addEdge]
  have hMissingEast : t.east (s.nextEdge + 1) = s.west s.active := by
    simp [t, kmswStepOfStep, hfreshS, State.addEdge]
  have hFields : t.UL = [s.nextEdge] ∧ t.UR = s.UR ∧
      t.LL = (s.nextEdge + 1) :: s.LL ∧ t.LR = s.LR ∧ t.active = s.nextEdge := by
    simp [t, kmswStepOfStep, hfreshS, State.addEdge]
  have hNext : t = kmswStage w (n + 1) := by
    simp [t, s, kmswStage, kmswStep, hw, kmswCodeStep, kmswStepOfStep, hfreshS]
  rcases hI with ⟨hU, hL, hstart, hend, hLR, hhead, hempty⟩
  have hLowNonempty : s.LL ++ s.LR ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ hLR
  have hOldUpperChain : List.IsChain (fun a b => s.east a = s.west b)
      (s.active :: s.UR) := by
    have h := hU
    change List.IsChain (fun a b => s.east a = s.west b) (s.UL ++ s.UR) at h
    rw [hULsingle] at h
    simpa using h
  have hURold : List.IsChain (fun a b => s.east a = s.west b) s.UR :=
    hOldUpperChain.tail
  have hURnew : List.IsChain (fun a b => t.east a = t.west b) s.UR :=
    chain_transfer_endpoints (s := s) (t := t)
      (hW := fun f hf => hOldW f (hURbound f hf))
      (hE := fun f hf => hOldE f (hURbound f hf)) hURold
  have hUpperChain : List.IsChain (fun a b => t.east a = t.west b)
      (s.nextEdge :: s.UR) := by
    apply hURnew.cons
    intro f hf
    have hrel := hOldUpperChain.rel_head? hf
    have hfUR : f ∈ s.UR := List.mem_of_mem_head? hf
    rw [hNewEast, hOldW f (hURbound f hfUR)]
    exact hrel
  have hLowerOld : List.IsChain (fun a b => s.east a = s.west b) (s.LL ++ s.LR) := by
    simpa [WestEastChain] using hL
  have hLowerStable : List.IsChain (fun a b => t.east a = t.west b) (s.LL ++ s.LR) :=
    chain_transfer_endpoints (s := s) (t := t)
      (hW := fun f hf => hOldW f (hLowBound f hf))
      (hE := fun f hf => hOldE f (hLowBound f hf)) hLowerOld
  have hLowerHeadWest : s.west ((s.LL ++ s.LR).head hLowNonempty) =
      s.west s.active := by
    have htop : boundaryStart s (s.UL ++ s.UR) = some (s.west s.active) := by
      simp [boundaryStart, hULsingle]
    have hlow : boundaryStart s (s.LL ++ s.LR) =
        some (s.west ((s.LL ++ s.LR).head hLowNonempty)) := by
      unfold boundaryStart
      rw [List.head?_eq_some_head hLowNonempty]
      simp only [Option.map_some]
    have hEq := hstart
    rw [htop, hlow] at hEq
    exact (Option.some.inj hEq).symm
  have hLowerChain : List.IsChain (fun a b => t.east a = t.west b)
      ((s.nextEdge + 1) :: (s.LL ++ s.LR)) := by
    apply List.IsChain.cons_of_ne_nil hLowNonempty hLowerStable
    calc
      t.east (s.nextEdge + 1) = s.west s.active := hMissingEast
      _ = s.west ((s.LL ++ s.LR).head hLowNonempty) := hLowerHeadWest.symm
      _ = t.west ((s.LL ++ s.LR).head hLowNonempty) :=
        (hOldW _ (hLowBound _ (List.head_mem _))).symm
  have hStartUpper : boundaryStart t (s.nextEdge :: s.UR) = some s.nextVertex := by
    simp [boundaryStart, hNewWest]
  have hStartLower : boundaryStart t ((s.nextEdge + 1) :: (s.LL ++ s.LR)) =
      some s.nextVertex := by
    simp [boundaryStart, hMissingWest]
  have hLowEndStable : boundaryEnd t (s.LL ++ s.LR) =
      boundaryEnd s (s.LL ++ s.LR) :=
    boundaryEnd_stable (fun f hf => hOldE f (hLowBound f hf))
  have hEndLower : boundaryEnd t ((s.nextEdge + 1) :: (s.LL ++ s.LR)) =
      boundaryEnd s (s.LL ++ s.LR) := by
    calc
      boundaryEnd t ((s.nextEdge + 1) :: (s.LL ++ s.LR)) =
          boundaryEnd t (s.LL ++ s.LR) := by
        cases hl : s.LL ++ s.LR with
        | nil => exact (hLowNonempty hl).elim
        | cons q qs => simp [boundaryEnd]
      _ = boundaryEnd s (s.LL ++ s.LR) := hLowEndStable
  have hEndUpper : boundaryEnd t (s.nextEdge :: s.UR) =
      boundaryEnd s (s.active :: s.UR) := by
    cases hu : s.UR with
    | nil =>
      simp only [boundaryEnd, List.getLast?_singleton, Option.map_some]
      exact congrArg some hNewEast
    | cons q qs =>
      have hnewLast : (s.nextEdge :: (q :: qs)).getLast? = (q :: qs).getLast? := by
        exact List.getLast?_append_of_ne_nil [s.nextEdge] (by simp)
      have holdLast : (s.active :: (q :: qs)).getLast? = (q :: qs).getLast? := by
        exact List.getLast?_append_of_ne_nil [s.active] (by simp)
      unfold boundaryEnd
      rw [hnewLast, holdLast]
      exact boundaryEnd_stable (fun f hf =>
        hOldE f (hURbound f (by rw [hu]; exact hf)))
  have hOldUpperEnd : boundaryEnd s (s.active :: s.UR) =
      boundaryEnd s (s.UL ++ s.UR) := by
    simp [hULsingle]
  have hEndUpper' := hEndUpper.trans hOldUpperEnd
  have hHeadNew : ∀ f fs, s.UR = f :: fs → t.west f = t.east s.nextEdge := by
    intro f fs hf
    have hbound := hURbound f (by rw [hf]; simp)
    calc
      t.west f = s.west f := hOldW f hbound
      _ = s.east s.active := hhead f fs hf
      _ = t.east s.nextEdge := hNewEast.symm
  have hEmptyNew : ∀ hLR' : s.LR ≠ [], s.UR = [] →
      t.east s.nextEdge = t.east (s.LR.getLast hLR') := by
    intro hLR' hu
    calc
      t.east s.nextEdge = s.east s.active := hNewEast
      _ = s.east (s.LR.getLast hLR') := hempty hLR' hu
      _ = t.east (s.LR.getLast hLR') :=
        (hOldE _ (hLowBound _ (List.mem_append_right _ (List.getLast_mem _)))).symm
  rw [← hNext]
  unfold kmswBoundaryChainInvariant
  rw [hFields.1, hFields.2.1, hFields.2.2.1, hFields.2.2.2.1, hFields.2.2.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change List.IsChain (fun a b => t.east a = t.west b) (s.nextEdge :: s.UR)
    exact hUpperChain
  · change List.IsChain (fun a b => t.east a = t.west b)
      ((s.nextEdge + 1) :: (s.LL ++ s.LR))
    exact hLowerChain
  · exact hStartUpper.trans hStartLower.symm
  · exact hEndUpper'.trans (hend.trans hEndLower.symm)
  · exact hLR
  · exact hHeadNew
  · exact hEmptyNew

/-- An up step replaces the active edge by two consecutive upper edges while -/
theorem kmswStage_up_boundary_invariant (w : ℕ → Fin 3) (n : ℕ)
    (hw : w n = 1)
    (hI : kmswBoundaryChainInvariant (kmswStage w n)) :
    kmswBoundaryChainInvariant (kmswStage w (n + 1)) := by
  let s := kmswStage w n
  let t := kmswStepOfStep s .up
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hxsS : s.UL = xs ++ [s.active] := by simpa [s] using hxs
  have hxsDrop : xs = s.UL.dropLast := by rw [hxsS]; simp
  have hULne : s.UL ≠ [] := by rw [hxsS]; simp
  have hULbound : ∀ f ∈ s.UL, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hURbound : ∀ f ∈ s.UR, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hLowBound : ∀ f ∈ s.LL ++ s.LR, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hOldW : ∀ f < s.nextEdge, t.west f = s.west f := by
    intro f hf
    have h0 : f ≠ s.nextEdge := by omega
    have h1 : f ≠ s.nextEdge + 1 := by omega
    simp [t, kmswStepOfStep, State.addEdge, h0, h1]
  have hOldE : ∀ f < s.nextEdge, t.east f = s.east f := by
    intro f hf
    have h0 : f ≠ s.nextEdge := by omega
    have h1 : f ≠ s.nextEdge + 1 := by omega
    simp [t, kmswStepOfStep, State.addEdge, h0, h1]
  have hNewWest : t.west s.nextEdge = s.west s.active := by
    simp [t, kmswStepOfStep, State.addEdge]
  have hNewEast : t.east s.nextEdge = s.nextVertex := by
    simp [t, kmswStepOfStep, State.addEdge]
  have hMissingWest : t.west (s.nextEdge + 1) = s.nextVertex := by
    simp [t, kmswStepOfStep, State.addEdge]
  have hMissingEast : t.east (s.nextEdge + 1) = s.east s.active := by
    simp [t, kmswStepOfStep, State.addEdge]
  have hFields : t.UL = s.UL.dropLast ++ [s.nextEdge] ∧
      t.UR = (s.nextEdge + 1) :: s.UR ∧ t.LL = s.LL ∧ t.LR = s.LR ∧
      t.active = s.nextEdge := by
    simp [t, kmswStepOfStep, State.addEdge]
  have hNext : t = kmswStage w (n + 1) := by
    simp [t, s, kmswStage, kmswStep, hw, kmswCodeStep, kmswStepOfStep, State.addEdge]
  rcases hI with ⟨hU, hL, hstart, hend, hLR, hhead, hempty⟩
  have hOldUpper : List.IsChain (fun a b => s.east a = s.west b)
      (s.UL ++ s.UR) := by simpa [WestEastChain] using hU
  have hULchain : List.IsChain (fun a b => s.east a = s.west b) s.UL :=
    hOldUpper.left_of_append
  have hXsActive : List.IsChain (fun a b => s.east a = s.west b)
      (xs ++ [s.active]) := by rw [← hxsS]; exact hULchain
  have hXsChain : List.IsChain (fun a b => s.east a = s.west b) xs :=
    hXsActive.left_of_append
  have hOldURchain : List.IsChain (fun a b => s.east a = s.west b) s.UR :=
    hOldUpper.right_of_append
  have hPrefixNew : List.IsChain (fun a b => t.east a = t.west b) (xs ++ [s.nextEdge]) := by
    have hxsStable : List.IsChain (fun a b => t.east a = t.west b) xs :=
      chain_transfer_endpoints (s := s) (t := t)
        (hW := fun f hf => hOldW f (hULbound f (by rw [hxsS]; exact List.mem_append_left _ hf)))
        (hE := fun f hf => hOldE f (hULbound f (by rw [hxsS]; exact List.mem_append_left _ hf)))
        hXsChain
    apply hxsStable.append (List.isChain_singleton _)
    intro f hf g hg
    obtain ⟨hnonempty, rfl⟩ := List.mem_getLast?_eq_getLast hf
    simp only [List.head?_singleton, Option.mem_some_iff] at hg
    subst g
    have hrel : s.east (xs.getLast hnonempty) = s.west s.active := by
      simpa using hXsActive.rel_getLast_head_of_append hnonempty (by simp)
    have hlastMem : xs.getLast hnonempty ∈ xs := List.getLast_mem hnonempty
    have hULmem : xs.getLast hnonempty ∈ s.UL := by
      rw [hxsS]
      exact List.mem_append_left _ hlastMem
    have hbound := hULbound _ hULmem
    calc
      t.east (xs.getLast hnonempty) = s.east (xs.getLast hnonempty) := hOldE _ hbound
      _ = s.west s.active := hrel
      _ = t.west s.nextEdge := hNewWest.symm
  have hActiveUR : ∀ f ∈ s.UR.head?, s.east s.active = s.west f := by
    intro f hf
    have hcons : s.UR = f :: s.UR.tail := List.eq_cons_of_mem_head? hf
    exact (hhead f s.UR.tail hcons).symm
  have hURnew : List.IsChain (fun a b => t.east a = t.west b) s.UR :=
    chain_transfer_endpoints (s := s) (t := t)
      (hW := fun f hf => hOldW f (hURbound f hf))
      (hE := fun f hf => hOldE f (hURbound f hf)) hOldURchain
  have hAfterNew : List.IsChain (fun a b => t.east a = t.west b)
      ((s.nextEdge + 1) :: s.UR) := by
    apply hURnew.cons
    intro f hf
    have hfUR : f ∈ s.UR := List.mem_of_mem_head? hf
    calc
      t.east (s.nextEdge + 1) = s.east s.active := hMissingEast
      _ = s.west f := hActiveUR f hf
      _ = t.west f := (hOldW f (hURbound f hfUR)).symm
  have hUpperChain : List.IsChain (fun a b => t.east a = t.west b)
      ((xs ++ [s.nextEdge]) ++ ((s.nextEdge + 1) :: s.UR)) := by
    have hJoin : ∀ f ∈ (xs ++ [s.nextEdge]).getLast?,
        ∀ g ∈ ((s.nextEdge + 1) :: s.UR).head?, t.east f = t.west g := by
      intro f hf g hg
      obtain ⟨hnonempty, rfl⟩ := List.mem_getLast?_eq_getLast hf
      simp only [List.head?_cons, Option.mem_some_iff] at hg
      subst g
      have hlast : (xs ++ [s.nextEdge]).getLast hnonempty = s.nextEdge :=
        List.getLast_append_singleton xs
      rw [hlast, hNewEast, hMissingWest]
    exact hPrefixNew.append hAfterNew hJoin
  have hLowerOld : List.IsChain (fun a b => s.east a = s.west b) (s.LL ++ s.LR) := by
    simpa [WestEastChain] using hL
  have hLowerChain : List.IsChain (fun a b => t.east a = t.west b) (s.LL ++ s.LR) :=
    chain_transfer_endpoints (s := s) (t := t)
      (hW := fun f hf => hOldW f (hLowBound f hf))
      (hE := fun f hf => hOldE f (hLowBound f hf)) hLowerOld
  have hStartLower : boundaryStart t (s.LL ++ s.LR) =
      boundaryStart s (s.LL ++ s.LR) :=
    boundaryStart_stable (fun f hf => hOldW f (hLowBound f hf))
  have hEndLower : boundaryEnd t (s.LL ++ s.LR) =
      boundaryEnd s (s.LL ++ s.LR) :=
    boundaryEnd_stable (fun f hf => hOldE f (hLowBound f hf))
  have hStartUpper : boundaryStart t
      ((xs ++ [s.nextEdge]) ++ ((s.nextEdge + 1) :: s.UR)) =
      boundaryStart s ((xs ++ [s.active]) ++ s.UR) := by
    cases hx : xs with
    | nil =>
      simp [boundaryStart, hNewWest]
    | cons p ps =>
      have hpUL : p ∈ s.UL := by rw [hxsS]; simp [hx]
      simp [boundaryStart, hOldW p (hULbound p hpUL)]
  have hOldUpperList : (xs ++ [s.active]) ++ s.UR = s.UL ++ s.UR := by
    rw [← hxsS]
  have hStartUpper' : boundaryStart t
      ((xs ++ [s.nextEdge]) ++ ((s.nextEdge + 1) :: s.UR)) =
      boundaryStart s (s.UL ++ s.UR) := by
    rw [← hOldUpperList]
    exact hStartUpper
  have hEndUpper : boundaryEnd t
      ((xs ++ [s.nextEdge]) ++ ((s.nextEdge + 1) :: s.UR)) =
      boundaryEnd s ((xs ++ [s.active]) ++ s.UR) := by
    cases hu : s.UR with
    | nil =>
      have hnewLast : ((xs ++ [s.nextEdge]) ++ [s.nextEdge + 1]).getLast? =
          some (s.nextEdge + 1) := by
        rw [List.getLast?_append_of_ne_nil (xs ++ [s.nextEdge]) (by simp)]
        simp
      have holdLast : (xs ++ [s.active]).getLast? = some s.active := by
        rw [List.getLast?_append_of_ne_nil xs (by simp : ([s.active] : List ℕ) ≠ [])]
        simp
      simp only [List.append_nil, boundaryEnd, hnewLast, holdLast, Option.map_some]
      exact congrArg some hMissingEast
    | cons q qs =>
      have hnewLast : ((xs ++ [s.nextEdge]) ++ ((s.nextEdge + 1) :: (q :: qs))).getLast? =
          (q :: qs).getLast? :=
        List.getLast?_append_of_ne_nil (xs ++ [s.nextEdge]) (by simp)
      have holdLast : ((xs ++ [s.active]) ++ (q :: qs)).getLast? = (q :: qs).getLast? :=
        List.getLast?_append_of_ne_nil (xs ++ [s.active]) (by simp)
      unfold boundaryEnd
      rw [hnewLast, holdLast]
      exact boundaryEnd_stable (fun f hf => hOldE f (hURbound f (by rw [hu]; exact hf)))
  have hEndUpper' : boundaryEnd t
      ((xs ++ [s.nextEdge]) ++ ((s.nextEdge + 1) :: s.UR)) =
      boundaryEnd s (s.UL ++ s.UR) := by
    rw [← hOldUpperList]
    exact hEndUpper
  have hFieldsULList : s.UL.dropLast = xs := hxsDrop.symm
  rw [← hNext]
  unfold kmswBoundaryChainInvariant
  rw [hFields.1, hFields.2.1, hFields.2.2.1, hFields.2.2.2.1, hFields.2.2.2.2,
    hFieldsULList]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change List.IsChain (fun a b => t.east a = t.west b)
      ((xs ++ [s.nextEdge]) ++ ((s.nextEdge + 1) :: s.UR))
    exact hUpperChain
  · change List.IsChain (fun a b => t.east a = t.west b) (s.LL ++ s.LR)
    exact hLowerChain
  · exact hStartUpper'.trans (hstart.trans hStartLower.symm)
  · exact hEndUpper'.trans (hend.trans hEndLower.symm)
  · exact hLR
  · intro f fs hf
    have hcons : (s.nextEdge + 1) :: s.UR = f :: fs := by
      calc
        (s.nextEdge + 1) :: s.UR = t.UR := hFields.2.1.symm
        _ = f :: fs := hf
    have hfirst : f = s.nextEdge + 1 := (List.cons.inj hcons).1.symm
    rw [hfirst]
    exact hMissingWest.trans hNewEast.symm
  · intro hLR' hu
    have htUR : (s.nextEdge + 1) :: s.UR = [] := by
      calc
        (s.nextEdge + 1) :: s.UR = t.UR := hFields.2.1.symm
        _ = [] := hu
    simp at htUR

/-- A left step which consumes the predecessor of the active UL edge preserves -/
theorem kmswStage_left_predecessor_boundary_invariant (w : ℕ → Fin 3) (n : ℕ)
    (hw : w n = 0) (e : ℕ) (es : List ℕ)
    (hpred : (kmswStage w n).UL.dropLast.reverse = e :: es)
    (hI : kmswBoundaryChainInvariant (kmswStage w n)) :
    kmswBoundaryChainInvariant (kmswStage w (n + 1)) := by
  let s := kmswStage w n
  let t := kmswStepOfStep s .left
  have hpredS : s.UL.dropLast.reverse = e :: es := hpred
  have hdrop : s.UL.dropLast = es.reverse ++ [e] := by
    have h := congrArg List.reverse hpredS
    simpa only [List.reverse_cons, List.reverse_reverse] using h
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hxsS : s.UL = xs ++ [s.active] := by simpa [s] using hxs
  have hxsDrop : xs = s.UL.dropLast := by rw [hxsS]; simp
  have hULold : s.UL = (es.reverse ++ [e]) ++ [s.active] := by
    calc
      s.UL = xs ++ [s.active] := hxs
      _ = s.UL.dropLast ++ [s.active] := by rw [← hxsDrop]
      _ = (es.reverse ++ [e]) ++ [s.active] := by rw [hdrop]
  have hULbound : ∀ f ∈ s.UL, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hURbound : ∀ f ∈ s.UR, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hLowBound : ∀ f ∈ s.LL ++ s.LR, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hOldUpperBound : ∀ f ∈ s.UL ++ s.UR, f < s.nextEdge := by
    intro f hf
    have hmem : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append] at hf ⊢
      tauto
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by simpa [s] using hmem)
  have hOldW : ∀ f < s.nextEdge, t.west f = s.west f := by
    intro f hf
    have hne : f ≠ s.nextEdge := by omega
    simp [t, kmswStepOfStep, hpredS, State.addEdge, hne]
  have hOldE : ∀ f < s.nextEdge, t.east f = s.east f := by
    intro f hf
    have hne : f ≠ s.nextEdge := by omega
    simp [t, kmswStepOfStep, hpredS, State.addEdge, hne]
  have hNewW : t.west s.nextEdge = s.west e := by
    simp [t, kmswStepOfStep, hpredS, State.addEdge]
  have hNewE : t.east s.nextEdge = s.east s.active := by
    simp [t, kmswStepOfStep, hpredS, State.addEdge]
  have hFields : t.UL = es.reverse ++ [s.nextEdge] ∧ t.UR = s.UR ∧
      t.LL = s.LL ∧ t.LR = s.LR ∧ t.active = s.nextEdge := by
    simp [t, kmswStepOfStep, hpredS, State.addEdge]
  have hNext : t = kmswStage w (n + 1) := by
    simp [t, s, kmswStage, kmswStep, hw, kmswCodeStep, kmswStepOfStep, hpredS]
  rcases hI with ⟨hU, hL, hstart, hend, hLR, hhead, hempty⟩
  have hOldChain : List.IsChain (fun a b => s.east a = s.west b) (s.UL ++ s.UR) := by
    simpa [WestEastChain] using hU
  have hOldChain' : List.IsChain (fun a b => s.east a = s.west b)
      ((es.reverse ++ [e]) ++ (s.active :: s.UR)) := by
    have hEq : (es.reverse ++ [e]) ++ (s.active :: s.UR) = s.UL ++ s.UR := by
      rw [hULold]
      simp [List.append_assoc]
    exact hEq ▸ hOldChain
  have hPrefixE : List.IsChain (fun a b => s.east a = s.west b)
      (es.reverse ++ [e]) := hOldChain'.left_of_append
  have hSuffix : List.IsChain (fun a b => s.east a = s.west b)
      (s.active :: s.UR) := hOldChain'.right_of_append
  have hPrefix : List.IsChain (fun a b => s.east a = s.west b) es.reverse :=
    hPrefixE.left_of_append
  have hURchain : List.IsChain (fun a b => s.east a = s.west b) s.UR := hSuffix.tail
  have hPrevRel : ∀ f ∈ es.reverse.getLast?, t.east f = t.west s.nextEdge := by
    intro f hf
    obtain ⟨hne, rfl⟩ := List.mem_getLast?_eq_getLast hf
    have hrel := hPrefixE.rel_getLast_head_of_append hne (by simp)
    have hfUL : es.reverse.getLast hne ∈ s.UL := by
      rw [hULold]
      exact List.mem_append_left _ (List.mem_append_left _ (by simp))
    calc
      t.east (es.reverse.getLast hne) = s.east (es.reverse.getLast hne) :=
        hOldE _ (hULbound _ hfUL)
      _ = s.west e := hrel
      _ = t.west s.nextEdge := hNewW.symm
  have hPrefixNew : List.IsChain (fun a b => t.east a = t.west b) es.reverse :=
    chain_transfer_endpoints (s := s) (t := t)
      (hW := fun f hf => hOldW f (hULbound f (by
        rw [hULold]
        exact List.mem_append_left _ (List.mem_append_left _ hf))))
      (hE := fun f hf => hOldE f (hULbound f (by
        rw [hULold]
        exact List.mem_append_left _ (List.mem_append_left _ hf)))) hPrefix
  have hBefore : List.IsChain (fun a b => t.east a = t.west b)
      (es.reverse ++ [s.nextEdge]) := by
    apply hPrefixNew.append (List.isChain_singleton _)
    intro f hf g hg
    obtain ⟨hne, rfl⟩ := List.mem_getLast?_eq_getLast hf
    simp only [List.head?_singleton, Option.mem_some_iff] at hg
    subst g
    exact hPrevRel _ hf
  have hURnew : List.IsChain (fun a b => t.east a = t.west b) s.UR :=
    chain_transfer_endpoints (s := s) (t := t)
      (hW := fun f hf => hOldW f (hURbound f hf))
      (hE := fun f hf => hOldE f (hURbound f hf)) hURchain
  have hAfterRel : ∀ f ∈ (es.reverse ++ [s.nextEdge]).getLast?, ∀ g ∈ s.UR.head?,
      t.east f = t.west g := by
    intro f hf g hg
    rw [List.getLast?_append_of_ne_nil _ (by simp)] at hf
    simp only [List.getLast?_singleton, Option.mem_some_iff] at hf
    subst f
    have hrel := hSuffix.rel_head? hg
    have hgUR : g ∈ s.UR := List.mem_of_mem_head? hg
    rw [hNewE, hOldW g (hURbound g hgUR)]
    exact hrel
  have hUpperChain : List.IsChain (fun a b => t.east a = t.west b)
      ((es.reverse ++ [s.nextEdge]) ++ s.UR) := hBefore.append hURnew hAfterRel
  have hLowerChain : List.IsChain (fun a b => t.east a = t.west b) (s.LL ++ s.LR) :=
    chain_transfer_endpoints (s := s) (t := t)
      (hW := fun f hf => hOldW f (hLowBound f hf))
      (hE := fun f hf => hOldE f (hLowBound f hf)) (by simpa [WestEastChain] using hL)
  have hStartLower : boundaryStart t (s.LL ++ s.LR) =
      boundaryStart s (s.LL ++ s.LR) :=
    boundaryStart_stable (fun f hf => hOldW f (hLowBound f hf))
  have hEndLower : boundaryEnd t (s.LL ++ s.LR) =
      boundaryEnd s (s.LL ++ s.LR) :=
    boundaryEnd_stable (fun f hf => hOldE f (hLowBound f hf))
  have hStartUpper : boundaryStart t ((es.reverse ++ [s.nextEdge]) ++ s.UR) =
      boundaryStart s ((es.reverse ++ [e, s.active]) ++ s.UR) := by
    cases hp : es.reverse with
    | nil =>
      simp [boundaryStart]
      exact hNewW
    | cons p ps =>
      have hpUL : p ∈ s.UL := by
        rw [hULold]
        simp [hp]
      simp [boundaryStart]
      exact hOldW p (hULbound p hpUL)
  have hOldUpperList : (es.reverse ++ [e, s.active]) ++ s.UR = s.UL ++ s.UR := by
    rw [hULold]
    simp [List.append_assoc]
  have hEndUpper : boundaryEnd t ((es.reverse ++ [s.nextEdge]) ++ s.UR) =
      boundaryEnd s ((es.reverse ++ [e, s.active]) ++ s.UR) := by
    cases hu : s.UR with
    | nil =>
      have hnewLast : (es.reverse ++ [s.nextEdge]).getLast? = some s.nextEdge := by
        rw [List.getLast?_append_of_ne_nil es.reverse (by simp : ([s.nextEdge] : List ℕ) ≠ [])]
        simp
      have holdLast : (es.reverse ++ [e, s.active]).getLast? = some s.active := by
        rw [List.getLast?_append_of_ne_nil es.reverse
          (by simp : ([e, s.active] : List ℕ) ≠ [])]
        simp
      simp only [List.append_nil, boundaryEnd, hnewLast, holdLast, Option.map_some]
      exact congrArg some hNewE
    | cons q qs =>
      have hnewLast : ((es.reverse ++ [s.nextEdge]) ++ (q :: qs)).getLast? =
          (q :: qs).getLast? :=
        List.getLast?_append_of_ne_nil (es.reverse ++ [s.nextEdge]) (by simp)
      have holdLast : ((es.reverse ++ [e, s.active]) ++ (q :: qs)).getLast? =
          (q :: qs).getLast? :=
        List.getLast?_append_of_ne_nil (es.reverse ++ [e, s.active]) (by simp)
      unfold boundaryEnd
      rw [hnewLast, holdLast]
      exact boundaryEnd_stable (fun f hf =>
        hOldE f (hURbound f (by rw [hu]; exact hf)))
  have hStartUpper' : boundaryStart t ((es.reverse ++ [s.nextEdge]) ++ s.UR) =
      boundaryStart s (s.UL ++ s.UR) := by
    rw [← hOldUpperList]
    exact hStartUpper
  have hEndUpper' : boundaryEnd t ((es.reverse ++ [s.nextEdge]) ++ s.UR) =
      boundaryEnd s (s.UL ++ s.UR) := by
    rw [← hOldUpperList]
    exact hEndUpper
  rw [← hNext]
  unfold kmswBoundaryChainInvariant
  rw [hFields.1, hFields.2.1, hFields.2.2.1, hFields.2.2.2.1, hFields.2.2.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change List.IsChain (fun a b => t.east a = t.west b)
      ((es.reverse ++ [s.nextEdge]) ++ s.UR)
    exact hUpperChain
  · change List.IsChain (fun a b => t.east a = t.west b) (s.LL ++ s.LR)
    exact hLowerChain
  · exact hStartUpper'.trans (hstart.trans hStartLower.symm)
  · exact hEndUpper'.trans (hend.trans hEndLower.symm)
  · exact hLR
  · intro f fs hf
    have ht : t.UR = f :: fs := by rw [hFields.2.1]; exact hf
    have hbound := hURbound f (by rw [hf]; simp)
    calc
      t.west f = s.west f := hOldW f hbound
      _ = s.east s.active := hhead f fs hf
      _ = t.east s.nextEdge := hNewE.symm
  · intro hLR' hu
    have huT : t.UR = [] := by rw [hFields.2.1]; exact hu
    calc
      t.east s.nextEdge = s.east s.active := hNewE
      _ = s.east (s.LR.getLast hLR') := hempty hLR' hu
      _ = t.east (s.LR.getLast hLR') :=
        (hOldE _ (hLowBound _ (List.mem_append_right _ (List.getLast_mem _)))).symm

/-- A down step with empty UR appends a pendant edge to both boundaries and
preserves the ordered chain invariant (`def-kmsw`, -/
theorem kmswStage_down_pendant_boundary_invariant (w : ℕ → Fin 3) (n : ℕ)
    (hw : w n = 2)
    (hUR : (kmswStage w n).UR = [])
    (hI : kmswBoundaryChainInvariant (kmswStage w n)) :
    kmswBoundaryChainInvariant (kmswStepOfStep (kmswStage w n) .down) := by
  let s := kmswStage w n
  have hURs : s.UR = [] := hUR
  let t := kmswStepOfStep s .down
  rcases hI with ⟨hU, hL, hstart, _, hLR, _, hempty⟩
  have hULne : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last w n).1
  have hULlast? : s.UL.getLast? = some s.active :=
    (kmswStage_UL_nonempty_active_last w n).2
  have hULbound : ∀ e ∈ s.UL, e < s.nextEdge := by
    intro e he
    have hids := (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    apply hids
    simp [s, hURs, he]
  have hLowbound : ∀ e ∈ s.LL ++ s.LR, e < s.nextEdge := by
    intro e he
    have hids := (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    apply hids
    simp only [List.mem_append] at he ⊢
    rcases he with he | he
    · simp [s, he]
    · simp [s, hURs, he]
  have hact : s.active < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hULlast : s.UL.getLast hULne = s.active := by
    have h := hULlast?
    rw [List.getLast?_eq_getLast_of_ne_nil hULne] at h
    exact Option.some.inj h
  have hLRne : s.LR ≠ [] := by
    exact hLR
  have hLowne : s.LL ++ s.LR ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ hLRne
  have hLowlast : (s.LL ++ s.LR).getLast hLowne = s.LR.getLast hLRne := by
    rw [List.getLast_append_of_right_ne_nil _ _ hLRne]
  have hUold : List.IsChain (fun e f => s.east e = s.west f) s.UL := by
    simpa [s, WestEastChain, hUR] using hU
  have hLold : List.IsChain (fun e f => s.east e = s.west f) (s.LL ++ s.LR) := by
    simpa [s, WestEastChain] using hL
  have hWestOld : ∀ e < s.nextEdge, t.west e = s.west e := by
    intro e he
    have hne : e ≠ s.nextEdge := by omega
    simp [t, kmswStepOfStep, hURs, State.addEdge, hne]
  have hEastOld : ∀ e < s.nextEdge, t.east e = s.east e := by
    intro e he
    have hne : e ≠ s.nextEdge := by omega
    simp [t, kmswStepOfStep, hURs, State.addEdge, hne]
  have hWestNew : t.west s.nextEdge = s.east s.active := by
    simp [t, kmswStepOfStep, hURs, State.addEdge]
  have hULchain : List.IsChain (fun e f => t.east e = t.west f) s.UL := by
    apply chain_transfer_endpoints
    · intro e he
      exact hWestOld e (hULbound e he)
    · intro e he
      exact hEastOld e (hULbound e he)
    · exact hUold
  have hLowchain : List.IsChain (fun e f => t.east e = t.west f) (s.LL ++ s.LR) := by
    apply chain_transfer_endpoints
    · intro e he
      exact hWestOld e (hLowbound e he)
    · intro e he
      exact hEastOld e (hLowbound e he)
    · exact hLold
  have hUnew : List.IsChain (fun e f => t.east e = t.west f) (s.UL ++ [s.nextEdge]) := by
    apply hULchain.append (List.isChain_singleton _) 
    intro e he f hf
    obtain ⟨h, rfl⟩ := List.mem_getLast?_eq_getLast he
    simp only [List.head?_singleton, Option.mem_some_iff] at hf
    subst f
    have hlast : s.UL.getLast h = s.active := hULlast
    rw [hlast]
    exact (hEastOld s.active hact).trans hWestNew.symm
  have hLnew : List.IsChain (fun e f => t.east e = t.west f)
      ((s.LL ++ s.LR) ++ [s.nextEdge]) := by
    apply hLowchain.append (List.isChain_singleton _)
    intro e he f hf
    obtain ⟨h, rfl⟩ := List.mem_getLast?_eq_getLast he
    simp only [List.head?_singleton, Option.mem_some_iff] at hf
    subst f
    have hlast : (s.LL ++ s.LR).getLast h = s.LR.getLast hLRne := hLowlast
    rw [hlast]
    calc
      t.east (s.LR.getLast hLRne) = s.east (s.LR.getLast hLRne) :=
        hEastOld _ (hLowbound _ (List.mem_append_right _ (List.getLast_mem _)))
      _ = s.east s.active := (hempty hLRne hURs).symm
      _ = t.west s.nextEdge := hWestNew.symm
  have hStartUL : boundaryStart t (s.UL ++ [s.nextEdge]) = boundaryStart s s.UL := by
    unfold boundaryStart
    rw [List.head?_append_of_ne_nil _ hULne]
    cases hh : s.UL.head? with
    | none => exact rfl
    | some e =>
      have hm : e ∈ s.UL.head? := by simp [hh]
      have he : e ∈ s.UL := by
        rw [List.eq_cons_of_mem_head? hm]
        simp
      simp only [Option.map_some]
      exact congrArg some (hWestOld e (hULbound e he))
  have hStartLow : boundaryStart t ((s.LL ++ s.LR) ++ [s.nextEdge]) =
      boundaryStart s (s.LL ++ s.LR) := by
    unfold boundaryStart
    rw [List.head?_append_of_ne_nil _ hLowne]
    cases hh : (s.LL ++ s.LR).head? with
    | none => exact rfl
    | some e =>
      have hm : e ∈ (s.LL ++ s.LR).head? := by simp [hh]
      have he : e ∈ s.LL ++ s.LR := by
        rw [List.eq_cons_of_mem_head? hm]
        simp
      simp only [Option.map_some]
      exact congrArg some (hWestOld e (hLowbound e he))
  have hNext : t = kmswStage w (n + 1) := by
    simp [t, s, kmswStage, kmswStep, hw, kmswCodeStep, kmswStepOfStep,
      hUR, State.addEdge]
  have hEmptyHandOff : ∀ hLR' : t.LR ≠ [], t.UR = [] →
      t.east t.active = t.east (t.LR.getLast hLR') := by
    intro hLR' hUR'
    have hh := CutConverse.east_active_eq_LR_terminal_of_UR_nil w (n + 1) (by
      rw [← hNext]
      exact hUR')
    simpa [← hNext, act, List.getLast?_eq_getLast_of_ne_nil hLR'] using hh
  change kmswBoundaryChainInvariant t
  unfold kmswBoundaryChainInvariant
  have hFields : t.UL = s.UL ++ [s.nextEdge] ∧ t.UR = [] ∧
      t.LL = s.LL ∧ t.LR = s.LR ++ [s.nextEdge] ∧ t.active = s.nextEdge := by
    simp [t, kmswStepOfStep, hURs, State.addEdge]
  rcases hFields with ⟨hULfield, hURfield, hLLfield, hLRfield, hactivefield⟩
  simp only [hULfield, hURfield, hLLfield, hLRfield, hactivefield]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [WestEastChain] using hUnew
  · simpa [WestEastChain, List.append_assoc] using hLnew
  · have hstartCore : boundaryStart s s.UL = boundaryStart s (s.LL ++ s.LR) := by
      simpa [s, hUR] using hstart
    simpa [List.append_assoc] using hStartUL.trans (hstartCore.trans hStartLow.symm)
  · simp [boundaryEnd]
  · simp
  · intro e es he
    cases he
  · intro hLR' hUR'
    have hLRt : t.LR ≠ [] := by
      rw [hLRfield]
      exact List.append_ne_nil_of_right_ne_nil _ (by simp)
    have hURt : t.UR = [] := by simp [hURfield]
    have hh := hEmptyHandOff hLRt hURt
    simpa only [hLRfield, hactivefield] using hh

/-- Every finite KMSW stage satisfies the ordered boundary chain invariant -/
theorem kmswStage_boundary_chain_invariant (w : ℕ → Fin 3) (n : ℕ) :
    kmswBoundaryChainInvariant (kmswStage w n) := by
  induction n with
  | zero => exact kmswStage_boundary_chain_invariant_zero w
  | succ n ih =>
    by_cases hleft : w n = 0
    · cases hs : (kmswStage w n).UL.dropLast.reverse with
      | nil => exact kmswStage_left_fresh_boundary_invariant w n hleft hs ih
      | cons e es => exact kmswStage_left_predecessor_boundary_invariant w n hleft e es hs ih
    · by_cases hup : w n = 1
      · exact kmswStage_up_boundary_invariant w n hup ih
      · have hdown : w n = 2 := by
          apply Fin.ext
          have hv := (w n).isLt
          have h0 : (w n).val ≠ 0 := fun h => hleft (Fin.ext h)
          have h1 : (w n).val ≠ 1 := fun h => hup (Fin.ext h)
          omega
        cases hu : (kmswStage w n).UR with
        | nil =>
          have hnext : kmswStage w (n + 1) =
              kmswStepOfStep (kmswStage w n) .down := by
            simp [kmswStage, kmswStep, kmswCodeStep, hdown]
          rw [hnext]
          exact kmswStage_down_pendant_boundary_invariant w n hdown hu ih
        | cons e es =>
          have hnext : kmswStage w (n + 1) =
              kmswStepOfStep (kmswStage w n) .down := by
            simp [kmswStage, kmswStep, kmswCodeStep, hdown]
          rw [hnext]
          exact kmswStep_down_activate_boundary_invariant (kmswStage w n) e es hu ih

private theorem kmswStageRank_old_vertex (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    kmswStageRank w (n + 1) v = kmswStageRank w n v := by
  have hne : v ≠ (kmswStage w n).nextVertex := by omega
  simp [kmswStageRank, hne]

private theorem kmswStageRank_old_edge (w : ℕ → Fin 3) (n : ℕ)
    (ih : ∀ e < (kmswStage w n).nextEdge,
      kmswStageRank w n ((kmswStage w n).west e) <
        kmswStageRank w n ((kmswStage w n).east e)) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    kmswStageRank w (n + 1) ((kmswStage w (n + 1)).west e) <
      kmswStageRank w (n + 1) ((kmswStage w (n + 1)).east e) := by
  have hends := kmswStage_endpoints_stable w (Nat.le_succ n) he
  have hb := CutConverse.endpoint_bound w n e he
  have hvW : (kmswStage w (n + 1)).west e < (kmswStage w n).nextVertex := by
    rw [hends.1]
    exact hb.1
  have hvE : (kmswStage w (n + 1)).east e < (kmswStage w n).nextVertex := by
    rw [hends.2]
    exact hb.2
  calc
    kmswStageRank w (n + 1) ((kmswStage w (n + 1)).west e) =
        kmswStageRank w n ((kmswStage w (n + 1)).west e) :=
      kmswStageRank_old_vertex w n _ hvW
    _ = kmswStageRank w n ((kmswStage w n).west e) := by rw [hends.1]
    _ < kmswStageRank w n ((kmswStage w n).east e) := ih e he
    _ = kmswStageRank w n ((kmswStage w (n + 1)).east e) := by rw [hends.2]
    _ = kmswStageRank w (n + 1) ((kmswStage w (n + 1)).east e) :=
      (kmswStageRank_old_vertex w n _ hvE).symm

private theorem kmswStageRank_old_edge_at_step (w : ℕ → Fin 3) (n : ℕ)
    (ih : ∀ e < (kmswStage w n).nextEdge,
      kmswStageRank w n ((kmswStage w n).west e) <
        kmswStageRank w n ((kmswStage w n).east e))
    {t : State} (ht : t = kmswStage w (n + 1)) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    kmswStageRank w (n + 1) (t.west e) < kmswStageRank w (n + 1) (t.east e) := by
  have h := kmswStageRank_old_edge w n ih e he
  rw [← ht] at h
  exact h

/-- Every allocated edge strictly increases the rational stage rank -/
theorem kmswStageRank_strict (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e < (kmswStage w n).nextEdge,
      kmswStageRank w n ((kmswStage w n).west e) <
        kmswStageRank w n ((kmswStage w n).east e) := by
  induction n with
  | zero => exact kmswStageRank_strict_zero w
  | succ n ih =>
    let s := kmswStage w n
    have hActBound : s.active < s.nextEdge := by
      exact (kmswStage_boundary_ids_lt_nextEdge w n).1
    have hActRank := ih s.active hActBound
    have hActEndpoints := CutConverse.endpoint_bound w n s.active hActBound
    have hActWestRank : kmswStageRank w (n + 1) (s.west s.active) =
        kmswStageRank w n (s.west s.active) :=
      kmswStageRank_old_vertex w n _ hActEndpoints.1
    have hActEastRank : kmswStageRank w (n + 1) (s.east s.active) =
        kmswStageRank w n (s.east s.active) :=
      kmswStageRank_old_vertex w n _ hActEndpoints.2
    by_cases hleft : w n = 0
    · cases hstack : s.UL.dropLast.reverse with
      | nil =>
        let t := kmswStepOfStep s .left
        have hNext : t = kmswStage w (n + 1) := by
          simp [t, s, kmswStage, kmswStep, kmswCodeStep, hleft,
            kmswStepOfStep, hstack, State.addEdge]
        have hCount : t.nextEdge = s.nextEdge + 2 := by
          simp [t, kmswStepOfStep, hstack, State.addEdge]
        have hNewWest : t.west s.nextEdge = s.nextVertex := by
          simp [t, kmswStepOfStep, hstack, State.addEdge]
        have hNewEast : t.east s.nextEdge = s.east s.active := by
          simp [t, kmswStepOfStep, hstack, State.addEdge]
        have hMissingWest : t.west (s.nextEdge + 1) = s.nextVertex := by
          simp [t, kmswStepOfStep, hstack, State.addEdge]
        have hMissingEast : t.east (s.nextEdge + 1) = s.west s.active := by
          simp [t, kmswStepOfStep, hstack, State.addEdge]
        have hNewRank : kmswStageRank w (n + 1) s.nextVertex =
            kmswStageRank w n (s.west s.active) - 1 := by
          simp [kmswStageRank, s, hleft, hstack]
        have hOldRank : ∀ f < s.nextEdge,
            kmswStageRank w (n + 1) (t.west f) <
              kmswStageRank w (n + 1) (t.east f) := by
          intro f hf
          exact kmswStageRank_old_edge_at_step w n ih hNext f hf
        intro e he
        rw [← hNext] at he ⊢
        by_cases hold : e < s.nextEdge
        · exact hOldRank e hold
        · have heq : e = s.nextEdge ∨ e = s.nextEdge + 1 := by omega
          rcases heq with hEq | hEq
          · subst e
            rw [hNewWest, hNewEast, hNewRank, hActEastRank]
            linarith
          · subst e
            rw [hMissingWest, hMissingEast, hNewRank, hActWestRank]
            linarith
      | cons e es =>
        let t := kmswStepOfStep s .left
        have hNext : t = kmswStage w (n + 1) := by
          simp [t, s, kmswStage, kmswStep, kmswCodeStep, hleft,
            kmswStepOfStep, hstack]
        have hCount : t.nextEdge = s.nextEdge + 1 := by
          simp [t, kmswStepOfStep, hstack, State.addEdge]
        have hNewWest : t.west s.nextEdge = s.west e := by
          simp [t, kmswStepOfStep, hstack, State.addEdge]
        have hNewEast : t.east s.nextEdge = s.east s.active := by
          simp [t, kmswStepOfStep, hstack, State.addEdge]
        have hOldRank : ∀ f < s.nextEdge,
            kmswStageRank w (n + 1) (t.west f) <
              kmswStageRank w (n + 1) (t.east f) := by
          intro f hf
          exact kmswStageRank_old_edge_at_step w n ih hNext f hf
        intro f hf
        rw [← hNext] at hf ⊢
        by_cases hold : f < s.nextEdge
        · exact hOldRank f hold
        · have hEq : f = s.nextEdge := by omega
          subst f
          have heULdrop : e ∈ s.UL.dropLast := by
            apply List.mem_reverse.mp
            rw [hstack]
            simp
          have heUL : e ∈ s.UL := List.dropLast_subset _ heULdrop
          have heOld : e < s.nextEdge := by
            have hmem : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
              simp only [List.mem_append] at heUL ⊢
              tauto
            exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by simpa [s] using hmem)
          have hInc : s.east e = s.west s.active := by
            obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
            have hxsS : s.UL = xs ++ [s.active] := by simpa [s] using hxs
            have hxsDrop : xs = s.UL.dropLast := by rw [hxsS]; simp
            have hULrev : s.UL.reverse = s.active :: e :: es := by
              calc
                s.UL.reverse = (xs ++ [s.active]).reverse := congrArg List.reverse hxsS
                _ = s.active :: xs.reverse := by simp
                _ = s.active :: e :: es := by rw [hxsDrop, hstack]
            have hcoh := CutConverse.ul_coherent w n
            change s.UL.reverse.map s.east =
              s.east s.active :: (s.UL.reverse.map s.west).dropLast at hcoh
            rw [hULrev] at hcoh
            simp only [List.map_cons, List.dropLast_cons_cons] at hcoh
            exact (List.cons.inj (List.cons.inj hcoh).2).1
          have heEndpoints := CutConverse.endpoint_bound w n e heOld
          rw [hNewWest, hNewEast]
          calc
            kmswStageRank w (n + 1) (s.west e) =
                kmswStageRank w n (s.west e) :=
              kmswStageRank_old_vertex w n _ heEndpoints.1
            _ < kmswStageRank w n (s.east e) := ih e heOld
            _ = kmswStageRank w n (s.west s.active) := congrArg _ hInc
            _ < kmswStageRank w n (s.east s.active) := hActRank
            _ = kmswStageRank w (n + 1) (s.east s.active) := hActEastRank.symm
    · by_cases hup : w n = 1
      · let t := kmswStepOfStep s .up
        have hNext : t = kmswStage w (n + 1) := by
          simp [t, s, kmswStage, kmswStep, kmswCodeStep, hup,
            kmswStepOfStep, State.addEdge]
        have hCount : t.nextEdge = s.nextEdge + 2 := by
          simp [t, kmswStepOfStep, State.addEdge]
        have hNewWest : t.west s.nextEdge = s.west s.active := by
          simp [t, kmswStepOfStep, State.addEdge]
        have hNewEast : t.east s.nextEdge = s.nextVertex := by
          simp [t, kmswStepOfStep, State.addEdge]
        have hMissingWest : t.west (s.nextEdge + 1) = s.nextVertex := by
          simp [t, kmswStepOfStep, State.addEdge]
        have hMissingEast : t.east (s.nextEdge + 1) = s.east s.active := by
          simp [t, kmswStepOfStep, State.addEdge]
        have hNewRank : kmswStageRank w (n + 1) s.nextVertex =
            (kmswStageRank w n (s.west s.active) +
              kmswStageRank w n (s.east s.active)) / 2 := by
          simp [kmswStageRank, s, hup]
        have hOldRank : ∀ f < s.nextEdge,
            kmswStageRank w (n + 1) (t.west f) <
              kmswStageRank w (n + 1) (t.east f) := by
          intro f hf
          exact kmswStageRank_old_edge_at_step w n ih hNext f hf
        intro f hf
        rw [← hNext] at hf ⊢
        by_cases hold : f < s.nextEdge
        · exact hOldRank f hold
        · have heq : f = s.nextEdge ∨ f = s.nextEdge + 1 := by omega
          rcases heq with hEq | hEq
          · subst f
            rw [hNewWest, hNewEast, hActWestRank, hNewRank]
            linarith
          · subst f
            rw [hMissingWest, hMissingEast, hNewRank, hActEastRank]
            linarith
      · have hdown : w n = 2 := by
          apply Fin.ext
          have hv := (w n).isLt
          have h0 : (w n).val ≠ 0 := fun h => hleft (Fin.ext h)
          have h1 : (w n).val ≠ 1 := fun h => hup (Fin.ext h)
          omega
        cases hu : s.UR with
        | nil =>
          let t := kmswStepOfStep s .down
          have hNext : t = kmswStage w (n + 1) := by
            simp [t, s, kmswStage, kmswStep, kmswCodeStep, hdown,
              kmswStepOfStep, hu, State.addEdge]
          have hCount : t.nextEdge = s.nextEdge + 1 := by
            simp [t, kmswStepOfStep, hu, State.addEdge]
          have hNewWest : t.west s.nextEdge = s.east s.active := by
            simp [t, kmswStepOfStep, hu, State.addEdge]
          have hNewEast : t.east s.nextEdge = s.nextVertex := by
            simp [t, kmswStepOfStep, hu, State.addEdge]
          have hNewRank : kmswStageRank w (n + 1) s.nextVertex =
              kmswStageRank w n (s.east s.active) + 1 := by
            simp [kmswStageRank, s, hdown, hu]
          have hOldRank : ∀ f < s.nextEdge,
              kmswStageRank w (n + 1) (t.west f) <
                kmswStageRank w (n + 1) (t.east f) := by
            intro f hf
            exact kmswStageRank_old_edge_at_step w n ih hNext f hf
          intro f hf
          rw [← hNext] at hf ⊢
          by_cases hold : f < s.nextEdge
          · exact hOldRank f hold
          · have hfEq : f = s.nextEdge := by omega
            subst f
            rw [hNewWest, hNewEast, hActEastRank, hNewRank]
            linarith
        | cons e es =>
          let t := kmswStepOfStep s .down
          have hNext : t = kmswStage w (n + 1) := by
            simp [t, s, kmswStage, kmswStep, kmswCodeStep, hdown,
              kmswStepOfStep, hu]
          have hCount : t.nextEdge = s.nextEdge := by
            simp [t, kmswStepOfStep, hu]
          have hOldRank : ∀ f < s.nextEdge,
              kmswStageRank w (n + 1) (t.west f) <
                kmswStageRank w (n + 1) (t.east f) := by
            intro f hf
            exact kmswStageRank_old_edge_at_step w n ih hNext f hf
          intro f hf
          rw [← hNext] at hf ⊢
          exact hOldRank f (by simpa [hCount] using hf)

end DirectedDistances.KMSW
