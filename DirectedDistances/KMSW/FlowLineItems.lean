/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineEntryFrontier
public import DirectedDistances.KMSW.QuadKMSWHat
meta import Lean.Elab.Tactic.Omega

/-! # KMSW bookkeeping at flow-line exit and re-entry times

Formalization helpers for items (i) and (ii) of `lem-flow-line-times`, -/

public section
namespace DirectedDistances.KMSW
open Quiver

private theorem flowLine_walkNL_eq_firstFlowLHit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    walkNL w h k = firstFlowLHit w h (walkNR w h k) := by
  cases k <;> rfl

private theorem flowLine_stepL_lower (c : Fin 3) :
    -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).1 := by
  fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]

private theorem flowLine_before_firstLHit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t n : ℕ) (htn : t ≤ n)
    (hn : n < firstFlowLHit w h t) : L w t ≤ L w n := by
  classical
  change (∀ n, ∃ m, n + 1 ≤ m ∧ L w m = L w n - 1) ∧ _ at h
  have hmin : ∀ j, t + 1 ≤ j → j < firstFlowLHit w h t →
      L w j ≠ L w t - 1 := by
    intro j hj hjhit heq
    change j < Nat.find (h.1 t) at hjhit
    exact (Nat.find_min (h.1 t) hjhit) ⟨hj, heq⟩
  have hbefore : ∀ j, t ≤ j → j < firstFlowLHit w h t → L w t ≤ L w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hj ih =>
        intro hjhit
        have hs : L w (j + 1) = L w j +
            (RandomWalk.lazyTwoDimensionalStep (w j)).1 := Finset.sum_range_succ _ _
        have hstep : L w j - 1 ≤ L w (j + 1) := by
          rw [hs]
          have hlow := flowLine_stepL_lower (w j)
          omega
        have hprev := ih (by omega)
        by_contra hlt
        have hneq := hmin (j + 1) (by omega) hjhit
        omega
  exact hbefore n htn hn

private theorem filter_range_has_two_final_records (p : ℕ → Bool) (a n : ℕ)
    (ha : 0 < a) (han : a ≤ n) (hentry : p (a - 1) = true)
    (hend : p n = true)
    (hno : ∀ m, a ≤ m → m < n → p m = false) :
    ∃ xs, (List.range (n + 1)).filter p = xs ++ [a - 1, n] := by
  let xs := (List.range (a - 1)).filter p
  have hpre : List.range a = List.range (a - 1) ++ [a - 1] := by
    have ha' : a - 1 + 1 = a := by omega
    calc
      List.range a = List.range (a - 1 + 1) := by rw [ha']
      _ = List.range (a - 1) ++ [a - 1] := List.range_succ
  have hmid : (List.range' a (n - a)).filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro m hm
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hm
    have hfalse := hno (a + i) (by omega) (by omega)
    simpa using hfalse
  have htail : List.range' a (n + 1 - a) = List.range' a (n - a) ++ [n] := by
    have h := List.range'_append_1 (s := a) (m := n - a) (n := 1)
    have hsum : a + (n - a) = n := Nat.add_sub_of_le han
    have hlen : n - a + 1 = n + 1 - a := by omega
    simpa [hsum, hlen] using h.symm
  have hrange : List.range (n + 1) = List.range a ++ List.range' a (n + 1 - a) := by
    rw [List.range_eq_range', List.range_eq_range']
    have hsum : a + (n + 1 - a) = n + 1 := by omega
    rw [← hsum, ← List.range'_append_1 (s := 0) (m := a) (n := n + 1 - a)]
    simp
  refine ⟨xs, ?_⟩
  rw [hrange, hpre, htail]
  simp only [List.filter_append, hmid]
  simp [xs, hentry, hend]

private theorem flowLine_exit_predecessor (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 0 < k) :
    ∃ es, (kmswStage w (walkNL w h k - 1)).UL.dropLast.reverse =
      act w (walkNR w h k - 1) :: es := by
  classical
  let a := walkNR w h k
  let n := walkNL w h k - 1
  have ha : 0 < a := by
    have hspec := walkNR_succ_spec w h (k - 1)
    have hk' : (k - 1) + 1 = k := by omega
    rw [hk'] at hspec
    dsimp [a]
    omega
  have han : a ≤ n := by
    have hspec := walkNL_spec w h k
    dsimp [a, n]
    omega
  have hEntryLevel : L w (a - 1) + 1 = L w a := by
    cases k with
    | zero => omega
    | succ j =>
        have hs := congrArg Prod.fst (walkNR_succ_previous_step w h j)
        simpa [a] using (show L w (walkNR w h (j + 1) - 1) + 1 =
          L w (walkNR w h (j + 1)) by omega)
  have hExitLevel : L w n = L w a := by
    have hstep := congrArg Prod.fst (walkNL_previous_step w h k)
    have hspec := (walkNL_spec w h k).2
    dsimp [n, a] at hstep ⊢
    omega
  have hAbove : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j := by
    intro j haj hjn
    have hjlt : j < walkNL w h k := by
      dsimp [n] at hjn
      omega
    have hjhit : j < firstFlowLHit w h a := by
      rw [← flowLine_walkNL_eq_firstFlowLHit w h k]
      simpa [a] using hjlt
    exact flowLine_before_firstLHit w h a j haj hjhit
  let p : ℕ → Bool := fun m =>
    decide (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j)
  have hpEntry : p (a - 1) = true := by
    change decide (∀ j, a - 1 < j → j ≤ n → L w (a - 1) + 1 ≤ L w j) = true
    apply decide_eq_true
    intro j hj hjn
    have hLj := hAbove j (by omega) (by omega)
    rw [hEntryLevel]
    exact hLj
  have hpEnd : p n = true := by
    change decide (∀ j, n < j → j ≤ n → L w n + 1 ≤ L w j) = true
    apply decide_eq_true
    intro j hj hjn
    omega
  have hpNo : ∀ m, a ≤ m → m < n → p m = false := by
    intro m ham hmn
    have hnot : ¬ (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j) := by
      intro hm
      have hLm := hAbove m ham (by omega)
      have hn := hm n (by omega) le_rfl
      rw [hExitLevel] at hn
      omega
    change decide (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j) = false
    exact decide_eq_false_iff_not.mpr hnot
  obtain ⟨xs, hrecords⟩ :=
    filter_range_has_two_final_records p a n ha han hpEntry hpEnd hpNo
  have hUL : (kmswStage w n).UL =
      List.map (act w) xs ++ [act w (a - 1), act w n] := by
    rw [kmswStage_UL_eq]
    change List.map (act w) (List.filter p (List.range (n + 1))) = _
    rw [hrecords, List.map_append]
    simp
  refine ⟨(List.map (act w) xs).reverse, ?_⟩
  rw [hUL]
  simp [a]

private theorem flowLine_predecessor_east (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ) (hp : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).east e = (kmswStage w n).west (act w n) := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hr : xs.reverse = e :: es := by simpa [hxs] using hp
  have hxs' : xs = es.reverse ++ [e] := by
    have h := congrArg List.reverse hr
    simpa using h
  have hc := (kmswStage_boundary_chain_invariant w n).1.left_of_append
  have hc' : List.IsChain
      (fun a b => (kmswStage w n).east a = (kmswStage w n).west b)
      (es.reverse ++ [e, act w n]) := by
    simpa [hxs, hxs', List.append_assoc, act] using hc
  exact (List.isChain_append_cons_cons.mp hc').2.1

private theorem flowLine_entry_reachable_all (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (walkNR w h k)).west (act w (walkNR w h k))⟩ := by
  induction k with
  | zero => exact flowLine_entry_zero w h
  | succ k ih => exact flowLine_entry_succ w h k ih

/-- Walk-indexed form of the later left-exit triangle; its index `k` is the
source index `N_{k+1}^L` (`eq:ref-for-lat-disc`). -/
private theorem flowLine_later_leftExit_triangle_walk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 0 < k) :
    let r := walkNR w h k
    let t := walkNL w h k
    let s := kmswStage w (t - 1)
    ∃ es, s.UL.dropLast.reverse = act w (r - 1) :: es ∧
      s.east (act w (r - 1)) = s.west (act w (t - 1)) ∧
      (kmswStage w t).triangles =
        s.triangles ++ [(act w (t - 1), act w t, act w (r - 1))] ∧
      act w t = s.nextEdge ∧
      (kmswStage w t).present (act w t) = true ∧
      (kmswStage w t).west (act w t) = s.west (act w (r - 1)) ∧
      (kmswStage w t).east (act w t) = s.east (act w (t - 1)) := by
  let r := walkNR w h k
  let t := walkNL w h k
  let u := t - 1
  let s := kmswStage w u
  change ∃ es, s.UL.dropLast.reverse = act w (r - 1) :: es ∧
    s.east (act w (r - 1)) = s.west (act w (t - 1)) ∧
    (kmswStage w t).triangles =
      s.triangles ++ [(act w (t - 1), act w t, act w (r - 1))] ∧
    act w t = s.nextEdge ∧
    (kmswStage w t).present (act w t) = true ∧
    (kmswStage w t).west (act w t) = s.west (act w (r - 1)) ∧
    (kmswStage w t).east (act w t) = s.east (act w (t - 1))
  obtain ⟨es, hpred⟩ := flowLine_exit_predecessor w h k hk
  have hcode : w u = 0 := by
    dsimp [u, t]
    exact walkNL_previous_code w h k
  have htnpos : 1 ≤ t := by
    have hspec : walkNR w h k + 1 ≤ t := by
      simpa [t] using (walkNL_spec w h k).1
    omega
  have husucc : u + 1 = t := by
    dsimp [u]
    omega
  have hstep : kmswStage w t = kmswStepOfStep s .left := by
    rw [← husucc]
    change kmswStep s (w u) = kmswStepOfStep s .left
    rw [hcode]
    rfl
  have hpred' : s.UL.dropLast.reverse = act w (r - 1) :: es := by
    simpa [s, u, r, t] using hpred
  have hjoin : s.east (act w (r - 1)) = s.west (act w u) := by
    exact flowLine_predecessor_east w u (act w (r - 1)) es hpred'
  have hactU : s.active = act w u := by rfl
  have htri : (kmswStage w t).triangles =
      s.triangles ++ [(act w u, s.nextEdge, act w (r - 1))] := by
    rw [hstep]
    simp [kmswStepOfStep, hpred', hactU]
  have hactive : act w t = s.nextEdge := by
    change (kmswStage w t).active = s.nextEdge
    rw [hstep]
    simp [kmswStepOfStep, hpred']
  have hpresent : (kmswStage w t).present (act w t) = true := by
    rw [hstep, hactive]
    simp [kmswStepOfStep, hpred', State.addEdge]
  have hwest : (kmswStage w t).west (act w t) = s.west (act w (r - 1)) := by
    rw [hstep, hactive]
    simp [kmswStepOfStep, hpred', State.addEdge]
  have heast : (kmswStage w t).east (act w t) = s.east (act w u) := by
    rw [hstep, hactive]
    simp [kmswStepOfStep, hpred', State.addEdge, hactU]
  refine ⟨es, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpred'
  · simpa [u] using hjoin
  · simpa [hactive, u] using htri
  · exact hactive
  · exact hpresent
  · exact hwest
  · simpa [u] using heast

/-- At each source time `N_k^L` with `k ≥ 2`, the triangle's third side is
the active edge at `walkNR (k - 1) - 1`; the other sides are the previously
active and new active edges. The old active edge has both endpoints
root-reachable, the boundary evidence expressible in this stage bookkeeping
for the source's `β₀` edge
(`lem-flow-line-times` (ii), `eq:ref-for-lat-disc`, -/
theorem flowLine_leftExit_triangle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 2 ≤ k) :
    let r := walkNR w h (k - 1)
    let t := walkNL w h (k - 1)
    let s := kmswStage w (t - 1)
    Reachable (⟨0⟩ : PresentVertex w) ⟨s.west (act w (t - 1))⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨s.east (act w (t - 1))⟩ ∧
      (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
      (∃ es, s.UL.dropLast.reverse = act w (r - 1) :: es ∧
      s.east (act w (r - 1)) = s.west (act w (t - 1)) ∧
      (kmswStage w t).triangles =
        s.triangles ++ [(act w (t - 1), act w t, act w (r - 1))] ∧
      act w t = s.nextEdge ∧
      (kmswStage w t).present (act w t) = true ∧
      (kmswStage w t).west (act w t) = s.west (act w (r - 1)) ∧
      (kmswStage w t).east (act w t) = s.east (act w (t - 1))) := by
  have hwalk : 0 < k - 1 := by omega
  let m := k - 1
  let r := walkNR w h m
  let t := walkNL w h m
  let u := t - 1
  let s := kmswStage w u
  have hentry := flowLine_entry_reachable_all w h m
  have hNLbounds : walkNR w h m + 1 ≤ t := by
    simpa [t] using (walkNL_spec w h m).1
  have hphaseIndex : walkNR w h m ≤ u := by dsimp [u]; omega
  have hphaseExit : u < t := by dsimp [u]; omega
  have hphaseWest := flowLine_phase_reachable_of_entry w h m u hentry
    hphaseIndex hphaseExit
  have hphaseEast := kmswStage_activeEast_reachable w u hphaseWest
  have hcoord :
      (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) := by
    simpa [t, m] using walkNL_previous_step w h m
  have htriangle := flowLine_later_leftExit_triangle_walk w h m hwalk
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [s, u, t, m, act] using hphaseWest
  · simpa [s, u, t, m, act] using hphaseEast
  · exact hcoord
  · simpa [r, t, s, u, m] using htriangle

/-- The first left exit is the exceptional base case of item (ii): the
upper-left predecessor list is empty, so the third side is a newly allocated -/
theorem flowLine_firstLeftExit_triangle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    let t := walkNL w h 0
    let s := kmswStage w (t - 1)
    (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨s.west s.active⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨s.east s.active⟩ ∧
      s.UL.dropLast.reverse = [] ∧
      (kmswStage w t).triangles =
        s.triangles ++ [(act w (t - 1), act w t, s.nextEdge + 1)] ∧
      act w t = s.nextEdge ∧
      (kmswStage w t).present (s.nextEdge + 1) = false := by
  let t := walkNL w h 0
  let s := kmswStage w (t - 1)
  obtain ⟨_, _, _, hUL⟩ := quadrantFirstR_exit_predecessor_emptyUL w h
  obtain ⟨htri, hactive, _, _, _, _, _, _, hmissing⟩ :=
    quadrantFirstR_exit_gluingTriangle w h
  obtain ⟨hwest, heast, _, _, _, _⟩ := quadrantFirstR_exit_triangle_reachability w h
  have hactive' : (kmswStage w t).active = s.nextEdge := by
    simpa [s, t, act] using hactive
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [t] using walkNL_previous_step w h 0
  · simpa [s, t, act] using hwest
  · simpa [s, t, act] using heast
  · simpa [s, t] using hUL
  · simpa [s, t, act, hactive'] using htri
  · constructor
    · simpa [s, t] using hactive
    · simpa [s, t] using hmissing

private theorem flowLine_rightEntry_singleEdge_walk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    let r := walkNR w h (k + 1)
    let s := kmswStage w (r - 1)
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w r).west (act w r)⟩ ∧
      w (r - 1) = 2 ∧
      (kmswStage w r).triangles = s.triangles ∧
      ((s.UR = [] ∧
          (kmswStage w r).nextEdge = s.nextEdge + 1 ∧
          (kmswStage w r).nextVertex = s.nextVertex + 1 ∧
          act w r = s.nextEdge ∧
          (kmswStage w r).west (act w r) = s.east s.active ∧
          (kmswStage w r).east (act w r) = s.nextVertex ∧
          (kmswStage w r).present (act w r) = true) ∨
        ∃ e es, s.UR = e :: es ∧ s.present e = false ∧
          (kmswStage w r).nextEdge = s.nextEdge ∧
          act w r = e ∧
          (kmswStage w r).west e = s.east s.active ∧
          (kmswStage w r).east e = s.east e ∧
          (kmswStage w r).present e = true) := by
  let r := walkNR w h (k + 1)
  let q := r - 1
  let s := kmswStage w q
  have hrpos : 0 < r := by
    have hspec := walkNR_succ_spec w h k
    dsimp [r]
    omega
  have hqsucc : q + 1 = r := by dsimp [q]; omega
  have hcode : w q = 2 := by
    simpa [q, r] using walkNR_succ_previous_code w h k
  have hstep : kmswStage w r = kmswStepOfStep s .down := by
    rw [← hqsucc]
    change kmswStep s (w q) = kmswStepOfStep s .down
    rw [hcode]
    rfl
  have hreach := flowLine_entry_reachable_all w h (k + 1)
  change Reachable (⟨0⟩ : PresentVertex w)
    ⟨(kmswStage w r).west (act w r)⟩ at hreach
  have htri : (kmswStage w r).triangles = s.triangles := by
    rw [hstep]
    cases hUR : s.UR with
    | nil => simp [kmswStepOfStep, hUR, State.addEdge]
    | cons e es => simp [kmswStepOfStep, hUR]
  cases hUR : s.UR with
  | nil =>
      have hnextEdge : (kmswStage w r).nextEdge = s.nextEdge + 1 := by
        rw [hstep]
        simp [kmswStepOfStep, hUR, State.addEdge]
      have hnextVertex : (kmswStage w r).nextVertex = s.nextVertex + 1 := by
        rw [hstep]
        simp [kmswStepOfStep, hUR, State.addEdge]
      have hactive : act w r = s.nextEdge := by
        change (kmswStage w r).active = s.nextEdge
        rw [hstep]
        simp [kmswStepOfStep, hUR]
      have hwest : (kmswStage w r).west (act w r) = s.east s.active := by
        rw [hstep, hactive]
        simp [kmswStepOfStep, hUR, State.addEdge]
      have heast : (kmswStage w r).east (act w r) = s.nextVertex := by
        rw [hstep, hactive]
        simp [kmswStepOfStep, hUR, State.addEdge]
      have hpresent : (kmswStage w r).present (act w r) = true := by
        rw [hstep, hactive]
        simp [kmswStepOfStep, hUR, State.addEdge]
      refine ⟨hreach, hcode, htri, Or.inl ⟨hUR, hnextEdge, hnextVertex,
        hactive, hwest, heast, hpresent⟩⟩
  | cons e es =>
      have heBound : e < s.nextEdge := by
        apply (kmswStage_boundary_ids_lt_nextEdge w q).2
        change e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr (by rw [hUR]; simp)))
      have heUR : e ∈ s.UR := by rw [hUR]; simp
      have hmissing : s.present e = false := by
        apply ((kmswStage_status w q).1 e heBound).2
        exact Or.inl heUR
      have hnextEdge : (kmswStage w r).nextEdge = s.nextEdge := by
        rw [hstep]
        simp [kmswStepOfStep, hUR]
      have hactive : act w r = e := by
        change (kmswStage w r).active = e
        rw [hstep]
        simp [kmswStepOfStep, hUR]
      have hhead : s.west e = s.east s.active := by
        obtain ⟨_, _, _, _, _, hhead, _⟩ := kmswStage_boundary_chain_invariant w q
        exact hhead e es hUR
      have hwest : (kmswStage w r).west e = s.east s.active := by
        rw [hstep]
        simp [kmswStepOfStep, hUR, hhead]
      have heast : (kmswStage w r).east e = s.east e := by
        rw [hstep]
        simp [kmswStepOfStep, hUR]
      have hpresent : (kmswStage w r).present e = true := by
        rw [hstep]
        simp [kmswStepOfStep, hUR, hmissing]
      refine ⟨hreach, hcode, htri, Or.inr ⟨e, es, hUR, hmissing,
        hnextEdge, hactive, hwest, heast, hpresent⟩⟩

/-- At each source time `N_k^R` with `k ≥ 2`, the code step is `(1,-1)` and
the active edge is a single present edge, with no triangle added. The edge is
entry's west endpoint is root-reachable by the tracked east frontier
(`lem-flow-line-times` (i), `eq:ref-for-lat-disc2`, -/
theorem flowLine_rightEntry_singleEdge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 2 ≤ k) :
    let r := walkNR w h (k - 1)
    let s := kmswStage w (r - 1)
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w r).west (act w r)⟩ ∧
      (L w r - L w (r - 1), R w r - R w (r - 1)) = (1, -1) ∧
      (kmswStage w r).triangles = s.triangles ∧
      ((s.UR = [] ∧
          (kmswStage w r).nextEdge = s.nextEdge + 1 ∧
          (kmswStage w r).nextVertex = s.nextVertex + 1 ∧
          act w r = s.nextEdge ∧
          (kmswStage w r).west (act w r) = s.east s.active ∧
          (kmswStage w r).east (act w r) = s.nextVertex ∧
          (kmswStage w r).present (act w r) = true) ∨
        ∃ e es, s.UR = e :: es ∧ s.present e = false ∧
          (kmswStage w r).nextEdge = s.nextEdge ∧
          act w r = e ∧
          (kmswStage w r).west e = s.east s.active ∧
          (kmswStage w r).east e = s.east e ∧
          (kmswStage w r).present e = true) := by
  have hindex : (k - 2) + 1 = k - 1 := by omega
  have hmain := flowLine_rightEntry_singleEdge_walk w h (k - 2)
  have hmain' :
      let r := walkNR w h (k - 1)
      let s := kmswStage w (r - 1)
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w r).west (act w r)⟩ ∧
        w (r - 1) = 2 ∧
        (kmswStage w r).triangles = s.triangles ∧
        ((s.UR = [] ∧
            (kmswStage w r).nextEdge = s.nextEdge + 1 ∧
            (kmswStage w r).nextVertex = s.nextVertex + 1 ∧
            act w r = s.nextEdge ∧
            (kmswStage w r).west (act w r) = s.east s.active ∧
            (kmswStage w r).east (act w r) = s.nextVertex ∧
            (kmswStage w r).present (act w r) = true) ∨
          ∃ e es, s.UR = e :: es ∧ s.present e = false ∧
            (kmswStage w r).nextEdge = s.nextEdge ∧
            act w r = e ∧
            (kmswStage w r).west e = s.east s.active ∧
            (kmswStage w r).east e = s.east e ∧
            (kmswStage w r).present e = true) := by
    simpa only [hindex] using hmain
  have hcoord := walkNR_succ_previous_step w h (k - 2)
  have hcoord' :
      (L w (walkNR w h (k - 1)) - L w (walkNR w h (k - 1) - 1),
        R w (walkNR w h (k - 1)) - R w (walkNR w h (k - 1) - 1)) = (1, -1) := by
    simpa only [hindex] using hcoord
  rcases hmain' with ⟨hreach, hcode, htri, hcase⟩
  exact ⟨hreach, by simpa using hcoord', htri, hcase⟩

end DirectedDistances.KMSW
