/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineTimesIff
public import DirectedDistances.KMSW.FlowLineItems

/-! Supporting lemmas for paper labels `lem-flow-line-times` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open Quiver

/-- The source's membership predicate for `\widehat M` at time `n`:
`lambda_n` has its initial vertex reachable from the root in the global
limit quiver `M_{0,\infty}` (`lem-flow-line-times`, -/
@[expose] def sourceFlowMhat (w : ℕ → Fin 3) (n : ℕ) : Prop :=
  Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).west (act w n)⟩

/-- Active-edge membership in `\widehat M` is equivalent to reachability of
both endpoints in the global limit quiver. The active edge is a present arrow
from its west endpoint to its east endpoint -/
theorem sourceFlowMhat_endpoints_iff (w : ℕ → Fin 3) (n : ℕ) :
    sourceFlowMhat w n ↔
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).west (act w n)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).east (act w n)⟩ := by
  constructor
  · intro hw
    exact ⟨hw, kmswStage_activeEast_reachable w n hw⟩
  · exact fun h => h.1








@[expose] def sourceFlowMhatInterfaceEdge (w : ℕ → Fin 3) (t e : ℕ) : Prop :=
  (Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (t - 1)).west e⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (t - 1)).east e⟩) ∧
  ∃ a b c,
    (kmswStage w t).triangles =
      (kmswStage w (t - 1)).triangles ++ [(a, b, c)] ∧
    e ∈ [a, b, c] ∧
    ¬ ∀ f ∈ [a, b, c],
      Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w t).west f⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w t).east f⟩

private theorem sourceFlowMhatInterfaceEdge_of_newTriangle
    (w : ℕ → Fin 3) (t e a b c : ℕ)
    (hwest : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (t - 1)).west e⟩)
    (heast : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (t - 1)).east e⟩)
    (htri : (kmswStage w t).triangles =
      (kmswStage w (t - 1)).triangles ++ [(a, b, c)])
    (he : e ∈ [a, b, c])
    (hnot : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w t).west b⟩) :
    sourceFlowMhatInterfaceEdge w t e := by
  refine ⟨⟨hwest, heast⟩, a, b, c, htri, he, ?_⟩
  intro hall
  exact hnot (hall b (by simp)).1





@[expose] def sourceFlowLeftCandidate (w : ℕ → Fin 3) (r n : ℕ) : Prop :=
  r + 1 ≤ n ∧ ¬ sourceFlowMhat w n





@[expose] def sourceFlowRightCandidate (w : ℕ → Fin 3) (t n : ℕ) : Prop :=
  t + 1 ≤ n ∧ sourceFlowMhat w n

noncomputable instance sourceFlowLeftCandidate_decidable (w : ℕ → Fin 3)
    (r : ℕ) : DecidablePred (sourceFlowLeftCandidate w r) := Classical.decPred _

noncomputable instance sourceFlowRightCandidate_decidable (w : ℕ → Fin 3)
    (t : ℕ) : DecidablePred (sourceFlowRightCandidate w t) := Classical.decPred _

private theorem sourceFlowMhat_of_rightPhase (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hn₁ : walkNR w h k ≤ n) (hn₂ : n < walkNL w h k) :
    sourceFlowMhat w n := by
  exact (flowLineTimes_iff w h n).2 ⟨k, hn₁, hn₂⟩

private theorem sourceFlow_notMhat_of_leftPhase (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hn₁ : walkNL w h k ≤ n) (hn₂ : n < walkNR w h (k + 1)) :
    ¬ sourceFlowMhat w n := by
  intro hr
  exact lPhase_activeWest_unreachable w h k n hn₁ hn₂ hr

/-- A later time outside `\widehat M` exists after any source time; the
phase partition supplies it (`lem-flow-line-times`, -/
theorem sourceFlowLeft_exists (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (r : ℕ) :
    ∃ n, sourceFlowLeftCandidate w r n := by
  obtain ⟨k, hk | hk⟩ := flowLine_phase_partition w h (r + 1)
  · refine ⟨walkNL w h k, ?_, ?_⟩
    · omega
    · have hlt : walkNL w h k < walkNR w h (k + 1) := by
        have hs := walkNR_succ_spec w h k
        omega
      exact sourceFlow_notMhat_of_leftPhase w h k _ le_rfl hlt
  · refine ⟨r + 1, le_rfl, ?_⟩
    exact sourceFlow_notMhat_of_leftPhase w h k _ hk.1 hk.2

/-- A later time in `\widehat M` exists after any source time, by the phase -/
theorem sourceFlowRight_exists (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t : ℕ) :
    ∃ n, sourceFlowRightCandidate w t n := by
  obtain ⟨k, hk | hk⟩ := flowLine_phase_partition w h (t + 1)
  · refine ⟨t + 1, le_rfl, ?_⟩
    exact sourceFlowMhat_of_rightPhase w h k _ hk.1 hk.2
  · refine ⟨walkNR w h (k + 1), ?_, ?_⟩
    · omega
    · have hlt : walkNR w h (k + 1) < walkNL w h (k + 1) := by
        have hs := walkNL_spec w h (k + 1)
        omega
      exact sourceFlowMhat_of_rightPhase w h (k + 1) _ le_rfl hlt

/-- The recursive pair is indexed like the existing walks: index zero is
`N₁ᴿ = 0`, and index `k` is source index `Nₖ₊₁`. Each component is literally
the least time satisfying the source predicate. -/
@[expose] noncomputable def sourceFlowTimes (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ × ℕ
  | 0 => by
      classical
      exact (0, Nat.find (sourceFlowLeft_exists w h 0))
  | k + 1 => by
      classical
      let r := Nat.find (sourceFlowRight_exists w h (sourceFlowTimes w h k).2)
      exact (r, Nat.find (sourceFlowLeft_exists w h r))

/-- Source-indexed right entrance, with `sourceFlowNR 0 = N₁ᴿ = 0` and
`sourceFlowNR k = Nₖ₊₁ᴿ` for positive `k` (`lem-flow-line-times`, -/
@[expose] noncomputable def sourceFlowNR (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : ℕ := (sourceFlowTimes w h k).1

/-- Source-indexed left exit, with `sourceFlowNL k = Nₖ₊₁ᴸ` -/
@[expose] noncomputable def sourceFlowNL (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : ℕ := (sourceFlowTimes w h k).2

private theorem sourceFlowLeft_find_walk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    Nat.find (sourceFlowLeft_exists w h (walkNR w h k)) = walkNL w h k := by
  classical
  apply (Nat.find_eq_iff (sourceFlowLeft_exists w h (walkNR w h k))).2
  constructor
  · constructor
    · exact (walkNL_spec w h k).1
    · apply sourceFlow_notMhat_of_leftPhase w h k (walkNL w h k) le_rfl
      have hs := walkNR_succ_spec w h k
      omega
  · intro n hn hc
    rcases hc with ⟨hbound, hnot⟩
    exact hnot (sourceFlowMhat_of_rightPhase w h k n (by omega) hn)

private theorem sourceFlowRight_find_walk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    Nat.find (sourceFlowRight_exists w h (walkNL w h k)) =
      walkNR w h (k + 1) := by
  classical
  apply (Nat.find_eq_iff (sourceFlowRight_exists w h (walkNL w h k))).2
  constructor
  · constructor
    · exact (walkNR_succ_spec w h k).1
    · apply sourceFlowMhat_of_rightPhase w h (k + 1)
        (walkNR w h (k + 1)) le_rfl
      have hs := walkNL_spec w h (k + 1)
      omega
  · intro n hn hc
    rcases hc with ⟨hbound, hm⟩
    exact (sourceFlow_notMhat_of_leftPhase w h k n (by omega) hn) hm

/-- The recursive source minima agree with the existing walk indexing:
`sourceFlowNR k = Nₖ₊₁ᴿ` and `sourceFlowNL k = Nₖ₊₁ᴸ` -/
theorem sourceFlowTimes_eq_walk (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    sourceFlowTimes w h k = (walkNR w h k, walkNL w h k) := by
  induction k with
  | zero =>
      change (0, Nat.find (sourceFlowLeft_exists w h 0)) = _
      rw [walkNR_zero w h]
      have heq := sourceFlowLeft_find_walk w h 0
      simpa only [walkNR_zero] using congrArg (fun n => (0, n)) heq
  | succ k ih =>
      cases hp : sourceFlowTimes w h k with
      | mk r t =>
          have hp' : (r, t) = (walkNR w h k, walkNL w h k) := hp.symm.trans ih
          have hr : r = walkNR w h k := congrArg Prod.fst hp'
          have ht : t = walkNL w h k := congrArg Prod.snd hp'
          subst r t
          simp [sourceFlowTimes, hp, sourceFlowRight_find_walk,
            sourceFlowLeft_find_walk]

theorem sourceFlowNR_eq_walkNR (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    sourceFlowNR w h k = walkNR w h k := by
  exact congrArg Prod.fst (sourceFlowTimes_eq_walk w h k)

theorem sourceFlowNL_eq_walkNL (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    sourceFlowNL w h k = walkNL w h k := by
  exact congrArg Prod.snd (sourceFlowTimes_eq_walk w h k)

/-- The initial recursive right time is the source value `N₁ᴿ = 0` -/
theorem sourceFlowNR_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    sourceFlowNR w h 0 = 0 := by
  rw [sourceFlowNR_eq_walkNR, walkNR_zero]

/-- The source left-exit time is the literal first hit of the horizontal
level specified in `eqn-flow-line-times` -/
theorem sourceFlowNL_level_min (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    sourceFlowNL w h k = Nat.find (h.1 (sourceFlowNR w h k)) := by
  rw [sourceFlowNL_eq_walkNL, sourceFlowNR_eq_walkNR]
  cases k <;> rfl

/-- The next source right-entry time is the literal first hit of the vertical
level specified in `eqn-flow-line-times` -/
theorem sourceFlowNR_succ_level_min (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    sourceFlowNR w h (k + 1) = Nat.find (h.2 (sourceFlowNL w h k)) := by
  rw [sourceFlowNR_eq_walkNR, sourceFlowNL_eq_walkNL]
  rfl

/-- The source left exit is the least time in the literal `\widehat M'` -/
theorem sourceFlowNL_candidate_isLeast (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    IsLeast {n | sourceFlowLeftCandidate w (sourceFlowNR w h k) n}
      (sourceFlowNL w h k) := by
  classical
  rw [sourceFlowNR_eq_walkNR, sourceFlowNL_eq_walkNL,
    ← sourceFlowLeft_find_walk]
  constructor
  · exact Nat.find_spec (sourceFlowLeft_exists w h (walkNR w h k))
  · intro n hn
    exact Nat.find_min' (sourceFlowLeft_exists w h (walkNR w h k)) hn

/-- The next source right entrance is the least time in the literal
`\widehat M` candidate set (`lem-flow-line-times`, -/
theorem sourceFlowNR_succ_candidate_isLeast (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    IsLeast {n | sourceFlowRightCandidate w (sourceFlowNL w h k) n}
      (sourceFlowNR w h (k + 1)) := by
  classical
  rw [sourceFlowNL_eq_walkNL, sourceFlowNR_eq_walkNR,
    ← sourceFlowRight_find_walk]
  constructor
  · exact Nat.find_spec (sourceFlowRight_exists w h (walkNL w h k))
  · intro n hn
    exact Nat.find_min' (sourceFlowRight_exists w h (walkNL w h k)) hn

/-- The source left exit is the least future hit of the prescribed `L` level -/
theorem sourceFlowNL_level_isLeast (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    IsLeast
      {n | sourceFlowNR w h k + 1 ≤ n ∧
        L w n = L w (sourceFlowNR w h k) - 1}
      (sourceFlowNL w h k) := by
  classical
  rw [sourceFlowNL_level_min]
  constructor
  · exact Nat.find_spec (h.1 (sourceFlowNR w h k))
  · intro n hn
    exact Nat.find_min' (h.1 (sourceFlowNR w h k)) hn

/-- The next source right entrance is the least future hit of the prescribed -/
theorem sourceFlowNR_succ_level_isLeast (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    IsLeast
      {n | sourceFlowNL w h k + 1 ≤ n ∧
        R w n = R w (sourceFlowNL w h k) - 1}
      (sourceFlowNR w h (k + 1)) := by
  classical
  rw [sourceFlowNR_succ_level_min]
  constructor
  · exact Nat.find_spec (h.2 (sourceFlowNL w h k))
  · intro n hn
    exact Nat.find_min' (h.2 (sourceFlowNL w h k)) hn

/-- Source-indexed item (i), retaining both alternatives for the active
present edge and all endpoint and boundary data (`lem-flow-line-times`, -/
theorem sourceFlow_rightEntry_singleEdge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 2 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
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
  simpa only [sourceFlowNR_eq_walkNR] using
    flowLine_rightEntry_singleEdge w h k hk









theorem sourceFlow_leftExit_triangle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 2 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let s := kmswStage w (t - 1)
    (Reachable (⟨0⟩ : PresentVertex w) ⟨s.west (act w (t - 1))⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨s.east (act w (t - 1))⟩ ∧
      (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
      (∃ es, s.UL.dropLast.reverse = act w (r - 1) :: es ∧
      s.east (act w (r - 1)) = s.west (act w (t - 1)) ∧
      (kmswStage w t).triangles =
        s.triangles ++ [(act w (t - 1), act w t, act w (r - 1))] ∧
      act w t = s.nextEdge ∧
      (kmswStage w t).present (act w t) = true ∧
      (kmswStage w t).west (act w t) = s.west (act w (r - 1)) ∧
      (kmswStage w t).east (act w t) = s.east (act w (t - 1)))) ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w t).west (act w t)⟩ ∧
      (∃ e ∈ [act w (t - 1), act w t, act w (r - 1)],
        (kmswStage w t).west (act w t) = (kmswStage w t).west e ∨
        (kmswStage w t).west (act w t) = (kmswStage w t).east e) ∧
      ¬ (∀ e ∈ [act w (t - 1), act w t, act w (r - 1)],
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w t).west e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w t).east e⟩) ∧
      sourceFlowMhatInterfaceEdge w t (act w (t - 1)) := by
  rw [sourceFlowNR_eq_walkNR, sourceFlowNL_eq_walkNL]
  have htriangle := flowLine_leftExit_triangle w h k hk
  have hnot := lPhase_activeWest_unreachable w h (k - 1)
      (walkNL w h (k - 1)) le_rfl (by
        have hs := walkNR_succ_spec w h (k - 1)
        omega)
  refine ⟨htriangle, hnot, ?_, ?_, ?_⟩
  · refine ⟨act w (walkNL w h (k - 1)), ?_, Or.inl rfl⟩
    simp
  · intro hall
    exact hnot (hall (act w (walkNL w h (k - 1))) (by simp)).1
  · rcases htriangle with ⟨hw, he, _, hparts⟩
    rcases hparts with ⟨_, _, _, htri, _, _, _⟩
    exact sourceFlowMhatInterfaceEdge_of_newTriangle w
      (walkNL w h (k - 1)) (act w (walkNL w h (k - 1) - 1))
      (act w (walkNL w h (k - 1) - 1)) (act w (walkNL w h (k - 1)))
      (act w (walkNR w h (k - 1) - 1))
      hw he htri (by simp) hnot

/-- Source-indexed initial triangle convention base case of item (ii). The third triangle side is the
new missing geometric edge `s.nextEdge + 1`. It is allocated at time `t` and
has the unordered endpoint pair joining the initial vertices of `lambda_t`
and `lambda_{t-1}`. The missing edge has no orientation; its directed
presence is false at stage `t`. The retained inequality
`¬ (s.nextEdge + 1 < s.nextEdge)` expresses “unallocated before `t`” only
through the `State` convention that IDs at least `nextEdge` are unallocated
arithmetic. The initial vertex of `lambda_t` is unreachable from the root.
The face-complement clause uses the missing edge's unordered endpoint pair, -/
theorem sourceFlow_firstLeftExit_triangle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    let t := sourceFlowNL w h 0
    let s := kmswStage w (t - 1)
    ((L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨s.west s.active⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨s.east s.active⟩ ∧
      s.UL.dropLast.reverse = [] ∧
      (kmswStage w t).triangles =
        s.triangles ++ [(act w (t - 1), act w t, s.nextEdge + 1)] ∧
      act w t = s.nextEdge ∧
      (kmswStage w t).present (s.nextEdge + 1) = false) ∧
      (kmswStage w t).nextEdge = s.nextEdge + 2 ∧
      s.nextEdge + 1 < (kmswStage w t).nextEdge ∧
      ¬ (s.nextEdge + 1 < s.nextEdge) ∧
      (kmswStage w t).present (act w t) = true ∧
      (kmswStage w t).west (act w t) = s.nextVertex ∧
      (kmswStage w t).east (act w t) = s.east s.active ∧
      ({(kmswStage w t).west (s.nextEdge + 1),
        (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ) =
        {(kmswStage w t).west (act w t),
          (kmswStage w (t - 1)).west (act w (t - 1))} ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w t).west (act w t)⟩ ∧
      (∃ e ∈ [act w (t - 1), act w t, s.nextEdge + 1],
        (kmswStage w t).west (act w t) = (kmswStage w t).west e ∨
        (kmswStage w t).west (act w t) = (kmswStage w t).east e) ∧
      ¬ ((∀ e ∈ [act w (t - 1), act w t],
          Reachable (⟨0⟩ : PresentVertex w)
            ⟨(kmswStage w t).west e⟩ ∧
          Reachable (⟨0⟩ : PresentVertex w)
            ⟨(kmswStage w t).east e⟩) ∧
        ∀ v ∈ ({(kmswStage w t).west (s.nextEdge + 1),
            (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ),
          Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩) ∧
      sourceFlowMhatInterfaceEdge w t (act w (t - 1)) ∧
      (kmswStage w t).nextVertex = s.nextVertex + 1 := by
  rw [sourceFlowNL_eq_walkNL]
  let N := walkNL w h 0
  let s := kmswStage w (N - 1)
  have hbase := flowLine_firstLeftExit_triangle w h
  have hnot := quadrantFirstR_exit_activeWest_unreachable w h
  obtain ⟨hpos, hcode, _, hUL⟩ :=
    quadrantFirstR_exit_predecessor_emptyUL w h
  have hNsucc : N - 1 + 1 = N := by
    dsimp [N]
    omega
  have hcode' : w (N - 1) = 0 := by
    simpa [N] using hcode
  have hUL' : s.UL.dropLast.reverse = [] := by
    simpa [s, N] using hUL
  have hstep : kmswStage w N = kmswStepOfStep s .left := by
    rw [← hNsucc]
    change kmswStep s (w (N - 1)) = kmswStepOfStep s .left
    rw [hcode']
    rfl
  have hnextEdge : (kmswStage w N).nextEdge = s.nextEdge + 2 := by
    rw [hstep]
    simp [kmswStepOfStep, hUL', State.addEdge]
  have hglue := quadrantFirstR_exit_gluingTriangle w h
  rcases hglue with
    ⟨_, hactive, hwestAct, hwestNew, heastNew, hwestMissing,
      heastMissing, hpNew, hpMissing⟩
  have hpAct : (kmswStage w N).present (act w N) = true := by
    rw [hactive]
    exact hpNew
  have hwestAct' : (kmswStage w N).west (act w N) = s.nextVertex := by
    exact hwestAct
  have heastAct' : (kmswStage w N).east (act w N) = s.east s.active := by
    rw [hactive]
    exact heastNew
  have hallocated : s.nextEdge + 1 < (kmswStage w N).nextEdge := by
    rw [hnextEdge]
    omega
  have hnotAllocated : ¬ (s.nextEdge + 1 < s.nextEdge) := by omega
  have hnextVertex : (kmswStage w N).nextVertex = s.nextVertex + 1 := by
    rw [hstep]
    simp [kmswStepOfStep, hUL', State.addEdge]
  have hnotN : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w N).west (act w N)⟩ := by
    simpa [N] using hnot
  have hbase' := (show
      ((L w N - L w (N - 1), R w N - R w (N - 1)) = (-1, 0) ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨s.west s.active⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨s.east s.active⟩ ∧
        s.UL.dropLast.reverse = [] ∧
        (kmswStage w N).triangles =
          s.triangles ++ [(act w (N - 1), act w N, s.nextEdge + 1)] ∧
        act w N = s.nextEdge ∧
        (kmswStage w N).present (s.nextEdge + 1) = false) from by
      simpa only [N, s] using hbase)
  rcases hbase' with ⟨hcoordBase, hw, he, hULBase, htri, hactiveBase, hmiss⟩
  have hendpoints :
      ({(kmswStage w N).west (s.nextEdge + 1),
        (kmswStage w N).east (s.nextEdge + 1)} : Set ℕ) =
        {(kmswStage w N).west (act w N),
          (kmswStage w (N - 1)).west (act w (N - 1))} := by
    rw [hwestMissing, heastMissing, hwestAct']
    rfl
  have hboundary :
      ∃ e ∈ [act w (N - 1), act w N, s.nextEdge + 1],
        (kmswStage w N).west (act w N) = (kmswStage w N).west e ∨
        (kmswStage w N).west (act w N) = (kmswStage w N).east e := by
    exact ⟨act w N, by simp, Or.inl rfl⟩
  have hnotFace :
      ¬ ((∀ e ∈ [act w (N - 1), act w N],
          Reachable (⟨0⟩ : PresentVertex w)
            ⟨(kmswStage w N).west e⟩ ∧
          Reachable (⟨0⟩ : PresentVertex w)
            ⟨(kmswStage w N).east e⟩) ∧
        ∀ v ∈ ({(kmswStage w N).west (s.nextEdge + 1),
            (kmswStage w N).east (s.nextEdge + 1)} : Set ℕ),
          Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩) := by
    rintro ⟨_, hall⟩
    apply hnotN
    have hv := hall ((kmswStage w N).west (s.nextEdge + 1)) (by simp)
    have hmissingWestAct :
        (kmswStage w N).west (s.nextEdge + 1) =
          (kmswStage w N).west (act w N) :=
      hwestMissing.trans hwestAct'.symm
    rw [hmissingWestAct] at hv
    exact hv
  have hinterface := sourceFlowMhatInterfaceEdge_of_newTriangle w N
    (act w (N - 1)) (act w (N - 1)) (act w N) (s.nextEdge + 1)
    hw he htri (by simp) hnotN
  simpa only [N, s] using
    (show
      ((L w N - L w (N - 1), R w N - R w (N - 1)) = (-1, 0) ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨s.west s.active⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨s.east s.active⟩ ∧
        s.UL.dropLast.reverse = [] ∧
        (kmswStage w N).triangles =
          s.triangles ++ [(act w (N - 1), act w N, s.nextEdge + 1)] ∧
        act w N = s.nextEdge ∧
        (kmswStage w N).present (s.nextEdge + 1) = false) ∧
        (kmswStage w N).nextEdge = s.nextEdge + 2 ∧
        s.nextEdge + 1 < (kmswStage w N).nextEdge ∧
        ¬ (s.nextEdge + 1 < s.nextEdge) ∧
        (kmswStage w N).present (act w N) = true ∧
        (kmswStage w N).west (act w N) = s.nextVertex ∧
        (kmswStage w N).east (act w N) = s.east s.active ∧
        ({(kmswStage w N).west (s.nextEdge + 1),
          (kmswStage w N).east (s.nextEdge + 1)} : Set ℕ) =
          {(kmswStage w N).west (act w N),
            (kmswStage w (N - 1)).west (act w (N - 1))} ∧
        ¬ Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w N).west (act w N)⟩ ∧
        (∃ e ∈ [act w (N - 1), act w N, s.nextEdge + 1],
          (kmswStage w N).west (act w N) = (kmswStage w N).west e ∨
          (kmswStage w N).west (act w N) = (kmswStage w N).east e) ∧
        ¬ ((∀ e ∈ [act w (N - 1), act w N],
            Reachable (⟨0⟩ : PresentVertex w)
              ⟨(kmswStage w N).west e⟩ ∧
            Reachable (⟨0⟩ : PresentVertex w)
              ⟨(kmswStage w N).east e⟩) ∧
          ∀ v ∈ ({(kmswStage w N).west (s.nextEdge + 1),
              (kmswStage w N).east (s.nextEdge + 1)} : Set ℕ),
            Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩) ∧
        sourceFlowMhatInterfaceEdge w N (act w (N - 1)) ∧
        (kmswStage w N).nextVertex = s.nextVertex + 1 from by
      refine ⟨⟨hcoordBase, hw, he, hULBase, htri, hactiveBase, hmiss⟩,
        hnextEdge, hallocated, hnotAllocated, hpAct, hwestAct', heastAct',
        hendpoints, hnotN, hboundary, hnotFace, hinterface, hnextVertex⟩)










theorem flow_line_times_corrected (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    sourceFlowNR w h 0 = 0 ∧
    (∀ k, sourceFlowNL w h k = Nat.find (h.1 (sourceFlowNR w h k))) ∧
    (∀ k, sourceFlowNR w h (k + 1) = Nat.find (h.2 (sourceFlowNL w h k))) ∧
    (∀ k, IsLeast
      {n | sourceFlowLeftCandidate w (sourceFlowNR w h k) n}
      (sourceFlowNL w h k)) ∧
    (∀ k, IsLeast
      {n | sourceFlowRightCandidate w (sourceFlowNL w h k) n}
      (sourceFlowNR w h (k + 1))) ∧
    (∀ k, IsLeast
      {n | sourceFlowNR w h k + 1 ≤ n ∧
        L w n = L w (sourceFlowNR w h k) - 1}
      (sourceFlowNL w h k)) ∧
    (∀ k, IsLeast
      {n | sourceFlowNL w h k + 1 ≤ n ∧
        R w n = R w (sourceFlowNL w h k) - 1}
      (sourceFlowNR w h (k + 1))) ∧
    (∀ k (_hk : 2 ≤ k),
      let r := sourceFlowNR w h (k - 1)
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
            (kmswStage w r).present e = true)) ∧
    (∀ k (_hk : 2 ≤ k),
      let r := sourceFlowNR w h (k - 1)
      let t := sourceFlowNL w h (k - 1)
      let s := kmswStage w (t - 1)
      (Reachable (⟨0⟩ : PresentVertex w) ⟨s.west (act w (t - 1))⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨s.east (act w (t - 1))⟩ ∧
        (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
        (∃ es, s.UL.dropLast.reverse = act w (r - 1) :: es ∧
          s.east (act w (r - 1)) = s.west (act w (t - 1)) ∧
          (kmswStage w t).triangles =
            s.triangles ++ [(act w (t - 1), act w t, act w (r - 1))] ∧
          act w t = s.nextEdge ∧
          (kmswStage w t).present (act w t) = true ∧
          (kmswStage w t).west (act w t) = s.west (act w (r - 1)) ∧
          (kmswStage w t).east (act w t) = s.east (act w (t - 1)))) ∧
        ¬ Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w t).west (act w t)⟩ ∧
        (∃ e ∈ [act w (t - 1), act w t, act w (r - 1)],
          (kmswStage w t).west (act w t) = (kmswStage w t).west e ∨
          (kmswStage w t).west (act w t) = (kmswStage w t).east e)) ∧
    (let t := sourceFlowNL w h 0
      let s := kmswStage w (t - 1)
      ((L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨s.west s.active⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨s.east s.active⟩ ∧
        s.UL.dropLast.reverse = [] ∧
        (kmswStage w t).triangles =
          s.triangles ++ [(act w (t - 1), act w t, s.nextEdge + 1)] ∧
        act w t = s.nextEdge ∧
        (kmswStage w t).present (s.nextEdge + 1) = false) ∧
      (kmswStage w t).nextEdge = s.nextEdge + 2 ∧
      s.nextEdge + 1 < (kmswStage w t).nextEdge ∧
      ¬ (s.nextEdge + 1 < s.nextEdge) ∧
      (kmswStage w t).present (act w t) = true ∧
      (kmswStage w t).west (act w t) = s.nextVertex ∧
      (kmswStage w t).east (act w t) = s.east s.active ∧
      ({(kmswStage w t).west (s.nextEdge + 1),
        (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ) =
        {(kmswStage w t).west (act w t),
          (kmswStage w (t - 1)).west (act w (t - 1))} ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w t).west (act w t)⟩ ∧
      (∃ e ∈ [act w (t - 1), act w t, s.nextEdge + 1],
        (kmswStage w t).west (act w t) = (kmswStage w t).west e ∨
        (kmswStage w t).west (act w t) = (kmswStage w t).east e)) ∧
    (∀ n, sourceFlowMhat w n ↔
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).west (act w n)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).east (act w n)⟩) ∧
    (∀ k, 2 ≤ k →
      let r := sourceFlowNR w h (k - 1)
      let t := sourceFlowNL w h (k - 1)
      ¬ (∀ e ∈ [act w (t - 1), act w t, act w (r - 1)],
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w t).west e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w t).east e⟩) ∧
      sourceFlowMhatInterfaceEdge w t (act w (t - 1))) ∧
    (let t := sourceFlowNL w h 0
      let s := kmswStage w (t - 1)
      ¬ ((∀ e ∈ [act w (t - 1), act w t],
            Reachable (⟨0⟩ : PresentVertex w)
              ⟨(kmswStage w t).west e⟩ ∧
            Reachable (⟨0⟩ : PresentVertex w)
              ⟨(kmswStage w t).east e⟩) ∧
          ∀ v ∈ ({(kmswStage w t).west (s.nextEdge + 1),
              (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ),
            Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩) ∧
      sourceFlowMhatInterfaceEdge w t (act w (t - 1)) ∧
      (kmswStage w t).nextVertex = s.nextVertex + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sourceFlowNR_zero w h
  · intro k
    exact sourceFlowNL_level_min w h k
  · intro k
    exact sourceFlowNR_succ_level_min w h k
  · intro k
    exact sourceFlowNL_candidate_isLeast w h k
  · intro k
    exact sourceFlowNR_succ_candidate_isLeast w h k
  · intro k
    exact sourceFlowNL_level_isLeast w h k
  · intro k
    exact sourceFlowNR_succ_level_isLeast w h k
  · intro k hk
    exact sourceFlow_rightEntry_singleEdge w h k hk
  · intro k hk
    rcases sourceFlow_leftExit_triangle w h k hk with
      ⟨htriangle, hnot, hboundary, _, _⟩
    exact ⟨htriangle, hnot, hboundary⟩
  · rcases sourceFlow_firstLeftExit_triangle w h with
      ⟨hbase, hnext, hallocated, hnotAllocated, hpAct, hwestAct,
        heastAct, hendpoints, hnot, hboundary, _, _, _⟩
    exact ⟨hbase, hnext, hallocated, hnotAllocated, hpAct, hwestAct,
      heastAct, hendpoints, hnot, hboundary⟩
  · intro n
    exact sourceFlowMhat_endpoints_iff w n
  · intro k hk
    rcases sourceFlow_leftExit_triangle w h k hk with
      ⟨_, _, _, hface, hinterface⟩
    exact ⟨hface, hinterface⟩
  · rcases sourceFlow_firstLeftExit_triangle w h with
      ⟨_, _, _, _, _, _, _, _, _, _, hface, hinterface, hnextVertex⟩
    exact ⟨hface, hinterface, hnextVertex⟩

/-- Almost-sure instance of the deterministic candidate package for the iid
author ruling, so it is not counted as a paper result (`lem-flow-line-times`, -/
theorem iidCodes_ae_flow_line_times_corrected :
    ∀ᵐ ω ∂DirectedDistances.RandomWalk.iidCodeMeasure,
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      ∃ h : HasFlowLineHits w,
        sourceFlowNR w h 0 = 0 ∧
        (∀ k, sourceFlowNL w h k = Nat.find (h.1 (sourceFlowNR w h k))) ∧
        (∀ k, sourceFlowNR w h (k + 1) = Nat.find (h.2 (sourceFlowNL w h k))) ∧
        (∀ k, IsLeast
          {n | sourceFlowLeftCandidate w (sourceFlowNR w h k) n}
          (sourceFlowNL w h k)) ∧
        (∀ k, IsLeast
          {n | sourceFlowRightCandidate w (sourceFlowNL w h k) n}
          (sourceFlowNR w h (k + 1))) ∧
        (∀ k, IsLeast
          {n | sourceFlowNR w h k + 1 ≤ n ∧
            L w n = L w (sourceFlowNR w h k) - 1}
          (sourceFlowNL w h k)) ∧
        (∀ k, IsLeast
          {n | sourceFlowNL w h k + 1 ≤ n ∧
            R w n = R w (sourceFlowNL w h k) - 1}
          (sourceFlowNR w h (k + 1))) ∧
        (∀ k (_hk : 2 ≤ k),
          let r := sourceFlowNR w h (k - 1)
          let s := kmswStage w (r - 1)
          Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w r).west (act w r)⟩ ∧
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
                (kmswStage w r).present e = true)) ∧
        (∀ k (_hk : 2 ≤ k),
          let r := sourceFlowNR w h (k - 1)
          let t := sourceFlowNL w h (k - 1)
          let s := kmswStage w (t - 1)
          (Reachable (⟨0⟩ : PresentVertex w) ⟨s.west (act w (t - 1))⟩ ∧
            Reachable (⟨0⟩ : PresentVertex w) ⟨s.east (act w (t - 1))⟩ ∧
            (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
            (∃ es, s.UL.dropLast.reverse = act w (r - 1) :: es ∧
              s.east (act w (r - 1)) = s.west (act w (t - 1)) ∧
              (kmswStage w t).triangles =
                s.triangles ++ [(act w (t - 1), act w t, act w (r - 1))] ∧
              act w t = s.nextEdge ∧
              (kmswStage w t).present (act w t) = true ∧
              (kmswStage w t).west (act w t) = s.west (act w (r - 1)) ∧
              (kmswStage w t).east (act w t) = s.east (act w (t - 1)))) ∧
            ¬ Reachable (⟨0⟩ : PresentVertex w)
              ⟨(kmswStage w t).west (act w t)⟩ ∧
            (∃ e ∈ [act w (t - 1), act w t, act w (r - 1)],
              (kmswStage w t).west (act w t) = (kmswStage w t).west e ∨
              (kmswStage w t).west (act w t) = (kmswStage w t).east e)) ∧
        (let t := sourceFlowNL w h 0
          let s := kmswStage w (t - 1)
          ((L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
            Reachable (⟨0⟩ : PresentVertex w) ⟨s.west s.active⟩ ∧
            Reachable (⟨0⟩ : PresentVertex w) ⟨s.east s.active⟩ ∧
            s.UL.dropLast.reverse = [] ∧
            (kmswStage w t).triangles =
              s.triangles ++ [(act w (t - 1), act w t, s.nextEdge + 1)] ∧
            act w t = s.nextEdge ∧
            (kmswStage w t).present (s.nextEdge + 1) = false) ∧
          (kmswStage w t).nextEdge = s.nextEdge + 2 ∧
          s.nextEdge + 1 < (kmswStage w t).nextEdge ∧
          ¬ (s.nextEdge + 1 < s.nextEdge) ∧
          (kmswStage w t).present (act w t) = true ∧
          (kmswStage w t).west (act w t) = s.nextVertex ∧
          (kmswStage w t).east (act w t) = s.east s.active ∧
          ({(kmswStage w t).west (s.nextEdge + 1),
            (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ) =
            {(kmswStage w t).west (act w t),
              (kmswStage w (t - 1)).west (act w (t - 1))} ∧
          ¬ Reachable (⟨0⟩ : PresentVertex w)
            ⟨(kmswStage w t).west (act w t)⟩ ∧
          (∃ e ∈ [act w (t - 1), act w t, s.nextEdge + 1],
            (kmswStage w t).west (act w t) = (kmswStage w t).west e ∨
            (kmswStage w t).west (act w t) = (kmswStage w t).east e)) ∧
        (∀ n, sourceFlowMhat w n ↔
          Reachable (⟨0⟩ : PresentVertex w)
            ⟨(kmswStage w n).west (act w n)⟩ ∧
          Reachable (⟨0⟩ : PresentVertex w)
            ⟨(kmswStage w n).east (act w n)⟩) ∧
        (∀ k, 2 ≤ k →
          let r := sourceFlowNR w h (k - 1)
          let t := sourceFlowNL w h (k - 1)
          ¬ (∀ e ∈ [act w (t - 1), act w t, act w (r - 1)],
            Reachable (⟨0⟩ : PresentVertex w)
              ⟨(kmswStage w t).west e⟩ ∧
            Reachable (⟨0⟩ : PresentVertex w)
              ⟨(kmswStage w t).east e⟩) ∧
          sourceFlowMhatInterfaceEdge w t (act w (t - 1))) ∧
        (let t := sourceFlowNL w h 0
          let s := kmswStage w (t - 1)
          ¬ ((∀ e ∈ [act w (t - 1), act w t],
                Reachable (⟨0⟩ : PresentVertex w)
                  ⟨(kmswStage w t).west e⟩ ∧
                Reachable (⟨0⟩ : PresentVertex w)
                  ⟨(kmswStage w t).east e⟩) ∧
              ∀ v ∈ ({(kmswStage w t).west (s.nextEdge + 1),
                  (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ),
                Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩) ∧
          sourceFlowMhatInterfaceEdge w t (act w (t - 1)) ∧
          (kmswStage w t).nextVertex = s.nextVertex + 1) := by
  filter_upwards [DirectedDistances.KMSW.ae_hasFlowLineHits] with ω hω
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  exact ⟨hω, flow_line_times_corrected w hω⟩

end DirectedDistances.PaperProofs.Section5
