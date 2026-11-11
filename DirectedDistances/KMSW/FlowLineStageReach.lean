/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.ActiveTimeMonotone
public import DirectedDistances.KMSW.FlowLineReachability
import DirectedDistances.KMSW.BoundaryDynamics
import DirectedDistances.KMSW.StageSubgraph

/-! # Reachability of the active flow-line edge

Activation-time reductions and stage-by-stage reachability helpers for -/

public section
namespace DirectedDistances.KMSW

open Quiver
open scoped Classical

private theorem path_before_arrow {w : ℕ → Fin 3} {u v z : PresentVertex w}
    (p : Path u v) (e : v ⟶ z) :
    ∀ f ∈ pathEdgeList p, ∃ hf : EdgePresent w f,
      actTime w f hf < actTime w e.val e.property.1 := by
  induction p generalizing z with
  | nil => simp [pathEdgeList]
  | @cons a b p f ih =>
    obtain hmem := ih f
    intro g hg
    have hlt := actTime_lt_of_consecutive w f.property.1 e.property.1
      (f.property.2.2.trans e.property.2.1.symm)
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨hgp, hltp⟩ := hmem g hg
      exact ⟨hgp, hltp.trans hlt⟩
    · have hgf := List.mem_singleton.mp hg
      subst g
      exact ⟨f.property.1, hlt⟩

private theorem reachable_vertex_iff_oldActPath (w : ℕ → Fin 3) (n : ℕ)
    (v : PresentVertex w) (hv : v.id = (kmswStage w n).west (act w n)) :
    Reachable (⟨0⟩ : PresentVertex w) v ↔
      v.id = 0 ∨ ∃ p : Path (⟨0⟩ : PresentVertex w) v,
        ∀ e ∈ pathEdgeList p, ∃ m < n, e = act w m := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => exact Or.inl rfl
    | @cons a b p e =>
        right
        refine ⟨Path.cons p e, ?_⟩
        intro f hf
        have hactive : EdgePresent w (act w n) :=
          EdgePresent.of_stage_present (act_lt_nextEdge w (le_rfl : n ≤ n))
            (kmswStage_active_present w n)
        have hends := edge_endpoints_eq w (act_lt_nextEdge w (le_rfl : n ≤ n))
        have hact : actTime w e.val e.property.1 < n := by
          have hcon := actTime_lt_of_consecutive w e.property.1 hactive
            (e.property.2.2.trans (hv.trans hends.1))
          rw [(actTime_eq_iff w (act w n) hactive n).2 rfl] at hcon
          exact hcon
        rcases (by simpa [pathEdgeList] using hf) with hf | hf
        · obtain ⟨hfp, hlt⟩ := path_before_arrow p e f hf
          refine ⟨actTime w f hfp, hlt.trans hact, ?_⟩
          exact actTime_spec w f hfp
        · subst f
          exact ⟨actTime w e.val e.property.1, hact,
            actTime_spec w e.val e.property.1⟩
  · rintro (hroot | ⟨p, hp⟩)
    · cases v with
      | mk id => simp_all
    · exact ⟨p⟩

/-- A path into the active west vertex uses only earlier active edges, unless
that vertex is the root (`lem-flow-line-times`, -/
theorem reachable_activeWest_iff_oldActPath (w : ℕ → Fin 3) (n : ℕ) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ ↔
    (kmswStage w n).west (act w n) = 0 ∨
      ∃ p : Path (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w n).west (act w n)⟩,
        ∀ e ∈ pathEdgeList p, ∃ m < n, e = act w m := by
  simpa using reachable_vertex_iff_oldActPath w n
    (⟨(kmswStage w n).west (act w n)⟩ : PresentVertex w) rfl

/-- Vertex IDs reachable from the root by edges active strictly before `n`,
with the root included (`lem-flow-line-times`, -/
@[expose] def actReachableBefore (w : ℕ → Fin 3) (n : ℕ) : Set ℕ :=
  {v | v = 0 ∨ ∃ p : Path (⟨0⟩ : PresentVertex w) ⟨v⟩,
    ∀ e ∈ pathEdgeList p, ∃ m < n, e = act w m}

/-- The sets of vertices reachable using active edges are increasing with the
activation cutoff (`lem-flow-line-times`, -/
theorem actReachableBefore_mono (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    actReachableBefore w m ⊆ actReachableBefore w n := by
  intro v hv
  change v = 0 ∨ _ at hv
  change v = 0 ∨ _
  rcases hv with hroot | ⟨p, hp⟩
  · exact Or.inl hroot
  · right
    refine ⟨p, ?_⟩
    intro e he
    obtain ⟨j, hj, hje⟩ := hp e he
    exact ⟨j, hj.trans_le hmn, hje⟩

private theorem actReachableBefore_path (w : ℕ → Fin 3) (n : ℕ) {v : ℕ}
    (hv : v ∈ actReachableBefore w n) :
    ∃ p : Path (⟨0⟩ : PresentVertex w) ⟨v⟩,
      ∀ e ∈ pathEdgeList p, ∃ m < n, e = act w m := by
  change v = 0 ∨ _ at hv
  rcases hv with hroot | hpath
  · rw [hroot]
    exact ⟨Path.nil, by simp [pathEdgeList]⟩
  · exact hpath

private theorem actReachableBefore_of_path (w : ℕ → Fin 3) (n : ℕ)
    {v : PresentVertex w} (p : Path (⟨0⟩ : PresentVertex w) v)
    (hp : ∀ e ∈ pathEdgeList p, ∃ m < n, e = act w m) :
    v.id ∈ actReachableBefore w n := by
  change v.id = 0 ∨ _
  exact Or.inr ⟨p, hp⟩

/-- Membership of the active west vertex in the strict activation prefix is
equivalent to its reachability in the limit present graph -/
theorem actReachableBefore_activeWest_iff (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).west (act w n) ∈ actReachableBefore w n ↔
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).west (act w n)⟩ := by
  simpa [actReachableBefore] using
    (reachable_activeWest_iff_oldActPath w n).symm

private theorem actReachableBefore_succ_iff (w : ℕ → Fin 3) (n v : ℕ) :
    v ∈ actReachableBefore w (n + 1) ↔
      v ∈ actReachableBefore w n ∨
        ((kmswStage w n).west (act w n) ∈ actReachableBefore w n ∧
          v = (kmswStage w n).east (act w n)) := by
  constructor
  · intro hv
    change v = 0 ∨ _ at hv
    rcases hv with hroot | ⟨p, hp⟩
    · exact Or.inl (Or.inl hroot)
    · cases p with
      | nil => exact Or.inl (Or.inl rfl)
      | @cons a b p e =>
          have hlast : e.val ∈ pathEdgeList (Path.cons p e) := by
            simp [pathEdgeList]
          obtain ⟨j, hj, hje⟩ := hp e.val hlast
          have hjle : j ≤ n := by omega
          by_cases hjn : j < n
          · left
            right
            refine ⟨Path.cons p e, ?_⟩
            intro f hf
            rcases (by simpa [pathEdgeList] using hf) with hf | hf
            · obtain ⟨hfp, hlt⟩ := path_before_arrow p e f hf
              have hte : actTime w e.val e.property.1 = j :=
                (actTime_eq_iff w e.val e.property.1 j).2 hje
              rw [hte] at hlt
              exact ⟨actTime w f hfp, lt_trans hlt hjn,
                actTime_spec w f hfp⟩
            · subst f
              exact ⟨j, hjn, hje⟩
          · have hjEq : j = n := by omega
            have hjeN : e.val = act w n := by simpa [hjEq] using hje
            have hte : actTime w e.val e.property.1 = n := by
              exact (actTime_eq_iff w e.val e.property.1 n).2 hjeN
            have hprefix : ∀ f ∈ pathEdgeList p, ∃ m < n, f = act w m := by
              intro f hf
              obtain ⟨hfp, hlt⟩ := path_before_arrow p e f hf
              rw [hte] at hlt
              exact ⟨actTime w f hfp, hlt, actTime_spec w f hfp⟩
            have hends := edge_endpoints_eq w (act_lt_nextEdge w (le_rfl : n ≤ n))
            have htarget : v = (kmswStage w n).east (act w n) := by
              calc
                v = edgeEast w e.val := e.property.2.2.symm
                _ = edgeEast w (act w n) := congrArg (edgeEast w) hjeN
                _ = (kmswStage w n).east (act w n) := hends.2.symm
            have hwest : (kmswStage w n).west (act w n) ∈ actReachableBefore w n := by
              have hpref := actReachableBefore_of_path w n p hprefix
              have hedge : edgeWest w e.val ∈ actReachableBefore w n :=
                e.property.2.1.symm ▸ hpref
              have hactive : edgeWest w (act w n) ∈ actReachableBefore w n :=
                (congrArg (edgeWest w) hjeN) ▸ hedge
              exact hends.1.symm ▸ hactive
            exact Or.inr ⟨hwest, htarget⟩
  · rintro (hold | ⟨hwest, htarget⟩)
    · exact actReachableBefore_mono w (Nat.le_succ n) hold
    · subst v
      obtain ⟨p, hp⟩ := actReachableBefore_path w n hwest
      have halloc := act_lt_nextEdge w (le_rfl : n ≤ n)
      have hends := edge_endpoints_eq w halloc
      let a : (⟨(kmswStage w n).west (act w n)⟩ : PresentVertex w) ⟶
          ⟨(kmswStage w n).east (act w n)⟩ :=
        ⟨act w n, ⟨n, halloc, kmswStage_active_present w n⟩,
          hends.1.symm, hends.2.symm⟩
      change (kmswStage w n).east (act w n) = 0 ∨ _
      right
      refine ⟨Path.cons p a, ?_⟩
      intro f hf
      rcases (by simpa [pathEdgeList] using hf) with hf | hf
      · obtain ⟨m, hm, hmf⟩ := hp f hf
        exact ⟨m, by omega, hmf⟩
      · subst f
        exact ⟨n, by omega, rfl⟩

/-- Adding the next active edge extends the root-reachable set exactly when its
west endpoint was already reachable (`lem-flow-line-times`, -/
theorem actReachableBefore_succ (w : ℕ → Fin 3) (n : ℕ) :
    actReachableBefore w (n + 1) =
      actReachableBefore w n ∪
        (if (kmswStage w n).west (act w n) ∈ actReachableBefore w n then
          {(kmswStage w n).east (act w n)} else ∅) := by
  classical
  ext v
  rw [actReachableBefore_succ_iff]
  by_cases hw : (kmswStage w n).west (act w n) ∈ actReachableBefore w n
  · simp [hw, or_comm]
  · simp [hw]

/-- An up step preserves reachability of the active west vertex -/
theorem actReachableBefore_up_activeWest (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1)
    (hr : (kmswStage w n).west (act w n) ∈ actReachableBefore w n) :
    (kmswStage w (n + 1)).west (act w (n + 1)) ∈
      actReachableBefore w (n + 1) := by
  apply (actReachableBefore_activeWest_iff w (n + 1)).2
  apply kmswStage_up_activeWest_reachable w n hc
  exact (actReachableBefore_activeWest_iff w n).1 hr

/-- A down step preserves reachability of the active west vertex -/
theorem actReachableBefore_down_activeWest (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2)
    (hr : (kmswStage w n).west (act w n) ∈ actReachableBefore w n) :
    (kmswStage w (n + 1)).west (act w (n + 1)) ∈
      actReachableBefore w (n + 1) := by
  apply (actReachableBefore_activeWest_iff w (n + 1)).2
  apply kmswStage_down_activeWest_reachable w n hc
  exact (actReachableBefore_activeWest_iff w n).1 hr

/-- On a left step, the next active west vertex is the nearest west UL vertex,
or the fresh vertex if the UL has no west edge -/
theorem kmswStage_left_activeWest_eq (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) :
    (kmswStage w (n + 1)).west (act w (n + 1)) =
      match (kmswStage w n).UL.dropLast.reverse with
      | [] => (kmswStage w n).nextVertex
      | e :: _ => (kmswStage w n).west e := by
  cases hu : (kmswStage w n).UL.dropLast.reverse with
  | nil =>
      simp [act, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
        hc, hu, State.addEdge]
  | cons e es =>
      simp [act, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
        hc, hu, State.addEdge]

private def flowLineCounterexampleCode (n : ℕ) : Fin 3 :=
  if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 2 else
    if n = 3 then 2 else if (n - 4) % 5 < 3 then 0 else 2

private theorem flowLineCounterexample_stageFour_activeWest :
    (kmswStage flowLineCounterexampleCode 4).west
      (act flowLineCounterexampleCode 4) = 1 := by
  rfl

private theorem flowLineCounterexample_stageFour_UL :
    (kmswStage flowLineCounterexampleCode 4).UL = [3, 4, 5] := by
  rfl

private theorem flowLineCounterexample_stageFour_UL_avoids_root :
    ∀ e ∈ (kmswStage flowLineCounterexampleCode 4).UL,
      (kmswStage flowLineCounterexampleCode 4).west e ≠ 0 ∧
        (kmswStage flowLineCounterexampleCode 4).east e ≠ 0 := by
  decide

private theorem flowLineCounterexample_one_mem_stageOne :
    1 ∈ actReachableBefore flowLineCounterexampleCode 1 := by
  change 1 = 0 ∨ _
  right
  let hPresent : EdgePresent flowLineCounterexampleCode 0 :=
    EdgePresent.of_stage_present (w := flowLineCounterexampleCode) (n := 0)
      (e := 0) (by decide) (by decide)
  let a : (⟨0⟩ : PresentVertex flowLineCounterexampleCode) ⟶ ⟨1⟩ :=
    ⟨0, hPresent, by rfl, by rfl⟩
  refine ⟨Path.nil.cons a, ?_⟩
  intro e he
  have he0 : e = 0 := by simpa [pathEdgeList] using he
  subst e
  exact ⟨0, by decide, by rfl⟩

private theorem flowLineCounterexample_one_mem_stageFour :
    1 ∈ actReachableBefore flowLineCounterexampleCode 4 :=
  actReachableBefore_mono flowLineCounterexampleCode (by decide)
    flowLineCounterexample_one_mem_stageOne

private theorem flowLineCounterexample_activeWest_mem_stageFour :
    (kmswStage flowLineCounterexampleCode 4).west
      (act flowLineCounterexampleCode 4) ∈
        actReachableBefore flowLineCounterexampleCode 4 := by
  rw [flowLineCounterexample_stageFour_activeWest]
  exact flowLineCounterexample_one_mem_stageFour

private theorem flowLineCounterexample_L_zero :
    L flowLineCounterexampleCode 0 = 0 := by decide

private theorem flowLineCounterexample_L_one :
    L flowLineCounterexampleCode 1 = -1 := by decide

private theorem flowLineCounterexample_R_one :
    R flowLineCounterexampleCode 1 = 0 := by decide

private theorem flowLineCounterexample_R_two :
    R flowLineCounterexampleCode 2 = 1 := by decide

private theorem flowLineCounterexample_R_three :
    R flowLineCounterexampleCode 3 = 0 := by decide

private theorem flowLineCounterexample_R_four :
    R flowLineCounterexampleCode 4 = -1 := by decide

private theorem flowLineCounterexample_walkNL_zero (h :
    HasFlowLineHits flowLineCounterexampleCode) :
    walkNL flowLineCounterexampleCode h 0 = 1 := by
  change (∀ n, ∃ m, n + 1 ≤ m ∧
    L flowLineCounterexampleCode m = L flowLineCounterexampleCode n - 1) ∧ _ at h
  have hcand : 0 + 1 ≤ 1 ∧
      L flowLineCounterexampleCode 1 = L flowLineCounterexampleCode 0 - 1 := by
    exact ⟨by omega, by
      rw [flowLineCounterexample_L_one, flowLineCounterexample_L_zero]
      norm_num⟩
  have hupper : firstFlowLHit flowLineCounterexampleCode h 0 ≤ 1 := by
    unfold firstFlowLHit
    exact Nat.find_min' (h.1 0) hcand
  have hspec := firstFlowLHit_spec flowLineCounterexampleCode h 0
  have heq : firstFlowLHit flowLineCounterexampleCode h 0 = 1 := by
    omega
  change firstFlowLHit flowLineCounterexampleCode h 0 = 1
  exact heq

private theorem flowLineCounterexample_walkNR_one (h :
    HasFlowLineHits flowLineCounterexampleCode) :
    walkNR flowLineCounterexampleCode h 1 = 4 := by
  change (∀ n, ∃ m, n + 1 ≤ m ∧
    L flowLineCounterexampleCode m = L flowLineCounterexampleCode n - 1) ∧
    (∀ n, ∃ m, n + 1 ≤ m ∧
      R flowLineCounterexampleCode m = R flowLineCounterexampleCode n - 1) at h
  change firstFlowRHit flowLineCounterexampleCode h
    (walkNL flowLineCounterexampleCode h 0) = 4
  rw [flowLineCounterexample_walkNL_zero h]
  have hcand : 1 + 1 ≤ 4 ∧
      R flowLineCounterexampleCode 4 = R flowLineCounterexampleCode 1 - 1 := by
    exact ⟨by omega, by
      rw [flowLineCounterexample_R_four, flowLineCounterexample_R_one]
      norm_num⟩
  have hupper : firstFlowRHit flowLineCounterexampleCode h 1 ≤ 4 := by
    unfold firstFlowRHit
    exact Nat.find_min' (h.2 1) hcand
  have hspec := firstFlowRHit_spec flowLineCounterexampleCode h 1
  have hlower : 4 ≤ firstFlowRHit flowLineCounterexampleCode h 1 := by
    by_contra hnot
    have hsmall : firstFlowRHit flowLineCounterexampleCode h 1 = 2 ∨
        firstFlowRHit flowLineCounterexampleCode h 1 = 3 := by omega
    rcases hsmall with htwo | hthree
    · have hhit := hspec.2
      rw [htwo, flowLineCounterexample_R_two, flowLineCounterexample_R_one] at hhit
      norm_num at hhit
    · have hhit := hspec.2
      rw [hthree, flowLineCounterexample_R_three,
        flowLineCounterexample_R_one] at hhit
      norm_num at hhit
  exact Nat.le_antisymm hupper hlower

end DirectedDistances.KMSW
