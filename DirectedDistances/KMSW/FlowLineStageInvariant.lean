/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineStageReach
import DirectedDistances.KMSW.StageIncidenceChains

/-! # Stage reachability during flow-line intervals

Helpers for the deterministic reachability characterization in -/

public section
namespace DirectedDistances.KMSW

open Quiver
open scoped Classical

/-- At cutoff zero, only the root is reachable by a path using strictly earlier
active edges (`lem-flow-line-times`, -/
theorem actReachableBefore_zero (w : ℕ → Fin 3) :
    actReachableBefore w 0 = {0} := by
  ext v
  constructor
  · intro hv
    change v = 0 ∨ _ at hv
    rcases hv with hroot | ⟨p, hp⟩
    · exact hroot
    · cases p with
      | nil => rfl
      | @cons a b p e =>
          have hlast : e.val ∈ pathEdgeList (Path.cons p e) := by
            simp [pathEdgeList]
          obtain ⟨m, hm, _⟩ := hp e.val hlast
          omega
  · intro hv
    have : v = 0 := by simpa using hv
    subst v
    change 0 = 0 ∨ _
    exact Or.inl rfl

/-- Finite computation of the vertices reachable by the first `n` active
edges (`lem-flow-line-times`, -/
@[expose] def stageReachableVertices (w : ℕ → Fin 3) : ℕ → Finset ℕ
  | 0 => {0}
  | n + 1 =>
      let s := stageReachableVertices w n
      if (kmswStage w n).west (act w n) ∈ s then
        insert ((kmswStage w n).east (act w n)) s else s

/-- The finite reachable set adds exactly the terminal vertex of an active
edge whose initial vertex was already reachable -/
theorem stageReachableVertices_succ (w : ℕ → Fin 3) (n : ℕ) :
    stageReachableVertices w (n + 1) =
      if (kmswStage w n).west (act w n) ∈ stageReachableVertices w n then
        insert ((kmswStage w n).east (act w n)) (stageReachableVertices w n)
      else stageReachableVertices w n := rfl

private theorem stageReachableVertices_lt_nextVertex (w : ℕ → Fin 3)
    (n v : ℕ) (hv : v ∈ stageReachableVertices w n) :
    v < (kmswStage w n).nextVertex := by
  induction n with
  | zero =>
      simp only [stageReachableVertices, Finset.mem_singleton] at hv
      subst v
      simp [kmswStage, kmswInit]
  | succ n ih =>
      rw [stageReachableVertices_succ] at hv
      by_cases hw : (kmswStage w n).west (act w n) ∈ stageReachableVertices w n
      · simp only [if_pos hw, Finset.mem_insert] at hv
        rcases hv with hve | hv
        · subst v
          exact ((kmswStage_endpoints_lt_nextVertex w n (act w n)
            (act_lt_nextEdge w (le_rfl : n ≤ n))).2).trans_le
              (CutConverse.nextVertex_mono w (Nat.le_succ n))
        · exact (ih hv).trans_le (CutConverse.nextVertex_mono w (Nat.le_succ n))
      · simp only [if_neg hw] at hv
        exact (ih hv).trans_le (CutConverse.nextVertex_mono w (Nat.le_succ n))

private theorem leftPredecessor_ne_activeEast (w : ℕ → Fin 3) (n e : ℕ)
    (es : List ℕ)
    (hpred : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).west e ≠ (kmswStage w n).east (act w n) := by
  let s := kmswStage w n
  have heUL : e ∈ s.UL := by
    have he : e ∈ s.UL.dropLast.reverse := by rw [hpred]; simp
    exact List.dropLast_subset _ (List.mem_reverse.mp he)
  have heBound : e < s.nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl heUL))
  have hactBound : act w n < s.nextEdge := by
    simpa [s] using act_lt_nextEdge w (le_rfl : n ≤ n)
  have hInc : s.east e = s.west s.active := by
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
    have hrev : xs.reverse = e :: es := by
      simpa [s, hUL, List.reverse_append] using hpred
    have hxs : xs = es.reverse ++ [e] := by
      have h := congrArg List.reverse hrev
      simpa only [List.reverse_reverse, List.reverse_cons, List.reverse_append,
        List.reverse_nil] using h
    have hUL' : s.UL = es.reverse ++ [e, s.active] := by
      rw [hUL, hxs]
      simp [s, List.append_assoc]
    have hchain : List.IsChain (fun a b => s.east a = s.west b) s.UL :=
      (kmswStage_boundary_chain_invariant w n).1.left_of_append
    rw [hUL'] at hchain
    exact (List.isChain_append_cons_cons.mp hchain).2.1
  have heRank := kmswStageRank_strict w n e heBound
  have hactRank := kmswStageRank_strict w n (act w n) hactBound
  rw [hInc] at heRank
  intro h
  have hlt : kmswStageRank w n (s.west e) <
      kmswStageRank w n (s.east (act w n)) := heRank.trans hactRank
  rw [h] at hlt
  exact (lt_irrefl _) hlt

/-- On a left step, reachability of the new active west endpoint is exactly
reachability of the nearest predecessor's west endpoint; when no predecessor
exists, the fresh endpoint is unreachable -/
theorem stageReachableVertices_left_activeWest_iff (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) :
    (kmswStage w (n + 1)).west (act w (n + 1)) ∈
        stageReachableVertices w (n + 1) ↔
      match (kmswStage w n).UL.dropLast.reverse with
      | [] => False
      | e :: _ => (kmswStage w n).west e ∈ stageReachableVertices w n := by
  rw [kmswStage_left_activeWest_eq w n hc]
  cases hpred : (kmswStage w n).UL.dropLast.reverse with
  | nil =>
      change (kmswStage w n).nextVertex ∈
        stageReachableVertices w (n + 1) ↔ False
      rw [stageReachableVertices_succ]
      have hfresh : (kmswStage w n).nextVertex ∉ stageReachableVertices w n := by
        intro hmem
        exact (Nat.lt_irrefl _ (stageReachableVertices_lt_nextVertex w n _ hmem))
      have heast : (kmswStage w n).nextVertex ≠ (kmswStage w n).east (act w n) := by
        have hbound := (kmswStage_endpoints_lt_nextVertex w n (act w n)
          (act_lt_nextEdge w (le_rfl : n ≤ n))).2
        omega
      by_cases hw : (kmswStage w n).west (act w n) ∈ stageReachableVertices w n
      · simp [hw, hfresh, heast]
      · simp [hw, hfresh]
  | cons e es =>
      change (kmswStage w n).west e ∈
        stageReachableVertices w (n + 1) ↔
          (kmswStage w n).west e ∈ stageReachableVertices w n
      rw [stageReachableVertices_succ]
      have hne := leftPredecessor_ne_activeEast w n e es hpred
      by_cases hw : (kmswStage w n).west (act w n) ∈ stageReachableVertices w n
      · simp [hw, hne]
      · simp [hw, hne]

/-- The finite stage computation agrees with path reachability in the strict
activation prefix (`lem-flow-line-times`, -/
theorem mem_stageReachableVertices_iff (w : ℕ → Fin 3) (n v : ℕ) :
    v ∈ stageReachableVertices w n ↔ v ∈ actReachableBefore w n := by
  induction n generalizing v with
  | zero => simp [stageReachableVertices, actReachableBefore_zero]
  | succ n ih =>
      rw [stageReachableVertices, actReachableBefore_succ]
      by_cases hw : (kmswStage w n).west (act w n) ∈ stageReachableVertices w n
      · have hr : (kmswStage w n).west (act w n) ∈ actReachableBefore w n :=
          (ih _).1 hw
        simp [hw, hr, ih, or_comm, Finset.mem_insert]
      · have hr : (kmswStage w n).west (act w n) ∉ actReachableBefore w n := by
          intro hp
          exact hw ((ih _).2 hp)
        simp [hw, hr, ih]

private def stageInvariantSampleCode (n : ℕ) : Fin 3 :=
  if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 2 else
    if n = 3 then 2 else if (n - 4) % 5 < 3 then 0 else 2

private theorem sample_UL_values :
    (kmswStage stageInvariantSampleCode 0).UL = [0] ∧
    (kmswStage stageInvariantSampleCode 1).UL = [1] ∧
    (kmswStage stageInvariantSampleCode 2).UL = [3] ∧
    (kmswStage stageInvariantSampleCode 3).UL = [3, 4] ∧
    (kmswStage stageInvariantSampleCode 4).UL = [3, 4, 5] := by
  decide

private theorem sample_stage4_UL :
    (kmswStage stageInvariantSampleCode 4).UL = [3, 4, 5] := by
  decide

private theorem sample_stage4_activeWest :
    (kmswStage stageInvariantSampleCode 4).west
      (act stageInvariantSampleCode 4) = 1 := by
  rfl

private theorem sample_stage5_activeWest :
    (kmswStage stageInvariantSampleCode 5).west
      (act stageInvariantSampleCode 5) = 3 := by
  rfl

private theorem sample_reachable_phase_prefix :
    (kmswStage stageInvariantSampleCode 0).west (act stageInvariantSampleCode 0) ∈
        stageReachableVertices stageInvariantSampleCode 0 ∧
    (kmswStage stageInvariantSampleCode 1).west (act stageInvariantSampleCode 1) ∉
        stageReachableVertices stageInvariantSampleCode 1 ∧
    (kmswStage stageInvariantSampleCode 2).west (act stageInvariantSampleCode 2) ∉
        stageReachableVertices stageInvariantSampleCode 2 ∧
    (kmswStage stageInvariantSampleCode 3).west (act stageInvariantSampleCode 3) ∉
        stageReachableVertices stageInvariantSampleCode 3 ∧
    (kmswStage stageInvariantSampleCode 4).west (act stageInvariantSampleCode 4) ∈
        stageReachableVertices stageInvariantSampleCode 4 ∧
    (kmswStage stageInvariantSampleCode 5).west (act stageInvariantSampleCode 5) ∉
        stageReachableVertices stageInvariantSampleCode 5 ∧
    (kmswStage stageInvariantSampleCode 6).west (act stageInvariantSampleCode 6) ∉
        stageReachableVertices stageInvariantSampleCode 6 ∧
    (kmswStage stageInvariantSampleCode 7).west (act stageInvariantSampleCode 7) ∉
        stageReachableVertices stageInvariantSampleCode 7 ∧
    (kmswStage stageInvariantSampleCode 8).west (act stageInvariantSampleCode 8) ∈
        stageReachableVertices stageInvariantSampleCode 8 ∧
    (kmswStage stageInvariantSampleCode 9).west (act stageInvariantSampleCode 9) ∈
        stageReachableVertices stageInvariantSampleCode 9 ∧
    (kmswStage stageInvariantSampleCode 10).west (act stageInvariantSampleCode 10) ∈
        stageReachableVertices stageInvariantSampleCode 10 := by
  decide

private def sampleReachableULCount (n : ℕ) : ℕ :=
  (((kmswStage stageInvariantSampleCode n).UL.reverse.filter fun e =>
    decide ((kmswStage stageInvariantSampleCode n).west e ∈
      stageReachableVertices stageInvariantSampleCode n))).length

private theorem sample_reachable_UL_count_values :
    sampleReachableULCount 0 = 1 ∧
    sampleReachableULCount 1 = 0 ∧
    sampleReachableULCount 2 = 0 ∧
    sampleReachableULCount 3 = 0 ∧
    sampleReachableULCount 4 = 1 ∧
    sampleReachableULCount 5 = 0 ∧
    sampleReachableULCount 6 = 0 ∧
    sampleReachableULCount 7 = 0 ∧
    sampleReachableULCount 8 = 1 ∧
    sampleReachableULCount 9 = 2 ∧
    sampleReachableULCount 10 = 1 := by
  decide

private def sampleULReachabilityBits (n : ℕ) : List Bool :=
  ((kmswStage stageInvariantSampleCode n).UL.reverse.map fun e =>
    decide ((kmswStage stageInvariantSampleCode n).west e ∈
      stageReachableVertices stageInvariantSampleCode n))

private theorem sample_UL_reachability_bit_values_0_4 :
    sampleULReachabilityBits 0 = [true] ∧
    sampleULReachabilityBits 1 = [false] ∧
    sampleULReachabilityBits 2 = [false] ∧
    sampleULReachabilityBits 3 = [false, false] ∧
    sampleULReachabilityBits 4 = [true, false, false] := by
  decide

private theorem sample_UL_reachability_bit_values_5_10 :
    sampleULReachabilityBits 5 = [false, false] ∧
    sampleULReachabilityBits 6 = [false] ∧
    sampleULReachabilityBits 7 = [false] := by
  decide

private theorem sample_UL_reachability_bit_values_8_10 :
    sampleULReachabilityBits 8 = [true, false] ∧
    sampleULReachabilityBits 9 = [true, true, false] ∧
    sampleULReachabilityBits 10 = [true, false] := by
  decide

private def alternateSampleCode (n : ℕ) : Fin 3 :=
  if n % 5 < 3 then 0 else 2

private def activeWestReachBit (w : ℕ → Fin 3) (n : ℕ) : Bool :=
  decide ((kmswStage w n).west (act w n) ∈ stageReachableVertices w n)

private theorem alternate_sample_reachability_prefix_0_4 :
    activeWestReachBit alternateSampleCode 0 = true ∧
    activeWestReachBit alternateSampleCode 1 = false ∧
    activeWestReachBit alternateSampleCode 2 = false ∧
    activeWestReachBit alternateSampleCode 3 = false ∧
    activeWestReachBit alternateSampleCode 4 = true := by
  decide

private theorem alternate_sample_reachability_prefix_5_9 :
    activeWestReachBit alternateSampleCode 5 = true ∧
    activeWestReachBit alternateSampleCode 6 = true ∧
    activeWestReachBit alternateSampleCode 7 = false ∧
    activeWestReachBit alternateSampleCode 8 = false ∧
    activeWestReachBit alternateSampleCode 9 = true := by
  decide

end DirectedDistances.KMSW
