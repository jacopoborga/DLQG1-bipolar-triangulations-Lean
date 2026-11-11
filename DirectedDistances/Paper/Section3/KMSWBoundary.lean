 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWBoundarySource

/-!
# Lemma 3.6 (`lem-kmsw-bdy`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/

































public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.KMSW



theorem kmsw_bdy (w : ℕ → Fin 3) (n : ℕ) :
    (
    (kmswStage w n).LL.reverse =
      ((List.range (n + 1)).filter (fun m => decide
        (0 < m ∧ ∀ j < m, L w m < L w j))).map (kmswLLCreatedEdge w)
    ) ∧
    (
    ∀ (k : ℕ), 1 ≤ k → ∀ (hhit : ∃ t, L w t = -(k : ℤ)),
      Nat.find hhit ≤ n →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = kmswLLCreatedEdge w (Nat.find hhit) ∧
        (kmswStage w n).LL.reverse[k - 1]? = some e.val ∧
        (kmswStageDirectedMap w n).missing (e, true) ∧
        (kmswStageDirectedMap w n).IsOuter (e, true) ∧
        (∀ m (hm : m ≤ n),
          PaperProofs.Section3.kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false =
              PaperProofs.Section3.kmswBoundaryVertex w n e false ↔
            L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j) ∧
        IsLeast {m | ∃ hm : m ≤ n,
          PaperProofs.Section3.kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false =
            PaperProofs.Section3.kmswBoundaryVertex w n e false} (Nat.find hhit)
    ) ∧
    (
    (kmswStage w n).LR =
      ((List.range (n + 1)).filter (fun m => decide
        (∀ j, j < m → R w m < R w j))).map (act w)
    ) ∧
    (
    ∀ (k : ℕ), 1 ≤ k → ∀ (hhit : ∃ t, R w t = -(k : ℤ)), Nat.find hhit ≤ n →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = act w (Nat.find hhit) ∧
        (kmswStage w n).LR[(k + 1) - 1]? = some e.val ∧
        (e, true) ∈ (kmswStageDirectedMap w n).lrDarts ∧
        (∀ m (hm : m ≤ n),
          PaperProofs.Section3.kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ true =
              PaperProofs.Section3.kmswBoundaryVertex w n e true ↔
            R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j) ∧
        IsLeast {m | ∃ hm : m ≤ n,
          PaperProofs.Section3.kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ true =
            PaperProofs.Section3.kmswBoundaryVertex w n e true} (Nat.find hhit)
    ) ∧
    (
    (kmswStage w n).UL =
      ((List.range (n + 1)).filter (fun m => decide
        (∀ j, m + 1 ≤ j → j ≤ n → L w m + 1 ≤ L w j))).map (act w)
    ) ∧
    (
    ∀ (k m : ℕ), 1 ≤ k →
      ((List.range (n + 1)).filter (fun t => decide
        (∀ j, t + 1 ≤ j → j ≤ n → L w t + 1 ≤ L w j)))[k - 1]? = some m →
      ∃ hm : m ≤ n,
        (kmswStage w n).UL[k - 1]? = some (act w m) ∧
        (⟨act w m, act_lt_nextEdge w hm⟩, false) ∈
          (kmswStageDirectedMap w n).ulDarts ∧
        ∀ m' (hm' : m' ≤ m), L w m' = L w m →
          (∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) →
          PaperProofs.Section3.kmswBoundaryVertex w n
              ⟨act w m', act_lt_nextEdge w (hm'.trans hm)⟩ false =
            PaperProofs.Section3.kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false
    ) ∧
    (
    (kmswStage w n).UR.reverse =
      ((List.range (n + 1)).filter (fun m => decide
        (0 < m ∧ m ≤ n ∧ ∀ j, m ≤ j → j ≤ n →
          R w (m - 1) + 1 ≤ R w j))).map (kmswURCreatedEdge w)
    ) ∧
    (
    ∀ (k m : ℕ), 1 ≤ k →
      ((List.range (n + 1)).filter (fun t => decide
        (0 < t ∧ t ≤ n ∧ ∀ j, t ≤ j → j ≤ n →
          R w (t - 1) + 1 ≤ R w j)))[k - 1]? = some m →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = kmswURCreatedEdge w m ∧
        (kmswStage w n).UR.reverse[k - 1]? = some e.val ∧
        (kmswStageDirectedMap w n).missing (e, false) ∧
        (kmswStageDirectedMap w n).IsOuter (e, false)
    ) ∧
    (
    stageOuterWordVal w n =
      ((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false)) ++
      ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
      ((kmswStage w n).LL.reverse.map fun e => (e, true)) ∧
    ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d
    ) ∧
    (
    ∀ d : StageDart (kmswStage w n).nextEdge,
      (d ∈ kmswStageULDartsFinset w n ↔
        d ∈ (kmswStageDirectedMap w n).ulDarts) ∧
      (d ∈ kmswStageLRDartsFinset w n ↔
        d ∈ (kmswStageDirectedMap w n).lrDarts) ∧
      (d ∈ kmswStageLLDartsFinset w n ↔
        (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = true) ∧
      (d ∈ kmswStageURDartsFinset w n ↔
        (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = false)
    ) ∧
    (
    ((kmswStageULDartsFinset w n).card : ℤ) = L w n - minL w n + 1 ∧
    ((kmswStageURDartsFinset w n).card : ℤ) = R w n - minR w n ∧
    ((kmswStageLLDartsFinset w n).card : ℤ) = -minL w n ∧
    ((kmswStageLRDartsFinset w n).card : ℤ) = -minR w n + 1
    ) :=
 
by exact DirectedDistances.PaperProofs.Section3.kmsw_bdy_source w n
 
 

end DirectedDistances.Paper.Section3
 
