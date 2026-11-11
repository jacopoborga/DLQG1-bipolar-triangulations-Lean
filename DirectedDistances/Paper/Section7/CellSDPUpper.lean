 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.CellSDPUpper

/-!
# Lemma 7.8 (`lem-cell-sdp-upper`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/















public section
namespace DirectedDistances.Paper.Section7

open Quiver MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7

 
theorem cell_sdp_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          (∀ x : ℕ,
            (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
              (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
            ∃ y : ℕ,
              (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
                (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)) ∧
          (∀ y : ℕ,
            (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
              (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
            ∃ x : ℕ,
              (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
                (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞))} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.cell_sdp_upper δ hδ
 
 

end DirectedDistances.Paper.Section7
 
