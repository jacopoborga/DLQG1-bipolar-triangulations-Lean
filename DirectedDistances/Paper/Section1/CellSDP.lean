 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.ThmCellSDP

/-!
# Theorem 1.13 (`thm-cell-sdp`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/















public section
namespace DirectedDistances.Paper.Section1

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7

 
theorem thm_cell_sdp (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
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
              (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)) ∧
        (∃ h : BoundaryHitWitnesses w, ∃ r : ℕ, 1 ≤ r ∧
          (∃ e ∈ (kmswStage w n).LR,
            (kmswStage w n).west e = boundaryVertex w h (r : ℤ) ∨
              (kmswStage w n).east e = boundaryVertex w h (r : ℤ)) ∧
          A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
            ((sdp (⟨boundaryVertex w h 0⟩ : StagePresentVertex w n)
              ⟨boundaryVertex w h (r : ℤ)⟩).toNat : ℝ))} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.thm_cell_sdp δ hδ hδ1
 
 

end DirectedDistances.Paper.Section1
 
