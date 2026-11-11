 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.CellSDPLower

/-!
# Lemma 7.6 (`lem-cell-sdp-lower`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/












public section
namespace DirectedDistances.Paper.Section7

open Quiver MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7

 
theorem cell_sdp_lower (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
      1 - δ ≤ iidCodeMeasure.real
        {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∃ r : ℕ, 1 ≤ r ∧
          (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
              (kmswStage (fun i => ω (i + 1)) n).east e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)) ∧
          A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
            ((sdp (⟨boundaryVertex (fun i => ω (i + 1)) h 0⟩ :
              StagePresentVertex (fun i => ω (i + 1)) n)
              ⟨boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)⟩).toNat : ℝ)} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.cell_sdp_lower δ hδ
 
 

end DirectedDistances.Paper.Section7
 
