 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.ThmCellLDP

/-!
# Theorem 1.12 (`thm-cell-ldp`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/















public section
namespace DirectedDistances.Paper.Section1

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7

 
theorem thm_cell_ldp (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
      1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
        (∃ a b : StagePresentVertex (fun i => ω (i + 1)) n, ∃ q : Path a b,
          A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)) ∧
        (∀ x y : StagePresentVertex (fun i => ω (i + 1)) n,
          x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
          y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
          ldpSup x y ≤ ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ))} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.thm_cell_ldp δ hδ hδ1
 
 

end DirectedDistances.Paper.Section1
 
