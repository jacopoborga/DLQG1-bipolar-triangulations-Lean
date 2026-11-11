 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.CellLDPLower

/-!
# Lemma 7.2 (`lem-cell-ldp-lower`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/











public section
namespace DirectedDistances.Paper.Section7

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section7

 
theorem cell_ldp_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
        1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
          c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
          iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
            (fun i => ω (i + 1)) n, ∃ q : Path a b,
              A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.cell_ldp_lower ε hε
 
 

end DirectedDistances.Paper.Section7
 
