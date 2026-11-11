 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.CellLDPUpper

/-!
# Lemma 7.4 (`lem-cell-ldp-upper`)

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

 
theorem cell_ldp_upper (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 2 / 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ) + ε) ≤
          iidCodeMeasure.real {ω | ∀ x y : StagePresentVertex
            (fun i => ω (i + 1)) n,
            x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            ldpSup x y ≤
              ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ)} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.cell_ldp_upper ε hε hεlt
 
 

end DirectedDistances.Paper.Section7
 
