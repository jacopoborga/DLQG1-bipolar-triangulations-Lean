/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.Section7LdpUnconditional

/- # Isolated proof provider for Lemma 7.2 (`lem-cell-ldp-lower`)

forwards to a proved helper; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

KMSW stage `kmswStage (fun i => ω (i + 1)) n` built from the first `n` random codes (the shift skips
the deterministic time-zero code); the event is that it has a directed path of present edges of
length at least `A⁻¹ n^{3/4}`. The `ε` family encodes the uniform `o(1)` in the exponent. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section7

/-- Lemma 7.2 isolated provider (`lem-cell-ldp-lower`, -/
theorem cell_ldp_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
        1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
          c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
          iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
            (fun i => ω (i + 1)) n, ∃ q : Path a b,
              A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  exact DirectedDistances.PaperProofs.Section7.cell_ldp_lower_of_ind_sym_ldpCode ε hε

end DirectedDistances.PaperProofs.SourceResults
