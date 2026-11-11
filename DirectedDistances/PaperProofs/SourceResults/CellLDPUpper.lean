/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.Section7LdpUnconditional

/- # Isolated proof provider for Lemma 7.4 (`lem-cell-ldp-upper`)

forwards to a proved helper; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

KMSW stage built from the first `n` random codes; the event bounds `ldpSup x y` (supremum of
present directed path lengths, `⊥` when unreachable, i.e. `−∞`) by `⌊A n^{3/4}⌋` for every pair of
stage vertices. The `ε` range `0 < ε < 2/3` encodes the uniform `o(1)` in the exponent. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section7

/-- Lemma 7.4 isolated provider (`lem-cell-ldp-upper`, -/
theorem cell_ldp_upper (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 2 / 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ) + ε) ≤
          iidCodeMeasure.real {ω | ∀ x y : StagePresentVertex
            (fun i => ω (i + 1)) n,
            x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            ldpSup x y ≤
              ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ)} := by
  exact DirectedDistances.PaperProofs.Section7.cell_ldp_upper_of_items_ldpCode ε hε hεlt

end DirectedDistances.PaperProofs.SourceResults
