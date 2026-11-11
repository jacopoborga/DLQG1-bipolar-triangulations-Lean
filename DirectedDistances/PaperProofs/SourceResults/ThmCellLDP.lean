/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.CellTheorems

/- # Isolated proof provider for Theorem 1.12 (`thm-cell-ldp`)

forwards to a proved helper; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

Reading: under `iidCodeMeasure`, the cell `M_{0,n}` is the KMSW stage built from the first `n`
random codes. For each `δ ∈ (0,1)` there is `A > 1` such that for every `n ≥ 1`, with probability
at least `1 - δ`, both `A⁻¹ n^{3/4} ≤ sup LDP` (some directed path has length at least
`A⁻¹ n^{3/4}`) and `sup LDP ≤ A n^{3/4}` (every pair of stage vertices has `ldpSup ≤ ⌊A n^{3/4}⌋₊`,
unreachable pairs being `⊥ = -∞`) hold on one event. The proof combines Lemmas 7.2 and 7.4. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7

/-- packaging only. -/
theorem thm_cell_ldp (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
      1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
        (∃ a b : StagePresentVertex (fun i => ω (i + 1)) n, ∃ q : Path a b,
          A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)) ∧
        (∀ x y : StagePresentVertex (fun i => ω (i + 1)) n,
          x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
          y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
          ldpSup x y ≤ ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ))} := by
  exact DirectedDistances.PaperProofs.Section7.thm_cell_ldp_code δ hδ hδ1

end DirectedDistances.PaperProofs.SourceResults
