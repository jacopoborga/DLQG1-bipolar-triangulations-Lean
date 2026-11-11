/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.CellSDPLowerUpperUnconditional

/- # Isolated proof provider for Lemma 7.6 (`lem-cell-sdp-lower`)

forwards to a proved helper; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

`iidCodeMeasure`, the cell is the KMSW stage built from the first `n` random codes; the event asks
for a positive-index vertex of the lower-right boundary (an endpoint of an `LR` edge) whose SDP
distance from the boundary vertex of index `0`, as a natural number via `.toNat`, is at least
`A⁻¹ n^{3/8}`. Through `.toNat` an unreachable vertex (`⊤`) does not satisfy the event, so the
event implies the source inequality. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open Quiver MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7

/-- Lemma 7.6 isolated provider (`lem-cell-sdp-lower`, -/
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
              ⟨boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)⟩).toNat : ℝ)} := by
  exact DirectedDistances.PaperProofs.Section7.cell_sdp_lower_sdpCode δ hδ

end DirectedDistances.PaperProofs.SourceResults
