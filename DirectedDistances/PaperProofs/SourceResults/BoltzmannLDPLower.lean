/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.BoltzmannLDPLowerShifted
-- Proof-only access to the assembly proposition body.
import all DirectedDistances.PaperProofs.Section7.BoltzmannLDPLowerAssembly

/- # Isolated proof provider for Lemma 7.11 (`lem-boltzmann-ldp-lower`)

forwards to proved helpers; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added. The proof-local shifted-density finding is recorded

Reading: `rightVertexMarkedBoltzmannLaw r` is the Boltzmann law of maps with right boundary
length `r` and a marked left-boundary vertex (marked-vertex convention; source/sink convention: `x₀` source, `x_r` sink);
`ldpLengthBase` of the underlying map is the maximal length of a simple directed path from the
source to the sink, bounded below by `A⁻¹ r^{3/2}` uniformly in `r ≥ 1`. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section7

/-- Lemma 7.11 isolated provider (`lem-boltzmann-ldp-lower`, -/
theorem boltzmann_ldp_lower (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q : RightVertexMarkedBoltzmannSpace r |
          A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤
            (ldpLengthBase q.1.2.2.out.B : ℝ)} := by
  exact lemma711_of_step2 ldpLower_lemma711Step2 δ hδ hδlt

end DirectedDistances.PaperProofs.SourceResults
