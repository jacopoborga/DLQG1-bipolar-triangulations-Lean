/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.Section7LdpUnconditional

/- # Isolated proof provider for Lemma 7.10 (`lem-boltzmann-ldp-upper`)

forwards to a proved helper; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

the Boltzmann law of maps with right boundary length `r` and a marked left-boundary vertex (marked-vertex convention;
source/sink convention: `x₀` source, `x_r` sink); `ldpLengthBase` of the underlying map is the maximal length of a
simple directed path from the source to the sink, bounded by `A r^{3/2}` uniformly in `r ≥ 1`. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section7

/-- Lemma 7.10 isolated provider (`lem-boltzmann-ldp-upper`, -/
theorem boltzmann_ldp_upper (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q : RightVertexMarkedBoltzmannSpace r |
          (ldpLengthBase q.1.2.2.out.B : ℝ) ≤
            A * (r : ℝ) ^ (3 / 2 : ℝ)} := by
  exact DirectedDistances.PaperProofs.Section7.boltzmann_ldp_upper_conditional_ldpCode δ hδ hδlt

end DirectedDistances.PaperProofs.SourceResults
