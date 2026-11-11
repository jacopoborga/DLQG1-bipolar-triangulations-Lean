/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.Section7SdpUnconditional

/- # Isolated proof provider for Lemma 7.12 (`lem-boltzmann-sdp-lower`)

forwards to a proved helper; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

the Boltzmann law of maps with right boundary length `r` and a marked left-boundary vertex (marked-vertex convention;
source/sink convention: `x₀` source, `x_r` sink); `rightBoundarySDPEvent r c` is the event that some vertex of the
directed right boundary has SDP distance at least `c` from the source (unreachable = `+∞`). -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.KMSW DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section7
open scoped ENNReal

/-- Lemma 7.12 isolated provider (`lem-boltzmann-sdp-lower`, -/
theorem boltzmann_sdp_lower (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  exact DirectedDistances.PaperProofs.Section7.boltzmann_sdp_lower_of_ind_sym_sdpCode δ hδ

end DirectedDistances.PaperProofs.SourceResults
