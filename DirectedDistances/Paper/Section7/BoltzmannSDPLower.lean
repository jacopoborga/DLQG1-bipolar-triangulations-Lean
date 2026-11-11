 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BoltzmannSDPLower

/-!
# Lemma 7.12 (`lem-boltzmann-sdp-lower`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/











public section
namespace DirectedDistances.Paper.Section7

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.KMSW DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section7
open scoped ENNReal

 
theorem boltzmann_sdp_lower (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.boltzmann_sdp_lower δ hδ
 
 

end DirectedDistances.Paper.Section7
 
