 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BoltzmannLDPLower

/-!
# Lemma 7.11 (`lem-boltzmann-ldp-lower`)

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

 
theorem boltzmann_ldp_lower (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q : RightVertexMarkedBoltzmannSpace r |
          A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤
            (ldpLengthBase q.1.2.2.out.B : ℝ)} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.boltzmann_ldp_lower δ hδ hδlt
 
 

end DirectedDistances.Paper.Section7
 
