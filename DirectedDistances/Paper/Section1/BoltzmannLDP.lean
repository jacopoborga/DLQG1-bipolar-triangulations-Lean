 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.ThmBoltzmannLDP

/-!
# Theorem 1.11 (`thm-boltzmann-ldp`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/





















public section
namespace DirectedDistances.Paper.Section1

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section7

 
theorem thm_boltzmann_ldp (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q : RightVertexMarkedBoltzmannSpace r |
          (A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (ldpLengthBase q.1.2.2.out.B : ℝ) ∧
            (ldpLengthBase q.1.2.2.out.B : ℝ) ≤ A * (r : ℝ) ^ (3 / 2 : ℝ)) ∧
          ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
              ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ)) ∧
          ∃ i : Fin (r + 1),
            ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)) ≤
              ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
                q.1.2.2.out.B.source (rightBoundaryVertex q i))} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.thm_boltzmann_ldp_provider δ hδ hδlt
 
 

end DirectedDistances.Paper.Section1
 
