/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DirectedDistances.Paper.Section1.BoltzmannLDP
/-! The full finite Boltzmann theorem, transported directly from its accepted proof. -/
public section

namespace DLQG1.Palomar.Principal
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section7
/-- Theorem 1.11, using its full accepted source-facing proof without additional premises. -/
theorem boltzmann_distances (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < 1) :
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
                q.1.2.2.out.B.source (rightBoundaryVertex q i))} := by
  exact DirectedDistances.Paper.Section1.thm_boltzmann_ldp δ hδ hδlt
end DLQG1.Palomar.Principal
