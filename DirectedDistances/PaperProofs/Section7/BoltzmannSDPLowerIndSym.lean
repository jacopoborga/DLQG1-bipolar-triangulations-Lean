module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPLowerTransferAssembly
import DirectedDistances.Recursive.BusemannWindowLimitZeroExcursionGerm

/-! # Symmetric independent increments for the Boltzmann SDP lower bound -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.KMSW DirectedDistances.Probability
open scoped ENNReal

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The remaining premises are exactly `hind_sdp` (Theorem 1.7(i), SDP) and
`hsym_sdp` (Theorem 1.7(iv) at index 0) -/
theorem boltzmann_sdp_lower_of_ind_sym
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment
        busemannSDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  exact boltzmann_sdp_lower_of_sdp_window_limit_negative_excursion
    hind_sdp hsym_sdp
    (sdp_window_limit_negative_excursion_producer hind_sdp hsym_sdp)

end DirectedDistances.PaperProofs.Section7
