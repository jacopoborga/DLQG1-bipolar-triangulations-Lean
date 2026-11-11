module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPLowerIndSym
import DirectedDistances.Recursive.BusemannSdpUnconditional
import DirectedDistances.Recursive.BusemannWindowLimitZeroExcursionGerm

/- # Code-level SDP consequences for Section 7

Helpers toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not paper results.

This module specializes every public theorem in the three Section 7 SDP modules with
`hind_sdp` or `hsym_sdp` premises: `BoltzmannSDPLowerIndSym`,
`SDPStableBoundOfIndSym`, and `BoltzmannSDPLowerTransferAssembly`.
The proved code-level increment independence and symmetry also supply the existing
negative-excursion producer, which in turn supplies the stable lower-bound premise.
OPEN remaining premises: none. These are code-level helper conclusions; independent -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.KMSW DirectedDistances.Probability
open scoped ENNReal

/-- Helper (code level, SDP) toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Discharges the independence and symmetry premises of `boltzmann_sdp_lower_of_ind_sym`. -/
theorem boltzmann_sdp_lower_of_ind_sym_sdpCode :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  exact boltzmann_sdp_lower_of_ind_sym
    sdpIncrements_iIndep_sdpCode hsymSdp_sdpCode

/-- Helper (code level, SDP) toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Discharges independence, symmetry, and the negative-excursion premise using its producer. -/
theorem sdp_hstable_of_window_negative_limit_sdpCode :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∃ kstar : ℕ,
      ∀ k : ℕ, kstar ≤ k →
        1 - δ / 2 ≤ iidCodeMeasure.real
          {ω | ∃ r : ℕ, r ≤ k ∧
            (busemannSDPMeasurableVersion ω r : ℝ) ≤
              -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  exact sdp_hstable_of_window_negative_limit
    sdpIncrements_iIndep_sdpCode hsymSdp_sdpCode
    (sdp_window_limit_negative_excursion_producer
      sdpIncrements_iIndep_sdpCode hsymSdp_sdpCode)

/-- Helper (code level, SDP) toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Discharges the stable lower-bound premise of `boltzmann_sdp_lower_of_hstable`. -/
theorem boltzmann_sdp_lower_of_hstable_sdpCode :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  exact boltzmann_sdp_lower_of_hstable sdp_hstable_of_window_negative_limit_sdpCode

/-- Helper (code level, SDP) toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Discharges independence, symmetry, and `SDPWindowLimitNegativeExcursion`. -/
theorem boltzmann_sdp_lower_of_sdp_window_limit_negative_excursion_sdpCode :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  exact boltzmann_sdp_lower_of_sdp_window_limit_negative_excursion
    sdpIncrements_iIndep_sdpCode hsymSdp_sdpCode
    (sdp_window_limit_negative_excursion_producer
      sdpIncrements_iIndep_sdpCode hsymSdp_sdpCode)

end DirectedDistances.PaperProofs.Section7
