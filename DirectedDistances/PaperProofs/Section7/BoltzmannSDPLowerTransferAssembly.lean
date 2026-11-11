module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPLowerConditionalAssembly
public import DirectedDistances.PaperProofs.Section7.SDPStableBoundOfIndSym
import DirectedDistances.PaperProofs.Section7.StoppedRightBoundarySDPTransfer
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic.NormNum

/-! # Transfer assembly for the Boltzmann SDP lower bound

Helpers toward Lemma 7.12 (`lem-boltzmann-sdp-lower`), -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.KMSW DirectedDistances.Probability
open scoped ENNReal Topology

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The remaining premise is the stated negative-excursion property for every -/
@[expose] def SDPWindowLimitNegativeExcursion : Prop :=
  ∀ ν : ProbabilityMeasure (J1WindowD 1 (by norm_num)),
    Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num)) atTop (𝓝 ν) →
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 < A ∧
      1 - ε ≤ (ν : Measure (J1WindowD 1 (by norm_num))).real
        {x : J1WindowD 1 (by norm_num) |
          ∃ t : J1Window 1, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
            x.path.1 t < -(A ^ (-(1 / 2 : ℝ)))}

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result. -/
theorem boltzmann_sdp_lower_of_hstable
    (hstable : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∃ kstar : ℕ,
      ∀ k : ℕ, kstar ≤ k →
        1 - δ / 2 ≤ iidCodeMeasure.real
          {ω | ∃ r : ℕ, r ≤ k ∧
            (busemannSDPMeasurableVersion ω r : ℝ) ≤
              -(A ^ (-(1 / 2 : ℝ))) * (k : ℝ) ^ (3 / 4 : ℝ)}) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  exact boltzmann_sdp_lower_conditional hstable stoppedRightBoundaryTransfer

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The remaining premises are `hind_sdp`, `hsym_sdp`, and -/
theorem boltzmann_sdp_lower_of_sdp_window_limit_negative_excursion
    (hind_sdp : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment
        busemannSDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym_sdp : iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    (hnegative : SDPWindowLimitNegativeExcursion) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        (rightBoundarySDPEvent r
          (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))) := by
  exact boltzmann_sdp_lower_conditional
    (sdp_hstable_of_window_negative_limit hind_sdp hsym_sdp hnegative)
    stoppedRightBoundaryTransfer

end DirectedDistances.PaperProofs.Section7
