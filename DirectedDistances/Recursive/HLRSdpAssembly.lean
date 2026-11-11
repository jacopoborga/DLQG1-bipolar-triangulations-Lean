module

public import DirectedDistances.Recursive.BusemannRightSideLocality
public import DirectedDistances.Recursive.HattedSidePrimedIndep
public import DirectedDistances.Recursive.IndependenceOfLR

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4

local notation "ThinCode" => (ℕ → Option FiniteThinMap)
local notation "Tsdp" =>
  thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The left SDP Busemann process is a measurable function of the left thin code and -/
@[expose] def LeftBusemannSdpLocality : Prop :=
  ∃ FL : ThinCode × (ℕ → Fin 3) → ℕ → ℤ, Measurable FL ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      (fun j : ℕ => busemannSDPMeasurableVersion ω (-(j : ℤ))) =
        FL (Tsdp .left (integrateCodes (hatLawCodes ω)), hatLawPrimedCodes ω)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The negative and nonnegative SDP Busemann processes are independent when the -/
theorem hLR_sdp_of_localities (hR : RightBusemannSdpLocality)
    (hL : LeftBusemannSdpLocality) :
    IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) iidCodeMeasure := by
  obtain ⟨FR, hFR, hRae⟩ := hR
  obtain ⟨FL, hFL, hLae⟩ := hL
  have hsep :
      IndepFun
        (fun ω => FL
          (Tsdp .left (integrateCodes (hatLawCodes ω)), hatLawPrimedCodes ω))
        (fun ω => FR (Tsdp .right (integrateCodes (hatLawCodes ω))))
        iidCodeMeasure := by
    simpa only [Function.comp_def, hattedIntegratedPath] using
      (hattedLeftPrimed_indep_right XDP.sdp).comp hFL hFR
  have hLfun :
      (fun ω => FL
        (Tsdp .left (integrateCodes (hatLawCodes ω)), hatLawPrimedCodes ω)) =ᵐ[iidCodeMeasure]
        (fun ω j => busemannSDPMeasurableVersion ω (-(j : ℤ))) := by
    filter_upwards [hLae] with ω hω
    exact hω.symm
  have hRfun :
      (fun ω => FR (Tsdp .right (integrateCodes (hatLawCodes ω)))) =ᵐ[iidCodeMeasure]
        (fun ω j => busemannSDPMeasurableVersion ω (j : ℤ)) := by
    filter_upwards [hRae] with ω hω
    exact hω.symm
  exact hsep.congr hLfun hRfun

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The SDP increments are independent under the two locality propositions. -/
theorem sdpIncrements_iIndep_of_localities (hR : RightBusemannSdpLocality)
    (hL : LeftBusemannSdpLocality) :
    iIndepFun
      (fun k ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω)
      iidCodeMeasure :=
  busemannSDPMeasurableVersion_ind_of_hLR (hLR_sdp_of_localities hR hL)

end DirectedDistances.Recursive
