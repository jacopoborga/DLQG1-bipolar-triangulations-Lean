module

public import Mathlib.Probability.Independence.Basic
public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.Recursive.BusemannRightTruncationFormula
public import DirectedDistances.Recursive.IndependenceOfLR
import DirectedDistances.Recursive.HattedSidePrimedIndep

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Paper.Section4 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PlanarMap

local notation "ThinCode" => (ℕ → Option FiniteThinMap)
local notation "Tldp" =>
  thinSideCode XDP.ldp renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The left Busemann profile is measurable with respect to the left thin code and -/
@[expose] def LeftBusemannLdpLocality : Prop :=
  ∃ FL : ThinCode × (ℕ → Fin 3) → ℕ → ℤ, Measurable FL ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      (fun j : ℕ => busemannLDPMeasurableVersion ω (-(j : ℤ))) =
        FL (Tldp .left (integrateCodes (hatLawCodes ω)), hatLawPrimedCodes ω)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Both Busemann profiles are zero at their shared boundary coordinate. Source: -/
theorem busemannLDPProfiles_zero_agree (ω : ℕ → Fin 3) :
    (fun j : ℕ => busemannLDPMeasurableVersion ω (-(j : ℤ))) 0 = 0 ∧
      (fun j : ℕ => busemannLDPMeasurableVersion ω (j : ℤ)) 0 = 0 := by
  constructor <;> simp [busemannLDPMeasurableVersion_zero]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Left locality and the proved right locality imply independence of the two -/
theorem hLR_ldp_of_leftLocality (hL : LeftBusemannLdpLocality) :
    IndepFun (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (j : ℤ)) iidCodeMeasure := by
  obtain ⟨FL, hFL, hL⟩ := hL
  obtain ⟨FR, hFR, hR⟩ := rightBusemannLdpLocality_proved
  have hCodes : IndepFun
      (fun ω => FL
        (Tldp .left (integrateCodes (hatLawCodes ω)), hatLawPrimedCodes ω))
      (fun ω => FR (Tldp .right (integrateCodes (hatLawCodes ω))))
      iidCodeMeasure := by
    change IndepFun
      (FL ∘ fun ω =>
        (Tldp .left (integrateCodes (hatLawCodes ω)), hatLawPrimedCodes ω))
      (FR ∘ fun ω => Tldp .right (integrateCodes (hatLawCodes ω))) iidCodeMeasure
    exact (hattedLeftPrimed_indep_right XDP.ldp).comp hFL hFR
  have hLeft :
      (fun ω => FL
        (Tldp .left (integrateCodes (hatLawCodes ω)), hatLawPrimedCodes ω)) =ᵐ[
          iidCodeMeasure]
        (fun ω j => busemannLDPMeasurableVersion ω (-(j : ℤ))) := by
    filter_upwards [hL] with ω hω
    exact hω.symm
  have hRight :
      (fun ω => FR (Tldp .right (integrateCodes (hatLawCodes ω)))) =ᵐ[
          iidCodeMeasure]
        (fun ω j => busemannLDPMeasurableVersion ω (j : ℤ)) := by
    filter_upwards [hR] with ω hω
    exact hω.symm
  exact hCodes.congr hLeft hRight

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The left locality proposition implies independent LDP increments. Source: -/
theorem ldpIncrements_iIndep_of_leftLocality
    (hL : LeftBusemannLdpLocality) :
    iIndepFun (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω)
      iidCodeMeasure :=
  busemannLDPMeasurableVersion_ind_of_hLR (hLR_ldp_of_leftLocality hL)

end DirectedDistances.Recursive
