module
public import Palomar.Principal.Support.BusemannIdentified
public import DirectedDistances.PaperProofs.SourceResults.BusemannPropertyTail
public section
open MeasureTheory ProbabilityTheory Filter Asymptotics
namespace DLQG1.Palomar.Principal
theorem busemann_tails :
(
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPWitness W (DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W)) ∧
    ∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure.real
        {W | ((DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W 1 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W 0 : ℤ) : ℝ) ≤ -x} -
          c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure.real
        {W | x ≤ |((DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W 0 -
          DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (-1) : ℤ) : ℝ)|} -
            2 * c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
              (fun x : ℝ => x ^ (-(2 / 3 : ℝ))))) ∧
    (
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPWitness W (DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W)) ∧
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure.real
        {W | x ≤ ((DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W 1 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W 0 : ℤ) : ℝ)} -
          c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure.real
        {W | x ≤ |((DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W 0 -
          DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (-1) : ℤ) : ℝ)|} -
            2 * c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
              (fun x : ℝ => x ^ (-(4 / 3 : ℝ))))) ∧
    ∀ k : ℤ,
      Integrable (fun W => ((DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k -
        DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1) : ℤ) : ℝ)) DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure ∧
        (∫ W, ((DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k -
          DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1) : ℤ) : ℝ) ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) = 0) := by
  simpa only
    [DLQG1.Palomar.Model.KMSW.wholePlaneIIDCodeMeasure_eq_source,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPWitness_iff_source,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPWitness_iff_source,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann_eq_source,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann_eq_source]
    using DirectedDistances.PaperProofs.SourceResults.thm_busemann_tail_provider

end DLQG1.Palomar.Principal
