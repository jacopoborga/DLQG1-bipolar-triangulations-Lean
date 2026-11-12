module
public import Palomar.Principal.Support.BusemannIdentified
public import DirectedDistances.Paper.Section1.BusemannProperty
public section
open MeasureTheory ProbabilityTheory Filter Asymptotics
namespace DLQG1.Palomar.Principal
theorem busemann_increments :
(
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPWitness W (DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W)) ∧
    iIndepFun (fun k W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W 1 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (1 - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W 0 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (0 - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1) ≤ -1) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1) - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k)
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure)) ∧
    (
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPWitness W (DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W)) ∧
    iIndepFun (fun k W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W 1 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (1 - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W 0 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (0 - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      -1 ≤ DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1)) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1) - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k)
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure)) := by
  simpa only
    [DLQG1.Palomar.Model.KMSW.wholePlaneIIDCodeMeasure_eq_source,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPWitness_iff_source,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPWitness_iff_source,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann_eq_source,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann_eq_source]
    using DirectedDistances.Paper.Section1.thm_busemann_property
end DLQG1.Palomar.Principal
