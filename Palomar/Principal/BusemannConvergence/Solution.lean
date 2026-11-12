module
public import Palomar.Principal.Support.BusemannIdentified
public import Palomar.Principal.Support.BusemannPaths
@[expose] public section
namespace DLQG1.Palomar.Model.RandomWalk
theorem wholePlaneIIDCodeMeasure_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure wholePlaneIIDCodeMeasure := by
  change MeasureTheory.IsProbabilityMeasure DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure
  infer_instance
attribute [instance] wholePlaneIIDCodeMeasure_isProbabilityMeasure
end DLQG1.Palomar.Model.RandomWalk
namespace DLQG1.Palomar.Model.PaperProofs.Section1
open MeasureTheory Filter
open DLQG1.Palomar.Model.Probability
open DLQG1.Palomar.Model.PaperProofs.Section7
open scoped Topology
noncomputable def identifiedLDPScalingPath (n : ℕ) (W : ℤ → Fin 3) : WholeLineCadlag :=
  ldpScalingPath (identifiedLDPBusemann W) n
noncomputable def identifiedSDPScalingPath (n : ℕ) (W : ℤ → Fin 3) : WholeLineCadlag :=
  sdpScalingPath (identifiedSDPBusemann W) n
theorem identifiedLDPScalingPath_eq_source (n : ℕ) :
    identifiedLDPScalingPath n = sourceLDPScalingPath n := by
  funext W
  simp only [identifiedLDPScalingPath, sourceLDPScalingPath, identifiedLDPBusemann_eq_source]
theorem identifiedSDPScalingPath_eq_source (n : ℕ) :
    identifiedSDPScalingPath n = sourceSDPScalingPath n := by
  funext W
  simp only [identifiedSDPScalingPath, sourceSDPScalingPath, identifiedSDPBusemann_eq_source]
theorem aemeasurable_identifiedLDPScalingPath (n : ℕ) :
    AEMeasurable (identifiedLDPScalingPath n)
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure := by
  rw [identifiedLDPScalingPath_eq_source]
  exact aemeasurable_sourceLDPScalingPath n
theorem aemeasurable_identifiedSDPScalingPath (n : ℕ) :
    AEMeasurable (identifiedSDPScalingPath n)
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure := by
  rw [identifiedSDPScalingPath_eq_source]
  exact aemeasurable_sourceSDPScalingPath n
noncomputable def identifiedLDPScalingLaw (n : ℕ) : ProbabilityMeasure WholeLineCadlag :=
  ⟨DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure.map (identifiedLDPScalingPath n),
    (Measure.isProbabilityMeasure_map_iff (aemeasurable_identifiedLDPScalingPath n)).2 inferInstance⟩
noncomputable def identifiedSDPScalingLaw (n : ℕ) : ProbabilityMeasure WholeLineCadlag :=
  ⟨DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure.map (identifiedSDPScalingPath n),
    (Measure.isProbabilityMeasure_map_iff (aemeasurable_identifiedSDPScalingPath n)).2 inferInstance⟩
theorem identifiedLDPScalingLaw_eq_source (n : ℕ) :
    identifiedLDPScalingLaw n = sourceLDPScalingLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ _ = Measure.map _ _
  rw [identifiedLDPScalingPath_eq_source]
  rfl
theorem identifiedSDPScalingLaw_eq_source (n : ℕ) :
    identifiedSDPScalingLaw n = sourceSDPScalingLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ _ = Measure.map _ _
  rw [identifiedSDPScalingPath_eq_source]
  rfl
end DLQG1.Palomar.Model.PaperProofs.Section1
namespace DLQG1.Palomar.Principal
open MeasureTheory Filter
open DLQG1.Palomar.Model.KMSW DLQG1.Palomar.Model.RandomWalk
open DLQG1.Palomar.Model.Probability
open DLQG1.Palomar.Model.PaperProofs.Section1 DLQG1.Palomar.Model.PaperProofs.Section7
open DirectedDistances.KMSW (BoundaryHitWitnesses kmswLLCreatedEdge boundaryHitTime)
open scoped Topology
theorem busemann_convergence :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W)) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) (identifiedSDPBusemann W)) ∧
    (∃ (a b : ℝ) (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
      LdpStableHalfLaw a μL ∧ SymmetricStableProcessLaw (2 / 3) a νL ∧
      SdpStableHalfLaw b μS ∧ SymmetricStableProcessLaw (4 / 3) b νS ∧
      Tendsto identifiedLDPScalingLaw atTop
        (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
      Tendsto identifiedSDPScalingLaw atTop
        (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero)))  := by
  refine ⟨?_, ?_, ?_⟩
  · change ∀ᵐ W ∂wholePlaneIIDCodeMeasure, identifiedLDPWitness W (identifiedLDPBusemann W)
    filter_upwards [DirectedDistances.Paper.Section1.thm_busemann_conv.1] with W hW
    apply (identifiedLDPWitness_iff_source W _).mpr
    simpa only [identifiedLDPBusemann_eq_source] using hW
  · change ∀ᵐ W ∂wholePlaneIIDCodeMeasure, identifiedSDPWitness W (identifiedSDPBusemann W)
    filter_upwards [DirectedDistances.Paper.Section1.thm_busemann_conv.2.1] with W hW
    apply (identifiedSDPWitness_iff_source W _).mpr
    simpa only [identifiedSDPBusemann_eq_source] using hW
  · have hL : identifiedLDPScalingLaw = sourceLDPScalingLaw :=
      funext identifiedLDPScalingLaw_eq_source
    have hS : identifiedSDPScalingLaw = sourceSDPScalingLaw :=
      funext identifiedSDPScalingLaw_eq_source
    simpa only [hL, hS] using full_functional_scaling_source_transport
end DLQG1.Palomar.Principal
