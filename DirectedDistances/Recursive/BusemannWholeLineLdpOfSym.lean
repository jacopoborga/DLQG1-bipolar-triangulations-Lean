module

public import DirectedDistances.Recursive.BusemannWholeLineLimitLdp
public import DirectedDistances.Recursive.BusemannNegativeHalfLimitLdp

public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped Topology






theorem ldpBusemannWholeLineLaw_tendsto_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∃ (μpos μneg : ProbabilityMeasure CadlagLocalZero),
      Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μpos) ∧
      (∀ N, (ProbabilityMeasure.map μpos
        (Subtype.val : CadlagLocalZero → CadlagLocal)).map
          (finiteCutoffWindows N) =
            ldpBusemannPositiveCutoffLimit ldpIncrements_iIndep_proved hsym N) ∧
      LdpBusemannWholeLineNegativeHalfConverges μneg ∧
      (∀ N, (μneg.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) = negativeHalfLdpCutoffLimit hsym N) ∧
      Tendsto ldpBusemannWholeLineLaw atTop
        (𝓝 ((probabilityProduct μpos μneg).map wholeLineGlueZero)) := by
  obtain ⟨μpos, hpos, hpos_cut⟩ :=
    ldpBusemannWholeLinePositiveHalfLaw_tendsto_of_sym hsym
  obtain ⟨μneg, hneg, hneg_cut⟩ :=
    ldpBusemannWholeLineNegativeHalfConverges_of_sym hsym
  exact ⟨μpos, μneg, hpos, hpos_cut, hneg, hneg_cut,
    ldpBusemannWholeLineLaw_tendsto_of_halfLimits hpos hneg⟩

end DirectedDistances.Recursive
