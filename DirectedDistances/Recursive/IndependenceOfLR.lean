module

public import DirectedDistances.Recursive.RightFrontierMeasurable
public import DirectedDistances.Recursive.LeftFrontierMeasurable
public import DirectedDistances.Recursive.IndependenceFromLR

/-! # CONDITIONAL independence from left/right Busemann independence

single premise of left/right Busemann-process independence at zero
are not counted as paper results; F1/F4 remain. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Probability

/-- CONDITIONAL LDP reduction of `item-busemann-ind`
`lem-geo-infty-ind` independence at zero in Busemann form -/
theorem busemannLDPMeasurableVersion_ind_of_hLR
    (hLR : IndepFun (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (j : ℤ)) iidCodeMeasure) :
    iIndepFun (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω)
      iidCodeMeasure :=
  busemannLDPMeasurableVersion_ind_of_LR
    busemannLDPMeasurableVersion_right_frontier
    busemannLDPMeasurableVersion_left_frontier hLR

/-- CONDITIONAL SDP reduction of `item-busemann-ind`
`lem-geo-infty-ind` independence at zero in Busemann form -/
theorem busemannSDPMeasurableVersion_ind_of_hLR
    (hLR : IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) iidCodeMeasure) :
    iIndepFun (fun k ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω)
      iidCodeMeasure :=
  busemannSDPMeasurableVersion_ind_of_LR
    busemannSDPMeasurableVersion_right_frontier
    busemannSDPMeasurableVersion_left_frontier hLR

end DirectedDistances.Recursive
