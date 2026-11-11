module

public import DirectedDistances.Recursive.SDPRecursiveConditional
public import DirectedDistances.Recursive.LDPRecursiveConditional
public import DirectedDistances.Recursive.SDPHgeoConditional
public import DirectedDistances.Recursive.RightStationaryBusemann
public import DirectedDistances.Recursive.LeftStationaryBusemann

/-! # CONDITIONAL explicit Busemann tails with only `ind` and `sym` open

Both one-sided stationarity laws are proved (`RightStationaryBusemann`,
`LeftStationaryBusemann`), so only items `ind` and `sym` of
hypotheses. For SDP, `hgeo` is supplied by `sdp_hgeo_of_items`. The explicit SDP
and the actual `g(-1)`. These are conditional helpers, not counted as paper
results; the F1/F4 caveats remain. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk
open scoped ENNReal Topology

section SDP

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion



theorem sdp_tail_asymptotics_explicit_of_ind_sym
    (hind : iIndepFun (fun k ω => SDPMasterFromLaw.increment Y k ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    let κ : ℝ := 3 - 6 * g (-1) ^ 2 - f 0
    κ = 0 ∧
      (fun R : ℝ =>
        (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
          (Real.Gamma (1 / 3 : ℝ) * (g (-1)) ^ (2 / 3 : ℝ) /
            (Real.sqrt 3 * Real.pi)) * R ^ (-(4 / 3 : ℝ)))
        =o[atTop] (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) ∧
      (fun R : ℝ =>
        (∑' y : ℤ, if R < (y : ℝ) then g y else 0) -
          (Real.Gamma (1 / 3 : ℝ) * (g (-1)) ^ (2 / 3 : ℝ) /
            (2 * Real.sqrt 3 * Real.pi)) * R ^ (-(4 / 3 : ℝ)))
        =o[atTop] (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) :=
  sdp_tail_asymptotics_of_busemann_items_and_hgeo hind
    busemannSDPMeasurableVersion_right_stationary
    busemannSDPMeasurableVersion_left_stationary hsym
    (sdp_hgeo_of_items hind busemannSDPMeasurableVersion_left_stationary hsym)

end SDP

section LDP

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannLDPMeasurableVersion
local notation "f" => ldpF iidCodeMeasure busemannLDPMeasurableVersion
local notation "g" => ldpG iidCodeMeasure busemannLDPMeasurableVersion




theorem ldp_tail_asymptotics_explicit_of_ind_sym
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    let κ : ℝ := 3 + f 0
    ((fun R : ℝ =>
      (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) *
          (κ / 2) ^ (1 / 3 : ℝ) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ)))) ∧
    ((fun R : ℝ =>
      (∑' y : ℤ, if (y : ℝ) < -R then g y else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) *
          (κ / 2) ^ (1 / 3 : ℝ) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ)))) :=
  ldp_tail_asymptotics_of_busemann_items hind
    busemannLDPMeasurableVersion_right_stationary
    busemannLDPMeasurableVersion_left_stationary hsym

end LDP
end DirectedDistances.Recursive
