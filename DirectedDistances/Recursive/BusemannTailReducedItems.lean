module

public import DirectedDistances.Recursive.RightStationaryBusemann
public import DirectedDistances.Recursive.BusemannTailLDPConditional
public import DirectedDistances.Recursive.BusemannTailSDPConditional
public import DirectedDistances.Recursive.BusemannMeanZeroSDPConditional

/-! # CONDITIONAL Busemann helpers with positive-index stationarity discharged

The remaining open item hypotheses are independence (`hind`), stationarity
for indices `k ≤ 0` (`hstatL`), and symmetry (`hsym`) from
for `k ≥ 1` is proved in `RightStationaryBusemann` and supplied here.
These CONDITIONAL helpers are not counted as paper results. The F1/F4
source-identification caveats remain. The inherited C14 discrepancy for the
explicit SDP tail constant is unresolved; the tail statement here only
asserts existence of a shared positive constant. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk
open scoped ENNReal Topology

local notation "μ" => iidCodeMeasure

section LDP

local notation "Y" => busemannLDPMeasurableVersion
local notation "f" => ldpF iidCodeMeasure busemannLDPMeasurableVersion
local notation "g" => ldpG iidCodeMeasure busemannLDPMeasurableVersion

variable
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement Y k) =
      iidCodeMeasure.map (ldpIncrement Y 0))
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))

include hind hstatL hsym

/-- CONDITIONAL helper for `eqn-busemann-tail-ldp`
item `ind` (`hind`), stationarity for `k ≤ 0` (`hstatL`), and item `sym`
(`hsym`). Stationarity for `k ≥ 1` is proved in `RightStationaryBusemann`.
One positive constant works for both weak-endpoint tails. This is not
counted as a paper result; F1/F4 remain. -/
theorem busemann_tail_ldp_of_reduced_items :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | ((Y ω 1 - Y ω 0 : ℤ) : ℝ) ≤ -x} -
        c₁ * x ^ (-(2 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₁ * x ^ (-(2 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) :=
  busemann_tail_ldp_of_items hind
    busemannLDPMeasurableVersion_right_stationary hstatL hsym

/-- CONDITIONAL helper for `eq:master-eq2`
are item `ind` (`hind`), stationarity for `k ≤ 0` (`hstatL`), and item
`sym` (`hsym`). Stationarity for `k ≥ 1` is proved in
`RightStationaryBusemann`. This is not counted as a paper result; F1/F4
remain. -/
theorem ldp_master_equation_of_reduced_items :
    ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
          f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
          (if y = -1 then
            (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
           else 0) :=
  ldp_master_equation_of_busemann_items hind
    busemannLDPMeasurableVersion_right_stationary hstatL hsym

end LDP

section SDP

local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion

variable
    (hind : iIndepFun (fun k ω => SDPMasterFromLaw.increment Y k ω) μ)
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (SDPMasterFromLaw.increment Y k) =
      iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0))
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))

include hind hstatL hsym

/-- CONDITIONAL helper for `eqn-busemann-tail-sdp`
item `ind` (`hind`), stationarity for `k ≤ 0` (`hstatL`), and item `sym`
(`hsym`). Stationarity for `k ≥ 1` is proved in `RightStationaryBusemann`.
One positive constant works for both weak-endpoint tails, with the absolute
tail constant twice the right tail constant. The inherited C14 explicit
constant discrepancy remains. This is not counted as a paper result;
F1/F4 remain. -/
theorem busemann_tail_sdp_of_reduced_items :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ ((Y ω 1 - Y ω 0 : ℤ) : ℝ)} -
        c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) :=
  busemann_tail_sdp_of_items hind
    busemannSDPMeasurableVersion_right_stationary hstatL hsym

/-- CONDITIONAL integrability and zero expectation helper for
item `ind` (`hind`), stationarity for `k ≤ 0` (`hstatL`), and item `sym`
(`hsym`). Stationarity for `k ≥ 1` is proved in `RightStationaryBusemann`.
This is not counted as a paper result; F1/F4 remain. -/
theorem busemann_sdp_increment_mean_zero_of_reduced_items :
    ∀ k : ℤ,
      Integrable (fun ω => ((Y ω k - Y ω (k - 1) : ℤ) : ℝ)) μ ∧
        (∫ ω, ((Y ω k - Y ω (k - 1) : ℤ) : ℝ) ∂μ) = 0 :=
  busemann_sdp_increment_mean_zero_of_items hind
    busemannSDPMeasurableVersion_right_stationary hstatL hsym

/-- CONDITIONAL helper for `eq:master-eq`
are item `ind` (`hind`), stationarity for `k ≤ 0` (`hstatL`), and item
`sym` (`hsym`). Stationarity for `k ≥ 1` is proved in
`RightStationaryBusemann`. This is not counted as a paper result; F1/F4
remain. -/
theorem sdp_master_equation_of_reduced_items :
    ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1),
          g j * g (y - j)) +
          (if y = -1 then
            (∑' j : {j : ℤ // j ≤ -2},
              f j * f (x - (j : ℤ) - 1)) +
              g (-1) ^ 2 * f (x + 1) + g (x - 1)
           else 0) :=
  sdp_master_equation_of_busemann_items hind
    busemannSDPMeasurableVersion_right_stationary hstatL hsym

end SDP
end DirectedDistances.Recursive
