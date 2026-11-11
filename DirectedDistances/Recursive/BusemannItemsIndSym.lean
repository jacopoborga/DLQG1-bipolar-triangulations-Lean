module

public import DirectedDistances.Recursive.BusemannTailReducedItems
public import DirectedDistances.Recursive.LDPFluctuationOfItems
public import DirectedDistances.Recursive.SDPHgeoConditional
public import DirectedDistances.Recursive.LeftStationaryBusemann

/-! # CONDITIONAL Busemann helpers from independence and symmetry

The remaining open hypotheses are exactly item `ind` (`hind`) and item `sym`
Item `stationary` is now proved for all indices `k`: `RightStationaryBusemann`
supplies the positive-index law and `LeftStationaryBusemann` supplies the
nonpositive-index law. These CONDITIONAL helpers are not counted as paper
SDP tail helper here asserts only the existence of `c₂`, with one witness for
both tails and absolute-tail constant `2 c₂`. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk
open DirectedDistances.Recursive.SDPExpansion
open scoped ENNReal Topology

local notation "μ" => iidCodeMeasure

section LDP

local notation "Y" => busemannLDPMeasurableVersion
local notation "f" => ldpF iidCodeMeasure busemannLDPMeasurableVersion
local notation "g" => ldpG iidCodeMeasure busemannLDPMeasurableVersion

variable
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))

include hind hsym

/-- CONDITIONAL helper for `eqn-busemann-tail-ldp`
The remaining open hypotheses are exactly item `ind` (`hind`) and item
`sym` (`hsym`) of `thm-busemann-property`
`k` by `RightStationaryBusemann` and `LeftStationaryBusemann`.
This helper is not counted as a paper result; F1/F4 remain. -/
theorem busemann_tail_ldp_of_ind_sym :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | ((Y ω 1 - Y ω 0 : ℤ) : ℝ) ≤ -x} -
        c₁ * x ^ (-(2 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₁ * x ^ (-(2 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) :=
  busemann_tail_ldp_of_reduced_items hind
    busemannLDPMeasurableVersion_left_stationary hsym

/-- CONDITIONAL helper for `eq:master-eq2`
The remaining open hypotheses are exactly item `ind` (`hind`) and item
`sym` (`hsym`) of `thm-busemann-property`
`k` by `RightStationaryBusemann` and `LeftStationaryBusemann`.
This helper is not counted as a paper result; F1/F4 remain. -/
theorem ldp_master_equation_of_ind_sym :
    ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
          f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
          (if y = -1 then
            (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
           else 0) :=
  ldp_master_equation_of_reduced_items hind
    busemannLDPMeasurableVersion_left_stationary hsym

/-- CONDITIONAL helper for `lem-ldp-fluctuation`
`LDPFluctuationOfItems`; it is not `lem-ldp-fluctuation` itself.
The remaining open hypotheses are exactly item `ind` (`hind`) and item
`sym` (`hsym`) of `thm-busemann-property`
`k` by `RightStationaryBusemann` and `LeftStationaryBusemann`.
This helper is not counted as a paper result; F1/F4 remain. -/
theorem ldp_fluctuation_of_ind_sym :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} :=
  ldp_fluctuation_of_items hind
    busemannLDPMeasurableVersion_left_stationary hsym

end LDP

section SDP

local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion

variable
    (hind : iIndepFun (fun k ω => SDPMasterFromLaw.increment Y k ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))

include hind hsym

/-- CONDITIONAL helper for `eqn-busemann-tail-sdp`
The remaining open hypotheses are exactly item `ind` (`hind`) and item
`sym` (`hsym`) of `thm-busemann-property`
`k` by `RightStationaryBusemann` and `LeftStationaryBusemann`.
This helper is not counted as a paper result; F1/F4 remain. The C14
statement asserts only the existence of `c₂`, with the same witness in both
tails and absolute-tail constant `2 c₂`. -/
theorem busemann_tail_sdp_of_ind_sym :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ ((Y ω 1 - Y ω 0 : ℤ) : ℝ)} -
        c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) :=
  busemann_tail_sdp_of_reduced_items hind
    busemannSDPMeasurableVersion_left_stationary hsym

/-- CONDITIONAL helper for `thm-busemann-tail` (vb)
The remaining open hypotheses are exactly item `ind` (`hind`) and item
`sym` (`hsym`) of `thm-busemann-property`
`k` by `RightStationaryBusemann` and `LeftStationaryBusemann`.
This helper is not counted as a paper result; F1/F4 remain. -/
theorem busemann_sdp_increment_mean_zero_of_ind_sym :
    ∀ k : ℤ,
      Integrable (fun ω => ((Y ω k - Y ω (k - 1) : ℤ) : ℝ)) μ ∧
        (∫ ω, ((Y ω k - Y ω (k - 1) : ℤ) : ℝ) ∂μ) = 0 :=
  busemann_sdp_increment_mean_zero_of_reduced_items hind
    busemannSDPMeasurableVersion_left_stationary hsym

/-- CONDITIONAL helper for `eq:master-eq`
The remaining open hypotheses are exactly item `ind` (`hind`) and item
`sym` (`hsym`) of `thm-busemann-property`
`k` by `RightStationaryBusemann` and `LeftStationaryBusemann`.
This helper is not counted as a paper result; F1/F4 remain. -/
theorem sdp_master_equation_of_ind_sym :
    ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1),
          g j * g (y - j)) +
          (if y = -1 then
            (∑' j : {j : ℤ // j ≤ -2},
              f j * f (x - (j : ℤ) - 1)) +
              g (-1) ^ 2 * f (x + 1) + g (x - 1)
           else 0) :=
  sdp_master_equation_of_reduced_items hind
    busemannSDPMeasurableVersion_left_stationary hsym

/-- CONDITIONAL helper for `eqn-sdp-identify-bound` and the `κ > 0`
The remaining open hypotheses are exactly item `ind` (`hind`) and item
`sym` (`hsym`) of `thm-busemann-property`
`k` by `RightStationaryBusemann` and `LeftStationaryBusemann`.
This helper is not counted as a paper result; F1/F4 remain. -/
theorem sdp_hgeo_of_ind_sym :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤
        (Measure.infinitePi (fun _ : ℕ => mu_f
          (KappaHgeoTransfer.incrementMass iidCodeMeasure
            busemannSDPMeasurableVersion))).real
          {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1} :=
  sdp_hgeo_of_items hind busemannSDPMeasurableVersion_left_stationary hsym

end SDP
end DirectedDistances.Recursive
