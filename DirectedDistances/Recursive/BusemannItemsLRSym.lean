module

public import DirectedDistances.Recursive.BusemannItemsIndSym
public import DirectedDistances.Recursive.BusemannTailExplicitIndSym
public import DirectedDistances.Recursive.IndependenceOfLR

/-! Supporting lemmas for paper labels `lem-geo-infty`, `lem-geo-infty-ind`, `lem-ldp-fluctuation`, `prop-thin-ind`, `thm-busemann`, `thm-busemann-tail` (see CORRESPONDENCE.md). -/

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

/-- CONDITIONAL helper for `eqn-busemann-tail-ldp`
`hLR`, the `lem-geo-infty-ind` independence at zero in Busemann form
Item ind is derived from `hLR` by `IndependenceOfLR`. This helper is not counted
as a paper result; F1/F4 remain. -/
theorem busemann_tail_ldp_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (j : ℤ)) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | ((Y ω 1 - Y ω 0 : ℤ) : ℝ) ≤ -x} -
        c₁ * x ^ (-(2 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₁ * x ^ (-(2 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) :=
  busemann_tail_ldp_of_ind_sym (busemannLDPMeasurableVersion_ind_of_hLR hLR) hsym

/-- CONDITIONAL helper for `eq:master-eq2`
`hLR`, the `lem-geo-infty-ind` independence at zero in Busemann form
Item ind is derived from `hLR` by `IndependenceOfLR`. This helper is not counted
as a paper result; F1/F4 remain. -/
theorem ldp_master_equation_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (j : ℤ)) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
          f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
          (if y = -1 then
            (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
           else 0) :=
  ldp_master_equation_of_ind_sym (busemannLDPMeasurableVersion_ind_of_hLR hLR) hsym

/-- CONDITIONAL helper for `lem-ldp-fluctuation`
`LDPFluctuationOfItems`; it is not `lem-ldp-fluctuation` itself. The remaining
hypotheses are exactly `hLR`, the `lem-geo-infty-ind` independence at zero in
`prop-thin-ind`, which is not formalized), and `hsym`, item sym
`IndependenceOfLR`. This helper is not counted as a paper result; F1/F4 remain. -/
theorem ldp_fluctuation_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (j : ℤ)) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} :=
  ldp_fluctuation_of_ind_sym (busemannLDPMeasurableVersion_ind_of_hLR hLR) hsym

end LDP

section SDP

local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion






theorem busemann_tail_sdp_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ ((Y ω 1 - Y ω 0 : ℤ) : ℝ)} -
        c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) :=
  busemann_tail_sdp_of_ind_sym (busemannSDPMeasurableVersion_ind_of_hLR hLR) hsym

/-- CONDITIONAL helper for `thm-busemann-tail` (vb)
remaining hypotheses are exactly `hLR`, the `lem-geo-infty-ind` independence at
`prop-thin-ind`, which is not formalized), and `hsym`, item sym
`IndependenceOfLR`. This helper is not counted as a paper result; F1/F4 remain. -/
theorem busemann_sdp_increment_mean_zero_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    ∀ k : ℤ,
      Integrable (fun ω => ((Y ω k - Y ω (k - 1) : ℤ) : ℝ)) iidCodeMeasure ∧
        (∫ ω, ((Y ω k - Y ω (k - 1) : ℤ) : ℝ) ∂iidCodeMeasure) = 0 :=
  busemann_sdp_increment_mean_zero_of_ind_sym
    (busemannSDPMeasurableVersion_ind_of_hLR hLR) hsym

/-- CONDITIONAL helper for `eq:master-eq`
`hLR`, the `lem-geo-infty-ind` independence at zero in Busemann form
Item ind is derived from `hLR` by `IndependenceOfLR`. This helper is not counted
as a paper result; F1/F4 remain. -/
theorem sdp_master_equation_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1),
          g j * g (y - j)) +
          (if y = -1 then
            (∑' j : {j : ℤ // j ≤ -2},
              f j * f (x - (j : ℤ) - 1)) +
              g (-1) ^ 2 * f (x + 1) + g (x - 1)
           else 0) :=
  sdp_master_equation_of_ind_sym (busemannSDPMeasurableVersion_ind_of_hLR hLR) hsym

/-- CONDITIONAL helper for `eqn-sdp-identify-bound` and the `κ > 0` exclusion
`hLR`, the `lem-geo-infty-ind` independence at zero in Busemann form
Item ind is derived from `hLR` by `IndependenceOfLR`. This helper is not counted
as a paper result; F1/F4 remain. -/
theorem sdp_hgeo_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤
        (Measure.infinitePi (fun _ : ℕ => mu_f
          (KappaHgeoTransfer.incrementMass iidCodeMeasure
            busemannSDPMeasurableVersion))).real
          {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1} :=
  sdp_hgeo_of_ind_sym (busemannSDPMeasurableVersion_ind_of_hLR hLR) hsym

end SDP

section ExplicitTails

local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion

/-- hypotheses are exactly `hLR`, the `lem-geo-infty-ind` independence at zero in
`prop-thin-ind`, which is not formalized), and `hsym`, item sym
`IndependenceOfLR`. This helper is not counted as a paper result; F1/F4 remain. -/
theorem sdp_tail_asymptotics_explicit_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) μ)
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
  sdp_tail_asymptotics_explicit_of_ind_sym
    (busemannSDPMeasurableVersion_ind_of_hLR hLR) hsym

end ExplicitTails

section ExplicitLDP

local notation "Y" => busemannLDPMeasurableVersion
local notation "f" => ldpF iidCodeMeasure busemannLDPMeasurableVersion
local notation "g" => ldpG iidCodeMeasure busemannLDPMeasurableVersion

/-- CONDITIONAL helper: explicit LDP strict-tail asymptotics
`hLR`, the `lem-geo-infty-ind` independence at zero in Busemann form
Item ind is derived from `hLR` by `IndependenceOfLR`. This helper is not counted
as a paper result; F1/F4 remain. -/
theorem ldp_tail_asymptotics_explicit_of_LR_sym
    (hLR : IndepFun (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (j : ℤ)) μ)
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
  ldp_tail_asymptotics_explicit_of_ind_sym
    (busemannLDPMeasurableVersion_ind_of_hLR hLR) hsym

end ExplicitLDP
end DirectedDistances.Recursive
