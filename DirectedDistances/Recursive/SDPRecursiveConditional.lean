module

public import DirectedDistances.Recursive.SDPMasterFromLaw
public import DirectedDistances.Recursive.SDPSplitting
public import DirectedDistances.Recursive.MeasurableVersionPos
public import DirectedDistances.Recursive.KappaExclusionAssembly
public import DirectedDistances.Recursive.SDPTailFromExpansions

/-! Supporting lemmas for paper labels `prop:SDP-recursive-equation`, `thm-busemann`, `thm-busemann-tail` (see CORRESPONDENCE.md). -/

















public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk
open DirectedDistances.Recursive.SDPExpansion
open scoped ENNReal Topology

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion

/-- The `hf` side fact for the CONDITIONAL SDP helpers: nonnegative atoms of -/
theorem busemann_sdpF_nonneg : ∀ x : ℤ, 0 ≤ f x :=
  SDPMasterFromLaw.sdpF_nonneg μ Y

/-- The `hfs` side fact for the CONDITIONAL SDP helpers: the left increment -/
theorem busemann_sdpF_hasSum_one : HasSum f (1 : ℝ) :=
  SDPMasterFromLaw.sdpF_hasSum_one μ Y measurable_busemannSDPMeasurableVersion

/-- The `hg` side fact for the CONDITIONAL SDP helpers: nonnegative atoms of -/
theorem busemann_sdpG_nonneg : ∀ y : ℤ, 0 ≤ g y :=
  SDPMasterFromLaw.sdpG_nonneg μ Y

/-- The `hgs` side fact for the CONDITIONAL SDP helpers: the right increment -/
theorem busemann_sdpG_hasSum_one : HasSum g (1 : ℝ) :=
  SDPMasterFromLaw.sdpG_hasSum_one μ Y measurable_busemannSDPMeasurableVersion

/-- CONDITIONAL `hsymm` side fact. Item `sym` is an open paper obligation -/
theorem busemann_sdpF_symm
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    ∀ x : ℤ, f (-x) = f x :=
  SDPMasterFromLaw.sdpF_symm μ Y measurable_busemannSDPMeasurableVersion hsym

private theorem busemann_sdp_increment_ge :
    ∀ᵐ ω ∂μ, ∀ k ≥ 1, -1 ≤ SDPMasterFromLaw.increment Y k ω := by
  simpa only [SDPMasterFromLaw.increment] using
    iidCodes_ae_busemannSDPMeasurableVersion_item_pos

/-- The `hgsupp` side fact for the CONDITIONAL SDP helpers follows from the
This is a helper, not a paper result. -/
theorem busemann_sdpG_zero_below : ∀ y : ℤ, y < -1 → g y = 0 := by
  intro y hy
  exact SDPMasterFromLaw.sdpG_zero_below μ Y busemann_sdp_increment_ge hy

private theorem busemann_sdp_splitting_real (x y : ℤ) :
    iidCodeMeasure.real {ω | (Y ω (-1), Y ω 1) = (x, y)} =
      (1 / 3 : ℝ) * iidCodeMeasure.real {ω |
        (Y ω (-2) - min (Y ω (-1)) 1, -min (Y ω (-1)) 1) = (x, y)} +
      (1 / 3 : ℝ) * iidCodeMeasure.real {ω | (-Y ω 1 - 1, -1) = (x, y)} +
      (1 / 3 : ℝ) * iidCodeMeasure.real {ω |
        (Y ω (-1) - min 0 (Y ω 2 + 1), Y ω 2 - min 0 (Y ω 2 + 1)) = (x, y)} := by
  have hfinite (s : Set (ℕ → Fin 3)) : (3 : ENNReal)⁻¹ * μ s ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ s)
  have h := congrArg ENNReal.toReal
    (iidCodeMeasure_busemannSDPMeasurableVersion_splitting_self x y)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfinite _, hfinite _⟩) (hfinite _),
    ENNReal.toReal_add (hfinite _) (hfinite _)] at h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    one_div, Measure.real] using h

section Conditional

variable
    (hind : iIndepFun (fun k ω => SDPMasterFromLaw.increment Y k ω) μ)
    (hstatR : ∀ k ≥ 1, iidCodeMeasure.map (SDPMasterFromLaw.increment Y k) =
      iidCodeMeasure.map (SDPMasterFromLaw.increment Y 1))
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (SDPMasterFromLaw.increment Y k) =
      iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0))
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))

include hind hstatR hstatL hsym







theorem sdp_master_equation_of_busemann_items :
    ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1),
          g j * g (y - j)) +
          (if y = -1 then
            (∑' j : {j : ℤ // j ≤ -2},
              f j * f (x - (j : ℤ) - 1)) +
              g (-1) ^ 2 * f (x + 1) + g (x - 1)
           else 0) :=
  SDPMasterFromLaw.sdp_master_equation_from_law μ Y
    measurable_busemannSDPMeasurableVersion busemannSDPMeasurableVersion_zero
    hind hstatR hstatL hsym busemann_sdp_increment_ge busemann_sdp_splitting_real

/-- CONDITIONAL κ exclusion for the SDP laws of the measurable representative.
The open items `ind`, `stationary` (two laws), and `sym` are explicit
hypotheses. The exact additional `hgeo` premise is the canonical iid-product
linear-bound input of `KappaExclusionAssembly`; its geometric proof is not
included here. This is not a paper result, `prop:SDP-recursive-equation`, or
`thm-busemann-tail`; F1/F4 caveats remain in force. -/
theorem sdp_kappa_zero_of_busemann_items_and_hgeo
    (hgeo : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤ ((Measure.infinitePi (fun _ : ℕ => mu_f f)).real
        {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1})) :
    let κ : ℝ := 3 - 6 * g (-1) ^ 2 - f 0
    κ = 0 := by
  exact SDPExpansion.sdp_kappa_eq_zero_of_linear_bound
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsym) busemann_sdpG_zero_below
    (sdp_master_equation_of_busemann_items hind hstatR hstatL hsym) hgeo

/-- CONDITIONAL positive-side characteristic expansion for the SDP laws of
the measurable representative. Its only hypotheses are the open item laws
`ind`, `stationary` (two laws), `sym`, and the explicit geometric input `hgeo`.
It is not a paper result; C14 and the F1/F4 caveats remain in force. -/
theorem sdp_positive_expansion_of_busemann_items_and_hgeo
    (hgeo : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤ ((Measure.infinitePi (fun _ : ℕ => mu_f f)).real
        {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1})) :
    let κ : ℝ := 3 - 6 * g (-1) ^ 2 - f 0
    let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
    κ = 0 ∧
      (fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (b : ℂ) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)]
          (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) := by
  exact SDPExpansion.sdp_kappa_zero_expansion_of_linear_bound
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsym) busemann_sdpG_zero_below
    (sdp_master_equation_of_busemann_items hind hstatR hstatL hsym) hgeo

/-- CONDITIONAL strict-tail asymptotics for the SDP increment laws of the
measurable representative, with the derived constants proved in
`SDPTailFromExpansions` (`eq:conc-asympt-3` and `eq:conc-asympt-4`,
item laws `ind`, `stationary` (two laws), `sym`, and `hgeo`. The constants are
subject to source candidate C14; this is not `thm-busemann-tail` or a paper
result, and F1/F4 caveats remain in force. -/
theorem sdp_tail_asymptotics_of_busemann_items_and_hgeo
    (hgeo : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤ ((Measure.infinitePi (fun _ : ℕ => mu_f f)).real
        {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1})) :
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
        =o[atTop] (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) := by
  have hκ : 3 - 6 * g (-1) ^ 2 - f 0 = 0 :=
    sdp_kappa_zero_of_busemann_items_and_hgeo hind hstatR hstatL hsym hgeo
  exact ⟨hκ,
    sdp_f_absolute_tail_asymptotic_of_master
      busemann_sdpF_nonneg busemann_sdpF_hasSum_one
      busemann_sdpG_nonneg busemann_sdpG_hasSum_one
      (busemann_sdpF_symm hsym) busemann_sdpG_zero_below
      (sdp_master_equation_of_busemann_items hind hstatR hstatL hsym) hκ,
    sdp_g_positive_tail_asymptotic_of_master
      busemann_sdpF_nonneg busemann_sdpF_hasSum_one
      busemann_sdpG_nonneg busemann_sdpG_hasSum_one
      (busemann_sdpF_symm hsym) busemann_sdpG_zero_below
      (sdp_master_equation_of_busemann_items hind hstatR hstatL hsym) hκ⟩

end Conditional
end DirectedDistances.Recursive
