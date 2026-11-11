module

public import DirectedDistances.Recursive.LDPMasterFromLaw
public import DirectedDistances.Recursive.LDPSplitting
public import DirectedDistances.Recursive.MeasurableVersionPos
public import DirectedDistances.Recursive.LDPTail

/-! Supporting lemmas for paper labels `prop:LDP-recursive-equation` (see CORRESPONDENCE.md). -/




















public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk
open scoped ENNReal

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannLDPMeasurableVersion
local notation "f" => ldpF iidCodeMeasure busemannLDPMeasurableVersion
local notation "g" => ldpG iidCodeMeasure busemannLDPMeasurableVersion

/-- The `hf` side fact for the CONDITIONAL LDP helpers: nonnegative atoms of
F1/F4 caveats apply. -/
theorem busemann_ldpF_nonneg : ∀ x : ℤ, 0 ≤ f x :=
  ldpF_nonneg μ Y

/-- The `hfs` side fact for the CONDITIONAL LDP helpers: the left increment
F1/F4 caveats apply. -/
theorem busemann_ldpF_hasSum_one : HasSum f (1 : ℝ) :=
  ldpF_hasSum_one μ Y measurable_busemannLDPMeasurableVersion

/-- The `hg` side fact for the CONDITIONAL LDP helpers: nonnegative atoms of
F1/F4 caveats apply. -/
theorem busemann_ldpG_nonneg : ∀ y : ℤ, 0 ≤ g y :=
  ldpG_nonneg μ Y

/-- The `hgs` side fact for the CONDITIONAL LDP helpers: the right increment
F1/F4 caveats apply. -/
theorem busemann_ldpG_hasSum_one : HasSum g (1 : ℝ) :=
  ldpG_hasSum_one μ Y measurable_busemannLDPMeasurableVersion

/-- CONDITIONAL `hsymm` side fact. Item `sym` is an open paper obligation
This is a helper, not a paper result; the module's F1/F4 caveats apply. -/
theorem busemann_ldpF_symm
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    ∀ x : ℤ, f (-x) = f x :=
  ldpF_symm μ Y measurable_busemannLDPMeasurableVersion hsym

private theorem busemann_ldp_increment_neg :
    ∀ᵐ ω ∂μ, ∀ k ≥ 1, ldpIncrement Y k ω ≤ -1 := by
  simpa only [ldpIncrement] using iidCodes_ae_busemannLDPMeasurableVersion_item_pos



theorem busemann_ldpG_zero_of_nonneg : ∀ y : ℤ, 0 ≤ y → g y = 0 := by
  intro y hy
  exact ldpG_zero_of_nonneg μ Y busemann_ldp_increment_neg hy

private theorem busemann_ldp_splitting_real (x y : ℤ) :
    iidCodeMeasure.real {ω | (Y ω (-1), Y ω 1) = (x, y)} =
      (1 / 3 : ℝ) * iidCodeMeasure.real {ω | (Y ω (-2) - max (Y ω (-1)) 1,
          -max (Y ω (-1)) 1) = (x, y)} +
        (1 / 3 : ℝ) * iidCodeMeasure.real {ω | (-Y ω 1 - 1, -1) = (x, y)} +
        (1 / 3 : ℝ) * iidCodeMeasure.real {ω | (Y ω (-1), Y ω 2) = (x, y)} := by
  have hfinite (s : Set (ℕ → Fin 3)) : (3 : ENNReal)⁻¹ * μ s ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ s)
  have h := congrArg ENNReal.toReal
    (iidCodeMeasure_busemannLDPMeasurableVersion_splitting_self x y)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfinite _, hfinite _⟩) (hfinite _),
    ENNReal.toReal_add (hfinite _) (hfinite _)] at h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    one_div, Measure.real] using h

section Conditional

variable
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    (hstatR : ∀ k ≥ 1, iidCodeMeasure.map (ldpIncrement Y k) =
      iidCodeMeasure.map (ldpIncrement Y 1))
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement Y k) =
      iidCodeMeasure.map (ldpIncrement Y 0))
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))

include hind hstatR hstatL hsym







theorem ldp_master_equation_of_busemann_items :
    ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
          f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
          (if y = -1 then
            (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
           else 0) :=
  ldp_master_equation_from_law μ Y measurable_busemannLDPMeasurableVersion
    busemannLDPMeasurableVersion_zero hind hstatR hstatL hsym
    busemann_ldp_increment_neg busemann_ldp_splitting_real








theorem ldp_tail_asymptotics_of_busemann_items :
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
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ)))) := by
  have hrec := ldp_master_equation_of_busemann_items hind hstatR hstatL hsym
  exact ⟨ldp_f_absolute_tail_asymptotic_of_master
      busemann_ldpF_nonneg busemann_ldpF_hasSum_one
      busemann_ldpG_nonneg busemann_ldpG_hasSum_one
      (busemann_ldpF_symm hsym) busemann_ldpG_zero_of_nonneg hrec,
    ldp_g_negative_tail_asymptotic_of_master
      busemann_ldpF_nonneg busemann_ldpF_hasSum_one
      busemann_ldpG_nonneg busemann_ldpG_hasSum_one
      (busemann_ldpF_symm hsym) busemann_ldpG_zero_of_nonneg hrec⟩

end Conditional
end DirectedDistances.Recursive
