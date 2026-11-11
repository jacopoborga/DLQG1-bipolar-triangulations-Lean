module

public import DirectedDistances.Recursive.SDPMeanZero
public import DirectedDistances.Recursive.BusemannTailSDPConditional
import DirectedDistances.Recursive.SDPSideSelection
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure












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

private theorem integer_integrable_integral_atoms
    (ν : Measure ℤ) [IsFiniteMeasure ν]
    (hm : Summable (fun n : ℤ => |(n : ℝ)| * ν.real {n})) :
    Integrable (fun n : ℤ => (n : ℝ)) ν ∧
      (∫ n : ℤ, (n : ℝ) ∂ν) = ∑' n : ℤ, (n : ℝ) * ν.real {n} := by
  have hi : Integrable (fun n : ℤ => (n : ℝ)) ν := by
    rw [← Measure.sum_smul_dirac ν]
    apply integrable_sum_dirac (fun n => measure_ne_top ν {n})
    change Summable (fun n : ℤ => ν.real {n} * ‖(n : ℝ)‖)
    simpa only [Real.norm_eq_abs, mul_comm] using hm
  refine ⟨hi, ?_⟩
  rw [integral_countable hi]
  simp only [smul_eq_mul, mul_comm]

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

/-- CONDITIONAL first absolute moment and zero atom mean for the right SDP
increment law, the zero-mean clause of `thm-busemann-tail` (vb),
This is not `thm-busemann-tail` and is not counted; F1/F4 apply. -/
theorem busemann_sdpG_first_moment_and_mean_zero_of_items :
    Summable (fun y : ℤ => |(y : ℝ)| * g y) ∧
      (∑' y : ℤ, (y : ℝ) * g y) = 0 := by
  obtain ⟨hκ, _, htail⟩ :=
    sdp_tail_asymptotics_of_busemann_items hind hstatR hstatL hsym
  have hG := (sdp_kappa_zero_side_expansions_of_master
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsym) busemann_sdpG_zero_below
    (sdp_master_equation_of_busemann_items hind hstatR hstatL hsym) hκ).2
  exact first_moment_and_mean_zero_of_sdp_expansions
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one busemann_sdpG_zero_below
    (by norm_num : (1 : ℝ) < 4 / 3) htail
    (Complex.isLittleO_ofReal_right.mpr hG)

/-- CONDITIONAL first absolute moment and zero atom mean for the left SDP
increment law, the zero-mean clause of `thm-busemann-tail` (vb),
This is not `thm-busemann-tail` and is not counted; F1/F4 apply. -/
theorem busemann_sdpF_first_moment_and_mean_zero_of_items :
    Summable (fun x : ℤ => |(x : ℝ)| * f x) ∧
      (∑' x : ℤ, (x : ℝ) * f x) = 0 := by
  have htail :=
    (sdp_tail_asymptotics_of_busemann_items hind hstatR hstatL hsym).2.1
  exact ⟨summable_abs_int_mul_of_tail_isBigO
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    (by norm_num : (1 : ℝ) < 4 / 3) (tail_isBigO_of_expansion htail),
    tsum_int_mul_eq_zero_of_symmetric (busemann_sdpF_symm hsym)⟩





theorem busemann_sdp_increment_mean_zero_of_items :
    ∀ k : ℤ,
      Integrable (fun ω => ((Y ω k - Y ω (k - 1) : ℤ) : ℝ)) μ ∧
        (∫ ω, ((Y ω k - Y ω (k - 1) : ℤ) : ℝ) ∂μ) = 0 := by
  have hD (k : ℤ) : Measurable (SDPMasterFromLaw.increment Y k) :=
    (measurable_busemannSDPMeasurableVersion k).sub
      (measurable_busemannSDPMeasurableVersion (k - 1))
  have hatom (k n : ℤ) :
      (iidCodeMeasure.map (SDPMasterFromLaw.increment Y k)).real {n} =
        iidCodeMeasure.real {ω | SDPMasterFromLaw.increment Y k ω = n} := by
    rw [map_measureReal_apply (hD k) (measurableSet_singleton n)]
    rfl
  have hg := busemann_sdpG_first_moment_and_mean_zero_of_items hind hstatR hstatL hsym
  have hf := busemann_sdpF_first_moment_and_mean_zero_of_items hind hstatR hstatL hsym
  have hgAtoms : Summable (fun n : ℤ => |(n : ℝ)| *
      (iidCodeMeasure.map (SDPMasterFromLaw.increment Y 1)).real {n}) := by
    simpa only [hatom, SDPMasterFromLaw.sdpG] using hg.1
  have hfAtoms : Summable (fun n : ℤ => |(n : ℝ)| *
      (iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0)).real {n}) := by
    simpa only [hatom, SDPMasterFromLaw.sdpF] using hf.1
  obtain ⟨hgi, hgv⟩ := integer_integrable_integral_atoms
    (iidCodeMeasure.map (SDPMasterFromLaw.increment Y 1)) hgAtoms
  obtain ⟨hfi, hfv⟩ := integer_integrable_integral_atoms
    (iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0)) hfAtoms
  have hgzero : (∫ n : ℤ, (n : ℝ)
      ∂(iidCodeMeasure.map (SDPMasterFromLaw.increment Y 1))) = 0 := by
    rw [hgv]
    simpa only [hatom, SDPMasterFromLaw.sdpG] using hg.2
  have hfzero : (∫ n : ℤ, (n : ℝ)
      ∂(iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0))) = 0 := by
    rw [hfv]
    simpa only [hatom, SDPMasterFromLaw.sdpF] using hf.2
  intro k
  have hbase : ∃ j : ℤ,
      iidCodeMeasure.map (SDPMasterFromLaw.increment Y k) =
        iidCodeMeasure.map (SDPMasterFromLaw.increment Y j) ∧
      Integrable (fun n : ℤ => (n : ℝ))
        (iidCodeMeasure.map (SDPMasterFromLaw.increment Y j)) ∧
      (∫ n : ℤ, (n : ℝ) ∂(iidCodeMeasure.map (SDPMasterFromLaw.increment Y j))) = 0 := by
    by_cases hk : 1 ≤ k
    · exact ⟨1, hstatR k hk, hgi, hgzero⟩
    · exact ⟨0, hstatL k (by omega), hfi, hfzero⟩
  obtain ⟨j, hkj, hji, hjzero⟩ := hbase
  have hki : Integrable (fun n : ℤ => (n : ℝ))
      (iidCodeMeasure.map (SDPMasterFromLaw.increment Y k)) := hkj.symm ▸ hji
  refine ⟨hki.comp_measurable (hD k), ?_⟩
  change (∫ ω, ((SDPMasterFromLaw.increment Y k ω : ℤ) : ℝ) ∂μ) = 0
  rw [← integral_map (hD k).aemeasurable (by fun_prop), hkj]
  exact hjzero

end Conditional
end DirectedDistances.Recursive
