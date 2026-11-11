module

public import DirectedDistances.Recursive.SDPRecursiveConditional
public import DirectedDistances.Recursive.SDPHgeoConditional
import DirectedDistances.Recursive.SDPSideSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-property`, `thm-busemann-tail` (see CORRESPONDENCE.md). -/





















public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics Function
open DirectedDistances.RandomWalk
open DirectedDistances.Recursive.SDPExpansion
open scoped ENNReal Topology

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion

private theorem probability_integer_predicate {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (D : Ω → ℤ) (hD : Measurable D)
    (P : ℤ → Prop) [DecidablePred P] :
    ν.real {ω | P (D ω)} =
      ∑' n : ℤ, if P n then ν.real {ω | D ω = n} else 0 := by
  classical
  let s : ℤ → Set Ω := fun n => {ω | D ω = n ∧ P n}
  have hU : {ω | P (D ω)} = ⋃ n : ℤ, s n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, s]
    exact ⟨fun h => ⟨D ω, rfl, h⟩, fun ⟨n, hn, hp⟩ => hn.symm ▸ hp⟩
  have hd : Pairwise (Disjoint on s) := by
    intro i j hij
    exact Set.disjoint_left.2 fun ω hi hj => hij (hi.1.symm.trans hj.1)
  have hm : ∀ n, MeasurableSet (s n) := by
    intro n
    by_cases hp : P n
    · simpa only [s, hp, and_true, Set.preimage, Set.mem_singleton_iff] using
        hD (measurableSet_singleton n)
    · simp only [s, hp, and_false, Set.ofPred_false, MeasurableSet.empty]
  rw [hU, Measure.real, measure_iUnion hd hm,
    ENNReal.tsum_toReal_eq (fun n => measure_ne_top ν (s n))]
  apply tsum_congr
  intro n
  by_cases hp : P n <;> simp [s, hp, Measure.real]

private theorem busemann_right_strict_probability (R : ℝ) :
    iidCodeMeasure.real {ω | R < ((Y ω 1 - Y ω 0 : ℤ) : ℝ)} =
      ∑' n : ℤ, if R < (n : ℝ) then SDPMasterFromLaw.sdpG μ Y n else 0 := by
  have hD : Measurable (SDPMasterFromLaw.increment Y 1) :=
    (measurable_busemannSDPMeasurableVersion 1).sub
      (measurable_busemannSDPMeasurableVersion (1 - 1))
  simpa only [SDPMasterFromLaw.increment, SDPMasterFromLaw.sdpG, sub_self] using
    probability_integer_predicate μ (SDPMasterFromLaw.increment Y 1) hD (fun n => R < (n : ℝ))

private theorem busemann_left_strict_probability (R : ℝ) :
    iidCodeMeasure.real {ω | R < |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} =
      ∑' n : ℤ, if R < |(n : ℝ)| then f n else 0 := by
  have hD : Measurable (SDPMasterFromLaw.increment Y 0) :=
    (measurable_busemannSDPMeasurableVersion 0).sub
      (measurable_busemannSDPMeasurableVersion (0 - 1))
  simpa only [SDPMasterFromLaw.increment, SDPMasterFromLaw.sdpF, zero_sub, neg_neg] using
    probability_integer_predicate μ (SDPMasterFromLaw.increment Y 0) hD (fun n => R < |(n : ℝ)|)

private theorem tendsto_normalized_of_remainder {F : ℝ → ℝ} {C ρ : ℝ}
    (h : (fun x => F x - C * x ^ ρ) =o[atTop] (fun x => x ^ ρ)) :
    Tendsto (fun x => F x / x ^ ρ) atTop (𝓝 C) := by
  have ht := h.tendsto_div_nhds_zero.add_const C
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [sub_div, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hx ρ).ne']
  exact sub_add_cancel _ _

private theorem weak_remainder_of_strict {F H : ℝ → ℝ} {C ρ : ℝ}
    (h : (fun x => F x - C * x ^ ρ) =o[atTop] (fun x => x ^ ρ))
    (hbound : ∀ x, F x ≤ H x ∧ H x ≤ F (x - 1)) :
    (fun x => H x - C * x ^ ρ) =o[atTop] (fun x => x ^ ρ) := by
  have hn := tendsto_normalized_of_remainder h
  have hshift : Tendsto (fun x : ℝ => x - 1) atTop atTop := by
    apply tendsto_atTop_atTop.2
    intro b
    exact ⟨b + 1, fun x hx => by linarith only [hx]⟩
  have hbase : Tendsto (fun x : ℝ => (x - 1) / x) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_atTop_zero
    simp only [sub_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hratio : Tendsto (fun x : ℝ => (x - 1) ^ ρ / x ^ ρ) atTop (𝓝 1) := by
    have ht := hbase.rpow_const (p := ρ) (Or.inl one_ne_zero)
    simp only [Real.one_rpow] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact Real.div_rpow (by linarith only [hx]) (by linarith only [hx]) ρ
  have hu : Tendsto (fun x : ℝ => F (x - 1) / x ^ ρ) atTop (𝓝 C) := by
    have ht := (hn.comp hshift).mul hratio
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_mul_div_cancel₀ (Real.rpow_pos_of_pos (by linarith only [hx]) ρ).ne'
  apply DirectedDistances.Tauberian.isLittleO_sub_mul_rpow_of_tendsto
  apply hn.squeeze' hu
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (hbound x).1 (Real.rpow_pos_of_pos hx ρ).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (hbound x).2 (Real.rpow_pos_of_pos hx ρ).le

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






theorem sdp_tail_asymptotics_of_busemann_items :
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
  have hmass : KappaHgeoTransfer.incrementMass μ Y = f := by
    funext x
    exact sdp_incrementMass_eq x
  apply sdp_tail_asymptotics_of_busemann_items_and_hgeo hind hstatR hstatL hsym
  simpa only [hmass] using sdp_hgeo_of_items hind hstatL hsym

/-- CONDITIONAL κ exclusion under only the four open item laws, for
This helper is not `thm-busemann-tail` and is not counted as a paper result;
the module's C14 and F1/F4 qualifications remain in force. -/
theorem sdp_kappa_zero_of_busemann_items :
    let κ : ℝ := 3 - 6 * g (-1) ^ 2 - f 0
    κ = 0 := by
  exact (sdp_tail_asymptotics_of_busemann_items hind hstatR hstatL hsym).1

private theorem busemann_tail_sdp_strict_of_items :
    let c₂ : ℝ := Real.Gamma (1 / 3 : ℝ) * (g (-1)) ^ (2 / 3 : ℝ) /
      (2 * Real.sqrt 3 * Real.pi)
    0 < c₂ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x < ((Y ω 1 - Y ω 0 : ℤ) : ℝ)} -
        c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x < |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) := by
  dsimp only
  have hq : 0 < g (-1) :=
    (sdp_side_nondegenerate_of_master
      busemann_sdpF_nonneg busemann_sdpF_hasSum_one
      busemann_sdpG_nonneg busemann_sdpG_hasSum_one
      (busemann_sdpF_symm hsym) busemann_sdpG_zero_below
      (sdp_master_equation_of_busemann_items hind hstatR hstatL hsym)).2
  have hpos : 0 < Real.Gamma (1 / 3 : ℝ) * (g (-1)) ^ (2 / 3 : ℝ) /
      (2 * Real.sqrt 3 * Real.pi) :=
    div_pos (mul_pos (Real.Gamma_pos_of_pos (by norm_num))
      (Real.rpow_pos_of_pos hq _))
      (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) Real.pi_pos)
  obtain ⟨_, hf, hg⟩ := sdp_tail_asymptotics_of_busemann_items hind hstatR hstatL hsym
  refine ⟨hpos, ?_, ?_⟩
  · simpa only [busemann_right_strict_probability] using hg
  · have hc : Real.Gamma (1 / 3 : ℝ) * (g (-1)) ^ (2 / 3 : ℝ) /
        (Real.sqrt 3 * Real.pi) =
        2 * (Real.Gamma (1 / 3 : ℝ) * (g (-1)) ^ (2 / 3 : ℝ) /
          (2 * Real.sqrt 3 * Real.pi)) := by ring
    simpa only [busemann_left_strict_probability, hc] using hf

/-- CONDITIONAL helper giving the two weak-endpoint tails in
item laws are explicit hypotheses. One positive constant works for both
tails, with the absolute tail constant exactly twice the right tail constant.
The witness is the derived constant in this module, `sqrt(3)/4` times the
printed value (C14, author ruling required); only existence is claimed here.
This is not `thm-busemann-tail`, does not assert its additional zero-mean
clause, and is not counted as a paper result. F1/F4 remain in force. -/
theorem busemann_tail_sdp_of_items :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ ((Y ω 1 - Y ω 0 : ℤ) : ℝ)} -
        c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) := by
  obtain ⟨hpos, hg, hf⟩ := busemann_tail_sdp_strict_of_items hind hstatR hstatL hsym
  refine ⟨_, hpos, weak_remainder_of_strict hg ?_, weak_remainder_of_strict hf ?_⟩
  · intro x
    constructor
    · refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      exact le_of_lt hω
    · refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith only [hω]
  · intro x
    constructor
    · refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      exact le_of_lt hω
    · refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith only [hω]

end Conditional
end DirectedDistances.Recursive
