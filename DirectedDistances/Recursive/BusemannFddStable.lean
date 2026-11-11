module

public import DirectedDistances.Recursive.BusemannItemsIndSym
public import DirectedDistances.Probability.SkewedStableProcessFdd
import DirectedDistances.Probability.SkewedStableHexpOfPos
import DirectedDistances.Recursive.SDPSideSelection

/-! Positive-time finite-dimensional helpers for Theorem 1.6. The positive-index law is `g`,
whose characteristic function is `G`, rather than the symmetric nonpositive-index law `f`.
The scales below are derived from Section 6 and are not standardized by convention.
F1/F4 remain source-identification gates. No functional convergence is asserted. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology ENNReal

private theorem integer_law_cf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → ℤ) (hD : Measurable D)
    (t : ℝ) :
    charFun (P.map (fun ω => (D ω : ℝ))) t =
      integerCF (fun z => P.real {ω | D ω = z}) t := by
  have hc : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  have hlaw : P.map (fun ω => (D ω : ℝ)) =
      SDPExpansion.mu_f (fun z => P.real {ω | D ω = z}) := by
    change P.map ((fun z : ℤ => (z : ℝ)) ∘ D) = _
    rw [← Measure.map_map hc hD, Measure.map_eq_sum P D hD,
      Measure.map_sum hc.aemeasurable]
    simp_rw [Measure.map_smul _ hc.aemeasurable, Measure.map_dirac' hc]
    unfold SDPExpansion.mu_f
    congr 1
    funext z
    congr 1
    exact (ENNReal.ofReal_toReal (measure_ne_top P (D ⁻¹' {z}))).symm
  rw [hlaw, SDPExpansion.mu_f_charFun (fun z => measureReal_nonneg)]
  rfl

private theorem sum_positive_increments {Ω : Type*} (Y : Ω → ℤ → ℤ)
    (h0 : ∀ ω, Y ω 0 = 0) (r : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range r,
      ((Y ω ((j : ℤ) + 1) - Y ω (j : ℤ) : ℤ) : ℝ)) = (Y ω (r : ℤ) : ℝ) := by
  induction r with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, h0,
      Int.cast_zero]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Int.cast_sub, Nat.cast_succ]
    ring

private theorem positive_fdd {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℤ → ℤ)
    (hY : ∀ j, Measurable (fun ω => Y ω j)) (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (fun j ω => Y ω j - Y ω (j - 1)) P)
    (hstat : ∀ j ≥ 1, P.map (fun ω => Y ω j - Y ω (j - 1)) =
      P.map (fun ω => Y ω 1 - Y ω 0))
    {ν : ℝ} {κ : ℂ} (hν : 0 < ν)
    (hpos : (fun s : ℝ =>
      charFun (P.map (fun ω => ((Y ω 1 - Y ω 0 : ℤ) : ℝ))) s -
        (1 - κ * ((s ^ ν : ℝ) : ℂ))) =o[𝓝[>] 0] (fun s : ℝ => s ^ ν))
    {m : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (ht : Monotone t) :
    ∃ μlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m),
        charFun (μlim : Measure _) θ = ∏ i : Fin m, Complex.exp
          (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ ν : ℝ))))) ∧
      TendstoInDistribution
        (fun n : ℕ => fun ω => WithLp.toLp 2 (fun i : Fin m =>
          (n : ℝ) ^ (-1 / ν) * (Y ω ⌊(n : ℝ) * t (i.val + 1)⌋ : ℝ)))
        atTop (fun x => x) (fun _ => P)
        ((μlim.map (cumulativeSum (k := m))) : Measure _) := by
  let X : ℕ → Ω → ℝ := fun j ω =>
    ((Y ω ((j : ℤ) + 1) - Y ω (j : ℤ) : ℤ) : ℝ)
  have hD (j : ℤ) : Measurable (fun ω => Y ω j - Y ω (j - 1)) :=
    (hY j).sub (hY (j - 1))
  have hc : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  have hX (j : ℕ) : Measurable (X j) := by
    exact hc.comp ((hY ((j : ℤ) + 1)).sub (hY (j : ℤ)))
  have hi : iIndepFun X P := by
    have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + 1) := by
      intro a b hab
      exact_mod_cast (add_right_cancel hab)
    have hh := (iIndepFun.precomp hinj hind).comp (fun _ => fun z : ℤ => (z : ℝ))
      (fun _ => hc)
    simpa only [Function.comp_def, add_sub_cancel_right] using hh
  have hid (j : ℕ) : IdentDistrib (X j) (X 0) P P := by
    have h : IdentDistrib (fun ω => Y ω ((j : ℤ) + 1) -
        Y ω (((j : ℤ) + 1) - 1)) (fun ω => Y ω 1 - Y ω (1 - 1)) P P :=
      ⟨(hD _).aemeasurable, (hD _).aemeasurable, by
        simpa only [sub_self] using hstat ((j : ℤ) + 1) (by omega)⟩
    simpa only [X, Function.comp_def, add_sub_cancel_right, Nat.cast_zero, zero_add,
      sub_self] using h.comp hc
  have hp : (fun s : ℝ => charFun (P.map (X 0)) s -
      (1 - κ * ((s ^ ν : ℝ) : ℂ))) =o[𝓝[>] 0] (fun s : ℝ => s ^ ν) := hpos
  have : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hX 0).aemeasurable).mpr inferInstance
  obtain ⟨μlim, hchar, hlim⟩ := tendsto_skewStable_processVector_law (k := m) hi hid hX hν
    (charFun_hexp_of_pos_expansion hν hp) (by rw [ht0]) ht
  have heq (n : ℕ) : skewStableProcessVector (k := m) (t := t) (ν := ν) X n =
      (fun ω => WithLp.toLp 2 (fun i : Fin m =>
        (n : ℝ) ^ (-1 / ν) * (Y ω ⌊(n : ℝ) * t (i.val + 1)⌋ : ℝ))) := by
    funext ω
    apply PiLp.ext
    intro i
    rw [skewStableProcessVector_apply X n ω i ht]
    simp only [ht0, mul_zero, Nat.floor_zero, Nat.Ico_zero_eq_range]
    change (n : ℝ) ^ (-1 / ν) *
      (∑ j ∈ Finset.range ⌊(n : ℝ) * t (i.val + 1)⌋₊,
        ((Y ω ((j : ℤ) + 1) - Y ω (j : ℤ) : ℤ) : ℝ)) = _
    rw [sum_positive_increments Y h0]
    rw [Int.natCast_floor_eq_floor
      (mul_nonneg (Nat.cast_nonneg n) (by rw [← ht0]; exact ht (Nat.zero_le _)))]
  refine ⟨μlim, hchar, ?_⟩
  have hsample (n : ℕ) : AEMeasurable
      (fun ω => WithLp.toLp 2 (fun i : Fin m =>
        (n : ℝ) ^ (-1 / ν) * (Y ω ⌊(n : ℝ) * t (i.val + 1)⌋ : ℝ))) P := by
    exact ((MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp
      (measurable_pi_iff.mpr fun i =>
        (hc.comp (hY _)).const_mul _)).aemeasurable
  apply TendstoInDistribution.of_tendsto_charFun hsample measurable_id.aemeasurable
  intro θ
  have hh := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim) θ
  simpa only [heq, Measure.map_id, ProbabilityMeasure.coe_mk] using hh

section LDP

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannLDPMeasurableVersion
local notation "f" => ldpF μ Y
local notation "g" => ldpG μ Y






theorem ldp_busemann_fdd_of_ind_sym
    (hind : iIndepFun (fun j ω => ldpIncrement Y j ω) μ)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {m : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (ht : Monotone t) :
    let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
    let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
    0 < a ∧ ∃ μlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m),
        charFun (μlim : Measure _) θ = ∏ i : Fin m, Complex.exp
          (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
      TendstoInDistribution
        (fun n : ℕ => fun ω => WithLp.toLp 2 (fun i : Fin m =>
          (n : ℝ) ^ (-3 / 2 : ℝ) * (Y ω ⌊(n : ℝ) * t (i.val + 1)⌋ : ℝ)))
        atTop (fun x => x) (fun _ => μ)
        ((μlim.map (cumulativeSum (k := m))) : Measure _) := by
  dsimp only
  let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
  let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
  have hrec := ldp_master_equation_of_ind_sym hind hsym
  have hsmall := (ldp_side_expansions_of_master
    busemann_ldpF_nonneg busemann_ldpF_hasSum_one
    busemann_ldpG_nonneg busemann_ldpG_hasSum_one
    (busemann_ldpF_symm hsym) busemann_ldpG_zero_of_nonneg hrec).2
  have hD : Measurable (ldpIncrement Y 1) :=
    (measurable_busemannLDPMeasurableVersion 1).sub
      (measurable_busemannLDPMeasurableVersion (1 - 1))
  have hcf (s : ℝ) :
      charFun (iidCodeMeasure.map (fun ω => ((Y ω 1 - Y ω 0 : ℤ) : ℝ))) s = negativeCF g s := by
    change charFun (iidCodeMeasure.map (fun ω => (ldpIncrement Y 1 ω : ℝ))) s = _
    rw [integer_law_cf μ (ldpIncrement Y 1) hD s]
    change integerCF g s = negativeCF g s
    unfold integerCF negativeCF
    symm
    refine (tsum_subtype {z : ℤ | z ≤ -1} (fun z : ℤ =>
      (g z : ℂ) * Complex.exp (((s * (z : ℝ) : ℝ) : ℂ) * Complex.I))).trans ?_
    apply tsum_congr
    intro z
    by_cases hz : z ≤ -1
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hz, ite_true]
    · simp [hz, busemann_ldpG_zero_of_nonneg z (by omega)]
  have hp : (fun s : ℝ =>
      charFun (iidCodeMeasure.map (fun ω => ((Y ω 1 - Y ω 0 : ℤ) : ℝ))) s -
        (1 - κ * ((s ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
      =o[𝓝[>] 0] (fun s : ℝ => s ^ (2 / 3 : ℝ)) := by
    apply hsmall.congr'
    · filter_upwards with s
      rw [hcf]
      dsimp [κ, a]
      ring
    · exact Filter.Eventually.of_forall fun _ => rfl
  have ha : 0 < a := by
    apply Real.rpow_pos_of_pos
    exact div_pos (add_pos_of_pos_of_nonneg (by norm_num) (busemann_ldpF_nonneg 0))
      (by norm_num)
  refine ⟨ha, ?_⟩
  have hh := positive_fdd (m := m) μ Y measurable_busemannLDPMeasurableVersion
    busemannLDPMeasurableVersion_zero hind busemannLDPMeasurableVersion_right_stationary
    (by norm_num : (0 : ℝ) < 2 / 3) hp ht0 ht
  norm_num only [show (-1 / (2 / 3 : ℝ)) = -3 / 2 by norm_num] at hh
  simpa only [neg_div] using hh

end LDP

section SDP

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF μ Y
local notation "g" => SDPMasterFromLaw.sdpG μ Y







theorem sdp_busemann_fdd_of_ind_sym
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {m : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (ht : Monotone t) :
    let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
    let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (b : ℂ)
    0 < b ∧ ∃ μlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m),
        charFun (μlim : Measure _) θ = ∏ i : Fin m, Complex.exp
          (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
      TendstoInDistribution
        (fun n : ℕ => fun ω => WithLp.toLp 2 (fun i : Fin m =>
          (n : ℝ) ^ (-3 / 4 : ℝ) * (Y ω ⌊(n : ℝ) * t (i.val + 1)⌋ : ℝ)))
        atTop (fun x => x) (fun _ => μ)
        ((μlim.map (cumulativeSum (k := m))) : Measure _) := by
  dsimp only
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (b : ℂ)
  have hrec := sdp_master_equation_of_ind_sym hind hsym
  have hκ := sdp_kappa_zero_of_busemann_items_and_hgeo hind
    busemannSDPMeasurableVersion_right_stationary
    busemannSDPMeasurableVersion_left_stationary hsym (sdp_hgeo_of_ind_sym hind hsym)
  have hsmall := (SDPExpansion.sdp_kappa_zero_side_expansions_of_master
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsym) busemann_sdpG_zero_below hrec hκ).2
  have hD : Measurable (SDPMasterFromLaw.increment Y 1) :=
    (measurable_busemannSDPMeasurableVersion 1).sub
      (measurable_busemannSDPMeasurableVersion (1 - 1))
  have hcf (s : ℝ) :
      charFun (iidCodeMeasure.map (fun ω => ((Y ω 1 - Y ω 0 : ℤ) : ℝ))) s =
        SDPExpansion.sdpCF g s := by
    change charFun (iidCodeMeasure.map (fun ω => (SDPMasterFromLaw.increment Y 1 ω : ℝ))) s = _
    rw [integer_law_cf μ (SDPMasterFromLaw.increment Y 1) hD s]
    change integerCF g s = SDPExpansion.sdpCF g s
    unfold integerCF SDPExpansion.sdpCF
    symm
    refine (tsum_subtype {z : ℤ | -1 ≤ z} (fun z : ℤ =>
      (g z : ℂ) * Complex.exp (((s * (z : ℝ) : ℝ) : ℂ) * Complex.I))).trans ?_
    apply tsum_congr
    intro z
    by_cases hz : -1 ≤ z
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hz, ite_true]
    · simp [hz, busemann_sdpG_zero_below z (by omega)]
  have hp : (fun s : ℝ =>
      charFun (iidCodeMeasure.map (fun ω => ((Y ω 1 - Y ω 0 : ℤ) : ℝ))) s -
        (1 - κ * ((s ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
      =o[𝓝[>] 0] (fun s : ℝ => s ^ (4 / 3 : ℝ)) := by
    apply hsmall.congr'
    · filter_upwards with s
      rw [hcf]
      dsimp [κ, b]
      ring
    · exact Filter.Eventually.of_forall fun _ => rfl
  have hb : 0 < b := Real.rpow_pos_of_pos
    (SDPExpansion.sdp_side_nondegenerate_of_master
      busemann_sdpF_nonneg busemann_sdpF_hasSum_one
      busemann_sdpG_nonneg busemann_sdpG_hasSum_one
      (busemann_sdpF_symm hsym) busemann_sdpG_zero_below hrec).2 _
  refine ⟨hb, ?_⟩
  have hh := positive_fdd (m := m) μ Y measurable_busemannSDPMeasurableVersion
    busemannSDPMeasurableVersion_zero hind busemannSDPMeasurableVersion_right_stationary
    (by norm_num : (0 : ℝ) < 4 / 3) hp ht0 ht
  norm_num only [show (-1 / (4 / 3 : ℝ)) = -3 / 4 by norm_num] at hh
  simpa only [neg_div] using hh

end SDP
end DirectedDistances.Recursive
