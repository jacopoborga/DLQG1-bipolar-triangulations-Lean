/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteShift
public import DirectedDistances.Probability.SkorokhodJ1WindowCadlagComp

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped ENNReal Topology Uniformity




theorem subseqLimit_slopeSummable {T : ℝ} (_hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ∑' k, j1TimeChangeSlopeNorm (μ k) < ⊤ := by
  let r : ℝ≥0∞ := (1 / 2 : ℝ≥0∞)
  have hr : r = (2⁻¹ : ℝ≥0∞) := by norm_num [r]
  have hdom (k : ℕ) : j1TimeChangeSlopeNorm (μ k) ≤ r ^ k := by
    calc
      j1TimeChangeSlopeNorm (μ k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := hμ k
      _ = r ^ k := by
        simp [r]
        rw [ENNReal.inv_pow]
  calc
    ∑' k, j1TimeChangeSlopeNorm (μ k) ≤ ∑' k, r ^ k := tsum_le_tsum hdom
    _ = 2 := by rw [hr, ENNReal.tsum_geometric_two]
    _ < ⊤ := ENNReal.ofNat_lt_top





noncomputable def subseqAlignedPath {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (k : ℕ) (u : J1Window T) : ℝ :=
  (x k).1 ((chainTimeChange hT μ (subseqLimit_slopeSummable hT μ hμ) k).symm u)





theorem subseqAlignedPath_step {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k)
    (k : ℕ) (u : J1Window T) :
    |subseqAlignedPath hT x μ hμ k u -
      subseqAlignedPath hT x μ hμ (k + 1) u| ≤ (1 / 2 : ℝ) ^ k := by
  let hsum := subseqLimit_slopeSummable hT μ hμ
  let w := (chainTimeChange hT μ hsum (k + 1)).symm u
  have hshift := chainTimeChange_symm_succ_eq hT μ hsum k
  have hpoint :
      subseqAlignedPath hT x μ hμ k u =
        (x k).1 ((μ k).symm w) := by
    simp only [subseqAlignedPath, w]
    rw [hshift, OrderIso.trans_apply]
  have hnext :
      subseqAlignedPath hT x μ hμ (k + 1) u = (x (k + 1)).1 w := by
    rfl
  rw [hpoint, hnext]
  have h := hx k ((μ k).symm w)
  have hinv := (μ k).apply_symm_apply w
  rw [hinv] at h
  rw [abs_sub_comm]
  simpa only [one_div, inv_pow] using h




noncomputable def subseqAlignedIncrement {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (_hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k)
    (k : ℕ) (u : J1Window T) : ℝ :=
  subseqAlignedPath hT x μ hμ k u - subseqAlignedPath hT x μ hμ (k + 1) u

private theorem subseqLimit_geometricSummable :
    Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) := by
  exact summable_geometric_two

/-- The aligned increments are absolutely summable at each point. -/
theorem subseqAlignedIncrement_summable {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k)
    (u : J1Window T) :
    Summable (fun k => subseqAlignedIncrement hT x μ hμ hx k u) := by
  apply Summable.of_norm_bounded subseqLimit_geometricSummable
  intro k
  rw [Real.norm_eq_abs]
  exact subseqAlignedPath_step hT x μ hμ hx k u




noncomputable def subseqAlignedLimit {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k)
    (u : J1Window T) : ℝ :=
  subseqAlignedPath hT x μ hμ 0 u -
    ∑' k, subseqAlignedIncrement hT x μ hμ hx k u




theorem subseqAlignedLimit_tendstoUniformly {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k) :
    TendstoUniformly
      (fun k u => subseqAlignedPath hT x μ hμ k u)
      (subseqAlignedLimit hT x μ hμ hx) atTop := by
  let inc := subseqAlignedIncrement hT x μ hμ hx
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    subseqLimit_geometricSummable
  have hbound (k : ℕ) (u : J1Window T) :
      ‖inc k u‖ ≤ (1 / 2 : ℝ) ^ k := by
    rw [Real.norm_eq_abs]
    change |subseqAlignedPath hT x μ hμ k u -
      subseqAlignedPath hT x μ hμ (k + 1) u| ≤ _
    exact subseqAlignedPath_step hT x μ hμ hx k u
  have hseries : TendstoUniformly
      (fun n u => ∑ i ∈ Finset.range n, inc i u)
      (fun u => ∑' i, inc i u) atTop :=
    tendstoUniformly_tsum_nat hgeom hbound
  have htel (n : ℕ) (u : J1Window T) :
      (∑ i ∈ Finset.range n, inc i u) =
        subseqAlignedPath hT x μ hμ 0 u - subseqAlignedPath hT x μ hμ n u := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [inc, subseqAlignedIncrement]
        ring
  have hpoint (u : J1Window T) :
      Tendsto (fun n => subseqAlignedPath hT x μ hμ n u) atTop
        (𝓝 (subseqAlignedLimit hT x μ hμ hx u)) := by
    have hs := hseries.tendsto_at u
    have hsub : Tendsto
        (fun n => subseqAlignedPath hT x μ hμ 0 u - ∑ i ∈ Finset.range n, inc i u)
        atTop (𝓝 (subseqAlignedPath hT x μ hμ 0 u - ∑' i, inc i u)) :=
      tendsto_const_nhds.sub hs
    have hrel : (fun n => subseqAlignedPath hT x μ hμ n u) =
        (fun n => subseqAlignedPath hT x μ hμ 0 u - ∑ i ∈ Finset.range n, inc i u) := by
      funext n
      linarith [htel n u]
    rw [hrel]
    simpa [subseqAlignedLimit, inc] using hsub
  have hstep (u : J1Window T) (n : ℕ) :
      dist (subseqAlignedPath hT x μ hμ n u)
        (subseqAlignedPath hT x μ hμ (n + 1) u) ≤ (2 : ℝ) / 2 / 2 ^ n := by
    rw [Real.dist_eq]
    calc
      |subseqAlignedPath hT x μ hμ n u - subseqAlignedPath hT x μ hμ (n + 1) u| ≤
          (1 / 2 : ℝ) ^ n := subseqAlignedPath_step hT x μ hμ hx n u
      _ = (2 : ℝ) / 2 / 2 ^ n := by
        rw [show (2 : ℝ) / 2 = 1 by norm_num]
        simp [one_div, inv_pow]
  have htail (u : J1Window T) (n : ℕ) :
      |subseqAlignedPath hT x μ hμ n u - subseqAlignedLimit hT x μ hμ hx u| ≤
        2 * (1 / 2 : ℝ) ^ n := by
    have h := dist_le_of_le_geometric_two_of_tendsto
      (C := (2 : ℝ)) (hstep u) (hpoint u) n
    rw [Real.dist_eq] at h
    calc
      |subseqAlignedPath hT x μ hμ n u - subseqAlignedLimit hT x μ hμ hx u| ≤
          2 / 2 ^ n := h
      _ = 2 * (1 / 2 : ℝ) ^ n := by
        rw [one_div, inv_pow]
        ring
  have hgeo : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 : ℝ)
  apply (Filter.HasBasis.tendstoUniformly_iff atTop_basis
    Metric.uniformity_basis_dist).2
  intro ε hε
  obtain ⟨N, hN⟩ :=
    (eventually_atTop.1 ((tendsto_order.1 hgeo).2 ε hε))
  refine ⟨N, trivial, ?_⟩
  intro n hn u
  change dist (subseqAlignedLimit hT x μ hμ hx u)
    (subseqAlignedPath hT x μ hμ n u) < ε
  rw [Real.dist_eq, abs_sub_comm]
  exact (htail u n).trans_lt (hN n hn)




theorem subseqAlignedLimit_tail {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k)
    (k : ℕ) (u : J1Window T) :
    |subseqAlignedPath hT x μ hμ k u - subseqAlignedLimit hT x μ hμ hx u| ≤
      2 * (1 / 2 : ℝ) ^ k := by
  have hstep (n : ℕ) :
      dist (subseqAlignedPath hT x μ hμ n u)
        (subseqAlignedPath hT x μ hμ (n + 1) u) ≤ (2 : ℝ) / 2 / 2 ^ n := by
    rw [Real.dist_eq]
    calc
      |subseqAlignedPath hT x μ hμ n u - subseqAlignedPath hT x μ hμ (n + 1) u| ≤
          (1 / 2 : ℝ) ^ n := subseqAlignedPath_step hT x μ hμ hx n u
      _ = (2 : ℝ) / 2 / 2 ^ n := by
        rw [show (2 : ℝ) / 2 = 1 by norm_num]
        simp [one_div, inv_pow]
  have hlim := (subseqAlignedLimit_tendstoUniformly hT x μ hμ hx).tendsto_at u
  have h := dist_le_of_le_geometric_two_of_tendsto
    (C := (2 : ℝ)) hstep hlim k
  rw [Real.dist_eq] at h
  calc
    |subseqAlignedPath hT x μ hμ k u - subseqAlignedLimit hT x μ hμ hx u| ≤
        2 / 2 ^ k := h
    _ = 2 * (1 / 2 : ℝ) ^ k := by
      rw [one_div, inv_pow]
      ring




theorem subseqAlignedLimit_isCadlag {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k) :
    IsCadlag (subseqAlignedLimit hT x μ hμ hx) := by
  apply isCadlag_of_tendstoUniformly
    (F := fun k u => subseqAlignedPath hT x μ hμ k u)
    (f := subseqAlignedLimit hT x μ hμ hx)
  · intro k
    change IsCadlag ((x k).1 ∘
      (chainTimeChange hT μ (subseqLimit_slopeSummable hT μ hμ) k).symm)
    exact isCadlag_comp_timeChange_symm (x k).2
      (chainTimeChange hT μ (subseqLimit_slopeSummable hT μ hμ) k)
  · exact subseqAlignedLimit_tendstoUniformly hT x μ hμ hx




noncomputable def subseqAlignedLimitWindow {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k) :
    CadlagWindow T :=
  ⟨subseqAlignedLimit hT x μ hμ hx,
    subseqAlignedLimit_isCadlag hT x μ hμ hx⟩




@[simp]
theorem subseqAlignedLimitWindow_apply {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k)
    (u : J1Window T) :
    (subseqAlignedLimitWindow hT x μ hμ hx).1 u = subseqAlignedLimit hT x μ hμ hx u := rfl




theorem subseqAlignedLimit_dCirc {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T) (μ : ℕ → J1TimeChange T)
    (hμ : ∀ k, j1TimeChangeSlopeNorm (μ k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hx : ∀ k t, |(x (k + 1)).1 (μ k t) - (x k).1 t| ≤ (1 / 2 : ℝ) ^ k)
    (k : ℕ) :
    j1WindowDCirc hT (x k) (subseqAlignedLimitWindow hT x μ hμ hx) ≤
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
  let hsum := subseqLimit_slopeSummable hT μ hμ
  let φ := (chainTimeChange hT μ hsum k).symm
  let : Nonempty (J1Window T) := ⟨⟨0, ⟨le_rfl, hT.le⟩⟩⟩
  have hvalue :
      (⨆ u : J1Window T,
        |(x k).1 (φ u) - (subseqAlignedLimitWindow hT x μ hμ hx).1 u|) ≤
        2 * (1 / 2 : ℝ) ^ k := by
    apply ciSup_le
    intro u
    simpa [φ, subseqAlignedPath] using subseqAlignedLimit_tail hT x μ hμ hx k u
  have hslope : j1TimeChangeSlopeNorm φ ≤
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
    rw [j1TimeChangeSlopeNorm_symm]
    exact chainTimeChange_slopeNorm_le_geometric hT μ hsum hμ k
  have hvalENN :
      ENNReal.ofReal (⨆ u : J1Window T,
        |(x k).1 (φ u) - (subseqAlignedLimitWindow hT x μ hμ hx).1 u|) ≤
        ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) :=
    ENNReal.ofReal_le_ofReal hvalue
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  have hcosts : BddBelow (Set.range fun ψ : J1TimeChange T =>
      j1WindowDCircCost (x k) (subseqAlignedLimitWindow hT x μ hμ hx) ψ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact bot_le
  change (⨅ ψ : J1TimeChange T,
    j1WindowDCircCost (x k) (subseqAlignedLimitWindow hT x μ hμ hx) ψ) ≤ _
  calc
    (⨅ ψ : J1TimeChange T,
        j1WindowDCircCost (x k) (subseqAlignedLimitWindow hT x μ hμ hx) ψ) ≤
        j1WindowDCircCost (x k) (subseqAlignedLimitWindow hT x μ hμ hx) φ :=
      ciInf_le hcosts φ
    _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := max_le hslope hvalENN

end DirectedDistances.Probability
