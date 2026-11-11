/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteLimit
public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteLemmas
public import DirectedDistances.Probability.SkorokhodJ1WindowDCirc

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped ENNReal Topology Uniformity

private theorem chain_timeChange_zero {T : ℝ} (hT : 0 < T)
    (φ : J1TimeChange T) :
    φ ⟨0, ⟨le_rfl, hT.le⟩⟩ = ⟨0, ⟨le_rfl, hT.le⟩⟩ := by
  let z : J1Window T := ⟨0, ⟨le_rfl, hT.le⟩⟩
  have hmin : z ≤ φ.symm z := (φ.symm z).property.1
  have hle : φ z ≤ z := by
    calc
      φ z ≤ φ (φ.symm z) := φ.monotone hmin
      _ = z := φ.apply_symm_apply z
  apply Subtype.ext
  exact le_antisymm hle (φ z).property.1

private theorem chain_timeChange_top {T : ℝ} (hT : 0 < T)
    (φ : J1TimeChange T) :
    φ ⟨T, ⟨hT.le, le_rfl⟩⟩ = ⟨T, ⟨hT.le, le_rfl⟩⟩ := by
  let z : J1Window T := ⟨T, ⟨hT.le, le_rfl⟩⟩
  have hmax : φ.symm z ≤ z := (φ.symm z).property.2
  have hge : z ≤ φ z := by
    calc
      z = φ (φ.symm z) := (φ.apply_symm_apply z).symm
      _ ≤ φ z := φ.monotone hmax
  apply Subtype.ext
  exact le_antisymm (φ z).property.2 hge




theorem chain_step_le {T : ℝ} (hT : 0 < T) (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k n : ℕ) (t : J1Window T) :
    |(j1TimeChangeChain μ k (n + 1) t : ℝ) -
        (j1TimeChangeChain μ k n t : ℝ)| ≤
      T * (Real.exp (j1TimeChangeSlopeNorm (μ (k + n))).toReal - 1) := by
  have hsum_ne : (∑' j, j1TimeChangeSlopeNorm (μ j)) ≠ ⊤ := ne_of_lt hsum
  have hμ_ne : j1TimeChangeSlopeNorm (μ (k + n)) ≠ ⊤ :=
    ne_top_of_tsum_ne_top hsum_ne (k + n)
  let u := j1TimeChangeChain μ k n t
  have hu : j1TimeChangeChain μ k (n + 1) t = μ (k + n) u := by
    simp [u, j1TimeChangeChain, OrderIso.trans_apply]
  rw [hu]
  exact j1TimeChange_displacement_le hT (μ (k + n))
    (lt_top_iff_ne_top.mpr hμ_ne) u




theorem chain_increment_summable {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤) :
    Summable (fun j => T *
      (Real.exp (j1TimeChangeSlopeNorm (μ j)).toReal - 1)) := by
  have hsum_ne : (∑' j, j1TimeChangeSlopeNorm (μ j)) ≠ ⊤ := ne_of_lt hsum
  have hnorm : Summable (fun j => (j1TimeChangeSlopeNorm (μ j)).toReal) :=
    ENNReal.summable_toReal hsum_ne
  let A : ℝ := (∑' j, j1TimeChangeSlopeNorm (μ j)).toReal
  have hnorm_tsum : (∑' j, (j1TimeChangeSlopeNorm (μ j)).toReal) = A := by
    simpa [A] using (ENNReal.tsum_toReal_eq
      (fun j => ne_top_of_tsum_ne_top hsum_ne j)).symm
  have hnorm_le (j : ℕ) : (j1TimeChangeSlopeNorm (μ j)).toReal ≤ A := by
    rw [← hnorm_tsum]
    exact hnorm.le_tsum j (fun i _ => ENNReal.toReal_nonneg)
  have hexp_bound (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
    have h := Real.add_one_le_exp (-x)
    have hmul : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    have hpos := Real.exp_pos x
    have hmul' := mul_le_mul_of_nonneg_right h hpos.le
    nlinarith
  have hle (j : ℕ) :
      T * (Real.exp (j1TimeChangeSlopeNorm (μ j)).toReal - 1) ≤
        (T * Real.exp A) * (j1TimeChangeSlopeNorm (μ j)).toReal := by
    have hx_nonneg : 0 ≤ (j1TimeChangeSlopeNorm (μ j)).toReal := ENNReal.toReal_nonneg
    have hexp := Real.exp_le_exp.mpr (hnorm_le j)
    have hprod :
        (j1TimeChangeSlopeNorm (μ j)).toReal *
            Real.exp (j1TimeChangeSlopeNorm (μ j)).toReal ≤
          (j1TimeChangeSlopeNorm (μ j)).toReal * Real.exp A :=
      mul_le_mul_of_nonneg_left hexp hx_nonneg
    have hdiff_nonneg : 0 ≤
        Real.exp (j1TimeChangeSlopeNorm (μ j)).toReal - 1 := by
      have h := Real.add_one_le_exp (j1TimeChangeSlopeNorm (μ j)).toReal
      linarith [hx_nonneg]
    calc
      T * (Real.exp (j1TimeChangeSlopeNorm (μ j)).toReal - 1) ≤
          T * ((j1TimeChangeSlopeNorm (μ j)).toReal *
            Real.exp (j1TimeChangeSlopeNorm (μ j)).toReal) :=
        mul_le_mul_of_nonneg_left (hexp_bound _) hT.le
      _ ≤ T * ((j1TimeChangeSlopeNorm (μ j)).toReal * Real.exp A) :=
        mul_le_mul_of_nonneg_left hprod hT.le
      _ = (T * Real.exp A) * (j1TimeChangeSlopeNorm (μ j)).toReal := by ring
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg hT.le (by
      have h := Real.add_one_le_exp (j1TimeChangeSlopeNorm (μ j)).toReal
      have hx_nonneg : 0 ≤ (j1TimeChangeSlopeNorm (μ j)).toReal :=
        ENNReal.toReal_nonneg
      linarith))
    hle
  exact hnorm.mul_left (T * Real.exp A)

private theorem chain_distance_le_sum_range {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) (δ : ℕ → ℝ) (hδ : ∀ j, T *
      (Real.exp (j1TimeChangeSlopeNorm (μ (k + j))).toReal - 1) ≤ δ j)
    (m r : ℕ) (t : J1Window T) :
    |(j1TimeChangeChain μ k (m + r) t : ℝ) -
        (j1TimeChangeChain μ k m t : ℝ)| ≤
      ∑ i ∈ Finset.range r, δ (m + i) := by
  induction r with
  | zero => simp
  | succ r ih =>
      simp only [Nat.add_succ, Finset.sum_range_succ]
      calc
        |(j1TimeChangeChain μ k (m + r + 1) t : ℝ) -
            (j1TimeChangeChain μ k m t : ℝ)| ≤
            |(j1TimeChangeChain μ k (m + r + 1) t : ℝ) -
                (j1TimeChangeChain μ k (m + r) t : ℝ)| +
              |(j1TimeChangeChain μ k (m + r) t : ℝ) -
                (j1TimeChangeChain μ k m t : ℝ)| := abs_sub_le _ _ _
        _ ≤ δ (m + r) + ∑ i ∈ Finset.range r, δ (m + i) :=
          add_le_add (chain_step_le hT μ hsum k (m + r) t |>.trans (hδ (m + r))) ih
        _ = (∑ i ∈ Finset.range r, δ (m + i)) + δ (m + r) := add_comm _ _




theorem chain_uniformCauchy {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) :
    UniformCauchySeqOn
      (fun n t => (j1TimeChangeChain μ k n t : ℝ)) atTop Set.univ := by
  let δ : ℕ → ℝ := fun j =>
    T * (Real.exp (j1TimeChangeSlopeNorm (μ (k + j))).toReal - 1)
  have hδsummable : Summable δ := by
    simpa [δ, Function.comp_def] using
      (chain_increment_summable hT μ hsum).comp_injective
        (fun _ _ h => Nat.add_left_cancel h)
  have hδnonneg (j : ℕ) : 0 ≤ δ j := by
    dsimp [δ]
    have hx : 0 ≤ (j1TimeChangeSlopeNorm (μ (k + j))).toReal :=
      ENNReal.toReal_nonneg
    have h := Real.add_one_le_exp (j1TimeChangeSlopeNorm (μ (k + j))).toReal
    exact mul_nonneg hT.le (by linarith)
  have htail : Tendsto (fun N => ∑' i, δ (N + i)) atTop (𝓝 0) := by
    have hprefix : Tendsto (fun N => ∑ i ∈ Finset.range N, δ i) atTop
        (𝓝 (∑' i, δ i)) := hδsummable.hasSum.tendsto_sum_nat
    have heq (N : ℕ) :
        (∑' i, δ (N + i)) = (∑' i, δ i) - ∑ i ∈ Finset.range N, δ i := by
      have hdecomp := hδsummable.sum_add_tsum_nat_add N
      have hshift : (∑' i, δ (N + i)) = ∑' i, δ (i + N) := by
        exact tsum_congr fun i => by rw [Nat.add_comm]
      rw [hshift]
      exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hdecomp)
    have hconst : Tendsto (fun _ : ℕ => ∑' i, δ i) atTop
        (𝓝 (∑' i, δ i)) := tendsto_const_nhds
    have hsub : Tendsto
        (fun N => (∑' i, δ i) - ∑ i ∈ Finset.range N, δ i) atTop (𝓝 0) := by
      simpa only [sub_self] using hconst.sub hprefix
    simpa only [heq] using hsub
  intro u hu
  rcases Metric.uniformity_basis_dist.mem_iff.mp hu with ⟨ε, hε, hεu⟩
  have htail_small : ∀ᶠ N in atTop, (∑' i, δ (N + i)) < ε := by
    filter_upwards [Metric.tendsto_nhds.mp htail ε hε] with N hN
    simpa [Real.dist_eq, abs_of_nonneg
      (tsum_nonneg fun i => hδnonneg (N + i))] using hN
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail_small
  have hpair : ∀ᶠ p : ℕ × ℕ in atTop ×ˢ atTop,
      N ≤ p.1 ∧ N ≤ p.2 := by
    rw [eventually_prod_iff]
    exact ⟨fun n => N ≤ n, eventually_atTop.2 ⟨N, fun _ hn => hn⟩,
      fun n => N ≤ n, eventually_atTop.2 ⟨N, fun _ hn => hn⟩,
      fun {_} hm {_} hn => ⟨hm, hn⟩⟩
  filter_upwards [hpair] with p hp t ht
  have hdist :
      |(j1TimeChangeChain μ k p.1 t : ℝ) -
        (j1TimeChangeChain μ k p.2 t : ℝ)| < ε := by
    rcases le_total p.1 p.2 with h | h
    · let r := p.2 - p.1
      have hr : p.1 + r = p.2 := Nat.add_sub_of_le h
      have hshift : Summable (fun i => δ (p.1 + i)) :=
        hδsummable.comp_injective (fun _ _ h => Nat.add_left_cancel h)
      have hbound := chain_distance_le_sum_range hT μ hsum k δ
        (fun j => le_rfl) p.1 r t
      have hsumle := hshift.sum_le_tsum (Finset.range r)
        (fun i hi => hδnonneg (p.1 + i))
      rw [hr] at hbound
      rw [abs_sub_comm]
      exact lt_of_le_of_lt (hbound.trans hsumle) (hN p.1 hp.1)
    ·
      let r := p.1 - p.2
      have hr : p.2 + r = p.1 := Nat.add_sub_of_le h
      have hshift : Summable (fun i => δ (p.2 + i)) :=
        hδsummable.comp_injective (fun _ _ h => Nat.add_left_cancel h)
      have hbound := chain_distance_le_sum_range hT μ hsum k δ
        (fun j => le_rfl) p.2 r t
      have hsumle := hshift.sum_le_tsum (Finset.range r)
        (fun i hi => hδnonneg (p.2 + i))
      rw [hr] at hbound
      exact lt_of_le_of_lt (hbound.trans hsumle) (hN p.2 hp.2)
  exact hεu hdist




noncomputable def chainLimit {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) : J1Window T → ℝ := fun t =>
  Classical.choose (cauchySeq_tendsto_of_complete
    ((chain_uniformCauchy hT μ hsum k).cauchySeq (x := t) (Set.mem_univ t)))

private theorem chainLimit_tendsto {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) (t : J1Window T) :
    Tendsto (fun n => (j1TimeChangeChain μ k n t : ℝ)) atTop
      (𝓝 (chainLimit hT μ hsum k t)) := by
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete
    ((chain_uniformCauchy hT μ hsum k).cauchySeq (x := t) (Set.mem_univ t)))




theorem chain_tendstoUniformly {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) :
    TendstoUniformly (fun n t => (j1TimeChangeChain μ k n t : ℝ))
      (chainLimit hT μ hsum k) atTop := by
  rw [← tendstoUniformlyOn_univ]
  exact (chain_uniformCauchy hT μ hsum k).tendstoUniformlyOn_of_tendsto
    (f := chainLimit hT μ hsum k)
    (fun t _ => chainLimit_tendsto hT μ hsum k t)




theorem chainLimit_endpoints {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) :
    chainLimit hT μ hsum k ⟨0, ⟨le_rfl, hT.le⟩⟩ = 0 ∧
      chainLimit hT μ hsum k ⟨T, ⟨hT.le, le_rfl⟩⟩ = T := by
  have hzero (n : ℕ) :
      (j1TimeChangeChain μ k n ⟨0, ⟨le_rfl, hT.le⟩⟩ : ℝ) = 0 := by
    have h := congrArg (fun x : J1Window T => (x : ℝ))
      (chain_timeChange_zero hT (j1TimeChangeChain μ k n))
    simpa using h
  have htop (n : ℕ) :
      (j1TimeChangeChain μ k n ⟨T, ⟨hT.le, le_rfl⟩⟩ : ℝ) = T := by
    have h := congrArg (fun x : J1Window T => (x : ℝ))
      (chain_timeChange_top hT (j1TimeChangeChain μ k n))
    simpa using h
  constructor
  · apply tendsto_nhds_unique (chainLimit_tendsto hT μ hsum k _)
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (𝓝 0))
  · apply tendsto_nhds_unique (chainLimit_tendsto hT μ hsum k _)
    simpa only [htop] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => T)
      atTop (𝓝 T))

private theorem chainLimit_norm_le_total {T : ℝ}
    (μ : ℕ → J1TimeChange T)
    (k n : ℕ) :
    j1TimeChangeSlopeNorm (j1TimeChangeChain μ k n) ≤
      ∑' j, j1TimeChangeSlopeNorm (μ j) := by
  calc
    j1TimeChangeSlopeNorm (j1TimeChangeChain μ k n) ≤
        ∑ i ∈ Finset.range n, j1TimeChangeSlopeNorm (μ (k + i)) :=
      j1TimeChangeChain_slopeNorm_le_sum μ k n
    _ ≤ ∑' i, j1TimeChangeSlopeNorm (μ (k + i)) :=
      CompleteLattice.summable.sum_le_tsum (f := fun i =>
        j1TimeChangeSlopeNorm (μ (k + i))) (Finset.range n) (fun _ _ => zero_le)
    _ ≤ ∑' j, j1TimeChangeSlopeNorm (μ j) :=
      CompleteLattice.summable.tsum_le_tsum_of_inj (fun i => k + i)
        (fun _ _ h => Nat.add_left_cancel h) (fun _ _ => zero_le) (fun _ => le_rfl)
        CompleteLattice.summable




theorem chainLimit_biLipschitz {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) (s t : J1Window T) :
    let S := (∑' j, j1TimeChangeSlopeNorm (μ j)).toReal
    Real.exp (-S) * |(t : ℝ) - s| ≤
        |chainLimit hT μ hsum k t - chainLimit hT μ hsum k s| ∧
      |chainLimit hT μ hsum k t - chainLimit hT μ hsum k s| ≤
        Real.exp S * |(t : ℝ) - s| := by
  dsimp only
  let S : ℝ := (∑' j, j1TimeChangeSlopeNorm (μ j)).toReal
  have htotal_ne : (∑' j, j1TimeChangeSlopeNorm (μ j)) ≠ ⊤ := ne_of_lt hsum
  have hseq : Tendsto
      (fun n => |(j1TimeChangeChain μ k n t : ℝ) -
        (j1TimeChangeChain μ k n s : ℝ)|) atTop
      (𝓝 |chainLimit hT μ hsum k t - chainLimit hT μ hsum k s|) :=
    ((chainLimit_tendsto hT μ hsum k t).sub
      (chainLimit_tendsto hT μ hsum k s)).abs
  have hbounds (n : ℕ) :
      Real.exp (-S) * |(t : ℝ) - s| ≤
          |(j1TimeChangeChain μ k n t : ℝ) -
            (j1TimeChangeChain μ k n s : ℝ)| ∧
        |(j1TimeChangeChain μ k n t : ℝ) -
            (j1TimeChangeChain μ k n s : ℝ)| ≤
          Real.exp S * |(t : ℝ) - s| := by
    have hnorm := chainLimit_norm_le_total μ k n
    have hnormtop : j1TimeChangeSlopeNorm (j1TimeChangeChain μ k n) < ⊤ :=
      lt_of_le_of_lt hnorm hsum
    have hnormreal :
        (j1TimeChangeSlopeNorm (j1TimeChangeChain μ k n)).toReal ≤ S :=
      ENNReal.toReal_mono htotal_ne hnorm
    have hchange := j1TimeChange_lipschitz_bounds
      (j1TimeChangeChain μ k n) hnormtop s t
    constructor
    · calc
        Real.exp (-S) * |(t : ℝ) - s| ≤
            Real.exp (-(j1TimeChangeSlopeNorm
              (j1TimeChangeChain μ k n)).toReal) * |(t : ℝ) - s| :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg hnormreal)) (abs_nonneg _)
        _ ≤ |(j1TimeChangeChain μ k n t : ℝ) -
            (j1TimeChangeChain μ k n s : ℝ)| := hchange.1
    · calc
        |(j1TimeChangeChain μ k n t : ℝ) -
            (j1TimeChangeChain μ k n s : ℝ)| ≤
            Real.exp ((j1TimeChangeSlopeNorm
              (j1TimeChangeChain μ k n)).toReal) * |(t : ℝ) - s| := hchange.2
        _ ≤ Real.exp S * |(t : ℝ) - s| :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr hnormreal) (abs_nonneg _)
  constructor
  · exact ge_of_tendsto hseq (Filter.Eventually.of_forall fun n => (hbounds n).1)
  · exact le_of_tendsto hseq (Filter.Eventually.of_forall fun n => (hbounds n).2)

private theorem chainLimit_monotone {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) : Monotone (chainLimit hT μ hsum k) := by
  intro s t hst
  have hdiff : Tendsto
      (fun n => (j1TimeChangeChain μ k n s : ℝ) -
        (j1TimeChangeChain μ k n t : ℝ)) atTop
      (𝓝 (chainLimit hT μ hsum k s - chainLimit hT μ hsum k t)) :=
    (chainLimit_tendsto hT μ hsum k s).sub
      (chainLimit_tendsto hT μ hsum k t)
  have hle (n : ℕ) :
      (j1TimeChangeChain μ k n s : ℝ) -
        (j1TimeChangeChain μ k n t : ℝ) ≤ 0 := by
    have h := (j1TimeChangeChain μ k n).monotone hst
    have hreal :
        (j1TimeChangeChain μ k n s : ℝ) ≤
          (j1TimeChangeChain μ k n t : ℝ) := by
      exact_mod_cast h
    exact sub_nonpos.mpr hreal
  exact sub_nonpos.mp (le_of_tendsto hdiff (Filter.Eventually.of_forall hle))




theorem chainLimit_strictMono {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) : StrictMono (chainLimit hT μ hsum k) := by
  intro s t hst
  have hmono := chainLimit_monotone hT μ hsum k hst.le
  have hbounds := chainLimit_biLipschitz hT μ hsum k s t
  have hpositive : 0 < Real.exp (-(∑' j, j1TimeChangeSlopeNorm (μ j)).toReal) *
      |(t : ℝ) - s| := mul_pos (Real.exp_pos _) (abs_pos.mpr (sub_ne_zero.mpr (by
        intro h
        exact hst.ne (Subtype.ext h.symm))))
  have hneq : chainLimit hT μ hsum k s ≠ chainLimit hT μ hsum k t := by
    intro heq
    have hzero : |chainLimit hT μ hsum k t - chainLimit hT μ hsum k s| = 0 := by
      rw [heq]
      simp
    have hle := hbounds.1
    rw [hzero] at hle
    linarith
  exact lt_of_le_of_ne hmono hneq

end DirectedDistances.Probability
