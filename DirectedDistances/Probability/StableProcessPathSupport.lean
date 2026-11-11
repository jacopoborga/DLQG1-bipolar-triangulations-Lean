/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.BusemannConvergenceIdentified
import DirectedDistances.Recursive.ItemPosBridge
import all DirectedDistances.Recursive.BusemannWindowLimit
import all DirectedDistances.Recursive.BusemannWindowLimitSDP
import all DirectedDistances.Recursive.BusemannPositiveHalfLaw
import all DirectedDistances.Recursive.BusemannPositiveHalfLawSDP
import DirectedDistances.Probability.SkorokhodJ1WindowDEval
import Mathlib.Topology.Order.IsLUB















public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.Recursive DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1
open scoped Topology

private theorem pathSupport_ae_closed_of_tendsto
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [HasOuterApproxClosed E] {μn : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hμ : Tendsto μn atTop (𝓝 μ))
    {F : Set E} (hF : IsClosed F)
    (hmem : ∀ n, ∀ᵐ x ∂(μn n : Measure E), x ∈ F) :
    ∀ᵐ x ∂(μ : Measure E), x ∈ F := by
  apply (mem_ae_iff_prob_eq_one hF.measurableSet).mpr
  apply le_antisymm (prob_le_one)
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hF
  have heq (n : ℕ) : (μn n : Measure E) F = 1 :=
    (mem_ae_iff_prob_eq_one hF.measurableSet).mp (hmem n)
  simpa only [heq, limsup_const] using h

private theorem pathSupport_ldp_nat_antitone :
    ∀ᵐ ω ∂iidCodeMeasure,
      Antitone (fun k : ℕ => busemannLDPMeasurableVersion ω (k : ℤ)) := by
  filter_upwards [ldp_measurable_increment_bound] with ω hω
  apply antitone_nat_of_succ_le
  intro n
  have h := hω ((n : ℤ) + 1) (by omega)
  change busemannLDPMeasurableVersion ω ((n : ℤ) + 1) -
    busemannLDPMeasurableVersion ω (((n : ℤ) + 1) - 1) ≤ -1 at h
  simp only [add_sub_cancel_right] at h
  push_cast
  omega

private theorem pathSupport_ldp_window_nonpos (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ t : J1Window T,
      (ldpBusemannWindow n hT ω).path.1 t ≤ 0 := by
  filter_upwards [pathSupport_ldp_nat_antitone] with ω hω t
  rw [ldpBusemannWindow_apply]
  apply mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by positivity) _)
  rw [← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) t.property.1)]
  have h := hω (Nat.zero_le ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊)
  simpa only [Nat.cast_zero, busemannLDPMeasurableVersion_zero, Int.cast_nonpos]
    using h

/-- Theorem 1.6 support ingredient: the canonical positive LDP window endpoint
law is supported on the nonpositive half-line. This uses the proved functional
window convergence and the discrete increment bound. -/
theorem ldpStableWindowLimit_endpoint_nonpos {T : ℝ} (hT : 0 < T) :
    let ν := Classical.choose
      (ldp_busemann_window_tendsto ldpIncrements_iIndep_proved hsymLdp_ldpCode hT)
    ∀ᵐ x ∂(ν : Measure (J1WindowD T hT)),
      x.path.1 ⟨T, hT.le, le_rfl⟩ ≤ 0 := by
  dsimp only
  let ν := Classical.choose
    (ldp_busemann_window_tendsto ldpIncrements_iIndep_proved hsymLdp_ldpCode hT)
  let e : J1WindowD T hT → ℝ := fun x => x.path.1 ⟨T, hT.le, le_rfl⟩
  have he : Measurable e := measurable_j1WindowD_eval hT _
  have hν := (Classical.choose_spec
    (ldp_busemann_window_tendsto ldpIncrements_iIndep_proved hsymLdp_ldpCode hT)).1
  have ht := tendsto_map_of_ae_continuousAt _ ν hν e he
    (Eventually.of_forall fun x => j1WindowD_eval_endpoint_continuousAt hT x)
  have hmem (n : ℕ) :
      ∀ᵐ y ∂((ldpBusemannWindowLaw n hT).map e : Measure ℝ), y ∈ Set.Iic 0 := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff he.aemeasurable measurableSet_Iic).mpr
    change ∀ᵐ x ∂iidCodeMeasure.map (ldpBusemannWindow n hT), e x ≤ 0
    have hm : Measurable (ldpBusemannWindow n hT) := by
      apply measurable_scaledPartialSumWindow
      intro j
      exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        ((measurable_busemannLDPMeasurableVersion _).sub
          (measurable_busemannLDPMeasurableVersion _))
    apply (ae_map_iff hm.aemeasurable (measurableSet_le he measurable_const)).mpr
    filter_upwards [pathSupport_ldp_window_nonpos n hT] with ω hω
    exact hω _
  have hs := pathSupport_ae_closed_of_tendsto ht isClosed_Iic hmem
  exact (ae_map_iff he.aemeasurable measurableSet_Iic).mp hs

private theorem pathSupport_partition_increment_charFun
    {Ψ : ℝ → ℂ} {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : StablePartitionLaw Ψ μ) (hzero : Ψ 0 = 0)
    (s t : Set.Ici (0 : ℝ)) (hst : s ≤ t) (u : ℝ) :
    charFun ((μ : Measure CadlagLocalZero).map
      (fun x => x.1.1 t - x.1.1 s)) u =
      Complex.exp (-((((t : ℝ) - (s : ℝ) : ℝ) : ℂ) * Ψ u)) := by
  let ts : Fin 3 → Set.Ici (0 : ℝ) := ![⟨0, le_rfl⟩, s, t]
  have hts : Monotone ts := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ts]
    · exact s.property
    · exact t.property
  have h := hμ 2 ts rfl hts ![0, u]
  have hm : Measurable (fun x : CadlagLocalZero => x.1.1 t - x.1.1 s) :=
    (measurable_ldpStableHalfEval t).sub (measurable_ldpStableHalfEval s)
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  simpa [ts, Fin.sum_univ_two, Fin.prod_univ_two, hzero] using h

/-- Theorem 1.6 support ingredient: every ordered increment of any law with
the full positive LDP partition exponent is almost surely nonpositive. The
positive scale is arbitrary. -/
theorem ldpStableHalfLaw_ae_increment_nonpos {a : ℝ}
    {μ : ProbabilityMeasure CadlagLocalZero} (hμ : LdpStableHalfLaw a μ)
    (s t : Set.Ici (0 : ℝ)) (hst : s ≤ t) :
    ∀ᵐ x ∂(μ : Measure CadlagLocalZero), x.1.1 t - x.1.1 s ≤ 0 := by
  rcases eq_or_lt_of_le hst with rfl | hst
  · exact Eventually.of_forall fun x => by simp only [sub_self, le_refl]
  let T : ℝ := ((t : ℝ) - (s : ℝ)) * a / ldpStableHalfScale
  have hT : 0 < T := div_pos (mul_pos (sub_pos.mpr hst) hμ.1) ldpStableHalfScale_pos
  let ν := Classical.choose
    (ldp_busemann_window_tendsto ldpIncrements_iIndep_proved hsymLdp_ldpCode hT)
  let e : J1WindowD T hT → ℝ := fun x => x.path.1 ⟨T, hT.le, le_rfl⟩
  have he : Measurable e := measurable_j1WindowD_eval hT _
  have hm := (measurable_ldpStableHalfEval t).sub (measurable_ldpStableHalfEval s)
  have heq : (μ : Measure CadlagLocalZero).map (fun x => x.1.1 t - x.1.1 s) =
      (ν : Measure (J1WindowD T hT)).map e := by
    apply Measure.ext_of_charFun
    funext u
    rw [pathSupport_partition_increment_charFun hμ.2
      (by simp [Real.zero_rpow, (by norm_num : (2 / 3 : ℝ) ≠ 0)]) s t hst.le u]
    rw [ldpBusemannWindowLimit_eval_charFun]
    congr 1
    dsimp [ldpStableHalfExponent, T]
    push_cast
    field_simp [ne_of_gt ldpStableHalfScale_pos]
  have hν : ∀ᵐ y ∂(ν : Measure (J1WindowD T hT)).map e, y ≤ 0 :=
    (ae_map_iff he.aemeasurable measurableSet_Iic).mpr
      (ldpStableWindowLimit_endpoint_nonpos hT)
  rw [← heq] at hν
  exact (ae_map_iff hm.aemeasurable measurableSet_Iic).mp hν

/-- A càdlàg half-line path which is nonincreasing on a dense set is
nonincreasing everywhere. Right continuity includes the origin. -/
theorem cadlagLocal_antitone_of_dense (x : CadlagLocal)
    {D : Set (Set.Ici (0 : ℝ))} (hD : Dense D) (hanti : AntitoneOn x.1 D) :
    Antitone x.1 := by
  intro s t hst
  rcases eq_or_lt_of_le hst with rfl | hst
  · exact le_rfl
  obtain ⟨u, _, hu, hut⟩ := hD.exists_seq_strictAnti_tendsto_of_lt hst
  obtain ⟨v, _, hv, hvt⟩ := hD.exists_seq_strictAnti_tendsto t
  have hu' : Tendsto u atTop (𝓝[>] s) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hut
      (Eventually.of_forall fun n => (hu n).1.1)
  have hv' : Tendsto v atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within v hvt
      (Eventually.of_forall fun n => (hv n).1)
  exact le_of_tendsto_of_tendsto
    ((x.2.isRightContinuous t).tendsto.comp hv')
    ((x.2.isRightContinuous s).tendsto.comp hu')
    (Eventually.of_forall fun n =>
      hanti (hu n).2 (hv n).2 ((hu n).1.2.trans (hv n).1).le)




theorem ldpStableHalfLaw_ae_antitone {a : ℝ}
    {μ : ProbabilityMeasure CadlagLocalZero} (hμ : LdpStableHalfLaw a μ) :
    ∀ᵐ x ∂(μ : Measure CadlagLocalZero),
      ∀ s t : Set.Ici (0 : ℝ), s ≤ t → x.1.1 t ≤ x.1.1 s := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (Set.Ici (0 : ℝ))
  let : Countable D := hDc.to_subtype
  have hp : ∀ s t : D, ∀ᵐ x ∂(μ : Measure CadlagLocalZero),
      s.val ≤ t.val → x.1.1 t.val ≤ x.1.1 s.val := by
    intro s t
    by_cases hst : s.val ≤ t.val
    · filter_upwards [ldpStableHalfLaw_ae_increment_nonpos hμ s.val t.val hst] with x hx _
      exact sub_nonpos.mp hx
    · exact Eventually.of_forall fun _ h => (hst h).elim
  have hp' := ae_all_iff.mpr fun s => ae_all_iff.mpr (hp s)
  filter_upwards [hp'] with x hx
  exact cadlagLocal_antitone_of_dense x.1 hD
    (fun s hs t ht hst => hx ⟨s, hs⟩ ⟨t, ht⟩ hst)

private theorem pathSupport_window_small_value_error {T : ℝ} (hT : 0 < T)
    (f g : J1WindowD T hT) {δ : ℝ} (hδ : dist f g < δ) :
    ∃ φ : J1TimeChange T, ∀ t, |f.path.1 (φ t) - g.path.1 t| < δ := by
  change (⨅ φ : J1TimeChange T,
    max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
      (⨆ t : J1Window T, |f.path.1 (φ t) - g.path.1 t|)) < δ at hδ
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt hδ
  refine ⟨φ, fun t => ?_⟩
  exact ((le_ciSup_of_le (j1WindowValueError_bddAbove f.path g.path φ) t le_rfl).trans
    (le_max_right _ _)).trans_lt hφ

private theorem pathSupport_leftLim_error {T : ℝ} (hT : 0 < T)
    (f g : J1WindowD T hT) (φ : J1TimeChange T) {δ : ℝ}
    (hδ : ∀ t, |f.path.1 (φ t) - g.path.1 t| < δ)
    (t : J1Window T) (ht : 0 < (t : ℝ)) :
    |f.path.1.leftLim (φ t) - g.path.1.leftLim t| ≤ δ := by
  have : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨⟨0, le_rfl, hT.le⟩, ht⟩
  have hφ : Tendsto φ (𝓝[<] t) (𝓝[<] (φ t)) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin
    · exact φ.continuous.continuousWithinAt
    · intro s hs
      exact φ.strictMono hs
  apply le_of_tendsto
    ((((f.path.2.tendsto_nhdsLT_leftLim (φ t)).comp hφ).sub
      (g.path.2.tendsto_nhdsLT_leftLim t)).abs)
  exact Eventually.of_forall fun s => (hδ s).le

/-- Theorem 1.6 support ingredient: a uniform lower bound on every jump is
a closed property in the finite-window J1 topology. Positive times include the
right endpoint, and the bound is simultaneous over all times. -/
theorem isClosed_j1Window_jump_lower_bound {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    IsClosed {x : J1WindowD T hT | ∀ t : J1Window T, 0 < (t : ℝ) →
      x.path.1.leftLim t ≤ x.path.1 t + ε} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f g hf hg t ht
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨n, hn⟩ := ((Metric.tendsto_atTop.mp hg) (δ / 3) (by positivity))
  obtain ⟨φ, hφ⟩ := pathSupport_window_small_value_error hT (f n) g (hn n le_rfl)
  have hφt : 0 < (φ t : ℝ) :=
    lt_of_le_of_lt (φ ⟨0, le_rfl, hT.le⟩).property.1 (φ.strictMono ht)
  have hbound := hf n (φ t) hφt
  have hleft := abs_le.mp (pathSupport_leftLim_error hT (f n) g φ hφ t ht)
  have hright := abs_lt.mp (hφ t)
  linarith

private theorem pathSupport_sdp_window_leftLim (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : ℕ → Fin 3) (t : J1Window T) (ht : 0 < (t : ℝ)) :
    (sdpBusemannWindow n hT ω).path.1.leftLim t =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        (busemannSDPMeasurableVersion ω
          (⌈((n + 1 : ℕ) : ℝ) * (t : ℝ)⌉ - 1) : ℝ) := by
  have : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨⟨0, le_rfl, hT.le⟩, ht⟩
  have hcoe : Tendsto (fun s : J1Window T => (s : ℝ))
      (𝓝[<] t) (𝓝[<] (t : ℝ)) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin
    · exact continuous_subtype_val.continuousWithinAt
    · exact fun s hs => hs
  have h := (floorStep_left_limit (fun j => (busemannSDPMeasurableVersion ω j : ℝ))
    (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)
    (t : ℝ)).comp hcoe
  apply leftLim_eq_of_tendsto
  have heq : (sdpBusemannWindow n hT ω).path.1 =
      fun s : J1Window T => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        (busemannSDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * (s : ℝ)⌋ : ℝ) :=
    funext fun s => sdpBusemannWindow_apply n hT ω s
  rw [heq]
  exact h

/-- Theorem 1.6 support ingredient: all negative jumps of the actual scaled
SDP window have size at most `(n + 1)^(-3/4)`, simultaneously in time. -/
theorem sdpBusemannWindow_ae_jump_lower_bound (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ t : J1Window T, 0 < (t : ℝ) →
      (sdpBusemannWindow n hT ω).path.1.leftLim t ≤
        (sdpBusemannWindow n hT ω).path.1 t +
          ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) := by
  filter_upwards [sdp_measurable_increment_bound] with ω hω t ht
  rw [pathSupport_sdp_window_leftLim n hT ω t ht, sdpBusemannWindow_apply]
  let r : ℝ := ((n + 1 : ℕ) : ℝ) * (t : ℝ)
  have hr : 0 < r := mul_pos (by positivity) ht
  have hceil : 1 ≤ ⌈r⌉ := by have := Int.ceil_pos.mpr hr; omega
  have hfloor := Int.floor_le_ceil r
  have hnear := Int.ceil_le_floor_add_one r
  have hscale : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  by_cases heq : ⌈r⌉ - 1 = ⌊r⌋
  · change _ * (busemannSDPMeasurableVersion ω (⌈r⌉ - 1) : ℝ) ≤
      _ * (busemannSDPMeasurableVersion ω ⌊r⌋ : ℝ) + _
    rw [heq]
    linarith
  · have heq' : ⌊r⌋ = ⌈r⌉ := by omega
    have hb := hω ⌈r⌉ hceil
    change -1 ≤ busemannSDPMeasurableVersion ω ⌈r⌉ -
      busemannSDPMeasurableVersion ω (⌈r⌉ - 1) at hb
    have hb' : (busemannSDPMeasurableVersion ω (⌈r⌉ - 1) : ℝ) ≤
        (busemannSDPMeasurableVersion ω ⌈r⌉ : ℝ) + 1 := by exact_mod_cast (by omega :
          busemannSDPMeasurableVersion ω (⌈r⌉ - 1) ≤
            busemannSDPMeasurableVersion ω ⌈r⌉ + 1)
    change _ * (busemannSDPMeasurableVersion ω (⌈r⌉ - 1) : ℝ) ≤
      _ * (busemannSDPMeasurableVersion ω ⌊r⌋ : ℝ) + _
    rw [heq']
    simpa only [mul_add, mul_one] using mul_le_mul_of_nonneg_left hb' hscale

/-- Theorem 1.6 support ingredient: every functional limit of the actual
scaled SDP window laws has no negative jumps, on one event for all positive
times in the window. -/
theorem sdpBusemannWindowLimit_ae_no_negative_jumps {T : ℝ} (hT : 0 < T)
    {ν : ProbabilityMeasure (J1WindowD T hT)}
    (hν : Tendsto (fun n => sdpBusemannWindowLaw n hT) atTop (𝓝 ν)) :
    ∀ᵐ x ∂(ν : Measure (J1WindowD T hT)), ∀ t : J1Window T,
      0 < (t : ℝ) → x.path.1.leftLim t ≤ x.path.1 t := by
  have hscale : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hn using 1
    norm_num [Function.comp_def]
  have hε (k : ℕ) : ∀ᵐ x ∂(ν : Measure (J1WindowD T hT)),
      ∀ t : J1Window T, 0 < (t : ℝ) →
        x.path.1.leftLim t ≤ x.path.1 t + 1 / ((k : ℝ) + 1) := by
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    have hεpos : 0 < ε := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hscale).2 ε hεpos)
    have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
    apply pathSupport_ae_closed_of_tendsto (hν.comp hshift)
      (isClosed_j1Window_jump_lower_bound hT ε)
    intro n
    change ∀ᵐ x ∂iidCodeMeasure.map (sdpBusemannWindow (n + N) hT),
      ∀ t : J1Window T, 0 < (t : ℝ) → x.path.1.leftLim t ≤ x.path.1 t + ε
    have hm : Measurable (sdpBusemannWindow (n + N) hT) := by
      apply measurable_scaledPartialSumWindow
      intro j
      exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        ((measurable_busemannSDPMeasurableVersion _).sub
          (measurable_busemannSDPMeasurableVersion _))
    apply (ae_map_iff hm.aemeasurable
      (isClosed_j1Window_jump_lower_bound hT ε).measurableSet).mpr
    filter_upwards [sdpBusemannWindow_ae_jump_lower_bound (n + N) hT] with ω hω t ht
    have hb := hω t ht
    have hn := hN (n + N) (by omega)
    linarith
  filter_upwards [ae_all_iff.mpr hε] with x hx t ht
  have h : x.path.1.leftLim t ≤ x.path.1 t + 0 :=
    ge_of_tendsto (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)
      (Eventually.of_forall fun k => hx k t ht)
  simpa only [add_zero] using h

private theorem pathSupport_leftLim_weighted {A : Type*} [LinearOrder A]
    [TopologicalSpace A] [OrderTopology A] {T : ℝ} (hT : 0 < T)
    (f : A → ℝ) (hf : IsCadlag f) (q : J1Window T → A)
    (hq : Continuous q) (hmono : StrictMono q)
    (c : J1Window T → ℝ) (hc : Continuous c)
    (t : J1Window T) (ht : 0 < (t : ℝ)) :
    (fun s => f (q s) * c s).leftLim t = f.leftLim (q t) * c t := by
  have : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨⟨0, le_rfl, hT.le⟩, ht⟩
  have hq' : Tendsto q (𝓝[<] t) (𝓝[<] (q t)) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin hq.continuousWithinAt
    exact fun s hs => hmono hs
  exact leftLim_eq_of_tendsto
    (((hf.tendsto_nhdsLT_leftLim (q t)).comp hq').mul
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))

private theorem pathSupport_sdp_cutoff_no_negative_jumps (N : ℕ) :
    ∀ᵐ v ∂(sdpBusemannPositiveCutoffLimit sdpIncrements_iIndep_proved
      hsymSdp_sdpCode N : Measure (LocalCutoffTuple N)),
      ∀ t : J1Window ((N : ℝ) + 1), 0 < (t : ℝ) →
        (v ⟨N, Nat.lt_succ_self N⟩).path.1.leftLim t ≤
          (v ⟨N, Nat.lt_succ_self N⟩).path.1 t := by
  let i : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
  let P : LocalCutoffTuple N → Prop := fun v =>
    ∀ t : J1Window ((N : ℝ) + 1), 0 < (t : ℝ) →
      (v i).path.1.leftLim t ≤ (v i).path.1 t
  have hP : MeasurableSet {v | P v} := by
    have heval : Measurable (fun v : LocalCutoffTuple N => v i) := measurable_pi_apply i
    have hm := (isClosed_j1Window_jump_lower_bound
      (by positivity : 0 < (N : ℝ) + 1) 0).measurableSet.preimage heval
    simpa only [Set.preimage_ofPred_eq, add_zero, P] using hm
  let ν : ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity)) :=
    Classical.choose (sdp_busemann_window_tendsto
    sdpIncrements_iIndep_proved hsymSdp_sdpCode
      (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))
  change ∀ᵐ v ∂(ν : Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
          (positiveHalfCutoffFactor N), P v
  apply (ae_map_iff (measurable_positiveHalfCutoffFactor N).aemeasurable hP).mpr
  have hν := (Classical.choose_spec (sdp_busemann_window_tendsto
    sdpIncrements_iIndep_proved hsymSdp_sdpCode
      (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))).1
  filter_upwards [sdpBusemannWindowLimit_ae_no_negative_jumps (by positivity) hν]
    with x hx
  intro t ht
  let q : J1Window ((N : ℝ) + 1) → J1Window ((N + 2 : ℕ) : ℝ) :=
    fun s => ⟨s, s.property.1, by have := s.property.2; push_cast; linarith⟩
  let c : J1Window ((N : ℝ) + 1) → ℝ :=
    fun s => localCutoff N (localWindowTime s)
  have hq : Continuous q := continuous_subtype_val.subtype_mk _
  have hc : Continuous c := (localCutoff_continuous N).comp localWindowTime_continuous
  have heq : (positiveHalfCutoffFactor N x i).path.1 =
      fun s => x.path.1 (q s) * c s := rfl
  change (positiveHalfCutoffFactor N x i).path.1.leftLim t ≤
    (positiveHalfCutoffFactor N x i).path.1 t
  rw [heq, pathSupport_leftLim_weighted (by positivity) x.path.1 x.path.2 q hq
    (fun _ _ h => h) c hc t ht]
  exact mul_le_mul_of_nonneg_right (hx (q t) ht) (le_max_left 0 _)

/-- Theorem 1.6 support ingredient: every actual positive-half SDP functional
limit has only nonnegative jumps, simultaneously at every positive time on the
whole half-line. This is canonical-process support, not yet the implication
from an arbitrary `SdpStableHalfLaw`. -/
theorem sdpBusemannPositiveHalfLimit_ae_no_negative_jumps
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ)) :
    ∀ᵐ x ∂(μ : Measure CadlagLocalZero), ∀ t : Set.Ici (0 : ℝ),
      0 < (t : ℝ) → x.1.1.leftLim t ≤ x.1.1 t := by
  have hN (N : ℕ) : ∀ᵐ x ∂(μ : Measure CadlagLocalZero),
      ∀ t : J1Window ((N : ℝ) + 1), 0 < (t : ℝ) →
        (cutoffWindow N x.1).1.leftLim t ≤ (cutoffWindow N x.1).1 t := by
    have h := pathSupport_sdp_cutoff_no_negative_jumps N
    rw [← sdpBusemannPositiveHalfLimit_cutoff hμ N] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable
      (ae_of_ae_map (finiteCutoffWindows_measurable N).aemeasurable h)
  filter_upwards [ae_all_iff.mpr hN] with x hx t ht
  obtain ⟨N, hNt⟩ := exists_nat_ge (t : ℝ)
  let s : J1Window ((N : ℝ) + 1) :=
    ⟨t, t.property, hNt.trans (by linarith)⟩
  have h := hx N s ht
  change (fun u => x.1.1 (localWindowTime u) *
    localCutoff N (localWindowTime u)).leftLim s ≤
      x.1.1 (localWindowTime s) * localCutoff N (localWindowTime s) at h
  rw [pathSupport_leftLim_weighted (by positivity) x.1.1 x.1.2 localWindowTime
    localWindowTime_continuous (fun _ _ h => h)
    (fun u => localCutoff N (localWindowTime u))
    ((localCutoff_continuous N).comp localWindowTime_continuous) s ht] at h
  change x.1.1.leftLim t * localCutoff N t ≤ x.1.1 t * localCutoff N t at h
  simpa only [localCutoff_eq_one N t hNt, mul_one] using h

end DirectedDistances.Probability
