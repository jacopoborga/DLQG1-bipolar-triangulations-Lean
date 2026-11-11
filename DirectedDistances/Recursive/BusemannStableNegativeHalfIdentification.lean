/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.BusemannStableHalfIdentification
public import DirectedDistances.Recursive.BusemannNegativeHalfLimitLdp
import all DirectedDistances.Recursive.BusemannStableHalfIdentification
import all DirectedDistances.Recursive.BusemannNegativeHalfLimitLdp

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result. The full LDP coefficient
used by the symmetric negative-half characteristic exponent is exactly the
proved negative-half scale and the positive-half scale formula. -/
theorem ldpStableNegativeHalfScale_eq_explicit :
    negativeHalfLdpScale =
      ((3 + ldpF iidCodeMeasure busemannLDPMeasurableVersion 0) / 2) ^
        (1 / 3 : ℝ) := rfl

/-- Helper toward Theorem 1.6; not a paper result. The negative-half scale
coincides with the positive-half scale, whose exponent has an additional factor
`1 / 2`. -/
theorem ldpStableNegativeHalfScale_eq_positiveHalfScale :
    negativeHalfLdpScale = ldpStableHalfScale :=
  ldpStableHalfScale_eq_negativeHalfLdpScale.symm

/-- Helper toward Theorem 1.6; not a paper result. Every law satisfying the
existing actual negative-half convergence predicate retains the symmetric
negative-half cutoff marginals. -/
theorem ldpBusemannNegativeHalfLimit_cutoff
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : LdpBusemannWholeLineNegativeHalfConverges ν) (N : ℕ) :
    (ν.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) =
      negativeHalfLdpCutoffLimit hsymLdp_ldpCode N := by
  obtain ⟨ν₀, hν₀, hcut⟩ :=
    ldpBusemannWholeLineNegativeHalfConverges_of_sym hsymLdp_ldpCode
  have heq : ν = ν₀ := tendsto_nhds_unique hν.2 hν₀.2
  rw [heq]
  exact hcut N

/-- Helper toward Theorem 1.6; not a paper result. The selected raw negative
window limit has the symmetric stable FDDs at every deterministic time. -/
theorem ldpBusemannNegativeHalfWindowLimit_fdd
    {T : ℝ} (hT : 0 < T) {m : ℕ} {t : ℕ → J1Window T}
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) :
    let ν := Classical.choose
      (negativeHalfLdpWindow_tendsto_of_sym hsymLdp_ldpCode hT)
    ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m),
        charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
          (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((negativeHalfLdpScale : ℂ) * (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
      ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
        (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  dsimp only
  obtain ⟨L, hchar, hL⟩ := negativeHalfLdpWindow_fdd_of_sym
    hsymLdp_ldpCode hT ht0 ht
  refine ⟨L, hchar, ?_⟩
  have hν := (Classical.choose_spec
    (negativeHalfLdpWindow_tendsto_of_sym hsymLdp_ldpCode hT)).1
  have hmap := tendsto_map_windowEvalVec _ _ hν
    (fun i : Fin m => t (i.val + 1)) (fun i hi => by
      by_cases hzero : (t (i.val + 1) : ℝ) = 0
      · have heq : t (i.val + 1) = (⟨0, le_rfl, hT.le⟩ : J1Window T) :=
          Subtype.ext hzero
        rw [heq]
        exact DirectedDistances.Probability.zero_mem_continuityTimes
          (T := T) (hT := hT)
          (μ := (Classical.choose (negativeHalfLdpWindow_tendsto_of_sym
            hsymLdp_ldpCode hT) : ProbabilityMeasure (J1WindowD T hT)))
      · have hpos : 0 < (t (i.val + 1) : ℝ) :=
          lt_of_le_of_ne (t (i.val + 1)).property.1 (Ne.symm hzero)
        exact negativeHalfLdpWindow_limit_continuousAt hsymLdp_ldpCode hT
          (t (i.val + 1)) hpos hi)
  exact tendsto_nhds_unique hmap hL

/-- Helper toward Theorem 1.6; not a paper result. Joint deterministic
negative-half evaluations of any actual limit are the corresponding selected
raw-window evaluations. -/
theorem ldpBusemannNegativeHalfLimit_evalVec_law
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : LdpBusemannWholeLineNegativeHalfConverges ν)
    (N : ℕ) {m : ℕ} (s : Fin m → Set.Ici (0 : ℝ))
    (hs : ∀ j, (s j : ℝ) ≤ (N : ℝ)) :
    (ν : Measure CadlagLocalZero).map (fun x j => x.1.1 (s j)) =
      ((Classical.choose (negativeHalfLdpWindow_tendsto_of_sym
        hsymLdp_ldpCode
        (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) :
          ProbabilityMeasure
            (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
              Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
        (windowEvalVec (fun j => ⟨s j, (s j).property, by
          have := hs j; push_cast; linarith⟩)) := by
  let i : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
  let sN : Fin m → J1Window ((i.val : ℝ) + 1) := fun j =>
    ⟨s j, (s j).property, by have := hs j; dsimp [i]; linarith⟩
  let e : LocalCutoffTuple N → (Fin m → ℝ) :=
    fun x j => (x i).path.1 (sN j)
  have he : Measurable e := Measurable.of_eval fun j =>
    (measurable_j1WindowD_eval (by positivity) (sN j)).comp
      (measurable_pi_apply i)
  have hleft : (fun x : CadlagLocalZero => e (finiteCutoffWindows N x.1)) =
      (fun x j => x.1.1 (s j)) := by
    funext x j
    change x.1.1 (s j) * localCutoff N (s j) = x.1.1 (s j)
    rw [localCutoff_eq_one N (s j) (hs j), mul_one]
  have hright :
      (fun x : J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity) =>
        e (positiveHalfCutoffFactor N x)) =
      windowEvalVec (fun j => ⟨s j, (s j).property, by
        have := hs j; push_cast; linarith⟩) := by
    funext x j
    change x.path.1 _ * localCutoff N (s j) = x.path.1 _
    rw [localCutoff_eq_one N (s j) (hs j), mul_one]
    rfl
  have hcut := congrArg
      (fun p : ProbabilityMeasure (LocalCutoffTuple N) =>
        (p : Measure (LocalCutoffTuple N)).map e)
      (ldpBusemannNegativeHalfLimit_cutoff hν N)
  change (((ν : Measure CadlagLocalZero).map
      (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N)).map e =
    (((Classical.choose (negativeHalfLdpWindow_tendsto_of_sym
      hsymLdp_ldpCode (by positivity)) :
        ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
          Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
            (positiveHalfCutoffFactor N)).map e at hcut
  rw [Measure.map_map he (finiteCutoffWindows_measurable N),
    Measure.map_map (he.comp (finiteCutoffWindows_measurable N))
      measurable_subtype_coe,
    Measure.map_map he (measurable_positiveHalfCutoffFactor N)] at hcut
  simpa only [Function.comp_def, hleft, hright] using hcut

/-- Helper toward Theorem 1.6; not a paper result. Every ordered partition
of an actual LDP negative-half limit has the symmetric stable joint increment
characteristic function, including repeated times and the empty partition. -/
theorem ldpBusemannNegativeHalfLimit_partition
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : LdpBusemannWholeLineNegativeHalfConverges ν)
    (k : ℕ) (t : ℕ → Set.Ici (0 : ℝ)) (ht0 : (t 0 : ℝ) = 0)
    (ht : Monotone t) (u : Fin k → ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      (((∑ j : Fin k, u j *
        (x.1.1 (t (j.val + 1)) - x.1.1 (t j.val)) : ℝ) : ℂ) * Complex.I)
        ∂(ν : Measure CadlagLocalZero)) =
      ∏ j : Fin k, Complex.exp
        (-((((t (j.val + 1) : ℝ) - (t j.val : ℝ) : ℝ) : ℂ) *
          ((negativeHalfLdpScale : ℂ) *
            (|u j| ^ (2 / 3 : ℝ) : ℝ)))) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (t k : ℝ)
  let T : ℝ := ((N + 2 : ℕ) : ℝ)
  have hT : 0 < T := by dsimp [T]; positivity
  let tw : ℕ → J1Window T := fun j =>
    ⟨t (min j k), (t (min j k)).property, by
      have h : (t (min j k) : ℝ) ≤ (t k : ℝ) := ht (Nat.min_le_right j k)
      change (t (min j k) : ℝ) ≤ T
      dsimp [T]; push_cast; linarith⟩
  have htw0 : (tw 0 : ℝ) = 0 := by simpa only [tw, Nat.zero_min] using ht0
  have htw : Monotone tw := fun i j hij => ht (min_le_min_right k hij)
  obtain ⟨L, hchar, hL⟩ :=
    ldpBusemannNegativeHalfWindowLimit_fdd hT htw0 htw
  have heval := ldpBusemannNegativeHalfLimit_evalVec_law hν N
    (fun j : Fin k => t (j.val + 1)) (fun j =>
      (show (t (j.val + 1) : ℝ) ≤ (t k : ℝ) from
        ht (show j.val + 1 ≤ k by omega)).trans hN)
  have htimes : (fun j : Fin k =>
      (⟨t (j.val + 1), (t (j.val + 1)).property, by
        have h := (show (t (j.val + 1) : ℝ) ≤ (t k : ℝ) from
          ht (show j.val + 1 ≤ k by omega)).trans hN
        dsimp [T]; push_cast; linarith⟩ : J1Window T)) =
        (fun j : Fin k => tw (j.val + 1)) := by
    funext j
    apply Subtype.ext
    simp only [tw, Nat.min_eq_left (show j.val + 1 ≤ k by omega)]
  rw [htimes] at heval
  have hcum : (ν : Measure CadlagLocalZero).map
      (fun (x : CadlagLocalZero) (j : Fin k) => x.1.1 (t (j.val + 1))) =
        (((L.map (cumulativeSum (k := k))).map WithLp.ofLp) :
          Measure (Fin k → ℝ)) :=
    heval.trans (congrArg ProbabilityMeasure.toMeasure hL)
  have hinc := congrArg (fun p : Measure (Fin k → ℝ) =>
    p.map (stableHalfIncrementMap (k := k))) hcum
  simp only [ProbabilityMeasure.toMeasure_map] at hinc
  rw [stableHalfIncrementMap_cumulativeSum_law,
    Measure.map_map (stableHalfIncrementMap (k := k)).measurable
      (Measurable.of_eval fun j => measurable_ldpStableHalfEval _)] at hinc
  have hz (x : CadlagLocalZero) : x.1.1 (t 0) = 0 := by
    have he : t 0 = (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ)) := Subtype.ext ht0
    rw [he, x.property]
  rw [← stableHalfIncrementMap_charFun (ν : Measure CadlagLocalZero)
    (fun x j => x.1.1 (t j)) (fun j => measurable_ldpStableHalfEval _) hz u]
  change charFun ((ν : Measure CadlagLocalZero).map
    (stableHalfIncrementMap ∘
      (fun (x : CadlagLocalZero) (j : Fin k) => x.1.1 (t (j.val + 1))))) _ = _
  rw [hinc, hchar]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [tw, Nat.min_eq_left (show j.val + 1 ≤ k by omega),
    Nat.min_eq_left (show j.val ≤ k by omega)]

/-- Helper toward Theorem 1.6; not a paper result. For every nonnegative
deterministic time, the characteristic function of the negative-half increment
is `exp (-t * a * |u|^(2/3))`, where
`a = negativeHalfLdpScale = ((3 + ldpF ... 0) / 2)^(1/3)`; the positive-half
exponent uses half this same scale. -/
theorem ldpBusemannNegativeHalfLimit_single_increment
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : LdpBusemannWholeLineNegativeHalfConverges ν)
    (s : Set.Ici (0 : ℝ)) (u : ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      ((u : ℂ) *
        ((x.1.1 s - x.1.1 ⟨0, le_rfl⟩ : ℝ) : ℂ) * Complex.I)
        ∂(ν : Measure CadlagLocalZero)) =
      Complex.exp (-((s : ℂ) *
        ((negativeHalfLdpScale : ℂ) * (|u| ^ (2 / 3 : ℝ) : ℝ)))) := by
  let t : ℕ → Set.Ici (0 : ℝ) := fun j =>
    if j = 0 then ⟨0, le_rfl⟩ else s
  have ht0 : (t 0 : ℝ) = 0 := by simp only [t, ite_true]
  have ht : Monotone t := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      change (0 : ℝ) ≤ (t j : ℝ)
      exact (t j).property
    · have hj : j ≠ 0 := by omega
      simp only [t, hi, hj, ite_false, le_refl]
  have h := ldpBusemannNegativeHalfLimit_partition hν 1 t ht0 ht
    (fun _ => u)
  simpa [t] using h

/-- Helper toward Theorem 1.6; not a paper result. The characteristic
function of the negative-half increment has the explicit symmetric stable
exponent. -/
theorem ldpBusemannNegativeHalfLimit_charFun
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : LdpBusemannWholeLineNegativeHalfConverges ν)
    (s : Set.Ici (0 : ℝ)) (u : ℝ) :
    charFun ((ν : Measure CadlagLocalZero).map
      (fun x => x.1.1 s - x.1.1 ⟨0, le_rfl⟩)) u =
      Complex.exp (-((s : ℂ) *
        ((negativeHalfLdpScale : ℂ) * (|u| ^ (2 / 3 : ℝ) : ℝ)))) := by
  have hm : Measurable (fun x : CadlagLocalZero =>
      x.1.1 s - x.1.1 (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ))) :=
    (measurable_ldpStableHalfEval s).sub
      (measurable_ldpStableHalfEval ⟨0, le_rfl⟩)
  rw [charFun_apply_real,
    integral_map hm.aemeasurable (by fun_prop)]
  exact ldpBusemannNegativeHalfLimit_single_increment hν s u

end DirectedDistances.Recursive

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result. The SDP symmetric
negative-half coefficient is the full scale proved by its transform expansion,
with explicit tail normalization `sdpG(-1)^(2/3)`; the positive-half exponent
uses half this same scale. -/
theorem sdpStableNegativeHalfScale_eq_explicit :
    negativeHalfSdpScale =
      (SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion (-1)) ^
        (2 / 3 : ℝ) := by
  rw [← sdpStableHalfScale_eq_negativeHalfSdpScale]
  rfl

/-- Helper toward Theorem 1.6; not a paper result. The SDP negative-half scale
is the positive-half scale, whose characteristic exponent has factor `1 / 2`. -/
theorem sdpStableNegativeHalfScale_eq_positiveHalfScale :
    negativeHalfSdpScale = sdpStableHalfScale :=
  sdpStableHalfScale_eq_negativeHalfSdpScale.symm

/-- Helper toward Theorem 1.6; not a paper result. Every law satisfying the
existing actual SDP negative-half convergence predicate retains the symmetric
negative-half cutoff marginals. -/
theorem sdpBusemannNegativeHalfLimit_cutoff
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν) (N : ℕ) :
    (ν.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) =
      negativeHalfSdpCutoffLimit hsymSdp_sdpCode N := by
  obtain ⟨ν₀, hν₀, hcut⟩ :=
    sdpBusemannWholeLineNegativeHalfConverges_of_sym hsymSdp_sdpCode
  have heq : ν = ν₀ := tendsto_nhds_unique hν.2 hν₀.2
  rw [heq]
  exact hcut N

/-- Helper toward Theorem 1.6; not a paper result. The selected raw negative
window limit has the symmetric stable FDDs at every deterministic time. -/
theorem sdpBusemannNegativeHalfWindowLimit_fdd
    {T : ℝ} (hT : 0 < T) {m : ℕ} {t : ℕ → J1Window T}
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) :
    let ν := Classical.choose
      (negativeHalfSdpWindow_tendsto_of_sym hsymSdp_sdpCode hT)
    ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m),
        charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
          (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((negativeHalfSdpScale : ℂ) * (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
      ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
        (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  dsimp only
  obtain ⟨L, hchar, hL⟩ := negativeHalfSdpWindow_fdd_of_sym
    hsymSdp_sdpCode hT ht0 ht
  refine ⟨L, hchar, ?_⟩
  have hν := (Classical.choose_spec
    (negativeHalfSdpWindow_tendsto_of_sym hsymSdp_sdpCode hT)).1
  have hmap := tendsto_map_windowEvalVec _ _ hν
    (fun i : Fin m => t (i.val + 1)) (fun i hi => by
      by_cases hzero : (t (i.val + 1) : ℝ) = 0
      · have heq : t (i.val + 1) = (⟨0, le_rfl, hT.le⟩ : J1Window T) :=
          Subtype.ext hzero
        rw [heq]
        exact DirectedDistances.Probability.zero_mem_continuityTimes
          (T := T) (hT := hT)
          (μ := (Classical.choose (negativeHalfSdpWindow_tendsto_of_sym
            hsymSdp_sdpCode hT) : ProbabilityMeasure (J1WindowD T hT)))
      · have hpos : 0 < (t (i.val + 1) : ℝ) :=
          lt_of_le_of_ne (t (i.val + 1)).property.1 (Ne.symm hzero)
        exact negativeHalfSdpWindow_limit_continuousAt hsymSdp_sdpCode hT
          (t (i.val + 1)) hpos hi)
  exact tendsto_nhds_unique hmap hL

/-- Helper toward Theorem 1.6; not a paper result. Joint deterministic
negative-half evaluations of any actual limit are the corresponding selected
raw-window evaluations. -/
theorem sdpBusemannNegativeHalfLimit_evalVec_law
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν)
    (N : ℕ) {m : ℕ} (s : Fin m → Set.Ici (0 : ℝ))
    (hs : ∀ j, (s j : ℝ) ≤ (N : ℝ)) :
    (ν : Measure CadlagLocalZero).map (fun x j => x.1.1 (s j)) =
      ((Classical.choose (negativeHalfSdpWindow_tendsto_of_sym
        hsymSdp_sdpCode
        (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) :
          ProbabilityMeasure
            (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
              Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
        (windowEvalVec (fun j => ⟨s j, (s j).property, by
          have := hs j; push_cast; linarith⟩)) := by
  let i : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
  let sN : Fin m → J1Window ((i.val : ℝ) + 1) := fun j =>
    ⟨s j, (s j).property, by have := hs j; dsimp [i]; linarith⟩
  let e : LocalCutoffTuple N → (Fin m → ℝ) :=
    fun x j => (x i).path.1 (sN j)
  have he : Measurable e := Measurable.of_eval fun j =>
    (measurable_j1WindowD_eval (by positivity) (sN j)).comp
      (measurable_pi_apply i)
  have hleft : (fun x : CadlagLocalZero => e (finiteCutoffWindows N x.1)) =
      (fun x j => x.1.1 (s j)) := by
    funext x j
    change x.1.1 (s j) * localCutoff N (s j) = x.1.1 (s j)
    rw [localCutoff_eq_one N (s j) (hs j), mul_one]
  have hright :
      (fun x : J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity) =>
        e (positiveHalfCutoffFactor N x)) =
      windowEvalVec (fun j => ⟨s j, (s j).property, by
        have := hs j; push_cast; linarith⟩) := by
    funext x j
    change x.path.1 _ * localCutoff N (s j) = x.path.1 _
    rw [localCutoff_eq_one N (s j) (hs j), mul_one]
    rfl
  have hcut := congrArg
      (fun p : ProbabilityMeasure (LocalCutoffTuple N) =>
        (p : Measure (LocalCutoffTuple N)).map e)
      (sdpBusemannNegativeHalfLimit_cutoff hν N)
  change (((ν : Measure CadlagLocalZero).map
      (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N)).map e =
    (((Classical.choose (negativeHalfSdpWindow_tendsto_of_sym
      hsymSdp_sdpCode (by positivity)) :
        ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
          Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
            (positiveHalfCutoffFactor N)).map e at hcut
  rw [Measure.map_map he (finiteCutoffWindows_measurable N),
    Measure.map_map (he.comp (finiteCutoffWindows_measurable N))
      measurable_subtype_coe,
    Measure.map_map he (measurable_positiveHalfCutoffFactor N)] at hcut
  simpa only [Function.comp_def, hleft, hright] using hcut

/-- Helper toward Theorem 1.6; not a paper result. Every ordered partition
of an actual SDP negative-half limit has the symmetric stable joint increment
characteristic function, including repeated times and the empty partition. -/
theorem sdpBusemannNegativeHalfLimit_partition
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν)
    (k : ℕ) (t : ℕ → Set.Ici (0 : ℝ)) (ht0 : (t 0 : ℝ) = 0)
    (ht : Monotone t) (u : Fin k → ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      (((∑ j : Fin k, u j *
        (x.1.1 (t (j.val + 1)) - x.1.1 (t j.val)) : ℝ) : ℂ) * Complex.I)
        ∂(ν : Measure CadlagLocalZero)) =
      ∏ j : Fin k, Complex.exp
        (-((((t (j.val + 1) : ℝ) - (t j.val : ℝ) : ℝ) : ℂ) *
          ((negativeHalfSdpScale : ℂ) *
            (|u j| ^ (4 / 3 : ℝ) : ℝ)))) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (t k : ℝ)
  let T : ℝ := ((N + 2 : ℕ) : ℝ)
  have hT : 0 < T := by dsimp [T]; positivity
  let tw : ℕ → J1Window T := fun j =>
    ⟨t (min j k), (t (min j k)).property, by
      have h : (t (min j k) : ℝ) ≤ (t k : ℝ) := ht (Nat.min_le_right j k)
      change (t (min j k) : ℝ) ≤ T
      dsimp [T]; push_cast; linarith⟩
  have htw0 : (tw 0 : ℝ) = 0 := by simpa only [tw, Nat.zero_min] using ht0
  have htw : Monotone tw := fun i j hij => ht (min_le_min_right k hij)
  obtain ⟨L, hchar, hL⟩ :=
    sdpBusemannNegativeHalfWindowLimit_fdd hT htw0 htw
  have heval := sdpBusemannNegativeHalfLimit_evalVec_law hν N
    (fun j : Fin k => t (j.val + 1)) (fun j =>
      (show (t (j.val + 1) : ℝ) ≤ (t k : ℝ) from
        ht (show j.val + 1 ≤ k by omega)).trans hN)
  have htimes : (fun j : Fin k =>
      (⟨t (j.val + 1), (t (j.val + 1)).property, by
        have h := (show (t (j.val + 1) : ℝ) ≤ (t k : ℝ) from
          ht (show j.val + 1 ≤ k by omega)).trans hN
        dsimp [T]; push_cast; linarith⟩ : J1Window T)) =
        (fun j : Fin k => tw (j.val + 1)) := by
    funext j
    apply Subtype.ext
    simp only [tw, Nat.min_eq_left (show j.val + 1 ≤ k by omega)]
  rw [htimes] at heval
  have hcum : (ν : Measure CadlagLocalZero).map
      (fun (x : CadlagLocalZero) (j : Fin k) => x.1.1 (t (j.val + 1))) =
        (((L.map (cumulativeSum (k := k))).map WithLp.ofLp) :
          Measure (Fin k → ℝ)) :=
    heval.trans (congrArg ProbabilityMeasure.toMeasure hL)
  have hinc := congrArg (fun p : Measure (Fin k → ℝ) =>
    p.map (stableHalfIncrementMap (k := k))) hcum
  simp only [ProbabilityMeasure.toMeasure_map] at hinc
  rw [stableHalfIncrementMap_cumulativeSum_law,
    Measure.map_map (stableHalfIncrementMap (k := k)).measurable
      (Measurable.of_eval fun j => measurable_ldpStableHalfEval _)] at hinc
  have hz (x : CadlagLocalZero) : x.1.1 (t 0) = 0 := by
    have he : t 0 = (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ)) := Subtype.ext ht0
    rw [he, x.property]
  rw [← stableHalfIncrementMap_charFun (ν : Measure CadlagLocalZero)
    (fun x j => x.1.1 (t j)) (fun j => measurable_ldpStableHalfEval _) hz u]
  change charFun ((ν : Measure CadlagLocalZero).map
    (stableHalfIncrementMap ∘
      (fun (x : CadlagLocalZero) (j : Fin k) => x.1.1 (t (j.val + 1))))) _ = _
  rw [hinc, hchar]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [tw, Nat.min_eq_left (show j.val + 1 ≤ k by omega),
    Nat.min_eq_left (show j.val ≤ k by omega)]

/-- Helper toward Theorem 1.6; not a paper result. For every nonnegative
deterministic time, the characteristic function of the SDP negative-half
increment is `exp (-t * b * |u|^(4/3))`, where
`b = negativeHalfSdpScale = sdpG(-1)^(2/3)`. -/
theorem sdpBusemannNegativeHalfLimit_single_increment
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν)
    (s : Set.Ici (0 : ℝ)) (u : ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      ((u : ℂ) *
        ((x.1.1 s - x.1.1 ⟨0, le_rfl⟩ : ℝ) : ℂ) * Complex.I)
        ∂(ν : Measure CadlagLocalZero)) =
      Complex.exp (-((s : ℂ) *
        ((negativeHalfSdpScale : ℂ) * (|u| ^ (4 / 3 : ℝ) : ℝ)))) := by
  let t : ℕ → Set.Ici (0 : ℝ) := fun j =>
    if j = 0 then ⟨0, le_rfl⟩ else s
  have ht0 : (t 0 : ℝ) = 0 := by simp only [t, ite_true]
  have ht : Monotone t := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      change (0 : ℝ) ≤ (t j : ℝ)
      exact (t j).property
    · have hj : j ≠ 0 := by omega
      simp only [t, hi, hj, ite_false, le_refl]
  have h := sdpBusemannNegativeHalfLimit_partition hν 1 t ht0 ht
    (fun _ => u)
  simpa [t] using h

/-- Helper toward Theorem 1.6; not a paper result. The characteristic
function of the SDP negative-half increment has the explicit symmetric stable
exponent. -/
theorem sdpBusemannNegativeHalfLimit_charFun
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν)
    (s : Set.Ici (0 : ℝ)) (u : ℝ) :
    charFun ((ν : Measure CadlagLocalZero).map
      (fun x => x.1.1 s - x.1.1 ⟨0, le_rfl⟩)) u =
      Complex.exp (-((s : ℂ) *
        ((negativeHalfSdpScale : ℂ) * (|u| ^ (4 / 3 : ℝ) : ℝ)))) := by
  have hm : Measurable (fun x : CadlagLocalZero =>
      x.1.1 s - x.1.1 (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ))) :=
    (measurable_ldpStableHalfEval s).sub
      (measurable_ldpStableHalfEval ⟨0, le_rfl⟩)
  rw [charFun_apply_real,
    integral_map hm.aemeasurable (by fun_prop)]
  exact sdpBusemannNegativeHalfLimit_single_increment hν s u

end DirectedDistances.Recursive
