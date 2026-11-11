/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.BusemannLdpUnconditional
public import DirectedDistances.Recursive.BusemannSdpUnconditional
import all DirectedDistances.Recursive.BusemannPositiveHalfLaw
import all DirectedDistances.Recursive.BusemannPositiveHalfLawSDP
import all DirectedDistances.Probability.SkorokhodJ1LocalLawCriterion
import all DirectedDistances.Probability.SkorokhodJ1LocalPositive
import all DirectedDistances.Probability.SkewedStableProcessFdd

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result. Every limit of the actual
positive-half laws retains the selected finite cutoff marginals. -/
theorem ldpBusemannPositiveHalfLimit_cutoff
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ)) (N : ℕ) :
    (μ.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) =
      ldpBusemannPositiveCutoffLimit ldpIncrements_iIndep_proved hsymLdp_ldpCode N := by
  obtain ⟨ν, hν, hcut⟩ := ldpBusemannWholeLinePositiveHalfLaw_tendsto_ldpCode
  have heq : μ = ν := tendsto_nhds_unique hμ hν
  rw [heq]
  exact hcut N

/-- Helper toward Theorem 1.6; not a paper result. The selected window limit has
the established FDD law at every deterministic time, including the endpoint. -/
theorem ldpBusemannWindowLimit_fdd
    {T : ℝ} (hT : 0 < T) {m : ℕ} {t : ℕ → J1Window T}
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) :
    let ν := Classical.choose
      (ldp_busemann_window_tendsto ldpIncrements_iIndep_proved hsymLdp_ldpCode hT)
    let a : ℝ := ((3 + ldpF iidCodeMeasure busemannLDPMeasurableVersion 0) / 2) ^
      (1 / 3 : ℝ)
    let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
    0 < a ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m),
        charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
          (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
      ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
        (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  dsimp only
  obtain ⟨ha, L, hchar, hL⟩ := ldp_busemann_window_fdd
    ldpIncrements_iIndep_proved hsymLdp_ldpCode hT ht0 ht
  refine ⟨ha, L, hchar, ?_⟩
  have hν := (Classical.choose_spec
    (ldp_busemann_window_tendsto ldpIncrements_iIndep_proved hsymLdp_ldpCode hT)).1
  have hmap := tendsto_map_windowEvalVec _ _ hν
    (fun i : Fin m => t (i.val + 1)) (fun i hi =>
      ldp_busemann_window_fixed_time_continuous
        ldpIncrements_iIndep_proved hsymLdp_ldpCode hT _ hi)
  exact tendsto_nhds_unique hmap hL

/-- Helper toward Theorem 1.6; not a paper result. A deterministic evaluation
of any positive-half limit agrees in law with the same evaluation of its selected
raw window. The cutoff is exactly one at the evaluation time. -/
theorem ldpBusemannPositiveHalfLimit_eval_law
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (N : ℕ) (s : Set.Ici (0 : ℝ)) (hs : (s : ℝ) ≤ (N : ℝ)) :
    (μ : Measure CadlagLocalZero).map (fun x => x.1.1 s) =
      ((Classical.choose (ldp_busemann_window_tendsto
        ldpIncrements_iIndep_proved hsymLdp_ldpCode
        (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) :
          ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
            Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
        (fun x => x.path.1 ⟨s, s.property, by push_cast; linarith⟩) := by
  let i : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
  let sN : J1Window ((i.val : ℝ) + 1) :=
    ⟨s, s.property, by dsimp [i]; linarith⟩
  let e : LocalCutoffTuple N → ℝ := fun x => (x i).path.1 sN
  have he : Measurable e :=
    (measurable_j1WindowD_eval (by positivity) sN).comp (measurable_pi_apply i)
  have hleft : (fun x : CadlagLocalZero =>
      e (finiteCutoffWindows N x.1)) = (fun x => x.1.1 s) := by
    funext x
    change x.1.1 s * localCutoff N s = x.1.1 s
    rw [localCutoff_eq_one N s hs, mul_one]
  have hright : (fun x : J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity) =>
      e (positiveHalfCutoffFactor N x)) =
        (fun x => x.path.1 ⟨s, s.property, by push_cast; linarith⟩) := by
    funext x
    change x.path.1 _ * localCutoff N s = x.path.1 _
    rw [localCutoff_eq_one N s hs, mul_one]
    rfl
  have hcut := congrArg (fun p : ProbabilityMeasure (LocalCutoffTuple N) =>
    (p : Measure (LocalCutoffTuple N)).map e)
      (ldpBusemannPositiveHalfLimit_cutoff hμ N)
  change (((μ : Measure CadlagLocalZero).map
    (Subtype.val : CadlagLocalZero → CadlagLocal)).map (finiteCutoffWindows N)).map e =
    (((Classical.choose (ldp_busemann_window_tendsto
      ldpIncrements_iIndep_proved hsymLdp_ldpCode (by positivity)) :
        ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
          Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
            (positiveHalfCutoffFactor N)).map e at hcut
  rw [Measure.map_map he (finiteCutoffWindows_measurable N),
    Measure.map_map (he.comp (finiteCutoffWindows_measurable N)) measurable_subtype_coe,
    Measure.map_map he (measurable_positiveHalfCutoffFactor N)] at hcut
  simpa only [Function.comp_def, hleft, hright] using hcut

/-- Helper toward Theorem 1.6; not a paper result. The shared scale from the
proved LDP transform expansion, also used by the symmetric negative half. -/
@[expose] noncomputable def ldpStableHalfScale : ℝ :=
  ((3 + ldpF iidCodeMeasure busemannLDPMeasurableVersion 0) / 2) ^ (1 / 3 : ℝ)

/-- Helper toward Theorem 1.6; not a paper result. The shared scale is positive. -/
theorem ldpStableHalfScale_pos : 0 < ldpStableHalfScale :=
  negativeHalfLdpScale_pos

/-- Helper toward Theorem 1.6; not a paper result. Both halves use the same scale. -/
theorem ldpStableHalfScale_eq_negativeHalfLdpScale :
    ldpStableHalfScale = negativeHalfLdpScale := rfl

/-- Helper toward Theorem 1.6; not a paper result. The positive-half exponent,
with characteristic coefficient `a/2` and the negative-subordinator sign. -/
@[expose] noncomputable def ldpStableHalfExponent (u : ℝ) : ℂ :=
  ((ldpStableHalfScale / 2 : ℝ) : ℂ) * (|u| ^ (2 / 3 : ℝ) : ℝ) *
    (1 + Complex.I * (Real.sqrt 3 : ℂ) *
      ((if 0 < u then (1 : ℝ) else if u < 0 then -1 else 0) : ℂ))

/-- Helper toward Theorem 1.6; not a paper result. Exact conversion from the
block characteristic-function normalization to the signed exponent. -/
theorem ldpStableHalfExponent_eq (u : ℝ) :
    ((if 0 ≤ u then
        ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (ldpStableHalfScale : ℂ)
      else star (((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 *
        (ldpStableHalfScale : ℂ))) * (|u| ^ (2 / 3 : ℝ) : ℝ)) =
      ldpStableHalfExponent u := by
  unfold ldpStableHalfExponent
  by_cases hu : u = 0
  · subst u
    simp [Real.zero_rpow, (by norm_num : (2 / 3 : ℝ) ≠ 0)]
  · rcases lt_or_gt_of_ne hu with hu | hu
    · simp [not_le_of_gt hu, not_lt.mpr hu.le, hu]
      ring
    · simp [hu.le, hu]
      ring

private theorem charFun_map_finOne_coord
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) (u : ℝ) :
    charFun (μ.map (fun z => z (0 : Fin 1))) u =
      charFun μ (EuclideanSpace.single (0 : Fin 1) u) := by
  let p : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (β := fun _ : Fin 1 => ℝ) 0
  have hp : (fun z : EuclideanSpace ℝ (Fin 1) => z (0 : Fin 1)) = p := rfl
  rw [hp, charFun_map_eq_charFunDual_smul]
  have hdual : u • p =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace.single (0 : Fin 1) u) := by
    ext z
    simp [p, EuclideanSpace.inner_single_left]
  rw [hdual, ← charFun_eq_charFunDual_toDualMap]

/-- Helper toward Theorem 1.6; not a paper result. The selected raw window has
the claimed single-time characteristic function at every deterministic time. -/
theorem ldpBusemannWindowLimit_eval_charFun
    {T : ℝ} (hT : 0 < T) (s : J1Window T) (u : ℝ) :
    let ν := Classical.choose
      (ldp_busemann_window_tendsto ldpIncrements_iIndep_proved hsymLdp_ldpCode hT)
    charFun ((ν : Measure (J1WindowD T hT)).map (fun x => x.path.1 s)) u =
      Complex.exp (-((s : ℂ) * ldpStableHalfExponent u)) := by
  classical
  let t : ℕ → J1Window T := fun j => if j = 0 then ⟨0, le_rfl, hT.le⟩ else s
  have ht0 : (t 0 : ℝ) = 0 := by simp only [t, ite_true]
  have ht : Monotone t := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      change (0 : ℝ) ≤ (t j : ℝ)
      exact (t j).property.1
    · have hj : j ≠ 0 := by omega
      simp only [t, hi, hj, ite_false, le_refl]
  obtain ⟨_, L, hchar, heval⟩ := ldpBusemannWindowLimit_fdd hT (m := 1) ht0 ht
  have heval' := congrArg (fun p : ProbabilityMeasure (Fin 1 → ℝ) =>
    (p : Measure (Fin 1 → ℝ)).map (fun z => z 0)) heval
  simp only [ProbabilityMeasure.toMeasure_map] at heval'
  rw [Measure.map_map (by fun_prop) (measurable_windowEvalVec _),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at heval'
  have hcum (z : EuclideanSpace ℝ (Fin 1)) :
      WithLp.ofLp (cumulativeSum z) 0 = z 0 := by
    rw [cumulativeSum_apply]
    have hIic : Finset.Iic (0 : Fin 1) = {0} := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      omega
    rw [hIic, Finset.sum_singleton]
  dsimp only [Function.comp_def] at heval'
  simp only [windowEvalVec, t, Fin.val_zero, zero_add, Nat.one_ne_zero,
    ite_false] at heval'
  simp_rw [hcum] at heval'
  dsimp only
  rw [heval', charFun_map_finOne_coord]
  have h : charFun (L : Measure _) (EuclideanSpace.single (0 : Fin 1) u) =
      Complex.exp (-((s : ℂ) *
        ((if 0 ≤ u then
          ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (ldpStableHalfScale : ℂ)
        else star (((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 *
          (ldpStableHalfScale : ℂ))) * (|u| ^ (2 / 3 : ℝ) : ℝ)))) := by
    simpa [t, ldpStableHalfScale] using hchar (EuclideanSpace.single (0 : Fin 1) u)
  rw [h]
  change Complex.exp (-((s : ℂ) * _)) = _
  rw [ldpStableHalfExponent_eq]

/-- Helper toward Theorem 1.6; not a paper result. For any limit of the actual
LDP positive-half laws, the characteristic function at every nonnegative
deterministic time is `exp (-t Ψ(u))`, with the explicit shared scale above. -/
theorem ldpBusemannPositiveHalfLimit_eval_charFun
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (s : Set.Ici (0 : ℝ)) (u : ℝ) :
    charFun ((μ : Measure CadlagLocalZero).map (fun x => x.1.1 s)) u =
      Complex.exp (-((s : ℂ) * ldpStableHalfExponent u)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (s : ℝ)
  rw [ldpBusemannPositiveHalfLimit_eval_law hμ N s hN]
  exact ldpBusemannWindowLimit_eval_charFun (by positivity) _ u

/-- Helper toward Theorem 1.6; not a paper result. Fixed-time evaluation on the
zero-origin half-line carrier is Borel measurable, by a cutoff coordinate. -/
theorem measurable_ldpStableHalfEval (s : Set.Ici (0 : ℝ)) :
    Measurable (fun x : CadlagLocalZero => x.1.1 s) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (s : ℝ)
  let i : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
  let sN : J1Window ((i.val : ℝ) + 1) :=
    ⟨s, s.property, by dsimp [i]; linarith⟩
  have hm := (measurable_j1WindowD_eval (by positivity) sN).comp
    ((measurable_pi_apply i).comp
      ((finiteCutoffWindows_measurable N).comp
        (measurable_subtype_coe : Measurable
          (Subtype.val : CadlagLocalZero → CadlagLocal))))
  convert hm using 1
  funext x
  change x.1.1 s = x.1.1 s * localCutoff N s
  rw [localCutoff_eq_one N s hN, mul_one]

/-- Helper toward Theorem 1.6; not a paper result. The single-time increment
formula, written as expectation under any actual positive-half limit. The sign
in `ldpStableHalfExponent` is zero at zero and ±1 on the two open half-lines. -/
theorem ldpBusemannPositiveHalfLimit_single_increment
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (s : Set.Ici (0 : ℝ)) (u : ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      ((u : ℂ) * ((x.1.1 s - x.1.1 ⟨0, le_rfl⟩ : ℝ) : ℂ) * Complex.I)
        ∂(μ : Measure CadlagLocalZero)) =
      Complex.exp (-((s : ℂ) * ldpStableHalfExponent u)) := by
  have h := ldpBusemannPositiveHalfLimit_eval_charFun hμ s u
  rw [charFun_apply_real,
    integral_map (measurable_ldpStableHalfEval s).aemeasurable (by fun_prop)] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [x.property, sub_zero]

/-- Helper toward Theorem 1.6; not a paper result. Joint deterministic evaluations
are transported together through a single retained cutoff marginal. -/
theorem ldpBusemannPositiveHalfLimit_evalVec_law
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (N : ℕ) {m : ℕ} (s : Fin m → Set.Ici (0 : ℝ))
    (hs : ∀ j, (s j : ℝ) ≤ (N : ℝ)) :
    (μ : Measure CadlagLocalZero).map (fun x j => x.1.1 (s j)) =
      ((Classical.choose (ldp_busemann_window_tendsto
        ldpIncrements_iIndep_proved hsymLdp_ldpCode
        (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) :
          ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
            Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
        (windowEvalVec (fun j => ⟨s j, (s j).property, by
          have := hs j; push_cast; linarith⟩)) := by
  let i : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
  let sN : Fin m → J1Window ((i.val : ℝ) + 1) := fun j =>
    ⟨s j, (s j).property, by have := hs j; dsimp [i]; linarith⟩
  let e : LocalCutoffTuple N → (Fin m → ℝ) := fun x j => (x i).path.1 (sN j)
  have he : Measurable e := Measurable.of_eval fun j =>
    (measurable_j1WindowD_eval (by positivity) (sN j)).comp (measurable_pi_apply i)
  have hleft : (fun x : CadlagLocalZero => e (finiteCutoffWindows N x.1)) =
      (fun x j => x.1.1 (s j)) := by
    funext x j
    change x.1.1 (s j) * localCutoff N (s j) = x.1.1 (s j)
    rw [localCutoff_eq_one N (s j) (hs j), mul_one]
  have hright : (fun x : J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity) =>
      e (positiveHalfCutoffFactor N x)) =
        windowEvalVec (fun j => ⟨s j, (s j).property, by
          have := hs j; push_cast; linarith⟩) := by
    funext x j
    change x.path.1 _ * localCutoff N (s j) = x.path.1 _
    rw [localCutoff_eq_one N (s j) (hs j), mul_one]
    rfl
  have hcut := congrArg (fun p : ProbabilityMeasure (LocalCutoffTuple N) =>
    (p : Measure (LocalCutoffTuple N)).map e)
      (ldpBusemannPositiveHalfLimit_cutoff hμ N)
  change (((μ : Measure CadlagLocalZero).map
    (Subtype.val : CadlagLocalZero → CadlagLocal)).map (finiteCutoffWindows N)).map e =
    (((Classical.choose (ldp_busemann_window_tendsto
      ldpIncrements_iIndep_proved hsymLdp_ldpCode (by positivity)) :
        ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
          Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
            (positiveHalfCutoffFactor N)).map e at hcut
  rw [Measure.map_map he (finiteCutoffWindows_measurable N),
    Measure.map_map (he.comp (finiteCutoffWindows_measurable N)) measurable_subtype_coe,
    Measure.map_map he (measurable_positiveHalfCutoffFactor N)] at hcut
  simpa only [Function.comp_def, hleft, hright] using hcut

/-- Helper toward Theorem 1.6; not a paper result. The continuous linear map
recovering consecutive increments from process values, with initial value zero. -/
@[expose] noncomputable def stableHalfIncrementMap {k : ℕ} :
    (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)
  exact e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj i -
      if h : i.val = 0 then 0 else ContinuousLinearMap.proj ⟨i.val - 1, by omega⟩)

/-- Helper toward Theorem 1.6; not a paper result. Coordinate formula for the
fixed linear increment map. -/
theorem stableHalfIncrementMap_apply {k : ℕ} (z : Fin k → ℝ) (i : Fin k) :
    stableHalfIncrementMap z i = z i -
      (if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩) := by
  by_cases hi : i.val = 0 <;> simp [stableHalfIncrementMap, hi]

/-- Helper toward Theorem 1.6; not a paper result. Cumulative summation is
inverted exactly, including the first coordinate and the empty vector. -/
theorem stableHalfIncrementMap_cumulativeSum {k : ℕ}
    (z : EuclideanSpace ℝ (Fin k)) :
    stableHalfIncrementMap (WithLp.ofLp (cumulativeSum z)) = z := by
  classical
  ext i
  rw [stableHalfIncrementMap_apply]
  by_cases hi : i.val = 0
  · rw [dite_eq_left hi, sub_zero]
    change cumulativeSum z i = z i
    rw [cumulativeSum_apply]
    have hI : Finset.Iic i = {i} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val]
      constructor
      · intro hj; apply Fin.ext; omega
      · intro hj; subst j; exact le_rfl
    rw [hI, Finset.sum_singleton]
  · rw [dite_eq_right hi]
    let p : Fin k := ⟨i.val - 1, by omega⟩
    change cumulativeSum z i - cumulativeSum z p = z i
    rw [cumulativeSum_apply, cumulativeSum_apply]
    have hI : Finset.Iic i = insert i (Finset.Iic p) := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val]
      constructor
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        · right; have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
          dsimp [p]; omega
      · rintro (rfl | hj)
        · exact le_rfl
        · dsimp [p] at hj; omega
    have hnot : i ∉ Finset.Iic p := by
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val]
      dsimp [p]; omega
    rw [hI, Finset.sum_insert hnot]
    ring

/-- Helper toward Theorem 1.6; not a paper result. Pushing a cumulative-vector
law through the fixed increment map recovers the original joint increment law. -/
theorem stableHalfIncrementMap_cumulativeSum_law {k : ℕ}
    (L : Measure (EuclideanSpace ℝ (Fin k))) :
    ((L.map (cumulativeSum (k := k))).map WithLp.ofLp).map
      (stableHalfIncrementMap (k := k)) = L := by
  rw [Measure.map_map (stableHalfIncrementMap (k := k)).measurable (by fun_prop),
    Measure.map_map ((stableHalfIncrementMap (k := k)).measurable.comp (by fun_prop))
      (cumulativeSum (k := k)).measurable]
  have heq : stableHalfIncrementMap ∘ WithLp.ofLp ∘ cumulativeSum =
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) :=
    funext stableHalfIncrementMap_cumulativeSum
  change L.map (stableHalfIncrementMap ∘ WithLp.ofLp ∘ cumulativeSum) = L
  rw [heq, Measure.map_id]

/-- Helper toward Theorem 1.6; not a paper result. The increment map on a
zero-origin sequence gives all consecutive differences. -/
theorem stableHalfIncrementMap_sequence {k : ℕ} (f : ℕ → ℝ) (hf : f 0 = 0)
    (i : Fin k) :
    stableHalfIncrementMap (fun j : Fin k => f (j.val + 1)) i =
      f (i.val + 1) - f i.val := by
  rw [stableHalfIncrementMap_apply]
  by_cases hi : i.val = 0
  · rw [dite_eq_left hi]
    simp only [hi, hf]
  · rw [dite_eq_right hi]
    have hp : i.val - 1 + 1 = i.val := by omega
    simp only [hp]

/-- Helper toward Theorem 1.6; not a paper result. A joint increment
characteristic function is the integral of the finite weighted increment sum. -/
theorem stableHalfIncrementMap_charFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℕ → ℝ) (hf : ∀ j, Measurable (fun x => f x j))
    (hzero : ∀ x, f x 0 = 0) {k : ℕ} (u : Fin k → ℝ) :
    charFun (P.map (fun x => stableHalfIncrementMap
      (fun j : Fin k => f x (j.val + 1)))) (WithLp.toLp 2 u) =
      ∫ x, Complex.exp (((∑ j : Fin k,
        u j * (f x (j.val + 1) - f x j.val) : ℝ) : ℂ) * Complex.I) ∂P := by
  have hm : Measurable (fun x => stableHalfIncrementMap
      (fun j : Fin k => f x (j.val + 1))) :=
    (stableHalfIncrementMap (k := k)).measurable.comp (Measurable.of_eval fun j => hf _)
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 3
  simp only [PiLp.inner_apply, stableHalfIncrementMap_sequence _ (hzero x),
    RCLike.inner_apply, conj_trivial]

/-- Helper toward Theorem 1.6; not a paper result. Every ordered partition
of the LDP positive-half limit has the stated joint increment exponent.
Repeated times and the empty partition are included. -/
theorem ldpBusemannPositiveHalfLimit_partition
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (k : ℕ) (t : ℕ → Set.Ici (0 : ℝ)) (ht0 : (t 0 : ℝ) = 0)
    (ht : Monotone t) (u : Fin k → ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      (((∑ j : Fin k, u j *
        (x.1.1 (t (j.val + 1)) - x.1.1 (t j.val)) : ℝ) : ℂ) * Complex.I)
        ∂(μ : Measure CadlagLocalZero)) =
      ∏ j : Fin k, Complex.exp
        (-((((t (j.val + 1) : ℝ) - (t j.val : ℝ) : ℝ) : ℂ) *
          ldpStableHalfExponent (u j))) := by
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
  obtain ⟨_, L, hchar, hL⟩ := ldpBusemannWindowLimit_fdd hT (m := k) htw0 htw
  have heval := ldpBusemannPositiveHalfLimit_evalVec_law hμ N
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
  have hcum : (μ : Measure CadlagLocalZero).map
      (fun (x : CadlagLocalZero) (j : Fin k) => x.1.1 (t (j.val + 1))) =
        (((L.map (cumulativeSum (k := k))).map WithLp.ofLp) :
          Measure (Fin k → ℝ)) := heval.trans (congrArg ProbabilityMeasure.toMeasure hL)
  have hinc := congrArg (fun p : Measure (Fin k → ℝ) =>
    p.map (stableHalfIncrementMap (k := k))) hcum
  simp only [ProbabilityMeasure.toMeasure_map] at hinc
  rw [stableHalfIncrementMap_cumulativeSum_law,
    Measure.map_map (stableHalfIncrementMap (k := k)).measurable
      (Measurable.of_eval fun j => measurable_ldpStableHalfEval _)] at hinc
  have hz (x : CadlagLocalZero) : x.1.1 (t 0) = 0 := by
    have he : t 0 = (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ)) := Subtype.ext ht0
    rw [he, x.property]
  rw [← stableHalfIncrementMap_charFun (μ : Measure CadlagLocalZero)
    (fun x j => x.1.1 (t j)) (fun j => measurable_ldpStableHalfEval _) hz u]
  change charFun ((μ : Measure CadlagLocalZero).map
    (stableHalfIncrementMap ∘ (fun (x : CadlagLocalZero) (j : Fin k) => x.1.1 (t (j.val + 1))))) _ = _
  rw [hinc, hchar]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [tw, Nat.min_eq_left (show j.val + 1 ≤ k by omega),
    Nat.min_eq_left (show j.val ≤ k by omega)]
  rw [show ((3 + ldpF iidCodeMeasure busemannLDPMeasurableVersion 0) / 2) ^
      (1 / 3 : ℝ) = ldpStableHalfScale from rfl, ldpStableHalfExponent_eq]

/-- Helper toward Theorem 1.6; not a paper result. The full finite-partition
formula, indexed by the supplied `k + 1` ordered times with initial time zero. -/
theorem ldpBusemannPositiveHalfLimit_partition_fin
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (k : ℕ) (t : Fin (k + 1) → Set.Ici (0 : ℝ))
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) (u : Fin k → ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      (((∑ j : Fin k, u j *
        (x.1.1 (t j.succ) - x.1.1 (t j.castSucc)) : ℝ) : ℂ) * Complex.I)
        ∂(μ : Measure CadlagLocalZero)) =
      ∏ j : Fin k, Complex.exp
        (-((((t j.succ : ℝ) - (t j.castSucc : ℝ) : ℝ) : ℂ) *
          ldpStableHalfExponent (u j))) := by
  let s : ℕ → Set.Ici (0 : ℝ) := fun j => t ⟨min j k, by omega⟩
  have hs0 : (s 0 : ℝ) = 0 := by simpa [s] using ht0
  have hs : Monotone s := fun i j hij => ht (min_le_min_right k hij)
  have h := ldpBusemannPositiveHalfLimit_partition hμ k s hs0 hs u
  have hsucc (j : Fin k) : s (j.val + 1) = t j.succ := by
    dsimp [s]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  have hcast (j : Fin k) : s j.val = t j.castSucc := by
    dsimp [s]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  simpa only [hsucc, hcast] using h

/-- Helper toward Theorem 1.6; not a paper result. Every limit of the actual
positive-half laws retains the selected finite cutoff marginals. -/
theorem sdpBusemannPositiveHalfLimit_cutoff
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ)) (N : ℕ) :
    (μ.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) =
      sdpBusemannPositiveCutoffLimit sdpIncrements_iIndep_proved hsymSdp_sdpCode N := by
  obtain ⟨ν, hν, hcut⟩ := sdpBusemannWholeLinePositiveHalfLaw_tendsto_sdpCode
  have heq : μ = ν := tendsto_nhds_unique hμ hν
  rw [heq]
  exact hcut N

/-- Helper toward Theorem 1.6; not a paper result. The selected window limit has
the established FDD law at every deterministic time, including the endpoint. -/
theorem sdpBusemannWindowLimit_fdd
    {T : ℝ} (hT : 0 < T) {m : ℕ} {t : ℕ → J1Window T}
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) :
    let ν := Classical.choose
      (sdp_busemann_window_tendsto sdpIncrements_iIndep_proved hsymSdp_sdpCode hT)
    let b : ℝ := (SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion (-1)) ^
      (2 / 3 : ℝ)
    let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (b : ℂ)
    0 < b ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m),
        charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
          (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
      ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
        (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  dsimp only
  obtain ⟨ha, L, hchar, hL⟩ := sdp_busemann_window_fdd
    sdpIncrements_iIndep_proved hsymSdp_sdpCode hT ht0 ht
  refine ⟨ha, L, hchar, ?_⟩
  have hν := (Classical.choose_spec
    (sdp_busemann_window_tendsto sdpIncrements_iIndep_proved hsymSdp_sdpCode hT)).1
  have hmap := tendsto_map_windowEvalVec _ _ hν
    (fun i : Fin m => t (i.val + 1)) (fun i hi =>
      sdp_busemann_window_fixed_time_continuous
        sdpIncrements_iIndep_proved hsymSdp_sdpCode hT _ hi)
  exact tendsto_nhds_unique hmap hL

/-- Helper toward Theorem 1.6; not a paper result. Joint deterministic evaluations
are transported together through a single retained cutoff marginal. -/
theorem sdpBusemannPositiveHalfLimit_evalVec_law
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (N : ℕ) {m : ℕ} (s : Fin m → Set.Ici (0 : ℝ))
    (hs : ∀ j, (s j : ℝ) ≤ (N : ℝ)) :
    (μ : Measure CadlagLocalZero).map (fun x j => x.1.1 (s j)) =
      ((Classical.choose (sdp_busemann_window_tendsto
        sdpIncrements_iIndep_proved hsymSdp_sdpCode
        (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) :
          ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
            Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
        (windowEvalVec (fun j => ⟨s j, (s j).property, by
          have := hs j; push_cast; linarith⟩)) := by
  let i : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
  let sN : Fin m → J1Window ((i.val : ℝ) + 1) := fun j =>
    ⟨s j, (s j).property, by have := hs j; dsimp [i]; linarith⟩
  let e : LocalCutoffTuple N → (Fin m → ℝ) := fun x j => (x i).path.1 (sN j)
  have he : Measurable e := Measurable.of_eval fun j =>
    (measurable_j1WindowD_eval (by positivity) (sN j)).comp (measurable_pi_apply i)
  have hleft : (fun x : CadlagLocalZero => e (finiteCutoffWindows N x.1)) =
      (fun x j => x.1.1 (s j)) := by
    funext x j
    change x.1.1 (s j) * localCutoff N (s j) = x.1.1 (s j)
    rw [localCutoff_eq_one N (s j) (hs j), mul_one]
  have hright : (fun x : J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity) =>
      e (positiveHalfCutoffFactor N x)) =
        windowEvalVec (fun j => ⟨s j, (s j).property, by
          have := hs j; push_cast; linarith⟩) := by
    funext x j
    change x.path.1 _ * localCutoff N (s j) = x.path.1 _
    rw [localCutoff_eq_one N (s j) (hs j), mul_one]
    rfl
  have hcut := congrArg (fun p : ProbabilityMeasure (LocalCutoffTuple N) =>
    (p : Measure (LocalCutoffTuple N)).map e)
      (sdpBusemannPositiveHalfLimit_cutoff hμ N)
  change (((μ : Measure CadlagLocalZero).map
    (Subtype.val : CadlagLocalZero → CadlagLocal)).map (finiteCutoffWindows N)).map e =
    (((Classical.choose (sdp_busemann_window_tendsto
      sdpIncrements_iIndep_proved hsymSdp_sdpCode (by positivity)) :
        ProbabilityMeasure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))) :
          Measure (J1WindowD ((N + 2 : ℕ) : ℝ) (by positivity))).map
            (positiveHalfCutoffFactor N)).map e at hcut
  rw [Measure.map_map he (finiteCutoffWindows_measurable N),
    Measure.map_map (he.comp (finiteCutoffWindows_measurable N)) measurable_subtype_coe,
    Measure.map_map he (measurable_positiveHalfCutoffFactor N)] at hcut
  simpa only [Function.comp_def, hleft, hright] using hcut

/-- Helper toward Theorem 1.6; not a paper result. The shared scale from the
proved SDP transform expansion, also used by the symmetric negative half. -/
@[expose] noncomputable def sdpStableHalfScale : ℝ :=
  (SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion (-1)) ^ (2 / 3 : ℝ)

/-- Helper toward Theorem 1.6; not a paper result. The shared scale is positive. -/
theorem sdpStableHalfScale_pos : 0 < sdpStableHalfScale :=
  negativeHalfSdpScale_pos hsymSdp_sdpCode

/-- Helper toward Theorem 1.6; not a paper result. Both halves use the same scale. -/
theorem sdpStableHalfScale_eq_negativeHalfSdpScale :
    sdpStableHalfScale = negativeHalfSdpScale := rfl

/-- Helper toward Theorem 1.6; not a paper result. The positive-half exponent,
with characteristic coefficient `b/2` and the upward-jump stable sign. -/
@[expose] noncomputable def sdpStableHalfExponent (u : ℝ) : ℂ :=
  ((sdpStableHalfScale / 2 : ℝ) : ℂ) * (|u| ^ (4 / 3 : ℝ) : ℝ) *
    (1 + Complex.I * (Real.sqrt 3 : ℂ) *
      ((if 0 < u then (1 : ℝ) else if u < 0 then -1 else 0) : ℂ))

/-- Helper toward Theorem 1.6; not a paper result. Exact conversion from the
block characteristic-function normalization to the signed exponent. -/
theorem sdpStableHalfExponent_eq (u : ℝ) :
    ((if 0 ≤ u then
        ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (sdpStableHalfScale : ℂ)
      else star (((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 *
        (sdpStableHalfScale : ℂ))) * (|u| ^ (4 / 3 : ℝ) : ℝ)) =
      sdpStableHalfExponent u := by
  unfold sdpStableHalfExponent
  by_cases hu : u = 0
  · subst u
    simp [Real.zero_rpow, (by norm_num : (4 / 3 : ℝ) ≠ 0)]
  · rcases lt_or_gt_of_ne hu with hu | hu
    · simp [not_le_of_gt hu, not_lt.mpr hu.le, hu]
      ring
    · simp [hu.le, hu]
      ring

/-- Helper toward Theorem 1.6; not a paper result. Every ordered partition
of the SDP positive-half limit has the stated joint increment exponent.
Repeated times and the empty partition are included. -/
theorem sdpBusemannPositiveHalfLimit_partition
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (k : ℕ) (t : ℕ → Set.Ici (0 : ℝ)) (ht0 : (t 0 : ℝ) = 0)
    (ht : Monotone t) (u : Fin k → ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      (((∑ j : Fin k, u j *
        (x.1.1 (t (j.val + 1)) - x.1.1 (t j.val)) : ℝ) : ℂ) * Complex.I)
        ∂(μ : Measure CadlagLocalZero)) =
      ∏ j : Fin k, Complex.exp
        (-((((t (j.val + 1) : ℝ) - (t j.val : ℝ) : ℝ) : ℂ) *
          sdpStableHalfExponent (u j))) := by
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
  obtain ⟨_, L, hchar, hL⟩ := sdpBusemannWindowLimit_fdd hT (m := k) htw0 htw
  have heval := sdpBusemannPositiveHalfLimit_evalVec_law hμ N
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
  have hcum : (μ : Measure CadlagLocalZero).map
      (fun (x : CadlagLocalZero) (j : Fin k) => x.1.1 (t (j.val + 1))) =
        (((L.map (cumulativeSum (k := k))).map WithLp.ofLp) :
          Measure (Fin k → ℝ)) := heval.trans (congrArg ProbabilityMeasure.toMeasure hL)
  have hinc := congrArg (fun p : Measure (Fin k → ℝ) =>
    p.map (stableHalfIncrementMap (k := k))) hcum
  simp only [ProbabilityMeasure.toMeasure_map] at hinc
  rw [stableHalfIncrementMap_cumulativeSum_law,
    Measure.map_map (stableHalfIncrementMap (k := k)).measurable
      (Measurable.of_eval fun j => measurable_ldpStableHalfEval _)] at hinc
  have hz (x : CadlagLocalZero) : x.1.1 (t 0) = 0 := by
    have he : t 0 = (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ)) := Subtype.ext ht0
    rw [he, x.property]
  rw [← stableHalfIncrementMap_charFun (μ : Measure CadlagLocalZero)
    (fun x j => x.1.1 (t j)) (fun j => measurable_ldpStableHalfEval _) hz u]
  change charFun ((μ : Measure CadlagLocalZero).map
    (stableHalfIncrementMap ∘ (fun (x : CadlagLocalZero) (j : Fin k) => x.1.1 (t (j.val + 1))))) _ = _
  rw [hinc, hchar]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [tw, Nat.min_eq_left (show j.val + 1 ≤ k by omega),
    Nat.min_eq_left (show j.val ≤ k by omega)]
  rw [show (SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion (-1)) ^
      (2 / 3 : ℝ) = sdpStableHalfScale from rfl, sdpStableHalfExponent_eq]

/-- Helper toward Theorem 1.6; not a paper result. The full finite-partition
formula, indexed by the supplied `k + 1` ordered times with initial time zero. -/
theorem sdpBusemannPositiveHalfLimit_partition_fin
    {μ : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (k : ℕ) (t : Fin (k + 1) → Set.Ici (0 : ℝ))
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) (u : Fin k → ℝ) :
    (∫ x : CadlagLocalZero, Complex.exp
      (((∑ j : Fin k, u j *
        (x.1.1 (t j.succ) - x.1.1 (t j.castSucc)) : ℝ) : ℂ) * Complex.I)
        ∂(μ : Measure CadlagLocalZero)) =
      ∏ j : Fin k, Complex.exp
        (-((((t j.succ : ℝ) - (t j.castSucc : ℝ) : ℝ) : ℂ) *
          sdpStableHalfExponent (u j))) := by
  let s : ℕ → Set.Ici (0 : ℝ) := fun j => t ⟨min j k, by omega⟩
  have hs0 : (s 0 : ℝ) = 0 := by simpa [s] using ht0
  have hs : Monotone s := fun i j hij => ht (min_le_min_right k hij)
  have h := sdpBusemannPositiveHalfLimit_partition hμ k s hs0 hs u
  have hsucc (j : Fin k) : s (j.val + 1) = t j.succ := by
    dsimp [s]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  have hcast (j : Fin k) : s j.val = t j.castSucc := by
    dsimp [s]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  simpa only [hsucc, hcast] using h

end DirectedDistances.Recursive
