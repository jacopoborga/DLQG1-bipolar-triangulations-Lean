module

public import DirectedDistances.Probability.SkewedStableLimitExists

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The continuous linear map taking a vector of consecutive increments to its
cumulative sums. -/
@[expose] noncomputable def cumulativeSum {k : ℕ} :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) := by
  let e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] (Fin k → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)
  let c : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun i =>
      ∑ j ∈ Finset.Iic i,
        ContinuousLinearMap.proj (ι := Fin k) (φ := fun _ : Fin k => ℝ) j
  exact e.symm.toContinuousLinearMap.comp (c.comp e.toContinuousLinearMap)

private theorem cumulativeSum_apply {k : ℕ}
    (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    cumulativeSum x i = ∑ j ∈ Finset.Iic i, x j := by
  let e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] (Fin k → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)
  have he (y : Fin k → ℝ) (i : Fin k) : (e.symm y) i = y i := by
    change e (e.symm y) i = y i
    rw [e.apply_symm_apply]
  have hx (j : Fin k) : (e x) j = x j := by
    rfl
  change (e.symm
    ((ContinuousLinearMap.pi fun r =>
      ∑ j ∈ Finset.Iic r,
        ContinuousLinearMap.proj (ι := Fin k) (φ := fun _ : Fin k => ℝ) j)
      (e x))) i = _
  rw [he]
  simp only [ContinuousLinearMap.pi_apply, sum_apply,
    ContinuousLinearMap.proj_apply]
  exact Finset.sum_congr rfl fun j hj => hx j

private def extendFin {k : ℕ} (f : Fin k → ℝ) (r : ℕ) : ℝ :=
  if hr : r < k then f ⟨r, hr⟩ else 0

private theorem sum_Iic_fin_eq_sum_range {k : ℕ} (i : Fin k)
    (f : Fin k → ℝ) :
    (∑ j ∈ Finset.Iic i, f j) =
      ∑ j ∈ Finset.range (i.val + 1), extendFin f j := by
  classical
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Fin.le_iff_val_le_val.mp (Finset.mem_Iic.mp hj)))
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro b hb
    have hbi : b ≤ i.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    refine ⟨⟨b, hbi.trans_lt i.isLt⟩, Finset.mem_Iic.mpr ?_, rfl⟩
    exact Fin.le_iff_val_le_val.mpr hbi
  · intro j hj
    rw [extendFin, dite_eq_left j.isLt]

private theorem sum_consecutive_interval_sums (b : ℕ → ℕ)
    (hb : Monotone b) (f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      ∑ j ∈ Finset.Ico (b i) (b (i + 1)), f j) =
      ∑ j ∈ Finset.Ico (b 0) (b m), f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simpa only [Nat.succ_eq_add_one] using
      (Finset.sum_Ico_consecutive f (hb (Nat.zero_le m))
        (hb (Nat.le_succ m)))

private theorem skewStableBlockVector_apply {Ω : Type*}
    [MeasurableSpace Ω] {k : ℕ} {ν : ℝ} {t : ℕ → ℝ}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (i : Fin k) :
    (skewStableBlockVector (k := k) (t := t) (ν := ν) X n ω) i =
      (n : ℝ) ^ (-1 / ν) *
        ∑ j ∈ Finset.Ico ⌊(n : ℝ) * t i.val⌋₊
          ⌊(n : ℝ) * t (i.val + 1)⌋₊, X j ω := by
  simp [skewStableBlockVector, PiLp.toLp_apply]

/-- The normalized finite process vector obtained by cumulatively summing the
consecutive block vector. -/
@[expose] noncomputable def skewStableProcessVector {Ω : Type*}
    [MeasurableSpace Ω] {k : ℕ} {ν : ℝ} {t : ℕ → ℝ}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin k) :=
  cumulativeSum (skewStableBlockVector (k := k) (t := t) (ν := ν) X n ω)

/-- Helper identity toward E-STABLE / thm-busemann-conv
vector is the normalized sum over the half-open interval from `⌊n t₀⌋` to
`⌊n t_{i+1}⌋`. This finite-dimensional identity is not the paper result. -/
theorem skewStableProcessVector_apply {Ω : Type*}
    [MeasurableSpace Ω] {k : ℕ} {ν : ℝ} {t : ℕ → ℝ}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (i : Fin k)
    (hmono : Monotone t) :
    (skewStableProcessVector (k := k) (t := t) (ν := ν) X n ω) i =
      (n : ℝ) ^ (-1 / ν) *
        ∑ j ∈ Finset.Ico ⌊(n : ℝ) * t 0⌋₊
          ⌊(n : ℝ) * t (i.val + 1)⌋₊, X j ω := by
  let b : ℕ → ℕ := fun r => ⌊(n : ℝ) * t r⌋₊
  have hb : Monotone b := by
    intro r s hrs
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hmono hrs)
      (Nat.cast_nonneg n))
  let v : Fin k → ℝ :=
    fun r => skewStableBlockVector (k := k) (t := t) (ν := ν) X n ω r
  rw [skewStableProcessVector, cumulativeSum_apply,
    sum_Iic_fin_eq_sum_range i v]
  calc
    _ = ∑ r ∈ Finset.range (i.val + 1),
        (n : ℝ) ^ (-1 / ν) *
          ∑ j ∈ Finset.Ico (b r) (b (r + 1)), X j ω := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrk : r < k := by
        have := Finset.mem_range.mp hr
        omega
      simp only [extendFin, dite_eq_left hrk, v]
      exact skewStableBlockVector_apply X n ω ⟨r, hrk⟩
    _ = (n : ℝ) ^ (-1 / ν) *
        ∑ r ∈ Finset.range (i.val + 1),
          ∑ j ∈ Finset.Ico (b r) (b (r + 1)), X j ω := by
      rw [← Finset.mul_sum]
    _ = (n : ℝ) ^ (-1 / ν) *
        ∑ j ∈ Finset.Ico (b 0) (b (i.val + 1)), X j ω := by
      rw [sum_consecutive_interval_sums b hb (fun j => X j ω)]
    _ = _ := rfl

/-- Helper toward E-STABLE / thm-busemann-conv
`n^(−1/ν) Σ_{j ∈ [⌊n t₀⌋, ⌊n t_{i+1}⌋)} X_j` (see
`skewStableProcessVector_apply`). For `t₀ = 0`, these are the normalized
partial-sum process values at the floor times `t₁, ..., tₖ`; for `t₀ > 0`,
they are increments from `t₀`, not process values from zero. The finite-dimensional
distributions converge to those of the skewed stable process. No functional
(Skorokhod J1) convergence, tightness, two-sided gluing or Busemann law identification is
claimed; this is not the paper result. The limiting block law is the product law from
`exists_skewStable_blockVector_limit`. -/
theorem tendsto_skewStable_processVector_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hX : ∀ i, Measurable (X i)) {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν))
    {k : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (hmono : Monotone t) :
    ∃ μlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)),
      (∀ θ : EuclideanSpace ℝ (Fin k),
        charFun (μlim : Measure _) θ = ∏ i : Fin k, Complex.exp
          (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ))))) ∧
      Tendsto
        (fun n : ℕ ↦
          (⟨P.map (skewStableProcessVector (k := k) (t := t) (ν := ν) X n),
            inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))))
        atTop (@nhds (ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
          MeasureTheory.ProbabilityMeasure.instTopologicalSpace
          (μlim.map (cumulativeSum (k := k)))) := by
  obtain ⟨μlim, hchar, hblock⟩ := tendsto_skewStable_blockVector_law
    hindep hident hX hν hexp ht0 hmono
  let blockLaw : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) := fun n =>
    ⟨P.map (skewStableBlockVector (k := k) (t := t) (ν := ν) X n), inferInstance⟩
  have hmap : Tendsto (fun n : ℕ => (blockLaw n).map (cumulativeSum (k := k)))
      atTop (@nhds (ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
        MeasureTheory.ProbabilityMeasure.instTopologicalSpace
        (μlim.map (cumulativeSum (k := k)))) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      blockLaw μlim hblock (cumulativeSum (k := k)).continuous
  have hblockMeas (n : ℕ) :
      Measurable (skewStableBlockVector (k := k) (t := t) (ν := ν) X n) := by
    change Measurable (fun ω ↦ (WithLp.equiv 2 (Fin k → ℝ)).symm
      (fun i : Fin k ↦ (n : ℝ) ^ (-1 / ν) *
        ∑ j ∈ Finset.Ico ⌊(n : ℝ) * t i.val⌋₊
          ⌊(n : ℝ) * t (i.val + 1)⌋₊, X j ω))
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp
      (measurable_pi_iff.mpr fun i ↦
        (Finset.measurable_fun_sum _ (fun j _ ↦ hX j)).const_mul _)
  have hprocessMap (n : ℕ) :
      (⟨P.map (skewStableProcessVector (k := k) (t := t) (ν := ν) X n),
        inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) =
        (blockLaw n).map (cumulativeSum (k := k)) := by
    apply Subtype.ext
    change P.map (fun ω ↦ cumulativeSum (skewStableBlockVector
      (k := k) (t := t) (ν := ν) X n ω)) =
      (P.map (skewStableBlockVector (k := k) (t := t) (ν := ν) X n)).map
        (cumulativeSum (k := k))
    rw [(Measure.map_map (cumulativeSum (k := k)).continuous.measurable
      (hblockMeas n))]
    rfl
  refine ⟨μlim, hchar, ?_⟩
  have hprocessFun :
      (fun n : ℕ =>
        (⟨P.map (skewStableProcessVector (k := k) (t := t) (ν := ν) X n),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))) =
        (fun n : ℕ => (blockLaw n).map (cumulativeSum (k := k))) :=
    funext hprocessMap
  rw [hprocessFun]
  exact hmap

end DirectedDistances.Probability
