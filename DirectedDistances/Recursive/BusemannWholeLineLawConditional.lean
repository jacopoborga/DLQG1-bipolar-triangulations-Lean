module

public import DirectedDistances.Recursive.BusemannWholeLineJumpConv

public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped Topology

private abbrev PositiveIncrementBlock := {k : ℤ // 0 < k}

private abbrev NonpositiveIncrementBlock := {k : ℤ // k ≤ 0}

private def positiveIncrementSamples (x : PositiveIncrementBlock → ℤ) : ℕ → ℤ :=
  fun j => (Finset.range j).sum (fun i => x ⟨(i : ℤ) + 1, by omega⟩)

private def negativeIncrementSamples (x : NonpositiveIncrementBlock → ℤ) : ℕ → ℤ :=
  fun j => if j = 0 then 0 else
    -((Finset.range (j + 1)).sum (fun i => x ⟨-(i : ℤ), by omega⟩))

private theorem truncatedScaledPath_tendsto (n : ℕ) (z : ℕ → ℤ) :
    Tendsto
      (fun M => scaledIntegerPositiveHalfPath n (fun j => z (min j M)))
      atTop (𝓝 (scaledIntegerPositiveHalfPath n z)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_order.1 tendsto_localJ1TailBound).2 ε hε)
  refine ⟨(n + 1) * (N + 1), ?_⟩
  intro M hM
  have heq : finiteCutoffWindows N
      (scaledIntegerPositiveHalfPath n (fun j => z (min j M))) =
      finiteCutoffWindows N (scaledIntegerPositiveHalfPath n z) := by
    funext i
    apply congrArg (fun p => J1WindowD.mk p)
    apply Subtype.ext
    funext t
    change (_ * (z (min ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ M) : ℝ)) * _ =
      (_ * (z ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ)) * _
    have hi : (i.val : ℝ) + 1 ≤ ((N + 1 : ℕ) : ℝ) := by
      norm_cast
      omega
    have ht : (t : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := t.property.2.trans hi
    have hj : ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ ≤ (n + 1) * (N + 1) := by
      apply Nat.floor_le_of_le
      exact_mod_cast mul_le_mul_of_nonneg_left ht (by positivity :
        0 ≤ ((n + 1 : ℕ) : ℝ))
    rw [min_eq_left (hj.trans hM)]
  have hb := dist_le_finiteCutoffWindowTruncDist_add_bound N
    (scaledIntegerPositiveHalfPath n (fun j => z (min j M)))
    (scaledIntegerPositiveHalfPath n z)
  rw [heq, finiteCutoffWindowTruncDist_self, zero_add] at hb
  exact hb.trans_lt (hN N le_rfl)

private theorem measurable_scaledIntegerPositiveHalfPath
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (z : Ω → ℕ → ℤ)
    (hz : ∀ j, Measurable (fun ω => z ω j)) :
    Measurable (fun ω => scaledIntegerPositiveHalfPath n (z ω)) := by
  let f : ℕ → Ω → CadlagLocal := fun M ω =>
    scaledIntegerPositiveHalfPath n (fun j => z ω (min j M))
  have hf (M : ℕ) : Measurable (f M) := by
    let v : Ω → Fin (M + 1) → ℤ := fun ω i => z ω i.val
    have hv : Measurable v := Measurable.of_eval fun i => hz i.val
    let g : (Fin (M + 1) → ℤ) → CadlagLocal := fun v =>
      scaledIntegerPositiveHalfPath n (fun j => v ⟨min j M, by omega⟩)
    exact (measurable_of_countable g).comp hv
  apply measurable_of_tendsto_metrizable hf
  apply tendsto_pi_nhds.mpr
  intro ω
  exact truncatedScaledPath_tendsto n (z ω)

private noncomputable def positiveIncrementHalfPath (n : ℕ)
    (x : PositiveIncrementBlock → ℤ) : CadlagLocalZero :=
  ⟨scaledIntegerPositiveHalfPath n (positiveIncrementSamples x), by
    simp [scaledIntegerPositiveHalfPath, positiveIncrementSamples]⟩

private noncomputable def negativeIncrementHalfPath (n : ℕ)
    (x : NonpositiveIncrementBlock → ℤ) : CadlagLocalZero :=
  ⟨scaledIntegerPositiveHalfPath n (negativeIncrementSamples x), by
    simp [scaledIntegerPositiveHalfPath, negativeIncrementSamples]⟩

private theorem measurable_positiveIncrementHalfPath (n : ℕ) :
    Measurable (positiveIncrementHalfPath n) := by
  have hz : ∀ j, Measurable (fun x => positiveIncrementSamples x j) := by
    intro j
    dsimp [positiveIncrementSamples]
    fun_prop
  have h := measurable_scaledIntegerPositiveHalfPath n
    (fun x => positiveIncrementSamples x) hz
  have hzero (x : PositiveIncrementBlock → ℤ) :
      (scaledIntegerPositiveHalfPath n (positiveIncrementSamples x)).1
        ⟨0, le_rfl⟩ = 0 := by
    simp [scaledIntegerPositiveHalfPath, positiveIncrementSamples]
  change Measurable (fun x =>
    (⟨scaledIntegerPositiveHalfPath n (positiveIncrementSamples x), hzero x⟩ :
      CadlagLocalZero))
  exact Measurable.subtype_mk (f := fun x =>
    scaledIntegerPositiveHalfPath n (positiveIncrementSamples x)) h (h := hzero)

private theorem measurable_negativeIncrementHalfPath (n : ℕ) :
    Measurable (negativeIncrementHalfPath n) := by
  have hz : ∀ j, Measurable (fun x => negativeIncrementSamples x j) := by
    intro j
    dsimp [negativeIncrementSamples]
    fun_prop
  have h := measurable_scaledIntegerPositiveHalfPath n
    (fun x => negativeIncrementSamples x) hz
  have hzero (x : NonpositiveIncrementBlock → ℤ) :
      (scaledIntegerPositiveHalfPath n (negativeIncrementSamples x)).1
        ⟨0, le_rfl⟩ = 0 := by
    simp [scaledIntegerPositiveHalfPath, negativeIncrementSamples]
  change Measurable (fun x =>
    (⟨scaledIntegerPositiveHalfPath n (negativeIncrementSamples x), hzero x⟩ :
      CadlagLocalZero))
  exact Measurable.subtype_mk (f := fun x =>
    scaledIntegerPositiveHalfPath n (negativeIncrementSamples x)) h (h := hzero)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The positive and nonpositive increment blocks are independent by item `ind`. -/
theorem ldpBusemannIncrementBlocks_indep
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure) :
    IndepFun
      (fun ω (i : {k : ℤ // 0 < k}) =>
        ldpIncrement busemannLDPMeasurableVersion i.1 ω)
      (fun ω (i : {k : ℤ // k ≤ 0}) =>
        ldpIncrement busemannLDPMeasurableVersion i.1 ω)
      iidCodeMeasure := by
  have hdisj : Disjoint {k : ℤ | 0 < k} {k : ℤ | k ≤ 0} := by
    apply Set.disjoint_left.mpr
    intro k hk hk'
    change 0 < k at hk
    change k ≤ 0 at hk'
    exact (not_lt_of_ge hk') hk
  have hmeas (k : ℤ) :
      Measurable (fun ω => ldpIncrement busemannLDPMeasurableVersion k ω) := by
    change Measurable (fun ω =>
      busemannLDPMeasurableVersion ω k -
        busemannLDPMeasurableVersion ω (k - 1))
    exact (measurable_busemannLDPMeasurableVersion k).sub
      (measurable_busemannLDPMeasurableVersion (k - 1))
  exact hind.indepFun_set {k : ℤ | 0 < k} {k : ℤ | k ≤ 0}
    hdisj hmeas

private theorem positiveIncrementSamples_eq (ω : ℕ → Fin 3) (j : ℕ) :
    positiveIncrementSamples
      (fun i => ldpIncrement busemannLDPMeasurableVersion i.1 ω) j =
      busemannLDPMeasurableVersion ω (j : ℤ) := by
  induction j with
  | zero => simp [positiveIncrementSamples, busemannLDPMeasurableVersion_zero]
  | succ j ih =>
    change (Finset.range (j + 1)).sum _ = _
    rw [Finset.sum_range_succ]
    have hsum := ih
    simp only [positiveIncrementSamples] at hsum
    rw [hsum]
    change busemannLDPMeasurableVersion ω (j : ℤ) +
        ldpIncrement busemannLDPMeasurableVersion ((j : ℤ) + 1) ω = _
    simp only [ldpIncrement]
    rw [Nat.cast_succ]
    ring_nf

private theorem nonpositiveIncrementSum_eq (ω : ℕ → Fin 3) (j : ℕ) :
    (Finset.range (j + 1)).sum
        (fun i => ldpIncrement busemannLDPMeasurableVersion (-(i : ℤ)) ω) =
      busemannLDPMeasurableVersion ω 0 -
        busemannLDPMeasurableVersion ω (-((j : ℤ) + 1)) := by
  induction j with
  | zero =>
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
    change busemannLDPMeasurableVersion ω 0 -
        busemannLDPMeasurableVersion ω (0 - 1) = _
    rfl
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have hinc : ldpIncrement busemannLDPMeasurableVersion
        (-((j : ℤ) + 1)) ω =
        busemannLDPMeasurableVersion ω (-((j : ℤ) + 1)) -
          busemannLDPMeasurableVersion ω (-((j : ℤ) + 1) - 1) := by
      rfl
    have hidx : -((j + 1 : ℕ) : ℤ) = -((j : ℤ) + 1) := by
      norm_cast
    rw [hidx, hinc]
    have hstep : -((j : ℤ) + 1) - 1 =
        -(((j + 1 : ℕ) : ℤ) + 1) := by
      push_cast
      omega
    rw [hstep]
    ring_nf

private theorem negativeIncrementSamples_eq (ω : ℕ → Fin 3) (j : ℕ) :
    negativeIncrementSamples
      (fun i => ldpIncrement busemannLDPMeasurableVersion i.1 ω) j =
      ldpBusemannNegativeSamples ω j := by
  by_cases hj : j = 0
  · subst j
    simp [negativeIncrementSamples, ldpBusemannNegativeSamples]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    simp [negativeIncrementSamples, ldpBusemannNegativeSamples, hj]
    rw [nonpositiveIncrementSum_eq]
    simp [busemannLDPMeasurableVersion_zero]

private theorem positiveIncrementHalfPath_eq (n : ℕ) (ω : ℕ → Fin 3) :
    positiveIncrementHalfPath n
      (fun i => ldpIncrement busemannLDPMeasurableVersion i.1 ω) =
      ldpBusemannWholeLinePositiveHalf n ω := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (positiveIncrementSamples
        (fun i => ldpIncrement busemannLDPMeasurableVersion i.1 ω)
        ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ) =
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (busemannLDPMeasurableVersion ω
        ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ)
  rw [positiveIncrementSamples_eq]

private theorem negativeIncrementHalfPath_eq (n : ℕ) (ω : ℕ → Fin 3) :
    negativeIncrementHalfPath n
      (fun i => ldpIncrement busemannLDPMeasurableVersion i.1 ω) =
      ldpBusemannWholeLineNegativeHalf n ω := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (negativeIncrementSamples
        (fun i => ldpIncrement busemannLDPMeasurableVersion i.1 ω)
        ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ) =
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (ldpBusemannNegativeSamples ω
        ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ)
  rw [negativeIncrementSamples_eq]

private theorem measurable_positiveIncrementBlock :
    Measurable (fun ω (i : PositiveIncrementBlock) =>
      ldpIncrement busemannLDPMeasurableVersion i.1 ω) := by
  apply Measurable.of_eval
  intro i
  exact measurable_busemannLDPMeasurableVersion i.1 |>.sub
    (measurable_busemannLDPMeasurableVersion (i.1 - 1))

private theorem measurable_nonpositiveIncrementBlock :
    Measurable (fun ω (i : NonpositiveIncrementBlock) =>
      ldpIncrement busemannLDPMeasurableVersion i.1 ω) := by
  apply Measurable.of_eval
  intro i
  exact measurable_busemannLDPMeasurableVersion i.1 |>.sub
    (measurable_busemannLDPMeasurableVersion (i.1 - 1))

private theorem measurable_ldpBusemannWholeLinePositiveHalf (n : ℕ) :
    Measurable (fun ω => ldpBusemannWholeLinePositiveHalf n ω) := by
  have hfactor : (fun ω => ldpBusemannWholeLinePositiveHalf n ω) =
      positiveIncrementHalfPath n ∘
        (fun ω i => ldpIncrement busemannLDPMeasurableVersion i.1 ω) := by
    funext ω
    exact (positiveIncrementHalfPath_eq n ω).symm
  rw [hfactor]
  exact (measurable_positiveIncrementHalfPath n).comp
    measurable_positiveIncrementBlock

private theorem measurable_ldpBusemannWholeLineNegativeHalf (n : ℕ) :
    Measurable (fun ω => ldpBusemannWholeLineNegativeHalf n ω) := by
  have hfactor : (fun ω => ldpBusemannWholeLineNegativeHalf n ω) =
      negativeIncrementHalfPath n ∘
        (fun ω i => ldpIncrement busemannLDPMeasurableVersion i.1 ω) := by
    funext ω
    exact (negativeIncrementHalfPath_eq n ω).symm
  rw [hfactor]
  exact (measurable_negativeIncrementHalfPath n).comp
    measurable_nonpositiveIncrementBlock

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The two half-path random elements are independent under item `ind`. -/
theorem ldpBusemannWholeLineHalfPaths_indep (n : ℕ)
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure) :
    IndepFun (fun ω => ldpBusemannWholeLinePositiveHalf n ω)
      (fun ω => ldpBusemannWholeLineNegativeHalf n ω) iidCodeMeasure := by
  have hblock := ldpBusemannIncrementBlocks_indep hind
  have hcomp := hblock.comp (measurable_positiveIncrementHalfPath n)
    (measurable_negativeIncrementHalfPath n)
  apply IndepFun.congr hcomp
  · exact Filter.Eventually.of_forall fun ω =>
      positiveIncrementHalfPath_eq n ω
  · exact Filter.Eventually.of_forall fun ω =>
      negativeIncrementHalfPath_eq n ω

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The joint half-path law is the product of its marginal laws. -/
theorem ldpBusemannWholeLineHalfPairLaw_eq_probabilityProduct (n : ℕ)
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure) :
    ProbabilityMeasure.map
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (fun ω =>
          (ldpBusemannWholeLinePositiveHalf n ω,
           ldpBusemannWholeLineNegativeHalf n ω)) =
      probabilityProduct
        (ProbabilityMeasure.map
          (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
          (ldpBusemannWholeLinePositiveHalf n))
        (ProbabilityMeasure.map
          (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
          (ldpBusemannWholeLineNegativeHalf n)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change iidCodeMeasure.map
      (fun ω =>
        (ldpBusemannWholeLinePositiveHalf n ω,
         ldpBusemannWholeLineNegativeHalf n ω)) =
    (iidCodeMeasure.map (fun ω => ldpBusemannWholeLinePositiveHalf n ω)).prod
      (iidCodeMeasure.map (fun ω => ldpBusemannWholeLineNegativeHalf n ω))
  exact (ldpBusemannWholeLineHalfPaths_indep n hind).map_prod_eq_prod_map_map
    (measurable_ldpBusemannWholeLinePositiveHalf n).aemeasurable
    (measurable_ldpBusemannWholeLineNegativeHalf n).aemeasurable

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Explicit premise for convergence of the reflected negative-half laws. -/
@[expose] def LdpBusemannWholeLineNegativeHalfConverges
    (ν : ProbabilityMeasure CadlagLocalZero) : Prop :=
  (∀ n, Measurable (ldpBusemannWholeLineNegativeHalf n)) ∧
    Tendsto
      (fun n => ProbabilityMeasure.map
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (ldpBusemannWholeLineNegativeHalf n))
      atTop (𝓝 ν)

end DirectedDistances.Recursive
