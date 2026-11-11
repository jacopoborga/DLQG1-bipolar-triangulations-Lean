module

public import DirectedDistances.Recursive.BusemannWholeLineSDP
import DirectedDistances.Recursive.HLRSdpFinal
public import DirectedDistances.Probability.WholeLineGlueLaw

import all DirectedDistances.Probability.SkorokhodJ1WholeLineLocal
import DirectedDistances.Probability.SkorokhodJ1WholeLineGlue
import DirectedDistances.Probability.SkorokhodFloorStep
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped Topology

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
abbrev SdpPositiveIncrementBlock := {k : ℤ // 0 < k}

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
abbrev SdpNonpositiveIncrementBlock := {k : ℤ // k ≤ 0}

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] def sdpPositiveIncrementSamples
    (x : SdpPositiveIncrementBlock → ℤ) : ℕ → ℤ :=
  fun j => (Finset.range j).sum (fun i => x ⟨(i : ℤ) + 1, by omega⟩)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] def sdpNegativeIncrementSamples
    (x : SdpNonpositiveIncrementBlock → ℤ) : ℕ → ℤ :=
  fun j => if j = 0 then 0 else
    -((Finset.range (j + 1)).sum (fun i => x ⟨-(i : ℤ), by omega⟩))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpCadlagRestrictPositive {f : ℝ → ℝ} (hf : IsCadlag f) :
    IsCadlag (fun t : Set.Ici (0 : ℝ) => f t) := by
  constructor
  · intro t
    apply (hf.isRightContinuous (t : ℝ)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall (fun _ h => h)⟩
  · intro t
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (t : ℝ)
    refine ⟨l, hl.comp ?_⟩
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall (fun _ h => h)⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def sdpScaledIntegerPositiveHalfPath (n : ℕ)
    (z : ℕ → ℤ) : CadlagLocal :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    (z ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ),
    sdpCadlagRestrictPositive (floorStep_isCadlag
      (fun j : ℤ => (z j.toNat : ℝ)) (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ))
      ((n + 1 : ℕ) : ℝ) (by positivity))⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem sdpTruncatedScaledPath_tendsto (n : ℕ) (z : ℕ → ℤ) :
    Tendsto (fun M => sdpScaledIntegerPositiveHalfPath n
      (fun j => z (min j M))) atTop
      (𝓝 (sdpScaledIntegerPositiveHalfPath n z)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_order.1 tendsto_localJ1TailBound).2 ε hε)
  refine ⟨(n + 1) * (N + 1), ?_⟩
  intro M hM
  have heq : finiteCutoffWindows N
      (sdpScaledIntegerPositiveHalfPath n (fun j => z (min j M))) =
      finiteCutoffWindows N (sdpScaledIntegerPositiveHalfPath n z) := by
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
    (sdpScaledIntegerPositiveHalfPath n (fun j => z (min j M)))
    (sdpScaledIntegerPositiveHalfPath n z)
  rw [heq, finiteCutoffWindowTruncDist_self, zero_add] at hb
  exact hb.trans_lt (hN N le_rfl)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem measurable_sdpScaledIntegerPositiveHalfPath
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (z : Ω → ℕ → ℤ)
    (hz : ∀ j, Measurable (fun ω => z ω j)) :
    Measurable (fun ω => sdpScaledIntegerPositiveHalfPath n (z ω)) := by
  let f : ℕ → Ω → CadlagLocal := fun M ω =>
    sdpScaledIntegerPositiveHalfPath n (fun j => z ω (min j M))
  have hf (M : ℕ) : Measurable (f M) := by
    let v : Ω → Fin (M + 1) → ℤ := fun ω i => z ω i.val
    have hv : Measurable v := Measurable.of_eval fun i => hz i.val
    let g : (Fin (M + 1) → ℤ) → CadlagLocal := fun v =>
      sdpScaledIntegerPositiveHalfPath n (fun j => v ⟨min j M, by omega⟩)
    exact (measurable_of_countable g).comp hv
  apply measurable_of_tendsto_metrizable hf
  apply tendsto_pi_nhds.mpr
  intro ω
  exact sdpTruncatedScaledPath_tendsto n (z ω)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def sdpPositiveIncrementHalfPath (n : ℕ)
    (x : {k : ℤ // 0 < k} → ℤ) : CadlagLocalZero :=
  ⟨sdpScaledIntegerPositiveHalfPath n (sdpPositiveIncrementSamples x), by
    simp [sdpScaledIntegerPositiveHalfPath, sdpPositiveIncrementSamples]⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def sdpNegativeIncrementHalfPath (n : ℕ)
    (x : {k : ℤ // k ≤ 0} → ℤ) : CadlagLocalZero :=
  ⟨sdpScaledIntegerPositiveHalfPath n (sdpNegativeIncrementSamples x), by
    simp [sdpScaledIntegerPositiveHalfPath, sdpNegativeIncrementSamples]⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem measurable_sdpPositiveIncrementHalfPath (n : ℕ) :
    Measurable (sdpPositiveIncrementHalfPath n) := by
  have hz : ∀ j, Measurable (fun x => sdpPositiveIncrementSamples x j) := by
    intro j
    dsimp [sdpPositiveIncrementSamples]
    fun_prop
  have h := measurable_sdpScaledIntegerPositiveHalfPath n
    (fun x => sdpPositiveIncrementSamples x) hz
  have hzero (x : SdpPositiveIncrementBlock → ℤ) :
      (sdpScaledIntegerPositiveHalfPath n (sdpPositiveIncrementSamples x)).1
        ⟨0, le_rfl⟩ = 0 := by
    simp [sdpScaledIntegerPositiveHalfPath, sdpPositiveIncrementSamples]
  unfold sdpPositiveIncrementHalfPath
  exact Measurable.subtype_mk (f := fun x =>
    sdpScaledIntegerPositiveHalfPath n (sdpPositiveIncrementSamples x)) h (h := hzero)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem measurable_sdpNegativeIncrementHalfPath (n : ℕ) :
    Measurable (sdpNegativeIncrementHalfPath n) := by
  have hz : ∀ j, Measurable (fun x => sdpNegativeIncrementSamples x j) := by
    intro j
    dsimp [sdpNegativeIncrementSamples]
    fun_prop
  have h := measurable_sdpScaledIntegerPositiveHalfPath n
    (fun x => sdpNegativeIncrementSamples x) hz
  have hzero (x : SdpNonpositiveIncrementBlock → ℤ) :
      (sdpScaledIntegerPositiveHalfPath n (sdpNegativeIncrementSamples x)).1
        ⟨0, le_rfl⟩ = 0 := by
    simp [sdpScaledIntegerPositiveHalfPath, sdpNegativeIncrementSamples]
  unfold sdpNegativeIncrementHalfPath
  exact Measurable.subtype_mk (f := fun x =>
    sdpScaledIntegerPositiveHalfPath n (sdpNegativeIncrementSamples x)) h (h := hzero)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannIncrementBlocks_indep :
    IndepFun
      (fun ω (i : {k : ℤ // 0 < k}) =>
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω)
      (fun ω (i : {k : ℤ // k ≤ 0}) =>
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω)
      iidCodeMeasure := by
  have hdisj : Disjoint {k : ℤ | 0 < k} {k : ℤ | k ≤ 0} := by
    apply Set.disjoint_left.mpr
    intro k hk hk'
    change 0 < k at hk
    change k ≤ 0 at hk'
    exact (not_lt_of_ge hk') hk
  have hmeas (k : ℤ) : Measurable
      (fun ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω) := by
    change Measurable (fun ω =>
      busemannSDPMeasurableVersion ω k - busemannSDPMeasurableVersion ω (k - 1))
    exact (measurable_busemannSDPMeasurableVersion k).sub
      (measurable_busemannSDPMeasurableVersion (k - 1))
  exact sdpIncrements_iIndep_proved.indepFun_set
    {k : ℤ | 0 < k} {k : ℤ | k ≤ 0} hdisj hmeas

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem sdpPositiveIncrementSamples_eq (ω : ℕ → Fin 3) (j : ℕ) :
    sdpPositiveIncrementSamples
      (fun i => SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω) j =
      busemannSDPMeasurableVersion ω (j : ℤ) := by
  induction j with
  | zero => simp [sdpPositiveIncrementSamples, busemannSDPMeasurableVersion_zero]
  | succ j ih =>
    change (Finset.range (j + 1)).sum _ = _
    rw [Finset.sum_range_succ]
    have hsum := ih
    simp only [sdpPositiveIncrementSamples] at hsum
    rw [hsum]
    change busemannSDPMeasurableVersion ω (j : ℤ) +
      SDPMasterFromLaw.increment busemannSDPMeasurableVersion
        ((j : ℤ) + 1) ω = _
    simp only [SDPMasterFromLaw.increment]
    rw [Nat.cast_succ]
    ring_nf

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem sdpNegativeIncrementSum_eq (ω : ℕ → Fin 3) (j : ℕ) :
    (Finset.range (j + 1)).sum
      (fun i => SDPMasterFromLaw.increment busemannSDPMeasurableVersion
        (-(i : ℤ)) ω) =
      busemannSDPMeasurableVersion ω 0 -
        busemannSDPMeasurableVersion ω (-((j : ℤ) + 1)) := by
  induction j with
  | zero =>
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
    change busemannSDPMeasurableVersion ω 0 -
      busemannSDPMeasurableVersion ω (0 - 1) = _
    rfl
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have hinc : SDPMasterFromLaw.increment busemannSDPMeasurableVersion
        (-((j : ℤ) + 1)) ω =
        busemannSDPMeasurableVersion ω (-((j : ℤ) + 1)) -
          busemannSDPMeasurableVersion ω (-((j : ℤ) + 1) - 1) := by
      rfl
    have hidx : -((j + 1 : ℕ) : ℤ) = -((j : ℤ) + 1) := by norm_cast
    rw [hidx, hinc]
    have hstep : -((j : ℤ) + 1) - 1 = -(((j + 1 : ℕ) : ℤ) + 1) := by
      push_cast
      omega
    rw [hstep]
    ring_nf

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def sdpBusemannNegativeSamples (ω : ℕ → Fin 3) (j : ℕ) : ℤ :=
  if j = 0 then 0 else busemannSDPMeasurableVersion ω (-((j : ℤ) + 1))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem sdpNegativeIncrementSamples_eq (ω : ℕ → Fin 3) (j : ℕ) :
    sdpNegativeIncrementSamples
      (fun i => SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω) j =
      sdpBusemannNegativeSamples ω j := by
  by_cases hj : j = 0
  · subst j
    simp [sdpNegativeIncrementSamples, sdpBusemannNegativeSamples]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    simp [sdpNegativeIncrementSamples, sdpBusemannNegativeSamples, hj]
    rw [sdpNegativeIncrementSum_eq]
    simp [busemannSDPMeasurableVersion_zero]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def sdpBusemannWholeLinePositiveHalf (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocalZero :=
  ⟨sdpBusemannPositiveHalfPath n ω, by
    rw [sdpBusemannPositiveHalfPath_apply]
    simp [busemannSDPMeasurableVersion_zero]⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def sdpBusemannWholeLineNegativeHalfPath (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocal :=
  sdpScaledIntegerPositiveHalfPath n (sdpBusemannNegativeSamples ω)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannWholeLineNegativeHalfPath_zero (n : ℕ) (ω : ℕ → Fin 3) :
    (sdpBusemannWholeLineNegativeHalfPath n ω).1 ⟨0, le_rfl⟩ = 0 := by
  simp [sdpBusemannWholeLineNegativeHalfPath, sdpScaledIntegerPositiveHalfPath,
    sdpBusemannNegativeSamples]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def sdpBusemannWholeLineNegativeHalf (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocalZero :=
  ⟨sdpBusemannWholeLineNegativeHalfPath n ω,
    sdpBusemannWholeLineNegativeHalfPath_zero n ω⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem natFloor_coe_eq_intFloor (x : ℝ) (hx : 0 ≤ x) :
    (⌊x⌋₊ : ℤ) = ⌊x⌋ := by
  rw [← Int.floor_toNat]
  exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem sdpPositiveIncrementHalfPath_eq (n : ℕ) (ω : ℕ → Fin 3) :
    sdpPositiveIncrementHalfPath n
      (fun i => SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω) =
      sdpBusemannWholeLinePositiveHalf n ω := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  dsimp [sdpPositiveIncrementHalfPath, sdpScaledIntegerPositiveHalfPath,
    sdpBusemannWholeLinePositiveHalf]
  change ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
      (sdpPositiveIncrementSamples
        (fun i => SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω)
        ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ) =
      (sdpBusemannPositiveHalfPath n ω).1 t
  rw [sdpBusemannPositiveHalfPath_apply, sdpPositiveIncrementSamples_eq]
  have ht : 0 ≤ ((n + 1 : ℕ) : ℝ) * (t : ℝ) :=
    mul_nonneg (by positivity) t.property
  rw [natFloor_coe_eq_intFloor _ ht]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem sdpNegativeIncrementHalfPath_eq (n : ℕ) (ω : ℕ → Fin 3) :
    sdpNegativeIncrementHalfPath n
      (fun i => SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω) =
      sdpBusemannWholeLineNegativeHalf n ω := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  dsimp [sdpNegativeIncrementHalfPath, sdpScaledIntegerPositiveHalfPath,
    sdpBusemannWholeLineNegativeHalf, sdpBusemannWholeLineNegativeHalfPath]
  change ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
      (sdpNegativeIncrementSamples
        (fun i => SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω)
        ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ) =
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
      (sdpBusemannNegativeSamples ω
        ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ)
  rw [sdpNegativeIncrementSamples_eq]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem measurable_sdpPositiveIncrementBlock :
    Measurable (fun ω (i : SdpPositiveIncrementBlock) =>
      SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_busemannSDPMeasurableVersion i.1).sub
    (measurable_busemannSDPMeasurableVersion (i.1 - 1))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem measurable_sdpNonpositiveIncrementBlock :
    Measurable (fun ω (i : SdpNonpositiveIncrementBlock) =>
      SDPMasterFromLaw.increment busemannSDPMeasurableVersion i.1 ω) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_busemannSDPMeasurableVersion i.1).sub
    (measurable_busemannSDPMeasurableVersion (i.1 - 1))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem measurable_sdpBusemannWholeLinePositiveHalf (n : ℕ) :
    Measurable (fun ω => sdpBusemannWholeLinePositiveHalf n ω) := by
  have hfactor : (fun ω => sdpBusemannWholeLinePositiveHalf n ω) =
      sdpPositiveIncrementHalfPath n ∘
        (fun ω i => SDPMasterFromLaw.increment
          busemannSDPMeasurableVersion i.1 ω) := by
    funext ω
    exact (sdpPositiveIncrementHalfPath_eq n ω).symm
  rw [hfactor]
  exact (measurable_sdpPositiveIncrementHalfPath n).comp
    measurable_sdpPositiveIncrementBlock

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem measurable_sdpBusemannWholeLineNegativeHalf (n : ℕ) :
    Measurable (fun ω => sdpBusemannWholeLineNegativeHalf n ω) := by
  have hfactor : (fun ω => sdpBusemannWholeLineNegativeHalf n ω) =
      sdpNegativeIncrementHalfPath n ∘
        (fun ω i => SDPMasterFromLaw.increment
          busemannSDPMeasurableVersion i.1 ω) := by
    funext ω
    exact (sdpNegativeIncrementHalfPath_eq n ω).symm
  rw [hfactor]
  exact (measurable_sdpNegativeIncrementHalfPath n).comp
    measurable_sdpNonpositiveIncrementBlock

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannWholeLineHalfPaths_indep (n : ℕ) :
    IndepFun (fun ω => sdpBusemannWholeLinePositiveHalf n ω)
      (fun ω => sdpBusemannWholeLineNegativeHalf n ω) iidCodeMeasure := by
  have hblock := sdpBusemannIncrementBlocks_indep
  have hcomp := hblock.comp (measurable_sdpPositiveIncrementHalfPath n)
    (measurable_sdpNegativeIncrementHalfPath n)
  apply IndepFun.congr hcomp
  · exact Filter.Eventually.of_forall fun ω => sdpPositiveIncrementHalfPath_eq n ω
  · exact Filter.Eventually.of_forall fun ω => sdpNegativeIncrementHalfPath_eq n ω

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannWholeLineHalfPairLaw_eq_probabilityProduct (n : ℕ) :
    ProbabilityMeasure.map
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (fun ω =>
          (sdpBusemannWholeLinePositiveHalf n ω,
           sdpBusemannWholeLineNegativeHalf n ω)) =
      probabilityProduct
        (ProbabilityMeasure.map
          (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
          (sdpBusemannWholeLinePositiveHalf n))
        (ProbabilityMeasure.map
          (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
          (sdpBusemannWholeLineNegativeHalf n)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change iidCodeMeasure.map
      (fun ω =>
        (sdpBusemannWholeLinePositiveHalf n ω,
         sdpBusemannWholeLineNegativeHalf n ω)) =
    (iidCodeMeasure.map (fun ω => sdpBusemannWholeLinePositiveHalf n ω)).prod
      (iidCodeMeasure.map (fun ω => sdpBusemannWholeLineNegativeHalf n ω))
  exact (sdpBusemannWholeLineHalfPaths_indep n).map_prod_eq_prod_map_map
    (measurable_sdpBusemannWholeLinePositiveHalf n).aemeasurable
    (measurable_sdpBusemannWholeLineNegativeHalf n).aemeasurable

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem subtype_coe_tendsto_left_bound {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t : Set.Ici (0 : ℝ) => (t : ℝ))
      (nhdsWithin ⟨s, hs.le⟩ (Set.Iio ⟨s, hs.le⟩))
      (nhdsWithin s (Set.Iio s)) := by
  apply ContinuousWithinAt.tendsto_nhdsWithin
  · exact continuous_subtype_val.continuousWithinAt
  · intro t ht
    exact Set.mem_Iio.mpr (Subtype.coe_lt_coe.mpr ht)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The negative half's left limit is its ceiling-minus-one sample. -/
private theorem sdpBusemannNegativeHalf_leftLim_apply (n : ℕ) (ω : ℕ → Fin 3)
    {s : ℝ} (hs : 0 < s) :
    (sdpBusemannWholeLineNegativeHalf n ω).val.1.leftLim ⟨s, hs.le⟩ =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        (sdpBusemannNegativeSamples ω
          (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ) := by
  have hne : NeBot (𝓝[<] (⟨s, hs.le⟩ : Set.Ici (0 : ℝ))) :=
    nhdsLT_neBot_of_exists_lt ⟨⟨0, le_rfl⟩, hs⟩
  have h := floorStep_left_limit
    (fun j : ℤ => (sdpBusemannNegativeSamples ω j.toNat : ℝ))
    (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity) s
  have hc := h.comp (subtype_coe_tendsto_left_bound hs)
  have hc' : Tendsto
      (fun t : Set.Ici (0 : ℝ) =>
        ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
          (sdpBusemannNegativeSamples ω
            ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ))
      (nhdsWithin ⟨s, hs.le⟩ (Set.Iio ⟨s, hs.le⟩))
      (𝓝 (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        (sdpBusemannNegativeSamples ω
          (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ))) := by
    convert hc using 1
    · funext t
      congr 2
  change (sdpBusemannWholeLineNegativeHalfPath n ω).1.leftLim ⟨s, hs.le⟩ = _
  exact leftLim_eq_of_tendsto
    (f := fun t : Set.Ici (0 : ℝ) =>
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
      (sdpBusemannNegativeSamples ω
      ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ))
    (a := ⟨s, hs.le⟩)
    (y := ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
      (sdpBusemannNegativeSamples ω
        (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ))
    (h := hne) hc'

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The whole-line path and zero glue agree off the first negative mesh interval. -/
theorem sdpGlue_matches_outside_first_negative_step (n : ℕ) (ω : ℕ → Fin 3)
    {t : ℝ}
    (ht : t < -1 / ((n + 1 : ℕ) : ℝ) ∨ 0 ≤ t) :
    (wholeLineGlueZero
      (sdpBusemannWholeLinePositiveHalf n ω,
       sdpBusemannWholeLineNegativeHalf n ω)).1 t =
      (sdpBusemannWholeLinePath n ω).1 t := by
  rcases ht with ht | ht
  · have hb : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hrecip : 0 < 1 / ((n + 1 : ℕ) : ℝ) := one_div_pos.mpr hb
    have ht' : t < -(1 / ((n + 1 : ℕ) : ℝ)) := by
      simpa only [neg_div] using ht
    have hstep : 1 / ((n + 1 : ℕ) : ℝ) < -t := by
      have h := neg_lt_neg ht'
      simpa using h
    have hs : 0 < -t := lt_trans hrecip hstep
    have hbs : 1 < ((n + 1 : ℕ) : ℝ) * -t := by
      have hmul := (div_lt_iff₀ hb).mp hstep
      nlinarith only [hmul]
    change wholeLineGlue
      (sdpBusemannWholeLinePositiveHalf n ω).val
      (sdpBusemannWholeLineNegativeHalf n ω).val
      (sdpBusemannWholeLinePositiveHalf n ω).property
      (sdpBusemannWholeLineNegativeHalf n ω).property t = _
    have ht0 : t < 0 := lt_trans ht' (neg_lt_zero.mpr hrecip)
    rw [wholeLineGlue_negative _ _ _ _ ht0]
    rw [sdpBusemannNegativeHalf_leftLim_apply n ω hs]
    rw [sdpBusemannWholeLinePath_apply]
    have hceil : (1 : ℤ) < ⌈((n + 1 : ℕ) : ℝ) * -t⌉ := by
      exact Int.lt_ceil.mpr (by exact_mod_cast hbs)
    have hidx : 0 ≤ ⌈((n + 1 : ℕ) : ℝ) * -t⌉ - 1 := by omega
    have hidxcast :
        (((⌈((n + 1 : ℕ) : ℝ) * -t⌉ - 1).toNat : ℕ) : ℤ) =
          ⌈((n + 1 : ℕ) : ℝ) * -t⌉ - 1 := Int.toNat_of_nonneg hidx
    have hsample : sdpBusemannNegativeSamples ω
        (⌈((n + 1 : ℕ) : ℝ) * -t⌉ - 1).toNat =
          busemannSDPMeasurableVersion ω
            (-⌈((n + 1 : ℕ) : ℝ) * -t⌉) := by
      unfold sdpBusemannNegativeSamples
      rw [ite_eq_right (by
        intro h
        have hcast := congrArg (fun z : ℕ => (z : ℤ)) h
        rw [hidxcast] at hcast
        omega)]
      rw [hidxcast]
      congr 1
      omega
    have hfloor :
        ⌊((n + 1 : ℕ) : ℝ) * t⌋ =
          -⌈((n + 1 : ℕ) : ℝ) * -t⌉ := by
      rw [show ((n + 1 : ℕ) : ℝ) * t =
        -(((n + 1 : ℕ) : ℝ) * -t) by ring, Int.floor_neg]
    rw [hsample, hfloor]
  · change wholeLineGlue
      (sdpBusemannWholeLinePositiveHalf n ω).val
      (sdpBusemannWholeLineNegativeHalf n ω).val
      (sdpBusemannWholeLinePositiveHalf n ω).property
      (sdpBusemannWholeLineNegativeHalf n ω).property t = _
    rw [wholeLineGlue_nonnegative _ _ _ _ ⟨t, ht⟩]
    rw [sdpBusemannWholeLinePath_nonnegative n ω ⟨t, ht⟩]
    rfl

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The path and its zero glue differ only on the first negative mesh interval. -/
theorem sdpBusemannWholeLinePath_glue_value_bound (n : ℕ) (ω : ℕ → Fin 3)
    (t : ℝ) :
    |(sdpBusemannWholeLinePath n ω).1 t -
        (wholeLineGlueZero
          (sdpBusemannWholeLinePositiveHalf n ω,
           sdpBusemannWholeLineNegativeHalf n ω)).1 t| ≤
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        |(busemannSDPMeasurableVersion ω (-1) : ℝ)| := by
  by_cases hleft : t < -1 / ((n + 1 : ℕ) : ℝ)
  · rw [sdpGlue_matches_outside_first_negative_step n ω (Or.inl hleft)]
    simp
    positivity
  · by_cases hright : 0 ≤ t
    · rw [sdpGlue_matches_outside_first_negative_step n ω (Or.inr hright)]
      simp
      positivity
    · have hb : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hlo : -1 / ((n + 1 : ℕ) : ℝ) ≤ t := le_of_not_gt hleft
      have hhi : t < 0 := lt_of_not_ge hright
      have hs : 0 < -t := neg_pos.mpr hhi
      have hsle : -t ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
        have hlo' : -(1 / ((n + 1 : ℕ) : ℝ)) ≤ t := by
          simpa only [neg_div] using hlo
        linarith
      have hmul : 0 < ((n + 1 : ℕ) : ℝ) * -t ∧
          ((n + 1 : ℕ) : ℝ) * -t ≤ 1 := by
        constructor
        · exact mul_pos hb hs
        · calc
            ((n + 1 : ℕ) : ℝ) * -t ≤
                ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hsle hb.le
            _ = 1 := by field_simp
      have hceil : ⌈((n + 1 : ℕ) : ℝ) * -t⌉ = 1 :=
        Int.ceil_eq_iff.mpr (by constructor <;> norm_num at * <;> linarith)
      have hfloor : ⌊((n + 1 : ℕ) : ℝ) * t⌋ = -1 :=
        Int.floor_eq_iff.mpr ?_
      · have hglue :
            (wholeLineGlueZero
              (sdpBusemannWholeLinePositiveHalf n ω,
               sdpBusemannWholeLineNegativeHalf n ω)).1 t = 0 := by
          change wholeLineGlue
            (sdpBusemannWholeLinePositiveHalf n ω).val
            (sdpBusemannWholeLineNegativeHalf n ω).val
            (sdpBusemannWholeLinePositiveHalf n ω).property
            (sdpBusemannWholeLineNegativeHalf n ω).property t = 0
          rw [wholeLineGlue_negative _ _ _ _ hhi]
          rw [sdpBusemannNegativeHalf_leftLim_apply n ω hs, hceil]
          simp [sdpBusemannNegativeSamples]
        rw [sdpBusemannWholeLinePath_apply, hfloor, hglue]
        simp only [sub_zero]
        rw [abs_mul, abs_of_nonneg (by positivity :
          0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ))]
      · constructor
        · have hmul' := mul_le_mul_of_nonneg_left hlo hb.le
          have hprod :
              ((n + 1 : ℕ) : ℝ) * (-1 / ((n + 1 : ℕ) : ℝ)) = -1 := by
            field_simp
          rw [hprod] at hmul'
          exact_mod_cast hmul'
        · simpa using mul_neg_of_pos_of_neg hb hhi

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The finite-window J1 distance is bounded by the first-step error. -/
theorem sdpBusemannWholeLinePath_glue_window_distance_bound
    (n m : ℕ) (ω : ℕ → Fin 3) :
    wholeLineJ1WindowDistance m (sdpBusemannWholeLinePath n ω)
      (wholeLineGlueZero
        (sdpBusemannWholeLinePositiveHalf n ω,
         sdpBusemannWholeLineNegativeHalf n ω)) ≤
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        |(busemannSDPMeasurableVersion ω (-1) : ℝ)| := by
  let C := ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    |(busemannSDPMeasurableVersion ω (-1) : ℝ)|
  let : Nonempty (J1Window (2 * ((m : ℝ) + 1))) :=
    ⟨⟨0, ⟨le_rfl, (by positivity : 0 < 2 * ((m : ℝ) + 1)).le⟩⟩⟩
  have hsup :
      (⨆ u : J1Window (2 * ((m : ℝ) + 1)),
        |(wholeLineJ1WindowPath m (sdpBusemannWholeLinePath n ω)).1 u -
          (wholeLineJ1WindowPath m
            (wholeLineGlueZero
              (sdpBusemannWholeLinePositiveHalf n ω,
               sdpBusemannWholeLineNegativeHalf n ω))).1 u|) ≤ C := by
    apply ciSup_le
    intro u
    let t := wholeLineJ1WindowTime m u
    have hcut0 : 0 ≤ wholeLineJ1Cutoff m t := by
      unfold wholeLineJ1Cutoff
      positivity
    have hcut1 : wholeLineJ1Cutoff m t ≤ 1 := by
      unfold wholeLineJ1Cutoff
      exact max_le (by norm_num) (min_le_left _ _)
    have hpoint := sdpBusemannWholeLinePath_glue_value_bound n ω t
    change |wholeLineJ1Cutoff m t *
        (sdpBusemannWholeLinePath n ω).1 t -
      wholeLineJ1Cutoff m t *
        (wholeLineGlueZero
          (sdpBusemannWholeLinePositiveHalf n ω,
           sdpBusemannWholeLineNegativeHalf n ω)).1 t| ≤ C
    rw [← mul_sub, abs_mul]
    calc
      |wholeLineJ1Cutoff m t| *
          |(sdpBusemannWholeLinePath n ω).1 t -
            (wholeLineGlueZero
              (sdpBusemannWholeLinePositiveHalf n ω,
               sdpBusemannWholeLineNegativeHalf n ω)).1 t| ≤
        1 * C := mul_le_mul
          (by simpa only [abs_of_nonneg hcut0] using hcut1) hpoint
          (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
  change j1WindowDist (by positivity :
      0 < 2 * ((m : ℝ) + 1))
      (wholeLineJ1WindowPath m (sdpBusemannWholeLinePath n ω))
      (wholeLineJ1WindowPath m
        (wholeLineGlueZero
          (sdpBusemannWholeLinePositiveHalf n ω,
           sdpBusemannWholeLineNegativeHalf n ω))) ≤ C
  exact (j1WindowDist_le_sup_dist (by positivity) _ _).trans hsup

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The weighted whole-line local J1 distance is bounded by twice the first-step error. -/
theorem sdpBusemannWholeLinePath_glue_local_distance_bound
    (n : ℕ) (ω : ℕ → Fin 3) :
    dist (sdpBusemannWholeLinePath n ω)
      (wholeLineGlueZero
        (sdpBusemannWholeLinePositiveHalf n ω,
         sdpBusemannWholeLineNegativeHalf n ω)) ≤
      2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        |(busemannSDPMeasurableVersion ω (-1) : ℝ)|) := by
  let C := ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    |(busemannSDPMeasurableVersion ω (-1) : ℝ)|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  change wholeLineLocalJ1Distance _ _ ≤ 2 * C
  unfold wholeLineLocalJ1Distance
  have hgeom : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
    summable_geometric_two
  have hupper : Summable (fun m : ℕ => C * (1 / 2 : ℝ) ^ m) :=
    hgeom.mul_left C
  calc
    (∑' m : ℕ, wholeLineLocalJ1Term m
        (sdpBusemannWholeLinePath n ω)
        (wholeLineGlueZero
          (sdpBusemannWholeLinePositiveHalf n ω,
           sdpBusemannWholeLineNegativeHalf n ω))) ≤
      ∑' m : ℕ, C * (1 / 2 : ℝ) ^ m := by
        apply (wholeLineLocalJ1Term_summable _ _).tsum_le_tsum
        intro m
        rw [wholeLineLocalJ1Term]
        calc
          (1 / 2 : ℝ) ^ (m + 1) *
              min 1 (wholeLineJ1WindowDistance m
                (sdpBusemannWholeLinePath n ω)
                (wholeLineGlueZero
                  (sdpBusemannWholeLinePositiveHalf n ω,
                   sdpBusemannWholeLineNegativeHalf n ω))) ≤
            (1 / 2 : ℝ) ^ (m + 1) * C :=
              mul_le_mul_of_nonneg_left
                ((min_le_right _ _).trans
                  (sdpBusemannWholeLinePath_glue_window_distance_bound n m ω))
                (by positivity)
          _ ≤ C * (1 / 2 : ℝ) ^ m := by
            calc
              (1 / 2 : ℝ) ^ (m + 1) * C =
                  C * ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m) := by
                    rw [pow_succ]
                    ring
              _ ≤ C * (1 * (1 / 2 : ℝ) ^ m) :=
                mul_le_mul_of_nonneg_left (by norm_num) hC
              _ = C * (1 / 2 : ℝ) ^ m := by ring
        exact hupper
    _ = 2 * C := by
      rw [tsum_mul_left, tsum_geometric_two]
      ring


/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem measurableIntCastReal : Measurable (fun z : ℤ => (z : ℝ)) :=
  measurable_of_countable _

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem sdpBusemannJumpCoefficient_tendsto :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ))
      atTop (𝓝 0) := by
  have hq : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (f₁ := fun n : ℕ => (n : ℝ))
      (f₂ := fun n : ℕ => ((n + 1 : ℕ) : ℝ))
    · filter_upwards [] with n
      exact_mod_cast Nat.le_succ n
    · exact tendsto_natCast_atTop_atTop
  have h :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (3 / 4 : ℝ))).comp hq
  have hpow : (-3 / 4 : ℝ) = -(3 / 4 : ℝ) := by ring
  rw [hpow]
  change Tendsto
    ((fun x : ℝ => x ^ (-(3 / 4 : ℝ))) ∘
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0)
  exact h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The probability of a local J1 error of fixed positive size tends to zero. -/
theorem tendsto_iidCodeMeasure_real_sdpBusemannWholeLinePath_glue_error
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n => iidCodeMeasure.real
        {ω | ε ≤ dist (sdpBusemannWholeLinePath n ω)
          (wholeLineGlueZero
            (sdpBusemannWholeLinePositiveHalf n ω,
             sdpBusemannWholeLineNegativeHalf n ω))})
      atTop (𝓝 0) := by
  let B : (ℕ → Fin 3) → ℝ :=
    fun ω => (busemannSDPMeasurableVersion ω (-1) : ℝ)
  let S : ℕ → Set (ℕ → Fin 3) := fun n =>
    {ω | ε ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω|}
  have hB : Measurable B := by
    dsimp [B]
    exact measurableIntCastReal.comp
      (measurable_busemannSDPMeasurableVersion (-1))
  have hcoeff : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ))
      atTop (𝓝 0) := sdpBusemannJumpCoefficient_tendsto
  have hanti : Antitone S := by
    intro n m hnm ω hω
    change ε ≤ 2 * (((m + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω| at hω
    have hpow : ((m + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
      · exact_mod_cast Nat.add_le_add_right hnm 1
      · norm_num
    have hprod :
        2 * (((m + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω| ≤
          2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω| := by
      calc
        2 * (((m + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω| =
            2 * ((((m + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω|) := by
          ring
        _ ≤ 2 * ((((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)) (by norm_num)
        _ = 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω| := by
          ring
    exact hω.trans hprod
  have hSmeas : ∀ n, MeasurableSet (S n) := by
    intro n
    change MeasurableSet
      {ω | ε ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω|}
    exact measurableSet_le measurable_const
      ((measurable_const : Measurable
        (fun _ : ℕ → Fin 3 =>
          2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)))).mul
        (continuous_abs.measurable.comp hB))
  have hinter : (⋂ n, S n) = ∅ := by
    ext ω
    constructor
    · intro hω
      have hlim : Tendsto
          (fun n : ℕ => 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω|)
          atTop (𝓝 0) := by
        simpa only [mul_zero, zero_mul] using
          (hcoeff.const_mul (2 : ℝ)).mul_const (|B ω|)
      obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
      have hωn : ε ≤
          2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω| := by
        exact Set.mem_iInter.mp hω n
      exact (not_lt_of_ge hωn) hn
    · simp
  have hcont : Tendsto (fun n => iidCodeMeasure (S n)) atTop
      (𝓝 (iidCodeMeasure (⋂ n, S n))) :=
    tendsto_measure_iInter_atTop
      (fun n => (hSmeas n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top iidCodeMeasure (S 0)⟩
  have hcontZero : Tendsto (fun n => iidCodeMeasure (S n)) atTop
      (𝓝 0) := by
    simpa only [hinter, measure_empty] using hcont
  have hcontReal : Tendsto (fun n => iidCodeMeasure.real (S n)) atTop
      (𝓝 0) := by
    change Tendsto
      (ENNReal.toReal ∘ fun n => iidCodeMeasure (S n)) atTop (𝓝 0)
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcontZero
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [(Metric.tendsto_nhds.mp hcontReal δ hδ)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hn' : iidCodeMeasure.real (S n) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hn
  calc
    iidCodeMeasure.real
        {ω | ε ≤ dist (sdpBusemannWholeLinePath n ω)
          (wholeLineGlueZero
            (sdpBusemannWholeLinePositiveHalf n ω,
             sdpBusemannWholeLineNegativeHalf n ω))} ≤
        iidCodeMeasure.real (S n) := by
      change (iidCodeMeasure
        {ω | ε ≤ dist (sdpBusemannWholeLinePath n ω)
          (wholeLineGlueZero
            (sdpBusemannWholeLinePositiveHalf n ω,
             sdpBusemannWholeLineNegativeHalf n ω))}).toReal ≤
        (iidCodeMeasure (S n)).toReal
      refine ENNReal.toReal_mono
        (measure_ne_top iidCodeMeasure (S n)) ?_
      apply measure_mono
      intro ω hω
      change ε ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) * |B ω|
      change ε ≤ dist (sdpBusemannWholeLinePath n ω)
        (wholeLineGlueZero
          (sdpBusemannWholeLinePositiveHalf n ω,
           sdpBusemannWholeLineNegativeHalf n ω)) at hω
      have hbound :=
        sdpBusemannWholeLinePath_glue_local_distance_bound n ω
      exact hω.trans (by simpa [B, mul_assoc] using hbound)
    _ < δ := hn'


end DirectedDistances.Recursive
