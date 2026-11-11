module

public import DirectedDistances.Recursive.BusemannNegativeHalfLimitSdp
public import DirectedDistances.Recursive.BusemannWindowLimitsSymOnly
import all DirectedDistances.Recursive.BusemannWholeLineSdpPieces
import all DirectedDistances.Probability.SkorokhodJ1WholeLineLocal
import DirectedDistances.Probability.SkorokhodFloorStep
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Assembly helpers for the SDP part of Theorem 1.6, conditional on index-zero
increment-law symmetry for the measurable code representative. The two half laws
have distinct index-4/3 cutoff limits. Independence gives the product law, continuous
left-limit gluing gives its whole-line limit, and a vanishing first-negative-mesh
error transfers convergence to the literal floor process at exponent 3/4. -/

public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped Topology

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannWholeLinePositiveHalf_measurable (n : ℕ) :
    Measurable (sdpBusemannWholeLinePositiveHalf n) :=
  measurable_sdpBusemannWholeLinePositiveHalf n

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The positive marginal in the zero-at-zero carrier. -/
@[expose] noncomputable def sdpBusemannWholeLinePositiveHalfLaw (n : ℕ) :
    ProbabilityMeasure CadlagLocalZero :=
  ProbabilityMeasure.map
    (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (sdpBusemannWholeLinePositiveHalf n)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The negative marginal, with the actual shifted samples used by zero gluing. -/
@[expose] noncomputable def sdpBusemannWholeLineNegativeHalfLaw (n : ℕ) :
    ProbabilityMeasure CadlagLocalZero :=
  ProbabilityMeasure.map
    (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (sdpBusemannWholeLineNegativeHalf n)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The joint law of the two actual half-path random elements. -/
@[expose] noncomputable def sdpBusemannWholeLineHalfPairLaw (n : ℕ) :
    ProbabilityMeasure (CadlagLocalZero × CadlagLocalZero) :=
  ProbabilityMeasure.map
    (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (fun ω => (sdpBusemannWholeLinePositiveHalf n ω,
      sdpBusemannWholeLineNegativeHalf n ω))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Finite-scale independence is unconditional for the code representative. -/
theorem sdpBusemannWholeLineHalfPairLaw_eq_product (n : ℕ) :
    sdpBusemannWholeLineHalfPairLaw n =
      probabilityProduct (sdpBusemannWholeLinePositiveHalfLaw n)
        (sdpBusemannWholeLineNegativeHalfLaw n) :=
  sdpBusemannWholeLineHalfPairLaw_eq_probabilityProduct n

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Separate marginal convergence gives the independent product limit. No probability -/
theorem sdpBusemannWholeLineHalfPairLaw_tendsto
    {μ ν : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν) :
    Tendsto sdpBusemannWholeLineHalfPairLaw atTop (𝓝 (probabilityProduct μ ν)) := by
  have hprod := tendsto_prod_of_tendsto hμ hν.2
  exact hprod.congr' (Eventually.of_forall fun n =>
    (sdpBusemannWholeLineHalfPairLaw_eq_product n).symm)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The glued random path, before the vanishing first-mesh correction. -/
@[expose] noncomputable def sdpBusemannWholeLineGluedPath (n : ℕ)
    (ω : ℕ → Fin 3) : WholeLineCadlag :=
  wholeLineGlueZero (sdpBusemannWholeLinePositiveHalf n ω,
    sdpBusemannWholeLineNegativeHalf n ω)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannWholeLineGluedPath_measurable (n : ℕ) :
    Measurable (sdpBusemannWholeLineGluedPath n) :=
  measurable_wholeLineGlueZero.comp
    ((sdpBusemannWholeLinePositiveHalf_measurable n).prodMk
      (sdpBusemannWholeLineNegativeHalf_measurable n))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Glued laws converge in whole-line local J1 whenever the separate half laws converge. -/
theorem sdpBusemannWholeLineGluedLaw_tendsto
    {μ ν : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν) :
    Tendsto (fun n =>
      ProbabilityMeasure.map
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (sdpBusemannWholeLineGluedPath n)) atTop
      (𝓝 ((probabilityProduct μ ν).map wholeLineGlueZero)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (sdpBusemannWholeLineHalfPairLaw_tendsto hμ hν) continuous_wholeLineGlueZero
  convert h using 1
  funext n
  apply ProbabilityMeasure.toMeasure_injective
  exact (Measure.map_map measurable_wholeLineGlueZero
    ((sdpBusemannWholeLinePositiveHalf_measurable n).prodMk
      (sdpBusemannWholeLineNegativeHalf_measurable n))).symm

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The actual floor path and zero glue become arbitrarily close for every code; this -/
theorem sdpBusemannWholeLinePath_glue_dist_tendsto (ω : ℕ → Fin 3) :
    Tendsto (fun n => dist (sdpBusemannWholeLinePath n ω)
      (sdpBusemannWholeLineGluedPath n ω)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => 2 *
      (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        |(busemannSDPMeasurableVersion ω (-1) : ℝ)|)) atTop (𝓝 0) := by
    simpa using (sdpBusemannJumpCoefficient_tendsto.mul_const
      |(busemannSDPMeasurableVersion ω (-1) : ℝ)|).const_mul 2
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun n => sdpBusemannWholeLinePath_glue_local_distance_bound n ω) hupper

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Finite integer clipping used only for measurability. -/
private noncomputable def sdpClippedWholeLinePath (n M : ℕ) (z : ℤ → ℤ) :
    WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    (z (max (-(M : ℤ)) (min ⌊((n + 1 : ℕ) : ℝ) * t⌋ (M : ℤ))) : ℝ),
    floorStep_isCadlag
      (fun j => (z (max (-(M : ℤ)) (min j (M : ℤ))) : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Clipping eventually leaves every fixed whole-line window unchanged. -/
private theorem sdpClippedWholeLinePath_tendsto (n : ℕ) (ω : ℕ → Fin 3) :
    Tendsto (fun M => sdpClippedWholeLinePath n M (busemannSDPMeasurableVersion ω))
      atTop (𝓝 (sdpBusemannWholeLinePath n ω)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply (wholeLineLocalJ1Distance_tendsto_iff_window_tendsto _ _).mpr
  intro m
  have heq : ∀ᶠ M : ℕ in atTop,
      wholeLineJ1WindowDistance m
        (sdpClippedWholeLinePath n M (busemannSDPMeasurableVersion ω))
        (sdpBusemannWholeLinePath n ω) = 0 := by
    filter_upwards [eventually_ge_atTop ((n + 1) * (m + 1))] with M hM
    have hp : wholeLineJ1WindowPath m
        (sdpClippedWholeLinePath n M (busemannSDPMeasurableVersion ω)) =
        wholeLineJ1WindowPath m (sdpBusemannWholeLinePath n ω) := by
      apply Subtype.ext
      funext u
      let t : ℝ := (u : ℝ) - ((m : ℝ) + 1)
      have htlo : -((m : ℝ) + 1) ≤ t := by dsimp [t]; linarith [u.property.1]
      have hthi : t ≤ (m : ℝ) + 1 := by dsimp [t]; linarith [u.property.2]
      have hMr : ((n + 1 : ℕ) : ℝ) * ((m : ℝ) + 1) ≤ (M : ℝ) := by
        exact_mod_cast hM
      have hlo : -(M : ℤ) ≤ ⌊((n + 1 : ℕ) : ℝ) * t⌋ := by
        apply Int.le_floor.mpr
        have hh := mul_le_mul_of_nonneg_left htlo
          (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))
        push_cast at hMr hh ⊢
        nlinarith only [hh, hMr]
      have hhi : ⌊((n + 1 : ℕ) : ℝ) * t⌋ ≤ (M : ℤ) := by
        apply Int.floor_le_iff.mpr
        have hh := mul_le_mul_of_nonneg_left hthi
          (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))
        push_cast at hMr hh ⊢
        linarith only [hh, hMr]
      change wholeLineJ1Cutoff m t * (_ *
        (busemannSDPMeasurableVersion ω
          (max (-(M : ℤ)) (min ⌊((n + 1 : ℕ) : ℝ) * t⌋ (M : ℤ))) : ℝ)) =
        wholeLineJ1Cutoff m t * (_ *
          (busemannSDPMeasurableVersion ω ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ))
      rw [min_eq_left hhi, max_eq_right hlo]
    change j1WindowDist _ _ _ = 0
    rw [hp]
    exact j1WindowDist_self _ _
  exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The actual whole-line floor path is Borel measurable in local J1. -/
theorem sdpBusemannWholeLinePath_measurable (n : ℕ) :
    Measurable (sdpBusemannWholeLinePath n) := by
  have hm (M : ℕ) : Measurable
      (fun ω => sdpClippedWholeLinePath n M (busemannSDPMeasurableVersion ω)) := by
    let I := ↥(Finset.Icc (-(M : ℤ)) (M : ℤ))
    let v : (ℕ → Fin 3) → I → ℤ := fun ω i =>
      busemannSDPMeasurableVersion ω i.val
    have hv : Measurable v := Measurable.of_eval fun _ =>
      measurable_busemannSDPMeasurableVersion _
    have hc (j : ℤ) : max (-(M : ℤ)) (min j (M : ℤ)) ∈
        Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    let g : (I → ℤ) → WholeLineCadlag := fun x =>
      ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
        (x ⟨max (-(M : ℤ)) (min ⌊((n + 1 : ℕ) : ℝ) * t⌋ (M : ℤ)), hc _⟩ : ℝ),
        floorStep_isCadlag
          (fun j => (x ⟨max (-(M : ℤ)) (min j (M : ℤ)), hc j⟩ : ℝ))
          (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)⟩
    exact (measurable_of_countable g).comp hv
  apply measurable_of_tendsto_metrizable hm
  exact tendsto_pi_nhds.mpr (sdpClippedWholeLinePath_tendsto n)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Whole-line law of the literal floor process, including its first negative mesh step. -/
@[expose] noncomputable def sdpBusemannWholeLineLaw (n : ℕ) :
    ProbabilityMeasure WholeLineCadlag :=
  ProbabilityMeasure.map
    (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (sdpBusemannWholeLinePath n)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The first-mesh correction preserves every weak limit of the glued laws, by bounded
Lipschitz tests and dominated convergence. This avoids assuming separability of the -/
theorem sdpBusemannWholeLineLaw_tendsto_of_gluedLaw_tendsto
    {ρ : ProbabilityMeasure WholeLineCadlag}
    (hglue : Tendsto (fun n => ProbabilityMeasure.map
      (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
      (sdpBusemannWholeLineGluedPath n)) atTop (𝓝 ρ)) :
    Tendsto sdpBusemannWholeLineLaw atTop (𝓝 ρ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  let x₀ := sdpBusemannWholeLinePath 0 (fun _ => 0)
  let B := C + |f x₀|
  have hB (x : WholeLineCadlag) : |f x| ≤ B := by
    have hh : |f x - f x₀| ≤ C := by simpa only [Real.dist_eq] using hC x x₀
    calc
      |f x| = |f x - f x₀ + f x₀| := by congr 1; ring
      _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
      _ ≤ B := add_le_add hh le_rfl
  have hX (n : ℕ) : Integrable
      (fun ω => f (sdpBusemannWholeLinePath n ω)) iidCodeMeasure :=
    Integrable.of_bound
      ((hL.continuous.measurable.comp
        (sdpBusemannWholeLinePath_measurable n)).aestronglyMeasurable)
      B (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hB _)
  have hY (n : ℕ) : Integrable
      (fun ω => f (sdpBusemannWholeLineGluedPath n ω)) iidCodeMeasure :=
    Integrable.of_bound
      ((hL.continuous.measurable.comp
        (sdpBusemannWholeLineGluedPath_measurable n)).aestronglyMeasurable)
      B (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hB _)
  have hdiff : Tendsto (fun n => ∫ ω,
      (f (sdpBusemannWholeLinePath n ω) - f (sdpBusemannWholeLineGluedPath n ω))
        ∂iidCodeMeasure) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence
      (μ := iidCodeMeasure) (f := fun _ => (0 : ℝ)) (fun _ => 2 * B)
      (fun n => ((hX n).sub (hY n)).aestronglyMeasurable) (integrable_const _) ?_ ?_
    · simpa only [integral_zero, Pi.sub_apply] using hd
    · intro n
      exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        have hxB := hB (sdpBusemannWholeLinePath n ω)
        have hyB := hB (sdpBusemannWholeLineGluedPath n ω)
        exact (abs_sub _ _).trans (by linarith only [hxB, hyB])
    · exact ae_of_all _ fun ω => by
        refine squeeze_zero_norm
          (a := fun n : ℕ => (L : ℝ) * dist (sdpBusemannWholeLinePath n ω)
            (sdpBusemannWholeLineGluedPath n ω)) ?_ ?_
        · intro n
          change |f (sdpBusemannWholeLinePath n ω) -
            f (sdpBusemannWholeLineGluedPath n ω)| ≤ _
          simpa only [Real.dist_eq] using
            hL.dist_le_mul (sdpBusemannWholeLinePath n ω)
              (sdpBusemannWholeLineGluedPath n ω)
        · simpa only [mul_zero] using
            (sdpBusemannWholeLinePath_glue_dist_tendsto ω).const_mul (L : ℝ)
  have hmX (n : ℕ) :
      (∫ x, f x ∂(sdpBusemannWholeLineLaw n : Measure WholeLineCadlag)) =
        ∫ ω, f (sdpBusemannWholeLinePath n ω) ∂iidCodeMeasure := by
    exact integral_map (sdpBusemannWholeLinePath_measurable n).aemeasurable
      hL.continuous.stronglyMeasurable.aestronglyMeasurable
  have hmY (n : ℕ) :
      (∫ x, f x ∂(ProbabilityMeasure.map
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (sdpBusemannWholeLineGluedPath n) : Measure WholeLineCadlag)) =
        ∫ ω, f (sdpBusemannWholeLineGluedPath n ω) ∂iidCodeMeasure := by
    exact integral_map (sdpBusemannWholeLineGluedPath_measurable n).aemeasurable
      hL.continuous.stronglyMeasurable.aestronglyMeasurable
  have hy := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hglue) f ⟨C, hC⟩ ⟨L, hL⟩
  simp_rw [hmY] at hy
  have hh := hdiff.add hy
  simp only [zero_add] at hh
  convert hh using 1
  funext n
  rw [hmX, integral_sub (hX n) (hY n), sub_add_cancel]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Whole-line local-J1 convergence of the literal floor path follows from the two
separate marginal limits, with the independent product glued by left limits.
The separate marginal inputs are discharged in the final symmetry-only assembly. -/
theorem sdpBusemannWholeLineLaw_tendsto_of_halfLimits
    {μ ν : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ))
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν) :
    Tendsto sdpBusemannWholeLineLaw atTop
      (𝓝 ((probabilityProduct μ ν).map wholeLineGlueZero)) :=
  sdpBusemannWholeLineLaw_tendsto_of_gluedLaw_tendsto
    (sdpBusemannWholeLineGluedLaw_tendsto hμ hν)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The value at the origin is continuous in half-line local J1. -/
private theorem sdpContinuousHalfLineOrigin :
    Continuous (fun x : CadlagLocal => x.1 ⟨0, le_rfl⟩) := by
  have he := continuous_j1WindowD_eval_zero
    (by positivity : (0 : ℝ) < ((0 : Fin 1).val : ℝ) + 1)
  have hw := (continuous_apply (0 : Fin 1)).comp (finiteCutoffWindows_continuous 0)
  have h := he.comp hw
  convert h using 1
  funext x
  simp [finiteCutoffWindows, toJ1WindowD, cutoffWindow, localWindowTime, localCutoff]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Forgetting the zero-at-zero proof recovers the existing positive-half law. -/
private theorem sdpPositiveHalfLaw_map_val (n : ℕ) :
    (sdpBusemannWholeLinePositiveHalfLaw n : Measure CadlagLocalZero).map
      (Subtype.val : CadlagLocalZero → CadlagLocal) =
        (sdpBusemannPositiveHalfLaw n : Measure CadlagLocal) := by
  change (iidCodeMeasure.map (sdpBusemannWholeLinePositiveHalf n)).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe
    (sdpBusemannWholeLinePositiveHalf_measurable n)]
  rfl

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The proved positive-half convergence lifts to the zero-at-zero carrier, retaining
the selected finite cutoff laws. Only index-zero symmetry remains explicit. -/
theorem sdpBusemannWholeLinePositiveHalfLaw_tendsto_of_sym
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) :
    ∃ μ : ProbabilityMeasure CadlagLocalZero,
      Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ) ∧
      ∀ N, (ProbabilityMeasure.map μ (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) =
          sdpBusemannPositiveCutoffLimit sdpIncrements_iIndep_proved hsym N := by
  obtain ⟨ν, hν, hcut⟩ :=
    sdpBusemannPositiveHalfLaw_tendsto_of_sym hsym
  let S : Set CadlagLocal := {x | x.1 ⟨0, le_rfl⟩ = 0}
  have hS : IsClosed S := isClosed_eq sdpContinuousHalfLineOrigin continuous_const
  have hn (n : ℕ) : (sdpBusemannPositiveHalfLaw n : Measure CadlagLocal) S = 1 := by
    rw [sdpBusemannPositiveHalfLaw_toMeasure,
      Measure.map_apply (measurable_sdpBusemannPositiveHalfPath n) hS.measurableSet]
    have heq : sdpBusemannPositiveHalfPath n ⁻¹' S = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact sdpBusemannPositiveHalfPath_zero n ω
    rw [heq, measure_univ]
  have hνS : (ν : Measure CadlagLocal) S = 1 := by
    apply le_antisymm (by simpa only [measure_univ] using
      (measure_mono (Set.subset_univ S) : (ν : Measure CadlagLocal) S ≤
        (ν : Measure CadlagLocal) Set.univ))
    have hb := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν hS
    simpa only [hn, limsup_const] using hb
  have hae : ∀ᵐ x ∂(ν : Measure CadlagLocal), x ∈ S :=
    (mem_ae_iff_prob_eq_one hS.measurableSet).mpr hνS
  have he : MeasurableEmbedding (Subtype.val : CadlagLocalZero → CadlagLocal) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hp : IsProbabilityMeasure
      ((ν : Measure CadlagLocal).comap (Subtype.val : CadlagLocalZero → CadlagLocal)) :=
    he.isProbabilityMeasure_comap (by
      change ∀ᵐ x ∂(ν : Measure CadlagLocal), x ∈ Set.range
        (Subtype.val : S → CadlagLocal)
      simpa only [Subtype.range_coe] using hae)
  let μ : ProbabilityMeasure CadlagLocalZero :=
    ⟨(ν : Measure CadlagLocal).comap Subtype.val, hp⟩
  have hmap : (μ : Measure CadlagLocalZero).map Subtype.val =
      (ν : Measure CadlagLocal) := by
    exact (map_comap_subtype_coe hS.measurableSet _).trans
      (Measure.restrict_eq_self_of_ae_mem hae)
  refine ⟨μ, ?_, ?_⟩
  · apply tendsto_of_forall_isClosed_limsup_le'
    intro F hF
    have hFi : IsClosed ((Subtype.val : CadlagLocalZero → CadlagLocal) '' F) :=
      (Topology.IsClosedEmbedding.subtypeVal hS).isClosedMap F hF
    have hμF : (μ : Measure CadlagLocalZero) F =
        (ν : Measure CadlagLocal) (Subtype.val '' F) := by
      rw [← hmap, Measure.map_apply measurable_subtype_coe hFi.measurableSet,
        Set.preimage_image_eq F Subtype.coe_injective]
    have hnF (n : ℕ) : (sdpBusemannWholeLinePositiveHalfLaw n : Measure _) F =
        (sdpBusemannPositiveHalfLaw n : Measure _) (Subtype.val '' F) := by
      rw [← sdpPositiveHalfLaw_map_val n,
        Measure.map_apply measurable_subtype_coe hFi.measurableSet,
        Set.preimage_image_eq F Subtype.coe_injective]
    simp_rw [hnF, hμF]
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν hFi
  · have heq : ProbabilityMeasure.map μ
        (Subtype.val : CadlagLocalZero → CadlagLocal) = ν :=
      ProbabilityMeasure.toMeasure_injective hmap
    simpa only [heq] using hcut

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Conditional on `hsym_sdp` only: whole-line local-J1 convergence of the literal SDP
floor path to the left-limit glue of independent positive and symmetric negative
index-4/3 half limits, retaining both families of cutoff laws. This concerns the
measurable code representative and is not Theorem 1.6 itself; its paper-facing
source identification and the symmetry premise remain separate obligations. -/
theorem sdpBusemannWholeLineLaw_tendsto_of_sym
    (hsym_sdp : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
        iidCodeMeasure.map
          (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) :
    ∃ (μpos μneg : ProbabilityMeasure CadlagLocalZero),
      Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μpos) ∧
      (∀ N, (ProbabilityMeasure.map μpos
        (Subtype.val : CadlagLocalZero → CadlagLocal)).map
          (finiteCutoffWindows N) =
            sdpBusemannPositiveCutoffLimit sdpIncrements_iIndep_proved hsym_sdp N) ∧
      SdpBusemannWholeLineNegativeHalfConverges μneg ∧
      (∀ N, (μneg.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) = negativeHalfSdpCutoffLimit hsym_sdp N) ∧
      Tendsto sdpBusemannWholeLineLaw atTop
        (𝓝 ((probabilityProduct μpos μneg).map wholeLineGlueZero)) := by
  obtain ⟨μpos, hpos, hpos_cut⟩ :=
    sdpBusemannWholeLinePositiveHalfLaw_tendsto_of_sym hsym_sdp
  obtain ⟨μneg, hneg, hneg_cut⟩ :=
    sdpBusemannWholeLineNegativeHalfConverges_of_sym hsym_sdp
  exact ⟨μpos, μneg, hpos, hpos_cut, hneg, hneg_cut,
    sdpBusemannWholeLineLaw_tendsto_of_halfLimits hpos hneg⟩

end DirectedDistances.Recursive
