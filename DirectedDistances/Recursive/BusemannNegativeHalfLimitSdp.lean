module

public import DirectedDistances.Recursive.BusemannWholeLineSdpPieces
import all DirectedDistances.Recursive.BusemannWholeLineSdpPieces
public import DirectedDistances.Recursive.BusemannItemsSymOnly
public import DirectedDistances.Probability.SkewedStableProcessFdd
public import DirectedDistances.Probability.ScaledWindowModulusGtOne
import all DirectedDistances.Recursive.BusemannPositiveHalfLaw
import all DirectedDistances.Recursive.BusemannFddStable
import all DirectedDistances.Recursive.BusemannWindowLimit
import all DirectedDistances.Recursive.BusemannWindowLimitNoFixedJumps
import DirectedDistances.Recursive.BusemannIncrementPowerTail
import DirectedDistances.Recursive.SDPQuadraticFromMaster
import DirectedDistances.Probability.SkewedStableHexpOfPos
import all DirectedDistances.Probability.SkorokhodJ1WholeLineLocal
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The SDP negative half has symmetric stable index `4 / 3`, with scaling exponent
`3 / 4`. The real transform expansion supplies the symmetric characteristic
function. The absolute power tail and proved zero mean supply centered tightness.
Window convergence, projective realization, local J1 convergence, and the
vanishing shifted-path correction follow for the measurable code representative.
Its source-identification gates are inherited from the imported modules. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology ENNReal

local notation "P" => iidCodeMeasure
local notation "Y" => busemannSDPMeasurableVersion

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] def SdpBusemannWholeLineNegativeHalfConverges
    (ν : ProbabilityMeasure CadlagLocalZero) : Prop :=
  (∀ n, Measurable (sdpBusemannWholeLineNegativeHalf n)) ∧
    Tendsto
      (fun n => ProbabilityMeasure.map
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (sdpBusemannWholeLineNegativeHalf n))
      atTop (𝓝 ν)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannWholeLineNegativeHalf_measurable (n : ℕ) :
    Measurable (sdpBusemannWholeLineNegativeHalf n) :=
  measurable_sdpBusemannWholeLineNegativeHalf n

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannReflectedIncrements_iIndep :
    iIndepFun (fun j : ℕ => fun ω =>
      -SDPMasterFromLaw.increment Y (-(j : ℤ)) ω) P := by
  have hinj : Function.Injective (fun j : ℕ => -(j : ℤ)) := by
    intro i j h
    exact_mod_cast neg_injective h
  exact (iIndepFun.precomp hinj sdpIncrements_iIndep_proved).comp
    (fun _ => fun z : ℤ => -z) (fun _ => measurable_neg)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem sdpBusemannReflectedIncrement_law
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) (j : ℕ) :
    iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y (-(j : ℤ)) ω) =
      iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) := by
  have hm (k : ℤ) : Measurable (SDPMasterFromLaw.increment Y k) :=
    (measurable_busemannSDPMeasurableVersion _).sub
      (measurable_busemannSDPMeasurableVersion _)
  change iidCodeMeasure.map ((fun z : ℤ => -z) ∘ SDPMasterFromLaw.increment Y (-(j : ℤ))) = _
  rw [← Measure.map_map measurable_neg (hm _),
    busemannSDPMeasurableVersion_left_stationary _ (by omega),
    Measure.map_map measurable_neg (hm _)]
  exact hsym.symm

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfSdpIncrement (j : ℕ) (ω : ℕ → Fin 3) : ℝ :=
  (-SDPMasterFromLaw.increment Y (-((j : ℤ) + 1)) ω : ℤ)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpIncrement_measurable (j : ℕ) :
    Measurable (negativeHalfSdpIncrement j) := by
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    (((measurable_busemannSDPMeasurableVersion _).sub
      (measurable_busemannSDPMeasurableVersion _)).neg)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpIncrement_iIndep : iIndepFun negativeHalfSdpIncrement P := by
  have h := (sdpBusemannReflectedIncrements_iIndep.precomp
    (show Function.Injective (fun j : ℕ => j + 1) from by
      intro a b h
      dsimp at h
      omega)).comp
      (fun _ => fun z : ℤ => (z : ℝ)) (fun _ => measurable_of_countable _)
  change iIndepFun (fun (j : ℕ) ω =>
    ((-SDPMasterFromLaw.increment Y (-((j : ℤ) + 1)) ω : ℤ) : ℝ)) P
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpIncrement_ident
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    (j : ℕ) :
    IdentDistrib (negativeHalfSdpIncrement j) (fun ω => (SDPMasterFromLaw.increment Y 0 ω : ℝ)) P
      P := by
  have hD (k : ℤ) : Measurable (SDPMasterFromLaw.increment Y k) :=
    (measurable_busemannSDPMeasurableVersion _).sub
      (measurable_busemannSDPMeasurableVersion _)
  have h : IdentDistrib
      (fun ω => -SDPMasterFromLaw.increment Y (-((j : ℤ) + 1)) ω) (SDPMasterFromLaw.increment Y 0)
        P P :=
    ⟨(hD _).neg.aemeasurable, (hD _).aemeasurable, by
      simpa only [Nat.cast_add, Nat.cast_one] using
        sdpBusemannReflectedIncrement_law hsym (j + 1)⟩
  exact h.comp (measurable_of_countable (fun z : ℤ => (z : ℝ)))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpIncrement_identDistrib
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    (j : ℕ) : IdentDistrib (negativeHalfSdpIncrement j) (negativeHalfSdpIncrement 0) P P :=
  (negativeHalfSdpIncrement_ident hsym j).trans
    (negativeHalfSdpIncrement_ident hsym 0).symm

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfSdpScale : ℝ :=
  (SDPMasterFromLaw.sdpG P Y (-1)) ^ (2 / 3 : ℝ)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpScale_pos
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    0 < negativeHalfSdpScale := by
  apply Real.rpow_pos_of_pos
  exact (SDPExpansion.sdp_real_transform_dichotomy_of_master
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsym) busemann_sdpG_zero_below
    (sdp_master_equation_of_sym hsym)).1

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpIncrement_charFun_expansion
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    (fun s : ℝ => charFun (iidCodeMeasure.map (negativeHalfSdpIncrement 0)) s -
      (1 - (negativeHalfSdpScale : ℂ) * (|s| ^ (4 / 3 : ℝ) : ℝ)))
      =o[𝓝 0] (fun s : ℝ => |s| ^ (4 / 3 : ℝ)) := by
  have hrec := sdp_master_equation_of_sym hsym
  have hκ := (sdp_tail_asymptotics_explicit_of_sym hsym).1
  have hdicho := SDPExpansion.sdp_real_transform_dichotomy_of_master
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsym) busemann_sdpG_zero_below hrec
  have hsmall : (fun s : ℝ => SDPExpansion.integerCF (SDPMasterFromLaw.sdpF P Y) s -
      (1 - (negativeHalfSdpScale : ℂ) * (s ^ (4 / 3 : ℝ) : ℝ)))
      =o[𝓝[>] 0] (fun s : ℝ => ((s ^ (4 / 3 : ℝ) : ℝ) : ℂ)) := by
    rcases hdicho.2 with hzero | hpos
    · exact hzero.2
    · exfalso
      rw [hκ] at hpos
      exact (lt_irrefl 0) hpos.1
  have hD : Measurable (SDPMasterFromLaw.increment Y 0) :=
    (measurable_busemannSDPMeasurableVersion _).sub
      (measurable_busemannSDPMeasurableVersion _)
  have hcf (s : ℝ) : charFun (iidCodeMeasure.map (negativeHalfSdpIncrement 0)) s =
      SDPExpansion.integerCF (SDPMasterFromLaw.sdpF P Y) s := by
    rw [(negativeHalfSdpIncrement_ident hsym 0).map_eq]
    exact integer_law_cf P (SDPMasterFromLaw.increment Y 0) hD s
  have hp : (fun s : ℝ => charFun (iidCodeMeasure.map (negativeHalfSdpIncrement 0)) s -
      (1 - (negativeHalfSdpScale : ℂ) * (s ^ (4 / 3 : ℝ) : ℝ)))
      =o[𝓝[>] 0] (fun s : ℝ => s ^ (4 / 3 : ℝ)) := by
    rw [← isLittleO_norm_right] at hsmall
    apply hsmall.congr'
    · exact Eventually.of_forall fun s => by dsimp only; rw [hcf]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos
        (Real.rpow_pos_of_pos (show 0 < s from hs) _)]
  have hprob : IsProbabilityMeasure (iidCodeMeasure.map (negativeHalfSdpIncrement 0)) :=
    (Measure.isProbabilityMeasure_map_iff
      (negativeHalfSdpIncrement_measurable 0).aemeasurable).mpr inferInstance
  have hh := charFun_hexp_of_pos_expansion (by norm_num : (0 : ℝ) < 4 / 3) hp
  have hstar : star (negativeHalfSdpScale : ℂ) = (negativeHalfSdpScale : ℂ) := by simp
  simpa only [hstar, ite_self] using hh

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdp_fdd_of_sym
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {m : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (ht : Monotone t) :
    ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m), charFun (L : Measure _) θ =
        ∏ i : Fin m, Complex.exp (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
          ((negativeHalfSdpScale : ℂ) * (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
      Tendsto (fun n : ℕ =>
        (⟨iidCodeMeasure.map (skewStableProcessVector (k := m) (t := t) (ν := (4 / 3 : ℝ))
          negativeHalfSdpIncrement n), inferInstance⟩ :
            ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))) atTop
        (@nhds (ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
          ProbabilityMeasure.instTopologicalSpace (L.map (cumulativeSum (k := m)))) := by
  have hexp := negativeHalfSdpIncrement_charFun_expansion hsym
  have hexp' : (fun s : ℝ => charFun (iidCodeMeasure.map (negativeHalfSdpIncrement 0)) s -
      (1 - (if 0 ≤ s then (negativeHalfSdpScale : ℂ) else
        (negativeHalfSdpScale : ℂ)) * (|s| ^ (4 / 3 : ℝ) : ℝ)))
      =o[𝓝 0] (fun s : ℝ => |s| ^ (4 / 3 : ℝ)) := by
    simpa only [ite_self] using hexp
  simpa only [ite_self] using tendsto_skewStable_processVector_law
    negativeHalfSdpIncrement_iIndep (negativeHalfSdpIncrement_identDistrib hsym)
    negativeHalfSdpIncrement_measurable (by norm_num : (0 : ℝ) < 4 / 3)
    hexp' (by rw [ht0]) ht

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpIncrement_powerTail
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      iidCodeMeasure.real {ω | x < |negativeHalfSdpIncrement 0 ω|} ≤ C * x ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ :=
    sdp_increment_powerTail_of_ind_sym sdpIncrements_iIndep_proved hsym
  refine ⟨C, hC, ?_⟩
  intro x hx
  have he : iidCodeMeasure.real {ω | x < |negativeHalfSdpIncrement 0 ω|} =
      iidCodeMeasure.real {ω | x < |(SDPMasterFromLaw.increment Y 0 ω : ℝ)|} :=
    congrArg ENNReal.toReal
      ((negativeHalfSdpIncrement_ident hsym 0).measure_mem_eq
        (measurableSet_lt measurable_const continuous_abs.measurable))
  rw [he]
  exact htail x hx

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfSdpWindow (n : ℕ) {T : ℝ} (hT : 0 < T) :
    (ℕ → Fin 3) → J1WindowD T hT :=
  scaledPartialSumWindow negativeHalfSdpIncrement (4 / 3) n hT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfSdpWindowLaw (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ProbabilityMeasure (J1WindowD T hT) :=
  ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (negativeHalfSdpWindow n hT)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpWindow_isTight_of_sym
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    IsTightMeasureSet (Set.range fun n : ℕ => iidCodeMeasure.map (negativeHalfSdpWindow n hT)) := by
  obtain ⟨C, hC, htail⟩ := negativeHalfSdpIncrement_powerTail hsym
  have hm := busemann_sdp_increment_mean_zero_of_sym hsym (-1)
  have heq : negativeHalfSdpIncrement 0 =
      fun ω => -((Y ω (-1) - Y ω (-2) : ℤ) : ℝ) := by
    funext ω
    exact Int.cast_neg _
  have hint : Integrable (negativeHalfSdpIncrement 0) P := by
    rw [heq]
    exact hm.1.neg
  have hmean : ∫ ω, negativeHalfSdpIncrement 0 ω ∂P = 0 := by
    rw [heq, integral_neg]
    exact neg_eq_zero.mpr hm.2
  exact scaledPartialSumWindow_isTight_gt_one P negativeHalfSdpIncrement
    negativeHalfSdpIncrement_measurable negativeHalfSdpIncrement_iIndep
    (negativeHalfSdpIncrement_identDistrib hsym)
    (by norm_num : (1 : ℝ) < 4 / 3) (by norm_num) hC htail hint hmean hT



/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpWindow_measurable (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Measurable (negativeHalfSdpWindow n hT) :=
  measurable_scaledPartialSumWindow negativeHalfSdpIncrement
    negativeHalfSdpIncrement_measurable (4 / 3) n hT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpWindow_fdd_of_sym
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {T : ℝ} (hT : 0 < T) {m : ℕ} {t : ℕ → J1Window T}
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) :
    ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m), charFun (L : Measure _) θ =
        ∏ i : Fin m, Complex.exp
          (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((negativeHalfSdpScale : ℂ) * (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
      Tendsto (fun n => (negativeHalfSdpWindowLaw n hT).map
        (windowEvalVec (fun i : Fin m => t (i.val + 1)))) atTop
        (𝓝 ((L.map (cumulativeSum (k := m))).map WithLp.ofLp)) := by
  obtain ⟨L, hchar, hlim⟩ := negativeHalfSdp_fdd_of_sym hsym
    (m := m) (t := fun j => (t j : ℝ)) ht0 (fun _ _ hij => ht hij)
  refine ⟨L, hchar, ?_⟩
  have hn := (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
    (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ))).comp (tendsto_add_atTop_nat 1)
  have heval (n : ℕ) :
      (negativeHalfSdpWindowLaw n hT).map
        (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
      ProbabilityMeasure.map (⟨iidCodeMeasure.map (skewStableProcessVector (k := m)
          (t := fun j => (t j : ℝ)) (ν := (4 / 3 : ℝ))
          negativeHalfSdpIncrement (n + 1)), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin m))) WithLp.ofLp := by
    apply ProbabilityMeasure.toMeasure_injective
    change (iidCodeMeasure.map (negativeHalfSdpWindow n hT)).map
      (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
      (iidCodeMeasure.map _).map WithLp.ofLp
    rw [Measure.map_map (measurable_windowEvalVec _)
      (negativeHalfSdpWindow_measurable n hT)]
    rw [Measure.map_map (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).measurable
      (by
        apply (cumulativeSum (k := m)).continuous.measurable.comp
        apply (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp
        apply measurable_pi_iff.mpr
        intro i
        exact (Finset.measurable_fun_sum _ (fun j _ =>
          negativeHalfSdpIncrement_measurable j)).const_mul _)]
    congr 1
    funext ω i
    dsimp only [Function.comp_apply]
    rw [windowEvalVec, negativeHalfSdpWindow,
      scaledPartialSumWindow_apply,
      skewStableProcessVector_apply negativeHalfSdpIncrement (n + 1) ω i
        (fun _ _ hij => ht hij)]
    rw [ht0, mul_zero, Nat.floor_zero, Nat.Ico_zero_eq_range,
      ← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) (t _).property.1)]
    have hnat (k : ℕ) : partialSumZ negativeHalfSdpIncrement ω (k : ℤ) =
        ∑ j ∈ Finset.range k, negativeHalfSdpIncrement j ω := by
      cases k <;> simp [partialSumZ]
    rw [hnat]
    norm_num
  convert hn using 1
  · funext n
    exact heval n

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpWindow_eval_limit_exists
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {T : ℝ} (hT : 0 < T) (k : ℕ) (t : Fin k → J1Window T) :
    ∃ L : ProbabilityMeasure (Fin k → ℝ),
      Tendsto (fun n => (negativeHalfSdpWindowLaw n hT).map (windowEvalVec t)) atTop
        (𝓝 L) := by
  classical
  let z : J1Window T := ⟨0, le_rfl, hT.le⟩
  let s : Finset (J1Window T) := insert z (Finset.univ.image t)
  have hs : 0 < s.card := Finset.card_pos.mpr ⟨z, Finset.mem_insert_self _ _⟩
  let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
  let q : ℕ → J1Window T := fun j => if j = 0 then z else
    (e ⟨min (j - 1) (s.card - 1), by omega⟩).val
  have hq0 : (q 0 : ℝ) = 0 := by simp only [q, ↓reduceIte, z]
  have hqmono : Monotone q := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      change (q 0 : ℝ) ≤ (q j : ℝ)
      rw [hq0]
      exact (q j).property.1
    · have hj : j ≠ 0 := by omega
      simp only [q, hi, hj, ite_false]
      exact e.monotone (show (⟨min (i - 1) (s.card - 1), by omega⟩ : Fin s.card) ≤
        ⟨min (j - 1) (s.card - 1), by omega⟩ from by
          change min (i - 1) (s.card - 1) ≤ min (j - 1) (s.card - 1)
          omega)
  have hq (j : Fin s.card) : q (j.val + 1) = (e j).val := by
    have hj : j.val + 1 ≠ 0 := by omega
    simp only [q, hj, ite_false]
    congr 2
    apply Fin.ext
    have := j.isLt
    simp only [Nat.add_sub_cancel]
    omega
  let r : Fin k → Fin s.card := fun i => e.symm ⟨t i,
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
  have hr (i : Fin k) : q ((r i).val + 1) = t i := by
    rw [hq]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  obtain ⟨L, _, hL⟩ := negativeHalfSdpWindow_fdd_of_sym hsym hT (m := s.card) hq0 hqmono
  let p : (Fin s.card → ℝ) → Fin k → ℝ := fun v i => v (r i)
  have hp : Continuous p := continuous_pi fun i => continuous_apply (r i)
  refine ⟨((L.map cumulativeSum).map WithLp.ofLp).map p, ?_⟩
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hL hp
  have heq (n : ℕ) :
      ((negativeHalfSdpWindowLaw n hT).map
        (windowEvalVec (fun i : Fin s.card => q (i.val + 1)))).map p =
      (negativeHalfSdpWindowLaw n hT).map (windowEvalVec t) := by
    rw [pm_map_map _ (measurable_windowEvalVec _) hp.measurable]
    congr 1
    funext x i
    change x.path.1 (q ((r i).val + 1)) = x.path.1 (t i)
    rw [hr]
  simpa only [heq] using hh


/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpWindow_tendsto_exists_of_sym
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => negativeHalfSdpWindowLaw n hT) atTop (𝓝 ν) := by
  classical
  let W : ℕ → ProbabilityMeasure (J1WindowD T hT) := fun n => negativeHalfSdpWindowLaw n hT
  have htight := negativeHalfSdpWindow_isTight_of_sym hsym hT
  have htight' : IsTightMeasureSet
      {((p : ProbabilityMeasure (J1WindowD T hT)) : Measure (J1WindowD T hT)) |
        p ∈ Set.range W} := by
    convert htight using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨q, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨W n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨ν, _, φ, hφ, hν⟩ :=
    (isCompact_closure_of_isTightMeasureSet htight').tendsto_subseq
      (x := W) (fun n => subset_closure ⟨n, rfl⟩)
  let endpoint : J1Window T := ⟨T, hT.le, le_rfl⟩
  let S : Set (J1Window T) := insert endpoint (continuityTimes (ν : Measure (J1WindowD T hT)))
  have hS : Sᶜ.Countable :=
    (countable_compl_continuityTimes (ν : Measure (J1WindowD T hT))).mono
      (Set.compl_subset_compl.mpr (Set.subset_insert _ _))
  refine ⟨ν, tendsto_of_tight_of_fdd W ν htight S hS (Set.mem_insert _ _) ?_⟩
  intro k t
  obtain ⟨L, hL⟩ := negativeHalfSdpWindow_eval_limit_exists hsym hT k (fun i => (t i).val)
  have hcont (i : Fin k) (hi : ((t i).val : ℝ) < T) :
      (t i).val ∈ continuityTimes (ν : Measure (J1WindowD T hT)) := by
    rcases (t i).property with he | hc
    · have he' : ((t i).val : ℝ) = T := congrArg Subtype.val he
      exact False.elim ((ne_of_lt hi) he')
    · exact hc
  have heq : ν.map (windowEvalVec (fun i => (t i).val)) = L :=
    tendsto_nhds_unique (tendsto_map_windowEvalVec (W ∘ φ) ν hν _ hcont)
      (hL.comp hφ.tendsto_atTop)
  rw [heq]
  exact hL





/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpWindow_tendsto_of_sym
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => negativeHalfSdpWindowLaw n hT) atTop (𝓝 ν) ∧
      ∃ S : Set (J1Window T), Sᶜ.Countable ∧
        (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ S ∧
        ∀ (m : ℕ) (t : ℕ → J1Window T), (t 0 : ℝ) = 0 → Monotone t →
          (∀ i : Fin m, t (i.val + 1) ∈ S) →
          ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
            (∀ θ : EuclideanSpace ℝ (Fin m),
              charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
                (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
                  ((negativeHalfSdpScale : ℂ) *
                    (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
            ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
              (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  obtain ⟨ν, hν⟩ := negativeHalfSdpWindow_tendsto_exists_of_sym hsym hT
  let endpoint : J1Window T := ⟨T, hT.le, le_rfl⟩
  let S : Set (J1Window T) := insert endpoint (continuityTimes (ν : Measure (J1WindowD T hT)))
  have hS : Sᶜ.Countable :=
    (countable_compl_continuityTimes (ν : Measure (J1WindowD T hT))).mono
      (Set.compl_subset_compl.mpr (Set.subset_insert _ _))
  refine ⟨ν, hν, S, hS, Set.mem_insert _ _, ?_⟩
  intro m t ht0 ht htS
  obtain ⟨L, hchar, hL⟩ := negativeHalfSdpWindow_fdd_of_sym hsym hT ht0 ht
  refine ⟨L, hchar, ?_⟩
  apply tendsto_nhds_unique _ hL
  apply tendsto_map_windowEvalVec _ ν hν
  intro i hi
  rcases htS i with he | hc
  · have he' : (t (i.val + 1) : ℝ) = T := congrArg Subtype.val he
    exact False.elim ((ne_of_lt hi) he')
  · exact hc


/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpWindow_limit_continuousAt
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {T : ℝ} (hT : 0 < T) (t : J1Window T)
    (ht0 : 0 < (t : ℝ)) (htT : (t : ℝ) < T) :
    ∀ᵐ x ∂((Classical.choose (negativeHalfSdpWindow_tendsto_of_sym hsym hT) :
      ProbabilityMeasure (J1WindowD T hT)) : Measure (J1WindowD T hT)),
      ContinuousAt x.path.1 t := by
  obtain ⟨_, S, hS, _, hfdd⟩ :=
    Classical.choose_spec (negativeHalfSdpWindow_tendsto_of_sym hsym hT)
  apply fixed_time_continuous_of_stable_fdd hT _ S hS
    (negativeHalfSdpScale : ℂ) (4 / 3) _ (by norm_num) t ht0 htT
  intro q hq0 hq hq1 hq2
  obtain ⟨L, hchar, heval⟩ := hfdd 2 q hq0 hq (by
    intro i
    fin_cases i
    · exact hq1
    · exact hq2)
  refine ⟨L, ?_, heval⟩
  have hstar : star (negativeHalfSdpScale : ℂ) = (negativeHalfSdpScale : ℂ) := by simp
  simpa only [hstar, ite_self] using hchar

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpWindowLimit_projective
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {S T : ℝ} (hS : 0 < S) (hST : S < T) :
    (Classical.choose (negativeHalfSdpWindow_tendsto_of_sym hsym (hS.trans hST))).map
      (restrictJ1Window hS hST) =
      Classical.choose (negativeHalfSdpWindow_tendsto_of_sym hsym hS) := by
  have hbig := (Classical.choose_spec
    (negativeHalfSdpWindow_tendsto_of_sym hsym (hS.trans hST))).1
  have hsmall := (Classical.choose_spec
    (negativeHalfSdpWindow_tendsto_of_sym hsym hS)).1
  have hmap := tendsto_map_of_ae_continuousAt _ _ hbig
    (restrictJ1Window hS hST) (measurable_restrictJ1Window hS hST) (by
      filter_upwards [negativeHalfSdpWindow_limit_continuousAt hsym
        (hS.trans hST) ⟨S, hS.le, hST.le⟩ hS hST] with x hx
      exact continuousAt_restrictJ1Window_of_path_continuousAt hS hST x hx)
  apply tendsto_nhds_unique hmap
  have heq (n : ℕ) :
      (negativeHalfSdpWindowLaw n (hS.trans hST)).map (restrictJ1Window hS hST) =
        negativeHalfSdpWindowLaw n hS := by
    apply ProbabilityMeasure.toMeasure_injective
    change (iidCodeMeasure.map (negativeHalfSdpWindow n _)).map _ = _
    rw [Measure.map_map (measurable_restrictJ1Window hS hST)
      (negativeHalfSdpWindow_measurable n _)]
    congr 1
  simpa only [heq] using hsmall



/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdp_sum (r : ℕ) (ω : ℕ → Fin 3) :
    ∑ j ∈ Finset.range r, negativeHalfSdpIncrement j ω =
      ((Y ω (-((r : ℤ) + 1)) - Y ω (-1) : ℤ) : ℝ) := by
  induction r with
  | zero => simp [negativeHalfSdpIncrement]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have he : -((r : ℤ) + 1) - 1 = -(((r + 1 : ℕ) : ℤ) + 1) := by
      push_cast
      ring
    simp only [negativeHalfSdpIncrement, SDPMasterFromLaw.increment, he, Int.cast_neg, Int.cast_sub]
    ring

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfSdpPath (n : ℕ) (ω : ℕ → Fin 3) : CadlagLocal :=
  sdpScaledIntegerPositiveHalfPath n
    (fun j => Y ω (-((j : ℤ) + 1)) - Y ω (-1))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpPath_measurable (n : ℕ) :
    Measurable (negativeHalfSdpPath n) := by
  apply measurable_sdpScaledIntegerPositiveHalfPath
  intro j
  exact (measurable_busemannSDPMeasurableVersion _).sub
    (measurable_busemannSDPMeasurableVersion _)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpWindow_apply (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : ℕ → Fin 3) (t : J1Window T) :
    (negativeHalfSdpWindow n hT ω).path.1 t =
      (negativeHalfSdpPath n ω).1 (localWindowTime t) := by
  rw [negativeHalfSdpWindow, scaledPartialSumWindow_apply,
    ← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) t.property.1)]
  have hnat (k : ℕ) : partialSumZ negativeHalfSdpIncrement ω (k : ℤ) =
      ∑ j ∈ Finset.range k, negativeHalfSdpIncrement j ω := by
    cases k <;> simp [partialSumZ]
  rw [hnat, negativeHalfSdp_sum]
  change _ = ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    ((Y ω (-((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℤ) + 1)) - Y ω (-1) : ℤ) : ℝ)
  norm_num

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfSdpPathLaw (n : ℕ) :
    ProbabilityMeasure CadlagLocal :=
  ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (negativeHalfSdpPath n)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpPath_cutoff_factor (n N : ℕ) (ω : ℕ → Fin 3) :
    positiveHalfCutoffFactor N (negativeHalfSdpWindow n (by positivity) ω) =
      finiteCutoffWindows N (negativeHalfSdpPath n ω) := by
  funext i
  apply congrArg (fun p => J1WindowD.mk p)
  apply Subtype.ext
  funext t
  change (negativeHalfSdpWindow n (by positivity) ω).path.1 _ * _ =
    (negativeHalfSdpPath n ω).1 (localWindowTime t) * _
  rw [negativeHalfSdpWindow_apply]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpPathLaw_cutoff (n N : ℕ) :
    (negativeHalfSdpPathLaw n).map (finiteCutoffWindows N) =
      (negativeHalfSdpWindowLaw n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))).map
        (positiveHalfCutoffFactor N) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidCodeMeasure.map (negativeHalfSdpPath n)).map (finiteCutoffWindows N) =
    (iidCodeMeasure.map (negativeHalfSdpWindow n (by positivity))).map _
  rw [Measure.map_map (finiteCutoffWindows_measurable N)
    (negativeHalfSdpPath_measurable n),
    Measure.map_map (measurable_positiveHalfCutoffFactor N)
      (negativeHalfSdpWindow_measurable n _)]
  congr 1
  funext ω
  exact (negativeHalfSdpPath_cutoff_factor n N ω).symm

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfSdpCutoffLimit
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) (N : ℕ) :
    ProbabilityMeasure (LocalCutoffTuple N) :=
  (Classical.choose (negativeHalfSdpWindow_tendsto_of_sym hsym
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))).map (positiveHalfCutoffFactor N)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpPathLaw_finite_tendsto_of_sym
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) (N : ℕ) :
    Tendsto (fun n => (negativeHalfSdpPathLaw n).map (finiteCutoffWindows N)) atTop
      (𝓝 (negativeHalfSdpCutoffLimit hsym N)) := by
  let ν := Classical.choose (negativeHalfSdpWindow_tendsto_of_sym hsym
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))
  have hν := (Classical.choose_spec (negativeHalfSdpWindow_tendsto_of_sym hsym
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))).1
  have hcont : ∀ᵐ x ∂(ν : Measure (J1WindowD (((N + 2 : ℕ) : ℝ)) (by positivity))),
      ContinuousAt (positiveHalfCutoffFactor N) x := by
    have hc : ∀ i : Fin (N + 1), ∀ᵐ x
        ∂(ν : Measure (J1WindowD (((N + 2 : ℕ) : ℝ)) (by positivity))),
        ContinuousAt x.path.1
          (⟨(i.val : ℝ) + 1, by positivity, by
            have hi : (i.val : ℝ) ≤ N := by
              exact_mod_cast (Nat.le_of_lt_succ i.isLt)
            push_cast
            linarith⟩ : J1Window (((N + 2 : ℕ) : ℝ))) := by
      intro i
      apply negativeHalfSdpWindow_limit_continuousAt hsym (by positivity)
      · positivity
      · have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
        push_cast
        linarith
    filter_upwards [ae_all_iff.2 hc] with x hx
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_cutoffJ1Window i.val (by positivity)).continuousAt.comp
      (continuousAt_restrictJ1Window_of_path_continuousAt (by positivity) (by
        have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
        push_cast
        linarith) x (hx i))
  have h := tendsto_map_of_ae_continuousAt
    (fun n => negativeHalfSdpWindowLaw n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) ν hν
    (positiveHalfCutoffFactor N) (measurable_positiveHalfCutoffFactor N) hcont
  simpa only [negativeHalfSdpPathLaw_cutoff, negativeHalfSdpCutoffLimit, ν] using h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpPathLaw_tendsto_of_sym
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto negativeHalfSdpPathLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) = negativeHalfSdpCutoffLimit hsym N := by
  let W (m : ℕ) : ProbabilityMeasure
      (J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity)) :=
    Classical.choose (negativeHalfSdpWindow_tendsto_of_sym hsym (by positivity))
  obtain ⟨Pwin, hP⟩ := projectiveProbabilityOnInverseLimit
    (X := fun m => J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity))
    (fun m => restrictJ1Window (by positivity) (by norm_cast; omega))
    (fun m => measurable_restrictJ1Window (by positivity) (by norm_cast; omega)) W
    (fun m => congrArg ProbabilityMeasure.toMeasure
      (negativeHalfSdpWindowLimit_projective hsym (by positivity) (by norm_cast; omega)))
  let ν := Pwin.map positiveHalfWindowGlue
  have hcut (N : ℕ) : ν.map (finiteCutoffWindows N) = negativeHalfSdpCutoffLimit hsym N := by
    apply ProbabilityMeasure.toMeasure_injective
    change ((Pwin : Measure PositiveHalfWindowTrajectory).map positiveHalfWindowGlue).map
      (finiteCutoffWindows N) = _
    rw [Measure.map_map (finiteCutoffWindows_measurable N) measurable_positiveHalfWindowGlue]
    have heq : (finiteCutoffWindows N ∘ positiveHalfWindowGlue) =
        positiveHalfCutoffFactor N ∘
          (fun x : PositiveHalfWindowTrajectory => x.1 (N + 1)) :=
      funext (finiteCutoffWindows_positiveHalfWindowGlue N)
    rw [heq, ← Measure.map_map (measurable_positiveHalfCutoffFactor N)
      ((measurable_pi_apply (N + 1)).comp measurable_subtype_coe), hP (N + 1)]
    rfl
  refine ⟨ν, tendsto_of_tendsto_finiteCutoffWindows negativeHalfSdpPathLaw ν ?_, hcut⟩
  intro N
  rw [hcut N]
  exact negativeHalfSdpPathLaw_finite_tendsto_of_sym hsym N



/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdp_uniform_error (n : ℕ) (ω : ℕ → Fin 3)
    (t : Set.Ici (0 : ℝ)) :
    |(sdpBusemannWholeLineNegativeHalfPath n ω).1 t - (negativeHalfSdpPath n ω).1 t| ≤
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) * |(Y ω (-1) : ℝ)| := by
  let j := ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊
  change |((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
      (sdpBusemannNegativeSamples ω j : ℝ) -
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
      ((Y ω (-((j : ℤ) + 1)) - Y ω (-1) : ℤ) : ℝ)| ≤ _
  by_cases hj : j = 0
  · simp only [hj, sdpBusemannNegativeSamples, ↓reduceIte, Nat.cast_zero,
      zero_add, Int.cast_zero, sub_self, mul_zero, abs_zero]
    positivity
  · simp only [sdpBusemannNegativeSamples, hj, ↓reduceIte, Int.cast_sub]
    rw [show ∀ a b c : ℝ, a * b - a * (b - c) = a * c by intros; ring]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdp_localJ1_dist_le_uniform_error (x y : CadlagLocal) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ t, |x.1 t - y.1 t| ≤ C) : dist x y ≤ 2 * C := by
  have hw (m : ℕ) : j1WindowDist (by positivity) (cutoffWindow m x)
      (cutoffWindow m y) ≤ C := by
    let : Nonempty (J1Window ((m : ℝ) + 1)) := ⟨⟨0, le_rfl, by positivity⟩⟩
    apply (j1WindowDist_le_sup_dist (by positivity) _ _).trans
    apply ciSup_le
    intro t
    change |x.1 (localWindowTime t) * localCutoff m (localWindowTime t) -
      y.1 (localWindowTime t) * localCutoff m (localWindowTime t)| ≤ C
    rw [← sub_mul, abs_mul]
    exact (mul_le_mul (h _) (localCutoff_abs_le_one m _) (abs_nonneg _) hC).trans
      (by rw [mul_one])
  have hsum : Summable (fun m : ℕ => C * (1 / 2 : ℝ) ^ m) :=
    summable_geometric_two.mul_left C
  change j1LocalDist x y ≤ 2 * C
  calc
    _ ≤ ∑' m : ℕ, C * (1 / 2 : ℝ) ^ m := by
      apply (localJ1Term_summable x y).tsum_le_tsum _ hsum
      intro m
      rw [localJ1Term]
      calc
        _ ≤ (1 / 2 : ℝ) ^ (m + 1) * C :=
          mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (hw m)) (by positivity)
        _ ≤ C * (1 / 2 : ℝ) ^ m := by
          rw [pow_succ]
          have hp : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
          nlinarith
    _ = 2 * C := by rw [tsum_mul_left, tsum_geometric_two]; ring

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfSdpPath_shift_error_tendsto (ω : ℕ → Fin 3) :
    Tendsto (fun n => dist (sdpBusemannWholeLineNegativeHalfPath n ω)
      (negativeHalfSdpPath n ω)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => dist_nonneg) (fun n =>
    negativeHalfSdp_localJ1_dist_le_uniform_error _ _ (by positivity)
      (negativeHalfSdp_uniform_error n ω))
  simpa only [zero_mul, mul_zero] using
    (sdpBusemannJumpCoefficient_tendsto.mul_const |(Y ω (-1) : ℝ)|).const_mul 2

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpActualPath_measurable (n : ℕ) :
    Measurable (sdpBusemannWholeLineNegativeHalfPath n) :=
  measurable_subtype_coe.comp (sdpBusemannWholeLineNegativeHalf_measurable n)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfSdpActualLaw_tendsto_of_raw
    {ρ : ProbabilityMeasure CadlagLocal}
    (hraw : Tendsto negativeHalfSdpPathLaw atTop (𝓝 ρ)) :
    Tendsto (fun n => ProbabilityMeasure.map
      (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
      (sdpBusemannWholeLineNegativeHalfPath n)) atTop (𝓝 ρ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  let x₀ := sdpBusemannWholeLineNegativeHalfPath 0 (fun _ => 0)
  let B := C + |f x₀|
  have hB (x : CadlagLocal) : |f x| ≤ B := by
    have hh : |f x - f x₀| ≤ C := by simpa only [Real.dist_eq] using hC x x₀
    calc
      |f x| = |f x - f x₀ + f x₀| := by congr 1; ring
      _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
      _ ≤ B := add_le_add hh le_rfl
  have hX (n : ℕ) : Integrable
      (fun ω => f (sdpBusemannWholeLineNegativeHalfPath n ω)) iidCodeMeasure :=
    Integrable.of_bound
      ((hL.continuous.measurable.comp
        (negativeHalfSdpActualPath_measurable n)).aestronglyMeasurable)
      B (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hB _)
  have hY (n : ℕ) : Integrable
      (fun ω => f (negativeHalfSdpPath n ω)) iidCodeMeasure :=
    Integrable.of_bound
      ((hL.continuous.measurable.comp
        (negativeHalfSdpPath_measurable n)).aestronglyMeasurable)
      B (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hB _)
  have hdiff : Tendsto (fun n => ∫ ω,
      (f (sdpBusemannWholeLineNegativeHalfPath n ω) - f (negativeHalfSdpPath n ω))
        ∂iidCodeMeasure) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence
      (μ := iidCodeMeasure) (f := fun _ => (0 : ℝ)) (fun _ => 2 * B)
      (fun n => ((hX n).sub (hY n)).aestronglyMeasurable) (integrable_const _) ?_ ?_
    · simpa only [integral_zero, Pi.sub_apply] using hd
    · intro n
      exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        have hxB := hB (sdpBusemannWholeLineNegativeHalfPath n ω)
        have hyB := hB (negativeHalfSdpPath n ω)
        exact (abs_sub _ _).trans (by linarith only [hxB, hyB])
    · exact ae_of_all _ fun ω => by
        refine squeeze_zero_norm
          (a := fun n : ℕ => (L : ℝ) * dist (sdpBusemannWholeLineNegativeHalfPath n ω)
            (negativeHalfSdpPath n ω)) ?_ ?_
        · intro n
          change |f (sdpBusemannWholeLineNegativeHalfPath n ω) -
            f (negativeHalfSdpPath n ω)| ≤ _
          simpa only [Real.dist_eq] using
            hL.dist_le_mul (sdpBusemannWholeLineNegativeHalfPath n ω)
              (negativeHalfSdpPath n ω)
        · simpa only [mul_zero] using
            (negativeHalfSdpPath_shift_error_tendsto ω).const_mul (L : ℝ)
  have hmX (n : ℕ) :
      (∫ x, f x ∂(ProbabilityMeasure.map
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (sdpBusemannWholeLineNegativeHalfPath n) : Measure CadlagLocal)) =
        ∫ ω, f (sdpBusemannWholeLineNegativeHalfPath n ω) ∂iidCodeMeasure := by
    exact integral_map (negativeHalfSdpActualPath_measurable n).aemeasurable
      hL.continuous.stronglyMeasurable.aestronglyMeasurable
  have hmY (n : ℕ) :
      (∫ x, f x ∂(negativeHalfSdpPathLaw n : Measure CadlagLocal)) =
        ∫ ω, f (negativeHalfSdpPath n ω) ∂iidCodeMeasure := by
    exact integral_map (negativeHalfSdpPath_measurable n).aemeasurable
      hL.continuous.stronglyMeasurable.aestronglyMeasurable
  have hy := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hraw) f ⟨C, hC⟩ ⟨L, hL⟩
  simp_rw [hmY] at hy
  have hh := hdiff.add hy
  simp only [zero_add] at hh
  convert hh using 1
  funext n
  rw [hmX, integral_sub (hX n) (hY n), sub_add_cancel]


/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem sdpHalfLineOrigin_continuous :
    Continuous (fun x : CadlagLocal => x.1 ⟨0, le_rfl⟩) := by
  have he := continuous_j1WindowD_eval_zero
    (by positivity : (0 : ℝ) < ((0 : Fin 1).val : ℝ) + 1)
  have hw := (continuous_apply (0 : Fin 1)).comp (finiteCutoffWindows_continuous 0)
  have h := he.comp hw
  convert h using 1
  funext x
  simp [finiteCutoffWindows, toJ1WindowD, cutoffWindow, localWindowTime, localCutoff]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
converge under index-zero symmetry alone. The retained cutoff marginals come from
`negativeHalfSdpWindow_tendsto_of_sym`, whose block characteristic functions have
the positive real coefficient `negativeHalfSdpScale` and index `4 / 3`.
The limit is existential because the assembly predicate accepts a law as argument.
The source-identification gates of the measurable representative remain inherited. -/
theorem sdpBusemannWholeLineNegativeHalfConverges_of_sym
    (hsym_sdp : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    ∃ ν : ProbabilityMeasure CadlagLocalZero,
      SdpBusemannWholeLineNegativeHalfConverges ν ∧
      ∀ N, (ν.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) = negativeHalfSdpCutoffLimit hsym_sdp N := by
  obtain ⟨ρ, hraw, hcut⟩ := negativeHalfSdpPathLaw_tendsto_of_sym hsym_sdp
  have hρ := negativeHalfSdpActualLaw_tendsto_of_raw hraw
  let S : Set CadlagLocal := {x | x.1 ⟨0, le_rfl⟩ = 0}
  have hS : IsClosed S := isClosed_eq sdpHalfLineOrigin_continuous continuous_const
  have hn (n : ℕ) :
      (iidCodeMeasure.map (sdpBusemannWholeLineNegativeHalfPath n)) S = 1 := by
    rw [Measure.map_apply (negativeHalfSdpActualPath_measurable n) hS.measurableSet]
    have heq : sdpBusemannWholeLineNegativeHalfPath n ⁻¹' S = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact sdpBusemannWholeLineNegativeHalfPath_zero n ω
    rw [heq, measure_univ]
  have hρS : (ρ : Measure CadlagLocal) S = 1 := by
    apply le_antisymm (by simpa only [measure_univ] using
      (measure_mono (Set.subset_univ S) : (ρ : Measure CadlagLocal) S ≤
        (ρ : Measure CadlagLocal) Set.univ))
    have hb := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hρ hS
    change (atTop.limsup fun n =>
      (iidCodeMeasure.map (sdpBusemannWholeLineNegativeHalfPath n)) S) ≤
        (ρ : Measure CadlagLocal) S at hb
    simpa only [hn, limsup_const] using hb
  have hae : ∀ᵐ x ∂(ρ : Measure CadlagLocal), x ∈ S :=
    (mem_ae_iff_prob_eq_one hS.measurableSet).mpr hρS
  have he : MeasurableEmbedding (Subtype.val : CadlagLocalZero → CadlagLocal) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hp : IsProbabilityMeasure
      ((ρ : Measure CadlagLocal).comap (Subtype.val : CadlagLocalZero → CadlagLocal)) :=
    he.isProbabilityMeasure_comap (by
      change ∀ᵐ x ∂(ρ : Measure CadlagLocal), x ∈ Set.range
        (Subtype.val : S → CadlagLocal)
      simpa only [Subtype.range_coe] using hae)
  let ν : ProbabilityMeasure CadlagLocalZero :=
    ⟨(ρ : Measure CadlagLocal).comap Subtype.val, hp⟩
  have hmap : (ν : Measure CadlagLocalZero).map Subtype.val =
      (ρ : Measure CadlagLocal) := by
    exact (map_comap_subtype_coe hS.measurableSet _).trans
      (Measure.restrict_eq_self_of_ae_mem hae)
  refine ⟨ν, ⟨sdpBusemannWholeLineNegativeHalf_measurable, ?_⟩, ?_⟩
  · apply tendsto_of_forall_isClosed_limsup_le'
    intro F hF
    have hFi : IsClosed ((Subtype.val : CadlagLocalZero → CadlagLocal) '' F) :=
      (Topology.IsClosedEmbedding.subtypeVal hS).isClosedMap F hF
    have hνF : (ν : Measure CadlagLocalZero) F =
        (ρ : Measure CadlagLocal) (Subtype.val '' F) := by
      rw [← hmap, Measure.map_apply measurable_subtype_coe hFi.measurableSet,
        Set.preimage_image_eq F Subtype.coe_injective]
    have hnF (n : ℕ) :
        (ProbabilityMeasure.map
          (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
          (sdpBusemannWholeLineNegativeHalf n) : Measure _) F =
        (ProbabilityMeasure.map
          (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
          (sdpBusemannWholeLineNegativeHalfPath n) : Measure _)
          (Subtype.val '' F) := by
      change (iidCodeMeasure.map (sdpBusemannWholeLineNegativeHalf n)) F =
        (iidCodeMeasure.map (sdpBusemannWholeLineNegativeHalfPath n)) (Subtype.val '' F)
      rw [Measure.map_apply (sdpBusemannWholeLineNegativeHalf_measurable n)
        hF.measurableSet, Measure.map_apply (negativeHalfSdpActualPath_measurable n)
        hFi.measurableSet]
      congr 1
      ext ω
      constructor
      · intro hω
        exact ⟨sdpBusemannWholeLineNegativeHalf n ω, hω, rfl⟩
      · rintro ⟨x, hx, heqx⟩
        have hx' : x = sdpBusemannWholeLineNegativeHalf n ω := Subtype.ext heqx
        change sdpBusemannWholeLineNegativeHalf n ω ∈ F
        rw [← hx']
        exact hx
    simp_rw [hnF, hνF]
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hρ hFi
  · have heq : ν.map (Subtype.val : CadlagLocalZero → CadlagLocal) = ρ :=
      ProbabilityMeasure.toMeasure_injective hmap
    simpa only [heq] using hcut

end DirectedDistances.Recursive
