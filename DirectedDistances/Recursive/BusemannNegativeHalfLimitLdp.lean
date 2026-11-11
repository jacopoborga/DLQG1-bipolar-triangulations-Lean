module

public import DirectedDistances.Recursive.BusemannWholeLineLimitLdp
import all DirectedDistances.Recursive.BusemannWholeLineLimitLdp
public import DirectedDistances.Recursive.BusemannItemsSymOnly
public import DirectedDistances.Probability.SkewedStableProcessFdd
public import DirectedDistances.Probability.ScaledWindowModulusGtOne
import all DirectedDistances.Recursive.BusemannPositiveHalfLaw
import all DirectedDistances.Recursive.BusemannWholeLineJumpConv
import all DirectedDistances.Recursive.BusemannFddStable
import all DirectedDistances.Recursive.BusemannWindowLimit
import all DirectedDistances.Recursive.BusemannWindowLimitNoFixedJumps
import all DirectedDistances.Recursive.BusemannWholeLineLawConditional
import DirectedDistances.Recursive.LDPQuadraticFromMaster
import DirectedDistances.Probability.SkewedStableHexpOfPos

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology ENNReal

local notation "P" => iidCodeMeasure
local notation "Y" => busemannLDPMeasurableVersion

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfLdpIncrement (j : ℕ) (ω : ℕ → Fin 3) : ℝ :=
  (-ldpIncrement Y (-((j : ℤ) + 1)) ω : ℤ)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpIncrement_measurable (j : ℕ) :
    Measurable (negativeHalfLdpIncrement j) := by
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    (((measurable_busemannLDPMeasurableVersion _).sub
      (measurable_busemannLDPMeasurableVersion _)).neg)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpIncrement_iIndep : iIndepFun negativeHalfLdpIncrement P := by
  have h := (ldpBusemannReflectedIncrements_iIndep.precomp
    (show Function.Injective (fun j : ℕ => j + 1) from by
      intro a b h
      dsimp at h
      omega)).comp
      (fun _ => fun z : ℤ => (z : ℝ)) (fun _ => measurable_of_countable _)
  change iIndepFun (fun (j : ℕ) ω =>
    ((-ldpIncrement Y (-((j : ℤ) + 1)) ω : ℤ) : ℝ)) P
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpIncrement_ident
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    (j : ℕ) :
    IdentDistrib (negativeHalfLdpIncrement j) (fun ω => (ldpIncrement Y 0 ω : ℝ)) P P := by
  have hD (k : ℤ) : Measurable (ldpIncrement Y k) :=
    (measurable_busemannLDPMeasurableVersion _).sub
      (measurable_busemannLDPMeasurableVersion _)
  have h : IdentDistrib
      (fun ω => -ldpIncrement Y (-((j : ℤ) + 1)) ω) (ldpIncrement Y 0) P P :=
    ⟨(hD _).neg.aemeasurable, (hD _).aemeasurable, by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ldpBusemannReflectedIncrement_law hsym (j + 1)⟩
  exact h.comp (measurable_of_countable (fun z : ℤ => (z : ℝ)))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpIncrement_identDistrib
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    (j : ℕ) : IdentDistrib (negativeHalfLdpIncrement j) (negativeHalfLdpIncrement 0) P P :=
  (negativeHalfLdpIncrement_ident hsym j).trans
    (negativeHalfLdpIncrement_ident hsym 0).symm

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfLdpScale : ℝ :=
  ((3 + ldpF P Y 0) / 2) ^ (1 / 3 : ℝ)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpScale_pos : 0 < negativeHalfLdpScale := by
  apply Real.rpow_pos_of_pos
  exact div_pos (add_pos_of_pos_of_nonneg (by norm_num) (busemann_ldpF_nonneg 0))
    (by norm_num)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpIncrement_charFun_expansion
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    (fun s : ℝ => charFun (iidCodeMeasure.map (negativeHalfLdpIncrement 0)) s -
      (1 - (negativeHalfLdpScale : ℂ) * (|s| ^ (2 / 3 : ℝ) : ℝ)))
      =o[𝓝 0] (fun s : ℝ => |s| ^ (2 / 3 : ℝ)) := by
  have hrec := ldp_master_equation_of_sym hsym
  have hsmall := (ldp_real_transform_expansion_of_master
    busemann_ldpF_nonneg busemann_ldpF_hasSum_one
    busemann_ldpG_nonneg busemann_ldpG_hasSum_one
    (busemann_ldpF_symm hsym) busemann_ldpG_zero_of_nonneg hrec).2
  have hD : Measurable (ldpIncrement Y 0) :=
    (measurable_busemannLDPMeasurableVersion _).sub
      (measurable_busemannLDPMeasurableVersion _)
  have hcf (s : ℝ) : charFun (iidCodeMeasure.map (negativeHalfLdpIncrement 0)) s =
      integerCF (ldpF P Y) s := by
    rw [(negativeHalfLdpIncrement_ident hsym 0).map_eq]
    exact integer_law_cf P (ldpIncrement Y 0) hD s
  have hp : (fun s : ℝ => charFun (iidCodeMeasure.map (negativeHalfLdpIncrement 0)) s -
      (1 - (negativeHalfLdpScale : ℂ) * (s ^ (2 / 3 : ℝ) : ℝ)))
      =o[𝓝[>] 0] (fun s : ℝ => s ^ (2 / 3 : ℝ)) := by
    rw [← isLittleO_norm_right] at hsmall
    apply hsmall.congr'
    · exact Eventually.of_forall fun s => by dsimp only; rw [hcf]; rfl
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos
        (Real.rpow_pos_of_pos (show 0 < s from hs) _)]
  have hprob : IsProbabilityMeasure (iidCodeMeasure.map (negativeHalfLdpIncrement 0)) :=
    (Measure.isProbabilityMeasure_map_iff
      (negativeHalfLdpIncrement_measurable 0).aemeasurable).mpr inferInstance
  have hh := charFun_hexp_of_pos_expansion (by norm_num : (0 : ℝ) < 2 / 3) hp
  have hstar : star (negativeHalfLdpScale : ℂ) = (negativeHalfLdpScale : ℂ) := by simp
  simpa only [hstar, ite_self] using hh

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdp_fdd_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {m : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (ht : Monotone t) :
    ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m), charFun (L : Measure _) θ =
        ∏ i : Fin m, Complex.exp (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
          ((negativeHalfLdpScale : ℂ) * (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
      Tendsto (fun n : ℕ =>
        (⟨iidCodeMeasure.map (skewStableProcessVector (k := m) (t := t) (ν := (2 / 3 : ℝ))
          negativeHalfLdpIncrement n), inferInstance⟩ :
            ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))) atTop
        (@nhds (ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
          ProbabilityMeasure.instTopologicalSpace (L.map (cumulativeSum (k := m)))) := by
  have hexp := negativeHalfLdpIncrement_charFun_expansion hsym
  have hexp' : (fun s : ℝ => charFun (iidCodeMeasure.map (negativeHalfLdpIncrement 0)) s -
      (1 - (if 0 ≤ s then (negativeHalfLdpScale : ℂ) else
        (negativeHalfLdpScale : ℂ)) * (|s| ^ (2 / 3 : ℝ) : ℝ)))
      =o[𝓝 0] (fun s : ℝ => |s| ^ (2 / 3 : ℝ)) := by
    simpa only [ite_self] using hexp
  simpa only [ite_self] using tendsto_skewStable_processVector_law
    negativeHalfLdpIncrement_iIndep (negativeHalfLdpIncrement_identDistrib hsym)
    negativeHalfLdpIncrement_measurable (by norm_num : (0 : ℝ) < 2 / 3)
    hexp' (by rw [ht0]) ht

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpIncrement_powerTail
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      iidCodeMeasure.real {ω | x < |negativeHalfLdpIncrement 0 ω|} ≤ C * x ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨_, _, habs⟩ := busemann_tail_ldp_strict_of_items ldpIncrements_iIndep_proved
    busemannLDPMeasurableVersion_right_stationary
    busemannLDPMeasurableVersion_left_stationary hsym
  have ht := normalized_remainder habs
  have he (x : ℝ) : iidCodeMeasure.real {ω | x < |negativeHalfLdpIncrement 0 ω|} =
      iidCodeMeasure.real {ω | x < |(ldpIncrement Y 0 ω : ℝ)|} :=
    congrArg ENNReal.toReal
      ((negativeHalfLdpIncrement_ident hsym 0).measure_mem_eq
        (measurableSet_lt measurable_const continuous_abs.measurable))
  simp only [ldpIncrement] at he
  have hb := ht.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨R, hR⟩ := eventually_atTop.mp hb
  let T : ℝ := max 1 R
  let K : ℝ := max 1 (2 *
    ((Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) *
      ((3 + ldpF P Y 0) / 2) ^ (1 / 3 : ℝ)) + 1)
  refine ⟨T ^ (2 / 3 : ℝ) + K, by dsimp [T, K]; positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxp : 0 < x ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [he]
  by_cases hTx : T ≤ x
  · have hb' := (hR x ((le_max_right 1 R).trans hTx)).le
    have hb'' : iidCodeMeasure.real {ω | x < |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} ≤
        K * x ^ (-(2 / 3 : ℝ)) := by
      rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, le_div_iff₀ hxp]
      apply le_trans _ (le_max_right _ _)
      simpa only [mul_comm] using hb'
    simpa only [zero_sub] using hb''.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left
        (Real.rpow_nonneg (by dsimp [T]; positivity) _))
          (Real.rpow_nonneg hx0.le _))
  · have hxT : x ≤ T := (not_le.mp hTx).le
    have hp : x ^ (2 / 3 : ℝ) ≤ T ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow hx0.le hxT (by norm_num)
    have hK : 0 ≤ K := (zero_le_one.trans (le_max_left _ _))
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ (T ^ (2 / 3 : ℝ) + K) * x ^ (-(2 / 3 : ℝ)) := by
        rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, le_div_iff₀ hxp, one_mul]
        exact hp.trans (le_add_of_nonneg_right hK)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfLdpWindow (n : ℕ) {T : ℝ} (hT : 0 < T) :
    (ℕ → Fin 3) → J1WindowD T hT :=
  scaledPartialSumWindow negativeHalfLdpIncrement (2 / 3) n hT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfLdpWindowLaw (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ProbabilityMeasure (J1WindowD T hT) :=
  ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (negativeHalfLdpWindow n hT)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpWindow_isTight_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    IsTightMeasureSet (Set.range fun n : ℕ => iidCodeMeasure.map (negativeHalfLdpWindow n hT)) := by
  obtain ⟨C, hC, htail⟩ := negativeHalfLdpIncrement_powerTail hsym
  exact scaledPartialSumWindow_isTight_lt_one' P negativeHalfLdpIncrement
    negativeHalfLdpIncrement_measurable negativeHalfLdpIncrement_iIndep
    (negativeHalfLdpIncrement_identDistrib hsym)
    (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num) hC htail hT



/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpWindow_measurable (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Measurable (negativeHalfLdpWindow n hT) :=
  measurable_scaledPartialSumWindow negativeHalfLdpIncrement
    negativeHalfLdpIncrement_measurable (2 / 3) n hT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpWindow_fdd_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) {m : ℕ} {t : ℕ → J1Window T}
    (ht0 : (t 0 : ℝ) = 0) (ht : Monotone t) :
    ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
      (∀ θ : EuclideanSpace ℝ (Fin m), charFun (L : Measure _) θ =
        ∏ i : Fin m, Complex.exp
          (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((negativeHalfLdpScale : ℂ) * (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
      Tendsto (fun n => (negativeHalfLdpWindowLaw n hT).map
        (windowEvalVec (fun i : Fin m => t (i.val + 1)))) atTop
        (𝓝 ((L.map (cumulativeSum (k := m))).map WithLp.ofLp)) := by
  obtain ⟨L, hchar, hlim⟩ := negativeHalfLdp_fdd_of_sym hsym
    (m := m) (t := fun j => (t j : ℝ)) ht0 (fun _ _ hij => ht hij)
  refine ⟨L, hchar, ?_⟩
  have hn := (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
    (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ))).comp (tendsto_add_atTop_nat 1)
  have heval (n : ℕ) :
      (negativeHalfLdpWindowLaw n hT).map
        (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
      ProbabilityMeasure.map (⟨iidCodeMeasure.map (skewStableProcessVector (k := m)
          (t := fun j => (t j : ℝ)) (ν := (2 / 3 : ℝ))
          negativeHalfLdpIncrement (n + 1)), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin m))) WithLp.ofLp := by
    apply ProbabilityMeasure.toMeasure_injective
    change (iidCodeMeasure.map (negativeHalfLdpWindow n hT)).map
      (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
      (iidCodeMeasure.map _).map WithLp.ofLp
    rw [Measure.map_map (measurable_windowEvalVec _)
      (negativeHalfLdpWindow_measurable n hT)]
    rw [Measure.map_map (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).measurable
      (by
        apply (cumulativeSum (k := m)).continuous.measurable.comp
        apply (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp
        apply measurable_pi_iff.mpr
        intro i
        exact (Finset.measurable_fun_sum _ (fun j _ =>
          negativeHalfLdpIncrement_measurable j)).const_mul _)]
    congr 1
    funext ω i
    dsimp only [Function.comp_apply]
    rw [windowEvalVec, negativeHalfLdpWindow,
      scaledPartialSumWindow_apply,
      skewStableProcessVector_apply negativeHalfLdpIncrement (n + 1) ω i
        (fun _ _ hij => ht hij)]
    rw [ht0, mul_zero, Nat.floor_zero, Nat.Ico_zero_eq_range,
      ← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) (t _).property.1)]
    have hnat (k : ℕ) : partialSumZ negativeHalfLdpIncrement ω (k : ℤ) =
        ∑ j ∈ Finset.range k, negativeHalfLdpIncrement j ω := by
      cases k <;> simp [partialSumZ]
    rw [hnat]
    norm_num
  convert hn using 1
  · funext n
    exact heval n

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpWindow_eval_limit_exists
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) (k : ℕ) (t : Fin k → J1Window T) :
    ∃ L : ProbabilityMeasure (Fin k → ℝ),
      Tendsto (fun n => (negativeHalfLdpWindowLaw n hT).map (windowEvalVec t)) atTop
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
  obtain ⟨L, _, hL⟩ := negativeHalfLdpWindow_fdd_of_sym hsym hT (m := s.card) hq0 hqmono
  let p : (Fin s.card → ℝ) → Fin k → ℝ := fun v i => v (r i)
  have hp : Continuous p := continuous_pi fun i => continuous_apply (r i)
  refine ⟨((L.map cumulativeSum).map WithLp.ofLp).map p, ?_⟩
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hL hp
  have heq (n : ℕ) :
      ((negativeHalfLdpWindowLaw n hT).map
        (windowEvalVec (fun i : Fin s.card => q (i.val + 1)))).map p =
      (negativeHalfLdpWindowLaw n hT).map (windowEvalVec t) := by
    rw [pm_map_map _ (measurable_windowEvalVec _) hp.measurable]
    congr 1
    funext x i
    change x.path.1 (q ((r i).val + 1)) = x.path.1 (t i)
    rw [hr]
  simpa only [heq] using hh


/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpWindow_tendsto_exists_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => negativeHalfLdpWindowLaw n hT) atTop (𝓝 ν) := by
  classical
  let W : ℕ → ProbabilityMeasure (J1WindowD T hT) := fun n => negativeHalfLdpWindowLaw n hT
  have htight := negativeHalfLdpWindow_isTight_of_sym hsym hT
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
  obtain ⟨L, hL⟩ := negativeHalfLdpWindow_eval_limit_exists hsym hT k (fun i => (t i).val)
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
theorem negativeHalfLdpWindow_tendsto_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => negativeHalfLdpWindowLaw n hT) atTop (𝓝 ν) ∧
      ∃ S : Set (J1Window T), Sᶜ.Countable ∧
        (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ S ∧
        ∀ (m : ℕ) (t : ℕ → J1Window T), (t 0 : ℝ) = 0 → Monotone t →
          (∀ i : Fin m, t (i.val + 1) ∈ S) →
          ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
            (∀ θ : EuclideanSpace ℝ (Fin m),
              charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
                (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
                  ((negativeHalfLdpScale : ℂ) *
                    (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
            ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
              (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  obtain ⟨ν, hν⟩ := negativeHalfLdpWindow_tendsto_exists_of_sym hsym hT
  let endpoint : J1Window T := ⟨T, hT.le, le_rfl⟩
  let S : Set (J1Window T) := insert endpoint (continuityTimes (ν : Measure (J1WindowD T hT)))
  have hS : Sᶜ.Countable :=
    (countable_compl_continuityTimes (ν : Measure (J1WindowD T hT))).mono
      (Set.compl_subset_compl.mpr (Set.subset_insert _ _))
  refine ⟨ν, hν, S, hS, Set.mem_insert _ _, ?_⟩
  intro m t ht0 ht htS
  obtain ⟨L, hchar, hL⟩ := negativeHalfLdpWindow_fdd_of_sym hsym hT ht0 ht
  refine ⟨L, hchar, ?_⟩
  apply tendsto_nhds_unique _ hL
  apply tendsto_map_windowEvalVec _ ν hν
  intro i hi
  rcases htS i with he | hc
  · have he' : (t (i.val + 1) : ℝ) = T := congrArg Subtype.val he
    exact False.elim ((ne_of_lt hi) he')
  · exact hc


/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpWindow_limit_continuousAt
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {T : ℝ} (hT : 0 < T) (t : J1Window T)
    (ht0 : 0 < (t : ℝ)) (htT : (t : ℝ) < T) :
    ∀ᵐ x ∂((Classical.choose (negativeHalfLdpWindow_tendsto_of_sym hsym hT) :
      ProbabilityMeasure (J1WindowD T hT)) : Measure (J1WindowD T hT)),
      ContinuousAt x.path.1 t := by
  obtain ⟨_, S, hS, _, hfdd⟩ :=
    Classical.choose_spec (negativeHalfLdpWindow_tendsto_of_sym hsym hT)
  apply fixed_time_continuous_of_stable_fdd hT _ S hS
    (negativeHalfLdpScale : ℂ) (2 / 3) _ (by norm_num) t ht0 htT
  intro q hq0 hq hq1 hq2
  obtain ⟨L, hchar, heval⟩ := hfdd 2 q hq0 hq (by
    intro i
    fin_cases i
    · exact hq1
    · exact hq2)
  refine ⟨L, ?_, heval⟩
  have hstar : star (negativeHalfLdpScale : ℂ) = (negativeHalfLdpScale : ℂ) := by simp
  simpa only [hstar, ite_self] using hchar

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpWindowLimit_projective
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))
    {S T : ℝ} (hS : 0 < S) (hST : S < T) :
    (Classical.choose (negativeHalfLdpWindow_tendsto_of_sym hsym (hS.trans hST))).map
      (restrictJ1Window hS hST) =
      Classical.choose (negativeHalfLdpWindow_tendsto_of_sym hsym hS) := by
  have hbig := (Classical.choose_spec
    (negativeHalfLdpWindow_tendsto_of_sym hsym (hS.trans hST))).1
  have hsmall := (Classical.choose_spec
    (negativeHalfLdpWindow_tendsto_of_sym hsym hS)).1
  have hmap := tendsto_map_of_ae_continuousAt _ _ hbig
    (restrictJ1Window hS hST) (measurable_restrictJ1Window hS hST) (by
      filter_upwards [negativeHalfLdpWindow_limit_continuousAt hsym
        (hS.trans hST) ⟨S, hS.le, hST.le⟩ hS hST] with x hx
      exact continuousAt_restrictJ1Window_of_path_continuousAt hS hST x hx)
  apply tendsto_nhds_unique hmap
  have heq (n : ℕ) :
      (negativeHalfLdpWindowLaw n (hS.trans hST)).map (restrictJ1Window hS hST) =
        negativeHalfLdpWindowLaw n hS := by
    apply ProbabilityMeasure.toMeasure_injective
    change (iidCodeMeasure.map (negativeHalfLdpWindow n _)).map _ = _
    rw [Measure.map_map (measurable_restrictJ1Window hS hST)
      (negativeHalfLdpWindow_measurable n _)]
    congr 1
  simpa only [heq] using hsmall



/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdp_sum (r : ℕ) (ω : ℕ → Fin 3) :
    ∑ j ∈ Finset.range r, negativeHalfLdpIncrement j ω =
      ((Y ω (-((r : ℤ) + 1)) - Y ω (-1) : ℤ) : ℝ) := by
  induction r with
  | zero => simp [negativeHalfLdpIncrement]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have he : -((r : ℤ) + 1) - 1 = -(((r + 1 : ℕ) : ℤ) + 1) := by
      push_cast
      ring
    simp only [negativeHalfLdpIncrement, ldpIncrement, he, Int.cast_neg, Int.cast_sub]
    ring

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfLdpPath (n : ℕ) (ω : ℕ → Fin 3) : CadlagLocal :=
  scaledIntegerPositiveHalfPath n
    (fun j => Y ω (-((j : ℤ) + 1)) - Y ω (-1))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpPath_measurable (n : ℕ) :
    Measurable (negativeHalfLdpPath n) := by
  apply measurable_scaledIntegerPositiveHalfPath
  intro j
  exact (measurable_busemannLDPMeasurableVersion _).sub
    (measurable_busemannLDPMeasurableVersion _)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpWindow_apply (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : ℕ → Fin 3) (t : J1Window T) :
    (negativeHalfLdpWindow n hT ω).path.1 t =
      (negativeHalfLdpPath n ω).1 (localWindowTime t) := by
  rw [negativeHalfLdpWindow, scaledPartialSumWindow_apply,
    ← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) t.property.1)]
  have hnat (k : ℕ) : partialSumZ negativeHalfLdpIncrement ω (k : ℤ) =
      ∑ j ∈ Finset.range k, negativeHalfLdpIncrement j ω := by
    cases k <;> simp [partialSumZ]
  rw [hnat, negativeHalfLdp_sum]
  change _ = ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
    ((Y ω (-((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℤ) + 1)) - Y ω (-1) : ℤ) : ℝ)
  norm_num

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfLdpPathLaw (n : ℕ) :
    ProbabilityMeasure CadlagLocal :=
  ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
    (negativeHalfLdpPath n)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpPath_cutoff_factor (n N : ℕ) (ω : ℕ → Fin 3) :
    positiveHalfCutoffFactor N (negativeHalfLdpWindow n (by positivity) ω) =
      finiteCutoffWindows N (negativeHalfLdpPath n ω) := by
  funext i
  apply congrArg (fun p => J1WindowD.mk p)
  apply Subtype.ext
  funext t
  change (negativeHalfLdpWindow n (by positivity) ω).path.1 _ * _ =
    (negativeHalfLdpPath n ω).1 (localWindowTime t) * _
  rw [negativeHalfLdpWindow_apply]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpPathLaw_cutoff (n N : ℕ) :
    (negativeHalfLdpPathLaw n).map (finiteCutoffWindows N) =
      (negativeHalfLdpWindowLaw n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))).map
        (positiveHalfCutoffFactor N) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidCodeMeasure.map (negativeHalfLdpPath n)).map (finiteCutoffWindows N) =
    (iidCodeMeasure.map (negativeHalfLdpWindow n (by positivity))).map _
  rw [Measure.map_map (finiteCutoffWindows_measurable N)
    (negativeHalfLdpPath_measurable n),
    Measure.map_map (measurable_positiveHalfCutoffFactor N)
      (negativeHalfLdpWindow_measurable n _)]
  congr 1
  funext ω
  exact (negativeHalfLdpPath_cutoff_factor n N ω).symm

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
@[expose] noncomputable def negativeHalfLdpCutoffLimit
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) (N : ℕ) :
    ProbabilityMeasure (LocalCutoffTuple N) :=
  (Classical.choose (negativeHalfLdpWindow_tendsto_of_sym hsym
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))).map (positiveHalfCutoffFactor N)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpPathLaw_finite_tendsto_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) (N : ℕ) :
    Tendsto (fun n => (negativeHalfLdpPathLaw n).map (finiteCutoffWindows N)) atTop
      (𝓝 (negativeHalfLdpCutoffLimit hsym N)) := by
  let ν := Classical.choose (negativeHalfLdpWindow_tendsto_of_sym hsym
    (by positivity : 0 < ((N + 2 : ℕ) : ℝ)))
  have hν := (Classical.choose_spec (negativeHalfLdpWindow_tendsto_of_sym hsym
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
      apply negativeHalfLdpWindow_limit_continuousAt hsym (by positivity)
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
    (fun n => negativeHalfLdpWindowLaw n (by positivity : 0 < ((N + 2 : ℕ) : ℝ))) ν hν
    (positiveHalfCutoffFactor N) (measurable_positiveHalfCutoffFactor N) hcont
  simpa only [negativeHalfLdpPathLaw_cutoff, negativeHalfLdpCutoffLimit, ν] using h

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem negativeHalfLdpPathLaw_tendsto_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto negativeHalfLdpPathLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) = negativeHalfLdpCutoffLimit hsym N := by
  let W (m : ℕ) : ProbabilityMeasure
      (J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity)) :=
    Classical.choose (negativeHalfLdpWindow_tendsto_of_sym hsym (by positivity))
  obtain ⟨Pwin, hP⟩ := projectiveProbabilityOnInverseLimit
    (X := fun m => J1WindowD ((m + 1 : ℕ) : ℝ) (by positivity))
    (fun m => restrictJ1Window (by positivity) (by norm_cast; omega))
    (fun m => measurable_restrictJ1Window (by positivity) (by norm_cast; omega)) W
    (fun m => congrArg ProbabilityMeasure.toMeasure
      (negativeHalfLdpWindowLimit_projective hsym (by positivity) (by norm_cast; omega)))
  let ν := Pwin.map positiveHalfWindowGlue
  have hcut (N : ℕ) : ν.map (finiteCutoffWindows N) = negativeHalfLdpCutoffLimit hsym N := by
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
  refine ⟨ν, tendsto_of_tendsto_finiteCutoffWindows negativeHalfLdpPathLaw ν ?_, hcut⟩
  intro N
  rw [hcut N]
  exact negativeHalfLdpPathLaw_finite_tendsto_of_sym hsym N



/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdp_uniform_error (n : ℕ) (ω : ℕ → Fin 3)
    (t : Set.Ici (0 : ℝ)) :
    |(ldpBusemannWholeLineNegativeHalfPath n ω).1 t - (negativeHalfLdpPath n ω).1 t| ≤
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) * |(Y ω (-1) : ℝ)| := by
  let j := ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊
  change |((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (ldpBusemannNegativeSamples ω j : ℝ) -
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      ((Y ω (-((j : ℤ) + 1)) - Y ω (-1) : ℤ) : ℝ)| ≤ _
  by_cases hj : j = 0
  · simp only [hj, ldpBusemannNegativeSamples, ↓reduceIte, Nat.cast_zero,
      zero_add, Int.cast_zero, sub_self, mul_zero, abs_zero]
    positivity
  · simp only [ldpBusemannNegativeSamples, hj, ↓reduceIte, Int.cast_sub]
    rw [show ∀ a b c : ℝ, a * b - a * (b - c) = a * c by intros; ring]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem localJ1_dist_le_uniform_error (x y : CadlagLocal) {C : ℝ}
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
theorem negativeHalfLdpPath_shift_error_tendsto (ω : ℕ → Fin 3) :
    Tendsto (fun n => dist (ldpBusemannWholeLineNegativeHalfPath n ω)
      (negativeHalfLdpPath n ω)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => dist_nonneg) (fun n =>
    localJ1_dist_le_uniform_error _ _ (by positivity) (negativeHalfLdp_uniform_error n ω))
  simpa only [zero_mul, mul_zero] using
    (ldpBusemannJumpCoefficient_tendsto.mul_const |(Y ω (-1) : ℝ)|).const_mul 2

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpActualPath_measurable (n : ℕ) :
    Measurable (ldpBusemannWholeLineNegativeHalfPath n) :=
  measurable_subtype_coe.comp (ldpBusemannWholeLineNegativeHalf_measurable n)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
private theorem negativeHalfLdpActualLaw_tendsto_of_raw
    {ρ : ProbabilityMeasure CadlagLocal}
    (hraw : Tendsto negativeHalfLdpPathLaw atTop (𝓝 ρ)) :
    Tendsto (fun n => ProbabilityMeasure.map
      (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
      (ldpBusemannWholeLineNegativeHalfPath n)) atTop (𝓝 ρ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  let x₀ := ldpBusemannWholeLineNegativeHalfPath 0 (fun _ => 0)
  let B := C + |f x₀|
  have hB (x : CadlagLocal) : |f x| ≤ B := by
    have hh : |f x - f x₀| ≤ C := by simpa only [Real.dist_eq] using hC x x₀
    calc
      |f x| = |f x - f x₀ + f x₀| := by congr 1; ring
      _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
      _ ≤ B := add_le_add hh le_rfl
  have hX (n : ℕ) : Integrable
      (fun ω => f (ldpBusemannWholeLineNegativeHalfPath n ω)) iidCodeMeasure :=
    Integrable.of_bound
      ((hL.continuous.measurable.comp
        (negativeHalfLdpActualPath_measurable n)).aestronglyMeasurable)
      B (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hB _)
  have hY (n : ℕ) : Integrable
      (fun ω => f (negativeHalfLdpPath n ω)) iidCodeMeasure :=
    Integrable.of_bound
      ((hL.continuous.measurable.comp
        (negativeHalfLdpPath_measurable n)).aestronglyMeasurable)
      B (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hB _)
  have hdiff : Tendsto (fun n => ∫ ω,
      (f (ldpBusemannWholeLineNegativeHalfPath n ω) - f (negativeHalfLdpPath n ω))
        ∂iidCodeMeasure) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence
      (μ := iidCodeMeasure) (f := fun _ => (0 : ℝ)) (fun _ => 2 * B)
      (fun n => ((hX n).sub (hY n)).aestronglyMeasurable) (integrable_const _) ?_ ?_
    · simpa only [integral_zero, Pi.sub_apply] using hd
    · intro n
      exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        have hxB := hB (ldpBusemannWholeLineNegativeHalfPath n ω)
        have hyB := hB (negativeHalfLdpPath n ω)
        exact (abs_sub _ _).trans (by linarith only [hxB, hyB])
    · exact ae_of_all _ fun ω => by
        refine squeeze_zero_norm
          (a := fun n : ℕ => (L : ℝ) * dist (ldpBusemannWholeLineNegativeHalfPath n ω)
            (negativeHalfLdpPath n ω)) ?_ ?_
        · intro n
          change |f (ldpBusemannWholeLineNegativeHalfPath n ω) -
            f (negativeHalfLdpPath n ω)| ≤ _
          simpa only [Real.dist_eq] using
            hL.dist_le_mul (ldpBusemannWholeLineNegativeHalfPath n ω)
              (negativeHalfLdpPath n ω)
        · simpa only [mul_zero] using
            (negativeHalfLdpPath_shift_error_tendsto ω).const_mul (L : ℝ)
  have hmX (n : ℕ) :
      (∫ x, f x ∂(ProbabilityMeasure.map
        (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
        (ldpBusemannWholeLineNegativeHalfPath n) : Measure CadlagLocal)) =
        ∫ ω, f (ldpBusemannWholeLineNegativeHalfPath n ω) ∂iidCodeMeasure := by
    exact integral_map (negativeHalfLdpActualPath_measurable n).aemeasurable
      hL.continuous.stronglyMeasurable.aestronglyMeasurable
  have hmY (n : ℕ) :
      (∫ x, f x ∂(negativeHalfLdpPathLaw n : Measure CadlagLocal)) =
        ∫ ω, f (negativeHalfLdpPath n ω) ∂iidCodeMeasure := by
    exact integral_map (negativeHalfLdpPath_measurable n).aemeasurable
      hL.continuous.stronglyMeasurable.aestronglyMeasurable
  have hy := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hraw) f ⟨C, hC⟩ ⟨L, hL⟩
  simp_rw [hmY] at hy
  have hh := hdiff.add hy
  simp only [zero_add] at hh
  convert hh using 1
  funext n
  rw [hmX, integral_sub (hX n) (hY n), sub_add_cancel]


/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
converge under index-zero symmetry alone. The retained cutoff marginals come from
`negativeHalfLdpWindow_tendsto_of_sym`, whose block characteristic functions have
the positive real coefficient `negativeHalfLdpScale` and index `2 / 3`.
The limit is existential because the assembly predicate accepts a law as argument.
No subordinator law or new open functional-limit premise is used. -/
theorem ldpBusemannWholeLineNegativeHalfConverges_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω)) :
    ∃ ν : ProbabilityMeasure CadlagLocalZero,
      LdpBusemannWholeLineNegativeHalfConverges ν ∧
      ∀ N, (ν.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) = negativeHalfLdpCutoffLimit hsym N := by
  obtain ⟨ρ, hraw, hcut⟩ := negativeHalfLdpPathLaw_tendsto_of_sym hsym
  have hρ := negativeHalfLdpActualLaw_tendsto_of_raw hraw
  let S : Set CadlagLocal := {x | x.1 ⟨0, le_rfl⟩ = 0}
  have hS : IsClosed S := isClosed_eq continuous_halfLineOrigin continuous_const
  have hn (n : ℕ) :
      (iidCodeMeasure.map (ldpBusemannWholeLineNegativeHalfPath n)) S = 1 := by
    rw [Measure.map_apply (negativeHalfLdpActualPath_measurable n) hS.measurableSet]
    have heq : ldpBusemannWholeLineNegativeHalfPath n ⁻¹' S = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact ldpBusemannWholeLineNegativeHalfPath_zero n ω
    rw [heq, measure_univ]
  have hρS : (ρ : Measure CadlagLocal) S = 1 := by
    apply le_antisymm (by simpa only [measure_univ] using
      (measure_mono (Set.subset_univ S) : (ρ : Measure CadlagLocal) S ≤
        (ρ : Measure CadlagLocal) Set.univ))
    have hb := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hρ hS
    change (atTop.limsup fun n =>
      (iidCodeMeasure.map (ldpBusemannWholeLineNegativeHalfPath n)) S) ≤
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
  refine ⟨ν, ⟨ldpBusemannWholeLineNegativeHalf_measurable, ?_⟩, ?_⟩
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
          (ldpBusemannWholeLineNegativeHalf n) : Measure _) F =
        (ProbabilityMeasure.map
          (⟨iidCodeMeasure, inferInstance⟩ : ProbabilityMeasure (ℕ → Fin 3))
          (ldpBusemannWholeLineNegativeHalfPath n) : Measure _)
          (Subtype.val '' F) := by
      change (iidCodeMeasure.map (ldpBusemannWholeLineNegativeHalf n)) F =
        (iidCodeMeasure.map (ldpBusemannWholeLineNegativeHalfPath n)) (Subtype.val '' F)
      rw [Measure.map_apply (ldpBusemannWholeLineNegativeHalf_measurable n)
        hF.measurableSet, Measure.map_apply (negativeHalfLdpActualPath_measurable n)
        hFi.measurableSet]
      congr 1
      ext ω
      constructor
      · intro hω
        exact ⟨ldpBusemannWholeLineNegativeHalf n ω, hω, rfl⟩
      · rintro ⟨x, hx, heqx⟩
        have hx' : x = ldpBusemannWholeLineNegativeHalf n ω := Subtype.ext heqx
        change ldpBusemannWholeLineNegativeHalf n ω ∈ F
        rw [← hx']
        exact hx
    simp_rw [hnF, hνF]
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hρ hFi
  · have heq : ν.map (Subtype.val : CadlagLocalZero → CadlagLocal) = ρ :=
      ProbabilityMeasure.toMeasure_injective hmap
    simpa only [heq] using hcut

end DirectedDistances.Recursive
