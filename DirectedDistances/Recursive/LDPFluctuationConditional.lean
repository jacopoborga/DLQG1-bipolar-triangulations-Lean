module

public import DirectedDistances.Recursive.LDPRecursiveConditional

import DirectedDistances.Recursive.BusemannTailLDPConditional

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Real

/-! Supporting lemmas for paper labels `lem-ldp-fluctuation` (see CORRESPONDENCE.md). -/











public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk
open scoped ENNReal

private theorem integral_min_of_power_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZmeas : Measurable Z) (hZnonneg : ∀ ω, 0 ≤ Z ω)
    {C α t : ℝ} (hC : 0 ≤ C) (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t)
    (htail : ∀ x, 0 < x → μ.real {ω | x < Z ω} ≤ C * x ^ (-α)) :
    ∫ ω, min (Z ω) t ∂μ ≤ C * t ^ (1 - α) / (1 - α) := by
  classical
  let u : Ω → ℝ := fun ω => min (Z ω) t
  let F : ℝ → ℝ := fun x => μ.real {ω | x < u ω}
  have hu_nonneg : ∀ ω, 0 ≤ u ω := fun ω => le_min (hZnonneg ω) ht.le
  have hu_meas : Measurable u := hZmeas.min measurable_const
  have hu_int : Integrable u μ := by
    apply (integrable_const t).mono' hu_meas.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hu_nonneg ω)]
    exact min_le_right _ _
  have hFanti : Antitone F := by
    intro x y hxy
    exact measureReal_mono (fun ω hω => lt_of_le_of_lt hxy hω) (measure_ne_top μ _)
  have hFmeas : Measurable F := hFanti.measurable
  have hFnonneg : ∀ x, 0 ≤ F x := fun x => measureReal_nonneg
  have hFleone : ∀ x, F x ≤ 1 := by
    intro x
    calc
      F x ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
      _ = 1 := by simp
  have hFintIoc : IntegrableOn F (Set.Ioc 0 t) (volume : Measure ℝ) := by
    apply Measure.integrableOn_of_bounded (ne_of_lt measure_Ioc_lt_top)
      hFmeas.aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFnonneg x)] using hFleone x
  have hFintIoi : IntegrableOn F (Set.Ioi 0) (volume : Measure ℝ) := by
    have hIglobal : Integrable ((Set.Ioc 0 t).indicator F) (volume : Measure ℝ) :=
      hFintIoc.integrable_indicator (measurableSet_Ioc : MeasurableSet (Set.Ioc 0 t))
    have hI : IntegrableOn ((Set.Ioc 0 t).indicator F) (Set.Ioi 0) volume :=
      hIglobal.integrableOn
    apply (integrableOn_congr_fun_ae ?_).2 hI
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
      with x hx
    have hx0 : 0 < x := hx
    by_cases hxt : x ≤ t
    · simp [Set.indicator, Set.mem_Ioc, hx0, hxt]
    · have htx : t ≤ x := le_of_not_ge hxt
      have hzero : F x = 0 := by
        have hs : {ω | x < u ω} = (∅ : Set Ω) := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
          constructor
          · intro h
            exact (not_lt_of_ge (le_trans (min_le_right _ _) htx)) h
          · intro h
            exact False.elim h
        simp [F, hs]
      simp [Set.indicator, Set.mem_Ioc, hx0, hxt, hzero]
  have hFtail (x : ℝ) (hx : t ≤ x) : F x = 0 := by
    have hs : {ω | x < u ω} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · intro h
        exact (not_lt_of_ge (le_trans (min_le_right _ _) hx)) h
      · intro h
        exact False.elim h
    simp [F, hs]
  have hFinterval : IntervalIntegrable F volume 0 t := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).2
      (hFintIoi.mono_set (by intro x hx; exact hx.1))
  have hFtailInt : IntegrableOn F (Set.Ioi t) volume :=
    hFintIoi.mono_set (Set.Ioi_subset_Ioi ht.le)
  have hlayer := hu_int.integral_eq_integral_meas_lt
    (Eventually.of_forall hu_nonneg)
  have hFbound : ∫ x in Set.Ioi 0, F x ∂volume ≤ C * t ^ (1 - α) / (1 - α) := by
    rw [← intervalIntegral.integral_interval_add_Ioi' hFinterval hFtailInt]
    have htailZero : ∫ x in Set.Ioi t, F x ∂volume = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi t))]
        with x hx
      exact hFtail x (le_of_lt hx)
    rw [htailZero, add_zero, intervalIntegral.integral_of_le ht.le]
    have hFint : IntegrableOn F (Set.Ioc 0 t) volume :=
      hFintIoi.mono_set (by intro x hx; exact hx.1)
    have hGint : IntegrableOn (fun x : ℝ => C * x ^ (-α)) (Set.Ioc 0 t) volume := by
      have hp : IntervalIntegrable (fun x : ℝ => x ^ (-α)) volume 0 t :=
        intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -α)
      have hp' : IntervalIntegrable (fun x : ℝ => C * x ^ (-α)) volume 0 t := by
        simpa only [mul_comm] using hp.const_mul C
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hp'
    have hFG (x : ℝ) (hx : x ∈ Set.Ioc 0 t) : F x ≤ C * x ^ (-α) := by
      have hx0 : 0 < x := hx.1
      by_cases hxt : x < t
      · have hset : {ω | x < u ω} = {ω | x < Z ω} := by
          ext ω
          simp [u, hxt]
        simpa [F, hset] using htail x hx0
      · have hxeq : x = t := le_antisymm hx.2 (le_of_not_gt hxt)
        rw [hxeq]
        simp [F, u]
        exact mul_nonneg hC (Real.rpow_nonneg ht.le _)
    have hmono := setIntegral_mono_on hFint hGint measurableSet_Ioc hFG
    calc
      ∫ x in Set.Ioc 0 t, F x ∂volume ≤
          ∫ x in Set.Ioc 0 t, C * x ^ (-α) ∂volume := hmono
      _ = C * t ^ (1 - α) / (1 - α) := by
        rw [← intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith : -1 < -α))]
        rw [show -α + 1 = 1 - α by ring,
          Real.zero_rpow (by linarith : (1 - α : ℝ) ≠ 0), sub_zero]
        ring
  rw [hlayer]
  exact hFbound

private theorem measureReal_lt_le_integral_div
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (hfm : Measurable f)
    (hn : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t < f ω} ≤ (∫ ω, f ω ∂μ) / t := by
  have hreal := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hn) hf t
  calc
    μ.real {ω | t < f ω} ≤ μ.real {ω | t ≤ f ω} :=
      measureReal_mono (by intro ω h; change t ≤ f ω; exact le_of_lt h)
        (measure_ne_top μ _)
    _ ≤ (∫ ω, f ω ∂μ) / t := (le_div_iff₀ ht).2 (by nlinarith [hreal])

/-- A tail bound for a finite sum from uniform power-law tails. This is a -/
theorem probability_sum_tail_of_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (Z : Fin m → Ω → ℝ)
    (hZmeas : ∀ i, Measurable (Z i))
    (hZnonneg : ∀ i ω, 0 ≤ Z i ω)
    {C α : ℝ} (hC : 0 ≤ C) (hα0 : 0 < α) (hα1 : α < 1)
    (htail : ∀ i x, 0 < x → μ.real {ω | x < Z i ω} ≤ C * x ^ (-α)) :
    ∀ t, 0 < t →
      μ.real {ω | t < ∑ i, Z i ω} ≤
        C * (1 + 1 / (1 - α)) * (m : ℝ) * t ^ (-α) := by
  classical
  intro t ht
  let W : Ω → ℝ := fun ω => ∑ i : Fin m, min (Z i ω) t
  have hmean (i : Fin m) :
      ∫ ω, min (Z i ω) t ∂μ ≤ C * t ^ (1 - α) / (1 - α) :=
    integral_min_of_power_tail μ (Z i) (hZmeas i) (hZnonneg i)
      hC hα0 hα1 ht (htail i)
  have hUiInt (i : Fin m) : Integrable (fun ω => min (Z i ω) t) μ := by
    exact (integrable_const t).mono' ((hZmeas i).min measurable_const).aestronglyMeasurable
      (by
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hZnonneg i ω) ht.le)]
        exact min_le_right _ _)
  have hWint : Integrable W μ := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hUiInt i
  have hWmeas : Measurable W := by
    dsimp [W]
    fun_prop
  have hWnonneg : ∀ ω, 0 ≤ W ω := by
    intro ω
    dsimp [W]
    exact Finset.sum_nonneg fun i hi => le_min (hZnonneg i ω) ht.le
  have hWbound :
      ∫ ω, W ω ∂μ ≤ (m : ℝ) * (C * t ^ (1 - α) / (1 - α)) := by
    change ∫ ω, ∑ i : Fin m, min (Z i ω) t ∂μ ≤ _
    rw [integral_finsetSum Finset.univ (fun i hi => hUiInt i)]
    calc
      ∑ i ∈ Finset.univ, ∫ ω, min (Z i ω) t ∂μ ≤
          ∑ i ∈ Finset.univ, C * t ^ (1 - α) / (1 - α) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hmean i
      _ = (m : ℝ) * (C * t ^ (1 - α) / (1 - α)) := by simp
  have hsub : {ω | t < ∑ i : Fin m, Z i ω} ⊆
      (⋃ i : Fin m, {ω | t < Z i ω}) ∪ {ω | t < W ω} := by
    intro ω hω
    by_cases hlarge : ∃ i, t < Z i ω
    · exact Or.inl (Set.mem_iUnion.mpr hlarge)
    · right
      have hsmall : ∀ i, Z i ω ≤ t := fun i => le_of_not_gt (fun h => hlarge ⟨i, h⟩)
      have hsum : (∑ i : Fin m, Z i ω) = W ω := by
        dsimp [W]
        apply Finset.sum_congr rfl
        intro i hi
        rw [min_eq_left (hsmall i)]
      change t < W ω
      exact hsum ▸ hω
  have hB : μ.real (⋃ i : Fin m, {ω | t < Z i ω}) ≤
      (m : ℝ) * C * t ^ (-α) := by
    calc
      μ.real (⋃ i : Fin m, {ω | t < Z i ω}) ≤
          ∑ i : Fin m, μ.real {ω | t < Z i ω} :=
            measureReal_iUnion_fintype_le (fun i => {ω | t < Z i ω})
      _ ≤ ∑ _i : Fin m, C * t ^ (-α) :=
        Finset.sum_le_sum fun i hi => htail i t ht
      _ = (m : ℝ) * C * t ^ (-α) := by simp [mul_assoc]
  have hA : μ.real {ω | t < W ω} ≤
      (m : ℝ) * (C * t ^ (1 - α) / (1 - α)) / t := by
    calc
      μ.real {ω | t < W ω} ≤ (∫ ω, W ω ∂μ) / t :=
        measureReal_lt_le_integral_div μ W hWint hWmeas hWnonneg ht
      _ ≤ (m : ℝ) * (C * t ^ (1 - α) / (1 - α)) / t :=
        div_le_div_of_nonneg_right hWbound ht.le
  have hpow : t ^ (1 - α) = t * t ^ (-α) := by
    rw [show (1 - α : ℝ) = 1 + (-α) by ring, Real.rpow_add ht, Real.rpow_one]
  have hcombine :
      (m : ℝ) * C * t ^ (-α) +
          (m : ℝ) * (C * t ^ (1 - α) / (1 - α)) / t =
        C * (1 + 1 / (1 - α)) * (m : ℝ) * t ^ (-α) := by
    rw [hpow]
    have hden : 1 - α ≠ 0 := by linarith
    field_simp [hden, ne_of_gt ht]
  calc
    μ.real {ω | t < ∑ i : Fin m, Z i ω} ≤
        μ.real ((⋃ i : Fin m, {ω | t < Z i ω}) ∪ {ω | t < W ω}) :=
          measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real (⋃ i : Fin m, {ω | t < Z i ω}) + μ.real {ω | t < W ω} :=
          measureReal_union_le _ _
    _ ≤ (m : ℝ) * C * t ^ (-α) +
        (m : ℝ) * (C * t ^ (1 - α) / (1 - α)) / t := add_le_add hB hA
    _ = C * (1 + 1 / (1 - α)) * (m : ℝ) * t ^ (-α) := hcombine


private theorem uniform_power_bound_of_asymptotic
    (P : ℝ → ℝ) (hP : ∀ t, P t ≤ 1) {a α : ℝ} (hα : 0 ≤ α)
    (hasym : (fun t => P t - a * t ^ (-α)) =o[atTop]
      (fun t : ℝ => t ^ (-α))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t → P t ≤ C * t ^ (-α) := by
  obtain ⟨r, hr⟩ := (hasym.def zero_lt_one).exists_forall_of_atTop
  let R : ℝ := max 1 r
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C : ℝ := |a| + 1 + 1 / R ^ (-α)
  have hRpow : 0 < R ^ (-α) := Real.rpow_pos_of_pos hR _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  have htpow : 0 ≤ t ^ (-α) := (Real.rpow_pos_of_pos ht _).le
  by_cases hRt : R ≤ t
  · have hh := hr t (le_trans (le_max_right 1 r) hRt)
    simp only [Real.norm_eq_abs, abs_of_nonneg htpow, one_mul] at hh
    have hup : P t - a * t ^ (-α) ≤ t ^ (-α) := (le_abs_self _).trans hh
    have ha : a ≤ |a| := le_abs_self a
    have hcoef : a + 1 ≤ C := by
      dsimp [C]
      have : 0 ≤ 1 / R ^ (-α) := by positivity
      linarith
    calc
      P t ≤ (a + 1) * t ^ (-α) := by linarith
      _ ≤ C * t ^ (-α) := mul_le_mul_of_nonneg_right hcoef htpow
  · have hpow : R ^ (-α) ≤ t ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos ht (le_of_not_ge hRt) (neg_nonpos.mpr hα)
    have hsmall : 1 ≤ C * t ^ (-α) := by
      calc
        1 = (1 / R ^ (-α)) * R ^ (-α) := by field_simp
        _ ≤ (1 / R ^ (-α)) * t ^ (-α) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ C * t ^ (-α) := by
          apply mul_le_mul_of_nonneg_right _ htpow
          dsimp [C]
          have := abs_nonneg a
          linarith
    exact (hP t).trans hsmall

private theorem tsum_ite_le_one {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hs : HasSum f 1) (p : ι → Prop) [DecidablePred p] :
    (∑' i, if p i then f i else 0) ≤ 1 := by
  have hn (i : ι) : 0 ≤ (if p i then f i else 0) := by
    split_ifs
    · exact hf i
    · exact le_rfl
  have hl (i : ι) : (if p i then f i else 0) ≤ f i := by
    split_ifs
    · exact le_rfl
    · exact hf i
  have hi := Summable.of_nonneg_of_le hn hl hs.summable
  simpa only [hs.tsum_eq] using hi.tsum_le_tsum hl hs.summable





theorem ldp_tail_bounds_of_busemann_items
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hstatR : ∀ k ≥ 1, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 1))
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0))
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      (∑' x : ℤ, if t < |(x : ℝ)| then
        ldpF iidCodeMeasure busemannLDPMeasurableVersion x else 0) ≤
          C * t ^ (-(2 / 3 : ℝ)) ∧
      (∑' y : ℤ, if (y : ℝ) < -t then
        ldpG iidCodeMeasure busemannLDPMeasurableVersion y else 0) ≤
          C * t ^ (-(2 / 3 : ℝ)) := by
  classical
  obtain ⟨hf, hg⟩ := ldp_tail_asymptotics_of_busemann_items hind hstatR hstatL hsym
  obtain ⟨Cf, hCf, hfb⟩ := uniform_power_bound_of_asymptotic
    (fun t => ∑' x : ℤ, if t < |(x : ℝ)| then
      ldpF iidCodeMeasure busemannLDPMeasurableVersion x else 0)
    (fun t => tsum_ite_le_one _ busemann_ldpF_nonneg busemann_ldpF_hasSum_one _)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) hf
  obtain ⟨Cg, hCg, hgb⟩ := uniform_power_bound_of_asymptotic
    (fun t => ∑' y : ℤ, if (y : ℝ) < -t then
      ldpG iidCodeMeasure busemannLDPMeasurableVersion y else 0)
    (fun t => tsum_ite_le_one _ busemann_ldpG_nonneg busemann_ldpG_hasSum_one _)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) hg
  refine ⟨max Cf Cg, le_trans hCf (le_max_left _ _), ?_⟩
  intro t ht
  have hp : 0 ≤ t ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg ht.le _
  exact ⟨(hfb t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp),
    (hgb t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)⟩


private theorem measurable_fluctuation_increment (k : ℤ) :
    Measurable (ldpIncrement busemannLDPMeasurableVersion k) :=
  (measurable_busemannLDPMeasurableVersion k).sub
    (measurable_busemannLDPMeasurableVersion (k - 1))

private theorem absolute_tail_eq_of_increment_map {k j : ℤ}
    (h : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion j)) (t : ℝ) :
    iidCodeMeasure.real {ω | t < |((ldpIncrement busemannLDPMeasurableVersion k ω : ℤ) : ℝ)|} =
      iidCodeMeasure.real {ω | t < |((ldpIncrement busemannLDPMeasurableVersion j ω : ℤ) : ℝ)|} := by
  have hm := congrArg (fun ν : Measure ℤ => ν.real {z | t < |(z : ℝ)|}) h
  rw [map_measureReal_apply (measurable_fluctuation_increment k) MeasurableSet.of_discrete,
    map_measureReal_apply (measurable_fluctuation_increment j) MeasurableSet.of_discrete] at hm
  exact hm






theorem ldp_absolute_increment_tail_bound_of_items
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hstatR : ∀ k ≥ 1, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 1))
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0))
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ, ∀ t : ℝ, 0 < t →
      iidCodeMeasure.real
        {ω | t < |((ldpIncrement busemannLDPMeasurableVersion k ω : ℤ) : ℝ)|} ≤
          C * t ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨_, hright, hleft⟩ := busemann_tail_ldp_strict_of_items hind hstatR hstatL hsym
  have hmass (P : Set (ℕ → Fin 3)) : iidCodeMeasure.real P ≤ 1 := by
    calc
      iidCodeMeasure.real P ≤ iidCodeMeasure.real Set.univ :=
        measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
      _ = 1 := by simp
  obtain ⟨Cr, hCr, hbr⟩ := uniform_power_bound_of_asymptotic _
    (fun _ => hmass _) (by norm_num : (0 : ℝ) ≤ 2 / 3) hright
  obtain ⟨Cl, hCl, hbl⟩ := uniform_power_bound_of_asymptotic _
    (fun _ => hmass _) (by norm_num : (0 : ℝ) ≤ 2 / 3) hleft
  have hrightAbs (t : ℝ) :
      iidCodeMeasure.real
        {ω | t < |((ldpIncrement busemannLDPMeasurableVersion 1 ω : ℤ) : ℝ)|} =
      iidCodeMeasure.real
        {ω | ((busemannLDPMeasurableVersion ω 1 -
          busemannLDPMeasurableVersion ω 0 : ℤ) : ℝ) < -t} := by
    apply measureReal_congr
    filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_item_pos] with ω hω
    have hn : ((busemannLDPMeasurableVersion ω 1 -
        busemannLDPMeasurableVersion ω 0 : ℤ) : ℝ) ≤ 0 := by
      have hh := hω 1 le_rfl
      simp only [sub_self] at hh
      exact_mod_cast (le_trans hh (by norm_num : (-1 : ℤ) ≤ 0))
    change (t < |((busemannLDPMeasurableVersion ω 1 -
        busemannLDPMeasurableVersion ω 0 : ℤ) : ℝ)|) =
      (((busemannLDPMeasurableVersion ω 1 -
        busemannLDPMeasurableVersion ω 0 : ℤ) : ℝ) < -t)
    rw [abs_of_nonpos hn]
    apply propext
    constructor <;> intro h <;> linarith only [h]
  refine ⟨max Cr Cl, le_trans hCr (le_max_left _ _), ?_⟩
  intro k t ht
  have hp := (Real.rpow_pos_of_pos ht (-(2 / 3 : ℝ))).le
  by_cases hk : 1 ≤ k
  · rw [absolute_tail_eq_of_increment_map (hstatR k hk) t, hrightAbs t]
    exact (hbr t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hk0 : k ≤ 0 := by omega
    rw [absolute_tail_eq_of_increment_map (hstatL k hk0) t]
    have hl : iidCodeMeasure.real
        {ω | t < |((ldpIncrement busemannLDPMeasurableVersion 0 ω : ℤ) : ℝ)|} ≤
          Cl * t ^ (-(2 / 3 : ℝ)) := by
      simpa only [ldpIncrement, zero_sub, neg_neg] using hbl t ht
    exact hl.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)

end DirectedDistances.Recursive
