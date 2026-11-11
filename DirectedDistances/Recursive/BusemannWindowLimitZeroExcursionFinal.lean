module

public import DirectedDistances.Recursive.BusemannWindowLimitZeroExcursion
public import DirectedDistances.Probability.StableNegativeMass
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Probability.IdentDistrib








public section

namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter WithLp
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology ENNReal

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannSDPMeasurableVersion

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The positive-time marginals of every window limit are spectrally positive stable laws. -/
theorem sdp_window_limit_stable_marginals
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ S : Set (J1Window 1), Sᶜ.Countable ∧
      (⟨1, by norm_num, le_rfl⟩ : J1Window 1) ∈ S ∧
      ∀ s ∈ S, 0 < (s : ℝ) →
        SpectrallyPositiveStableLaw (4 / 3)
          ((SDPMasterFromLaw.sdpG μ Y (-1)) ^ (2 / 3 : ℝ) * (s : ℝ) / 2)
          (ν.map (fun x => x.path.1 s)) := by
  obtain ⟨S, hS, hEnd, hfdd⟩ := sdp_busemann_window_limit_fdd hind hsym hν
  refine ⟨S, hS, hEnd, ?_⟩
  intro s hs hs0
  let t : ℕ → J1Window 1 := fun n => if n = 0 then ⟨0, by norm_num⟩ else s
  have ht0 : (t 0 : ℝ) = 0 := by simp [t]
  have htm : Monotone t := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      simp only [t, ↓reduceIte]
      split_ifs
      · exact le_rfl
      · exact hs0.le
    · have hj : j ≠ 0 := by omega
      simp [t, hi, hj]
  obtain ⟨hb, L, hchar, hEval⟩ := hfdd 1 t ht0 htm (by simpa [t] using hs)
  let b : ℝ := (SDPMasterFromLaw.sdpG μ Y (-1)) ^ (2 / 3 : ℝ)
  let κ : ℂ := ((1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) * (b : ℂ)
  have hstable := sdp_one_coordinate_marginal_spectrally_positive
    (b := b * (s : ℝ)) (mul_pos hb hs0)
    (κ := (s : ℂ) * κ) (by dsimp [κ]; push_cast; ring) L
    (by
      intro θ
      rw [hchar]
      simp only [t, Fin.isValue, Fin.val_zero, zero_add, one_ne_zero, ↓reduceIte,
        Fin.prod_univ_one, sub_zero, one_mul]
      congr 1
      split_ifs <;> simp [κ] <;> ring)
  have heq : ν.map (fun x => x.path.1 s) = L.map (fun z => z (0 : Fin 1)) := by
    apply ProbabilityMeasure.toMeasure_injective
    have hh := congrArg
      (fun p : ProbabilityMeasure (Fin 1 → ℝ) =>
        ((p : Measure (Fin 1 → ℝ)).map (fun z => z (0 : Fin 1)))) hEval
    simp only [ProbabilityMeasure.toMeasure_map] at hh
    rw [Measure.map_map (by fun_prop) (measurable_windowEvalVec _),
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    have hI : Finset.Iic (0 : Fin 1) = {0} := by decide
    simpa [Function.comp_def, windowEvalVec, t, cumulativeSum, hI] using hh
  rw [heq]
  exact hstable

private theorem stable_positive_dilation
    {α c r : ℝ} {ρ : ProbabilityMeasure ℝ}
    (hρ : SpectrallyPositiveStableLaw α c ρ) (hr : 0 < r) :
    SpectrallyPositiveStableLaw α (c * r ^ α) (ρ.map (r * ·)) := by
  refine ⟨hρ.1, hρ.2.1, mul_pos hρ.2.2.1 (Real.rpow_pos_of_pos hr _), ?_⟩
  intro u
  change charFun ((ρ : Measure ℝ).map (r * ·)) u = _
  rw [charFun_map_mul, hρ.2.2.2, abs_mul, abs_of_pos hr,
    Real.mul_rpow hr.le (abs_nonneg u)]
  have hpos : (0 < r * u) ↔ 0 < u := mul_pos_iff_of_pos_left hr
  have hneg : (r * u < 0) ↔ u < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hr : r * u < r * 0 ↔ u < 0)
  simp only [hpos, hneg]
  congr 1
  push_cast
  ring

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The negative mass of a spectrally positive stable law is independent of its scale. -/
theorem sdp_stable_negative_mass_scale_invariant
    {c d : ℝ} {ρ σ : ProbabilityMeasure ℝ}
    (hρ : SpectrallyPositiveStableLaw (4 / 3) c ρ)
    (hσ : SpectrallyPositiveStableLaw (4 / 3) d σ) :
    (ρ : Measure ℝ) (Set.Iio 0) = (σ : Measure ℝ) (Set.Iio 0) := by
  let r : ℝ := (d / c) ^ (3 / 4 : ℝ)
  have hdc : 0 < d / c := div_pos hσ.2.2.1 hρ.2.2.1
  have hr : 0 < r := Real.rpow_pos_of_pos hdc _
  have hscale : c * r ^ (4 / 3 : ℝ) = d := by
    dsimp [r]
    rw [← Real.rpow_mul hdc.le]
    norm_num
    exact mul_div_cancel₀ d hρ.2.2.1.ne'
  have hlaw : ρ.map (r * ·) = σ := by
    apply spectrally_positive_stable_law_unique _ hσ
    rw [← hscale]
    exact stable_positive_dilation hρ hr
  rw [← hlaw, ProbabilityMeasure.map_apply' _ (by fun_prop) measurableSet_Iio]
  congr 1
  ext x
  change x < 0 ↔ r * x < 0
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀ hr : r * x < r * 0 ↔ x < 0).symm

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
All positive-time marginals on the co-countable time set have the same positive -/
theorem sdp_window_limit_uniform_negative_mass
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ S : Set (J1Window 1), Sᶜ.Countable ∧ ∃ q : ℝ≥0∞, 0 < q ∧
      ∀ s ∈ S, 0 < (s : ℝ) →
        (ν : Measure (J1WindowD 1 (by norm_num))) {x | x.path.1 s < 0} = q := by
  obtain ⟨S, hS, hEnd, hstable⟩ := sdp_window_limit_stable_marginals hind hsym hν
  let e : J1Window 1 := ⟨1, by norm_num, le_rfl⟩
  let ρ := ν.map (fun x => x.path.1 e)
  have hρ := hstable e hEnd (by norm_num : (0 : ℝ) < 1)
  refine ⟨S, hS, (ρ : Measure ℝ) (Set.Iio 0),
    spectrally_positive_stable_negative_mass hρ, ?_⟩
  intro s hs hs0
  have heq := sdp_stable_negative_mass_scale_invariant (hstable s hs hs0) hρ
  rw [ProbabilityMeasure.map_apply' _
    (measurable_j1WindowD_eval (by norm_num) s).aemeasurable measurableSet_Iio] at heq
  exact heq

private theorem negative_interval_isOpen (a b c : ℝ) :
    IsOpen {x : J1WindowD 1 (by norm_num) |
      ∃ s : J1Window 1, a < (s : ℝ) ∧ (s : ℝ) < b ∧ x.path.1 s < c} := by
  rw [Metric.isOpen_iff]
  rintro x ⟨s, has, hsb, hsc⟩
  let δ := min ((s : ℝ) - a) (min (b - (s : ℝ)) (c - x.path.1 s))
  have hδ : 0 < δ := lt_min (sub_pos.mpr has)
    (lt_min (sub_pos.mpr hsb) (sub_pos.mpr hsc))
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  change (⨅ φ : J1TimeChange 1,
    max (⨆ t : J1Window 1, |((φ t : ℝ) - (t : ℝ))|)
      (⨆ t : J1Window 1, |y.path.1 (φ t) - x.path.1 t|)) < δ at hy
  obtain ⟨φ, hcost⟩ := exists_lt_of_ciInf_lt hy
  have htime : |(φ s : ℝ) - (s : ℝ)| < δ :=
    ((le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ) s le_rfl).trans
      (le_max_left _ _)).trans_lt hcost
  have hvalue : |y.path.1 (φ s) - x.path.1 s| < δ :=
    ((le_ciSup_of_le (j1WindowValueError_bddAbove y.path x.path φ) s le_rfl).trans
      (le_max_right _ _)).trans_lt hcost
  refine ⟨φ s, ?_, ?_, ?_⟩
  · have h := (abs_lt.mp htime).1
    have hd : δ ≤ (s : ℝ) - a := min_le_left _ _
    linarith
  · have h := (abs_lt.mp htime).2
    have hd : δ ≤ b - (s : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  · have h := (abs_lt.mp hvalue).2
    have hd : δ ≤ c - x.path.1 s := (min_le_right _ _).trans (min_le_right _ _)
    linarith

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Every weak limit gives positive mass to negative values arbitrarily near zero. -/
theorem sdp_window_limit_negative_germ_pos
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    0 < (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} := by
  obtain ⟨S, hS, q, hq, hmass⟩ := sdp_window_limit_uniform_negative_mass hind hsym hν
  let U : ℕ → Set (J1WindowD 1 (by norm_num)) := fun n =>
    {x | ∃ s : J1Window 1,
      0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0}
  have hanti : Antitone U := by
    intro n m hnm x hx
    obtain ⟨s, hs0, hsm, hneg⟩ := hx
    refine ⟨s, hs0, hsm.trans_le ?_, hneg⟩
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hbound (n : ℕ) : q ≤ (ν : Measure _) (U n) := by
    let b : ℝ := 1 / ((n + 1 : ℕ) : ℝ)
    have hb : 0 < b := by dsimp [b]; positivity
    have hb1 : b ≤ 1 := by
      dsimp [b]
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    let B : Set ℝ := Subtype.val '' Sᶜ
    have hB : B.Countable := hS.image Subtype.val
    have hnot : ¬ Set.Ioo 0 b ⊆ B := by
      intro hsub
      exact (not_le_of_gt hb) (Cardinal.Real.Ioo_countable_iff.mp (hB.mono hsub))
    obtain ⟨r, hr, hrB⟩ := Set.not_subset.mp hnot
    let s : J1Window 1 := ⟨r, hr.1.le, hr.2.le.trans hb1⟩
    have hs : s ∈ S := by
      by_contra h
      exact hrB ⟨s, h, rfl⟩
    rw [← hmass s hs hr.1]
    exact measure_mono (fun x hx => ⟨s, hr.1, hr.2, hx⟩)
  have hmeas (n : ℕ) : MeasurableSet (U n) :=
    (negative_interval_isOpen 0 (1 / ((n + 1 : ℕ) : ℝ)) 0).measurableSet
  have hpos : 0 < (ν : Measure _) (⋂ n, U n) := by
    rw [hanti.measure_iInter (fun n => (hmeas n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    exact hq.trans_le (le_iInf hbound)
  have heq : (⋂ n, U n) =
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, U]
  rw [heq] at hpos
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The negative germ event is Borel measurable on the path space. -/
theorem sdp_window_negative_germ_measurableSet :
    MeasurableSet {x : J1WindowD 1 (by norm_num) |
      ∀ n : ℕ, ∃ s : J1Window 1,
        0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} := by
  have h (n : ℕ) :=
    (negative_interval_isOpen 0 (1 / ((n + 1 : ℕ) : ℝ)) 0).measurableSet
  simpa only [Set.ofPred_forall] using MeasurableSet.iInter h

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
At co-countably many times, a past evaluation is independent of the following increment.
This is a path-law statement, rather than independence only on a latent FDD space. -/
theorem sdp_window_limit_eval_indep_increment
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ S : Set (J1Window 1), Sᶜ.Countable ∧
      ∀ s ∈ S, ∀ u ∈ S, s ≤ u →
        IndepFun (fun x => x.path.1 s) (fun x => x.path.1 u - x.path.1 s)
          (ν : Measure (J1WindowD 1 (by norm_num))) := by
  obtain ⟨S, hS, _, hfdd⟩ := sdp_busemann_window_limit_fdd_indep_increments hind hsym hν
  refine ⟨S, hS, ?_⟩
  intro s hs u hu hsu
  let t : ℕ → J1Window 1 :=
    fun n => if n = 0 then ⟨0, by norm_num⟩ else if n = 1 then s else u
  have ht0 : (t 0 : ℝ) = 0 := by simp [t]
  have htm : Monotone t := by
    intro i j hij
    dsimp [t]
    split_ifs <;> first
    | exact le_rfl
    | exact s.property.1
    | exact u.property.1
    | exact hsu
    | omega
  obtain ⟨_, L, _, hInd, hEval⟩ := hfdd 2 t ht0 htm (by
    intro i
    fin_cases i <;> simp [t, hs, hu])
  have hcoord : IndepFun (fun z : EuclideanSpace ℝ (Fin 2) => z (0 : Fin 2))
      (fun z => z (1 : Fin 2)) (L : Measure _) :=
    hInd.indepFun (by decide : (0 : Fin 2) ≠ 1)
  apply indepFun_of_identDistrib_pair hcoord
  refine ⟨by fun_prop, ?_, ?_⟩
  · exact ((measurable_j1WindowD_eval (by norm_num) s).prodMk
      ((measurable_j1WindowD_eval (by norm_num) u).sub
        (measurable_j1WindowD_eval (by norm_num) s))).aemeasurable
  · let d : (Fin 2 → ℝ) → ℝ × ℝ := fun z => (z 0, z 1 - z 0)
    have hh := congrArg
      (fun p : ProbabilityMeasure (Fin 2 → ℝ) => (p : Measure (Fin 2 → ℝ)).map d)
      hEval
    simp only [ProbabilityMeasure.toMeasure_map] at hh
    rw [Measure.map_map (by dsimp [d]; fun_prop) (measurable_windowEvalVec _),
      Measure.map_map (by dsimp [d]; fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    have hI0 : Finset.Iic (0 : Fin 2) = {0} := by decide
    have hI1 : Finset.Iic (1 : Fin 2) = {0, 1} := by decide
    simpa [d, Function.comp_def, windowEvalVec, t, cumulativeSum, hI0, hI1]
      using hh.symm

private theorem cumulativeSum_coordinate {m : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    cumulativeSum z i = ∑ j ∈ Finset.Iic i, z j := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)
  have he (y : Fin m → ℝ) (j : Fin m) : (e.symm y) j = y j := by
    change e (e.symm y) j = y j
    rw [e.apply_symm_apply]
  change (e.symm
    ((ContinuousLinearMap.pi fun r =>
      ∑ j ∈ Finset.Iic r,
        ContinuousLinearMap.proj (ι := Fin m) (φ := fun _ : Fin m => ℝ) j)
      (e z))) i = _
  rw [he]
  simp only [ContinuousLinearMap.pi_apply, sum_apply, ContinuousLinearMap.proj_apply]
  rfl

private theorem cumulativeSum_sub {m : ℕ}
    (z : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin m) :
    cumulativeSum z i.succ - cumulativeSum z i.castSucc = z i.succ := by
  have hI : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.ext_iff, Fin.le_def,
      Fin.val_succ, Fin.val_castSucc]
    constructor <;> intro h <;> omega
  rw [cumulativeSum_coordinate, cumulativeSum_coordinate, hI,
    Finset.sum_insert (by simp), add_sub_cancel_right]

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Every ordered finite grid in the co-countable time set has independent actual path increments. -/
theorem sdp_window_limit_path_indep_increments
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ S : Set (J1Window 1), Sᶜ.Countable ∧
      ∀ (m : ℕ) (t : Fin (m + 1) → J1Window 1), Monotone t → (∀ i, t i ∈ S) →
        iIndepFun (fun (i : Fin m) (x : J1WindowD 1 (by norm_num)) =>
          x.path.1 (t i.succ) - x.path.1 (t i.castSucc)) (ν : Measure _) := by
  obtain ⟨S, hS, _, hfdd⟩ := sdp_busemann_window_limit_fdd_indep_increments hind hsym hν
  refine ⟨S, hS, ?_⟩
  intro m t htm htS
  let q : ℕ → J1Window 1 := fun n =>
    if n = 0 then ⟨0, by norm_num⟩ else t ⟨min (n - 1) m, by omega⟩
  have hq0 : (q 0 : ℝ) = 0 := by simp [q]
  have hqm : Monotone q := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      simp only [q, ↓reduceIte]
      split_ifs
      · exact le_rfl
      · exact (t _).property.1
    · have hj : j ≠ 0 := by omega
      simp only [q, ite_eq_right hi, ite_eq_right hj]
      apply htm
      change min (i - 1) m ≤ min (j - 1) m
      omega
  have hqt (i : Fin (m + 1)) : q (i.val + 1) = t i := by
    simp only [q, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    congr 1
    apply Fin.ext
    exact min_eq_left (by omega)
  obtain ⟨_, L, _, hInd, hEval⟩ := hfdd (m + 1) q hq0 hqm (by
    intro i
    rw [hqt]
    exact htS i)
  have hEval' : ν.map (windowEvalVec t) =
      (L.map (cumulativeSum (k := m + 1))).map WithLp.ofLp := by
    simpa only [hqt] using hEval
  let d : (Fin (m + 1) → ℝ) → Fin m → ℝ :=
    fun z i => z i.succ - z i.castSucc
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hmap := congrArg
    (fun p : ProbabilityMeasure (Fin (m + 1) → ℝ) =>
      (p : Measure (Fin (m + 1) → ℝ)).map d) hEval'
  simp only [ProbabilityMeasure.toMeasure_map] at hmap
  rw [Measure.map_map hd (measurable_windowEvalVec _),
    Measure.map_map hd (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  have hdiff : (d ∘ WithLp.ofLp) ∘ cumulativeSum =
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) => fun i : Fin m => z i.succ) := by
    funext z i
    exact cumulativeSum_sub z i
  rw [hdiff] at hmap
  have hInd' := hInd.precomp (g := fun i : Fin m => i.succ) (Fin.succ_injective m)
  have hm (i : Fin m) : Measurable (fun x : J1WindowD 1 (by norm_num) =>
      x.path.1 (t i.succ) - x.path.1 (t i.castSucc)) :=
    (measurable_j1WindowD_eval (by norm_num) _).sub
      (measurable_j1WindowD_eval (by norm_num) _)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  change (ν : Measure _).map (d ∘ windowEvalVec t) = _
  rw [hmap, hInd'.map_fun_eq_pi_map (by fun_prop)]
  congr 1
  funext i
  have hh := congrArg (fun p : Measure (Fin m → ℝ) => p.map (fun z => z i)) hmap
  rw [Measure.map_map (by fun_prop) (hd.comp (measurable_windowEvalVec _)),
    Measure.map_map (by fun_prop) (by fun_prop)] at hh
  exact hh.symm

end DirectedDistances.Recursive
