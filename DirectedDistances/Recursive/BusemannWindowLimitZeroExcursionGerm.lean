module

public import DirectedDistances.Recursive.BusemannWindowLimitZeroExcursionFinal
public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPLowerTransferAssembly
import DirectedDistances.Recursive.BusemannWindowLimitNegativeExcursion
import Mathlib.Analysis.Real.Cardinality

/-! # Early evaluation measurability of negative germs

Helpers toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not paper results. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology ENNReal

local notation "μ" => iidCodeMeasure
local notation "Y" => busemannSDPMeasurableVersion

/-- Helper toward Lemma 7.12; not a paper result.
Negative values in an open time interval are detected by any dense set of times. -/
theorem sdp_window_negative_interval_iff_dense
    (D : Set (J1Window 1)) (hD : Dense D)
    (x : J1WindowD 1 (by norm_num)) {a b : ℝ} (hb : b ≤ 1) :
    (∃ s : J1Window 1, a < (s : ℝ) ∧ (s : ℝ) < b ∧ x.path.1 s < 0) ↔
      ∃ s ∈ D, a < (s : ℝ) ∧ (s : ℝ) < b ∧ x.path.1 s < 0 := by
  constructor
  · rintro ⟨s, has, hsb, hsneg⟩
    obtain ⟨r, hr, hnear⟩ := Metric.continuousWithinAt_iff.mp
      (x.path.2.isRightContinuous s) (-x.path.1 s) (neg_pos.mpr hsneg)
    let u : ℝ := min b ((s : ℝ) + r)
    have hsu : (s : ℝ) < u := lt_min hsb (lt_add_of_pos_right _ hr)
    obtain ⟨v, hsv, hvu⟩ := exists_between hsu
    let t : J1Window 1 :=
      ⟨v, s.property.1.trans hsv.le, hvu.le.trans ((min_le_left _ _).trans hb)⟩
    obtain ⟨z, hzD, hsz, hzt⟩ :=
      hD.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr (show s < t from hsv))
    have hszR : (s : ℝ) < (z : ℝ) := hsz
    have hztR : (z : ℝ) < v := hzt
    have hzb : (z : ℝ) < b := hztR.trans (hvu.trans_le (min_le_left _ _))
    have hzr : (z : ℝ) < (s : ℝ) + r :=
      hztR.trans (hvu.trans_le (min_le_right _ _))
    have hdist : dist z s < r := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr hszR)]
      linarith
    have hclose := hnear (show z ∈ Set.Ioi s from hsz) hdist
    rw [Real.dist_eq] at hclose
    exact ⟨z, hzD, has.trans hszR, hzb, by linarith [(abs_lt.mp hclose).2]⟩
  · rintro ⟨s, _, has, hsb, hneg⟩
    exact ⟨s, has, hsb, hneg⟩

/-- Helper toward Lemma 7.12; not a paper result.
The negative germ can be tested using only times below any positive cutoff. -/
theorem sdp_window_negative_germ_iff_cutoff
    (x : J1WindowD 1 (by norm_num)) {δ : ℝ} (hδ : 0 < δ) :
    (∀ n : ℕ, ∃ s : J1Window 1,
      0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0) ↔
    (∀ n : ℕ, ∃ s : J1Window 1,
      0 < (s : ℝ) ∧ (s : ℝ) < min δ (1 / ((n + 1 : ℕ) : ℝ)) ∧
        x.path.1 s < 0) := by
  constructor
  · intro hx n
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    have hk' : 1 / ((k + 1 : ℕ) : ℝ) < δ := by simpa only [Nat.cast_add,
      Nat.cast_one] using hk
    obtain ⟨s, hs0, hsm, hneg⟩ := hx (max k n)
    have hsmall (j : ℕ) (hj : j ≤ max k n) :
        1 / ((max k n + 1 : ℕ) : ℝ) ≤ 1 / ((j + 1 : ℕ) : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hj 1
    exact ⟨s, hs0, lt_min ((hsm.trans_le (hsmall k (le_max_left _ _))).trans hk')
      (hsm.trans_le (hsmall n (le_max_right _ _))), hneg⟩
  · intro hx n
    obtain ⟨s, hs0, hsm, hneg⟩ := hx n
    exact ⟨s, hs0, hsm.trans_le (min_le_right _ _), hneg⟩

/-- Helper toward Lemma 7.12; not a paper result.
The negative germ is measurable in evaluations strictly before every positive cutoff. -/
theorem sdp_window_negative_germ_measurable_early
    (D : Set (J1Window 1)) (hDc : D.Countable) (hD : Dense D)
    {δ : ℝ} (hδ : 0 < δ) :
    MeasurableSet[⨆ s : {s : J1Window 1 // s ∈ D ∧ 0 < (s : ℝ) ∧ (s : ℝ) < δ},
      MeasurableSpace.comap (fun x : J1WindowD 1 (by norm_num) => x.path.1 s.1)
        inferInstance]
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} := by
  classical
  let I := {s : J1Window 1 // s ∈ D ∧ 0 < (s : ℝ) ∧ (s : ℝ) < δ}
  have hIset :
      {s : J1Window 1 | s ∈ D ∧ 0 < (s : ℝ) ∧ (s : ℝ) < δ}.Countable :=
    hDc.mono (fun _ h => h.1)
  have : Countable I := hIset.to_subtype
  let m : MeasurableSpace (J1WindowD 1 (by norm_num)) :=
    ⨆ s : I, MeasurableSpace.comap (fun x => x.path.1 s.1) inferInstance
  have hm (s : I) : Measurable[m] (fun x => x.path.1 s.1) :=
    Measurable.of_comap_le (le_iSup (fun s : I =>
      MeasurableSpace.comap (fun x : J1WindowD 1 (by norm_num) => x.path.1 s.1)
        inferInstance) s)
  have heq :
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} =
      ⋂ n : ℕ, ⋃ s : I,
        {x | (s.1 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s.1 < 0} := by
    ext x
    rw [Set.mem_iInter]
    constructor
    · intro hx n
      have hn := (sdp_window_negative_germ_iff_cutoff x hδ).mp hx n
      have hb : min δ (1 / ((n + 1 : ℕ) : ℝ)) ≤ 1 := by
        apply (min_le_right _ _).trans
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      obtain ⟨s, hsD, hs0, hsm, hneg⟩ :=
        (sdp_window_negative_interval_iff_dense D hD x hb).mp hn
      exact Set.mem_iUnion.mpr
        ⟨⟨s, hsD, hs0, hsm.trans_le (min_le_left _ _)⟩,
          hsm.trans_le (min_le_right _ _), hneg⟩
    · intro hx n
      obtain ⟨s, hsn, hneg⟩ := Set.mem_iUnion.mp (hx n)
      exact ⟨s.1, s.2.2.1, hsn, hneg⟩
  rw [heq]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun s =>
    MeasurableSet.inter (MeasurableSet.const _) ((hm s) measurableSet_Iio)))

private theorem germ_dense_of_countable_compl
    (S : Set (J1Window 1)) (hS : Sᶜ.Countable) : Dense S := by
  rw [Metric.dense_iff]
  intro x r hr
  let a : ℝ := max 0 ((x : ℝ) - r / 2)
  let b : ℝ := min 1 ((x : ℝ) + r / 2)
  have hab : a < b := by
    dsimp [a, b]
    exact max_lt (lt_min (by norm_num) (by linarith [x.property.1]))
      (lt_min (by linarith [x.property.2]) (by linarith))
  let B : Set ℝ := Subtype.val '' Sᶜ
  have hB : B.Countable := hS.image Subtype.val
  have hnot : ¬ Set.Ioo a b ⊆ B := by
    intro hsub
    exact (not_le_of_gt hab)
      (Cardinal.Real.Ioo_countable_iff.mp (hB.mono hsub))
  obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hnot
  let z : J1Window 1 :=
    ⟨y, (le_max_left _ _).trans hy.1.le, hy.2.le.trans (min_le_left _ _)⟩
  refine ⟨z, ?_, ?_⟩
  · change |y - (x : ℝ)| < r
    have hlo := (le_max_right 0 ((x : ℝ) - r / 2)).trans_lt hy.1
    have hhi := hy.2.trans_le (min_le_right 1 ((x : ℝ) + r / 2))
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · by_contra hz
    exact hyB ⟨z, hz, rfl⟩

/-- Helper toward Lemma 7.12; not a paper result.
A countable dense set of good finite-grid times detects the negative germ before -/
theorem sdp_window_limit_negative_germ_good_times
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ D : Set (J1Window 1), D.Countable ∧ Dense D ∧
      (∀ (m : ℕ) (t : Fin (m + 1) → J1Window 1),
        Monotone t → (∀ i, t i ∈ D) →
          iIndepFun (fun (i : Fin m) (x : J1WindowD 1 (by norm_num)) =>
            x.path.1 (t i.succ) - x.path.1 (t i.castSucc)) (ν : Measure _)) ∧
      ∀ δ : ℝ, 0 < δ →
        MeasurableSet[⨆ s : {s : J1Window 1 // s ∈ D ∧ 0 < (s : ℝ) ∧ (s : ℝ) < δ},
          MeasurableSpace.comap (fun x : J1WindowD 1 (by norm_num) => x.path.1 s.1)
            inferInstance]
          {x : J1WindowD 1 (by norm_num) |
            ∀ n : ℕ, ∃ s : J1Window 1,
              0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} := by
  obtain ⟨S, hS, hgrid⟩ := sdp_window_limit_path_indep_increments hind hsym hν
  obtain ⟨D, hDS, hDc, hDd⟩ :=
    (germ_dense_of_countable_compl S hS).exists_countable_dense_subset
  refine ⟨D, hDc, hDd, ?_, ?_⟩
  · intro m t ht htD
    exact hgrid m t ht (fun i => hDS (htD i))
  · intro δ hδ
    exact sdp_window_negative_germ_measurable_early D hDc hDd hδ

/-- Helper toward Lemma 7.12; not a paper result.
Every SDP window limit starts at zero almost surely. -/
theorem sdp_window_limit_zero_ae
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∀ᵐ x ∂(ν : Measure (J1WindowD 1 (by norm_num))),
      x.path.1 ⟨0, by norm_num⟩ = 0 := by
  let e : J1WindowD 1 (by norm_num) → ℝ := fun x => x.path.1 ⟨0, by norm_num⟩
  let ρ : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩
  have he : Continuous e := continuous_j1WindowD_eval_zero (by norm_num)
  have hmap (n : ℕ) : (sdpBusemannWindowLaw n (by norm_num)).map e = ρ := by
    apply ProbabilityMeasure.toMeasure_injective
    have hm : Measurable (sdpBusemannWindow n (by norm_num : (0 : ℝ) < 1)) := by
      apply measurable_scaledPartialSumWindow
      intro j
      exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        ((measurable_busemannSDPMeasurableVersion _).sub
          (measurable_busemannSDPMeasurableVersion _))
    change (iidCodeMeasure.map (sdpBusemannWindow n
      (by norm_num : (0 : ℝ) < 1))).map e = Measure.dirac 0
    rw [Measure.map_map he.measurable hm]
    have hcomp : e ∘ sdpBusemannWindow n (by norm_num : (0 : ℝ) < 1) =
        fun _ => (0 : ℝ) := by
      funext ω
      dsimp [e, Function.comp_def]
      rw [sdpBusemannWindow_apply]
      simp [busemannSDPMeasurableVersion_zero]
    rw [hcomp, Measure.map_const, measure_univ, one_smul]
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num)) ν hν he
  have heq : ν.map e = ρ := tendsto_nhds_unique ht
    (by simpa only [hmap] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ)))
  have hmass : (ν : Measure _) {x | e x = 0} = 1 := by
    have hh := congrArg (fun p : ProbabilityMeasure ℝ => (p : Measure ℝ) {0}) heq
    rw [ProbabilityMeasure.map_apply' _ he.measurable.aemeasurable
      (measurableSet_singleton 0)] at hh
    have hset : e ⁻¹' {0} = {x | e x = 0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rw [hset] at hh
    change (ν : Measure _) {x | e x = 0} = (Measure.dirac (0 : ℝ)) {0} at hh
    simpa using hh
  have hmeas : MeasurableSet {x | e x = 0} := by
    have hset : e ⁻¹' {0} = {x | e x = 0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rw [← hset]
    exact he.measurable (measurableSet_singleton 0)
  exact (ae_iff_measure_eq hmeas.nullMeasurableSet).mpr
    (by simpa only [measure_univ] using hmass)

/-- Helper toward Lemma 7.12; not a paper result.
The reverse increments along any decreasing good-time sequence are jointly independent. -/
theorem sdp_window_limit_antitone_indep_increments
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ S : Set (J1Window 1), Sᶜ.Countable ∧
      ∀ s : ℕ → J1Window 1, Antitone s → (∀ n, s n ∈ S) →
        iIndepFun (fun n (x : J1WindowD 1 (by norm_num)) =>
          x.path.1 (s n) - x.path.1 (s (n + 1))) (ν : Measure _) := by
  classical
  obtain ⟨S, hS, hgrid⟩ := sdp_window_limit_path_indep_increments hind hsym hν
  refine ⟨S, hS, ?_⟩
  intro s hs hsS
  have hfin (m : ℕ) :
      iIndepFun (fun (i : Fin m) (x : J1WindowD 1 (by norm_num)) =>
        x.path.1 (s i.val) - x.path.1 (s (i.val + 1))) (ν : Measure _) := by
    let t : Fin (m + 1) → J1Window 1 := fun i => s (m - i.val)
    have htm : Monotone t := fun i j hij => hs (by change m - j.val ≤ m - i.val; omega)
    have hh := (hgrid m t htm (fun i => hsS _)).precomp
      (g := Fin.rev) (Fin.rev_injective)
    convert hh using 1
    funext i x
    dsimp [t]
    have ha : m - (m - (i.val + 1) + 1) = i.val := by omega
    have hb : m - (m - (i.val + 1)) = i.val + 1 := by omega
    rw [ha, hb]
  apply iIndepFun_iff_finset.mpr
  intro I
  obtain rfl | hI := I.eq_empty_or_nonempty
  · exact iIndepFun.of_subsingleton
  · let g (i : I) : Fin (I.max' hI + 1) :=
      ⟨i.1, Nat.lt_add_one_of_le (I.le_max' i.1 i.2)⟩
    exact (hfin (I.max' hI + 1)).precomp (g := g)
      (fun i j hij => Subtype.ext (congrArg Fin.val hij))

private theorem germ_tail_self_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : ProbabilityMeasure Ω)
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hXi : iIndepFun X ν.toMeasure) {A : Set Ω}
    (hA : ∀ n : ℕ, MeasurableSet[⨆ i ≥ n,
      MeasurableSpace.comap (X i) inferInstance] A) :
    IndepSet A A ν.toMeasure := by
  let m : ℕ → MeasurableSpace Ω := fun i =>
    MeasurableSpace.comap (X i) inferInstance
  let P : ℕ → MeasurableSpace Ω := fun n => ⨆ i < n, m i
  let T : MeasurableSpace Ω := ⨅ n : ℕ, ⨆ i ≥ n, m i
  let : MeasurableSpace Ω := mΩ
  have hm : ∀ i, m i ≤ mΩ := fun i => (hXm i).comap_le
  have hT : T ≤ mΩ :=
    (iInf_le _ 0).trans (iSup_le fun i => iSup_le fun _ => hm i)
  have hP : ∀ n, P n ≤ mΩ :=
    fun n => iSup_le fun i => iSup_le fun _ => hm i
  have hi (n : ℕ) : Indep (P n) T ν.toMeasure := by
    have hh := indep_iSup_of_disjoint hm hXi.iIndep
      (S := {i | i < n}) (T := {i | n ≤ i})
      (Set.disjoint_left.mpr (fun i hi hj =>
        (not_lt_of_ge (show n ≤ i from hj)) (show i < n from hi)))
    exact indep_of_indep_of_le_right hh (iInf_le _ n)
  have hmono : Monotone P := by
    intro n k hnk
    exact iSup_le fun i => iSup_le fun hin =>
      le_iSup_of_le i (le_iSup_of_le (lt_of_lt_of_le hin hnk) le_rfl)
  have hh := indep_iSup_of_monotone hi hP hT hmono
  have hTle : T ≤ ⨆ n, P n := by
    apply (iInf_le _ 0).trans
    refine iSup_le fun i => iSup_le fun _ => ?_
    exact le_iSup_of_le (i + 1)
      (le_iSup_of_le i (le_iSup_of_le (Nat.lt_succ_self i) le_rfl))
  exact (indep_of_indep_of_le_left hh hTle).indepSet_of_measurableSet
    (MeasurableSpace.measurableSet_iInf.mpr hA)
    (MeasurableSpace.measurableSet_iInf.mpr hA)

private theorem germ_centered_eval_measurable_tail
    (s : ℕ → J1Window 1) (hspos : ∀ n, 0 < (s n : ℝ))
    (hs : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 0))
    (n k : ℕ) (hnk : n ≤ k) :
    Measurable[⨆ i ≥ n, MeasurableSpace.comap
      (fun x : J1WindowD 1 (by norm_num) =>
        x.path.1 (s i) - x.path.1 (s (i + 1))) inferInstance]
      (fun x : J1WindowD 1 (by norm_num) =>
        x.path.1 (s k) - x.path.1 ⟨0, by norm_num⟩) := by
  let m : MeasurableSpace (J1WindowD 1 (by norm_num)) :=
    ⨆ i ≥ n, MeasurableSpace.comap
      (fun x : J1WindowD 1 (by norm_num) =>
        x.path.1 (s i) - x.path.1 (s (i + 1))) inferInstance
  have hm (i : ℕ) (hi : n ≤ i) :
      Measurable[m] (fun x => x.path.1 (s i) - x.path.1 (s (i + 1))) :=
    Measurable.of_comap_le (le_iSup_of_le i (le_iSup_of_le hi le_rfl))
  have hsum (j : ℕ) : Measurable[m]
      (fun x => x.path.1 (s k) - x.path.1 (s (k + j))) := by
    induction j with
    | zero => simpa only [Nat.add_zero, sub_self] using
        (measurable_const : Measurable[m] (fun _ => (0 : ℝ)))
    | succ j ih =>
      convert ih.add (hm (k + j) (by omega)) using 1
      funext x
      simp only [Nat.add_succ, Pi.add_apply]
      ring
  apply measurable_of_tendsto_metrizable hsum
  rw [tendsto_pi_nhds]
  intro x
  have hsk : Tendsto (fun j => s (k + j)) atTop
      (𝓝 (⟨0, by norm_num⟩ : J1Window 1)) := by
    apply tendsto_subtype_rng.mpr
    apply hs.comp
    convert tendsto_add_atTop_nat k using 1
    funext j
    exact Nat.add_comm _ _
  have hright : Tendsto (fun j => s (k + j)) atTop
      (𝓝[>] (⟨0, by norm_num⟩ : J1Window 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsk, Filter.Eventually.of_forall (fun j => hspos _)⟩
  exact tendsto_const_nhds.sub
    (Filter.Tendsto.comp (x.path.2.isRightContinuous _) hright)

private theorem germ_good_sequence
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    ∃ s : ℕ → J1Window 1, Antitone s ∧ (∀ n, 0 < (s n : ℝ)) ∧
      Tendsto (fun n => (s n : ℝ)) atTop (𝓝 0) ∧
      iIndepFun (fun n (x : J1WindowD 1 (by norm_num)) =>
        x.path.1 (s n) - x.path.1 (s (n + 1))) (ν : Measure _) ∧
      ∃ q : ℝ≥0∞, 0 < q ∧ ∀ n,
        (ν : Measure (J1WindowD 1 (by norm_num)))
          {x | x.path.1 (s n) < 0} = q := by
  classical
  obtain ⟨S, hS, hi⟩ := sdp_window_limit_antitone_indep_increments hind hsym hν
  obtain ⟨U, hU, q, hq, hmass⟩ :=
    sdp_window_limit_uniform_negative_mass hind hsym hν
  have hSU : (S ∩ U)ᶜ.Countable := by
    rw [Set.compl_inter]
    exact hS.union hU
  have hd := germ_dense_of_countable_compl (S ∩ U) hSU
  let V := {s : J1Window 1 // s ∈ S ∩ U ∧ 0 < (s : ℝ)}
  have hex (r : {r : ℝ // 0 < r}) : ∃ z : V, (z.1 : ℝ) < r.1 := by
    let b : J1Window 1 := ⟨min r.1 1, (lt_min r.2 (by norm_num)).le,
      min_le_right _ _⟩
    have hb : (⟨0, by norm_num⟩ : J1Window 1) < b :=
      lt_min r.2 (by norm_num)
    obtain ⟨z, hzSU, hz0, hzb⟩ := hd.exists_mem_open isOpen_Ioo
      (Set.nonempty_Ioo.mpr hb)
    have hzbR : (z : ℝ) < min r.1 1 := hzb
    exact ⟨⟨z, hzSU, hz0⟩, hzbR.trans_le (min_le_left _ _)⟩
  choose p hp using hex
  let z : ℕ → V := Nat.rec (p ⟨1, by norm_num⟩) (fun n w =>
    p ⟨min (w.1 : ℝ) (1 / ((n + 2 : ℕ) : ℝ)), lt_min w.2.2 (by positivity)⟩)
  let s : ℕ → J1Window 1 := fun n => (z n).1
  have hstep (n : ℕ) : (s (n + 1) : ℝ) <
      min (s n : ℝ) (1 / ((n + 2 : ℕ) : ℝ)) := hp _
  have hspos (n : ℕ) : 0 < (s n : ℝ) := (z n).2.2
  have hanti : Antitone s := antitone_nat_of_succ_le
    (fun n => ((hstep n).trans_le (min_le_left _ _)).le)
  have hbound (n : ℕ) : (s n : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    cases n with
    | zero =>
      change ((p ⟨1, by norm_num⟩).1 : ℝ) ≤ 1 / ((0 + 1 : ℕ) : ℝ)
      simpa only [Nat.zero_add, Nat.cast_one, div_one] using
        (hp ⟨1, by norm_num⟩).le
    | succ n => exact ((hstep n).trans_le (min_le_right _ _)).le
  have ht : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hspos n).le) hbound
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)))
  exact ⟨s, hanti, hspos, ht, hi s hanti (fun n => (z n).2.1.1), q, hq,
    fun n => hmass _ (z n).2.1.2 (hspos n)⟩

/-- Helper toward Lemma 7.12; not a paper result.
Every SDP window limit has negative values arbitrarily near zero almost surely. -/
theorem sdp_window_limit_negative_germ_eq_one
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    (ν : Measure (J1WindowD 1 (by norm_num))).real
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} = 1 := by
  classical
  obtain ⟨s, _, hspos, hs, hi, q, hq, hmass⟩ := germ_good_sequence hind hsym hν
  let X : ℕ → J1WindowD 1 (by norm_num) → ℝ := fun i x =>
    x.path.1 (s i) - x.path.1 (s (i + 1))
  let F : ℕ → J1WindowD 1 (by norm_num) → ℝ := fun k x =>
    x.path.1 (s k) - x.path.1 ⟨0, by norm_num⟩
  let A : Set (J1WindowD 1 (by norm_num)) :=
    {x | ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧ F k x < 0}
  have hXm (i : ℕ) : Measurable (X i) :=
    (measurable_j1WindowD_eval (by norm_num) _).sub
      (measurable_j1WindowD_eval (by norm_num) _)
  have hAtail (n : ℕ) : MeasurableSet[⨆ i ≥ n,
      MeasurableSpace.comap (X i) inferInstance] A := by
    have heq : A = ⋂ j : ℕ, ⋃ k : {k : ℕ // max j n ≤ k}, {x | F k.1 x < 0} := by
      ext x
      simp only [A, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
      constructor
      · intro hx j
        obtain ⟨k, hk, hneg⟩ := hx (max j n)
        exact ⟨⟨k, hk⟩, hneg⟩
      · intro hx j
        obtain ⟨k, hneg⟩ := hx j
        exact ⟨k.1, (le_max_left _ _).trans k.2, hneg⟩
    rw [heq]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iUnion (fun k =>
      (germ_centered_eval_measurable_tail s hspos hs n k.1
        ((le_max_right _ _).trans k.2)) measurableSet_Iio))
  have hAm : MeasurableSet A := by
    have hle : (⨆ i ≥ (0 : ℕ), MeasurableSpace.comap (X i) inferInstance) ≤
        (inferInstance : MeasurableSpace (J1WindowD 1 (by norm_num))) :=
      iSup_le fun i => iSup_le fun _ => (hXm i).comap_le
    exact hle _ (hAtail 0)
  have hself : IndepSet A A (ν : Measure _) :=
    germ_tail_self_indep ν X hXm hi hAtail
  let V : ℕ → Set (J1WindowD 1 (by norm_num)) := fun n =>
    {x | ∃ k : ℕ, n ≤ k ∧ x.path.1 (s k) < 0}
  have hVm (n : ℕ) : MeasurableSet (V n) := by
    have heq : V n = ⋃ k : ℕ,
        {x : J1WindowD 1 (by norm_num) | n ≤ k ∧ x.path.1 (s k) < 0} := by
      ext x
      simp only [V, Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [heq]
    exact MeasurableSet.iUnion (fun k => (MeasurableSet.const _).inter
      ((measurable_j1WindowD_eval (by norm_num) _) measurableSet_Iio))
  have hVanti : Antitone V := by
    intro n m hnm x hx
    obtain ⟨k, hmk, hneg⟩ := hx
    exact ⟨k, hnm.trans hmk, hneg⟩
  have hVbound (n : ℕ) : q ≤ (ν : Measure _) (V n) := by
    rw [← hmass n]
    exact measure_mono (fun x hx => ⟨n, le_rfl, hx⟩)
  have hBpos : 0 < (ν : Measure _) (⋂ n, V n) := by
    rw [hVanti.measure_iInter (fun n => (hVm n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    exact hq.trans_le (le_iInf hVbound)
  have hAB : A =ᵐ[(ν : Measure _)] (⋂ n, V n) := by
    filter_upwards [sdp_window_limit_zero_ae hν] with x hx
    simp only [A, F, Set.mem_ofPred_eq, Set.mem_iInter, V, hx, sub_zero]
  have hApos : 0 < (ν : Measure _).real A := by
    rw [measureReal_def, measure_congr hAB]
    exact ENNReal.toReal_pos hBpos.ne' (measure_ne_top _ _)
  have hmul := hself.measure_inter_eq_mul
  have hreal : (ν : Measure _).real A = ((ν : Measure _).real A) ^ 2 := by
    have hh := congrArg ENNReal.toReal hmul
    simpa only [Set.inter_self, ENNReal.toReal_mul, measureReal_def, pow_two] using hh
  have hAone : (ν : Measure _).real A = 1 := by
    have hle : (ν : Measure _).real A ≤ 1 := measureReal_le_one
    nlinarith
  have hsub : (⋂ n, V n) ⊆
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ t : J1Window 1,
          0 < (t : ℝ) ∧ (t : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 t < 0} := by
    intro x hx n
    have hn : 0 < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually (gt_mem_nhds hn))
    obtain ⟨k, hk, hneg⟩ := (Set.mem_iInter.mp hx) N
    exact ⟨s k, hspos k, hN k hk, hneg⟩
  apply le_antisymm measureReal_le_one
  calc
    1 = (ν : Measure _).real (⋂ n, V n) := by
      rw [← measureReal_congr hAB, hAone]
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

/-- Helper toward Lemma 7.12; not a paper result.
The negative germ event of every SDP window limit is independent of itself. -/
theorem sdp_window_limit_negative_germ_self_indep
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    IndepSet
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0}
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0}
      (ν : Measure (J1WindowD 1 (by norm_num))) := by
  apply (indepSet_iff_measure_inter_eq_mul sdp_window_negative_germ_measurableSet
    sdp_window_negative_germ_measurableSet (ν : Measure _)).mpr
  rw [Set.inter_self]
  have hh := sdp_window_limit_negative_germ_eq_one hind hsym hν
  have he : (ν : Measure (J1WindowD 1 (by norm_num)))
      {x : J1WindowD 1 (by norm_num) |
        ∀ n : ℕ, ∃ s : J1Window 1,
          0 < (s : ℝ) ∧ (s : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) ∧ x.path.1 s < 0} = 1 :=
    (ENNReal.toReal_eq_one_iff _).mp hh
  rw [he, mul_one]

/-- Helper toward Lemma 7.12; not a paper result.
Every SDP window limit has a negative value in the open unit interval almost surely. -/
theorem sdp_window_limit_negative_excursion_eq_one
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))
    {ν : ProbabilityMeasure (J1WindowD 1 (by norm_num))}
    (hν : Tendsto (fun k : ℕ => sdpBusemannWindowLaw k (by norm_num))
      atTop (𝓝 ν)) :
    (ν : Measure (J1WindowD 1 (by norm_num)))
      {x : J1WindowD 1 (by norm_num) |
        ∃ s : J1Window 1, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ x.path.1 s < 0} = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  exact sdp_window_negative_excursion_eq_one_of_germ_eq_one ν
    (sdp_window_limit_negative_germ_eq_one hind hsym hν)

/-- Helper toward Lemma 7.12; not a paper result.
The negative-excursion premise used by the Section 7 transfer assembly follows from -/
theorem sdp_window_limit_negative_excursion_producer
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment Y j ω) μ)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω)) :
    DirectedDistances.PaperProofs.Section7.SDPWindowLimitNegativeExcursion := by
  exact sdp_window_negative_threshold_of_zero_excursion
    (fun _ hν => sdp_window_limit_negative_excursion_eq_one hind hsym hν)

end DirectedDistances.Recursive
