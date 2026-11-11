/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitReduction2
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau

/- # The conditional local-limit law toward Proposition 3.9

pseudo-emetric topology of the geometric class distance (Definition 3.8).
Global countability of geometric ball classes is not assumed: the limiting
law has a separable support supplied by the finite-window representatives.
DC retains exactly its deterministic definition in `UIBOTLocalLimitReduction`. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter Set
open scoped Topology ENNReal

local instance : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

private theorem ball_subset {x y : D39GeomRootedMapClass.{0}} {a b : ℝ≥0∞}
    (hxy : x ∈ Metric.eball y b) (hab : a ≤ b) :
    Metric.eball x a ⊆ Metric.eball y b := by
  intro z hz
  exact (d39ClassDistance_ultrametric z x y).trans_lt
    (max_lt (lt_of_lt_of_le hz hab) hxy)

private def ballFamily : Set (Set D39GeomRootedMapClass.{0}) :=
  {s | ∃ (x : D39GeomRootedMapClass.{0}) (r : ℕ), s = Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r)}

private theorem ballFamily_pi : IsPiSystem ballFamily := by
  rintro s ⟨x, r, rfl⟩ t ⟨y, q, rfl⟩ ⟨z, hz, hz'⟩
  change edist z x < _ at hz
  change edist z y < _ at hz'
  rcases le_total ((1 / 2 : ℝ≥0∞) ^ r) ((1 / 2 : ℝ≥0∞) ^ q) with h | h
  · have hxy : x ∈ Metric.eball y ((1 / 2 : ℝ≥0∞) ^ q) :=
      (d39ClassDistance_ultrametric x z y).trans_lt
        (max_lt (lt_of_lt_of_le (by change edist x z < _; rw [edist_comm]; exact hz) h) hz')
    exact ⟨x, r, inter_eq_left.mpr (ball_subset hxy h)⟩
  · have hyx : y ∈ Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r) :=
      (d39ClassDistance_ultrametric y z x).trans_lt
        (max_lt (lt_of_lt_of_le (by change edist y z < _; rw [edist_comm]; exact hz') h) hz)
    exact ⟨y, q, inter_eq_right.mpr (ball_subset hyx h)⟩

private theorem ballFamily_measurable (s) (hs : s ∈ ballFamily) : MeasurableSet s := by
  obtain ⟨x, r, rfl⟩ := hs
  exact Metric.isOpen_eball.measurableSet

private theorem open_mem_ball_cover (S : Set D39GeomRootedMapClass.{0})
    {G : Set D39GeomRootedMapClass.{0}} (hG : IsOpen G)
    {x : D39GeomRootedMapClass.{0}} (hx : x ∈ closure S) (hxG : x ∈ G) :
    ∃ c ∈ S, ∃ r : ℕ, x ∈ Metric.eball c ((1 / 2 : ℝ≥0∞) ^ r) ∧
      Metric.eball c ((1 / 2 : ℝ≥0∞) ^ r) ⊆ G := by
  obtain ⟨ε, hε, hεG⟩ := EMetric.isOpen_iff.mp hG x hxG
  obtain ⟨r, hr⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt hε)
  have hr' : (1 / 2 : ℝ≥0∞) ^ r < ε := by simpa only [one_div] using hr
  have hp : 0 < (1 / 2 : ℝ≥0∞) ^ r := bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))
  obtain ⟨c, hc, hxc⟩ := EMetric.mem_closure_iff.mp hx _ hp
  refine ⟨c, hc, r, hxc, ?_⟩
  apply Subset.trans (ball_subset (by change edist c x < _; rw [edist_comm]; exact hxc) le_rfl)
  exact (Metric.eball_subset_eball hr'.le).trans hεG

private theorem weak_of_ball_masses
    (μ : ℕ → ProbabilityMeasure D39GeomRootedMapClass.{0})
    (ν : ProbabilityMeasure D39GeomRootedMapClass.{0})
    (S : Set D39GeomRootedMapClass.{0}) (hS : S.Countable)
    (hsupport : ∀ᵐ x ∂(ν : Measure D39GeomRootedMapClass.{0}), x ∈ closure S)
    (hball : ∀ s ∈ ballFamily, Tendsto (fun k => μ k s) atTop (𝓝 (ν s))) :
    Tendsto μ atTop (𝓝 ν) := by
  classical
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  apply (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 1) atTop (by simp))
    (by isBoundedDefault)).2
  intro a ha
  let T : Set (Set D39GeomRootedMapClass.{0}) :=
    {s | s ∈ ballFamily ∧ s ⊆ G ∧ ∃ c ∈ S, ∃ r : ℕ,
      s = Metric.eball c ((1 / 2 : ℝ≥0∞) ^ r)}
  have hTc : T.Countable := by
    apply ((hS.prod (Set.countable_univ : (Set.univ : Set ℕ).Countable)).image
      (fun p : D39GeomRootedMapClass.{0} × ℕ => Metric.eball p.1 ((1 / 2 : ℝ≥0∞) ^ p.2))).mono
    rintro s ⟨_, _, c, hc, r, rfl⟩
    exact ⟨(c, r), ⟨hc, mem_univ _⟩, rfl⟩
  have hcover : G =ᵐ[(ν : Measure D39GeomRootedMapClass.{0})] ⋃ s ∈ T, s := by
    filter_upwards [hsupport] with x hx
    apply propext
    constructor
    · intro hxG
      obtain ⟨c, hc, r, hxr, hsub⟩ := open_mem_ball_cover S hG hx hxG
      exact mem_iUnion₂.mpr ⟨_, ⟨⟨c, r, rfl⟩, hsub, c, hc, r, rfl⟩, hxr⟩
    · intro hxT
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hxT
      exact hs.2.1 hxs
  have heq : ν G = ν (⋃ s ∈ T, s) := by
    apply ENNReal.coe_injective
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using measure_congr hcover
  have hTne : T.Nonempty := by
    by_contra h
    have hT : T = ∅ := not_nonempty_iff_eq_empty.mp h
    simp only [hT, mem_empty_iff_false, iUnion_of_empty, iUnion_empty,
      ProbabilityMeasure.coeFn_empty] at heq
    rw [heq] at ha
    exact not_lt_of_ge bot_le ha
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  have hGlim : Tendsto (fun n => ν (accumulate f n)) atTop (𝓝 (ν G)) := by
    have ht : Tendsto (fun n => ν (accumulate f n)) atTop (𝓝 (ν (⋃ n, f n))) :=
      (ENNReal.tendsto_toNNReal_iff (by simp) (by simp)).2 tendsto_measure_iUnion_accumulate
    have hu : (⋃ n, f n) = ⋃ s ∈ T, s := by rw [hf, biUnion_range]
    rwa [hu, ← heq] at ht
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hGlim).1 a ha).exists
  let t := (Finset.range (n + 1)).image f
  have ht : ∀ s ∈ t, s ∈ ballFamily := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact (hf ▸ mem_range_self i : f i ∈ T).1
  have hfinite := ballFamily_pi.tendsto_probabilityMeasure_biUnion ht
    ballFamily_measurable hball
  have hn' : a < ν (⋃ s ∈ t, s) := by
    simpa only [t, Finset.set_biUnion_finset_image, accumulate_def,
      Finset.mem_range, Nat.lt_succ_iff] using hn
  filter_upwards [(tendsto_order.1 hfinite).1 a hn'] with k hk
  apply hk.trans_le
  apply ProbabilityMeasure.apply_mono
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
  exact (hf ▸ mem_range_self i : f i ∈ T).2.1 hxs

private def windowClasses : Set D39GeomRootedMapClass.{0} :=
  range (fun p : (Σ N : ℕ, Fin (2 * N) → Fin 3) =>
    Quotient.mk d39DomainSetoid (uibotWindowRepresentative p.1 p.2))

private theorem ae_mem_closure_windowClasses (DC : UIBOTDeterministicComparison) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      uibotMeasurableWholePlaneClassMap DC W ∈ closure windowClasses := by
  have heq : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N r : ℕ,
      UIBOTRootWindowCapture (shiftedStream W N) N (r + 1) →
      d39GeomBallClassMap r (uibotMeasurableWholePlaneClassMap DC W) =
        Quotient.mk (d39GeomBallClassSetoid r)
          (uibotWindowRepresentative N (fun i => shiftedStream W N i.val)) := by
    exact ae_all_iff.mpr (fun N => ae_all_iff.mpr
      (fun r => uibotMeasurableWholePlaneClassMap_ae_window DC N r))
  filter_upwards [heq, wholePlaneIID_ae_eventual_uibotRootWindowCapture] with W hW hcap
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨r, hr⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt hε)
  obtain ⟨N, hN⟩ := hcap (r + 1)
  refine ⟨Quotient.mk d39DomainSetoid
    (uibotWindowRepresentative N (fun i => shiftedStream W N i.val)),
    ⟨⟨N, (fun i => shiftedStream W N i.val)⟩, rfl⟩, ?_⟩
  have hm : Quotient.mk d39DomainSetoid
      (uibotWindowRepresentative N (fun i => shiftedStream W N i.val)) ∈
      Metric.eball (uibotMeasurableWholePlaneClassMap DC W) ((1 / 2 : ℝ≥0∞) ^ r) := by
    rw [d39GeomClass_openBall_eq_ballClass]
    change d39GeomBallClassMap r _ = d39GeomBallClassMap r _
    rw [d39GeomBallClassMap_mk]
    exact hW N r (hN N le_rfl)
  change edist _ _ < _ at hm
  rw [edist_comm] at hm
  exact hm.trans (by simpa only [one_div] using hr)

/-- Helper toward Proposition 3.9: the pushforward of the uniform finite
map and independent uniform all-edge root to the geometric local class space. -/
@[expose] def uibotFiniteGeometricProbabilityLaw
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    ProbabilityMeasure D39GeomRootedMapClass.{0} := by
  let : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
  let : MeasurableSpace (Fin n) := ⊤
  exact ProbabilityMeasure.map (⟨uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne,
    uibotFiniteUniformSampleLaw_probability ℓ ρ n hℓ hρ hn hne⟩ : ProbabilityMeasure _)
      (uibotFiniteGeometricClassMap ℓ ρ n hℓ hρ hn hne)

/-- Helper toward Proposition 3.9: the law of the measurable whole-plane
iid KMSW geometric class, conditional on the deterministic comparison DC. -/
@[expose] def uibotWholePlaneGeometricProbabilityLaw (DC : UIBOTDeterministicComparison) :
    ProbabilityMeasure D39GeomRootedMapClass.{0} :=
  ProbabilityMeasure.map (⟨wholePlaneIIDCodeMeasure, inferInstance⟩ : ProbabilityMeasure _)
    (uibotMeasurableWholePlaneClassMap DC)

/- Helper toward Proposition 3.9: along every diverging admissible size
sequence with fixed positive boundary lengths, the actual finite-map
pushforwards converge weakly for the geometric local topology to the iid -/
theorem uibotFiniteGeometricProbabilityLaw_tendsto_of_comparison
    (DC : UIBOTDeterministicComparison)
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) :
    Tendsto (fun k => uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k)
      hℓ hρ (hsize k) (hne k)) atTop
      (𝓝 (uibotWholePlaneGeometricProbabilityLaw DC)) := by
  apply weak_of_ball_masses _ _ windowClasses (countable_range _) ?_ ?_
  · exact (ae_map_iff (measurable_uibotMeasurableWholePlaneClassMap DC).aemeasurable
      isClosed_closure.measurableSet).mpr (ae_mem_closure_windowClasses DC)
  · rintro s ⟨x, r, rfl⟩
    have hevent : Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r) =
        {y | d39GeomBallClassMap r y = d39GeomBallClassMap r x} := by
      rw [d39GeomClass_openBall_eq_ballClass]
      ext y
      exact eq_comm
    have hfinite (k : ℕ) :
        uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k)
          (Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r)) =
        ((uibotFiniteUniformSampleLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k))
          {p | d39GeomBallClassMap r
            (uibotFiniteGeometricClassMap ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) p) =
              d39GeomBallClassMap r x}).toNNReal := by
      let : MeasurableSpace (KMSWMapIsoClass ℓ ρ (ns k)) := ⊤
      let : MeasurableSpace (Fin (ns k)) := ⊤
      let := uibotFiniteMapFintype ℓ ρ (ns k) (hsize k)
      change ((uibotFiniteUniformSampleLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k)).map
        (uibotFiniteGeometricClassMap ℓ ρ (ns k) hℓ hρ (hsize k) (hne k))
        (Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r))).toNNReal = _
      rw [Measure.map_apply (measurable_of_countable _) Metric.isOpen_eball.measurableSet, hevent]
      rfl
    have hwhole : uibotWholePlaneGeometricProbabilityLaw DC
        (Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r)) =
        (wholePlaneIIDCodeMeasure {W | d39GeomBallClassMap r
          (uibotMeasurableWholePlaneClassMap DC W) = d39GeomBallClassMap r x}).toNNReal := by
      change (wholePlaneIIDCodeMeasure.map (uibotMeasurableWholePlaneClassMap DC)
        (Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r))).toNNReal = _
      rw [Measure.map_apply (measurable_uibotMeasurableWholePlaneClassMap DC)
        Metric.isOpen_eball.measurableSet, hevent]
      rfl
    simp_rw [hfinite, hwhole]
    apply (ENNReal.tendsto_toNNReal_iff (by finiteness) (by
      intro k
      let : MeasurableSpace (KMSWMapIsoClass ℓ ρ (ns k)) := ⊤
      let : MeasurableSpace (Fin (ns k)) := ⊤
      let := uibotFiniteUniformSampleLaw_probability ℓ ρ (ns k) hℓ hρ (hsize k) (hne k)
      exact measure_ne_top _ _)).2
    exact uibotMeasurableGeometricBallLaw_tendsto_of_comparison
      DC ℓ ρ hℓ hρ ns hns hsize hne r (d39GeomBallClassMap r x)





theorem uibotGeometricLocalLimit_eq_iidPushforward_of_comparison
    (DC : UIBOTDeterministicComparison)
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) :
    letI : Nonempty (ProbabilityMeasure D39GeomRootedMapClass.{0}) :=
      ⟨uibotWholePlaneGeometricProbabilityLaw DC⟩
    ((limUnder atTop (fun k => uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k)
        hℓ hρ (hsize k) (hne k)) : ProbabilityMeasure D39GeomRootedMapClass.{0}) :
          Measure D39GeomRootedMapClass.{0}) =
      wholePlaneIIDCodeMeasure.map (uibotMeasurableWholePlaneClassMap DC) := by
  let : Nonempty (ProbabilityMeasure D39GeomRootedMapClass.{0}) :=
    ⟨uibotWholePlaneGeometricProbabilityLaw DC⟩
  have h := (uibotFiniteGeometricProbabilityLaw_tendsto_of_comparison
    DC ℓ ρ hℓ hρ ns hns hsize hne).limUnder_eq
  exact congrArg ProbabilityMeasure.toMeasure h



















end DirectedDistances.PaperProofs.Section3

end
