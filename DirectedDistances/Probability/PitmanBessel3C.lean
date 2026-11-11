/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.BrownianPathMeasure4

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/

/-! Helper toward Lemma 4.11: scalar path-law determination and exact Gaussian
finite-dimensional laws of the radial process. The reflection/Pitman identity
is not assumed in any theorem below. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Set Function TopologicalSpace
open DirectedDistances.RandomWalk
open Filter
open scoped NNReal Topology

local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: finite restrictions determine a scalar continuous-path measure. -/
theorem continuousScalarPath_measure_ext_of_finset
    (μ ν : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfdd : ∀ I : Finset ℝ≥0,
      μ.map (fun f => I.restrict (fun t => f t)) =
        ν.map (fun f => I.restrict (fun t => f t))) : μ = ν := by
  classical
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ℝ≥0
  let : Countable D := hDc.to_subtype
  let ev : C(ℝ≥0, ℝ) → D → ℝ := fun f t => f t
  have hevc : Continuous ev := continuous_pi (fun t => continuous_eval_const t.val)
  have hev : MeasurableEmbedding ev := hevc.measurableEmbedding (by
    intro f g h
    apply DFunLike.ext'
    apply f.continuous.ext_on hDd g.continuous
    intro t ht
    exact congrFun h ⟨t, ht⟩)
  apply hev.map_injective
  have hproj (I : Finset D) :
      (μ.map ev).map I.restrict = (ν.map ev).map I.restrict := by
    let J : Finset ℝ≥0 := I.image Subtype.val
    have hi (i : I) : i.val.val ∈ J := Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩
    let r : (J → ℝ) → I → ℝ := fun v i => v ⟨i.val.val, hi i⟩
    have hr : Measurable r := measurable_pi_iff.mpr (fun i => measurable_pi_apply _)
    have h := congrArg (Measure.map r) (hfdd J)
    have hm : Measurable (fun f : C(ℝ≥0, ℝ) => J.restrict (fun t => f t)) :=
      (continuous_pi (fun i : J => continuous_eval_const i.val)).measurable
    rw [Measure.map_map hr hm, Measure.map_map hr hm] at h
    have hI : Measurable (I.restrict : (D → ℝ) → I → ℝ) :=
      measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)
    rw [Measure.map_map hI hev.measurable, Measure.map_map hI hev.measurable]
    exact h
  exact IsProjectiveLimit.unique (P := fun I => (μ.map ev).map I.restrict)
    (fun I => rfl) (fun I => (hproj I).symm)

/-- Helper toward Lemma 4.11: the scalar Brownian law on continuous paths is unique,
without assuming that such a measure exists. -/
theorem brownianScalarPath_measure_unique (μ ν : Measure C(ℝ≥0, ℝ))
    (hμ : IsBrownianReal (fun t (p : C(ℝ≥0, ℝ)) => p t) μ)
    (hν : IsBrownianReal (fun t (p : C(ℝ≥0, ℝ)) => p t) ν) : μ = ν := by
  let : IsProbabilityMeasure μ := (hμ.hasLaw_eval 0).isProbabilityMeasure
  let : IsProbabilityMeasure ν := (hν.hasLaw_eval 0).isProbabilityMeasure
  apply continuousScalarPath_measure_ext_of_finset
  intro I
  exact (hμ.hasLaw I).map_eq.trans (hν.hasLaw I).map_eq.symm

/-- Helper toward Lemma 4.11: the exact joint Gaussian law of the first three
coordinates at an arbitrary finite set of times. -/
theorem firstThree_hasLaw_restrict
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (I : Finset ℝ≥0) :
    HasLaw (fun p (i : Fin 3) (t : I) => p t i.castSucc)
      (Measure.pi (fun _ : Fin 3 => BrownianReal.projectiveFamily I)) W₄ := by
  have hm (i : Fin 3) : Measurable
      (fun p : C(ℝ≥0, Fin 4 → ℝ) => fun t : I => p t i.castSucc) := by
    apply measurable_pi_iff.mpr
    intro t
    exact (measurable_pi_apply i.castSucc).comp (continuous_eval_const t.val).measurable
  have hi := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) => I.restrict (fun t => f t))
    (fun _ => (continuous_pi (fun t : I => continuous_eval_const t.val)).measurable)
  refine ⟨(measurable_pi_iff.mpr hm).aemeasurable, ?_⟩
  rw [hi.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  congr 1
  funext i
  exact (hB i.castSucc).hasLaw I |>.map_eq

/-- Helper toward Lemma 4.11: all radial finite-dimensional laws are explicit
pushforwards of three independent Brownian Gaussian finite-dimensional laws. -/
theorem radial3_hasLaw_restrict
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (I : Finset ℝ≥0) :
    HasLaw (fun p (t : I) => radial3Path (firstThreePath p) t)
      ((Measure.pi (fun _ : Fin 3 => BrownianReal.projectiveFamily I)).map
        (fun x (t : I) => Real.sqrt ((x 0 t)^2 + (x 1 t)^2 + (x 2 t)^2))) W₄ := by
  have hm : Measurable (fun (x : Fin 3 → I → ℝ) (t : I) =>
      Real.sqrt ((x 0 t)^2 + (x 1 t)^2 + (x 2 t)^2)) := by fun_prop
  exact (hasLaw_map hm.aemeasurable).comp (firstThree_hasLaw_restrict W₄ hB hI I)

/-- Helper toward Lemma 4.11: continuous-path-valued Brownian processes have
the same whole-path distribution, on possibly different probability spaces. -/
theorem brownianScalarPath_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : Ω → C(ℝ≥0, ℝ)} {Y : Ω' → C(ℝ≥0, ℝ)}
    (hX : Measurable X) (hY : Measurable Y)
    (hBX : IsBrownianReal (fun t ω => X ω t) P)
    (hBY : IsBrownianReal (fun t ω => Y ω t) Q) :
    IdentDistrib X Y P Q := by
  refine ⟨hX.aemeasurable, hY.aemeasurable, ?_⟩
  apply continuousScalarPath_measure_ext_of_finset
  intro I
  have hm : Measurable (fun f : C(ℝ≥0, ℝ) => I.restrict (fun t => f t)) :=
    (continuous_pi (fun t : I => continuous_eval_const t.val)).measurable
  rw [Measure.map_map hm hX, Measure.map_map hm hY]
  exact (hBX.hasLaw I).map_eq.trans (hBY.hasLaw I).map_eq.symm

/-- Helper toward Lemma 4.11: the minimum and maximum versions of the scalar
Pitman transform have identical entire-path laws by Brownian sign symmetry.
This does not identify either law with the BES(3) law. -/
theorem scalarPitman_neg_identDistrib
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t 0) W₄) :
    IdentDistrib (fun p => scalarPitman (-pathCoordinate p 0))
      (fun p => scalarPitman (pathCoordinate p 0)) W₄ W₄ := by
  have h := brownianScalarPath_identDistrib
    ((continuous_pathCoordinate 0).neg.measurable)
    (continuous_pathCoordinate 0).measurable hB.neg hB
  exact h.comp continuous_scalarPitman.measurable

/-- Helper toward Lemma 4.11: the sign-reversed minimum transform is literally
the classical `2 M - B` expression, with maximum over the closed time interval. -/
theorem scalarPitman_neg_apply (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    scalarPitman (-f) t = 2 * sSup (f '' Set.Icc 0 t) - f t := by
  have he : (fun s => (-f) s) '' Set.Icc 0 t = -(f '' Set.Icc 0 t) := by
    ext x
    simp only [Set.mem_image, Set.mem_neg, ContinuousMap.neg_apply]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simp only [neg_neg]⟩
    · rintro ⟨s, hs, he⟩
      exact ⟨s, hs, by rw [he, neg_neg]⟩
  change -f t - 2 * sInf ((fun s => (-f) s) '' Set.Icc 0 t) = _
  rw [he, Real.sInf_neg]
  ring

/-- Helper toward Lemma 4.11: the Pitman statistic on a finite set of times,
with its endpoint explicitly included in that set. -/
@[expose] noncomputable def finitePitmanStatistic (I : Finset ℝ≥0) (t : I)
    (x : I → ℝ) : ℝ :=
  x t - 2 * Finset.univ.inf' ⟨t, Finset.mem_univ t⟩ x

/-- Helper toward Lemma 4.11: every finite Pitman statistic is continuous. -/
theorem continuous_finitePitmanStatistic (I : Finset ℝ≥0) (t : I) :
    Continuous (finitePitmanStatistic I t) := by
  exact (continuous_apply t).sub (continuous_const.mul
    (Continuous.finset_inf'_apply ⟨t, Finset.mem_univ t⟩
      (fun i _ => continuous_apply i)))

/-- Helper toward Lemma 4.11: the finite Pitman statistic has an explicit
Gaussian pushforward law. No reflection principle is used or assumed. -/
theorem finitePitmanStatistic_hasLaw
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t 0) W₄)
    (I : Finset ℝ≥0) (t : I) :
    HasLaw (fun p => finitePitmanStatistic I t (fun s => p s 0))
      ((BrownianReal.projectiveFamily I).map (finitePitmanStatistic I t)) W₄ :=
  (hasLaw_map (continuous_finitePitmanStatistic I t).measurable.aemeasurable).comp
    (hB.hasLaw I)

/-- Helper toward Lemma 4.11: a finite sample of a prescribed dense sequence
in the initial interval, including the endpoint. -/
@[expose] noncomputable def pitmanSampleTimes (t : ℝ≥0)
    (q : ℕ → Set.Icc (0 : ℝ≥0) t) (n : ℕ) : Finset ℝ≥0 :=
  insert t ((Finset.range (n + 1)).image (fun k => (q k).val))

/-- Helper toward Lemma 4.11: the endpoint belongs to every finite sample. -/
theorem mem_pitmanSampleTimes (t : ℝ≥0) (q : ℕ → Set.Icc (0 : ℝ≥0) t) (n : ℕ) :
    t ∈ pitmanSampleTimes t q n := Finset.mem_insert_self _ _

/-- Helper toward Lemma 4.11: finite sampled minima recover the entire-path
Pitman evaluation along any dense sequence in the closed initial interval. -/
theorem finitePitmanStatistic_tendsto (f : C(ℝ≥0, ℝ)) (t : ℝ≥0)
    (q : ℕ → Set.Icc (0 : ℝ≥0) t) (hq : DenseRange q) :
    Tendsto (fun n => finitePitmanStatistic (pitmanSampleTimes t q n)
      ⟨t, mem_pitmanSampleTimes t q n⟩ (fun s => f s)) atTop
      (𝓝 (scalarPitman f t)) := by
  classical
  let m (n : ℕ) : ℝ := Finset.univ.inf'
    ⟨(⟨t, mem_pitmanSampleTimes t q n⟩ : pitmanSampleTimes t q n), Finset.mem_univ _⟩
    (fun s => f s)
  obtain ⟨u, hu, hmu, hmin⟩ := continuousRunningMinimum_exists_eq_and_le f t
  have hmem (n : ℕ) (s : pitmanSampleTimes t q n) : s.val ∈ Set.Icc 0 t := by
    have hs := s.property
    change s.val ∈ insert t ((Finset.range (n + 1)).image (fun k => (q k).val)) at hs
    rcases Finset.mem_insert.mp hs with hs | hs
    · rw [hs]
      exact ⟨zero_le, le_rfl⟩
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hs
      exact hk ▸ (q k).property
  have hm : Tendsto m atTop (𝓝 (continuousRunningMinimum f t)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      apply Filter.Eventually.of_forall
      intro n
      apply lt_of_lt_of_le ha
      rw [hmu]
      exact Finset.le_inf' _ _ (fun s _ => hmin s (hmem n s))
    · intro b hb
      have ho : IsOpen {s : Set.Icc (0 : ℝ≥0) t | f s < b} :=
        isOpen_lt (f.continuous.comp continuous_subtype_val) continuous_const
      obtain ⟨k, hk⟩ := hq.exists_mem_open ho ⟨⟨u, hu⟩, by
        change f u < b
        rwa [← hmu]⟩
      filter_upwards [eventually_ge_atTop k] with n hn
      have hkI : (q k).val ∈ pitmanSampleTimes t q n :=
        Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), rfl⟩)
      exact lt_of_le_of_lt (Finset.inf'_le (fun s : pitmanSampleTimes t q n => f s)
        (Finset.mem_univ (⟨(q k).val, hkI⟩ : pitmanSampleTimes t q n))) hk
  exact tendsto_const_nhds.sub (tendsto_const_nhds.mul hm)

/-- Helper toward Lemma 4.11: the explicit Gaussian finite-sample statistics
converge in law to the scalar Pitman marginal. Identifying this limit with the
three-dimensional Gaussian radius still requires the reflection computation. -/
theorem gaussianFinitePitman_tendstoInDistribution
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t 0) W₄)
    (t : ℝ≥0) (q : ℕ → Set.Icc (0 : ℝ≥0) t) (hq : DenseRange q) :
    TendstoInDistribution
      (fun n => finitePitmanStatistic (pitmanSampleTimes t q n)
        ⟨t, mem_pitmanSampleTimes t q n⟩) atTop
      (fun p => scalarPitman (pathCoordinate p 0) t)
      (fun n => BrownianReal.projectiveFamily (pitmanSampleTimes t q n)) W₄ := by
  let X (n : ℕ) (p : C(ℝ≥0, Fin 4 → ℝ)) : ℝ :=
    finitePitmanStatistic (pitmanSampleTimes t q n)
      ⟨t, mem_pitmanSampleTimes t q n⟩ (fun s => p s 0)
  have hlaw (n : ℕ) := finitePitmanStatistic_hasLaw W₄ hB (pitmanSampleTimes t q n)
    ⟨t, mem_pitmanSampleTimes t q n⟩
  have hc : TendstoInDistribution X atTop (fun p => scalarPitman (pathCoordinate p 0) t)
      (fun _ => W₄) W₄ :=
    tendstoInDistribution_of_ae_tendsto (fun n => (hlaw n).aemeasurable)
      ((continuous_eval_const t).comp
        (continuous_scalarPitman.comp (continuous_pathCoordinate 0))).measurable.aemeasurable
      (Filter.Eventually.of_forall (fun p => finitePitmanStatistic_tendsto
        (pathCoordinate p 0) t q hq))
  refine ⟨fun n => (continuous_finitePitmanStatistic _ _).measurable.aemeasurable,
    hc.aemeasurable_limit, ?_⟩
  apply hc.tendsto.congr'
  apply Filter.Eventually.of_forall
  intro n
  apply ProbabilityMeasure.toMeasure_injective
  exact (hlaw n).map_eq







































end DirectedDistances.Probability
