/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3B
public import DirectedDistances.RandomWalk.ConditionedLimitPathLaw
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Helpers toward Lemma 4.11: exact continuous-path assembly interfaces.
Neither the walk's functional limit nor the Pitman--Bessel identity is asserted here. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open DirectedDistances.Probability
open scoped Topology NNReal ENNReal

local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: the exact compact-interval tightness/FDD assembly
interface, including the zero interval. It does not assume a walk limit. -/
theorem compactPath_tendsto_of_tight_of_fdd (T : ℝ≥0)
    (μ : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ))
    (ν : ProbabilityMeasure C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ))
    (htight : IsTightMeasureSet
      (Set.range (fun n => (μ n : Measure C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)))))
    (hfdd : ∀ (k : ℕ) (t : Fin k → Set.Icc (0 : ℝ≥0) T),
      TendstoInDistribution
        (fun _ (f : C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)) => fun i => f (t i)) atTop
        (fun f : C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ) => fun i => f (t i))
        (fun n => (μ n : Measure C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ))) ν) :
    Tendsto μ atTop (𝓝 ν) :=
  continuousPath_tendsto_of_tight_of_fdd μ ν htight (fun k t => (hfdd k t).tendsto)

/-- Helper toward Lemma 4.11: restriction from one compact time interval to a smaller one. -/
@[expose] def compactRestrictionBetween (S T : ℝ≥0) (hST : S ≤ T)
    (f : C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)) : C(Set.Icc (0 : ℝ≥0) S, ℝ × ℝ) :=
  ⟨fun t => f ⟨t.val, t.property.1, t.property.2.trans hST⟩,
    f.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

/-- Helper toward Lemma 4.11: nested compact restrictions are continuous. -/
theorem continuous_compactRestrictionBetween (S T : ℝ≥0) (hST : S ≤ T) :
    Continuous (compactRestrictionBetween S T hST) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp (continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _))

/-- Helper toward Lemma 4.11: compatibility of nested restrictions. -/
theorem compactRestrictionBetween_comp (S T : ℝ≥0) (hST : S ≤ T)
    (f : C(ℝ≥0, ℝ × ℝ)) :
    compactRestrictionBetween S T hST (compactPathRestriction T f) =
      compactPathRestriction S f := rfl

/-- Helper toward Lemma 4.11: every locally uniform neighborhood contains an
open cylinder determined by one compact initial interval. -/
theorem exists_compactPathRestriction_cylinder
    (G : Set C(ℝ≥0, ℝ × ℝ)) (hG : IsOpen G) (f : C(ℝ≥0, ℝ × ℝ)) (hf : f ∈ G) :
    ∃ (T : ℝ≥0) (U : Set C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)),
      IsOpen U ∧ compactPathRestriction T f ∈ U ∧ compactPathRestriction T ⁻¹' U ⊆ G := by
  have hb := nhds_basis_uniformity (x := f)
    ((Metric.uniformity_basis_dist (α := ℝ × ℝ)).compactConvergenceUniformity (α := ℝ≥0))
  obtain ⟨⟨K, ε⟩, ⟨hK, hε⟩, hsub⟩ := hb.mem_iff.mp (hG.mem_nhds hf)
  obtain ⟨T, hT⟩ := hK.bddAbove
  refine ⟨T, Metric.ball (compactPathRestriction T f) ε, Metric.isOpen_ball,
    Metric.mem_ball_self hε, ?_⟩
  intro g hg
  apply hsub
  intro t ht
  exact (ContinuousMap.dist_apply_le_dist (⟨t, zero_le, hT ht⟩ : Set.Icc 0 T)).trans_lt hg

/-- Helper toward Lemma 4.11: finitely many compact-interval cylinders can be
combined into one cylinder on a common larger compact interval. -/
theorem finite_union_compactPathRestriction_cylinders
    (F : Finset (Set C(ℝ≥0, ℝ × ℝ)))
    (hF : ∀ s ∈ F, ∃ (T : ℝ≥0) (U : Set C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)),
      IsOpen U ∧ s = compactPathRestriction T ⁻¹' U) :
    ∃ (T : ℝ≥0) (U : Set C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)),
      IsOpen U ∧ (⋃ s ∈ F, s) = compactPathRestriction T ⁻¹' U := by
  classical
  choose t U hU hs using (fun s : F => hF s.val s.property)
  let T : ℝ≥0 := Finset.univ.sup t
  have ht (s : F) : t s ≤ T := Finset.le_sup (Finset.mem_univ s)
  let V : Set C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ) :=
    ⋃ s : F, compactRestrictionBetween (t s) T (ht s) ⁻¹' U s
  refine ⟨T, V, isOpen_iUnion (fun s =>
    (hU s).preimage (continuous_compactRestrictionBetween (t s) T (ht s))), ?_⟩
  ext f
  constructor
  · intro hf
    obtain ⟨s, hsmem, hfs⟩ := mem_iUnion₂.mp hf
    apply mem_iUnion.mpr
    refine ⟨⟨s, hsmem⟩, ?_⟩
    change compactRestrictionBetween (t ⟨s, hsmem⟩) T (ht ⟨s, hsmem⟩)
      (compactPathRestriction T f) ∈ U ⟨s, hsmem⟩
    rw [compactRestrictionBetween_comp]
    change f ∈ compactPathRestriction (t ⟨s, hsmem⟩) ⁻¹' U ⟨s, hsmem⟩
    rw [← hs ⟨s, hsmem⟩]
    exact hfs
  · intro hf
    obtain ⟨s, hfs⟩ := mem_iUnion.mp hf
    apply mem_iUnion₂.mpr
    refine ⟨s.val, s.property, ?_⟩
    rw [hs s]
    exact hfs

/-- Helper toward Lemma 4.11: weak convergence of every compact restriction
implies weak convergence on whole paths with locally uniform topology.
No extra tightness assumption is needed. -/
theorem continuousPath_tendsto_of_compact_restrictions
    (μ : ℕ → ProbabilityMeasure C(ℝ≥0, ℝ × ℝ))
    (ν : ProbabilityMeasure C(ℝ≥0, ℝ × ℝ))
    (hconv : ∀ T : ℝ≥0,
      Tendsto (fun n => (μ n).map (compactPathRestriction T)) atTop
        (𝓝 (ν.map (compactPathRestriction T)))) :
    Tendsto μ atTop (𝓝 ν) := by
  classical
  let S : Set (Set C(ℝ≥0, ℝ × ℝ)) :=
    {s | ∃ (T : ℝ≥0) (U : Set C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)),
      IsOpen U ∧ s = compactPathRestriction T ⁻¹' U}
  have hsmall : ∀ (G : Set C(ℝ≥0, ℝ × ℝ)), IsOpen G →
      ∀ f ∈ G, ∃ s ∈ S, s ∈ 𝓝 f ∧ s ⊆ G := by
    intro G hG f hf
    obtain ⟨T, U, hU, hfU, hsub⟩ := exists_compactPathRestriction_cylinder G hG f hf
    exact ⟨compactPathRestriction T ⁻¹' U, ⟨T, U, hU, rfl⟩,
      (hU.preimage (continuous_compactPathRestriction T)).mem_nhds hfU, hsub⟩
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  refine (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 1) atTop (by simp))
    (by isBoundedDefault)).mpr ?_
  intro r hr
  obtain ⟨F, hF, hrF, hFG⟩ := ν.exists_lt_measure_biUnion_of_isOpen hsmall hG hr
  obtain ⟨T, U, hU, heq⟩ := finite_union_compactPathRestriction_cylinders F hF
  have hm (p : ProbabilityMeasure C(ℝ≥0, ℝ × ℝ)) :
      (p.map (compactPathRestriction T)) U = p (⋃ s ∈ F, s) := by
    rw [ProbabilityMeasure.map_apply p
      (continuous_compactPathRestriction T).measurable.aemeasurable hU.measurableSet, heq]
  have hrU : (r : ℝ≥0∞) <
      (ν.map (compactPathRestriction T) : Measure C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)) U := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ENNReal.coe_lt_coe.mpr ((hm ν).symm ▸ hrF)
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto (hconv T) hU
  filter_upwards [eventually_lt_of_lt_liminf (hrU.trans_le hlim)] with n hn
  have hn' : r < ((μ n).map (compactPathRestriction T)) U := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hn
    exact ENNReal.coe_lt_coe.mp hn
  rw [hm] at hn'
  exact hn'.trans_le (ProbabilityMeasure.apply_mono (μ n) hFG)



theorem continuousPath_tendsto_of_compact_restrictions_inDistribution
    (μ : ℕ → ProbabilityMeasure C(ℝ≥0, ℝ × ℝ))
    (ν : ProbabilityMeasure C(ℝ≥0, ℝ × ℝ))
    (hconv : ∀ T : ℝ≥0,
      TendstoInDistribution (fun _ f => compactPathRestriction T f) atTop
        (compactPathRestriction T) (fun n => (μ n : Measure C(ℝ≥0, ℝ × ℝ))) ν) :
    Tendsto μ atTop (𝓝 ν) :=
  continuousPath_tendsto_of_compact_restrictions μ ν (fun T => (hconv T).tendsto)

/-- Helper toward Lemma 4.11: the radius of the first three independent Brownian
coordinate paths is independent of the fourth entire path. Brownian marginal
laws are unnecessary for this purely probabilistic independence assertion. -/
theorem indepFun_radial3Path_coordinate_three
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    IndepFun (fun p => radial3Path (firstThreePath p))
      (fun p => pathCoordinate p 3) W₄ := by
  let S : Finset (Fin 4) := {0, 1, 2}
  let T : Finset (Fin 4) := {3}
  have hi (i : Fin 3) : i.castSucc ∈ S := by
    fin_cases i <;> decide
  let assemble : (S → C(ℝ≥0, ℝ)) → C(ℝ≥0, Fin 3 → ℝ) := fun v =>
    ⟨fun t i => v ⟨i.castSucc, hi i⟩ t,
      continuous_pi (fun i => (v ⟨i.castSucc, hi i⟩).continuous)⟩
  have ha : Continuous assemble := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_pi (fun i => continuous_eval.comp
      (((continuous_apply (⟨i.castSucc, hi i⟩ : S)).comp continuous_fst).prodMk continuous_snd))
  have h := (hI.indepFun_finset S T (by decide)
    (fun i => (continuous_pathCoordinate i).measurable)).comp
      (continuous_radial3Path.comp ha).measurable
      (measurable_pi_apply (⟨3, by decide⟩ : T))
  exact h

/-- Helper toward Lemma 4.11: a generic tensorization step. Independent pairs
with equal scalar path laws have equal laws after the manuscript's continuous
linear mixing map. This helper does not assume or prove the scalar Pitman theorem. -/
theorem identDistrib_brownianMix_of_independent_marginals
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {A B : Ω → C(ℝ≥0, ℝ)} {A' B' : Ω' → C(ℝ≥0, ℝ)}
    (hA : IdentDistrib A A' P Q) (hB : IdentDistrib B B' P Q)
    (hI : IndepFun A B P) (hI' : IndepFun A' B' Q) :
    IdentDistrib (fun ω => brownianMix (A ω) (B ω))
      (fun ω => brownianMix (A' ω) (B' ω)) P Q := by
  have hpair : IdentDistrib (fun ω => (A ω, B ω)) (fun ω => (A' ω, B' ω)) P Q := by
    refine ⟨hA.aemeasurable_fst.prodMk hB.aemeasurable_fst,
      hA.aemeasurable_snd.prodMk hB.aemeasurable_snd, ?_⟩
    rw [hI.map_prod_eq_prod_map_map hA.aemeasurable_fst hB.aemeasurable_fst,
      hI'.map_prod_eq_prod_map_map hA.aemeasurable_snd hB.aemeasurable_snd,
      hA.map_eq, hB.map_eq]
  exact hpair.comp continuous_brownianMix.measurable

/-- Helper toward Lemma 4.11: compact-interval tightness and whole-process
finite-dimensional convergence assemble into locally uniform weak convergence. -/
theorem continuousPath_tendsto_of_compact_tight_of_fdd
    (μ : ℕ → ProbabilityMeasure C(ℝ≥0, ℝ × ℝ))
    (ν : ProbabilityMeasure C(ℝ≥0, ℝ × ℝ))
    (htight : ∀ T : ℝ≥0, IsTightMeasureSet (Set.range
      (fun n => (((μ n).map (compactPathRestriction T)) :
        Measure C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ)))))
    (hfdd : ∀ (k : ℕ) (t : Fin k → ℝ≥0),
      Tendsto (fun n => (μ n).map (fun f i => f (t i))) atTop
        (𝓝 (ν.map (fun f i => f (t i))))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply continuousPath_tendsto_of_compact_restrictions
  intro T
  apply continuousPath_tendsto_of_tight_of_fdd _ _ (htight T)
  intro k t
  have hcomp (p : ProbabilityMeasure C(ℝ≥0, ℝ × ℝ)) :
      (p.map (compactPathRestriction T)).map (fun f i => f (t i)) =
        p.map (fun f i => f (t i).val) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_map
      (continuous_pi (fun i => continuous_eval_const (t i))).measurable
      (continuous_compactPathRestriction T).measurable
  simpa only [hcomp] using hfdd k (fun i => (t i).val)

/- REMAINING OPEN MATHEMATICS, with full binders. The source and binder
justifications remain those in ConditionedLimitPathLaw.lean:285–324.
The two assembly interfaces there are proved above; the following are not.

1. The iid locally uniform functional limit, including identification of the
joint finite-dimensional laws (not merely separate endpoint Gaussian limits):

∀ (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
  (hB : ∀ i : Fin 4,
    IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
  (hI : iIndepFun
    (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄),
  TendstoInDistribution (fun n ω => diffusiveInterpolation n (codeWalk ω)) atTop
    iidBrownianPath (fun _ => iidCodeMeasure) W₄

2. The scalar Pitman theorem on entire paths, in the four-coordinate realization
needed by the vector-law tensorization helper above:

∀ (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
  (hB : ∀ i : Fin 4,
    IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
  (hI : iIndepFun
    (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄),
  IdentDistrib (fun p => scalarPitman (pathCoordinate p 0))
    (fun p => radial3Path (firstThreePath p)) W₄ W₄

3. Existence, before any canonical choice-defined Brownian path measure:

∃ W₄ : Measure C(ℝ≥0, Fin 4 → ℝ), IsProbabilityMeasure W₄ ∧
  (∀ i : Fin 4,
    IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄) ∧
  iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄

Next: feed compact moment tightness and joint evaluation FDD convergence into
continuousPath_tendsto_of_compact_tight_of_fdd; prove the scalar identity;
combine it with the proved radial/residual independence and the tensorization
helper; then finish the conditioned polygonal/step-path approximation transfer. -/

end DirectedDistances.RandomWalk
