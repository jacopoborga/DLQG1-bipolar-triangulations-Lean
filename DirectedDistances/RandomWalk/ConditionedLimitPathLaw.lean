/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3
public import DirectedDistances.RandomWalk.ConditionedFunctionalInterpolation
public import DirectedDistances.RandomWalk.IIDWalkEndpointCLT
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic.Positivity

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.Probability
open scoped NNReal Topology

-- Canonical Borel structures, local because the upstream bundled module is unavailable.
local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, ℝ × ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ × ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, Fin 4 → ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, Fin 4 → ℝ) := ⟨rfl⟩

/-- Helper toward Lemma 4.11: a scalar coordinate of a finite-dimensional continuous path. -/
@[expose] def pathCoordinate {k : ℕ} (p : C(ℝ≥0, Fin k → ℝ)) (i : Fin k) :
    C(ℝ≥0, ℝ) := ⟨fun t => p t i, (continuous_apply i).comp p.continuous⟩

/-- Helper toward Lemma 4.11: coordinate projection is continuous for locally uniform topology. -/
theorem continuous_pathCoordinate {k : ℕ} (i : Fin k) :
    Continuous (fun p : C(ℝ≥0, Fin k → ℝ) => pathCoordinate p i) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_apply i).comp continuous_eval

/-- Helper toward Lemma 4.11: the first three coordinates used to construct the BES(3) radius. -/
@[expose] def firstThreePath (p : C(ℝ≥0, Fin 4 → ℝ)) : C(ℝ≥0, Fin 3 → ℝ) :=
  ⟨fun t i => p t i.castSucc, continuous_pi (fun i => (pathCoordinate p i.castSucc).continuous)⟩

/-- Helper toward Lemma 4.11: restriction to the first three spatial coordinates is continuous. -/
theorem continuous_firstThreePath : Continuous firstThreePath := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_pi (fun i => (continuous_apply i.castSucc).comp continuous_eval)

/-- Helper toward Lemma 4.11: the covariance-normalized unconditioned Brownian candidate.
Coordinates zero and three are independent standard Brownian motions under the intended input law. -/
@[expose] noncomputable def iidBrownianPath (p : C(ℝ≥0, Fin 4 → ℝ)) : C(ℝ≥0, ℝ × ℝ) :=
  brownianMix (pathCoordinate p 0) (pathCoordinate p 3)

/-- Helper toward Lemma 4.11: the unconditioned candidate is continuous in its input path. -/
theorem continuous_iidBrownianPath : Continuous iidBrownianPath :=
  continuous_brownianMix.comp ((continuous_pathCoordinate 0).prodMk (continuous_pathCoordinate 3))

/-- Helper toward Lemma 4.11: precisely `sqrt(2/3) (A, sqrt(3) B/2 - A/2)`.
Here `A` is the radius of the first three coordinates and `B` is the fourth coordinate. -/
@[expose] noncomputable def conditionedBrownianPath (p : C(ℝ≥0, Fin 4 → ℝ)) :
    C(ℝ≥0, ℝ × ℝ) :=
  brownianMix (radial3Path (firstThreePath p)) (pathCoordinate p 3)

/-- Helper toward Lemma 4.11: the source limiting path is a continuous function of four paths. -/
theorem continuous_conditionedBrownianPath : Continuous conditionedBrownianPath :=
  continuous_brownianMix.comp
    ((continuous_radial3Path.comp continuous_firstThreePath).prodMk (continuous_pathCoordinate 3))

/-- Helper toward Lemma 4.11: covariance-normalized Brownian law from a four-coordinate path law. -/
@[expose] noncomputable def iidBrownianPathLaw (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) :
    Measure C(ℝ≥0, ℝ × ℝ) := W₄.map iidBrownianPath

/-- Helper toward Lemma 4.11: the manuscript's BES(3)/Brownian limiting law, with no
choice of a Brownian measure and no identification with a Pitman image built into the definition. -/
@[expose] noncomputable def conditionedBrownianPathLaw (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) :
    Measure C(ℝ≥0, ℝ × ℝ) := W₄.map conditionedBrownianPath

/-- Helper toward Lemma 4.11: the unconditioned candidate is a probability law. -/
instance iidBrownianPathLaw_isProbabilityMeasure (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    [IsProbabilityMeasure W₄] : IsProbabilityMeasure (iidBrownianPathLaw W₄) :=
  (Measure.isProbabilityMeasure_map_iff
    continuous_iidBrownianPath.measurable.aemeasurable).mpr inferInstance

/-- Helper toward Lemma 4.11: the source limiting candidate is a probability law. -/
instance conditionedBrownianPathLaw_isProbabilityMeasure (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    [IsProbabilityMeasure W₄] : IsProbabilityMeasure (conditionedBrownianPathLaw W₄) :=
  (Measure.isProbabilityMeasure_map_iff
    continuous_conditionedBrownianPath.measurable.aemeasurable).mpr inferInstance

/-- Helper toward Lemma 4.11: under independent input coordinates the Pitman coordinate
and the residual Brownian coordinate are independent as entire paths. -/
theorem indepFun_scalarPitman_coordinate_zero_three
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    IndepFun (fun p => scalarPitman (pathCoordinate p 0))
      (fun p => pathCoordinate p 3) W₄ :=
  IndepFun.scalarPitman_left (hI.indepFun (show (0 : Fin 4) ≠ 3 by decide))

/-- Helper toward Lemma 4.11: scalar projections of the Brownian candidate have the exact
source variance at every time, including time zero. -/
theorem hasLaw_iidBrownianPath_projection
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (a b : ℝ) (t : ℝ≥0) :
    HasLaw (fun p => a * (iidBrownianPath p t).1 + b * (iidBrownianPath p t).2)
      (gaussianReal 0 (((2 / 3 : ℝ) * (a ^ 2 - a * b + b ^ 2)).toNNReal * t)) W₄ := by
  have hi : IndepFun (fun p : C(ℝ≥0, Fin 4 → ℝ) => p t 0) (fun p => p t 3) W₄ := by
    exact (hI.indepFun (show (0 : Fin 4) ≠ 3 by decide)).comp
      (show Continuous (fun f : C(ℝ≥0, ℝ) => f t) from (by fun_prop)).measurable
      (show Continuous (fun f : C(ℝ≥0, ℝ) => f t) from (by fun_prop)).measurable
  exact hasLaw_brownianMix_projection ((hB 0).hasLaw_eval t) ((hB 3).hasLaw_eval t) hi a b

/-- Helper toward Lemma 4.11: at time one every projection of the path candidate agrees
with the existing iid endpoint Gaussian law, after its stated inverse coordinate change. -/
theorem identDistrib_iidBrownianPath_endpoint_projection
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (a b : ℝ) :
    IdentDistrib (fun p => a * (iidBrownianPath p 1).1 + b * (iidBrownianPath p 1).2)
      (fun z : ℝ × ℝ => a * z.1 + b * ((z.2 - z.1) / 2)) W₄ iidEndpointLimitLaw := by
  have h := hasLaw_iidBrownianPath_projection W₄ hB hI a b 1
  simp only [mul_one] at h
  exact h.identDistrib (hasLaw_iidEndpointLimit_projection a b)

/-- Helper toward Lemma 4.11: the complete diagonal endpoint law agrees with the existing
endpoint limit, not only its two scalar marginals. -/
theorem hasLaw_iidBrownianPath_diagonal_endpoint
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    HasLaw (fun p => ((iidBrownianPath p 1).1,
      (iidBrownianPath p 1).1 + 2 * (iidBrownianPath p 1).2)) iidEndpointLimitLaw W₄ := by
  have hX := hasLaw_iidBrownianPath_projection W₄ hB hI 1 0 1
  have hY := hasLaw_iidBrownianPath_projection W₄ hB hI 1 2 1
  norm_num at hX hY
  have hi : IndepFun (fun p => (iidBrownianPath p 1).1)
      (fun p => (iidBrownianPath p 1).1 + 2 * (iidBrownianPath p 1).2) W₄ := by
    have h := (hI.indepFun (show (0 : Fin 4) ≠ 3 by decide)).comp
      (show Measurable (fun f : C(ℝ≥0, ℝ) => Real.sqrt (2 / 3) * f 1) from
        (show Continuous _ from (by fun_prop)).measurable)
      (show Measurable (fun f : C(ℝ≥0, ℝ) => Real.sqrt (2 / 3) * Real.sqrt 3 * f 1) from
        (show Continuous _ from (by fun_prop)).measurable)
    convert h using 1
    · rfl
    · funext p
      change Real.sqrt (2 / 3) * p 1 0 +
          2 * (Real.sqrt (2 / 3) * (Real.sqrt 3 / 2 * p 1 3 - p 1 0 / 2)) =
        Real.sqrt (2 / 3) * Real.sqrt 3 * p 1 3
      ring
  refine ⟨hX.aemeasurable.prodMk hY.aemeasurable, ?_⟩
  rw [hi.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hX.map_eq, hY.map_eq]
  have he : (2 / 3 : ℝ).toNNReal = (2 / 3 : ℝ≥0) := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  rw [he]
  rfl

/-- Helper toward Lemma 4.11: full endpoint compatibility after the inverse diagonal map. -/
theorem identDistrib_iidBrownianPath_endpoint
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    IdentDistrib (fun p => iidBrownianPath p 1)
      (fun z : ℝ × ℝ => (z.1, (z.2 - z.1) / 2)) W₄ iidEndpointLimitLaw := by
  have hid : HasLaw (id : ℝ × ℝ → ℝ × ℝ) iidEndpointLimitLaw iidEndpointLimitLaw :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have h := ((hasLaw_iidBrownianPath_diagonal_endpoint W₄ hB hI).identDistrib hid).comp
    (show Measurable (fun z : ℝ × ℝ => (z.1, (z.2 - z.1) / 2)) from (by fun_prop))
  convert h using 1
  · funext p
    apply Prod.ext
    · rfl
    · dsimp
      ring
  · rfl

/-- Helper toward Lemma 4.11: joint continuity of scalar interpolation in the sequence and time. -/
theorem continuous_walkLinearScalar_joint :
    Continuous (fun p : (ℕ → ℝ) × ℝ≥0 => walkLinearScalar p.1 p.2) := by
  have hlf : LocallyFinite (fun k : ℕ => Set.Icc (k : ℝ≥0) (k + 1)) := by
    intro x
    refine ⟨Set.Iio (x + 1), Iio_mem_nhds (lt_add_one x), ?_⟩
    apply (Finset.range (⌊((x : ℝ) + 1)⌋₊ + 1)).finite_toSet.subset
    intro k hk
    obtain ⟨y, hy, hyx⟩ := hk
    have hky : (k : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy.1
    have hyx' : (y : ℝ) < (x : ℝ) + 1 := by exact_mod_cast hyx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hky.trans hyx'.le)))
  have hlf' := hlf.preimage_continuous
    (continuous_snd : Continuous (Prod.snd : (ℕ → ℝ) × ℝ≥0 → ℝ≥0))
  apply hlf'.continuous
  · ext p
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    refine ⟨⌊(p.2 : ℝ)⌋₊, ?_⟩
    constructor
    · exact_mod_cast Nat.floor_le p.2.coe_nonneg
    · exact_mod_cast (Nat.lt_floor_add_one (p.2 : ℝ)).le
  · intro k
    exact isClosed_Icc.preimage continuous_snd
  · intro k
    have hc : Continuous (fun p : (ℕ → ℝ) × ℝ≥0 =>
        p.1 k + ((p.2 : ℝ) - k) * (p.1 (k + 1) - p.1 k)) := by fun_prop
    exact hc.continuousOn.congr (fun p hp => walkLinearScalar_on_cell p.1 k p.2 hp)

/-- Helper toward Lemma 4.11: interpolation is continuous as a map from whole discrete paths
with their product topology to continuous paths with locally uniform topology. -/
theorem continuous_diffusiveInterpolation (n : ℕ) :
    Continuous (diffusiveInterpolation n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h₁ : Continuous (fun p : (ℕ → ℤ × ℤ) × ℝ≥0 =>
      ((fun k => ((p.1 k).1 : ℝ)), (n : ℝ≥0) * p.2)) := by fun_prop
  have h₂ : Continuous (fun p : (ℕ → ℤ × ℤ) × ℝ≥0 =>
      ((fun k => ((p.1 k).2 : ℝ)), (n : ℝ≥0) * p.2)) := by fun_prop
  exact ((continuous_walkLinearScalar_joint.comp h₁).div_const _).prodMk
    ((continuous_walkLinearScalar_joint.comp h₂).div_const _)

/-- Helper toward Lemma 4.11: the actual source-conditioned polygonal path law. -/
@[expose] noncomputable def conditionedInterpolationPathLaw (n : ℕ) :
    Measure C(ℝ≥0, ℝ × ℝ) :=
  (conditionedVectorPathLaw 0 0).map (diffusiveInterpolation n)

/-- Helper toward Lemma 4.11: the source-conditioned polygonal law is a probability measure. -/
instance conditionedInterpolationPathLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (conditionedInterpolationPathLaw n) :=
  (Measure.isProbabilityMeasure_map_iff
    (continuous_diffusiveInterpolation n).measurable.aemeasurable).mpr inferInstance

/-- Helper toward Lemma 4.11: exported measurability of the discrete vector transform. -/
theorem measurable_vectorPitmanPath : Measurable vectorPitman := by
  have hf : Measurable (fun z : ℕ → ℤ × ℤ => fun k => (z k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hf).prodMk
    (((measurable_pi_apply n).snd).add ((measurable_globalLazyRunningMinimum n).comp hf))

/-- Helper toward Lemma 4.11: the exact iid coupling survives whole-path interpolation. -/
theorem conditionedInterpolationPathLaw_eq_map (n : ℕ) :
    conditionedInterpolationPathLaw n =
      iidCodeMeasure.map (fun ω => diffusiveInterpolation n (vectorPitman (codeWalk ω))) := by
  unfold conditionedInterpolationPathLaw
  rw [← map_vectorPitman_codeWalk]
  exact Measure.map_map (continuous_diffusiveInterpolation n).measurable
    (measurable_vectorPitmanPath.comp measurable_codeWalk)

/-- Helper toward Lemma 4.11: the pathwise linear factorization also holds for the full law.
The right side still contains the scalar Pitman transform; no BES(3) identity is assumed. -/
theorem iidBrownianPathLaw_map_vectorPitman (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) :
    (iidBrownianPathLaw W₄).map continuousVectorPitman =
      W₄.map (fun p => brownianMix (scalarPitman (pathCoordinate p 0)) (pathCoordinate p 3)) := by
  unfold iidBrownianPathLaw
  rw [Measure.map_map continuous_continuousVectorPitman.measurable
    continuous_iidBrownianPath.measurable]
  congr 1
  funext p
  exact continuousVectorPitman_brownianMix _ _

/-- Helper toward Lemma 4.11: restriction of a whole path to a compact initial interval,
including the zero interval. -/
@[expose] def compactPathRestriction (T : ℝ≥0) (f : C(ℝ≥0, ℝ × ℝ)) :
    C(Set.Icc (0 : ℝ≥0) T, ℝ × ℝ) :=
  ⟨fun t => f t.1, f.continuous.comp continuous_subtype_val⟩

/-- Helper toward Lemma 4.11: restriction is continuous in the respective compact-open topologies. -/
theorem continuous_compactPathRestriction (T : ℝ≥0) : Continuous (compactPathRestriction T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/- EXACT INTENDED LEMMA 4.11, continuous interpolation formulation (OPEN):

∀ (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
  (hB : ∀ i : Fin 4,
    IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
  (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄),
  TendstoInDistribution
    (fun n (z : ℕ → ℤ × ℤ) => diffusiveInterpolation n z) atTop
    conditionedBrownianPath (fun _ => conditionedVectorPathLaw 0 0) W₄

Binder justification: `W₄` realizes the three standard Brownian coordinates
whose Euclidean radius is the source's zero-start BES(3), plus its independent
standard Brownian `B`. `hB` imposes exactly standard Brownian laws (including
almost-sure zero start); `hI` imposes independence of these whole paths. No
conditioning, recurrence, tightness, convergence or Pitman identity is a premise.
`n : ℕ` is the source scaling parameter; convergence is at infinity, so the
harmless value at n=0 does not affect the statement. The discrete carrier and
`conditionedVectorPathLaw 0 0` are the source-conditioned walk. The target is
C(ℝ≥0, ℝ×ℝ), with its existing compact-open (locally uniform) topology.
To recover the literal step-walk statement, prove convergence transfer using
`codeWalk_vectorPitman_interpolation_sup_le` and the exact coupling above.
This comment is not a theorem and does not assert that interpolation transfer is done.

OPEN WHOLE-PATH IDENTIFICATION (same source-justified binders):
∀ (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
  (hB : ∀ i : Fin 4,
    IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
  (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄),
  (iidBrownianPathLaw W₄).map continuousVectorPitman = conditionedBrownianPathLaw W₄

OPEN IID FUNCTIONAL LIMIT:
∀ (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
  (hB : ∀ i : Fin 4,
    IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
  (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄),
  TendstoInDistribution (fun n ω => diffusiveInterpolation n (codeWalk ω)) atTop
    iidBrownianPath (fun _ => iidCodeMeasure) W₄

OPEN EXISTENCE (not a choice-defined input):
∃ W₄ : Measure C(ℝ≥0, Fin 4 → ℝ), IsProbabilityMeasure W₄ ∧
  (∀ i : Fin 4, IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄) ∧
  iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄

ASSEMBLY INTERFACES (OPEN), with the canonical Borel structures:
1. Tightness/FDD on a compact interval:
∀ (T : ℝ≥0)
  (μ : ℕ → ProbabilityMeasure C(Set.Icc (0:ℝ≥0) T, ℝ×ℝ))
  (ν : ProbabilityMeasure C(Set.Icc (0:ℝ≥0) T, ℝ×ℝ)),
  IsTightMeasureSet
    (Set.range (fun n => (μ n : Measure C(Set.Icc (0:ℝ≥0) T, ℝ×ℝ)))) →
  (∀ (k : ℕ) (t : Fin k → Set.Icc (0:ℝ≥0) T),
    TendstoInDistribution
      (fun n (f : C(Set.Icc (0:ℝ≥0) T, ℝ×ℝ)) => fun i => f (t i)) atTop
      (fun f : C(Set.Icc (0:ℝ≥0) T, ℝ×ℝ) => fun i => f (t i))
      (fun n => (μ n : Measure C(Set.Icc (0:ℝ≥0) T, ℝ×ℝ))) ν) →
  Tendsto μ atTop (𝓝 ν)
2. Compatible restrictions:
∀ (μ : ℕ → ProbabilityMeasure C(ℝ≥0,ℝ×ℝ))
  (ν : ProbabilityMeasure C(ℝ≥0,ℝ×ℝ)),
  (∀ T : ℝ≥0,
    TendstoInDistribution (fun _ f => compactPathRestriction T f) atTop
      (compactPathRestriction T) (fun n => (μ n : Measure C(ℝ≥0,ℝ×ℝ))) ν) →
  Tendsto μ atTop (𝓝 ν)
identification with the displayed Brownian law must also be checked. -/

end DirectedDistances.RandomWalk
