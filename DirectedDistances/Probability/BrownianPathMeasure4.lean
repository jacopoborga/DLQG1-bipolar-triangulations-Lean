/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedLimitPathLaw2

/-! Helper toward Lemma 4.11: finite products of scalar continuous-path laws.
This construction uses an arbitrary supplied probability law. It does not
select or assert the existence of a scalar Brownian path law. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk
open scoped NNReal

local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: assemble four scalar paths into one vector path. -/
@[expose] def assembleFourPaths (v : Fin 4 → C(ℝ≥0, ℝ)) : C(ℝ≥0, Fin 4 → ℝ) :=
  ⟨fun t i => v i t, continuous_pi (fun i => (v i).continuous)⟩

/-- Helper toward Lemma 4.11: assembly is continuous in the compact-open topology. -/
theorem continuous_assembleFourPaths : Continuous assembleFourPaths := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_pi (fun i => continuous_eval.comp
    (((continuous_apply i).comp continuous_fst).prodMk continuous_snd))

/-- Helper toward Lemma 4.11: coordinate extraction inverts assembly. -/
@[simp] theorem pathCoordinate_assembleFourPaths (v : Fin 4 → C(ℝ≥0, ℝ)) (i : Fin 4) :
    pathCoordinate (assembleFourPaths v) i = v i := rfl

/-- Helper toward Lemma 4.11: assembly inverts coordinate extraction. -/
@[simp] theorem assembleFourPaths_pathCoordinate (p : C(ℝ≥0, Fin 4 → ℝ)) :
    assembleFourPaths (fun i => pathCoordinate p i) = p := rfl

/-- Helper toward Lemma 4.11: the product of four scalar path laws, pushed to vector paths. -/
@[expose] noncomputable def fourPathProduct (W : Measure C(ℝ≥0, ℝ)) :
    Measure C(ℝ≥0, Fin 4 → ℝ) :=
  (Measure.pi (fun _ : Fin 4 => W)).map assembleFourPaths

/-- Helper toward Lemma 4.11: the assembled product has total mass one. -/
instance fourPathProduct_isProbabilityMeasure (W : Measure C(ℝ≥0, ℝ))
    [IsProbabilityMeasure W] : IsProbabilityMeasure (fourPathProduct W) :=
  (Measure.isProbabilityMeasure_map_iff
    continuous_assembleFourPaths.measurable.aemeasurable).mpr inferInstance

/-- Helper toward Lemma 4.11: each coordinate of the product has the supplied scalar law. -/
theorem fourPathProduct_map_coordinate (W : Measure C(ℝ≥0, ℝ))
    [IsProbabilityMeasure W] (i : Fin 4) :
    (fourPathProduct W).map (fun p => pathCoordinate p i) = W := by
  rw [fourPathProduct, Measure.map_map (continuous_pathCoordinate i).measurable
    continuous_assembleFourPaths.measurable]
  exact (measurePreserving_eval (fun _ : Fin 4 => W) i).map_eq

/-- Helper toward Lemma 4.11: the full vector of extracted coordinate paths has product law. -/
theorem fourPathProduct_map_coordinates (W : Measure C(ℝ≥0, ℝ))
    [IsProbabilityMeasure W] :
    (fourPathProduct W).map (fun p i => pathCoordinate p i) =
      Measure.pi (fun _ : Fin 4 => W) := by
  rw [fourPathProduct, Measure.map_map
    (measurable_pi_iff.mpr (fun i => (continuous_pathCoordinate i).measurable))
    continuous_assembleFourPaths.measurable]
  exact Measure.map_id

/-- Helper toward Lemma 4.11: the four entire coordinate paths are independent. -/
theorem fourPathProduct_iIndepFun (W : Measure C(ℝ≥0, ℝ))
    [IsProbabilityMeasure W] :
    iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i)
      (fourPathProduct W) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (continuous_pathCoordinate i).measurable.aemeasurable)).mpr
  simp only [fourPathProduct_map_coordinates, fourPathProduct_map_coordinate]

/-- Helper toward Lemma 4.11: extraction is a random variable with the scalar input law. -/
theorem fourPathProduct_hasLaw_coordinate (W : Measure C(ℝ≥0, ℝ))
    [IsProbabilityMeasure W] (i : Fin 4) :
    HasLaw (fun p => pathCoordinate p i) W (fourPathProduct W) :=
  ⟨(continuous_pathCoordinate i).measurable.aemeasurable,
    fourPathProduct_map_coordinate W i⟩

/-- Helper toward Lemma 4.11: Brownian coordinate laws are preserved by the
explicit product construction. This is a property of a supplied scalar law,
not a theorem asserting existence of either Brownian measure. -/
theorem fourPathProduct_isBrownianReal (W : Measure C(ℝ≥0, ℝ))
    [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (p : C(ℝ≥0, ℝ)) => p t) W) (i : Fin 4) :
    IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) (fourPathProduct W) where
  hasLaw I := (hW.hasLaw I).comp (fourPathProduct_hasLaw_coordinate W i)
  cont := Filter.Eventually.of_forall (fun p => (pathCoordinate p i).continuous)


















end DirectedDistances.Probability
