/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3N
public import DirectedDistances.RandomWalk.ConditionedLimitPathLaw2

/-! Helper toward Lemma 4.11: the vector Pitman law obtained by
tensorizing the scalar whole-path identity with the independent residual.
These results identify the Brownian limit law; they do not assert the walk's
functional convergence. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter Set
open DirectedDistances.RandomWalk
open scoped Topology NNReal ENNReal

local instance pitman3OContinuousMapMeasurableSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance pitman3OContinuousMapBorelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance pitman3OContinuousMapSecondCountable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: the vector Pitman image of the covariance
Σ-Brownian path law is precisely the manuscript's conditioned Brownian law,
with the Bessel radius independent of the residual Brownian path. -/
theorem iidBrownianPathLaw_map_continuousVectorPitman
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    (iidBrownianPathLaw W₄).map continuousVectorPitman =
      conditionedBrownianPathLaw W₄ := by
  rw [iidBrownianPathLaw_map_vectorPitman]
  exact (identDistrib_brownianMix_of_independent_marginals
    (scalarPitman_identDistrib_radial3Path W₄ hB hI)
    (IdentDistrib.refl (continuous_pathCoordinate (3 : Fin 4)).measurable.aemeasurable)
    (indepFun_scalarPitman_coordinate_zero_three W₄ hI)
    (indepFun_radial3Path_coordinate_three W₄ hI)).map_eq

end DirectedDistances.Probability
