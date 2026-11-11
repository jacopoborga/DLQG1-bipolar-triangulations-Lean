/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanWholePath2
public import DirectedDistances.Probability.PitmanBessel3L

/-! Helper toward Lemma 4.11: the scalar Pitman identity on entire
continuous paths and all finite-dimensional laws.
These results identify the Brownian limit law; they do not assert the walk's
functional convergence. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter Set
open DirectedDistances.RandomWalk
open scoped Topology NNReal ENNReal

local instance pitman3NContinuousMapMeasurableSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance pitman3NContinuousMapBorelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance pitman3NContinuousMapSecondCountable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: the scalar Brownian Pitman transform has the
same entire continuous-path law as the radius of three independent standard
Brownian motions. The equality is on the Borel compact-open path space. -/
theorem scalarPitman_identDistrib_radial3Path
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    IdentDistrib (fun p => scalarPitman (pathCoordinate p 0))
      (fun p => radial3Path (firstThreePath p)) W₄ W₄ := by
  apply WholePathSinc.identDistrib_continuousPath_of_sinc_transition
    (fun p => scalarPitman (pathCoordinate p 0))
    (fun p => radial3Path (firstThreePath p))
    (continuous_scalarPitman.comp (continuous_pathCoordinate 0)).measurable
    (continuous_radial3Path.comp continuous_firstThreePath).measurable
    (fun t => (scalarPitman_nonneg_ae W₄ (hB 0)).mono (fun p hp => hp t))
    (fun t => Eventually.of_forall (fun p => radial3Path_nonneg (firstThreePath p) t))
    (scalarPitman_radial3_identDistrib_eval W₄ hB hI 0)
    (fun u a => Real.exp (-(u : ℝ) * a^2 / 2))
  · intro s u k t ht F a
    exact scalarPitman_past_sinc_transition W₄ hB hI s u t ht F a
  · intro s u k t ht F a
    exact radial3_past_sinc_transition W₄ hB hI s u t ht F a

/-- Helper toward Lemma 4.11: all finite-dimensional Pitman and radial laws
agree, for arbitrary finite time families with repetitions and time zero. -/
theorem scalarPitman_fdd_identDistrib_radial3
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (k : ℕ) (t : Fin k → ℝ≥0) :
    IdentDistrib (fun p j => scalarPitman (pathCoordinate p 0) (t j))
      (fun p j => radial3Path (firstThreePath p) (t j)) W₄ W₄ :=
  (scalarPitman_identDistrib_radial3Path W₄ hB hI).comp
    (continuous_pi (fun j => continuous_eval_const (t j))).measurable

/-- Helper toward Lemma 4.11: the finite-set scalar Pitman law is the exact
radial pushforward of three independent Brownian projective-family laws. -/
theorem scalarPitman_finset_hasLaw_radial3
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (I : Finset ℝ≥0) :
    HasLaw (fun p (t : I) => scalarPitman (pathCoordinate p 0) t)
      ((Measure.pi (fun _ : Fin 3 => BrownianReal.projectiveFamily I)).map
        (fun x (t : I) => Real.sqrt ((x 0 t)^2 + (x 1 t)^2 + (x 2 t)^2))) W₄ := by
  have hi := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) => fun t : I => f t)
    (fun _ => (continuous_pi (fun t : I => continuous_eval_const t.val)).measurable)
  have hl : HasLaw (fun p (i : Fin 3) (t : I) => p t i.castSucc)
      (Measure.pi (fun _ : Fin 3 => BrownianReal.projectiveFamily I)) W₄ :=
    hi.hasLaw_pi (fun i => (hB i.castSucc).toIsPreBrownianReal.hasLaw I)
  have hr := (hasLaw_map (by fun_prop : AEMeasurable
    (fun x : Fin 3 → I → ℝ => fun t : I =>
      Real.sqrt ((x 0 t)^2 + (x 1 t)^2 + (x 2 t)^2))
      (Measure.pi (fun _ : Fin 3 => BrownianReal.projectiveFamily I)))).comp hl
  exact ((scalarPitman_identDistrib_radial3Path W₄ hB hI).comp
    (continuous_pi (fun t : I => continuous_eval_const t.val)).measurable).symm.hasLaw hr

end DirectedDistances.Probability
