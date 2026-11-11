module

public import DirectedDistances.RandomWalk.ConditionedVectorTrajectory
public import DirectedDistances.RandomWalk.ConditionedSourceBarrier
public import DirectedDistances.RandomWalk.ConditionedVectorRegeneration
public import DirectedDistances.RandomWalk.ConditionedVectorPastRegeneration
public import DirectedDistances.RandomWalk.ConditionedVectorBarrierJoint

/-! # Checked RN-parametrized providers instantiated for the constructed law

Instances of the checked providers with `ν := conditionedVectorPathLaw x y`, the
all-horizon RN hypothesis being discharged by `conditionedVectorPathLaw_map_prefix` -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem conditionedVectorPathLaw_map_prefix_zero (k : ℕ) :
    (conditionedVectorPathLaw 0 0).map (fun q => fun j : Fin (k + 1) => q j.val) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0) := by
  simpa only [Nat.cast_zero] using conditionedVectorPathLaw_map_prefix 0 0 k

/-- Instance of `conditionedSource_barrier_probability` for
`ν := conditionedVectorPathLaw x y` -/
theorem conditionedVectorPathLaw_barrier_probability (x : ℕ) (y : ℤ)
    (s : ℕ) (hs : s ≤ x) :
    (conditionedVectorPathLaw x y).real {p | ∀ j, (x : ℤ) - (s : ℤ) ≤ (p j).1} =
      ((s : ℝ) + 1) / ((x : ℝ) + 1) :=
  conditionedSource_barrier_probability x y (conditionedVectorPathLaw x y)
    (conditionedVectorPathLaw_map_prefix x y) s hs

/-- Instance of `conditionedSource_cylinder_regeneration` for
`ν := conditionedVectorPathLaw 0 0` -/
theorem conditionedVectorPathLaw_cylinder_regeneration
    (n X : ℕ) (w : Fin n → Fin 3)
    (hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1)
    (hX : (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 = (X : ℤ)) :
    let Y : ℤ := (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).2
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
    let F : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (X : ℤ) ≤ (p (n + k)).1}
    (ProbabilityTheory.cond (conditionedVectorPathLaw 0 0) (C ∩ F)).map
      (fun p => fun k => p (n + k) - ((X : ℤ), Y)) = conditionedVectorPathLaw 0 0 :=
  conditionedSource_cylinder_regeneration (conditionedVectorPathLaw 0 0)
    conditionedVectorPathLaw_map_prefix_zero n X w hw hX

/-- Instance of `conditionedSource_cylinder_restrict_regeneration` for
`ν := conditionedVectorPathLaw 0 0` -/
theorem conditionedVectorPathLaw_cylinder_restrict_regeneration
    (n : ℕ) (w : Fin n → Fin 3) :
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
    let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
    ((conditionedVectorPathLaw 0 0).restrict (C ∩ B)).map
        (fun p => fun k => p (n + k) - p n) =
      (conditionedVectorPathLaw 0 0) (C ∩ B) • conditionedVectorPathLaw 0 0 :=
  conditionedSource_cylinder_restrict_regeneration (conditionedVectorPathLaw 0 0)
    conditionedVectorPathLaw_map_prefix_zero n w

/-- Instance of `conditionedSource_past_restrict_regeneration` for
`ν := conditionedVectorPathLaw 0 0` -/
theorem conditionedVectorPathLaw_past_restrict_regeneration
    (n : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) inferInstance] A) :
    let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
    ((conditionedVectorPathLaw 0 0).restrict (A ∩ B)).map
        (fun p => fun k => p (n + k) - p n) =
      (conditionedVectorPathLaw 0 0) (A ∩ B) • conditionedVectorPathLaw 0 0 :=
  conditionedSource_past_restrict_regeneration (conditionedVectorPathLaw 0 0)
    conditionedVectorPathLaw_map_prefix_zero n A hA

/-- Instance of `conditionedSource_prefix_inter_future_barrier` for
`ν := conditionedVectorPathLaw x y` -/
theorem conditionedVectorPathLaw_prefix_inter_future_barrier (x : ℕ) (y : ℤ)
    (n X a : ℕ) (w : Fin n → Fin 3)
    (hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1)
    (haX : a ≤ X)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ)) :
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w}
    (conditionedVectorPathLaw x y).real (C ∩ {p | ∀ j, (a : ℤ) ≤ (p (n + j)).1}) =
      (conditionedVectorPathLaw x y).real C * (((X - a : ℕ) : ℝ) + 1) / ((X : ℝ) + 1) :=
  conditionedSource_prefix_inter_future_barrier x y (conditionedVectorPathLaw x y)
    (conditionedVectorPathLaw_map_prefix x y) n X a w hw haX hX

/-- Instance of `conditionedSource_prefix_inter_barrier` for
`ν := conditionedVectorPathLaw x y` -/
theorem conditionedVectorPathLaw_prefix_inter_barrier (x : ℕ) (y : ℤ)
    (n X a : ℕ) (w : Fin n → Fin 3)
    (ha : ∀ j, (a : ℤ) ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ)) :
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w}
    (conditionedVectorPathLaw x y).real (C ∩ {p | ∀ j, (a : ℤ) ≤ (p j).1}) =
      (conditionedVectorPathLaw x y).real C * (((X - a : ℕ) : ℝ) + 1) / ((X : ℝ) + 1) :=
  conditionedSource_prefix_inter_barrier x y (conditionedVectorPathLaw x y)
    (conditionedVectorPathLaw_map_prefix x y) n X a w ha hX

end DirectedDistances.RandomWalk
