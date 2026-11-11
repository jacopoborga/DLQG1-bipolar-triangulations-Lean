module

public import DirectedDistances.Probability.CutIndependence

/-! # Independence from every integer split -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

/-- independence of the past and future tuple observations at every integer cut
implies mutual independence of the indexed family. -/
theorem iIndepFun_of_indepFun_int_splits
    {Ω : Type*} [MeasurableSpace Ω] {β : ℤ → Type*}
    [mβ : ∀ j, MeasurableSpace (β j)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ∀ j, Ω → β j}
    (hcut : ∀ k : ℤ,
      IndepFun (fun ω (j : {j : ℤ // j ≤ k}) => X j ω)
        (fun ω (j : {j : ℤ // k + 1 ≤ j}) => X j ω) μ) :
    iIndepFun X μ :=
  iIndepFun_of_indepFun_int_cuts hcut

/-- family with a single value type. -/
theorem iIndepFun_of_indepFun_int_splits' {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℤ → Ω → β}
    (hcut : ∀ k : ℤ,
      IndepFun (fun ω (j : {j : ℤ // j ≤ k}) => X j ω)
        (fun ω (j : {j : ℤ // k + 1 ≤ j}) => X j ω) μ) :
    iIndepFun X μ :=
  iIndepFun_of_indepFun_int_cuts hcut

end DirectedDistances.Probability
