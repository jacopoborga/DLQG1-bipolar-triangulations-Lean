module

public import DirectedDistances.Probability.SplitIndependence

/-! # Composing split independence with measurable determinations -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory





theorem iIndepFun_of_cut_determination
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℤ → Ω → β}
    {α γ : ℤ → Type*}
    [mα : ∀ k, MeasurableSpace (α k)] [mγ : ∀ k, MeasurableSpace (γ k)]
    (A : ∀ k, Ω → α k) (B : ∀ k, Ω → γ k)
    (hAB : ∀ k, IndepFun (A k) (B k) μ)
    (F : ∀ k, α k → (∀ _j : {j : ℤ // j ≤ k}, β))
    (G : ∀ k, γ k → (∀ _j : {j : ℤ // k + 1 ≤ j}, β))
    (hF : ∀ k, Measurable (F k)) (hG : ∀ k, Measurable (G k))
    (hdetL : ∀ k,
      (fun ω (j : {j : ℤ // j ≤ k}) => X j ω) =ᵐ[μ] fun ω => F k (A k ω))
    (hdetR : ∀ k,
      (fun ω (j : {j : ℤ // k + 1 ≤ j}) => X j ω) =ᵐ[μ] fun ω => G k (B k ω))
    (_hX : ∀ j, Measurable (X j)) :
    iIndepFun X μ := by
  apply iIndepFun_of_indepFun_int_splits
  intro k
  have hcomp : IndepFun (F k ∘ A k) (G k ∘ B k) μ :=
    (hAB k).comp (hF k) (hG k)
  exact hcomp.congr (hdetL k).symm (hdetR k).symm

end DirectedDistances.Probability
