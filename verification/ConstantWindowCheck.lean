module

public import verification.ConstantWindow

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk

#print axioms DirectedDistances.RandomWalk.bridgeConstantWindow
#print axioms DirectedDistances.RandomWalk.measurable_bridgeConstantWindow
#print axioms DirectedDistances.RandomWalk.bridgeConstantWindow_eq_of_some

-- Exact instance of the universal-extension clause; no new convergence theorem.
example (A : ℝ) (hA : 1 < A) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ),
        |((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
            (MeasureTheory.Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            (bridgeConstantWindow n N ⁻¹' B) -
          (uibhbotEncodingWindowLaw N).real B| ≤ ε := by
  obtain ⟨n₀, hbound⟩ :=
    DirectedDistances.Paper.Section5.disk_walk_conv_corrected A hA N ε hε
  refine ⟨n₀, ?_⟩
  intro n hn ℓ hlo hhi hle hmod B
  exact (hbound n hn ℓ hlo hhi hle hmod).2.2 (bridgeConstantWindow n N)
    (measurable_bridgeConstantWindow n N)
    (bridgeConstantWindow_eq_of_some n N) B
