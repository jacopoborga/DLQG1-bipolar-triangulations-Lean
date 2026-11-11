 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.DiskWalkConv

/-!
# Lemma 5.18 (`lem-disk-walk-conv`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/




















public section
namespace DirectedDistances.Paper.Section5



theorem disk_walk_conv_corrected :
    ∀ A : ℝ, 1 < A → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
        A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
        (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
        (∀ S : Set (Option (Fin (2 * N + 1) → ℤ × ℤ)),
          |((ProbabilityTheory.cond DirectedDistances.RandomWalk.iidCodeMeasure
                (DirectedDistances.RandomWalk.coneEvent (ℓ : ℤ) 0 n)).prod
              (MeasureTheory.Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
              (DirectedDistances.RandomWalk.bridgeOptionWindow n N ⁻¹' S) -
            (DirectedDistances.RandomWalk.uibhbotEncodingWindowLaw N).real (some ⁻¹' S)| ≤ ε) ∧
        ((ProbabilityTheory.cond DirectedDistances.RandomWalk.iidCodeMeasure
              (DirectedDistances.RandomWalk.coneEvent (ℓ : ℤ) 0 n)).prod
            (MeasureTheory.Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            (DirectedDistances.RandomWalk.bridgeOptionWindow n N ⁻¹' {none}) ≤ ε ∧
        (∀ W : (ℕ → Fin 3) × ℕ → (Fin (2 * N + 1) → ℤ × ℤ), Measurable W →
          (∀ p x, DirectedDistances.RandomWalk.bridgeOptionWindow n N p = some x → W p = x) →
          ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ),
            |((ProbabilityTheory.cond DirectedDistances.RandomWalk.iidCodeMeasure
                  (DirectedDistances.RandomWalk.coneEvent (ℓ : ℤ) 0 n)).prod
                (MeasureTheory.Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real (W ⁻¹' B) -
              (DirectedDistances.RandomWalk.uibhbotEncodingWindowLaw N).real B| ≤ ε) :=
 
by exact DirectedDistances.PaperProofs.Section5.disk_walk_conv_corrected
 
 

end DirectedDistances.Paper.Section5
 
