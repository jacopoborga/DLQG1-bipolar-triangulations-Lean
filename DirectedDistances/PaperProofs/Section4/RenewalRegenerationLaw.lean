/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalSelectorConsequence
public import DirectedDistances.Paper.Section4.CondWalkRNLaw

/-! # Thin source-law provider for the conditional renewal law -/

public section

namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk

/-- conditional future law after the supplied positive-success time of the literal
Paper.Section4.cond_walk_rn_law; the source renewal times T_m are NOT defined
here (the six renewalTime declarations remain unadmitted), the geometric
equivalence by Lemma 4.8 is not claimed; not the paper result. -/
theorem conditionedVectorPathLaw_selector_regeneration
    (m : ℕ)
    (T : (ℕ → ℤ × ℤ) → WithTop ℕ)
    (hGraph : ∀ p, IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (T p)) :
    let μf : Measure {p // T p < ⊤} := (conditionedVectorPathLaw 0 0).comap
      (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ))
    let history :=
      stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val)
    let future :=
      stoppedVectorFuture (finiteTimeIndex T) (fun ω => ω.val)
    condDistrib future history μf =ᵐ[μf.map history]
      Kernel.const (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)
        (conditionedVectorPathLaw 0 0) := by
  have hProbability : IsProbabilityMeasure (conditionedVectorPathLaw 0 0) :=
    (DirectedDistances.Paper.Section4.cond_walk_rn_law (0 : ℕ) (0 : ℤ)).1
  exact @DirectedDistances.RandomWalk.conditionedSource_selector_condDistrib_ae_eq_const
    (conditionedVectorPathLaw 0 0) hProbability (fun k => by
      simpa only [Nat.cast_zero] using
        (DirectedDistances.Paper.Section4.cond_walk_rn_law
          (0 : ℕ) (0 : ℤ)).2.1 k) m T hGraph

end DirectedDistances.PaperProofs.Section4
