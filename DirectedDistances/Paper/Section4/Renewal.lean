 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.Renewal

/-!
# Lemma 4.9 (`lem-renewal`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/


















public section
namespace DirectedDistances.Paper.Section4
open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk


theorem renewal (m : ℕ) :
    let T : (ℕ → ℤ × ℤ) → WithTop ℕ := renewalTime m
    let μf : Measure {p // T p < ⊤} := (conditionedVectorPathLaw 0 0).comap
      (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ))
    let history :=
      stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val)
    let future :=
      stoppedVectorFuture (finiteTimeIndex T) (fun ω => ω.val)
    condDistrib future history μf =ᵐ[μf.map history]
      Kernel.const (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)
        (conditionedVectorPathLaw 0 0) :=
 
by exact DirectedDistances.PaperProofs.Section4.renewal m
 
 

end DirectedDistances.Paper.Section4
 
