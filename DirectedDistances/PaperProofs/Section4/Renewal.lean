/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section4.RenewalTimeCharacterization
public import DirectedDistances.PaperProofs.Section4.RenewalRegenerationLaw

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.Section4
open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk

 
theorem renewal (m : ℕ) :
    let T : (ℕ → ℤ × ℤ) → WithTop ℕ := Paper.Section4.renewalTime m
    let μf : Measure {p // T p < ⊤} := (conditionedVectorPathLaw 0 0).comap
      (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ))
    let history :=
      stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val)
    let future :=
      stoppedVectorFuture (finiteTimeIndex T) (fun ω => ω.val)
    condDistrib future history μf =ᵐ[μf.map history]
      Kernel.const (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)
        (conditionedVectorPathLaw 0 0) :=
  conditionedVectorPathLaw_selector_regeneration m (Paper.Section4.renewalTime m)
    (fun p => (Paper.Section4.renewalTime_characterization m p).1)

end DirectedDistances.PaperProofs.Section4
