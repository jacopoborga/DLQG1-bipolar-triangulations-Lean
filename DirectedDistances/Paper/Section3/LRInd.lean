 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.LRIndConcrete

/-!
# Lemma 3.15 (`lem-lr-ind`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/




























public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.PlanarMap
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory



theorem lr_ind {x : XDP} {ℓ s r : ℕ}
    (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (hF : 0 < boltzmannLaw ℓ r
      (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
      (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2
      (boltzmannFiber (ℓ := ℓ) (r := r) x s)) :
    ∃ default :
      {mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR},
      ProbabilityTheory.IndepFun
        (Subtype.val ∘ lrCutLeftClass (lrCutGlueRepData x ℓ s r) default)
        (Subtype.val ∘ lrCutRightClass (lrCutGlueRepData x ℓ s r) default)
        ((boltzmannLaw ℓ r
          (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
          (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) :=
 
by exact DirectedDistances.PlanarMap.lem_lr_ind hℓ hr hF
 
 

end DirectedDistances.Paper.Section3
 
