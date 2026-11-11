 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BipolarBoundaryDefinition

/-!
# Definition 1.9 (`def-bipolar-bdy`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/

















public section
namespace DirectedDistances.Paper.Section1

open DirectedDistances.PlanarMap

 
theorem def_bipolar_bdy {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (ℓ r : ℕ) :
    (IsBipolarMapWithBoundary M ℓ r ↔
      (1 ≤ ℓ ∧ 1 ≤ r) ∧
      M.toCombinatorialMap.IsPlanar ∧
      M.IsAcyclic ∧
      (∀ d, ¬ M.missing d) ∧
      ∃ s t : MapVertex M,
        (¬ ∃ u, M.directedStep u s) ∧
        (∀ v, (¬ ∃ u, M.directedStep u v) → v = s) ∧
        (¬ ∃ w, M.directedStep t w) ∧
        (∀ v, (¬ ∃ w, M.directedStep v w) → v = t) ∧
        ∃ W : NonemptyWord D,
        ∃ Pℓ : SimpleDirectedDartPath M s t ℓ,
        ∃ Pr : SimpleDirectedDartPath M s t r,
          FourArcsWitness M W Pℓ.darts []
            (Pr.darts.reverse.map M.toCombinatorialMap.edgeInv) []) ∧
    (IsBipolarMapWithBoundary M ℓ r ↔
      HasIntrinsicBipolarBoundary M ℓ r ∧ 1 ≤ ℓ ∧ 1 ≤ r) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_bipolar_bdy_provider M ℓ r
 
 

end DirectedDistances.Paper.Section1
 
