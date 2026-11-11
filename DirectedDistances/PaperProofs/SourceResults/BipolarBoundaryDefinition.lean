/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarOuterDecomposition

/-! Supporting lemmas for paper labels `def-bipolar`, `def-bipolar-bdy` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]






theorem def_bipolar_bdy_provider (M : DirectedMapWithMissing D) (ℓ r : ℕ) :
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
      HasIntrinsicBipolarBoundary M ℓ r ∧ 1 ≤ ℓ ∧ 1 ≤ r) := by
  constructor
  · exact isBipolarMapWithBoundary_iff M ℓ r
  · constructor
    · intro h
      have hIntrinsic := (isBipolarMapWithBoundary_iff_intrinsic M ℓ r).mp h
      have hFields := (isBipolarMapWithBoundary_iff M ℓ r).mp h
      exact ⟨hIntrinsic, hFields.1.1, hFields.1.2⟩
    · rintro ⟨hIntrinsic, _, _⟩
      exact (isBipolarMapWithBoundary_iff_intrinsic M ℓ r).mpr
        hIntrinsic

end DirectedDistances.PaperProofs.SourceResults
