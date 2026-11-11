 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.FiltrationMonoAnchor

/-!
# Lemma 4.15 (`lem-filtration-mono`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/























public section
namespace DirectedDistances.Paper.Section4

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section4





theorem filtration_mono (x : DirectedDistances.PlanarMap.XDP) :
    MeasurableSet (selectedCutCoherentDomain x (fun m p => renewalTime m p)
      (fun p m => And.left (renewalTime_characterization m p))) ∧
    conditionedVectorPathLaw 0 0 (selectedCutCoherentDomain x (fun m p => renewalTime m p)
      (fun p m => And.left (renewalTime_characterization m p)))ᶜ = 0 ∧
    (∀ k K, 1 ≤ k → k ≤ K →
      MeasurableSpace.comap (Subtype.val : selectedCutCoherentDomain x
          (fun m p => renewalTime m p)
          (fun p m => And.left (renewalTime_characterization m p)) → (ℕ → ℤ × ℤ))
        (sourceCutFiltration x K) ≤
      MeasurableSpace.comap Subtype.val (sourceCutFiltration x k)) ∧
    (∀ A : Set (selectedCutCoherentDomain x (fun m p => renewalTime m p)
        (fun p m => And.left (renewalTime_characterization m p))),
      MeasurableSet[⨅ j : ℕ, MeasurableSpace.comap Subtype.val
        (sourceCutFiltration x (j + 1))] A →
      ((conditionedVectorPathLaw 0 0).comap Subtype.val) A = 0 ∨
        ((conditionedVectorPathLaw 0 0).comap Subtype.val) A = 1) ∧
    (∀ A : Set (ℕ → ℤ × ℤ),
      MeasurableSet[⨅ j : ℕ, sourceCutFiltration x (j + 1)] A →
      conditionedVectorPathLaw 0 0 A = 0 ∨ conditionedVectorPathLaw 0 0 A = 1) ∧
    (∀ k K, 1 ≤ k → k ≤ K → ∀ A,
      MeasurableSet[sourceCutFiltration x K] A →
      ∃ B, MeasurableSet[sourceCutFiltration x k] B ∧
        A =ᵐ[conditionedVectorPathLaw 0 0] B) :=
 
by exact DirectedDistances.PaperProofs.Section4.filtration_mono_source x
 
 

end DirectedDistances.Paper.Section4
 
