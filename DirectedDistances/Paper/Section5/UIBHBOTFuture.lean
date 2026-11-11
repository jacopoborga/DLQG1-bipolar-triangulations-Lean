 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIBHBOTFutureLemma510Provider

/-!
# Lemma 5.10 (`lem-uihbot-future`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/





















public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section5

 
theorem lem_uihbot_future :
    (∃ Y : (ℕ → Fin 3) → GeometricSideClass,
      Measurable Y ∧
      (∀ᵐ w ∂iidCodeMeasure,
        ∃ (hb : BoundaryHitWitnesses (fun i => w (i + 1)))
          (hf : KMSWFiniteIncidence (fun i => w (i + 1))),
          Y w = geometricSideClass (kmswCodeGeometricSide w hb hf)) ∧
      ∀ k : ℤ, ∃ X : (ℤ → Fin 3) → GeometricSideClass,
        AEMeasurable X (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) ∧
        (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
          ∃ (hb : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
            (H : WholePlaneRotationHypothesis W)
            (_hf : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1))),
            X W = geometricSideClass
              (uibhbotFutureInducedPlaneGeometricSide k W hb H)) ∧
        (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map X = iidCodeMeasure.map Y) ∧
    (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k l : ℤ, l ≤ k →
        ∀ v : ℕ → UIBHBOTPresentVertex W,
          v 0 = uibhbotBusemannSource l W →
            ∀ a : ∀ n : ℕ, v n ⟶ v (n + 1),
              ∃ h : BoundaryHitWitnesses
                  (fun i => uibhbotFutureCode k W (i + 1)),
                ∃ u : ℕ → PresentVertex
                    (fun i => uibhbotFutureCode k W (i + 1)),
                ∃ e : ∀ n, u n ⟶ u (n + 1),
                  u 0 = ⟨boundaryVertex
                    (fun i => uibhbotFutureCode k W (i + 1)) h (l - k)⟩ ∧
                  (∀ n, (uibhbotFutureToGlobal k W).obj (u n) = v n) ∧
                  (∀ n, ((uibhbotFutureToGlobal k W).map (e n)).val =
                    (a n).val) ∧
                  (∀ n, (v n).id ∈ (uibhbotFutureSubmap k W h).vertices) ∧
                  (∀ n, (a n).val ∈ (uibhbotFutureSubmap k W h).edges)) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_uihbot_future_source_provider
 
 

end DirectedDistances.Paper.Section5
 
