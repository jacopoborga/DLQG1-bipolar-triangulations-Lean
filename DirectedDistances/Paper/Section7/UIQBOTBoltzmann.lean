 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIQBOTBoltzmann

/-!
# Lemma 7.9 (`lem-uiqbot-boltzmann`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/
























public section
namespace DirectedDistances.Paper.Section7

open MeasureTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4

 
theorem uiqbot_boltzmann :
    (∀ r : ℕ, ∀ hr : 1 ≤ r,
      (conditionedVectorPathLaw 0 0).map (stoppedMarked r hr) =
        rightVertexMarkedBoltzmannLaw r) ∧
    (∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let w := boltzmannKMSWStream (pathCode p)
      let t := (conditionedSecondCoordinateFirstHit r p).toNat
      let m := (stoppedMarked r hr p).2.val
      conditionedSecondCoordinateFirstHit r p < ⊤ ∧
      (∀ e < (kmswStage w (t - 1)).nextEdge, (kmswStage w (t - 1)).present e = true) ∧
      (kmswMap w (t - 1)).IsPlanar ∧
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        (∀ e < (kmswStage w (t - 1)).nextEdge, (kmswStage w (t - 1)).present e = true →
          EdgePresent w e ∧
          (kmswStage w (t - 1)).west e = edgeWest w e ∧
          (kmswStage w (t - 1)).east e = edgeEast w e ∧
          ∀ n, t - 1 ≤ n →
            e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true ∧
            (kmswStage w n).west e = (kmswStage w (t - 1)).west e ∧
            (kmswStage w n).east e = (kmswStage w (t - 1)).east e) ∧
        (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
          (∃ k : ℕ, 0 < k ∧
            (kmswInfRot w hfin ^ k) (d.1.val, d.2) =
              ((stageRot w (t - 1) d).1.val, (stageRot w (t - 1) d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w (t - 1)).nextEdge ≤
                ((kmswInfRot w hfin ^ j) (d.1.val, d.2)).1) ∧
          (∃ k : ℕ, 0 < k ∧
            ((kmswInfRot w hfin).symm ^ k) (d.1.val, d.2) =
              (((stageRot w (t - 1)).symm d).1.val, ((stageRot w (t - 1)).symm d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w (t - 1)).nextEdge ≤
                (((kmswInfRot w hfin).symm ^ j) (d.1.val, d.2)).1) ∧
          (∃ k : ℕ, 0 < k ∧
            ((kmswInfRot w hfin).symm ^ k) (d.1.val, !d.2) =
              (((kmswMap w (t - 1)).faceSucc d).1.val,
                ((kmswMap w (t - 1)).faceSucc d).2) ∧
            ∀ j : ℕ, 0 < j → j < k →
              (kmswStage w (t - 1)).nextEdge ≤
                (((kmswInfRot w hfin).symm ^ j) (d.1.val, !d.2)).1)) ∧
        (∃ W : CoherentRealizationWitness w hfin,
          ∃ Us : (W.Q (t - 1)).Face,
            (W.Q (t - 1)).IsUnbounded Us ∧
            StageLeftBoundaryVertex (W.Q (t - 1)) Us
              ((stoppedLeftBoundaryVertices w t).getD m 0) ∧
            TopLeftBoundaryVertex w W.P W.U
              ((stoppedLeftBoundaryVertices w t).getD m 0) ∧
            (∀ j, m < j → j ≤ (L w t).toNat →
              ¬ (StageLeftBoundaryVertex (W.Q (t - 1)) Us
                    ((stoppedLeftBoundaryVertices w t).getD j 0) ∧
                  TopLeftBoundaryVertex w W.P W.U
                    ((stoppedLeftBoundaryVertices w t).getD j 0)))) ∧
        ∃ (ht : 1 ≤ t) (ell : ℕ) (c : KMSWWalkClass ell r t),
          (∀ i : Fin (t - 1), c.val i = pathCode p (i.val + 1)) ∧
          (stoppedMarked r hr p).1 = ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ ∧
          Nonempty (DirectedMapWithMissingIso
            (kmswStageDirectedMap (codeExtend c) (t - 1))
            (kmswStageDirectedMap w (t - 1))) ∧
          (stageMapVertex (codeExtend c) (t - 1)
            ((kmswWalkClassRep_baseIso ht c).vertexEquiv
              ((kmswWalkClassRep ht c).B.leftPath.vertices.getD m
                (kmswWalkClassRep ht c).B.source))).id =
            (stoppedLeftBoundaryVertices w t).getD m 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - ε ≤ (conditionedVectorPathLaw 0 0).real {p | ∃ t : ℕ,
        (p t).2 = -(r : ℤ) ∧ (∀ j < t, (p j).2 ≠ -(r : ℤ)) ∧
        (r : ℝ) ^ 2 / A ≤
          ((kmswStage (boltzmannKMSWStream (pathCode p)) (t - 1)).nextEdge : ℝ) ∧
        ((kmswStage (boltzmannKMSWStream (pathCode p)) (t - 1)).nextEdge : ℝ) ≤
          A * (r : ℝ) ^ 2}) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.uiqbot_boltzmann
 
 

end DirectedDistances.Paper.Section7
 
