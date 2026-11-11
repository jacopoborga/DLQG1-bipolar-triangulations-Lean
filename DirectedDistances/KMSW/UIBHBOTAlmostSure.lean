module

public import DirectedDistances.KMSW.UIBHBOTRotationHypothesis
public import DirectedDistances.KMSW.UIBHBOTRelaxedCaptureAE
import DirectedDistances.RandomWalk.ExcursionBlockUniformTail





public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk MeasureTheory



theorem uibhbotWordFamilyLaw_ae_rotationHypothesis :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        WholePlaneRotationHypothesis (uibhbotCodeWord w (fun k => (hw k).1)) := by
  filter_upwards [uibhbotWordFamilyLaw_ae_hP2,
    ae_uibhbotConcatWalk_snd_unbounded_below] with w hP2 hP1
  obtain ⟨hw, hP2⟩ := hP2
  exact ⟨hw, uibhbotCodeWord_rotationHypothesis w hw hP1 hP2⟩



theorem uibhbotWordFamilyLaw_ae_finiteIncidence :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k), ∀ N : ℕ,
        KMSWFiniteIncidence (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) := by
  filter_upwards [uibhbotWordFamilyLaw_ae_rotationHypothesis] with w hrot
  obtain ⟨hw, hrot⟩ := hrot
  exact ⟨hw, hrot.1⟩



theorem uibhbotWordFamilyLaw_ae_cofinalFreshness :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        ∀ N v, ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
          wholePlaneFresh (uibhbotCodeWord w (fun k => (hw k).1)) M M' hMM'
            (wholePlaneVertexTrans (uibhbotCodeWord w (fun k => (hw k).1)) N M hNM v) := by
  filter_upwards [uibhbotWordFamilyLaw_ae_rotationHypothesis] with w hrot
  obtain ⟨hw, hrot⟩ := hrot
  exact ⟨hw, hrot.2⟩



theorem uibhbotWordFamilyLaw_ae_eventualWholePlaneBall :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k), ∀ r : ℕ,
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        ∃ N₀, ∀ N ≥ N₀,
          let c := activeInitial (shiftedStream W N) N
          let S := kmswStageBallVertices (fun _ _ => True)
            (kmswStage (shiftedStream W N) (2 * N)) r c
          kmswWindowCaptureEventStrongRel (shiftedStream W N) (2 * N) r c ∧
            (∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r c,
              minL (shiftedStream W N) k = L (shiftedStream W N) k) ∧
            wholePlaneBallVertices W r (wholePlaneVertexι W N c) =
              (wholePlaneVertexι W N) '' (S : Set ℕ) ∧
            Set.BijOn (fun e : Fin (kmswStage (shiftedStream W N) (2 * N)).nextEdge =>
              wholePlaneEdgeι W N e.val)
              {e | (kmswStage (shiftedStream W N) (2 * N)).west e.val ∈ S ∧
                (kmswStage (shiftedStream W N) (2 * N)).east e.val ∈ S}
              {e | wholePlaneEdgeWest W e ∈
                  wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
                wholePlaneEdgeEast W e ∈
                  wholePlaneBallVertices W r (wholePlaneVertexι W N c)} := by
  apply uibhbotWordFamilyLaw_ae_eventualWholePlaneBall_of_pos
  rw [uibhbotWordFamilyLaw_backwardRUnbounded]
  exact zero_lt_one

end DirectedDistances.KMSW
