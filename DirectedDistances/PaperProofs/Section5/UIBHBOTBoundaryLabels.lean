module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBusemannDistanceApprox
public import DirectedDistances.RandomWalk.UIBHBOTBusemannIncrement

/-! The two-sided first-hit times have the source normalization and order. The existing
one-sided run labels do not have that normalization: their zeroth label is the
east endpoint of the missing root, whereas the source's zeroth label is its west
endpoint. No identification of these two label systems is assumed here. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.RandomWalk MeasureTheory



theorem ae_uibhbotBoundaryHitTime_isLeast :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      IsLeast {t : ℤ | (wholePlaneWordIntegral W t).1 = k}
        (uibhbotBoundaryHitTime k W) := by
  filter_upwards [ae_uibhbotBoundaryHit] with W h k
  refine ⟨(h k).1, ?_⟩
  intro s hs
  by_contra hn
  exact (h k).2 s (by omega) hs



theorem uibhbotBoundaryHitTime_concat_isLeast (w : ℤ → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) (k : ℤ) :
    IsLeast {t : ℤ | (uibhbotConcatWalk w t).1 = k}
      (uibhbotBoundaryHitTime k (uibhbotCodeWordRel w)) := by
  have h := uibhbotBoundaryHit_codeWordRel k w hw
  rw [← uibhbotBoundaryHitTime_codeWordRel k w hw] at h
  have he (t : ℤ) :
      wholePlaneWordIntegral (uibhbotCodeWordRel w) t = uibhbotConcatWalk w t := by
    rw [uibhbotCodeWordRel_eq w (fun j => (hw j).1)]
    exact wholePlaneWordIntegral_uibhbotCodeWord w (fun j => (hw j).1) t
  refine ⟨(congrArg Prod.fst (he _)).symm.trans h.1, ?_⟩
  intro s hs
  by_contra hn
  exact h.2 s (by omega) ((congrArg Prod.fst (he s)).trans hs)



theorem uibhbotBoundaryHitTime_codeWordRel_zero (w : ℤ → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) :
    uibhbotBoundaryHitTime 0 (uibhbotCodeWordRel w) = 0 := by
  rw [uibhbotBoundaryHitTime_codeWordRel 0 w hw, neg_zero,
    uibhbotBlockBoundary_zero]



theorem ae_uibhbotBoundaryHitTime_zero :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      uibhbotBoundaryHitTime 0 W = 0 := by
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
  apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable
    (measurableSet_eq_fun (measurable_uibhbotBoundaryHitTime 0)
      measurable_const)).mpr
  filter_upwards [ae_uibhbotWordFamily_all_stopped] with w hw
  exact uibhbotBoundaryHitTime_codeWordRel_zero w hw



theorem ae_uibhbotBoundaryHitTime_strictAnti :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      StrictAnti (fun k : ℤ => uibhbotBoundaryHitTime k W) := by
  filter_upwards [ae_uibhbotBoundaryHit, ae_uibhbotBoundaryHit_strictRecord]
    with W hh hr a b hab
  change uibhbotBoundaryHitTime b W < uibhbotBoundaryHitTime a W
  by_contra hn
  have hle : uibhbotBoundaryHitTime a W ≤ uibhbotBoundaryHitTime b W := by omega
  rcases hle.eq_or_lt with he | hl
  · have ha := (hh a).1
    rw [he, (hh b).1] at ha
    omega
  · have h := hr b (uibhbotBoundaryHitTime a W) hl
    rw [(hh a).1] at h
    omega



theorem uibhbotBoundaryVertex_zero (W : ℤ → Fin 3) :
    uibhbotBoundaryVertex W 0 = wholePlaneVertexι W 1 0 := by
  simp [uibhbotBoundaryVertex, uibhbotBoundaryId,
    DirectedDistances.Recursive.busemannBoundaryIdTotal,
    DirectedDistances.Recursive.boundaryHitTimeTotal, kmswStage, kmswInit]



theorem ae_uibhbotBoundary_creatingLetter_zero :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), W (-1) = 0 := by
  filter_upwards [ae_uibhbotBoundaryHitTime_zero, ae_uibhbotBoundaryHit_strictRecord]
    with W hz hr
  have h := hr 0 (-1) (by rw [hz]; omega)
  have hi : (wholePlaneWordIntegral W (-1)).1 =
      -(lazyTwoDimensionalStep (W (-1))).1 := by
    simp [wholePlaneWordIntegral]
  rw [hi] at h
  apply Fin.ext
  change (W (-1)).val = 0
  change 0 < -((W (-1) : ℤ) - 1) at h
  omega



theorem uibhbotRootEdge_west_of_creatingLetter (W : ℤ → Fin 3)
    (hW : W (-1) = 0) :
    wholePlaneEdgeWest W (uibhbotRootEdge W) = wholePlaneVertexι W 1 2 := by
  rw [uibhbotRootEdge, wholePlaneEdgeWest_ι]
  have hb : kmswLLCreatedEdge (shiftedStream W 1) 1 <
      (kmswStage (shiftedStream W 1) 1).nextEdge := by
    simp [kmswLLCreatedEdge, kmswStage, shiftedStream, hW, kmswStep,
      kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  rw [← (edge_endpoints_eq (shiftedStream W 1) hb).1]
  simp [kmswLLCreatedEdge, kmswStage, shiftedStream, hW, kmswStep,
    kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]



theorem uibhbotRootEdge_east_eq_boundaryVertex_zero (W : ℤ → Fin 3)
    (hW : W (-1) = 0) :
    wholePlaneEdgeEast W (uibhbotRootEdge W) = uibhbotBoundaryVertex W 0 := by
  rw [uibhbotBoundaryVertex_zero, uibhbotRootEdge, wholePlaneEdgeEast_ι]
  have hb : kmswLLCreatedEdge (shiftedStream W 1) 1 <
      (kmswStage (shiftedStream W 1) 1).nextEdge := by
    simp [kmswLLCreatedEdge, kmswStage, shiftedStream, hW, kmswStep,
      kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  rw [← (edge_endpoints_eq (shiftedStream W 1) hb).2]
  simp [kmswLLCreatedEdge, kmswStage, shiftedStream, hW, kmswStep,
    kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]



theorem uibhbotRootEdge_west_ne_boundaryVertex_zero (W : ℤ → Fin 3)
    (hW : W (-1) = 0) :
    wholePlaneEdgeWest W (uibhbotRootEdge W) ≠ uibhbotBoundaryVertex W 0 := by
  rw [uibhbotRootEdge_west_of_creatingLetter W hW, uibhbotBoundaryVertex_zero]
  intro h
  have he := wholePlaneVertexι_injective W 1 h
  omega




theorem uibhbotBusemannSource_zero_eq_root_west (W : ℤ → Fin 3)
    (ht : uibhbotBoundaryHitTime 0 W = 0) (hW : W (-1) = 0) :
    (uibhbotBusemannSource 0 W).id = wholePlaneEdgeWest W (uibhbotRootEdge W) := by
  rw [uibhbotRootEdge_west_of_creatingLetter W hW]
  change lemma38StartVertexι W (uibhbotBoundaryHitTime 0 W) 0 = _
  rw [ht]
  have h := uibhbotStartVertex_activeInitial W (-1) 1
  have ha : activeInitial (lemma38StartStream W (-1)) 1 = 2 := by
    rw [CutConverse.activeInitial_eq]
    simp [act, kmswStage, lemma38StartStream, hW, kmswStep,
      kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  rw [ha] at h
  simpa only [lemma38StartVertexι, show (-1 : ℤ) ≤ 0 by omega,
    ite_true, Int.natAbs_neg, Int.natAbs_one, show (-1 : ℤ) + (1 : ℕ) = 0 by omega]
    using h.symm




theorem ae_uibhbotBusemannSource_zero_ne_boundaryVertex :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      (uibhbotBusemannSource 0 W).id ≠ uibhbotBoundaryVertex W 0 := by
  filter_upwards [ae_uibhbotBoundaryHitTime_zero,
    ae_uibhbotBoundary_creatingLetter_zero] with W ht hW
  rw [uibhbotBusemannSource_zero_eq_root_west W ht hW]
  exact uibhbotRootEdge_west_ne_boundaryVertex_zero W hW



theorem ae_uibhbotRootEdge_runLabel_zero_endpoints :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      wholePlaneEdgeEast W (uibhbotRootEdge W) = uibhbotBoundaryVertex W 0 ∧
      wholePlaneEdgeWest W (uibhbotRootEdge W) ≠ uibhbotBoundaryVertex W 0 := by
  filter_upwards [ae_uibhbotBoundary_creatingLetter_zero] with W hW
  exact ⟨uibhbotRootEdge_east_eq_boundaryVertex_zero W hW,
    uibhbotRootEdge_west_ne_boundaryVertex_zero W hW⟩





theorem ae_uibhbotBoundaryLabels_root_obstruction :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ¬ ∃ e : ℤ → WholePlaneEdge W,
        wholePlaneEdgeWest W (e 0) = uibhbotBoundaryVertex W 0 ∧
        e 0 = uibhbotRootEdge W := by
  filter_upwards [ae_uibhbotRootEdge_runLabel_zero_endpoints] with W h
  rintro ⟨e, hw, he⟩
  rw [he] at hw
  exact h.2 hw

end DirectedDistances.PaperProofs.Section5
