module

public import DirectedDistances.KMSW.M0CutUniversalFresh
public import DirectedDistances.KMSW.BoundaryVertexRange
public import DirectedDistances.KMSW.M0CutFaceSuccTransport

/-! Supporting lemmas for paper labels `thm-busemann` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW





theorem m0Cut_fresh_of_offSeam (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (v : ℕ)
    (hv : ∀ k : ℤ, v ≠ boundaryVertex (shiftedStream W 0) h0 k)
    (M : ℕ) (h : 0 ≤ M) : wholePlaneFresh W 0 M h v := by
  classical
  by_contra hn
  rcases (m0Cut_not_fresh_iff_seam W v M h).mp hn with hsmall | hseam
  · have hcases : v = 0 ∨ v = 1 := by omega
    rcases hcases with rfl | rfl
    · exact hv 0 (boundaryVertex_zero _ h0).symm
    · exact hv 1 (boundaryVertex_one _ h0).symm
  · obtain ⟨j, _, rfl, hdown | hleft⟩ := hseam
    · obtain ⟨hc, hUR, _⟩ := hdown
      obtain ⟨k, hk⟩ := stageLLLRVertex_eq_boundaryVertex
        (shiftedStream W 0) h0 (kmswStage (shiftedStream W 0) j).nextVertex (by
          refine ⟨j + 1, (kmswStage (shiftedStream W 0) j).nextEdge,
            Or.inr ?_, Or.inr ?_⟩
          · simp [kmswStage, kmswStep, hc, kmswStepOfStep, hUR, State.addEdge]
          · simp [kmswStage, kmswStep, hc, kmswStepOfStep, hUR, State.addEdge])
      exact hv k hk.symm
    · obtain ⟨hc, hUL, _⟩ := hleft
      obtain ⟨k, hk⟩ := stageLLLRVertex_eq_boundaryVertex
        (shiftedStream W 0) h0 (kmswStage (shiftedStream W 0) j).nextVertex (by
          refine ⟨j + 1, (kmswStage (shiftedStream W 0) j).nextEdge + 1,
            Or.inl ?_, Or.inl ?_⟩
          · simp [kmswStage, kmswStep, hc, kmswStepOfStep, hUL, State.addEdge]
          · simp [kmswStage, kmswStep, hc, kmswStepOfStep, hUL, State.addEdge])
      exact hv k hk.symm





theorem m0Cut_edgePresent_iff_offSeam (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (e : ℕ)
    (he : (∀ k : ℤ, edgeWest (shiftedStream W 0) e ≠
        boundaryVertex (shiftedStream W 0) h0 k) ∨
      (∀ k : ℤ, edgeEast (shiftedStream W 0) e ≠
        boundaryVertex (shiftedStream W 0) h0 k)) :
    EdgePresent (shiftedStream W 0) e ↔
      wholePlaneEdgePresent W (wholePlaneEdgeι W 0 e) := by
  rcases he with hw | he
  · exact m0Cut_edgePresent_iff_of_fresh W e false
      (fun M h => m0Cut_fresh_of_offSeam W h0 _ hw M h)
  · exact m0Cut_edgePresent_iff_of_fresh W e true
      (fun M h => m0Cut_fresh_of_offSeam W h0 _ he M h)





theorem m0Cut_faceSucc_offSeam (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (d : ℕ × Bool)
    (hd : ∀ k : ℤ,
      (if !d.2 then edgeEast (shiftedStream W 0) d.1
        else edgeWest (shiftedStream W 0) d.1) ≠
          boundaryVertex (shiftedStream W 0) h0 k) :
    wholePlaneFaceSucc W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d) := by
  exact m0Cut_faceSucc_runZero_of_fresh W H d
    (fun M h => m0Cut_fresh_of_offSeam W h0 _ hd M h)





theorem m0Cut_edgeMissing_iff_offSeam (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (e : ℕ)
    (he : (∀ k : ℤ, edgeWest (shiftedStream W 0) e ≠
        boundaryVertex (shiftedStream W 0) h0 k) ∨
      (∀ k : ℤ, edgeEast (shiftedStream W 0) e ≠
        boundaryVertex (shiftedStream W 0) h0 k)) :
    ¬ EdgePresent (shiftedStream W 0) e ↔
      ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W 0 e) := by
  exact not_congr (m0Cut_edgePresent_iff_offSeam W h0 e he)

end DirectedDistances.KMSW
