module

public import DirectedDistances.KMSW.WholePlaneFreshness
public import DirectedDistances.KMSW.BoundaryLabelling

/-! Supporting lemmas for paper labels `thm-busemann` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW







theorem m0Cut_not_fresh_iff_seam (W : ℤ → Fin 3) (v M : ℕ) (h : 0 ≤ M) :
    ¬ wholePlaneFresh W 0 M h v ↔
      v < 2 ∨ ∃ j < 4 * v + 1,
        v = (kmswStage (shiftedStream W 0) j).nextVertex ∧
          ((kmswCodeStep (shiftedStream W 0 j) = .down ∧
              (kmswStage (shiftedStream W 0) j).UR = [] ∧
              (kmswWindowPatchData (shiftedStream W M) M j).B ≠ []) ∨
            (kmswCodeStep (shiftedStream W 0 j) = .left ∧
              (kmswStage (shiftedStream W 0) j).UL.dropLast.reverse = [] ∧
              (kmswWindowPatchData (shiftedStream W M) M j).A.reverse ≠ [])) := by
  simpa only [Nat.sub_zero] using wholePlaneFresh_iff_windowSeam W 0 M h v







theorem m0Cut_down_seam_prefix (W : ℤ → Fin 3) :
    W (-1) = 1 → W 0 = 2 →
      (kmswStage (shiftedStream W 1) 1).nextVertex = 3 ∧
        wholePlaneVertexTrans W 0 1 (by omega) 2 = 1 ∧
        ¬ wholePlaneFresh W 0 1 (by omega) 2 := by
  intro hp hzero
  have halloc : 2 <
      (kmswStage (fun i => shiftedStream W 1 (1 + i)) 1).nextVertex := by
    simp [kmswStage, kmswStep, kmswCodeStep, shiftedStream, hzero,
      kmswStepOfStep, kmswInit, State.addEdge]
  have hmap : wholePlaneVertexTrans W 0 1 (by omega) 2 = 1 := by
    change kmswWindowVertexMapInf (shiftedStream W 1) 1 2 = 1
    rw [kmswWindowVertexMapInf_eq_stage (shiftedStream W 1) 1 1 2 halloc]
    simp [kmswWindowPatchVertexMap, kmswWindowPatchData, shiftedStream,
      kmswStage, kmswStep, kmswCodeStep, hp, hzero, kmswStepOfStep,
      kmswInit, State.addEdge]
  have hnext : (kmswStage (shiftedStream W 1) 1).nextVertex = 3 := by
    simp [kmswStage, kmswStep, kmswCodeStep, shiftedStream, hp,
      kmswStepOfStep, kmswInit, State.addEdge]
  refine ⟨hnext, hmap, ?_⟩
  unfold wholePlaneFresh
  rw [Nat.sub_zero, hnext, hmap]
  omega







theorem m0Cut_offLeft_not_fresh_prefix (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) :
    W (-1) = 1 → W 0 = 2 → W 1 = 2 →
      (∀ k : ℤ, k ≤ 1 → (2 : ℕ) ≠ boundaryVertex (shiftedStream W 0) h0 k) ∧
        ¬ wholePlaneFresh W 0 1 (by omega) 2 := by
  intro hp hzero hone
  have htime : boundaryHitTime (shiftedStream W 0) h0 2 = 2 := by
    unfold boundaryHitTime
    simp only [show (2 : ℤ) ≠ 0 by omega, show (0 : ℤ) < 2 by omega,
      ↓reduceDIte]
    apply (Nat.find_eq_iff _).mpr
    constructor
    · simp [R, Finset.sum_range_succ, shiftedStream, hzero, hone,
        RandomWalk.lazyTwoDimensionalStep]
    · intro n hn
      have hcases : n = 0 ∨ n = 1 := by omega
      rcases hcases with rfl | rfl <;>
        simp [R, shiftedStream, hzero,
          RandomWalk.lazyTwoDimensionalStep]
  have hvertex : boundaryVertex (shiftedStream W 0) h0 2 = 2 := by
    rw [boundaryVertex_right_hit_eq _ h0 (by omega : (1 : ℤ) ≤ 2), htime,
      CutConverse.activeInitial_eq]
    simp [act, kmswStage, kmswStep, kmswCodeStep, shiftedStream,
      hzero, hone, kmswStepOfStep, kmswInit, State.addEdge]
  refine ⟨?_, (m0Cut_down_seam_prefix W hp hzero).2.2⟩
  intro k hk heq
  have hindex := boundaryVertex_injective (shiftedStream W 0) h0
    (hvertex.trans heq)
  omega

end DirectedDistances.KMSW
