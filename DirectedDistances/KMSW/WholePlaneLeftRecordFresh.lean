module

public import DirectedDistances.KMSW.WholePlaneCofinalFreshness
public import DirectedDistances.KMSW.UIBHBOTWholePlaneWord




public section
namespace DirectedDistances.KMSW

private theorem kmswStage_allocates (w : ℕ → Fin 3) (k : ℕ)
    (h : (kmswCodeStep (w k) = .down ∧ (kmswStage w k).UR = []) ∨
      (kmswCodeStep (w k) = .left ∧
        (kmswStage w k).UL.dropLast.reverse = [])) :
    (kmswStage w k).nextVertex < (kmswStage w (k + 1)).nextVertex := by
  rcases h with hdown | hleft
  · rcases hdown with ⟨hc, hu⟩
    simp [kmswStage, kmswStep, hc, kmswStepOfStep, hu, State.addEdge]
  · rcases hleft with ⟨hc, hs⟩
    have hdrop : (kmswStage w k).UL.dropLast = [] :=
      List.reverse_eq_nil_iff.mp hs
    simp [kmswStage, kmswStep, hc, kmswStepOfStep, hdrop, State.addEdge]



theorem kmswCreationStage_unique (w : ℕ → Fin 3) (u k j : ℕ)
    (hku : (kmswStage w k).nextVertex = u)
    (hk : (kmswCodeStep (w k) = .down ∧ (kmswStage w k).UR = []) ∨
      (kmswCodeStep (w k) = .left ∧
        (kmswStage w k).UL.dropLast.reverse = []))
    (hju : (kmswStage w j).nextVertex = u)
    (hj : (kmswCodeStep (w j) = .down ∧ (kmswStage w j).UR = []) ∨
      (kmswCodeStep (w j) = .left ∧
        (kmswStage w j).UL.dropLast.reverse = [])) :
    j = k := by
  have hallocK := kmswStage_allocates w k hk
  have hallocJ := kmswStage_allocates w j hj
  by_contra hne
  have hlt : k < j ∨ j < k := by omega
  rcases hlt with hlt | hlt
  · have hmono := CutConverse.nextVertex_mono w
      (show k + 1 ≤ j by omega)
    have hlt' : u < (kmswStage w j).nextVertex := by
      rw [← hku]
      exact hallocK.trans_le hmono
    omega
  · have hmono := CutConverse.nextVertex_mono w
      (show j + 1 ≤ k by omega)
    have hlt' : u < (kmswStage w k).nextVertex := by
      rw [← hju]
      exact hallocJ.trans_le hmono
    omega

end DirectedDistances.KMSW
