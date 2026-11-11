module

public import DirectedDistances.PaperProofs.Section4.ThinMapSeamSeparation
public import DirectedDistances.PaperProofs.Section4.ThinMapSideCarrier
public import DirectedDistances.KMSW.StageOuterCycle
import DirectedDistances.KMSW.InfiniteTriangulation
import DirectedDistances.PlanarMap.PlanarPathCutHalves
import DirectedDistances.PlanarMap.PlanarPathCutLeftmostRegion

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/



























public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (B : ThinMapBoundaryRays w hfin)

private theorem boundary_not_period_three {d : ℕ × Bool}
    (hd : d ∈ Set.range B.left ∪ Set.range B.right) :
    kmswInfFaceSucc w hfin
      (kmswInfFaceSucc w hfin (kmswInfFaceSucc w hfin d)) ≠ d := by
  rcases hd with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · intro h
    rw [B.left_step i, B.left_step (i + 1), B.left_step (i + 1 + 1)] at h
    have hi := B.left_injective h
    omega
  · intro h
    have hback : kmswInfFaceSucc w hfin
        (kmswInfFaceSucc w hfin (kmswInfFaceSucc w hfin (B.right (i + 3)))) =
        B.right i := by
      rw [show i + 3 = (i + 2) + 1 by omega, B.right_step (i + 2),
        show i + 2 = (i + 1) + 1 by omega, B.right_step (i + 1), B.right_step i]
    have heq := (kmswInfFaceSucc w hfin).injective
      ((kmswInfFaceSucc w hfin).injective
        ((kmswInfFaceSucc w hfin).injective (hback.trans h.symm)))
    have hi := B.right_injective heq
    omega







theorem thinMapBoundary_not_mem_stageTriangle {d : ℕ × Bool}
    (hd : d ∈ Set.range B.left ∪ Set.range B.right) (j : TriangleCreationTime w) :
    d ∉ stageTriangleDartList w j := by
  intro htriangle
  have hcycle := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  obtain ⟨h12, h23, h31, _⟩ := hcycle
  have hperiod : kmswInfFaceSucc w hfin
      (kmswInfFaceSucc w hfin (kmswInfFaceSucc w hfin d)) = d := by
    rcases List.mem_cons.mp htriangle with h | h
    · subst d
      rw [h12, h23, h31]
    · rcases List.mem_cons.mp h with h | h
      · subst d
        rw [h23, h31, h12]
      · rcases List.mem_cons.mp h with h | h
        · subst d
          rw [h31, h12, h23]
        · exact (List.not_mem_nil h).elim
  exact boundary_not_period_three w hfin B hd hperiod







theorem thinMapBoundary_mem_stageOuterWord (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : (d.1.val, d.2) ∈ Set.range B.left ∪ Set.range B.right) :
    d ∈ stageOuterWord w n := by
  rcases stage_dart_partition w n d with houter | ⟨j, ⟨_, htriangle⟩, _⟩
  · exact houter
  · exact (thinMapBoundary_not_mem_stageTriangle w hfin B hd j htriangle).elim

private theorem stageVal_injective (k : ℕ) :
    Function.Injective (fun d : StageDart k => (d.1.val, d.2)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  obtain ⟨he, hb⟩ := Prod.mk.inj h
  cases Fin.ext he
  cases hb
  rfl







theorem thinMapStage_faceSucc_eq_infinite_of_not_outer (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (hd : d ∉ stageOuterWord w n) :
    (((kmswMap w n).faceSucc d).1.val, ((kmswMap w n).faceSucc d).2) =
      kmswInfFaceSucc w hfin (d.1.val, d.2) := by
  obtain ⟨j, ⟨hj, htriangle⟩, _⟩ := (stage_dart_partition w n d).resolve_left hd
  obtain ⟨hs12, hs23, hs31, _⟩ := stageTriangle_isFace w j n hj
  obtain ⟨hi12, hi23, hi31, _⟩ := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  have hval₁ : ((stageTriangleDart₁ w n j hj).1.val,
      (stageTriangleDart₁ w n j hj).2) = (stageTriangleDartTriple w j).1 := rfl
  have hval₂ : ((stageTriangleDart₂ w n j hj).1.val,
      (stageTriangleDart₂ w n j hj).2) = (stageTriangleDartTriple w j).2.1 := rfl
  have hval₃ : ((stageTriangleDart₃ w n j hj).1.val,
      (stageTriangleDart₃ w n j hj).2) = (stageTriangleDartTriple w j).2.2 := rfl
  rcases List.mem_cons.mp htriangle with h | h
  · have hd₁ : d = stageTriangleDart₁ w n j hj :=
      stageVal_injective _ (h.trans hval₁.symm)
    rw [hd₁, hs12, hval₁, hval₂, hi12]
  · rcases List.mem_cons.mp h with h | h
    · have hd₂ : d = stageTriangleDart₂ w n j hj :=
        stageVal_injective _ (h.trans hval₂.symm)
      rw [hd₂, hs23, hval₂, hval₃, hi23]
    · rcases List.mem_cons.mp h with h | h
      · have hd₃ : d = stageTriangleDart₃ w n j hj :=
          stageVal_injective _ (h.trans hval₃.symm)
        rw [hd₃, hs31, hval₃, hval₁, hi31]
      · exact (List.not_mem_nil h).elim







theorem thinMapStageSideStep_iff_of_not_outer
    (P : InfinitePresentPath w ⟨0⟩) (side : ThinMapSide) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge) (hd : d ∉ stageOuterWord w n) :
    thinMapStageSideStep w hfin P B side n d e ↔
      thinMapSideStep w hfin P B side (d.1.val, d.2) (e.1.val, e.2) := by
  have hboundary : (d.1.val, d.2) ∉ Set.range B.left ∪ Set.range B.right :=
    fun h => hd (thinMapBoundary_mem_stageOuterWord w hfin B n d h)
  have hface := thinMapStage_faceSucc_eq_infinite_of_not_outer w hfin n d hd
  constructor
  · rintro (⟨rfl, _⟩ | ⟨rfl, hseam⟩)
    · exact Or.inl ⟨hface, Or.inl hboundary⟩
    · exact Or.inr ⟨rfl, hseam⟩
  · rintro (⟨he, _⟩ | ⟨he, hseam⟩)
    · exact Or.inl ⟨stageVal_injective _ (he.trans hface.symm), Or.inl hboundary⟩
    · exact Or.inr ⟨stageVal_injective _ he, hseam⟩

end DirectedDistances.PaperProofs.Section4
