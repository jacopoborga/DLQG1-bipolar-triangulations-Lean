module

public import DirectedDistances.KMSW.DirectedContain
import DirectedDistances.KMSW.StageSubgraph
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! Supporting lemmas for paper labels `lem-long-path` (see CORRESPONDENCE.md). -/






@[expose] public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW





theorem boundaryVertex_lt_stageNextVertex (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) (n : ℕ)
    (hn : boundaryHitTime w h k ≤ n) :
    boundaryVertex w h k < (kmswStage w n).nextVertex := by
  by_cases hk0 : k = 0
  ·
    subst k
    rw [boundaryVertex_zero]
    have hbound :=
      (kmswStage_endpoints_lt_nextVertex w 0 0 (initial_edge_present w 0).1).1
    rw [(initial_edge_endpoints w 0).1] at hbound
    exact hbound.trans_le (CutConverse.nextVertex_mono w (Nat.zero_le n))
  · by_cases hk1 : k = 1
    · subst k
      rw [boundaryVertex_one]
      have hbound :=
        (kmswStage_endpoints_lt_nextVertex w 0 0 (initial_edge_present w 0).1).2
      rw [(initial_edge_endpoints w 0).2] at hbound
      exact hbound.trans_le (CutConverse.nextVertex_mono w (Nat.zero_le n))
    · have hstable :=
        boundaryHit_activeInitial_stable_of_ne_zero w h hk0 (Nat.le_refl _)
      have hbound :=
        (kmswStage_endpoints_lt_nextVertex w (boundaryHitTime w h k)
          (act w (boundaryHitTime w h k))
          (act_lt_nextEdge w (Nat.le_refl _))).1
      rw [hstable] at hbound
      exact hbound.trans_le (CutConverse.nextVertex_mono w hn)





theorem activeInitial_lt_stageNextVertex (w : ℕ → Fin 3) {t n : ℕ} (htn : t ≤ n) :
    activeInitial w t < (kmswStage w n).nextVertex := by
  rw [CutConverse.activeInitial_eq]
  have hbound :=
    (kmswStage_endpoints_lt_nextVertex w t (act w t)
      (act_lt_nextEdge w (Nat.le_refl _))).1
  exact hbound.trans_le (CutConverse.nextVertex_mono w htn)

end DirectedDistances.PaperProofs.Section7
