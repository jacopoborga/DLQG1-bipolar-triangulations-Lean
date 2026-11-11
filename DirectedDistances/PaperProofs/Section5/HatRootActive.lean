module

public import DirectedDistances.KMSW.HatFaceVertices
public import DirectedDistances.PaperProofs.Section5.QuadrantWalk

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open Quiver

/-- The hatted limit maps fix the initial vertex and root edge -/
theorem hat_root_limit_maps (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    hatLimitEdgeMap w h 0 = 0 ∧ hatLimitVertexMap w h 0 = 0 := by
  have he : 0 < (kmswStage (hatCodes w h) 0).nextEdge := by
    simp [kmswStage, kmswInit]
  have hv : 0 < (kmswStage (hatCodes w h) 0).nextVertex := by
    simp [kmswStage, kmswInit]
  constructor
  · rw [hatLimitEdgeMap_eq_stage w h 0 0 he]
    rfl
  · rw [hatLimitVertexMap_eq_stage w h 0 0 hv]
    exact hatAllVertexMap_root w h 0

/-- The original and hatted root edges both run from vertex `0` to vertex
`1` (reading `edgeWest`/`edgeEast` as the tail/head of the directed edge) -/
theorem hat_root_edge_endpoints (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 ∧
      edgeWest (hatCodes w h) 0 = 0 ∧ edgeEast (hatCodes w h) 0 = 1 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The explicit edge equivalence sends the hatted root edge to the global
root edge, with its tail vertex `0` fixed (`lem-quad-kmsw`, -/
theorem hat_explicit_root_edge (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∃ hr : EdgePresent (hatCodes w h) 0,
      (hatExplicitEdgeEquiv w h ⟨0, hr⟩).1 = 0 ∧
      edgeWest w (hatExplicitEdgeEquiv w h ⟨0, hr⟩).1 = 0 := by
  have hr : EdgePresent (hatCodes w h) 0 := by
    refine ⟨0, ?_, ?_⟩
    · simp [kmswStage, kmswInit]
    · simp [kmswStage, kmswInit]
  refine ⟨hr, ?_, ?_⟩
  · rw [hatExplicitEdgeEquiv_apply, hat_root_limit_maps w h |>.1]
  · rw [hatExplicitEdgeEquiv_apply, hat_root_limit_maps w h |>.1,
      (hat_root_edge_endpoints w h).1]




theorem quadrantRStageTime_eq_sourceQuadrantS (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    quadrantRStageTime w h m = sourceQuadrantS w h m := by
  classical
  by_cases hm0 : m = 0
  · subst m
    rw [quadrantRStageTime_eq_of_initial_R w h]
    · exact (sourceQuadrantS_zero w h).symm
    · have hp := (walkNL_spec w h 0).1
      omega
  · have hm : 1 ≤ m := by omega
    have hpred : sourceQuadrantHatTime w = quadrantHatTime w := by
      funext n
      apply propext
      change (1 ≤ n ∧ sourceLambdaInMhat w n) ↔ quadrantHatTime w n
      constructor
      · rintro ⟨hn, hmem⟩
        exact ⟨hn, hmem.1⟩
      · rintro ⟨hn, hmem⟩
        exact ⟨hn,
          (sourceLambdaInMhat_iff_quadrantHatTime w n hn).mpr ⟨hn, hmem⟩⟩
    have hs := sourceQuadrantS_isLeast_count w h hm
    have hq := quadrantS_characterization w h hm
    have htime := quadrantS_eq_quadrantRStageTime w h hm
    have hcountR : Nat.count (sourceQuadrantHatTime w)
        (quadrantRStageTime w h m + 1) = m := by
      rw [← htime, hpred]
      exact hq.2.1
    have hsource_le : sourceQuadrantS w h m ≤ quadrantRStageTime w h m := by
      apply hs.2
      exact hcountR
    have hcountSource : Nat.count (quadrantHatTime w)
        (sourceQuadrantS w h m + 1) = m := by
      rw [← hpred]
      exact hs.1
    have htime_le : quadrantRStageTime w h m ≤ sourceQuadrantS w h m := by
      rw [← htime]
      exact hq.2.2 _ hcountSource
    exact Nat.le_antisymm htime_le hsource_le

/-- At every finite hatted stage, the local active edge maps to the global
active edge at the aligned R time (`lem-quad-kmsw`, -/
theorem hat_active_edge_stage_alignment (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    hatAllEdgeMap w h m ((kmswStage (hatCodes w h) m).active) =
      (kmswStage w (quadrantRStageTime w h m)).active := by
  exact (hatAll_sim w h m).incidenceSim.active






theorem hat_root_active_alignment (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    hatLimitEdgeMap w h 0 = 0 ∧
      hatLimitVertexMap w h 0 = 0 ∧
      edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 ∧
      edgeWest (hatCodes w h) 0 = 0 ∧ edgeEast (hatCodes w h) 0 = 1 ∧
      (∃ hr : EdgePresent (hatCodes w h) 0,
        (hatExplicitEdgeEquiv w h ⟨0, hr⟩).1 = 0 ∧
        edgeWest w (hatExplicitEdgeEquiv w h ⟨0, hr⟩).1 = 0) ∧
      (∀ m, hatAllEdgeMap w h m ((kmswStage (hatCodes w h) m).active) =
        (kmswStage w (quadrantRStageTime w h m)).active) ∧
      (∀ m, quadrantRStageTime w h m = sourceQuadrantS w h m) ∧
      (∀ m, hatLimitEdgeMap w h ((kmswStage (hatCodes w h) m).active) =
        act w (sourceQuadrantS w h m)) := by
  have hroot := hat_root_limit_maps w h
  have hend := hat_root_edge_endpoints w h
  refine ⟨hroot.1, hroot.2, hend.1, hend.2.1, hend.2.2.1, hend.2.2.2,
    hat_explicit_root_edge w h, ?_, ?_, ?_⟩
  · exact hat_active_edge_stage_alignment w h
  · intro m
    exact quadrantRStageTime_eq_sourceQuadrantS w h m
  · intro m
    rw [hatLimitEdgeMap_eq_stage w h m _
      (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) m).1,
      hat_active_edge_stage_alignment w h m,
      quadrantRStageTime_eq_sourceQuadrantS w h m]
    rfl

end DirectedDistances.PaperProofs.Section5
