module

public import DirectedDistances.KMSW.PathSpaceTransfer
public import DirectedDistances.KMSW.AllocatedVertices








public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory Quiver DirectedDistances.RandomWalk
open scoped Classical

/-- The left outer boundary is an injective chain of present directed edges -/
theorem kmswLeftBoundary_infinite_present_path (w : ℕ → Fin 3)
    (htrans : Tendsto (L w) atTop atTop) (hL : ∀ j, 0 ≤ L w j)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    Function.Injective (kmswLeftBoundaryEdge w) ∧
      (∀ i, edgeEast w (kmswLeftBoundaryEdge w i) =
        edgeWest w (kmswLeftBoundaryEdge w (i + 1))) ∧
      edgeWest w (kmswLeftBoundaryEdge w 0) = 0 ∧
      (∀ i, EdgePresent w (kmswLeftBoundaryEdge w i)) := by
  have hinj : Function.Injective (kmswLeftBoundaryEdge w) := by
    intro i j hij
    have ht := CutConverse.act_injective w hij
    have hi := (natSelect_spec (left_record_infinite w htrans) i).2
    have hj := (natSelect_spec (left_record_infinite w htrans) j).2
    exact hi.symm.trans ((congrArg
      (Nat.count (fun m => ∀ k, m < k → L w m + 1 ≤ L w k)) ht).trans hj)
  have hstep : ∀ i, edgeEast w (kmswLeftBoundaryEdge w i) =
      edgeWest w (kmswLeftBoundaryEdge w (i + 1)) := by
    intro i
    obtain ⟨N₁, h₁⟩ := kmswStage_UL_getElem?_eventually w htrans i
    obtain ⟨N₂, h₂⟩ := kmswStage_UL_getElem?_eventually w htrans (i + 1)
    let n := max N₁ N₂
    obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp (h₁ n (le_max_left _ _))
    obtain ⟨hi', hv'⟩ := List.getElem?_eq_some_iff.mp (h₂ n (le_max_right _ _))
    have hc := (kmswStage_boundary_chain_invariant w n).1.left_of_append
    have hr := hc.getElem i hi'
    rw [hv, hv'] at hr
    have hb (k : ℕ) (hk : k < (kmswStage w n).UL.length) :=
      (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl (List.getElem_mem hk))))
    have he := edge_endpoints_eq w (hb i hi)
    have he' := edge_endpoints_eq w (hb (i + 1) hi')
    rw [hv] at he
    rw [hv'] at he'
    exact he.2.symm.trans (hr.trans he'.1)
  have hzero : edgeWest w (kmswLeftBoundaryEdge w 0) = 0 := by
    obtain ⟨N₁, h₁⟩ := kmswStage_UL_getElem?_eventually w htrans 0
    obtain ⟨N₂, h₂⟩ := kmswStage_LR_getElem?_eventually w hR 0
    let n := max N₁ N₂
    have hu := h₁ n (le_max_left _ _)
    have hr := h₂ n (le_max_right _ _)
    have hs := (kmswStage_boundary_chain_invariant w n).2.2.1
    rw [kmswStage_LL_eq_nil w hL n, List.nil_append] at hs
    have huhead : (kmswStage w n).UL.head? = some (kmswLeftBoundaryEdge w 0) := by
      simpa only [List.head?_eq_getElem?] using hu
    have hrhead : (kmswStage w n).LR.head? = some (kmswRightBoundaryEdge w 0) := by
      simpa only [List.head?_eq_getElem?] using hr
    have hune : (kmswStage w n).UL ≠ [] := by
      intro h
      simp only [h, List.head?_nil] at huhead
      contradiction
    simp only [boundaryStart, List.head?_append_of_ne_nil _ hune, huhead, hrhead,
      Option.map_some] at hs
    have hs' := Option.some.inj hs
    obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hu
    obtain ⟨hj, hjv⟩ := List.getElem?_eq_some_iff.mp hr
    have he := edge_endpoints_eq w
      ((kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl (List.getElem_mem hi)))))
    have he' := edge_endpoints_eq w
      ((kmswStage_boundary_ids_lt_nextEdge w n).2 _
        (List.mem_append_right _ (List.getElem_mem hj)))
    rw [hv] at he
    rw [hjv] at he'
    exact he.1.symm.trans (hs'.trans (he'.1.trans
      (kmswRightBoundary_infinite_path w hL hR).2.2.1))
  refine ⟨hinj, hstep, hzero, fun i => ?_⟩
  obtain ⟨N, hN⟩ := eventually_present_of_nonneg_of_unbounded w hL hR
    (kmswLeftBoundaryEdge w i)
  exact ⟨N, hN N le_rfl⟩

/-- The right outer boundary is also directed away from the source; the
reverse order in the face successor is only a face-traversal convention -/
theorem kmswRightBoundary_infinite_present_path (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    Function.Injective (kmswRightBoundaryEdge w) ∧
      (∀ i, edgeEast w (kmswRightBoundaryEdge w i) =
        edgeWest w (kmswRightBoundaryEdge w (i + 1))) ∧
      edgeWest w (kmswRightBoundaryEdge w 0) = 0 ∧
      (∀ i, EdgePresent w (kmswRightBoundaryEdge w i)) := by
  obtain ⟨hi, hs, hz, _⟩ := kmswRightBoundary_infinite_path w hL hR
  refine ⟨hi, hs, hz, fun i => ?_⟩
  obtain ⟨N, hN⟩ := eventually_present_of_nonneg_of_unbounded w hL hR
    (kmswRightBoundaryEdge w i)
  exact ⟨N, hN N le_rfl⟩





theorem conditionedVectorPathLaw_ae_unique_carrier :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        (edgeWest w 0 = 0 ∧ edgeEast w 0 = 1) ∧
        (∀ n, (kmswMap w n).IsPlanar ∧ (kmswStageDirectedMap w n).IsAcyclic ∧
          (∀ e : Fin (kmswStage w n).nextEdge,
            e.val ∈ (kmswStage w n).UL ↔
              (e, false) ∈ (kmswStageDirectedMap w n).ulDarts) ∧
          (∀ e : Fin (kmswStage w n).nextEdge,
            e.val ∈ (kmswStage w n).LR ↔
              (e, true) ∈ (kmswStageDirectedMap w n).lrDarts)) ∧
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          (∀ i, kmswInfFaceSucc w hfin (kmswLeftBoundaryEdge w i, false) =
            (kmswLeftBoundaryEdge w (i + 1), false)) ∧
          (∀ i, kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w (i + 1), true) =
            (kmswRightBoundaryEdge w i, true)) ∧
          kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w 0, true) =
            (kmswLeftBoundaryEdge w 0, false) ∧
          (∀ e, IsLeftBoundaryEdge w e ↔ ∃ i, e = kmswLeftBoundaryEdge w i) ∧
          (∀ e, IsRightBoundaryEdge w e ↔ ∃ i, e = kmswRightBoundaryEdge w i) ∧
          (∀ d : ℕ × Bool,
            (∀ i, d ≠ (kmswLeftBoundaryEdge w i, false)) →
            (∀ i, d ≠ (kmswRightBoundaryEdge w i, true)) →
            ∃! j : TriangleCreationTime w,
              d ∈ stageTriangleDartList w j ∧
                FaceSucc3Cycle (kmswInfFaceSucc w hfin)
                  (stageTriangleDartTriple w j).1
                  (stageTriangleDartTriple w j).2.1
                  (stageTriangleDartTriple w j).2.2) ∧
          (∀ e, ∃ N, ∀ n, N ≤ n →
            e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true) ∧
          (∀ v : ℕ, ∃ n, v < (kmswStage w n).nextVertex) ∧
          (∀ v : ℕ, Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩) ∧
          acyclic (PresentVertex w) ∧
          (∀ v : ℕ, (¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔ v = 0) ∧
          (∀ v : ℕ, ∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
          (Function.Injective (kmswLeftBoundaryEdge w) ∧
            (∀ i, edgeEast w (kmswLeftBoundaryEdge w i) =
              edgeWest w (kmswLeftBoundaryEdge w (i + 1))) ∧
            edgeWest w (kmswLeftBoundaryEdge w 0) = 0 ∧
            (∀ i, EdgePresent w (kmswLeftBoundaryEdge w i))) ∧
          (Function.Injective (kmswRightBoundaryEdge w) ∧
            (∀ i, edgeEast w (kmswRightBoundaryEdge w i) =
              edgeWest w (kmswRightBoundaryEdge w (i + 1))) ∧
            edgeWest w (kmswRightBoundaryEdge w 0) = 0 ∧
            (∀ i, EdgePresent w (kmswRightBoundaryEdge w i))) := by
  filter_upwards [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hp
  obtain ⟨w, hwp, hfin, htrans, hR, hL, _, _⟩ := hp
  have halloc := kmsw_vertex_allocated_of_finite_incidence w hfin
  refine ⟨w, ⟨hwp, ⟨rfl, rfl⟩, ?_, hfin, ?_⟩, ?_⟩
  · intro n
    exact ⟨kmswMap_isPlanar w n, kmswStageDirectedMap_isAcyclic w n,
      kmswStageDirectedMap_UL_bridge w n, kmswStageDirectedMap_LR_bridge w n⟩
  · exact ⟨kmswInfFaceSucc_left w hfin (stageOuterWord_faceSucc w) htrans,
      kmswInfFaceSucc_right w hfin (stageOuterWord_faceSucc w) hL hR,
      kmswInfFaceSucc_junction w hfin (stageOuterWord_faceSucc w) hL htrans hR,
      isLeftBoundaryEdge_iff w htrans, isRightBoundaryEdge_iff w hR,
      kmswInfDart_nonOuterFace_cycle w hfin htrans hR hL,
      eventually_present_of_nonneg_of_unbounded w hL hR, halloc,
      fun v => allocated_vertex_reachable_from_zero w hL v (halloc v),
      presentVertex_acyclic w,
      fun v => allocated_vertex_source_iff_zero w hL v (halloc v),
      fun v => allocated_vertex_outgoing_present_edge w hR v (halloc v),
      kmswLeftBoundary_infinite_present_path w htrans hL hR,
      kmswRightBoundary_infinite_present_path w hL hR⟩
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

end DirectedDistances.KMSW
