module

public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.RunBoundaryVertexLabels
import DirectedDistances.PaperProofs.Section7.CellLDPUpperRouteUp
import DirectedDistances.KMSW.LeftmostGeodesicSdpPlanar

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW




theorem cell_sdp_first_exit_prefix (w : ℕ → Fin 3) {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (n : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    ∃ T, ¬ (P.edge T < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge T) = true) ∧
      (∀ t, t < T → P.edge t < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge t) = true) ∧
      (∃ q : Path (⟨v⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩,
        q.length = T) ∧
      (∃ e, e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ∧
        ((kmswStage w n).west e = (P.initial T).1.id ∨
          (kmswStage w n).east e = (P.initial T).1.id)) := by
  obtain ⟨T, hExit, hBefore⟩ := first_unpresent_edge w P n
  have hp : ∀ e ∈ pathEdgeList (P.initial T).2,
      e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true := by
    intro e he
    rw [P.prefix_edges T] at he
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
    rw [← hi]
    exact hBefore i.val i.isLt
  obtain ⟨q, hq⟩ := path_lifts_to_stage_of_edges_present w n (P.initial T).2 hp
  exact ⟨T, hExit, hBefore, ⟨q, hq.trans (P.prefix_length T)⟩,
    first_unpresent_edge_upper_boundary w P n T hv hExit hBefore⟩




theorem cell_sdp_geodesic_exit (w : ℕ → Fin 3) {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments) (n : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    ∃ T, ¬ (P.edge T < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge T) = true) ∧
      (∀ t, t < T → P.edge t < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge t) = true) ∧
      (∃ q : Path (⟨v⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩,
        q.length = T ∧ IsShortest q) ∧
      sdp (⟨v⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩ = (T : ℕ∞) ∧
      sdp (⟨v⟩ : PresentVertex w) (P.initial T).1 = (T : ℕ∞) ∧
      (∃ e, e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ∧
        ((kmswStage w n).west e = (P.initial T).1.id ∨
          (kmswStage w n).east e = (P.initial T).1.id)) := by
  obtain ⟨T, hExit, hBefore, ⟨q, hq⟩, hUpper⟩ := cell_sdp_first_exit_prefix w P n hv
  have hlimit : sdp (⟨v⟩ : PresentVertex w) (P.initial T).1 = (T : ℕ∞) := by
    rw [← (isShortest_iff_length_eq_sdp _).mp (P.initial_isShortest w hP T),
      P.prefix_length T]
  have hstage : sdp (⟨v⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩ =
      (T : ℕ∞) := by
    apply le_antisymm
    · simpa only [hq] using sdp_le_length q
    · rw [← hlimit]
      exact sdp_limit_le_sdp_stage w n ⟨v⟩ ⟨(P.initial T).1.id⟩
  have hshort : IsShortest q := (isShortest_iff_length_eq_sdp q).mpr (by
    rw [hq, hstage])
  exact ⟨T, hExit, hBefore, ⟨q, hq, hshort⟩, hstage, hlimit, hUpper⟩




theorem cell_sdp_geodesic_exit_future_boundary (w : ℕ → Fin 3) {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments) (n : ℕ)
    (hv : v < (kmswStage w n).nextVertex)
    (hFuture : BoundaryHitWitnesses (fun i => w (n + i))) :
    ∃ T, ¬ (P.edge T < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge T) = true) ∧
      (∀ t, t < T → P.edge t < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge t) = true) ∧
      ∃ k : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
        k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
        (P.initial T).1.id = kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hFuture k) ∧
        (∃ q : Path (⟨v⟩ : StagePresentVertex w n)
            ⟨kmswWindowVertexMapInf w n
              (boundaryVertex (fun i => w (n + i)) hFuture k)⟩,
          q.length = T ∧ IsShortest q) ∧
        sdp (⟨v⟩ : StagePresentVertex w n)
          ⟨kmswWindowVertexMapInf w n
            (boundaryVertex (fun i => w (n + i)) hFuture k)⟩ = (T : ℕ∞) ∧
        sdp (⟨v⟩ : PresentVertex w) (P.initial T).1 = (T : ℕ∞) := by
  obtain ⟨T, hExit, hBefore, hq, hstage, hlimit, e, he, hend⟩ :=
    cell_sdp_geodesic_exit w P hP n hv
  obtain ⟨k, hkL, hkR, hk⟩ :=
    stage_upper_endpoint_future_boundary_bounded w n hFuture e (P.initial T).1.id he hend
  refine ⟨T, hExit, hBefore, k, hkL, hkR, hk, ?_, ?_, hlimit⟩
  · rw [← hk]
    exact hq
  · rw [← hk]
    exact hstage

end DirectedDistances.PaperProofs.Section7
