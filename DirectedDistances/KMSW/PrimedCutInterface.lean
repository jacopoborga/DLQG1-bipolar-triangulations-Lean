module

public import DirectedDistances.KMSW.QuadKMSWHatFlipped
public import DirectedDistances.KMSW.QuadKMSWHatAllStages

/-! # Finite candidate cut path at a hatted exit

Finite ordered-list helpers toward `lem-quad-kmsw`
419–426 reference to the boundary convention has drifted to line 415).
These do not prove the primed simulation, identify this path with β₀,
prove `hLR`, or establish any numbered paper result.

For codes starting with `1,0` and then repeating `0,0,2`, the candidate
cut at the first exit is `[1]`. Its last edge `1` is absent from the global
frontier `[3,2,4,0]` after the exit. This is a sanity example only. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/-- Candidate finite cut path: the image of the pre-exit hatted UL boundary.
not a β₀ identification or a primed simulation. -/
@[expose] noncomputable def cutAtExit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : List ℕ :=
  (kmswStage (hatCodes w h) (hatExitIndex w h k)).UL.map
    (hatAllEdgeMap w h (hatExitIndex w h k))

/-- The exit replacement appends one UL edge, so deleting its last edge
recovers the pre-exit boundary. Finite helper toward `lem-quad-kmsw` -/
theorem hatExit_UL_eq_dropLast (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    (kmswStage (hatCodes w h) (hatExitIndex w h k)).UL =
      (kmswStage (hatCodes w h) (hatExitIndex w h k + 1)).UL.dropLast := by
  rw [kmswStage, kmswStep, hatCodes_at_exit]
  change (kmswStage (hatCodes w h) (hatExitIndex w h k)).UL =
    (kmswStepOfStep (kmswStage (hatCodes w h) (hatExitIndex w h k)) .down).UL.dropLast
  cases hs : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR <;>
    simp only [kmswStepOfStep, hs, List.dropLast_concat]

/-- The cut is also the image of the post-replacement drop-last prefix,
using the extended edge map. Finite helper toward `lem-quad-kmsw` -/
theorem cutAtExit_eq_map_dropLast (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    cutAtExit w h k =
      ((kmswStage (hatCodes w h) (hatExitIndex w h k + 1)).UL.dropLast).map
        (hatAllEdgeMap w h (hatExitIndex w h k + 1)) := by
  rw [← hatExit_UL_eq_dropLast, cutAtExit]
  apply List.map_congr_left
  intro e he
  apply (hatAllEdgeMap_extend w h (hatExitIndex w h k) e _).symm
  apply (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) (hatExitIndex w h k)).2 e
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl he))

/-- The candidate cut ends at the old global active edge, at time
`walkNL w h k - 1`. Finite helper toward `lem-quad-kmsw` -/
theorem cutAtExit_getLast? (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    (cutAtExit w h k).getLast? = some (kmswStage w (walkNL w h k - 1)).active := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last (hatCodes w h) (hatExitIndex w h k)
  have ha := (hatAll_sim w h (hatExitIndex w h k)).incidenceSim.active
  rw [quadrantRStageTime_hatExitIndex] at ha
  rw [cutAtExit, hxs, List.map_append]
  simp only [List.map_cons, List.map_nil, List.getLast?_append_cons,
    List.getLast?_singleton, ha]

/-- The old active edge belongs to the candidate finite cut. Helper toward
that it belongs to the global outer frontier. -/
theorem active_mem_cutAtExit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    (kmswStage w (walkNL w h k - 1)).active ∈ cutAtExit w h k := by
  exact List.mem_of_getLast? (cutAtExit_getLast? w h k)

/-- Every candidate cut edge was already allocated globally before the
L exit. This uses the pre-exit time, not the later R re-entry time.
Finite helper toward `lem-quad-kmsw` -/
theorem cutAtExit_edge_bound (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k e : ℕ) (he : e ∈ cutAtExit w h k) :
    e < (kmswStage w (walkNL w h k - 1)).nextEdge := by
  unfold cutAtExit at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  have hfBound : f < (kmswStage (hatCodes w h) (hatExitIndex w h k)).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) (hatExitIndex w h k)).2 f
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hf))
  have hb := (hatAll_sim w h (hatExitIndex w h k)).incidenceSim.edge_bound f hfBound
  rwa [quadrantRStageTime_hatExitIndex] at hb

end DirectedDistances.KMSW
