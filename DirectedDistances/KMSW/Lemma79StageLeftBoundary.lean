module

public import DirectedDistances.KMSW.MonotoneLayoutInvariant
public import DirectedDistances.KMSW.MonotoneStageFaces
public import DirectedDistances.KMSW.StageBoundaryMap
public import DirectedDistances.KMSW.StoppedLeftBoundaryMark

public section
namespace DirectedDistances.KMSW

/-- Endpoint incidence in the geometric upper-left boundary of a stage. Helper
toward Lemma 7.9 (`lem-uiqbot-boltzmann`); not a paper result. See -/
@[expose] def StageLeftBoundaryVertex {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n)
    (U : P.Face) (v : ℕ) : Prop :=
  ∃ d ∈ kmswStageULDartRun w n, P.dartBorders d U ∧
    (v = stageEndpoint (kmswStage w n) d ∨
      v = stageEndpoint (kmswStage w n) (edgeFlip _ d))

/-- The upper-left stage path, ordered from its west endpoint to its terminal
vertex. Helper toward Lemma 7.9 (`lem-uiqbot-boltzmann`); not a paper result. -/
@[expose] def stageLeftBoundaryVertices (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  (kmswStage w n).UL.map (kmswStage w n).west ++
    [(kmswStage w n).east (act w n)]

/-- The ordered stage path agrees with the stopped-list convention at time
`n + 1`. Helper toward Lemma 7.9 (`lem-uiqbot-boltzmann`); not a paper result. -/
theorem stageLeftBoundaryVertices_eq_stopped (w : ℕ → Fin 3) (n : ℕ) :
    stageLeftBoundaryVertices w n = stoppedLeftBoundaryVertices w (n + 1) := by
  simp [stageLeftBoundaryVertices, stoppedLeftBoundaryVertices]

/-- The upper-left dart run borders the unique unbounded face of a monotone
stage. Helper toward Lemma 7.9 (`lem-uiqbot-boltzmann`); not a paper result. -/
theorem kmswStage_UL_path_borders_exterior {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) :
    ∃ U : P.Face, P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      ∀ d, d ∈ kmswStageULDartRun w n → P.dartBorders d U := by
  obtain ⟨_, U, _, hUnbounded, hUnique, hBorders⟩ := G.face_partition
  refine ⟨U, hUnbounded, hUnique, ?_⟩
  intro d hd
  apply hBorders d |>.2
  rw [kmswStage_isOuter_iff_boundary]
  have hmem : d ∈ kmswStageULDartsFinset w n := by
    exact List.mem_toFinset.mpr hd
  obtain ⟨hside, hedge⟩ := (kmswStageULDartsFinset_mem w n d).mp hmem
  exact Or.inl ⟨hside, List.mem_append_left _ hedge⟩

private theorem stageLeftBoundary_east_vertices (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.map (kmswStage w n).east =
      ((kmswStage w n).UL.map (kmswStage w n).west).drop 1 ++
        [(kmswStage w n).east (act w n)] := by
  have h := congrArg List.reverse (CutConverse.ul_coherent w n)
  simpa [CutConverse.ULCoherent, act] using h

private theorem stageLeftBoundaryVertex_endpoint_iff {w : ℕ → Fin 3}
    (n v : ℕ) :
    (∃ d ∈ kmswStageULDartRun w n,
      v = stageEndpoint (kmswStage w n) d ∨
        v = stageEndpoint (kmswStage w n) (edgeFlip _ d)) ↔
      v ∈ stageLeftBoundaryVertices w n := by
  constructor
  · rintro ⟨d, hd, hv⟩
    have hfin : d ∈ kmswStageULDartsFinset w n := List.mem_toFinset.mpr hd
    obtain ⟨hside, hedge⟩ := (kmswStageULDartsFinset_mem w n d).mp hfin
    rcases d with ⟨e, b⟩
    have hb : b = false := hside
    cases b
    · simp only [stageEndpoint, edgeFlip_apply, Bool.false_eq_true,
        Bool.not_false, ↓reduceIte] at hv
      change v ∈ (kmswStage w n).UL.map (kmswStage w n).west ++
        [(kmswStage w n).east (act w n)]
      rcases hv with hv | hv
      · exact List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨e.val, hedge, hv.symm⟩))
      · have heast : v = (kmswStage w n).east e.val := hv
        have hmem : (kmswStage w n).east e.val ∈
            (kmswStage w n).UL.map (kmswStage w n).east :=
          List.mem_map.mpr ⟨e.val, hedge, rfl⟩
        have hlist : (kmswStage w n).east e.val ∈
            (kmswStage w n).UL.map (kmswStage w n).west ++
              [(kmswStage w n).east (act w n)] := by
          rw [stageLeftBoundary_east_vertices w n] at hmem
          rcases List.mem_append.mp hmem with h | h
          · exact List.mem_append.mpr (Or.inl (List.mem_of_mem_drop h))
          · exact List.mem_append.mpr (Or.inr h)
        rw [heast]
        exact hlist
    · cases hb
  · intro hv
    rw [stageLeftBoundaryVertices] at hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_map.mp hv with ⟨e, he, hwest⟩
      let d : StageDart (kmswStage w n).nextEdge :=
        (⟨e, stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inl he)))⟩, false)
      have hfin : d ∈ kmswStageULDartsFinset w n :=
        (kmswStageULDartsFinset_mem w n d).mpr ⟨rfl, he⟩
      have hd : d ∈ kmswStageULDartRun w n := List.mem_toFinset.mp hfin
      refine ⟨d, hd, ?_⟩
      left
      simpa [d, stageEndpoint] using hwest.symm
    · have hv' := List.mem_singleton.mp hv
      obtain ⟨es, hes⟩ := kmswStage_UL_last w n
      have hactive : act w n ∈ (kmswStage w n).UL := by
        rw [hes]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      let d : StageDart (kmswStage w n).nextEdge :=
        (⟨act w n, stageRun_edge_bound w n (act w n)
          (Or.inl (Or.inl (Or.inl hactive)))⟩, false)
      have hfin : d ∈ kmswStageULDartsFinset w n :=
        (kmswStageULDartsFinset_mem w n d).mpr ⟨rfl, hactive⟩
      have hd : d ∈ kmswStageULDartRun w n := List.mem_toFinset.mp hfin
      refine ⟨d, hd, ?_⟩
      right
      simpa [d, stageEndpoint, edgeFlip_apply] using hv'

/-- The geometric UL incidence vertex set is exactly the ordered UL stage
path. Helper toward Lemma 7.9 (`lem-uiqbot-boltzmann`); not a paper result. -/
theorem stageLeftBoundaryVertex_iff {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (U : P.Face) (hU : P.IsUnbounded U) (v : ℕ) :
    StageLeftBoundaryVertex P U v ↔ v ∈ stageLeftBoundaryVertices w n := by
  obtain ⟨U₀, hU₀, hUnique, hBorders⟩ :=
    kmswStage_UL_path_borders_exterior G
  have hEq : U = U₀ := hUnique U hU
  rw [StageLeftBoundaryVertex, hEq]
  constructor
  · rintro ⟨d, hd, hborder, hv⟩
    exact (stageLeftBoundaryVertex_endpoint_iff n v).1
      ⟨d, hd, hv⟩
  · intro hv
    obtain ⟨d, hd, hend⟩ := (stageLeftBoundaryVertex_endpoint_iff n v).2 hv
    exact ⟨d, hd, hBorders d hd, hend⟩

end DirectedDistances.KMSW
