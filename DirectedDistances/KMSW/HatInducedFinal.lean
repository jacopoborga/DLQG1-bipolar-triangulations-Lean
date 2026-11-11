module

public import DirectedDistances.KMSW.HatInducedAssembly
public import DirectedDistances.KMSW.HatInducedExitPendant
public import DirectedDistances.KMSW.HatInducedEmbedding
public import DirectedDistances.KMSW.HatFaceRotation
public import DirectedDistances.KMSW.HatFaceIso

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open Quiver




theorem hatRotInduced_all (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, HatRotInducedAt w h m := by
  exact hatRotInduced_all_of_exitPendant w h
    (fun k hur ih => hatDartMap_rot_induced_exit_pendant w h k hur ih)



@[expose] noncomputable def hatInducedEmbedding (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) :
    RootedInducedEmbedding
      (kmswRootedStage (hatCodes w h) m)
      (kmswRootedStage w (quadrantRStageTime w h m)) := by
  refine
    { dartMap := hatDartMap w h m
      injective := hatDartMap_injective w h m
      flip_comm := ?_
      present := ?_
      tail_comm := ?_
      rot_induced := hatRotInduced_all w h m
      root_comm := hatDartMap_root w h m }
  · intro d
    exact (hatDartMap_edgeInv w h m d).symm
  · intro d hd
    exact hatDartMap_present w h m d hd
  · intro d hd
    exact hatDartMap_tail w h m d hd



theorem hatInducedEmbedding_dartMap (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) :
    (hatInducedEmbedding w h m).dartMap = hatDartMap w h m := rfl





theorem hatKMSW_paperRoot (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m,
      0 < (kmswStage (hatCodes w h) m).nextEdge ∧
      (kmswStage (hatCodes w h) m).present 0 = true ∧
      0 < (kmswStage w (quadrantRStageTime w h m)).nextEdge ∧
      (kmswStage w (quadrantRStageTime w h m)).present 0 = true ∧
      (∀ b : Bool,
        hatDartMap w h m
          (⟨⟨0, (initial_edge_present (hatCodes w h) m).1⟩, b⟩) =
            (⟨⟨0, (initial_edge_present w (quadrantRStageTime w h m)).1⟩, b⟩ :
              StageDart (kmswStage w (quadrantRStageTime w h m)).nextEdge)) ∧
      (kmswStage (hatCodes w h) m).west 0 = 0 ∧
      (kmswStage w (quadrantRStageTime w h m)).west 0 = 0 ∧
      hatAllVertexMap w h m ((kmswStage (hatCodes w h) m).west 0) = 0 := by
  obtain ⟨hvertex, hedge, _, _⟩ := hat_root_correspondence w h
  intro m
  have hlocal := initial_edge_present (hatCodes w h) m
  have hglobal := initial_edge_present w (quadrantRStageTime w h m)
  have hlocalWest := (initial_edge_endpoints (hatCodes w h) m).1
  have hglobalWest := (initial_edge_endpoints w (quadrantRStageTime w h m)).1
  refine ⟨hlocal.1, hlocal.2, hglobal.1, hglobal.2, ?_, hlocalWest,
    hglobalWest, ?_⟩
  · intro b
    apply Prod.ext
    · apply Fin.ext
      change hatAllEdgeMap w h m 0 = 0
      exact hedge m
    · rfl
  · rw [hlocalWest]
    exact hvertex m



theorem hatInducedEmbedding_compatible (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    (hatInducedEmbedding w h (m + 1)).dartMap
        (outerSucc_castDart
          (kmswStage_nextEdge_mono (hatCodes w h) (Nat.le_succ m)) d) =
      outerSucc_castDart
        (kmswStage_nextEdge_mono w
          (quadrantRStageTime_mono w h (Nat.le_succ m)))
        ((hatInducedEmbedding w h m).dartMap d) := by
  rw [hatInducedEmbedding_dartMap, hatInducedEmbedding_dartMap]
  exact hatDartMap_compatible w h m (m + 1) (Nat.le_succ m) d




theorem hatKMSW_graphFace (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∃ (V : {a : PresentVertex (hatCodes w h) //
          ∃ m, a.id < (kmswStage (hatCodes w h) m).nextVertex} ≃
        {v : PresentVertex w // Reachable (⟨0⟩ : PresentVertex w) v})
      (E : {e : ℕ // EdgePresent (hatCodes w h) e} ≃
        {e : ℕ // EdgePresent w e ∧
          Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ ∧
          Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩})
      (F : HatLocalTri w h ≃ GlobalHatTri w),
      (∀ a, (V a).1.id = hatLimitVertexMap w h a.1.id) ∧
      (∀ e, (E e).1 = hatLimitEdgeMap w h e.1) ∧
      (∀ e, edgeWest w (E e).1 =
          hatLimitVertexMap w h (edgeWest (hatCodes w h) e.1) ∧
        edgeEast w (E e).1 =
          hatLimitVertexMap w h (edgeEast (hatCodes w h) e.1)) ∧
      (∀ t, (F t).1 =
        ((E ⟨t.1.1, (hatLocalTri_edges_present w h t).1⟩).1,
         (E ⟨t.1.2.1, (hatLocalTri_edges_present w h t).2.1⟩).1,
         (E ⟨t.1.2.2, (hatLocalTri_edges_present w h t).2.2⟩).1)) :=
  hatExplicitGraphFaceIso w h



theorem hatKMSW_stageEmbeddings (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, ∃ i : RootedInducedEmbedding
      (kmswRootedStage (hatCodes w h) m)
      (kmswRootedStage w (quadrantRStageTime w h m)),
      i.dartMap = hatDartMap w h m := by
  intro m
  exact ⟨hatInducedEmbedding w h m, hatInducedEmbedding_dartMap w h m⟩




theorem hatKMSW_cofinal (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (∀ v : PresentVertex w, Reachable (⟨0⟩ : PresentVertex w) v →
      ∃ m a, a < (kmswStage (hatCodes w h) m).nextVertex ∧
        hatAllVertexMap w h m a = v.id) ∧
    (∀ e : ℕ, EdgePresent w e →
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ →
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩ →
      ∃ m a, a < (kmswStage (hatCodes w h) m).nextEdge ∧
        (kmswStage (hatCodes w h) m).present a = true ∧
        hatAllEdgeMap w h m a = e) ∧
    (∀ s : GlobalHatTriSrc w, ∃ m t,
      t ∈ (kmswStage (hatCodes w h) m).triangles ∧
      (hatAllEdgeMap w h m t.1, hatAllEdgeMap w h m t.2.1,
        hatAllEdgeMap w h m t.2.2) = s.1) :=
  hatDartMap_cofinal w h



theorem hatKMSW_LL_nil (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    (kmswStage (hatCodes w h) m).LL = [] := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change (kmswStepOfStep (kmswStage (hatCodes w h) m)
        (kmswCodeStep (hatCodes w h m))).LL = []
      cases hc : kmswCodeStep (hatCodes w h m) with
      | left =>
          have hn := noFreshLeftSource_hatCodes w h m hc
          cases hp : (kmswStage (hatCodes w h) m).UL.dropLast.reverse with
          | nil => exact (hn hp).elim
          | cons e es =>
              simpa only [kmswStepOfStep, hp, State.addEdge] using ih
      | up => simpa only [kmswStepOfStep, State.addEdge] using ih
      | down =>
          cases hu : (kmswStage (hatCodes w h) m).UR <;>
            simpa only [kmswStepOfStep, hu, State.addEdge] using ih




theorem hatKMSW_stagewise (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (∃ (V : {a : PresentVertex (hatCodes w h) //
          ∃ m, a.id < (kmswStage (hatCodes w h) m).nextVertex} ≃
        {v : PresentVertex w // Reachable (⟨0⟩ : PresentVertex w) v})
      (E : {e : ℕ // EdgePresent (hatCodes w h) e} ≃
        {e : ℕ // EdgePresent w e ∧
          Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ ∧
          Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩})
      (F : HatLocalTri w h ≃ GlobalHatTri w),
      (∀ a, (V a).1.id = hatLimitVertexMap w h a.1.id) ∧
      (∀ e, (E e).1 = hatLimitEdgeMap w h e.1) ∧
      (∀ e, edgeWest w (E e).1 =
          hatLimitVertexMap w h (edgeWest (hatCodes w h) e.1) ∧
        edgeEast w (E e).1 =
          hatLimitVertexMap w h (edgeEast (hatCodes w h) e.1)) ∧
      (∀ t, (F t).1 =
        ((E ⟨t.1.1, (hatLocalTri_edges_present w h t).1⟩).1,
         (E ⟨t.1.2.1, (hatLocalTri_edges_present w h t).2.1⟩).1,
         (E ⟨t.1.2.2, (hatLocalTri_edges_present w h t).2.2⟩).1))) ∧
      (∀ m, ∃ i : RootedInducedEmbedding
        (kmswRootedStage (hatCodes w h) m)
        (kmswRootedStage w (quadrantRStageTime w h m)),
        i.dartMap = hatDartMap w h m) ∧
      (∀ m,
        0 < (kmswStage (hatCodes w h) m).nextEdge ∧
        (kmswStage (hatCodes w h) m).present 0 = true ∧
        0 < (kmswStage w (quadrantRStageTime w h m)).nextEdge ∧
        (kmswStage w (quadrantRStageTime w h m)).present 0 = true ∧
        (∀ b : Bool,
          hatDartMap w h m
            (⟨⟨0, (initial_edge_present (hatCodes w h) m).1⟩, b⟩) =
              (⟨⟨0, (initial_edge_present w (quadrantRStageTime w h m)).1⟩, b⟩ :
                StageDart (kmswStage w (quadrantRStageTime w h m)).nextEdge)) ∧
        (kmswStage (hatCodes w h) m).west 0 = 0 ∧
        (kmswStage w (quadrantRStageTime w h m)).west 0 = 0 ∧
        hatAllVertexMap w h m ((kmswStage (hatCodes w h) m).west 0) = 0) ∧
      ((∀ v : PresentVertex w, Reachable (⟨0⟩ : PresentVertex w) v →
          ∃ m a, a < (kmswStage (hatCodes w h) m).nextVertex ∧
            hatAllVertexMap w h m a = v.id) ∧
        (∀ e : ℕ, EdgePresent w e →
          Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ →
          Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩ →
          ∃ m a, a < (kmswStage (hatCodes w h) m).nextEdge ∧
            (kmswStage (hatCodes w h) m).present a = true ∧
            hatAllEdgeMap w h m a = e) ∧
        (∀ s : GlobalHatTriSrc w, ∃ m t,
          t ∈ (kmswStage (hatCodes w h) m).triangles ∧
          (hatAllEdgeMap w h m t.1, hatAllEdgeMap w h m t.2.1,
            hatAllEdgeMap w h m t.2.2) = s.1)) ∧
      (∀ m, (kmswStage (hatCodes w h) m).LL = []) := by
  exact ⟨hatKMSW_graphFace w h, hatKMSW_stageEmbeddings w h,
    hatKMSW_paperRoot w h, hatKMSW_cofinal w h,
    fun m => hatKMSW_LL_nil w h m⟩

end DirectedDistances.KMSW
