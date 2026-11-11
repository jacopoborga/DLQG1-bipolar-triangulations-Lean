module

public import DirectedDistances.KMSW.KMSWWindowCaptureEventRel
public import DirectedDistances.KMSW.KMSWWindowGlobalSeamFresh
public import DirectedDistances.KMSW.WindowCodeDecoder

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem event_stage_eq (u w : ℕ → Fin 3) (s m : ℕ)
    (hcode : ∀ i < m, w (s + i) = u i) :
    ∀ k ≤ m, kmswStage (fun i => w (s + i)) k = kmswStage u k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      change kmswStep (kmswStage (fun i => w (s + i)) k) (w (s + k)) =
        kmswStep (kmswStage u k) (u k)
      rw [ih (by omega), hcode k (by omega)]

private theorem event_frontier_transport (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (hfresh : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hfront : ¬ UpperFrontierEndpoint (kmswStage (fun i => w (s + i)) m) v) :
    ¬ UpperFrontierEndpoint (kmswStage w (s + m))
      (kmswWindowPatchVertexMap w s m v) := by
  let F := kmswStage (fun i => w (s + i)) m
  let G := kmswStage w (s + m)
  let G₀ := kmswStage w s
  let d := kmswWindowPatchData w s m
  let ψ := kmswWindowPatchVertexMap w s m
  have hrel := kmswWindowPatchData_rel w s m
  have hvr := kmswWindowPatchVertexMap_rel w s m
  change KMSWWindowPatchRel G₀ G F d.φ d.A d.B d.YL d.YR d.XL d.XR at hrel
  change KMSWWindowPatchVertexRel G F d.φ ψ at hvr
  have hres (e : ℕ) (he : e ∈ d.A ++ d.B) :
      G.west e < G₀.nextVertex ∧ G.east e < G₀.nextVertex := by
    have hbase : e ∈ G₀.UL ++ G₀.UR := by
      rcases List.mem_append.mp he with ha | hb
      · apply List.mem_append_left
        apply List.dropLast_subset
        rw [hrel.left_residual]
        exact List.mem_append_left _ ha
      · apply List.mem_append_right
        rw [hrel.right_residual]
        exact List.mem_append_right _ hb
    have heid := (kmswStage_boundary_ids_lt_nextEdge w s).2 e (by
      change e ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
      simp only [List.mem_append] at hbase ⊢
      tauto)
    have hs := kmswStage_endpoints_stable w (show s ≤ s + m by omega) heid
    change G.west e = G₀.west e ∧ G.east e = G₀.east e at hs
    rw [hs.1, hs.2]
    exact kmswStage_endpoints_lt_nextVertex w s e heid
  rintro (⟨e, he, hend⟩ | hnew)
  · change e ∈ G.UL ++ G.UR at he
    have hsplit : e ∈ d.A ++ d.B ∨
        ∃ f, f ∈ F.UL ++ F.UR ∧ d.φ f = e := by
      rw [hrel.ul, hrel.ur] at he
      simp only [List.mem_append] at he
      rcases he with (ha | hul) | (hur | hb)
      · exact Or.inl (List.mem_append_left _ ha)
      · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hul
        exact Or.inr ⟨f, List.mem_append_left _ hf, hfe⟩
      · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hur
        exact Or.inr ⟨f, List.mem_append_right _ hf, hfe⟩
      · exact Or.inl (List.mem_append_right _ hb)
    rcases hsplit with hresid | ⟨f, hf, rfl⟩
    · have hb := hres e hresid
      change G.west e = ψ v ∨ G.east e = ψ v at hend
      change G₀.nextVertex ≤ ψ v at hfresh
      rcases hend with hw | he
      · omega
      · omega
    · have hfid := (kmswStage_boundary_ids_lt_nextEdge
          (fun i => w (s + i)) m).2 f (by
        change f ∈ F.UL ++ F.UR ++ F.LL ++ F.LR
        simp only [List.mem_append] at hf ⊢
        tauto)
      have hb := kmswStage_endpoints_lt_nextVertex (fun i => w (s + i)) m f hfid
      change G.west (d.φ f) = ψ v ∨ G.east (d.φ f) = ψ v at hend
      apply hfront
      left
      refine ⟨f, hf, ?_⟩
      rcases hend with hw | he
      · left
        exact kmswWindowPatchVertexMap_injOn w s m hb.1 hv
          ((hvr.west_endpoint f hfid).trans hw)
      · right
        exact kmswWindowPatchVertexMap_injOn w s m hb.2 hv
          ((hvr.east_endpoint f hfid).trans he)
  · exact (Nat.not_le_of_gt (hvr.vertex_bound v hv)) hnew

private theorem event_path_endpoint_bound (u : ℕ → Fin 3) (m : ℕ)
    {k c v : ℕ} (hc : c < (kmswStage u m).nextVertex)
    (hp : KMSWStagePath (fun _ _ => True) (kmswStage u m) Set.univ c k v) :
    v < (kmswStage u m).nextVertex := by
  cases hp with
  | nil _ => exact hc
  | snoc _ _ _ hadj =>
      obtain ⟨d, _, _, hend⟩ := hadj
      rw [← hend]
      exact stageEndpoint_lt_nextVertex u m (edgeFlip _ d)

private theorem rel_fresh (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventRel u m r c)
    (hcode : ∀ i < m, w (s + i) = u i)
    (hglob : ∀ k ∈ kmswBallLeftSeamSet u m r c,
      minL w (s + k) = L w (s + k)) :
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
  classical
  intro v hv
  have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  refine ⟨?_, kmswWindowPatchVertexMap_fresh_of_global_seams u m v hb
    (hev.2.1 v hv).1 w s hcode ?_⟩
  · rw [event_stage_eq u w s m hcode m le_rfl]
    exact hb
  · intro k hk hcreate
    refine ⟨(hev.2.1 v hv).2 k hk hcreate, ?_⟩
    intro hleft
    by_cases hnonseam : (kmswStage u k).UL.dropLast.reverse ≠ []
    · exact Or.inl hnonseam
    · apply Or.inr
      apply hglob k
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,
        ⟨v, hv, hcreate⟩, hleft, not_not.mp hnonseam⟩

private theorem rel_front (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrongRel u m r c)
    (hcode : ∀ i < m, w (s + i) = u i)
    (hglob : ∀ k ∈ kmswBallLeftSeamSet u m r c,
      minL w (s + k) = L w (s + k)) :
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      ¬ UpperFrontierEndpoint (kmswStage w (s + m))
        (kmswWindowPatchVertexMap w s m v) := by
  intro v hv
  have hf := rel_fresh u w m r c s hev.1 hcode hglob v hv
  apply event_frontier_transport w s m v hf.1 hf.2
  rw [event_stage_eq u w s m hcode m le_rfl]
  exact hev.2 v hv

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/
theorem kmswWindowCaptureEventRel_ballVerticesImageEq_future
    (u : ℕ → Fin 3) (m r c : ℕ) (hevent : kmswWindowCaptureEventRel u m r c) :
    ∀ (w : ℕ → Fin 3) (s : ℕ), (∀ i < m, w (s + i) = u i) →
      (∀ k ∈ kmswBallLeftSeamSet u m r c, minL w (s + k) = L w (s + k)) →
      ∀ n ≥ s + m,
        (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
            (kmswWindowPatchVertexMap w s m) =
          kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
            (kmswWindowPatchVertexMap w s m c) := by
  classical
  intro w s hcode hglob n hn
  have hc := hevent.1
  have hinner := hevent.2.2
  have hs := event_stage_eq u w s m hcode m le_rfl
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c
  have hS := rel_fresh u w m r c s hevent hcode hglob
  have hClosed : ∀ v, kmswStageDistanceLe (fun _ _ => True)
      (kmswStage (fun i => w (s + i)) m) r c v → v ∈ (S : Set ℕ) := by
    intro v hv
    rw [hs] at hv
    obtain ⟨k, hk, hp⟩ := hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (event_path_endpoint_bound u m hc hp), k, hk, hp⟩
  have hfront : ∀ v, kmswStageDistanceLe (fun _ _ => True)
      (kmswStage (fun i => w (s + i)) m) (r - 1) c v →
      ¬ UpperFrontierEndpoint (kmswStage w (s + m))
        (kmswWindowPatchVertexMap w s m v) := by
    intro v hv
    have hvS : v ∈ S := by
      apply hClosed v
      obtain ⟨k, hk, hp⟩ := hv
      exact ⟨k, by omega, hp⟩
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hvS).1
    have hvin : v ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u m) (r - 1) c := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hs ▸ hv⟩
    apply event_frontier_transport w s m v (hS v hvS).1 (hS v hvS).2
    rw [hs]
    exact hinner v hvin
  have hresult := kmswWindowAllEdgesBallVerticesImageEq_future
    w s m S r c hS hClosed hfront n hn
  rw [hs] at hresult
  exact hresult

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/
theorem kmswWindowCaptureEventStrongRel_edge_allocated
    (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrongRel u m r c)
    (hcode : ∀ i < m, w (s + i) = u i)
    (hglob : ∀ k ∈ kmswBallLeftSeamSet u m r c,
      minL w (s + k) = L w (s + k))
    (n : ℕ) (hn : s + m ≤ n) (e : ℕ) (he : e < (kmswStage w n).nextEdge)
    (hend : (kmswStage w n).west e ∈
        (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
          (kmswWindowPatchVertexMap w s m) ∨
      (kmswStage w n).east e ∈
        (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
          (kmswWindowPatchVertexMap w s m)) :
    e < (kmswStage w (s + m)).nextEdge := by
  by_contra h
  have hnew := Nat.le_of_not_gt h
  rcases hend with hw | heast
  · obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hw
    exact (kmswStage_no_new_incidence_of_not_upperFrontier w (s + m) _
      (rel_front u w m r c s hev hcode hglob v hv) n hn e he hnew).1 hve.symm
  · obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp heast
    exact (kmswStage_no_new_incidence_of_not_upperFrontier w (s + m) _
      (rel_front u w m r c s hev hcode hglob v hv) n hn e he hnew).2 hve.symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/
theorem kmswWindowCaptureEventStrongRel_edgeMapOn_bijective
    (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrongRel u m r c)
    (hcode : ∀ i < m, w (s + i) = u i)
    (hglob : ∀ k ∈ kmswBallLeftSeamSet u m r c,
      minL w (s + k) = L w (s + k)) :
    Function.Bijective (kmswWindowFreshSetEdgeMapOn w s m
      (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c)) := by
  exact kmswWindowFreshSetEdgeMap_bijective w s m _
    (rel_fresh u w m r c s hev.1 hcode hglob)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/
theorem kmswWindowCaptureEventStrongRel_edge_bijOn_future
    (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrongRel u m r c)
    (hcode : ∀ i < m, w (s + i) = u i)
    (hglob : ∀ k ∈ kmswBallLeftSeamSet u m r c,
      minL w (s + k) = L w (s + k)) (n : ℕ) (hn : s + m ≤ n) :
    let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c
    Set.BijOn (fun e => (kmswWindowFreshSetEdgeMap w s m e).val)
      (kmswWindowFreshSetSourceEdges w s m S)
      {e : ℕ | e < (kmswStage w n).nextEdge ∧
        (kmswStage w n).west e ∈ S.image (kmswWindowPatchVertexMap w s m) ∧
        (kmswStage w n).east e ∈ S.image (kmswWindowPatchVertexMap w s m)} := by
  classical
  dsimp only
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c
  have hb := kmswWindowCaptureEventStrongRel_edgeMapOn_bijective u w m r c s hev hcode hglob
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have hm := (kmswWindowFreshSetEdgeMapOn w s m S ⟨e, he⟩).property
    have hs := kmswStage_endpoints_stable w hn
      (kmswWindowFreshSetEdgeMap w s m e).isLt
    exact ⟨(kmswWindowFreshSetEdgeMap w s m e).isLt.trans_le
      (kmswStage_nextEdge_mono w hn), hs.1 ▸ hm.1, hs.2 ▸ hm.2⟩
  · intro e he f hf hef
    have hval : kmswWindowFreshSetEdgeMap w s m e =
        kmswWindowFreshSetEdgeMap w s m f := Fin.ext hef
    have hsub := hb.1 (show kmswWindowFreshSetEdgeMapOn w s m S ⟨e, he⟩ =
        kmswWindowFreshSetEdgeMapOn w s m S ⟨f, hf⟩ from Subtype.ext hval)
    exact congrArg Subtype.val hsub
  · intro e he
    have hold := kmswWindowCaptureEventStrongRel_edge_allocated u w m r c s hev hcode hglob
      n hn e he.1 (Or.inl he.2.1)
    have hs := kmswStage_endpoints_stable w hn hold
    have htarget : (⟨e, hold⟩ : Fin (kmswStage w (s + m)).nextEdge) ∈
        kmswWindowFreshSetTargetEdges w s m S := by
      exact ⟨hs.1 ▸ he.2.1, hs.2 ▸ he.2.2⟩
    obtain ⟨f, hf⟩ := hb.2 ⟨⟨e, hold⟩, htarget⟩
    exact ⟨f.val, f.property, congrArg (fun x => x.val.val) hf⟩

private theorem stage_path_colimit (W : ℤ → Fin 3) (N n : ℕ)
    {c k v : ℕ}
    (hp : KMSWStagePath (fun _ _ => True) (kmswStage (shiftedStream W N) n)
      Set.univ c k v) :
    WholePlanePath W Set.univ (wholePlaneVertexι W N c) k (wholePlaneVertexι W N v) := by
  induction hp with
  | nil _ => exact .nil (Set.mem_univ _)
  | snoc hp _ _ ha ih =>
      obtain ⟨⟨e, b⟩, _, hx, hy⟩ := ha
      have hs := edge_endpoints_eq (shiftedStream W N) e.isLt
      apply WholePlanePath.snoc ih (Set.mem_univ _) (Set.mem_univ _)
      refine ⟨wholePlaneEdgeι W N e.val, ?_⟩
      rw [wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι]
      cases b
      · exact Or.inl ⟨congrArg _ (hs.1.symm.trans hx),
          congrArg _ (hs.2.symm.trans hy)⟩
      · exact Or.inr ⟨congrArg _ (hs.1.symm.trans hy),
          congrArg _ (hs.2.symm.trans hx)⟩

private theorem patch_colimit (W : ℤ → Fin 3) (N M m v : ℕ) (hNM : N ≤ M)
    (hv : v < (kmswStage (shiftedStream W N) m).nextVertex) :
    wholePlaneVertexι W M (kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m v) =
      wholePlaneVertexι W N v := by
  have hv' : v < (kmswStage (fun i => shiftedStream W M ((M - N) + i)) m).nextVertex := by
    rw [shiftedStream_shift W N M hNM]
    exact hv
  rw [← kmswWindowVertexMapInf_eq_stage _ _ _ _ hv']
  exact congrFun (wholePlaneVertexι_trans W N M hNM) v

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/
theorem wholePlaneBallVertices_eq_image_of_windowCaptureEventRel
    (W : ℤ → Fin 3) (N m r c : ℕ)
    (hevent : kmswWindowCaptureEventRel (shiftedStream W N) m r c)
    (hglob : ∀ M, N ≤ M → ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m r c,
      minL (shiftedStream W M) (M - N + k) =
        L (shiftedStream W M) (M - N + k)) :
    wholePlaneBallVertices W r (wholePlaneVertexι W N c) =
      (fun v => wholePlaneVertexι W N v) ''
        (↑(kmswStageBallVertices (fun _ _ => True)
          (kmswStage (shiftedStream W N) m) r c) : Set ℕ) := by
  classical
  apply Set.ext
  intro x
  constructor
  · rintro ⟨k, hk, hp⟩
    obtain ⟨M, hNM, v, hv, hlift⟩ := wholePlanePath_lift W N c hp
    obtain ⟨n, hn, hpM⟩ := hlift (M - N + m)
    have hc := kmswWindowVertexMapInf_eq_stage (shiftedStream W M) (M - N) m c
      (by rw [shiftedStream_shift W N M hNM]; exact hevent.1)
    change wholePlaneVertexTrans W N M hNM c =
      kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m c at hc
    rw [hc] at hpM
    have hvBound : v < (kmswStage (shiftedStream W M) n).nextVertex := by
      cases hpM with
      | nil _ =>
          exact ((kmswWindowPatchVertexMap_rel (shiftedStream W M) (M - N) m).vertex_bound
            c (by rw [shiftedStream_shift W N M hNM]; exact hevent.1)).trans_le
              (CutConverse.nextVertex_mono _ hn)
      | snoc _ _ _ ha =>
          obtain ⟨d, _, _, hd⟩ := ha
          rw [← hd]
          exact stageEndpoint_lt_nextVertex _ n (edgeFlip _ d)
    have hvBall : v ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage (shiftedStream W M) n) r
        (kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvBound, k, hk, hpM⟩
    have hballs := kmswWindowCaptureEventRel_ballVerticesImageEq_future
      (shiftedStream W N) m r c hevent (shiftedStream W M) (M - N)
      (fun i _ => congrFun (shiftedStream_shift W N M hNM) i) (hglob M hNM) n hn
    rw [← hballs] at hvBall
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hvBall
    refine ⟨u, hu, ?_⟩
    have huBound := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    exact (patch_colimit W N M m u hNM huBound).symm.trans
      ((congrArg (wholePlaneVertexι W M) huv).trans hv)
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk, hp⟩ := (Finset.mem_filter.mp hv).2
    exact ⟨k, hk, stage_path_colimit W N m hp⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/
theorem kmswWindowCaptureEventStrongRel_wholePlaneEdge_bijOn
    (W : ℤ → Fin 3) (N m r c : ℕ)
    (hev : kmswWindowCaptureEventStrongRel (shiftedStream W N) m r c)
    (hglob : ∀ M, N ≤ M → ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m r c,
      minL (shiftedStream W M) (M - N + k) =
        L (shiftedStream W M) (M - N + k)) :
    let S := kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) m) r c
    Set.BijOn (fun e : Fin (kmswStage (shiftedStream W N) m).nextEdge =>
      wholePlaneEdgeι W N e.val)
      {e | (kmswStage (shiftedStream W N) m).west e.val ∈ S ∧
        (kmswStage (shiftedStream W N) m).east e.val ∈ S}
      {e | wholePlaneEdgeWest W e ∈ wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
        wholePlaneEdgeEast W e ∈ wholePlaneBallVertices W r (wholePlaneVertexι W N c)} := by
  classical
  dsimp only
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) m) r c
  have hball := wholePlaneBallVertices_eq_image_of_windowCaptureEventRel W N m r c hev.1 hglob
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have hs := edge_endpoints_eq (shiftedStream W N) e.isLt
    change wholePlaneEdgeWest W (wholePlaneEdgeι W N e.val) ∈
        wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
      wholePlaneEdgeEast W (wholePlaneEdgeι W N e.val) ∈
        wholePlaneBallVertices W r (wholePlaneVertexι W N c)
    rw [wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι, hball, ← hs.1, ← hs.2]
    exact ⟨⟨_, he.1, rfl⟩, ⟨_, he.2, rfl⟩⟩
  · intro e _ f _ hef
    exact Fin.ext (wholePlaneEdgeι_injective W N hef)
  · intro e he
    rw [hball] at he
    obtain ⟨v, hv, hve⟩ := he.1
    obtain ⟨z, hz, hze⟩ := he.2
    obtain ⟨⟨L, q⟩, rfl⟩ := Quotient.exists_rep e
    let M := max N L
    have hNM : N ≤ M := Nat.le_max_left N L
    have hLM : L ≤ M := Nat.le_max_right N L
    let f := wholePlaneEdgeTrans W L M hLM q
    have hfw : wholePlaneVertexι W M (edgeWest (shiftedStream W M) f) =
        wholePlaneEdgeWest W (wholePlaneEdgeι W L q) := by
      rw [wholePlaneEdgeWest_ι, wholePlaneEdgeTrans_west]
      exact congrFun (wholePlaneVertexι_trans W L M hLM) _
    have hfe : wholePlaneVertexι W M (edgeEast (shiftedStream W M) f) =
        wholePlaneEdgeEast W (wholePlaneEdgeι W L q) := by
      rw [wholePlaneEdgeEast_ι, wholePlaneEdgeTrans_east]
      exact congrFun (wholePlaneVertexι_trans W L M hLM) _
    have hvb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
    have hzb := Finset.mem_range.mp (Finset.mem_filter.mp hz).1
    have hwest : edgeWest (shiftedStream W M) f =
        kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m v := by
      apply wholePlaneVertexι_injective W M
      exact (hfw.trans hve.symm).trans (patch_colimit W N M m v hNM hvb).symm
    have heast : edgeEast (shiftedStream W M) f =
        kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m z := by
      apply wholePlaneVertexι_injective W M
      exact (hfe.trans hze.symm).trans (patch_colimit W N M m z hNM hzb).symm
    let n := max (M - N + m) f
    have hn : M - N + m ≤ n := Nat.le_max_left _ _
    have hf : f < (kmswStage (shiftedStream W M) n).nextEdge :=
      (kmsw_edge_allocated_by_self (shiftedStream W M) f).trans_le
        (kmswStage_nextEdge_mono _ (Nat.le_max_right _ _))
    have hs := edge_endpoints_eq (shiftedStream W M) hf
    have htarget : f < (kmswStage (shiftedStream W M) n).nextEdge ∧
        (kmswStage (shiftedStream W M) n).west f ∈
          S.image (kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m) ∧
        (kmswStage (shiftedStream W M) n).east f ∈
          S.image (kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m) := by
      rw [hs.1, hs.2, hwest, heast]
      exact ⟨hf, Finset.mem_image.mpr ⟨v, hv, rfl⟩,
        Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    have hb := kmswWindowCaptureEventStrongRel_edge_bijOn_future
      (shiftedStream W N) (shiftedStream W M) m r c (M - N) hev
      (fun i _ => congrFun (shiftedStream_shift W N M hNM) i) (hglob M hNM) n hn
    obtain ⟨a, ha, haf⟩ := hb.2.2 htarget
    have hstage := congrArg (fun u => kmswStage u m) (shiftedStream_shift W N M hNM)
    have hab : a.val < (kmswStage (shiftedStream W N) m).nextEdge := by
      rw [← hstage]
      exact a.isLt
    have hasource : (kmswStage (shiftedStream W N) m).west a.val ∈ S ∧
        (kmswStage (shiftedStream W N) m).east a.val ∈ S := by
      rw [← hstage]
      exact ha
    refine ⟨⟨a.val, hab⟩, hasource, ?_⟩
    have hinf : wholePlaneEdgeTrans W N M hNM a.val = f := by
      change kmswWindowEdgeMapInf (shiftedStream W M) (M - N) a.val = f
      rw [kmswWindowEdgeMapInf_eq_stage _ _ _ _ a.isLt]
      exact haf
    exact (congrFun (wholePlaneEdgeι_trans W N M hNM) a.val).symm.trans
      ((congrArg (wholePlaneEdgeι W M) hinf).trans
        (congrFun (wholePlaneEdgeι_trans W L M hLM) q))

private theorem disk_window_valid {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
  unfold bridgeOptionWindow at h
  split at h
  · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
  · contradiction

private theorem disk_window_code {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    ∀ i < 2 * N,
      (fun j => p.1 (j + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + i) =
        windowCodeDecode N x i := by
  intro i hi
  exact (windowCodeDecode_bridge h i hi).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/
theorem kmswDiskBallVertices_eq_image_future_rel {n N r c : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventRel (windowCodeDecode N x) (2 * N) r c)
    (hglob : ∀ k ∈ kmswBallLeftSeamSet (windowCodeDecode N x) (2 * N) r c,
      minL (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + k) =
        L (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + k))
    (n' : ℕ) (hn' : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n') :
    kmswStageBallVertices (fun _ _ => True) (kmswStage (fun i => p.1 (i + 1)) n') r
        (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N) c) =
      (kmswStageBallVertices (fun _ _ => True)
        (kmswStage (windowCodeDecode N x) (2 * N)) r c).image
          (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
            ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)) := by
  have hNT := (disk_window_valid h).1
  exact (kmswWindowCaptureEventRel_ballVerticesImageEq_future
    (windowCodeDecode N x) (2 * N) r c hev (fun i => p.1 (i + 1))
    ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (disk_window_code h) hglob
    n' (by omega)).symm

private theorem equiv_of_common_image {α β γ : Type*}
    (S : Set α) (D : Set β) (C : Set γ) (f : α → β) (g : α → γ)
    (hf : Set.InjOn f S) (hg : Set.InjOn g S)
    (hD : D = f '' S) (hC : C = g '' S) :
    ∃ e : D ≃ C, ∀ (d : D) (v : α), v ∈ S → d.val = f v → (e d).val = g v := by
  classical
  let f' : S → D := fun v => ⟨f v.val, by
    rw [hD]
    exact ⟨v.val, v.property, rfl⟩⟩
  let g' : S → C := fun v => ⟨g v.val, by
    rw [hC]
    exact ⟨v.val, v.property, rfl⟩⟩
  have hf' : Function.Bijective f' := by
    constructor
    · intro a b hab
      exact Subtype.ext (hf a.property b.property (congrArg Subtype.val hab))
    · intro d
      have hd : d.val ∈ f '' S :=
        (congrArg (fun A : Set β => d.val ∈ A) hD).mp d.property
      obtain ⟨v, hv, hvd⟩ := hd
      exact ⟨⟨v, hv⟩, Subtype.ext hvd⟩
  have hg' : Function.Bijective g' := by
    constructor
    · intro a b hab
      exact Subtype.ext (hg a.property b.property (congrArg Subtype.val hab))
    · intro d
      have hd : d.val ∈ g '' S :=
        (congrArg (fun A : Set γ => d.val ∈ A) hC).mp d.property
      obtain ⟨v, hv, hvd⟩ := hd
      exact ⟨⟨v, hv⟩, Subtype.ext hvd⟩
  let ef := Equiv.ofBijective f' hf'
  let eg := Equiv.ofBijective g' hg'
  refine ⟨ef.symm.trans eg, ?_⟩
  intro d v hv hd
  have hdf : d = ef ⟨v, hv⟩ := Subtype.ext hd
  rw [hdf]
  change (eg (ef.symm (ef ⟨v, hv⟩))).val = g v
  rw [ef.symm_apply_apply]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with globally certified left seams; not the paper result. -/
theorem kmswDiskWholePlaneBall_coupling_rel {n N r c : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventRel (windowCodeDecode N x) (2 * N) r c)
    (hglob : ∀ k ∈ kmswBallLeftSeamSet (windowCodeDecode N x) (2 * N) r c,
      minL (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + k) =
        L (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + k))
    (W : ℤ → Fin 3)
    (hW : ∀ i < 2 * N, shiftedStream W N i = windowCodeDecode N x i)
    (hglobW : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (windowCodeDecode N x) (2 * N) r c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (n' : ℕ) (hn' : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n') :
    let w := fun i => p.1 (i + 1)
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    let S := kmswStageBallVertices (fun _ _ => True)
      (kmswStage (windowCodeDecode N x) (2 * N)) r c
    let D := kmswStageBallVertices (fun _ _ => True) (kmswStage w n') r
      (kmswWindowPatchVertexMap w s (2 * N) c)
    let C := wholePlaneBallVertices W r (wholePlaneVertexι W N c)
    D = S.image (kmswWindowPatchVertexMap w s (2 * N)) ∧
      C = (wholePlaneVertexι W N) '' (S : Set ℕ) ∧
      ∃ e : {v // v ∈ D} ≃ {v // v ∈ C},
        ∀ (d : {v // v ∈ D}) (v : ℕ), v ∈ S →
          d.val = kmswWindowPatchVertexMap w s (2 * N) v →
          (e d).val = wholePlaneVertexι W N v := by
  classical
  dsimp only
  have hD := kmswDiskBallVertices_eq_image_future_rel h hev hglob n' hn'
  have hs : kmswStage (shiftedStream W N) (2 * N) =
      kmswStage (windowCodeDecode N x) (2 * N) := kmswStage_congr hW
  have heW : kmswWindowCaptureEventRel (shiftedStream W N) (2 * N) r c :=
    (kmswWindowCaptureEventRel_congr _ _ _ _ _ hW).mpr hev
  have hglobW' : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k) := by
    intro M hNM k hk
    apply hglobW M hNM k
    rw [kmswBallLeftSeamSet_congr _ _ _ _ _ hW] at hk
    exact hk
  have hC := wholePlaneBallVertices_eq_image_of_windowCaptureEventRel
    W N (2 * N) r c heW hglobW'
  rw [hs] at hC
  refine ⟨hD, hC, ?_⟩
  apply equiv_of_common_image
    (↑(kmswStageBallVertices (fun _ _ => True)
      (kmswStage (windowCodeDecode N x) (2 * N)) r c) : Set ℕ)
    (↑(kmswStageBallVertices (fun _ _ => True) (kmswStage (fun i => p.1 (i + 1)) n') r
      (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
        ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N) c)) : Set ℕ)
    (wholePlaneBallVertices W r (wholePlaneVertexι W N c))
    (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
      ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)) (wholePlaneVertexι W N)
  · intro a ha b hb hab
    exact kmswWindowPatchVertexMap_injOn _ _ _
      (by
        rw [← kmswStage_windowCodeDecode_bridge h (2 * N) le_rfl]
        exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (by
        rw [← kmswStage_windowCodeDecode_bridge h (2 * N) le_rfl]
        exact Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
  · intro a _ b _ hab
    exact wholePlaneVertexι_injective W N hab
  · ext v
    rw [hD]
    exact Finset.mem_image
  · exact hC

end DirectedDistances.KMSW
