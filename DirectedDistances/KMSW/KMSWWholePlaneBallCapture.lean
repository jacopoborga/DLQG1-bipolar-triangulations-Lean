module

public import DirectedDistances.KMSW.KMSWWindowEventCapture
public import DirectedDistances.KMSW.KMSWWholePlaneColimit

import DirectedDistances.KMSW.InfiniteRotation

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
window-code event; all-edges reading kept parametric w.r.t. Definition 3.8
(no reading adopted); not the paper result. The centre remains a parameter;
no UIBHBOT root is chosen. All geometric edge identities, including missing
edges and parallel edges, remain in the edge carrier. -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
all-edges reading kept parametric w.r.t. Definition 3.8 (no reading adopted);
not the paper result. -/
@[expose] def wholePlaneAdjacent (W : ℤ → Fin 3)
    (x y : WholePlaneVertex W) : Prop :=
  ∃ e : WholePlaneEdge W,
    (wholePlaneEdgeWest W e = x ∧ wholePlaneEdgeEast W e = y) ∨
    (wholePlaneEdgeWest W e = y ∧ wholePlaneEdgeEast W e = x)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
all-edges reading kept parametric w.r.t. Definition 3.8 (no reading adopted);
not the paper result. -/
inductive WholePlanePath (W : ℤ → Fin 3) (V : Set (WholePlaneVertex W))
    (root : WholePlaneVertex W) : ℕ → WholePlaneVertex W → Prop where
  | nil (hv : root ∈ V) : WholePlanePath W V root 0 root
  | snoc {n y z} (hpath : WholePlanePath W V root n y)
      (hy : y ∈ V) (hz : z ∈ V) (hadj : wholePlaneAdjacent W y z) :
      WholePlanePath W V root (n + 1) z

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
all-edges reading kept parametric w.r.t. Definition 3.8 (no reading adopted);
not the paper result. -/
@[expose] def wholePlaneDistanceLe (W : ℤ → Fin 3) (r : ℕ)
    (x y : WholePlaneVertex W) : Prop :=
  ∃ k, k ≤ r ∧ WholePlanePath W Set.univ x k y

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
all-edges reading kept parametric w.r.t. Definition 3.8 (no reading adopted);
not the paper result. The centre is a parameter. -/
@[expose] def wholePlaneBallVertices (W : ℤ → Fin 3) (r : ℕ)
    (x : WholePlaneVertex W) : Set (WholePlaneVertex W) :=
  {y | wholePlaneDistanceLe W r x y}

private def runAdjacent (w : ℕ → Fin 3) (x y : ℕ) : Prop :=
  ∃ e, (edgeWest w e = x ∧ edgeEast w e = y) ∨
    (edgeWest w e = y ∧ edgeEast w e = x)

private inductive RunPath (w : ℕ → Fin 3) (root : ℕ) : ℕ → ℕ → Prop where
  | nil : RunPath w root 0 root
  | snoc {k x y} (hp : RunPath w root k x) (ha : runAdjacent w x y) :
      RunPath w root (k + 1) y

private theorem run_path_trans (W : ℤ → Fin 3) (N M : ℕ) (hNM : N ≤ M)
    {c k v : ℕ} (hp : RunPath (shiftedStream W N) c k v) :
    RunPath (shiftedStream W M) (wholePlaneVertexTrans W N M hNM c) k
      (wholePlaneVertexTrans W N M hNM v) := by
  induction hp with
  | nil => exact .nil
  | snoc hp ha ih =>
      obtain ⟨e, ha | ha⟩ := ha
      · exact .snoc ih ⟨wholePlaneEdgeTrans W N M hNM e, Or.inl ⟨
          (wholePlaneEdgeTrans_west W N M hNM e).trans (congrArg _ ha.1),
          (wholePlaneEdgeTrans_east W N M hNM e).trans (congrArg _ ha.2)⟩⟩
      · exact .snoc ih ⟨wholePlaneEdgeTrans W N M hNM e, Or.inr ⟨
          (wholePlaneEdgeTrans_west W N M hNM e).trans (congrArg _ ha.1),
          (wholePlaneEdgeTrans_east W N M hNM e).trans (congrArg _ ha.2)⟩⟩

private theorem run_path_stage (w : ℕ → Fin 3) {c k v : ℕ}
    (hp : RunPath w c k v) :
    ∃ t, ∀ n ≥ t, KMSWStagePath (fun _ _ => True) (kmswStage w n) Set.univ c k v := by
  induction hp with
  | nil => exact ⟨0, fun _ _ => .nil (Set.mem_univ _)⟩
  | @snoc k x y hp ha ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨e, ha⟩ := ha
      refine ⟨max t e, ?_⟩
      intro n hn
      have he : e < (kmswStage w n).nextEdge :=
        (kmsw_edge_allocated_by_self w e).trans_le
          (kmswStage_nextEdge_mono w (by omega))
      have hs := edge_endpoints_eq w he
      apply KMSWStagePath.snoc (ht n (by omega)) (Set.mem_univ _) (Set.mem_univ _)
      rcases ha with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · exact ⟨(⟨e, he⟩, false), trivial, hs.1.trans hx, hs.2.trans hy⟩
      · exact ⟨(⟨e, he⟩, true), trivial, hs.2.trans hx, hs.1.trans hy⟩

private theorem colimit_path_run (W : ℤ → Fin 3) (N c : ℕ)
    {k : ℕ} {x : WholePlaneVertex W}
    (hp : WholePlanePath W Set.univ (wholePlaneVertexι W N c) k x) :
    ∃ M, ∃ hNM : N ≤ M, ∃ v,
      wholePlaneVertexι W M v = x ∧
        RunPath (shiftedStream W M) (wholePlaneVertexTrans W N M hNM c) k v := by
  induction hp with
  | nil =>
      refine ⟨N, le_rfl, c, rfl, ?_⟩
      rw [wholePlaneVertexTrans_self]
      exact .nil
  | @snoc k y z hp _ _ ha ih =>
      obtain ⟨M, hNM, v, hv, hpM⟩ := ih
      obtain ⟨e, ha⟩ := ha
      obtain ⟨⟨L, e⟩, rfl⟩ := Quotient.exists_rep e
      let K := max M L
      have hMK : M ≤ K := Nat.le_max_left M L
      have hLK : L ≤ K := Nat.le_max_right M L
      let a := wholePlaneVertexTrans W M K hMK v
      let f := wholePlaneEdgeTrans W L K hLK e
      have hpK := run_path_trans W M K hMK hpM
      have hc := congrFun (wholePlaneVertexTrans_comp W N M K hNM hMK) c
      change wholePlaneVertexTrans W M K hMK (wholePlaneVertexTrans W N M hNM c) =
        wholePlaneVertexTrans W N K (hNM.trans hMK) c at hc
      rw [hc] at hpK
      have hvK : wholePlaneVertexι W K a = y :=
        (congrFun (wholePlaneVertexι_trans W M K hMK) v).trans hv
      have hwK : wholePlaneVertexι W K (edgeWest (shiftedStream W K) f) =
          wholePlaneEdgeWest W (wholePlaneEdgeι W L e) := by
        rw [wholePlaneEdgeWest_ι, wholePlaneEdgeTrans_west]
        exact congrFun (wholePlaneVertexι_trans W L K hLK) _
      have heK : wholePlaneVertexι W K (edgeEast (shiftedStream W K) f) =
          wholePlaneEdgeEast W (wholePlaneEdgeι W L e) := by
        rw [wholePlaneEdgeEast_ι, wholePlaneEdgeTrans_east]
        exact congrFun (wholePlaneVertexι_trans W L K hLK) _
      rcases ha with ⟨hy, hz⟩ | ⟨hz, hy⟩
      · have hwa : edgeWest (shiftedStream W K) f = a :=
          wholePlaneVertexι_injective W K ((hwK.trans hy).trans hvK.symm)
        exact ⟨K, hNM.trans hMK, edgeEast (shiftedStream W K) f,
          heK.trans hz, .snoc hpK ⟨f, Or.inl ⟨hwa, rfl⟩⟩⟩
      · have hea : edgeEast (shiftedStream W K) f = a :=
          wholePlaneVertexι_injective W K ((heK.trans hy).trans hvK.symm)
        exact ⟨K, hNM.trans hMK, edgeWest (shiftedStream W K) f,
          hwK.trans hz, .snoc hpK ⟨f, Or.inr ⟨rfl, hea⟩⟩⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
length to a stage of some run `M ≥ N`, at arbitrarily late times in that run;
all-edges reading kept parametric w.r.t. Definition 3.8 (no reading adopted);
not the paper result. -/
theorem wholePlanePath_lift (W : ℤ → Fin 3) (N c : ℕ)
    {k : ℕ} {x : WholePlaneVertex W}
    (hp : WholePlanePath W Set.univ (wholePlaneVertexι W N c) k x) :
    ∃ M, ∃ hNM : N ≤ M, ∃ v, wholePlaneVertexι W M v = x ∧
      ∀ t, ∃ n ≥ t,
        KMSWStagePath (fun _ _ => True) (kmswStage (shiftedStream W M) n)
          Set.univ (wholePlaneVertexTrans W N M hNM c) k v := by
  obtain ⟨M, hNM, v, hv, hpM⟩ := colimit_path_run W N c hp
  obtain ⟨s, hs⟩ := run_path_stage _ hpM
  exact ⟨M, hNM, v, hv, fun t => ⟨max t s, Nat.le_max_left _ _,
    hs _ (Nat.le_max_right _ _)⟩⟩

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
window-code event; all-edges reading kept parametric w.r.t. Definition 3.8
(no reading adopted); not the paper result. The centre `c` remains a parameter;
no UIBHBOT root is chosen. -/
theorem wholePlaneBallVertices_eq_image_of_windowCaptureEvent
    (W : ℤ → Fin 3) (N m r c : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m r c) :
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
    have hballs := kmswWindowCaptureEvent_ballVerticesImageEq_future
      (shiftedStream W N) m r c hevent (shiftedStream W M) (M - N)
      (fun i _ => congrFun (shiftedStream_shift W N M hNM) i) n hn
    rw [← hballs] at hvBall
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hvBall
    refine ⟨u, hu, ?_⟩
    have huBound := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    exact (patch_colimit W N M m u hNM huBound).symm.trans
      ((congrArg (wholePlaneVertexι W M) huv).trans hv)
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk, hp⟩ := (Finset.mem_filter.mp hv).2
    exact ⟨k, hk, stage_path_colimit W N m hp⟩

end DirectedDistances.KMSW
