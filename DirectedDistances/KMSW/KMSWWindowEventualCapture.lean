module

public import DirectedDistances.KMSW.KMSWWholePlaneBallCapture

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem strong_stage_congr {u u' : ℕ → Fin 3} {m : ℕ}
    (hcode : ∀ i < m, u i = u' i) : kmswStage u m = kmswStage u' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change kmswStep (kmswStage u m) (u m) = kmswStep (kmswStage u' m) (u' m)
      rw [ih (fun i hi => hcode i (by omega)), hcode m (by omega)]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The entire radius ball avoids the upper frontier. -/
@[expose] def kmswWindowCaptureEventStrong (u : ℕ → Fin 3) (m r c : ℕ) : Prop :=
  kmswWindowCaptureEvent u m r c ∧
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      ¬ UpperFrontierEndpoint (kmswStage u m) v

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Only indices in `[0, m)` affect the strong event. -/
theorem kmswWindowCaptureEventStrong_congr (u u' : ℕ → Fin 3) (m r c : ℕ)
    (hcode : ∀ i < m, u i = u' i) :
    kmswWindowCaptureEventStrong u m r c ↔ kmswWindowCaptureEventStrong u' m r c := by
  have hs := strong_stage_congr hcode
  unfold kmswWindowCaptureEventStrong
  rw [kmswWindowCaptureEvent_congr u u' m r c hcode, hs]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The strong event is a measurable cylinder event. -/
theorem measurableSet_kmswWindowCaptureEventStrong (m r c : ℕ) :
    MeasurableSet {u : ℕ → Fin 3 | kmswWindowCaptureEventStrong u m r c} := by
  let pref : (ℕ → Fin 3) → (Fin m → Fin 3) := fun u i => u i.val
  let extend : (Fin m → Fin 3) → (ℕ → Fin 3) :=
    fun a i => if hi : i < m then a ⟨i, hi⟩ else 0
  let A : Set (Fin m → Fin 3) := {a | kmswWindowCaptureEventStrong (extend a) m r c}
  have hpref : Measurable pref :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have heq : {u : ℕ → Fin 3 | kmswWindowCaptureEventStrong u m r c} = pref ⁻¹' A := by
    ext u
    change kmswWindowCaptureEventStrong u m r c ↔
      kmswWindowCaptureEventStrong (extend (pref u)) m r c
    apply kmswWindowCaptureEventStrong_congr
    intro i hi
    dsimp only [extend, pref]
    rw [dite_eq_left hi]
  rw [heq]
  exact hA.preimage hpref

private theorem strong_fresh (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrong u m r c)
    (hcode : ∀ i < m, w (s + i) = u i) :
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
  classical
  intro v hv
  have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  refine ⟨?_, kmswWindowPatchVertexMap_fresh_for_every_prefix u m v hb
    (hev.1.2.1 v hv).1 (hev.1.2.1 v hv).2 w s hcode⟩
  rw [strong_stage_congr hcode]
  exact hb

private theorem strong_front (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrong u m r c)
    (hcode : ∀ i < m, w (s + i) = u i) :
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      ¬ UpperFrontierEndpoint (kmswStage w (s + m))
        (kmswWindowPatchVertexMap w s m v) := by
  classical
  intro v hv
  have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  exact kmswWindowPatchVertexMap_not_upperFrontier_for_every_prefix u m v hb
    (hev.1.2.1 v hv).1 (hev.1.2.1 v hv).2 (hev.2 v hv) w s hcode

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Any later edge incident to the ball image was allocated by the window end.
One endpoint suffices; all geometric edge identities are retained. -/
theorem kmswWindowCaptureEventStrong_edge_allocated
    (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrong u m r c)
    (hcode : ∀ i < m, w (s + i) = u i)
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
      (strong_front u w m r c s hev hcode v hv) n hn e he hnew).1 hve.symm
  · obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp heast
    exact (kmswStage_no_new_incidence_of_not_upperFrontier w (s + m) _
      (strong_front u w m r c s hev hcode v hv) n hn e he hnew).2 hve.symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
At the window endpoint the induced-edge map is bijective. -/
theorem kmswWindowCaptureEventStrong_edgeMapOn_bijective
    (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrong u m r c)
    (hcode : ∀ i < m, w (s + i) = u i) :
    Function.Bijective (kmswWindowFreshSetEdgeMapOn w s m
      (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c)) := by
  exact kmswWindowFreshSetEdgeMap_bijective w s m _
    (strong_fresh u w m r c s hev hcode)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The induced-edge map is a bijection onto every later stage's edges with
both endpoints in the captured ball image. -/
theorem kmswWindowCaptureEventStrong_edge_bijOn_future
    (u w : ℕ → Fin 3) (m r c s : ℕ)
    (hev : kmswWindowCaptureEventStrong u m r c)
    (hcode : ∀ i < m, w (s + i) = u i) (n : ℕ) (hn : s + m ≤ n) :
    let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c
    Set.BijOn (fun e => (kmswWindowFreshSetEdgeMap w s m e).val)
      (kmswWindowFreshSetSourceEdges w s m S)
      {e : ℕ | e < (kmswStage w n).nextEdge ∧
        (kmswStage w n).west e ∈ S.image (kmswWindowPatchVertexMap w s m) ∧
        (kmswStage w n).east e ∈ S.image (kmswWindowPatchVertexMap w s m)} := by
  classical
  dsimp only
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c
  have hb := kmswWindowCaptureEventStrong_edgeMapOn_bijective u w m r c s hev hcode
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
    have hold := kmswWindowCaptureEventStrong_edge_allocated u w m r c s hev hcode
      n hn e he.1 (Or.inl he.2.1)
    have hs := kmswStage_endpoints_stable w hn hold
    have htarget : (⟨e, hold⟩ : Fin (kmswStage w (s + m)).nextEdge) ∈
        kmswWindowFreshSetTargetEdges w s m S := by
      exact ⟨hs.1 ▸ he.2.1, hs.2 ▸ he.2.2⟩
    obtain ⟨f, hf⟩ := hb.2 ⟨⟨e, hold⟩, htarget⟩
    exact ⟨f.val, f.property, congrArg (fun x => x.val.val) hf⟩

private theorem strong_patch_colimit (W : ℤ → Fin 3) (N M m v : ℕ)
    (hNM : N ≤ M) (hv : v < (kmswStage (shiftedStream W N) m).nextVertex) :
    wholePlaneVertexι W M (kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m v) =
      wholePlaneVertexι W N v := by
  have hv' : v <
      (kmswStage (fun i => shiftedStream W M ((M - N) + i)) m).nextVertex := by
    rw [shiftedStream_shift W N M hNM]
    exact hv
  rw [← kmswWindowVertexMapInf_eq_stage _ _ _ _ hv']
  exact congrFun (wholePlaneVertexι_trans W N M hNM) v

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Window induced geometric edges correspond bijectively to the colimit induced
ball edges, preserving edge identity and multiedges. -/
theorem kmswWindowCaptureEventStrong_wholePlaneEdge_bijOn
    (W : ℤ → Fin 3) (N m r c : ℕ)
    (hev : kmswWindowCaptureEventStrong (shiftedStream W N) m r c) :
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
  have hball := wholePlaneBallVertices_eq_image_of_windowCaptureEvent W N m r c hev.1
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
      exact (hfw.trans hve.symm).trans (strong_patch_colimit W N M m v hNM hvb).symm
    have heast : edgeEast (shiftedStream W M) f =
        kmswWindowPatchVertexMap (shiftedStream W M) (M - N) m z := by
      apply wholePlaneVertexι_injective W M
      exact (hfe.trans hze.symm).trans (strong_patch_colimit W N M m z hNM hzb).symm
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
    have hb := kmswWindowCaptureEventStrong_edge_bijOn_future
      (shiftedStream W N) (shiftedStream W M) m r c (M - N) hev
      (fun i _ => congrFun (shiftedStream_shift W N M hNM) i) n hn
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

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The ordinary capture event at radius `r + 1` supplies the strong event at radius `r`. -/
theorem kmswWindowCaptureEventStrong_of_succ (u : ℕ → Fin 3) (m r c : ℕ)
    (hev : kmswWindowCaptureEvent u m (r + 1) c) :
    kmswWindowCaptureEventStrong u m r c := by
  classical
  have hsub {a b : ℕ} (hab : a ≤ b) {v : ℕ}
      (hv : v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) a c) :
      v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) b c := by
    obtain ⟨hbound, k, hk, hp⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hbound, k, hk.trans hab, hp⟩
  have hfront : ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      ¬ UpperFrontierEndpoint (kmswStage u m) v := by
    intro v hv
    exact hev.2.2 v (by simpa only [Nat.add_sub_cancel] using hv)
  refine ⟨⟨hev.1, ?_, ?_⟩, hfront⟩
  · intro v hv
    exact hev.2.1 v (hsub (by omega) hv)
  · intro v hv
    exact hfront v (hsub (by omega) hv)

end DirectedDistances.KMSW
