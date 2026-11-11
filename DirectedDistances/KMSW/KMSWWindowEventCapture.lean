module

public import DirectedDistances.KMSW.KMSWWindowDeterminedCapture
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result. -/

public section
namespace DirectedDistances.KMSW

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

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Non-seam vertices outside the window upper frontier stay outside the global
upper frontier, for every compatible prefix. -/
theorem kmswWindowPatchVertexMap_not_upperFrontier_for_every_prefix
    (u : ℕ → Fin 3) (m v : ℕ)
    (hv : v < (kmswStage u m).nextVertex) (hbase : 2 ≤ v)
    (hnonseam : ∀ k < m, v = (kmswStage u k).nextVertex →
      (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ []) ∧
      (kmswCodeStep (u k) = .left →
        (kmswStage u k).UL.dropLast.reverse ≠ []))
    (hfront : ¬ UpperFrontierEndpoint (kmswStage u m) v) :
    ∀ (w : ℕ → Fin 3) (s : ℕ), (∀ i < m, w (s + i) = u i) →
      ¬ UpperFrontierEndpoint (kmswStage w (s + m))
        (kmswWindowPatchVertexMap w s m v) := by
  intro w s hcode
  have hs := event_stage_eq u w s m hcode m le_rfl
  apply event_frontier_transport w s m v
  · rw [hs]
    exact hv
  · exact kmswWindowPatchVertexMap_fresh_for_every_prefix
      u m v hv hbase hnonseam w s hcode
  · rw [hs]
    exact hfront

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The centre is an allocated vertex. The radius ball avoids initial vertices and
seam allocations; its inner ball avoids the window upper frontier. -/
@[expose] def kmswWindowCaptureEvent (u : ℕ → Fin 3) (m r c : ℕ) : Prop :=
  c < (kmswStage u m).nextVertex ∧
    (∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      2 ≤ v ∧ ∀ k < m, v = (kmswStage u k).nextVertex →
        (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ []) ∧
        (kmswCodeStep (u k) = .left →
          (kmswStage u k).UL.dropLast.reverse ≠ [])) ∧
    (∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) (r - 1) c,
      ¬ UpperFrontierEndpoint (kmswStage u m) v)

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

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The event implies exact all-geometric-edge ball capture at every later stage,
uniformly over compatible prefixes and continuations and with parametric centre. -/
theorem kmswWindowCaptureEvent_ballVerticesImageEq_future
    (u : ℕ → Fin 3) (m r c : ℕ) (hevent : kmswWindowCaptureEvent u m r c) :
    ∀ (w : ℕ → Fin 3) (s : ℕ), (∀ i < m, w (s + i) = u i) →
      ∀ n ≥ s + m,
        (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
            (kmswWindowPatchVertexMap w s m) =
          kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
            (kmswWindowPatchVertexMap w s m c) := by
  classical
  intro w s hcode n hn
  obtain ⟨hc, hball, hinner⟩ := hevent
  have hs := event_stage_eq u w s m hcode m le_rfl
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c
  have hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
    intro v hv
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
    obtain ⟨hbase, hnonseam⟩ := hball v hv
    refine ⟨?_, kmswWindowPatchVertexMap_fresh_for_every_prefix
      u m v hb hbase hnonseam w s hcode⟩
    rw [hs]
    exact hb
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
    exact kmswWindowPatchVertexMap_not_upperFrontier_for_every_prefix
      u m v hb (hball v hvS).1 (hball v hvS).2 (hinner v hvin) w s hcode
  have hresult := kmswWindowAllEdgesBallVerticesImageEq_future
    w s m S r c hS hClosed hfront n hn
  rw [hs] at hresult
  exact hresult

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Only the letters with indices strictly below `m` affect the event. -/
theorem kmswWindowCaptureEvent_congr (u u' : ℕ → Fin 3) (m r c : ℕ)
    (hcode : ∀ i < m, u i = u' i) :
    kmswWindowCaptureEvent u m r c ↔ kmswWindowCaptureEvent u' m r c := by
  have hprefix : ∀ i < m, u (0 + i) = u' i := by
    simpa only [Nat.zero_add] using hcode
  have hstage := event_stage_eq u' u 0 m hprefix
  simp only [Nat.zero_add] at hstage
  have hnonseam (v : ℕ) :
      (∀ k < m, v = (kmswStage u k).nextVertex →
        (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ []) ∧
        (kmswCodeStep (u k) = .left →
          (kmswStage u k).UL.dropLast.reverse ≠ [])) ↔
      (∀ k < m, v = (kmswStage u' k).nextVertex →
        (kmswCodeStep (u' k) = .down → (kmswStage u' k).UR ≠ []) ∧
        (kmswCodeStep (u' k) = .left →
          (kmswStage u' k).UL.dropLast.reverse ≠ [])) := by
    constructor
    · intro h k hk hv
      rw [← hstage k (by omega)] at hv ⊢
      rw [← hcode k hk]
      exact h k hk hv
    · intro h k hk hv
      rw [hstage k (by omega)] at hv ⊢
      rw [hcode k hk]
      exact h k hk hv
  unfold kmswWindowCaptureEvent
  rw [hstage m le_rfl]
  simp_rw [hnonseam]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The capture event is a measurable cylinder event in the code stream. -/
theorem measurableSet_kmswWindowCaptureEvent (m r c : ℕ) :
    MeasurableSet {u : ℕ → Fin 3 | kmswWindowCaptureEvent u m r c} := by
  let pref : (ℕ → Fin 3) → (Fin m → Fin 3) := fun u i => u i.val
  let extend : (Fin m → Fin 3) → (ℕ → Fin 3) :=
    fun a i => if hi : i < m then a ⟨i, hi⟩ else 0
  let A : Set (Fin m → Fin 3) := {a | kmswWindowCaptureEvent (extend a) m r c}
  have hpref : Measurable pref :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have heq : {u : ℕ → Fin 3 | kmswWindowCaptureEvent u m r c} = pref ⁻¹' A := by
    ext u
    change kmswWindowCaptureEvent u m r c ↔
      kmswWindowCaptureEvent (extend (pref u)) m r c
    apply kmswWindowCaptureEvent_congr
    intro i hi
    dsimp only [extend, pref]
    rw [dite_eq_left hi]
  rw [heq]
  exact hA.preimage hpref

end DirectedDistances.KMSW
