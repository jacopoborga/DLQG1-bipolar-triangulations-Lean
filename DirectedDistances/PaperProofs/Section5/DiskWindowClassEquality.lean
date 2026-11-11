module

public import DirectedDistances.PaperProofs.Section5.DiskBSBallLaw
public import DirectedDistances.PaperProofs.Section5.DiskWindowFramedCapture
public import DirectedDistances.PaperProofs.Section5.UIBHBOTWindowClassCompare
public import DirectedDistances.KMSW.InfiniteRotation

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Disk prefix and window identifications, retaining the distinction between the
bridge endpoint parameter `ell` and the independently sampled level `p.2`.

The final decoder/class identification is not established here. In the imported
interface, `diskBridgePrefix` and `diskBridgeDecoderCore` have hidden bodies;
no exported on-support evaluation theorem is available from their defining module.
Ordered-frame and outer-face transport also remain assembly obligations. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private theorem window_valid {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
  unfold bridgeOptionWindow at h
  split at h
  · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
  · contradiction

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The finite padded code and the full shifted bridge give the same disk stage. -/
theorem diskWindowClass_prefix_stage {ell n : ℕ}
    (p : (ℕ → Fin 3) × ℕ) (c : KMSWLeftWalkClass (ell + 1) n)
    (hc : c.val = fun i => p.1 (i.val + 1)) :
    kmswStage (finiteCodeExtend (n := n + 1) c.val) n =
      kmswStage (fun i => p.1 (i + 1)) n := by
  apply kmswStage_congr
  intro i hi
  simp only [finiteCodeExtend, Nat.add_sub_cancel, hc, dite_eq_left hi]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The full disk stage and the window endpoint have identical vertex balls on capture. -/
theorem diskWindowClass_vertex_ball_stable {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let w := fun i => p.1 (i + 1)
    kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r (activeInitial w T) =
      kmswStageBallVertices (fun _ _ => True) (kmswStage w (T + N)) r
        (activeInitial w T) := by
  exact (diskBall_eq_image_of_eventK_noDip h hev hnd n (window_valid h).2).trans
    (diskBall_eq_image_of_eventK_noDip h hev hnd
      ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N) le_rfl).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The decoded class equals the class read from the shifted bridge window. -/
theorem diskWindowClass_decoded_eq_shift {n N r : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    uibhbotDecodedWindowBallClass N r x =
      uibhbotWindowStageBallClass N r
        (fun i => p.1 ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + i + 1)) := by
  apply uibhbotWindowStageBallClass_eq_prefix
  intro i hi
  exact windowCodeDecode_bridge h i hi

private theorem window_code {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    ∀ i < 2 * N, p.1 ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + i + 1) =
      windowCodeDecode N x i := fun i hi => (windowCodeDecode_bridge h i hi).symm

private theorem dart_mem_iff (s : State) (r c : ℕ) (d : StageDart s.nextEdge) :
    d ∈ kmswStageBallDarts (fun _ _ => True) s r c ↔
      s.west d.1.val ∈ kmswStageBallVertices (fun _ _ => True) s r c ∧
        s.east d.1.val ∈ kmswStageBallVertices (fun _ _ => True) s r c := by
  rcases d with ⟨e, b⟩
  cases b <;> simp [kmswStageBallDarts_mem_iff, stageEndpoint, edgeFlip, and_comm]

private theorem window_fresh {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
        (activeInitial u N),
      v < (kmswStage (fun i => w (s + i)) (2 * N)).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s (2 * N) v := by
  classical
  dsimp only
  let u := windowCodeDecode N x
  let w := fun i => p.1 (i + 1)
  let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
  have hstage : kmswStage (fun i => w (s + i)) (2 * N) = kmswStage u (2 * N) :=
    kmswStage_congr (window_code h)
  have hglob := kmswDiskSeam_hglob_of_noDip h r (activeInitial u N) K0 hev.2 hnd
  intro v hv
  have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  refine ⟨by rw [hstage]; exact hb, ?_⟩
  apply kmswWindowPatchVertexMap_fresh_of_global_seams u (2 * N) v hb
    (hev.1.1.2.1 v hv).1 w s (window_code h)
  intro k hk hcreate
  refine ⟨(hev.1.1.2.1 v hv).2 k hk hcreate, ?_⟩
  intro hleft
  by_cases hnonseam : (kmswStage u k).UL.dropLast.reverse ≠ []
  · exact Or.inl hnonseam
  · apply Or.inr
    apply hglob k
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,
      ⟨v, hv, hcreate⟩, hleft, not_not.mp hnonseam⟩

private theorem window_frontier_transport (w : ℕ → Fin 3) (s m v : ℕ)
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

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The window dart equivalence at its endpoint needs no cone condition at the sampled level. -/
theorem diskWindowClass_endpoint_darts_equiv {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    let c := activeInitial u N
    ∃ E : KMSWStageBallDart (fun _ _ => True)
          (kmswStage (fun i => w (s + i)) (2 * N)) r c ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (s + 2 * N)) r
          (kmswWindowPatchVertexMap w s (2 * N) c),
      ∀ d, (E d).1 = kmswWindowDartMap w s (2 * N) d.1 := by
  classical
  dsimp only
  let u := windowCodeDecode N x
  let w := fun i => p.1 (i + 1)
  let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
  let c := activeInitial u N
  have hstage : kmswStage (fun i => w (s + i)) (2 * N) = kmswStage u (2 * N) :=
    kmswStage_congr (window_code h)
  have hfresh := window_fresh h hev hnd
  dsimp only at hfresh
  have hglob := kmswDiskSeam_hglob_of_noDip h r c K0 hev.2 hnd
  have himage := kmswWindowCaptureEventRel_ballVerticesImageEq_future u (2 * N) r c
    hev.1.1 w s (window_code h) hglob (s + 2 * N) le_rfl
  rw [← hstage] at himage hfresh
  refine ⟨Equiv.ofBijective _
    (kmswWindowBallDartMap_bijective_of_fresh_image w s (2 * N) r c hfresh himage), ?_⟩
  intro d
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every dart touching the captured disk ball was allocated by the window endpoint.
The bridge endpoint and sampled level need not coincide. -/
theorem diskWindowClass_incident_edge_allocated {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let w := fun i => p.1 (i + 1)
    ∀ j, T + N ≤ j → ∀ e, e < (kmswStage w j).nextEdge →
      ((kmswStage w j).west e ∈
          kmswStageBallVertices (fun _ _ => True) (kmswStage w j) r
            (activeInitial w T) ∨
        (kmswStage w j).east e ∈
          kmswStageBallVertices (fun _ _ => True) (kmswStage w j) r
            (activeInitial w T)) →
      e < (kmswStage w (T + N)).nextEdge := by
  dsimp only
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let w := fun i => p.1 (i + 1)
  let u := windowCodeDecode N x
  have hs : T - N + 2 * N = T + N := by
    have hv := (window_valid h).1
    dsimp only [T]
    omega
  intro j hj e he hend
  have hballs := diskBall_eq_image_of_eventK_noDip h hev hnd j hj
  rw [hballs] at hend
  have ha := kmswWindowCaptureEventStrongRel_edge_allocated u w (2 * N) r
    (activeInitial u N) (T - N) hev.1 (window_code h)
    (kmswDiskSeam_hglob_of_noDip h r (activeInitial u N) K0 hev.2 hnd)
    j (by omega) e he hend
  simpa only [hs] using ha

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The endpoint-stage ball darts and final disk-stage ball darts are equivalent
by unchanged geometric edge identities and endpoint sides. -/
theorem diskWindowClass_stage_darts_equiv {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let w := fun i => p.1 (i + 1)
    ∃ E : KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r (activeInitial w T),
      ∀ d, (E d).1.1.val = d.1.1.val ∧ (E d).1.2 = d.1.2 := by
  classical
  dsimp only
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let w := fun i => p.1 (i + 1)
  have htn : T + N ≤ n := (window_valid h).2
  have hballs :
      kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r (activeInitial w T) =
        kmswStageBallVertices (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T) := diskWindowClass_vertex_ball_stable h hev hnd
  have hends (e : ℕ) (he : e < (kmswStage w (T + N)).nextEdge) :
      (kmswStage w n).west e = (kmswStage w (T + N)).west e ∧
        (kmswStage w n).east e = (kmswStage w (T + N)).east e :=
    kmswStage_endpoints_stable w htn he
  have hbound (d : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
      (activeInitial w T)) : d.1.1.val < (kmswStage w (T + N)).nextEdge := by
    have hd := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2
    apply diskWindowClass_incident_edge_allocated h hev hnd n htn _ d.1.1.isLt
    cases hb : d.1.2
    · exact Or.inl (by simpa only [stageEndpoint, hb, Bool.false_eq_true,
        ite_false] using hd.1)
    · exact Or.inr (by simpa only [stageEndpoint, hb, ite_true] using hd.1)
  let f : KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
      (activeInitial w T) →
      KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r (activeInitial w T) :=
    fun d => ⟨(⟨d.1.1.val, d.1.1.isLt.trans_le (kmswStage_nextEdge_mono w htn)⟩,
      d.1.2), by
      rw [dart_mem_iff]
      have hd := (dart_mem_iff _ _ _ _).mp d.2
      have hs := hends d.1.1.val d.1.1.isLt
      simpa only [hs.1, hs.2, hballs] using hd⟩
  let g : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
      (activeInitial w T) →
      KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
        (activeInitial w T) := fun d => ⟨(⟨d.1.1.val, hbound d⟩, d.1.2), by
      rw [dart_mem_iff]
      have hd := (dart_mem_iff _ _ _ _).mp d.2
      have hs := hends d.1.1.val (hbound d)
      simpa only [hs.1, hs.2, hballs] using hd⟩
  refine ⟨⟨f, g, ?_, ?_⟩, fun _ => ⟨rfl, rfl⟩⟩
  · intro d
    apply Subtype.ext
    rfl
  · intro d
    apply Subtype.ext
    rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Ambient rotation at captured vertices is unchanged after the window endpoint. -/
theorem diskWindowClass_stage_rotation {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let w := fun i => p.1 (i + 1)
    ∀ j (hj : T + N ≤ j) (d : StageDart (kmswStage w (T + N)).nextEdge),
      stageEndpoint (kmswStage w (T + N)) d ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T) →
      stageRot w j (outerSucc_castDart (kmswStage_nextEdge_mono w hj) d) =
        outerSucc_castDart (kmswStage_nextEdge_mono w hj) (stageRot w (T + N) d) := by
  dsimp only
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let w := fun i => p.1 (i + 1)
  intro j hj d hd
  change T + N ≤ j at hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hballs :
        kmswStageBallVertices (fun _ _ => True) (kmswStage w (j + 1)) r
            (activeInitial w T) =
          kmswStageBallVertices (fun _ _ => True) (kmswStage w (T + N)) r
            (activeInitial w T) :=
      (diskBall_eq_image_of_eventK_noDip h hev hnd (j + 1) (by omega)).trans
        (diskBall_eq_image_of_eventK_noDip h hev hnd (T + N) le_rfl).symm
    have hnew : ∀ e, (kmswStage w j).nextEdge ≤ e →
        e < (kmswStage w (j + 1)).nextEdge →
        (kmswStage w (j + 1)).west e ≠ stageEndpoint (kmswStage w (T + N)) d ∧
          (kmswStage w (j + 1)).east e ≠
            stageEndpoint (kmswStage w (T + N)) d := by
      intro e hje he
      have hbound (hend :
          (kmswStage w (j + 1)).west e ∈
              kmswStageBallVertices (fun _ _ => True) (kmswStage w (j + 1)) r
                (activeInitial w T) ∨
            (kmswStage w (j + 1)).east e ∈
              kmswStageBallVertices (fun _ _ => True) (kmswStage w (j + 1)) r
                (activeInitial w T)) : False := by
        have ha : e < (kmswStage w (T + N)).nextEdge :=
          diskWindowClass_incident_edge_allocated h hev hnd
            (j + 1) (by omega) e he hend
        have hm := kmswStage_nextEdge_mono w hj
        omega
      constructor
      · intro heq
        apply hbound
        exact Or.inl (by rw [heq, hballs]; exact hd)
      · intro heq
        apply hbound
        exact Or.inr (by rw [heq, hballs]; exact hd)
    have hep : stageEndpoint (kmswStage w j)
        (outerSucc_castDart (kmswStage_nextEdge_mono w hj) d) =
          stageEndpoint (kmswStage w (T + N)) d := by
      have hs := kmswStage_endpoints_stable w hj d.1.isLt
      cases hb : d.2 <;>
        simp only [outerSucc_castDart, stageEndpoint, hb, Bool.false_eq_true,
          ite_false, ite_true, Fin.val_castLE, hs.1, hs.2]
    have hs := stageRot_step_local w j _ hnew
      (outerSucc_castDart (kmswStage_nextEdge_mono w hj) d) hep
    rw [ih] at hs
    exact hs

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The entire captured ball avoids the full stage's upper frontier. -/
theorem diskWindowClass_ball_not_upper_frontier {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let w := fun i => p.1 (i + 1)
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage w (T + N)) r
        (activeInitial w T),
      ¬ UpperFrontierEndpoint (kmswStage w (T + N)) v := by
  dsimp only
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let w := fun i => p.1 (i + 1)
  let u := windowCodeDecode N x
  let s := T - N
  have hsm : s + 2 * N = T + N := by
    have hNT := (window_valid h).1
    dsimp only [s, T]
    omega
  have hstage : kmswStage (fun i => w (s + i)) (2 * N) = kmswStage u (2 * N) :=
    kmswStage_congr (window_code h)
  intro v hv
  rw [diskBall_eq_image_of_eventK_noDip h hev hnd (T + N) le_rfl] at hv
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  have hfresh := window_fresh h hev hnd z hz
  have hfront : ¬ UpperFrontierEndpoint (kmswStage (fun i => w (s + i)) (2 * N)) z := by
    rw [hstage]
    exact hev.1.2 z hz
  have hn := window_frontier_transport w s (2 * N) z hfresh.1 hfresh.2 hfront
  simpa only [hsm] using hn

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Present and missing edge tags at captured vertices are unchanged at every later stage. -/
theorem diskWindowClass_stage_present {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let w := fun i => p.1 (i + 1)
    ∀ j, T + N ≤ j → ∀ d : StageDart (kmswStage w (T + N)).nextEdge,
      stageEndpoint (kmswStage w (T + N)) d ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T) →
      (kmswStage w j).present d.1.val = (kmswStage w (T + N)).present d.1.val := by
  dsimp only
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let w := fun i => p.1 (i + 1)
  intro j hj d hd
  change T + N ≤ j at hj
  have hfront := diskWindowClass_ball_not_upper_frontier h hev hnd _ hd
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have he := d.1.isLt.trans_le (kmswStage_nextEdge_mono w hj)
    have hactive : (kmswStage w (j + 1)).active ∈
        (kmswStage w (j + 1)).UL ++ (kmswStage w (j + 1)).UR := by
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last w (j + 1)
      rw [hxs]
      simp
    have hf := kmswStage_upperFrontier_endpoints w (T + N) (j + 1)
      (by omega) _ hactive
    have hne : d.1.val ≠ (kmswStage w (j + 1)).active := by
      intro hEq
      have hs := kmswStage_endpoints_stable w (show T + N ≤ j + 1 by omega) d.1.isLt
      apply hfront
      cases hb : d.2
      · have hv := hf.1
        rw [← hEq, hs.1] at hv
        simpa only [stageEndpoint, hb, Bool.false_eq_true, ite_false] using hv
      · have hv := hf.2
        rw [← hEq, hs.2] at hv
        simpa only [stageEndpoint, hb, ite_true] using hv
    change (kmswStep (kmswStage w j) (w j)).present d.1.val = _
    change d.1.val ≠ (kmswStep (kmswStage w j) (w j)).active at hne
    rw [kmswStep_present_existing _ _ he, ite_eq_right hne]
    exact ih


end DirectedDistances.PaperProofs.Section5
