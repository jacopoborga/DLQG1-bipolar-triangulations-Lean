module

public import DirectedDistances.PaperProofs.Section5.DiskWindowFramedCapture
public import DirectedDistances.PaperProofs.Section5.DiskWindowClassEquality

/-! Helpers toward Proposition 5.16 (`prop-disk-bs-conv`), not paper results. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.RandomWalk

private theorem diskStageBall_window_valid {n N : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
  unfold bridgeOptionWindow at h
  split at h
  · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
  · contradiction

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The disk padded code and the increment stream agree through stage `n`. -/
theorem diskStageBall_stage_eq_walk {n : ℕ} (p : (ℕ → Fin 3) × ℕ)
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2) :
    ∃ c : KMSWLeftWalkClass (p.2 + 1) n,
      c.val = (fun i => p.1 (i.val + 1)) ∧
        ∃ k : Fin ((p.2 + 1) - 1), k.val + 1 = p.2 ∧
          kmswStage (finiteCodeExtend (n := n + 1) c.val) n =
            kmswStage (fun i => p.1 (i + 1)) n := by
  obtain ⟨c, hc, k, hk⟩ := diskWindowWalkClassAndIndex p hcone hpos
  refine ⟨c, hc, k, hk, ?_⟩
  apply kmswStage_congr
  intro i hi
  have hlt : i < n + 1 - 1 := by omega
  simp only [finiteCodeExtend]
  rw [hc]
  simp only [dite_eq_left hlt]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The stage-`n` and stage-`t` vertex balls are the same window-map image, where
`t` is the end of the captured window. Source: -/
theorem diskStageBall_vertices_eq_at_n_and_t
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let s := T - N
    let t := T + N
    let c := activeInitial u N
    (∃ c₀ : KMSWLeftWalkClass (p.2 + 1) n,
      c₀.val = (fun i => p.1 (i.val + 1)) ∧
        ∃ k₀ : Fin ((p.2 + 1) - 1), k₀.val + 1 = p.2 ∧
          kmswStage (finiteCodeExtend (n := n + 1) c₀.val) n =
            kmswStage w n) ∧
    kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
        (activeInitial w T) =
      (kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r c).image
        (kmswWindowPatchVertexMap w s (2 * N)) ∧
    kmswStageBallVertices (fun _ _ => True) (kmswStage w t) r
        (activeInitial w T) =
      (kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r c).image
        (kmswWindowPatchVertexMap w s (2 * N)) := by
  dsimp only
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let c := activeInitial u N
  have hvalid := diskStageBall_window_valid h
  have hn : T + N ≤ n := by dsimp [T]; exact hvalid.2
  have hstage := diskBall_eq_image_of_eventK_noDip h hev hnd n hn
  have ht : T + N ≤ T + N := le_rfl
  have hstageT := diskBall_eq_image_of_eventK_noDip h hev hnd (T + N) ht
  refine ⟨diskStageBall_stage_eq_walk p hcone hpos, ?_, ?_⟩
  · simpa [u, w, T, s, c] using hstage
  · simpa [u, w, T, s, c] using hstageT

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every dart in the stage-`n` ball has an edge ID already allocated at stage `t`. -/
theorem diskStageBall_edgeId_captured_at_t
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∀ d : StageDart (kmswStage w n).nextEdge,
      stageEndpoint (kmswStage w n) d ∈
          kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
            (activeInitial w T) →
      stageEndpoint (kmswStage w n) (edgeFlip _ d) ∈
          kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
            (activeInitial w T) →
      d.1.val < (kmswStage w (T + N)).nextEdge := by
  classical
  dsimp only
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let m := 2 * N
  let c := activeInitial u N
  have hvalid := diskStageBall_window_valid h
  have htn : T + N ≤ n := by dsimp [T]; exact hvalid.2
  have htn' : s + m ≤ n := by dsimp [s, m, T]; omega
  have hsm : s + m = T + N := by dsimp [s, m, T]; omega
  have hvertices := diskStageBall_vertices_eq_at_n_and_t h hev hcone hpos hnd
  dsimp only at hvertices
  rcases hvertices with ⟨_, hverticesN, hverticesT⟩
  have hcode : ∀ i < m, w (s + i) = u i := by
    intro i hi
    exact (windowCodeDecode_bridge h i hi).symm
  have hglob := kmswDiskSeam_hglob_of_noDip h r c K0 hev.2 hnd
  intro d hd₁ hd₂
  have hN₁ : stageEndpoint (kmswStage w n) d ∈
      (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
        (kmswWindowPatchVertexMap w s m) := by
    rw [← hverticesN]
    exact hd₁
  have hN₂ : stageEndpoint (kmswStage w n) (edgeFlip _ d) ∈
      (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
        (kmswWindowPatchVertexMap w s m) := by
    rw [← hverticesN]
    exact hd₂
  cases d with
  | mk e b =>
    cases b with
    | false =>
      have he := kmswWindowCaptureEventStrongRel_edge_allocated u w m r c s
        hev.1 hcode hglob n htn' e.val e.isLt
          (Or.inl (by simpa [stageEndpoint] using hN₁))
      rw [← hsm]
      simpa [w] using he
    | true =>
      have he := kmswWindowCaptureEventStrongRel_edge_allocated u w m r c s
        hev.1 hcode hglob n htn' e.val e.isLt
          (Or.inr (by simpa [stageEndpoint] using hN₁))
      rw [← hsm]
      simpa [w] using he

private theorem diskStageBall_vertex_complete_at_t
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p)
    (v : ℕ)
    (hv : v ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage (fun i => p.1 (i + 1))
        ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N)) r
      (activeInitial (fun i => p.1 (i + 1))
        ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat))) :
    ∀ e, edgeWest (fun i => p.1 (i + 1)) e = v ∨
      edgeEast (fun i => p.1 (i + 1)) e = v →
      e < (kmswStage (fun i => p.1 (i + 1))
        ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N)).nextEdge := by
  classical
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let m := 2 * N
  let c := activeInitial u N
  have hvalid := diskStageBall_window_valid h
  have hTN : N ≤ T := by dsimp [T]; exact hvalid.1
  have hvertices := diskStageBall_vertices_eq_at_n_and_t h hev hcone hpos hnd
  dsimp only at hvertices
  have hwindowImage : v ∈
      (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
        (kmswWindowPatchVertexMap w s m) := by
    rw [← hvertices.2.2]
    exact hv
  obtain ⟨v₀, hv₀, hmap⟩ := Finset.mem_image.mp hwindowImage
  have hcode : ∀ i < m, w (s + i) = u i := by
    intro i hi
    exact (windowCodeDecode_bridge h i hi).symm
  have hglob := kmswDiskSeam_hglob_of_noDip h r c K0 hev.2 hnd
  intro e he
  let q := max (T + N) e
  have hq : s + m ≤ q := by dsimp [q, s, m]; omega
  have heq : e < (kmswStage w q).nextEdge := by
    exact (kmsw_edge_allocated_by_self w e).trans_le
      (kmswStage_nextEdge_mono w (le_max_right _ _))
  have hends := edge_endpoints_eq w heq
  have hvImage :
      (kmswStage w q).west e ∈
          (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
            (kmswWindowPatchVertexMap w s m) ∨
        (kmswStage w q).east e ∈
          (kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c).image
            (kmswWindowPatchVertexMap w s m) := by
    rcases he with hw | heast
    · left
      rw [hends.1, hw, ← hmap]
      exact Finset.mem_image.mpr ⟨v₀, hv₀, rfl⟩
    · right
      rw [hends.2, heast, ← hmap]
      exact Finset.mem_image.mpr ⟨v₀, hv₀, rfl⟩
  have hcaptured := kmswWindowCaptureEventStrongRel_edge_allocated
    u w m r c s hev.1 hcode hglob q hq
    e heq hvImage
  have hsm : s + m = T + N := by dsimp [s, m]; omega
  rw [hsm] at hcaptured
  exact hcaptured

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The radius-ball dart sets at stages `n` and `T + N` are equivalent by the
edge-identity map, preserving edge IDs and dart sides. -/
theorem diskStageBallDartsEquiv_at_n_and_t
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) := by
  classical
  dsimp only
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let u := windowCodeDecode N x
  let s := T - N
  let m := 2 * N
  let c := activeInitial u N
  let t := T + N
  have hvalid := diskStageBall_window_valid h
  have htn : t ≤ n := by dsimp [t, T]; exact hvalid.2
  have hvertices := diskStageBall_vertices_eq_at_n_and_t h hev hcone hpos hnd
  dsimp only at hvertices
  have hballEq : kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
      (activeInitial w T) =
      kmswStageBallVertices (fun _ _ => True) (kmswStage w t) r
        (activeInitial w T) := hvertices.2.1.trans hvertices.2.2.symm
  have hbound (d : StageDart (kmswStage w n).nextEdge)
      (hd : d ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r
        (activeInitial w T)) : d.1.val < (kmswStage w t).nextEdge := by
    have hends := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp hd
    exact diskStageBall_edgeId_captured_at_t h hev hcone hpos hnd d hends.1 hends.2
  let down : ∀ d : StageDart (kmswStage w n).nextEdge,
      d.1.val < (kmswStage w t).nextEdge → StageDart (kmswStage w t).nextEdge :=
    fun d hd => ((⟨d.1.val, hd⟩), d.2)
  have hendpoint (d : StageDart (kmswStage w n).nextEdge)
      (hd : d.1.val < (kmswStage w t).nextEdge) :
      stageEndpoint (kmswStage w t) (down d hd) =
        stageEndpoint (kmswStage w n) d := by
    cases d with
    | mk e b =>
      have hs := kmswStage_endpoints_stable w htn hd
      cases b
      · simpa [down, stageEndpoint] using hs.1.symm
      · simpa [down, stageEndpoint] using hs.2.symm
  have hflipEndpoint (d : StageDart (kmswStage w n).nextEdge)
      (hd : d.1.val < (kmswStage w t).nextEdge) :
      stageEndpoint (kmswStage w t) (edgeFlip (kmswStage w t).nextEdge (down d hd)) =
        stageEndpoint (kmswStage w n) (edgeFlip (kmswStage w n).nextEdge d) := by
    cases d with
    | mk e b =>
      have hs := kmswStage_endpoints_stable w htn hd
      cases b
      · simpa [down, edgeFlip, stageEndpoint] using hs.2.symm
      · simpa [down, edgeFlip, stageEndpoint] using hs.1.symm
  let f : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
      (activeInitial w T) →
      KMSWStageBallDart (fun _ _ => True) (kmswStage w t) r
        (activeInitial w T) := fun d =>
    ⟨down d.1 (hbound d.1 d.2), by
      rw [kmswStageBallDarts_mem_iff]
      have hd := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2
      have hflipBound : (edgeFlip _ d.1).1.val < (kmswStage w t).nextEdge := by
        simpa [edgeFlip] using hbound d.1 d.2
      constructor
      · rw [← hballEq, hendpoint d.1 (hbound d.1 d.2)]
        exact hd.1
      · rw [← hballEq, hflipEndpoint d.1 (hbound d.1 d.2)]
        simpa using hd.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hp : (a.1.1.val, a.1.2) = (b.1.1.val, b.1.2) := by
        simpa [f] using
          congrArg (fun d : StageDart (kmswStage w t).nextEdge =>
            (d.1.val, d.2)) (congrArg Subtype.val hab)
      have hdart : a.1 = b.1 := by
        exact Prod.ext
          (show a.1.1 = b.1.1 by
            exact Fin.ext (by simpa using congrArg Prod.fst hp))
          (show a.1.2 = b.1.2 by simpa using congrArg Prod.snd hp)
      exact Subtype.ext hdart
    · intro b
      rcases b with ⟨⟨e, side⟩, hbSub⟩
      let d := outerSucc_castDart (kmswStage_nextEdge_mono w htn) (e, side)
      have hd : d ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) := by
        rw [kmswStageBallDarts_mem_iff]
        have hb := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp hbSub
        have hstart : stageEndpoint (kmswStage w n) d =
            stageEndpoint (kmswStage w t) (e, side) := by
          have hs := kmswStage_endpoints_stable w htn e.isLt
          cases side
          · simpa [d, outerSucc_castDart, stageEndpoint] using hs.1
          · simpa [d, outerSucc_castDart, stageEndpoint] using hs.2
        have hflip : stageEndpoint (kmswStage w n) (edgeFlip _ d) =
            stageEndpoint (kmswStage w t) (edgeFlip _ (e, side)) := by
          have hs := kmswStage_endpoints_stable w htn e.isLt
          cases side
          · simpa [d, outerSucc_castDart, stageEndpoint, edgeFlip] using hs.2
          · simpa [d, outerSucc_castDart, stageEndpoint, edgeFlip] using hs.1
        constructor
        · rw [hballEq, hstart]
          exact hb.1
        · rw [hballEq, hflip]
          exact hb.2
      refine ⟨⟨d, hd⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
  refine ⟨Equiv.ofBijective f hf, ?_, ?_⟩
  · intro d
    rfl
  · intro d
    rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The edge-identity equivalence commutes with dart reversal. Source: -/
theorem diskStageBallDartsEquiv_at_n_and_t_flip
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      ∀ d, e (kmswStageBallDartFlip (fun _ _ => True)
          (kmswStage w n) r (activeInitial w T) d) =
        kmswStageBallDartFlip (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T) (e d) := by
  classical
  dsimp only
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  obtain ⟨e, heId, heSide⟩ :=
    diskStageBallDartsEquiv_at_n_and_t h hev hcone hpos hnd
  refine ⟨e, ?_⟩
  intro d
  cases d with
  | mk d hd =>
    cases d with
    | mk edge side =>
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        calc
          (e (kmswStageBallDartFlip (fun _ _ => True) (kmswStage w n) r
            (activeInitial w T) ⟨(edge, side), hd⟩)).1.1.val = edge.val := by
              simpa [kmswStageBallDartFlip, edgeFlip] using
                heId (kmswStageBallDartFlip (fun _ _ => True)
                  (kmswStage w n) r (activeInitial w T) ⟨(edge, side), hd⟩)
          _ = (e ⟨(edge, side), hd⟩).1.1.val := by
            exact (heId ⟨(edge, side), hd⟩).symm
      · calc
          (e (kmswStageBallDartFlip (fun _ _ => True) (kmswStage w n) r
            (activeInitial w T) ⟨(edge, side), hd⟩)).1.2 = !side := by
              simpa [kmswStageBallDartFlip, edgeFlip] using
                heSide (kmswStageBallDartFlip (fun _ _ => True)
                  (kmswStage w n) r (activeInitial w T) ⟨(edge, side), hd⟩)
          _ = !(e ⟨(edge, side), hd⟩).1.2 := by
            simp [heSide ⟨(edge, side), hd⟩]

private theorem diskStageBallMapIso_core
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      (∀ d, e (kmswStageBallDartFlip (fun _ _ => True)
          (kmswStage w n) r (activeInitial w T) d) =
        kmswStageBallDartFlip (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T) (e d)) ∧
      (∀ d, e (kmswStageBallRot (fun _ _ => True) w n r
          (activeInitial w T) d) =
        kmswStageBallRot (fun _ _ => True) w (T + N) r
          (activeInitial w T) (e d)) ∧
      (∀ d, e ((kmswStageBallRot (fun _ _ => True) w n r
          (activeInitial w T)).symm d) =
        (kmswStageBallRot (fun _ _ => True) w (T + N) r
          (activeInitial w T)).symm (e d)) ∧
      (∀ d, (kmswStage w n).present d.1.1.val =
        (kmswStage w (T + N)).present (e d).1.1.val) ∧
      (∀ d, kmswStageBallMapMissing (fun _ _ => True) w n r
          (activeInitial w T) d ↔
        kmswStageBallMapMissing (fun _ _ => True) w (T + N) r
          (activeInitial w T) (e d)) := by
  classical
  dsimp only
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let t := T + N
  let P : KMSWStageEdgePredicate := fun _ _ => True
  let source := kmswStage w n
  let target := kmswStage w t
  let c := activeInitial w T
  have hvalid := diskStageBall_window_valid h
  have htn : T + N ≤ n := by
    dsimp only [T]
    exact hvalid.2
  obtain ⟨e, heId, heSide⟩ :=
    diskStageBallDartsEquiv_at_n_and_t h hev hcone hpos hnd
  have hvertices := diskStageBall_vertices_eq_at_n_and_t h hev hcone hpos hnd
  dsimp only at hvertices
  have hballs :
      kmswStageBallVertices P source r c = kmswStageBallVertices P target r c :=
    hvertices.2.1.trans hvertices.2.2.symm
  let castD : StageDart target.nextEdge → StageDart source.nextEdge :=
    fun d => outerSucc_castDart (kmswStage_nextEdge_mono w htn) d
  have hendpoint (d : StageDart target.nextEdge) :
      stageEndpoint source (castD d) = stageEndpoint target d := by
    cases d with
    | mk edge side =>
      have hs := kmswStage_endpoints_stable w htn edge.isLt
      cases hb : side <;>
        simp only [stageEndpoint, castD, outerSucc_castDart,
          Bool.false_eq_true, ↓reduceIte, Fin.val_castLE]
      · exact hs.1
      · exact hs.2
  have hcastFlip (d : StageDart target.nextEdge) :
      castD (edgeFlip _ d) = edgeFlip _ (castD d) := by
    cases d with
    | mk edge side => cases side <;> rfl
  have hballmem (d : StageDart target.nextEdge) :
      d ∈ kmswStageBallDarts P target r c ↔
        castD d ∈ kmswStageBallDarts P source r c := by
    rw [kmswStageBallDarts_mem_iff, kmswStageBallDarts_mem_iff]
    rw [hendpoint d, ← hcastFlip d, hendpoint (edgeFlip _ d), hballs]
  let U : Set (StageDart target.nextEdge) :=
    {d | stageEndpoint target d ∈ kmswStageBallVertices P target r c}
  have hU : ∀ d, d ∈ U → stageRot w t d ∈ U := by
    intro d hd
    change stageEndpoint target d ∈ kmswStageBallVertices P target r c at hd
    change stageEndpoint target (stageRot w t d) ∈
      kmswStageBallVertices P target r c
    have hsame :=
      (stageRot_sameCycle_iff_endpoint_eq w t d (stageRot w t d)).mp
        ⟨1, rfl⟩
    exact hsame ▸ hd
  have hstageRot := diskWindowClass_stage_rotation h hev hnd
  dsimp only at hstageRot
  have hcomm : ∀ d, d ∈ U →
      castD (stageRot w t d) = stageRot w n (castD d) := by
    intro d hd
    have hd' : stageEndpoint target d ∈
        kmswStageBallVertices P target r c := by
      change stageEndpoint target d ∈ kmswStageBallVertices P target r c at hd
      exact hd
    simpa only [castD, source, target, t] using
      (hstageRot n htn d hd').symm
  have hmem : ∀ d, d ∈ U →
      (d ∈ kmswStageBallDarts P target r c ↔
        castD d ∈ kmswStageBallDarts P source r c) := by
    intro d _
    exact hballmem d
  have hrotFor (d : KMSWStageBallDart P target r c) :
      castD ((kmswStageBallRot P w t r c d).1) =
        (kmswStageBallRot P w n r c
          ⟨castD d.1, (hballmem d.1).mp d.2⟩).1 := by
    have hdU : d.1 ∈ U := by
      change stageEndpoint target d.1 ∈ kmswStageBallVertices P target r c
      exact ((kmswStageBallDarts_mem_iff P target r c d.1).mp d.2).1
    have h := firstReturn_map_congr_of_invariant
      (stageRot w t) (stageRot w n)
      (kmswStageBallDarts P target r c)
      (kmswStageBallDarts P source r c) U castD hU hcomm hmem d hdU
    simpa only [kmswStageBallRot] using h
  have hback (d : KMSWStageBallDart P source r c) :
      castD (e d).1 = d.1 := by
    apply Prod.ext
    · apply Fin.ext
      change (e d).1.1.val = d.1.1.val
      exact heId d
    · exact heSide d
  have hrotation : ∀ d, e (kmswStageBallRot P w n r c d) =
      kmswStageBallRot P w t r c (e d) := by
    intro d
    have hdU : (e d).1 ∈ U := by
      change stageEndpoint target (e d).1 ∈
        kmswStageBallVertices P target r c
      exact ((kmswStageBallDarts_mem_iff P target r c (e d).1).mp
        (e d).2).1
    have hret := hrotFor (e d)
    have hsub :
        (⟨castD (e d).1, (hballmem (e d).1).mp (e d).2⟩ :
          KMSWStageBallDart P source r c) = d := by
      apply Subtype.ext
      exact hback d
    rw [hsub] at hret
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hval := congrArg
        (fun z : StageDart source.nextEdge => z.1.val) hret
      simp only [castD, outerSucc_castDart, Fin.val_castLE] at hval
      calc
        (e (kmswStageBallRot P w n r c d)).1.1.val =
            (kmswStageBallRot P w n r c d).1.1.val := heId _
        _ = (kmswStageBallRot P w t r c (e d)).1.1.val := hval.symm
    · have hside := congrArg
        (fun z : StageDart source.nextEdge => z.2) hret
      simp only [castD, outerSucc_castDart] at hside
      calc
        (e (kmswStageBallRot P w n r c d)).1.2 =
            (kmswStageBallRot P w n r c d).1.2 := heSide _
        _ = (kmswStageBallRot P w t r c (e d)).1.2 := hside.symm
  have hinvRotation : ∀ d, e ((kmswStageBallRot P w n r c).symm d) =
      (kmswStageBallRot P w t r c).symm (e d) := by
    intro d
    have h := hrotation ((kmswStageBallRot P w n r c).symm d)
    simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
      (congrArg (kmswStageBallRot P w t r c).symm h).symm
  have hflip : ∀ d, e (kmswStageBallDartFlip P source r c d) =
      kmswStageBallDartFlip P target r c (e d) := by
    intro d
    cases d with
    | mk d hd =>
      cases d with
      | mk edge side =>
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          calc
            (e (kmswStageBallDartFlip P source r c
              ⟨(edge, side), hd⟩)).1.1.val = edge.val := by
                simpa [kmswStageBallDartFlip, edgeFlip] using
                  heId (kmswStageBallDartFlip P source r c
                    ⟨(edge, side), hd⟩)
            _ = (e ⟨(edge, side), hd⟩).1.1.val := by
              exact (heId ⟨(edge, side), hd⟩).symm
        · calc
            (e (kmswStageBallDartFlip P source r c
              ⟨(edge, side), hd⟩)).1.2 = !side := by
                simpa [kmswStageBallDartFlip, edgeFlip] using
                  heSide (kmswStageBallDartFlip P source r c
                    ⟨(edge, side), hd⟩)
            _ = !(e ⟨(edge, side), hd⟩).1.2 := by
              simp [heSide ⟨(edge, side), hd⟩]
  have hpresent : ∀ d, source.present d.1.1.val =
      target.present (e d).1.1.val := by
    intro d
    have hp := diskWindowClass_stage_present h hev hnd
    dsimp only at hp
    have hstatus := hp n htn (e d).1
      ((kmswStageBallDarts_mem_iff P target r c (e d).1).mp (e d).2).1
    calc
      source.present d.1.1.val = source.present (e d).1.1.val := by
        rw [heId d]
      _ = target.present (e d).1.1.val := hstatus
  have hmissing : ∀ d,
      kmswStageBallMapMissing P w n r c d ↔
        kmswStageBallMapMissing P w t r c (e d) := by
    intro d
    change (source.present d.1.1.val = false) ↔
      (target.present (e d).1.1.val = false)
    rw [hpresent d]
  exact ⟨e, heId, heSide, hflip, hrotation, hinvRotation, hpresent, hmissing⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The edge identity equivalence commutes with the restricted ball rotation. -/
theorem diskStageBallDartsEquiv_at_n_and_t_rot
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      ∀ d, e (kmswStageBallRot (fun _ _ => True) w n r
          (activeInitial w T) d) =
        kmswStageBallRot (fun _ _ => True) w (T + N) r
          (activeInitial w T) (e d) := by
  obtain ⟨e, heId, heSide, _, hrot, _, _, _⟩ :=
    diskStageBallMapIso_core h hev hcone hpos hnd
  exact ⟨e, heId, heSide, hrot⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The edge identity equivalence commutes with inverse ball rotation. -/
theorem diskStageBallDartsEquiv_at_n_and_t_rot_symm
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      ∀ d, e ((kmswStageBallRot (fun _ _ => True) w n r
          (activeInitial w T)).symm d) =
        (kmswStageBallRot (fun _ _ => True) w (T + N) r
          (activeInitial w T)).symm (e d) := by
  obtain ⟨e, heId, heSide, _, _, hinv, _, _⟩ :=
    diskStageBallMapIso_core h hev hcone hpos hnd
  exact ⟨e, heId, heSide, hinv⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The edge identity equivalence preserves stage edge presence. -/
theorem diskStageBallDartsEquiv_at_n_and_t_present
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      ∀ d, (kmswStage w n).present d.1.1.val =
        (kmswStage w (T + N)).present (e d).1.1.val := by
  obtain ⟨e, heId, heSide, _, _, _, hpresent, _⟩ :=
    diskStageBallMapIso_core h hev hcone hpos hnd
  exact ⟨e, heId, heSide, hpresent⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The edge identity equivalence preserves missing-edge status. -/
theorem diskStageBallDartsEquiv_at_n_and_t_missing
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      ∀ d, kmswStageBallMapMissing (fun _ _ => True) w n r
          (activeInitial w T) d ↔
        kmswStageBallMapMissing (fun _ _ => True) w (T + N) r
          (activeInitial w T) (e d) := by
  obtain ⟨e, heId, heSide, _, _, _, _, hmissing⟩ :=
    diskStageBallMapIso_core h hev hcone hpos hnd
  exact ⟨e, heId, heSide, hmissing⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The ball darts are related by an equivalence preserving edge IDs, sides, the
edge involution, rotation and inverse rotation, presence, and missing status.
This declaration asserts no outer-face correspondence. -/
theorem diskStageBallMapIso_at_n_and_t
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      (∀ d, e (kmswStageBallDartFlip (fun _ _ => True)
          (kmswStage w n) r (activeInitial w T) d) =
        kmswStageBallDartFlip (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T) (e d)) ∧
      (∀ d, e (kmswStageBallRot (fun _ _ => True) w n r
          (activeInitial w T) d) =
        kmswStageBallRot (fun _ _ => True) w (T + N) r
          (activeInitial w T) (e d)) ∧
      (∀ d, e ((kmswStageBallRot (fun _ _ => True) w n r
          (activeInitial w T)).symm d) =
        (kmswStageBallRot (fun _ _ => True) w (T + N) r
          (activeInitial w T)).symm (e d)) ∧
      (∀ d, (kmswStage w n).present d.1.1.val =
        (kmswStage w (T + N)).present (e d).1.1.val) ∧
      (∀ d, kmswStageBallMapMissing (fun _ _ => True) w n r
          (activeInitial w T) d ↔
        kmswStageBallMapMissing (fun _ _ => True) w (T + N) r
          (activeInitial w T) (e d)) := by
  exact diskStageBallMapIso_core h hev hcone hpos hnd


end DirectedDistances.PaperProofs.Section5
