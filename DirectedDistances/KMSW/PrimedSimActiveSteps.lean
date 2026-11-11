module

public import DirectedDistances.KMSW.PrimedSimActive

/-! # Ordinary allocating steps of the partial primed simulation

Partial helpers toward `lem-quad-kmsw`
These declarations do not count as the paper lemma or the P2 simulation. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/-- The ordinary-step bound places both global stages strictly before re-entry. -/
theorem PrimedSimActive.ordinary_bounds {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k) :
    walkNL w h k ≤ n ∧ n + 1 < walkNR w h (k + 1) := by
  have ha := sim.after_base
  have ht := sim.time_alignment
  change n = walkNL w h k +
    (m - primedIntervalBase (primedSimInput w) h k) - 1 at ht
  have hgap := (walkNR_succ_spec w h k).1
  change m < primedIntervalBase (primedSimInput w) h k +
    (walkNR w h (k + 1) - walkNL w h k) at hm
  omega

/-- Explicit up allocation maps fix every previously allocated ID. -/
theorem primedUp_maps_extend (sh gl : State) (eφ vφ : ℕ → ℕ) :
    (∀ e, e < sh.nextEdge → kmswShiftUpEdgeMap sh gl eφ e = eφ e) ∧
    (∀ v, v < sh.nextVertex → kmswShiftUpVertexMap sh gl vφ v = vφ v) := by
  constructor
  · intro e he
    simp only [kmswShiftUpEdgeMap, ite_eq_right (by omega : e ≠ sh.nextEdge),
      ite_eq_right (by omega : e ≠ sh.nextEdge + 1)]
  · intro v hv
    simp only [kmswShiftUpVertexMap, ite_eq_right (by omega : v ≠ sh.nextVertex)]

private theorem local_bounds (u : ℕ → Fin 3) (m : ℕ) :
    (kmswMissingRootStage u m).active < (kmswMissingRootStage u m).nextEdge ∧
    (∀ e ∈ primedGlobalFrontier (kmswMissingRootStage u m),
      e < (kmswMissingRootStage u m).nextEdge) ∧
    (∀ e, e < (kmswMissingRootStage u m).nextEdge →
      (kmswMissingRootStage u m).west e < (kmswMissingRootStage u m).nextVertex ∧
      (kmswMissingRootStage u m).east e < (kmswMissingRootStage u m).nextVertex) := by
  obtain ⟨hv, he, hw, ht, _, _, ha, hul, hur, hll, hlr⟩ :=
    kmswMissingRootStage_agree u m
  have hb := kmswStage_boundary_ids_lt_nextEdge u m
  refine ⟨by simpa only [he, ha] using hb.1, ?_, ?_⟩
  · intro e hem
    apply (he ▸ hb.2 e)
    simpa only [primedGlobalFrontier, hul, hur, hll, hlr, List.mem_append, or_assoc] using hem
  · intro e hem
    rw [hw, ht, hv]
    exact kmswStage_endpoints_lt_nextVertex u m e (he ▸ hem)

/-- Allocated IDs retain their bounds and injectivity under the explicit up
allocation maps. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.up_allocation {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w n
    let eψ := kmswShiftUpEdgeMap sh gl eφ
    let vψ := kmswShiftUpVertexMap sh gl vφ
    (∀ e, e < sh.nextEdge + 2 → eψ e < gl.nextEdge + 2) ∧
    (∀ e f, e < sh.nextEdge + 2 → f < sh.nextEdge + 2 → eψ e = eψ f → e = f) ∧
    (∀ v, v < sh.nextVertex + 1 → vψ v < gl.nextVertex + 1) ∧
    (∀ v z, v < sh.nextVertex + 1 → z < sh.nextVertex + 1 → vψ v = vψ z → v = z) := by
  dsimp only
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftUpEdgeMap sh gl eφ
  let vψ := kmswShiftUpVertexMap sh gl vφ
  change (∀ e, e < sh.nextEdge + 2 → eψ e < gl.nextEdge + 2) ∧
    (∀ e f, e < sh.nextEdge + 2 → f < sh.nextEdge + 2 → eψ e = eψ f → e = f) ∧
    (∀ v, v < sh.nextVertex + 1 → vψ v < gl.nextVertex + 1) ∧
    (∀ v z, v < sh.nextVertex + 1 → z < sh.nextVertex + 1 → vψ v = vψ z → v = z)
  dsimp only [eψ, vψ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      omega
    rcases heOld with heOld | he0 | he1
    · have hbound : eφ e < gl.nextEdge := sim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      have hpost : eφ e < gl.nextEdge + 2 := by omega
      simpa [eψ, kmswShiftUpEdgeMap, hne0, hne1] using hpost
    · subst e
      simp [kmswShiftUpEdgeMap]
    · subst e
      simp [kmswShiftUpEdgeMap]
  · intro e f he hf hef
    have hclass (x : ℕ) (hx : x < sh.nextEdge + 2) :
        x < sh.nextEdge ∨ x = sh.nextEdge ∨ x = sh.nextEdge + 1 := by omega
    rcases hclass e he with heOld | he0 | he1 <;>
      rcases hclass f hf with hfOld | hf0 | hf1
    · have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      have hnf0 : f ≠ sh.nextEdge := by omega
      have hnf1 : f ≠ sh.nextEdge + 1 := by omega
      have heq : eφ e = eφ f := by
        simpa [eψ, kmswShiftUpEdgeMap, hne0, hne1, hnf0, hnf1] using hef
      exact sim.edge_injective e f heOld hfOld heq
    · subst f
      have hbound : eφ e < gl.nextEdge := sim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst f
      have hbound : eφ e < gl.nextEdge := sim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e
      have hbound : eφ f < gl.nextEdge := sim.edge_bound f hfOld
      have hne0 : f ≠ sh.nextEdge := by omega
      have hne1 : f ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e; subst f; rfl
    · subst e; subst f
      simp [kmswShiftUpEdgeMap] at hef
    · subst e
      have hbound : eφ f < gl.nextEdge := sim.edge_bound f hfOld
      have hne0 : f ≠ sh.nextEdge := by omega
      have hne1 : f ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e; subst f
      simp [kmswShiftUpEdgeMap] at hef
    · subst e; subst f; rfl
  · intro v hv
    have hvOld : v < sh.nextVertex ∨ v = sh.nextVertex := by
      omega
    rcases hvOld with hvOld | hvNew
    · have hbound : vφ v < gl.nextVertex := sim.vertex_bound v hvOld
      have hne : v ≠ sh.nextVertex := by omega
      simpa [kmswStepOfStep, State.addEdge, vψ,
        kmswShiftUpVertexMap, hne] using Nat.lt_succ_of_lt hbound
    · subst v
      simp [kmswShiftUpVertexMap]
  · intro v z hv hz hvz
    have hclass (x : ℕ) (hx : x < sh.nextVertex + 1) :
        x < sh.nextVertex ∨ x = sh.nextVertex := by omega
    rcases hclass v hv with hvOld | hvNew <;>
      rcases hclass z hz with hzOld | hzNew
    · have hneV : v ≠ sh.nextVertex := by omega
      have hneZ : z ≠ sh.nextVertex := by omega
      have heq : vφ v = vφ z := by
        simpa [vψ, kmswShiftUpVertexMap, hneV, hneZ] using hvz
      exact sim.vertex_injective v z hvOld hzOld heq
    · subst z
      have hbound : vφ v < gl.nextVertex := sim.vertex_bound v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      simp [kmswShiftUpVertexMap, hneV] at hvz
      omega
    · subst v
      have hbound : vφ z < gl.nextVertex := sim.vertex_bound z hzOld
      have hneZ : z ≠ sh.nextVertex := by omega
      simp [kmswShiftUpVertexMap, hneZ] at hvz
      omega
    · subst v; subst z; rfl

private theorem active_present {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    (kmswMissingRootStage u m).present (kmswMissingRootStage u m).active = true := by
  have hne : (kmswMissingRootStage u m).active ≠ 0 := by
    intro hz
    have ha := sim.active_alignment
    rw [hz] at ha
    have hp := kmswStage_active_present w n
    change (kmswStage w n).present (kmswStage w n).active = true at hp
    rw [← ha] at hp
    rw [sim.missing_root.2.1] at hp
    cases hp
  obtain ⟨_, _, _, _, hp, _, ha, _⟩ := kmswMissingRootStage_agree u m
  rw [hp _ hne, ha]
  exact kmswStage_active_present u m

/-- Up preserves both incidence clauses, including unordered incidence of the
C18 missing root. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.up_incidence {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hu : u m = 1) (hw : w n = 1) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    let vψ := kmswShiftUpVertexMap (kmswMissingRootStage u m) (kmswStage w n) vφ
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = true →
      (kmswStage w (n + 1)).west (eψ e) =
        vψ ((kmswMissingRootStage u (m + 1)).west e) ∧
      (kmswStage w (n + 1)).east (eψ e) =
        vψ ((kmswMissingRootStage u (m + 1)).east e)) ∧
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = false →
      ({(kmswStage w (n + 1)).west (eψ e),
        (kmswStage w (n + 1)).east (eψ e)} : Multiset ℕ) =
        {vψ ((kmswMissingRootStage u (m + 1)).west e),
          vψ ((kmswMissingRootStage u (m + 1)).east e)}) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .up := by
    simp only [kmswStage, hw]; rfl
  obtain ⟨ha, _, hend⟩ := local_bounds u m
  have hi := sim.present_incidence sh.active ha (active_present sim)
  rw [sim.active_alignment] at hi
  have hact := hend sh.active ha
  dsimp only
  constructor
  · intro e he hp
    rw [hl] at he hp ⊢
    rw [hg]
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      change e < sh.nextEdge + 2 at he
      omega
    rcases hc with he | rfl | rfl
    · have hb : eφ e < gl.nextEdge := sim.edge_bound e he
      have hv := hend e he
      have hpold : sh.present e = true := by
        simpa [sh, gl, kmswStepOfStep, State.addEdge, show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega] using hp
      have hh := sim.present_incidence e he hpold
      simpa [sh, gl, kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap,
        kmswShiftUpVertexMap, show e ≠ sh.nextEdge from by omega,
        show e ≠ sh.nextEdge + 1 from by omega,
        show eφ e ≠ gl.nextEdge from by omega,
        show eφ e ≠ gl.nextEdge + 1 from by omega,
        ne_of_lt hv.1, ne_of_lt hv.2] using hh
    · simpa [sh, gl, kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap,
        kmswShiftUpVertexMap, ne_of_lt hact.1] using And.intro hi.1
          (rfl : gl.nextEdge = gl.nextEdge)
    · simp [sh, kmswStepOfStep, State.addEdge] at hp
  · intro e he hp
    rw [hl] at he hp ⊢
    rw [hg]
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      change e < sh.nextEdge + 2 at he
      omega
    rcases hc with he | rfl | rfl
    · have hb : eφ e < gl.nextEdge := sim.edge_bound e he
      have hv := hend e he
      have hpold : sh.present e = false := by
        simpa [sh, gl, kmswStepOfStep, State.addEdge, show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega] using hp
      have hh := sim.missing_incidence e he hpold
      simpa [sh, gl, kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap,
        kmswShiftUpVertexMap, show e ≠ sh.nextEdge from by omega,
        show e ≠ sh.nextEdge + 1 from by omega,
        show eφ e ≠ gl.nextEdge from by omega,
        show eφ e ≠ gl.nextEdge + 1 from by omega,
        ne_of_lt hv.1, ne_of_lt hv.2] using hh
    · simp [sh, kmswStepOfStep, State.addEdge] at hp
    · simp [sh, gl, kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap,
        kmswShiftUpVertexMap, ne_of_lt hact.2, hi.2]

/-- Up preserves present-edge exclusion from the growing reachable set and
keeps the C18 root missing on LL. The reachable set is constant on this
ordinary L-phase step. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.up_complement_root {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 1) (hw : w n = 1) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = true →
      (kmswStage w (n + 1)).present (eψ e) = true ∧
        eψ e ∉ stageReachablePresentEdges w (n + 1)) ∧
    ((kmswMissingRootStage u (m + 1)).present 0 = false ∧
      (kmswStage w (n + 1)).present (eψ 0) = false ∧
      eψ 0 ∈ (kmswStage w (n + 1)).LL) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .up := by
    simp only [kmswStage, hw]; rfl
  have hbounds := sim.ordinary_bounds hm
  have hreach := lPhase_reachablePresentEdges_succ_eq w h k n hbounds.1 hbounds.2
  have hnot : gl.nextEdge ∉ stageReachablePresentEdges w (n + 1) := by
    have hun := lPhase_activeWest_unreachable w h k (n + 1) (by omega) hbounds.2
    have hactive : act w (n + 1) = gl.nextEdge := by
      simp only [act, hg, kmswStepOfStep]
    rw [hactive] at hun
    intro he
    exact hun he.2.2.1
  dsimp only
  constructor
  · intro e he hp
    rw [hl] at he hp
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      change e < sh.nextEdge + 2 at he
      omega
    rcases hc with he | rfl | rfl
    · have hb : eφ e < gl.nextEdge := sim.edge_bound e he
      have hpold : sh.present e = true := by
        simpa [kmswStepOfStep, State.addEdge, show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega] using hp
      have hh := sim.present_complement e he hpold
      constructor
      · simpa [sh, gl, hg, kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap,
          show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega,
          show eφ e ≠ gl.nextEdge from by omega,
          show eφ e ≠ gl.nextEdge + 1 from by omega] using hh.1
      · simpa [sh, gl, kmswShiftUpEdgeMap,
          show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega, hreach] using hh.2
    · constructor
      · simp [sh, gl, hg, kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap]
      · simpa [sh, gl, kmswShiftUpEdgeMap] using hnot
    · simp [kmswStepOfStep, State.addEdge] at hp
  · have ha : 0 < sh.nextEdge := by have hh := (local_bounds u m).1; change sh.active < sh.nextEdge at hh; omega
    have hb : eφ 0 < gl.nextEdge := sim.edge_bound 0 ha
    refine ⟨kmswMissingRootStage_present_zero u (m + 1), ?_, ?_⟩
    · simpa [sh, gl, hg, kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap,
        show 0 ≠ sh.nextEdge from by omega,
        show 0 ≠ sh.nextEdge + 1 from by omega,
        show eφ 0 ≠ gl.nextEdge from by omega,
        show eφ 0 ≠ gl.nextEdge + 1 from by omega] using sim.missing_root.2.1
    · simpa [sh, gl, hg, kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap,
        show 0 ≠ sh.nextEdge from by omega,
        show 0 ≠ sh.nextEdge + 1 from by omega] using sim.missing_root.2.2

/-- Up aligns the new active edge and the entire UL stack. Partial helper, -/
theorem PrimedSimActive.up_active_UL {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hu : u m = 1) (hw : w n = 1) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    eψ (kmswMissingRootStage u (m + 1)).active = (kmswStage w (n + 1)).active ∧
    (kmswMissingRootStage u (m + 1)).UL.map eψ = (kmswStage w (n + 1)).UL := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .up := by
    simp only [kmswStage, hw]; rfl
  have hmap : sh.UL.map (kmswShiftUpEdgeMap sh gl eφ) = sh.UL.map eφ := by
    apply List.map_congr_left
    intro e he
    apply (primedUp_maps_extend sh gl eφ vφ).1
    apply (local_bounds u m).2.1
    simp only [primedGlobalFrontier, List.mem_append]
    exact Or.inl he
  dsimp only
  rw [hl, hg]
  constructor
  · simp [sh, gl, kmswStepOfStep, kmswShiftUpEdgeMap]
  · have hh := congrArg List.dropLast hmap
    rw [← List.map_dropLast, ← List.map_dropLast] at hh
    have hul := congrArg List.dropLast sim.UL_alignment
    rw [← List.map_dropLast] at hul
    simpa [sh, gl, kmswStepOfStep, State.addEdge, List.map_append,
      kmswShiftUpEdgeMap] using congrArg (fun es => es ++ [gl.nextEdge]) (hh.trans hul)

private theorem stage_triangle_bounds (u : ℕ → Fin 3) (m : ℕ) :
    ∀ a b c, (a, b, c) ∈ (kmswStage u m).triangles →
      a < (kmswStage u m).nextEdge ∧ b < (kmswStage u m).nextEdge ∧
      c < (kmswStage u m).nextEdge := by
  induction m with
  | zero => simp [kmswStage, kmswInit]
  | succ m ih =>
    intro a b c ht
    have ha := (kmswStage_boundary_ids_lt_nextEdge u m).1
    have hb := (kmswStage_boundary_ids_lt_nextEdge u m).2
    generalize hc : u m = d at *
    simp only [kmswStage, hc] at ht ⊢
    fin_cases d
    · change (a, b, c) ∈ (kmswStepOfStep (kmswStage u m) .left).triangles at ht
      change a < (kmswStepOfStep (kmswStage u m) .left).nextEdge ∧ b < (kmswStepOfStep (kmswStage u m) .left).nextEdge ∧ c < (kmswStepOfStep (kmswStage u m) .left).nextEdge
      cases hp : (kmswStage u m).UL.dropLast.reverse with
      | nil =>
        simp only [kmswStepOfStep, hp, State.addEdge, List.mem_append,
          List.mem_singleton] at ht ⊢
        rcases ht with ht | ht
        · obtain ⟨h1, h2, h3⟩ := ih a b c ht
          omega
        · cases ht
          omega
      | cons e es =>
        have he : e < (kmswStage u m).nextEdge := by
          apply hb
          have hm : e ∈ (kmswStage u m).UL.dropLast.reverse := by rw [hp]; simp
          have hm' := List.mem_of_mem_dropLast (List.mem_reverse.mp hm)
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inl hm'))
        simp only [kmswStepOfStep, hp, State.addEdge, List.mem_append,
          List.mem_singleton] at ht ⊢
        rcases ht with ht | ht
        · obtain ⟨h1, h2, h3⟩ := ih a b c ht
          omega
        · cases ht
          omega
    · change (a, b, c) ∈ (kmswStepOfStep (kmswStage u m) .up).triangles at ht
      change a < (kmswStepOfStep (kmswStage u m) .up).nextEdge ∧ b < (kmswStepOfStep (kmswStage u m) .up).nextEdge ∧ c < (kmswStepOfStep (kmswStage u m) .up).nextEdge
      simp only [kmswStepOfStep, State.addEdge, List.mem_append, List.mem_singleton] at ht ⊢
      rcases ht with ht | ht
      · obtain ⟨h1, h2, h3⟩ := ih a b c ht
        omega
      · cases ht
        omega
    · change (a, b, c) ∈ (kmswStepOfStep (kmswStage u m) .down).triangles at ht
      change a < (kmswStepOfStep (kmswStage u m) .down).nextEdge ∧ b < (kmswStepOfStep (kmswStage u m) .down).nextEdge ∧ c < (kmswStepOfStep (kmswStage u m) .down).nextEdge
      cases hp : (kmswStage u m).UR with
      | nil =>
        simp only [kmswStepOfStep, hp, State.addEdge] at ht ⊢
        obtain ⟨h1, h2, h3⟩ := ih a b c ht
        omega
      | cons e es =>
        simp only [kmswStepOfStep, hp] at ht ⊢
        exact ih a b c ht

/-- Up preserves every geometric triangle incidence. Partial helper, not -/
theorem PrimedSimActive.up_triangles {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hu : u m = 1) (hw : w n = 1) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    ∀ a b c, (a, b, c) ∈ (kmswMissingRootStage u (m + 1)).triangles →
      ∃ x y z, (x, y, z) ∈ (kmswStage w (n + 1)).triangles ∧
        ({eψ a, eψ b, eψ c} : Multiset ℕ) = {x, y, z} := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .up := by
    simp only [kmswStage, hw]; rfl
  dsimp only
  intro a b c ht
  rw [hl] at ht
  simp only [kmswStepOfStep, List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | ht
  · obtain ⟨x, y, z, hxyz, hi⟩ := sim.triangle_incidence a b c ht
    obtain ⟨_, he, _, _, _, htri, _⟩ := kmswMissingRootStage_agree u m
    have ht' : (a, b, c) ∈ (kmswStage u m).triangles := htri ▸ ht
    obtain ⟨ha, hb, hc⟩ := stage_triangle_bounds u m a b c ht'
    have hext := (primedUp_maps_extend sh gl eφ vφ).1
    refine ⟨x, y, z, ?_, ?_⟩
    · rw [hg]
      exact List.mem_append_left _ hxyz
    · change ({kmswShiftUpEdgeMap sh gl eφ a, kmswShiftUpEdgeMap sh gl eφ b,
          kmswShiftUpEdgeMap sh gl eφ c} : Multiset ℕ) = {x, y, z}
      simpa only [hext a (he.symm ▸ ha), hext b (he.symm ▸ hb), hext c (he.symm ▸ hc)] using hi
  · cases ht
    refine ⟨gl.active, gl.nextEdge, gl.nextEdge + 1, ?_, ?_⟩
    · rw [hg]
      simp [kmswStepOfStep]
    · change ({kmswShiftUpEdgeMap sh gl eφ sh.active, kmswShiftUpEdgeMap sh gl eφ sh.nextEdge,
          kmswShiftUpEdgeMap sh gl eφ (sh.nextEdge + 1)} : Multiset ℕ) =
          {gl.active, gl.nextEdge, gl.nextEdge + 1}
      have ha := (local_bounds u m).1
      have hext := (primedUp_maps_extend sh gl eφ vφ).1 sh.active ha
      simp only [hext]
      simp [sh, gl, kmswShiftUpEdgeMap, sim.active_alignment]

/-- A sufficient local boundary strengthening for ordinary allocating steps:
no earlier fresh down step has extended the primed LR beyond its missing root.
Partial induction data, not `lem-quad-kmsw` -/
structure PrimedSimActiveRootLR (u w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k m n : ℕ) (eφ vφ : ℕ → ℕ) : Prop
    extends PrimedSimActive u w h k m n eφ vφ where
  LR_root : (kmswMissingRootStage u m).LR = [0]

/-- Forget the additional local LR condition. Partial helper, not -/
theorem PrimedSimActiveRootLR.forget {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ) :
    PrimedSimActive u w h k m n eφ vφ := sim.toPrimedSimActive

/-- The first replacement triangle satisfies the local LR strengthening. -/
theorem primedFirstStep_simActiveRootLR (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu : u 0 = 1) :
    PrimedSimActiveRootLR u w h 0 1 (walkNL w h 0)
      (primedFirstStepEdgeMap w (walkNL w h 0))
      (primedFirstStepVertexMap w (walkNL w h 0)) where
  toPrimedSimActive := primedFirstStep_simActive u w h hu
  LR_root := by
    simp [kmswMissingRootStage, hu, kmswStep, kmswCodeStep, kmswStepOfStep,
      State.addEdge, kmswMissingRootInit, kmswInit]

/-- Up prepends the corresponding newly allocated missing side to the
oriented common UR prefix. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.up_UR {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hu : u m = 1) (hw : w n = 1) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    let vψ := kmswShiftUpVertexMap (kmswMissingRootStage u m) (kmswStage w n) vφ
    ∃ xs ys zs : List ℕ,
      (kmswMissingRootStage u (m + 1)).UR = xs ++ ys ∧
      (kmswStage w (n + 1)).UR = xs.map eψ ++ zs ∧
      (xs.length : ℤ) = R w (n + 1) - R w (walkNL w h k) ∧
      ∀ e ∈ xs,
        (kmswStage w (n + 1)).west (eψ e) =
          vψ ((kmswMissingRootStage u (m + 1)).west e) ∧
        (kmswStage w (n + 1)).east (eψ e) =
          vψ ((kmswMissingRootStage u (m + 1)).east e) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .up := by
    simp only [kmswStage, hw]; rfl
  obtain ⟨xs, ys, zs, hxs, hgs, hlen, hi⟩ := sim.UR_alignment
  have hb (e : ℕ) (he : e ∈ xs) : e < sh.nextEdge := by
    apply (local_bounds u m).2.1
    simp only [primedGlobalFrontier, List.mem_append]
    exact Or.inr (Or.inl (hxs ▸ List.mem_append_left _ he))
  have hmap : xs.map (kmswShiftUpEdgeMap sh gl eφ) = xs.map eφ := by
    apply List.map_congr_left
    intro e he
    exact (primedUp_maps_extend sh gl eφ vφ).1 e (hb e he)
  dsimp only
  refine ⟨(sh.nextEdge + 1) :: xs, ys, zs, ?_, ?_, ?_, ?_⟩
  · simpa only [hl, kmswStepOfStep, List.cons_append] using congrArg (List.cons (sh.nextEdge + 1)) hxs
  · simpa [sh, gl, hg, kmswStepOfStep, List.map_cons, hmap,
      kmswShiftUpEdgeMap] using congrArg (List.cons (gl.nextEdge + 1)) hgs
  · have hr : R w (n + 1) = R w n + 1 := by
      simp [R, Finset.sum_range_succ, hw, lazyTwoDimensionalStep]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    omega
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · have ha := (local_bounds u m).1
      have hv := (local_bounds u m).2.2 sh.active ha
      have hh := sim.present_incidence sh.active ha (active_present sim)
      rw [sim.active_alignment] at hh
      simp [sh, gl, hl, hg, kmswStepOfStep, State.addEdge,
        kmswShiftUpEdgeMap, kmswShiftUpVertexMap, ne_of_lt hv.2, hh.2]
    · have heold := hb e he
      have hgeb : eφ e < gl.nextEdge := sim.edge_bound e heold
      have hv := (local_bounds u m).2.2 e heold
      simpa [sh, gl, hl, hg, kmswStepOfStep, State.addEdge,
        kmswShiftUpEdgeMap, kmswShiftUpVertexMap,
        show e ≠ sh.nextEdge from by omega,
        show e ≠ sh.nextEdge + 1 from by omega,
        show eφ e ≠ gl.nextEdge from by omega,
        show eφ e ≠ gl.nextEdge + 1 from by omega,
        ne_of_lt hv.1, ne_of_lt hv.2] using hi e he

private theorem local_missing_ne_active (u : ℕ → Fin 3) (m e : ℕ)
    (he : e ∈ (kmswMissingRootStage u m).UR ∨ e ∈ (kmswMissingRootStage u m).LL) :
    e ≠ (kmswMissingRootStage u m).active := by
  intro heq
  rw [heq] at he
  obtain ⟨_, _, _, _, _, _, ha, _, hur, hll, _⟩ := kmswMissingRootStage_agree u m
  rw [ha, hur, hll] at he
  have hb := (kmswStage_boundary_ids_lt_nextEdge u m).1
  have hf := ((kmswStage_status u m).1 _ hb).mpr he
  have ht := kmswStage_active_present u m
  change (kmswStage u m).present (kmswStage u m).active = true at ht
  rw [hf] at ht
  cases ht

/-- With only the missing root on local LR, every surviving local boundary
image remains on the global frontier or the cut after up. Partial helper, -/
theorem PrimedSimActiveRootLR.up_boundary {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hu : u m = 1) (hw : w n = 1) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    ∀ e, e ∈ primedGlobalFrontier (kmswMissingRootStage u (m + 1)) →
      eψ e ∈ primedGlobalFrontier (kmswStage w (n + 1)) ∨ eψ e ∈ cutAtExit w h k := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftUpEdgeMap sh gl eφ
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .up := by
    simp only [kmswStage, hw]; rfl
  have hold (e : ℕ) (he : e ∈ sh.UR ∨ e ∈ sh.LL) :
      eψ e ∈ primedGlobalFrontier (kmswStage w (n + 1)) ∨ eψ e ∈ cutAtExit w h k := by
    have hf : e ∈ primedGlobalFrontier sh := by
      simp only [primedGlobalFrontier, List.mem_append]
      exact Or.inr (he.elim (fun hh => Or.inl hh) (fun hh => Or.inr (Or.inl hh)))
    have hb := (local_bounds u m).2.1 e hf
    have hext : eψ e = eφ e := (primedUp_maps_extend sh gl eφ vφ).1 e hb
    rw [hext]
    rcases sim.frontier_image e hf with hh | hh
    · by_cases hh' : eφ e ∈ primedGlobalFrontier (kmswStage w (n + 1))
      · exact Or.inl hh'
      · have ha : eφ e = gl.active := primedGlobalFrontier_up_loss w n (eφ e) hh (hg ▸ hh')
        have heq : e = sh.active := sim.edge_injective e sh.active hb (local_bounds u m).1
          (ha.trans sim.active_alignment.symm)
        exact (local_missing_ne_active u m e he heq).elim
    · exact Or.inr hh
  dsimp only
  intro e he
  simp only [primedGlobalFrontier, List.mem_append] at he
  rcases he with he | he | he | he
  · left
    have hul := (sim.forget.up_active_UL hu hw).2
    have hh : eψ e ∈ (kmswStage w (n + 1)).UL := by
      rw [← hul]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    simp only [primedGlobalFrontier, List.mem_append]
    exact Or.inl hh
  · simp only [hl, kmswStepOfStep, List.mem_cons] at he
    rcases he with rfl | he
    · left
      simp [sh, gl, hg, primedGlobalFrontier, kmswStepOfStep, State.addEdge,
        kmswShiftUpEdgeMap]
    · exact hold e (Or.inl he)
  · simp only [hl, kmswStepOfStep, State.addEdge] at he
    exact hold e (Or.inr he)
  · have he0 : e = 0 := by simpa only [hl, kmswStepOfStep, State.addEdge, sh, sim.LR_root,
        List.mem_singleton] using he
    subst e
    left
    have hb0 : 0 < sh.nextEdge := by have hh := (local_bounds u m).1; change sh.active < sh.nextEdge at hh; omega
    have hext := (primedUp_maps_extend sh gl eφ vφ).1 0 hb0
    change kmswShiftUpEdgeMap sh gl eφ 0 ∈ primedGlobalFrontier (kmswStage w (n + 1))
    rw [hext, hg]
    simp only [primedGlobalFrontier, kmswStepOfStep, State.addEdge, List.mem_append]
    exact Or.inr (Or.inr (Or.inl sim.missing_root.2.2))

/-- One ordinary up step preserves the strengthened invariant with explicit
fresh-ID images `E ↦ global E`, `E+1 ↦ global E+1`, `V ↦ global V`. -/
theorem PrimedSimActiveRootLR.step_up {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 1) (hw : w n = 1) :
    PrimedSimActiveRootLR u w h k (m + 1) (n + 1)
      (kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ)
      (kmswShiftUpVertexMap (kmswMissingRootStage u m) (kmswStage w n) vφ) := by
  have hl : kmswMissingRootStage u (m + 1) =
      kmswStepOfStep (kmswMissingRootStage u m) .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep (kmswStage w n) .up := by
    simp only [kmswStage, hw]; rfl
  have hb := sim.forget.up_allocation
  have hi := sim.forget.up_incidence hu hw
  have hc := sim.forget.up_complement_root hm hu hw
  have ha := sim.forget.up_active_UL hu hw
  refine {
    edge_bound := ?_, edge_injective := ?_, vertex_bound := ?_, vertex_injective := ?_
    present_incidence := hi.1, missing_incidence := hi.2
    present_complement := hc.1, missing_root := hc.2
    triangle_incidence := sim.forget.up_triangles hu hw
    boundary_image := ?_
    after_base := ?_, time_alignment := ?_
    active_alignment := ha.1, UL_alignment := ha.2
    UR_alignment := sim.forget.up_UR hu hw
    LR_root := ?_ }
  · simpa only [hl, hg, kmswStepOfStep, State.addEdge, Nat.add_assoc] using hb.1
  · simpa only [hl, kmswStepOfStep, State.addEdge, Nat.add_assoc] using hb.2.1
  · simpa only [hl, hg, kmswStepOfStep, State.addEdge] using hb.2.2.1
  · simpa only [hl, kmswStepOfStep, State.addEdge] using hb.2.2.2
  · intro e he
    apply sim.up_boundary hu hw e
    simpa only [primedGlobalFrontier, List.mem_append, or_assoc] using he
  · have hh := sim.after_base
    omega
  · have ht := sim.time_alignment
    have hh := sim.after_base
    omega
  · simpa only [hl, kmswStepOfStep, State.addEdge] using sim.LR_root

/-- Extension-form up transition for the strengthened local LR invariant. -/
theorem PrimedSimActiveRootLR.step_up_extends {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 1) (hw : w n = 1) :
    ∃ eφ' vφ',
      (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
      (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
      PrimedSimActiveRootLR u w h k (m + 1) (n + 1) eφ' vφ' := by
  exact ⟨_, _, (primedUp_maps_extend _ _ eφ vφ).1,
    (primedUp_maps_extend _ _ eφ vφ).2, sim.step_up hm hu hw⟩

/-- An ordinary down activation preserves the local LR strengthening, with
unchanged maps. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActiveRootLR.step_down {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 2) (hw : w n = 2) :
    PrimedSimActiveRootLR u w h k (m + 1) (n + 1) eφ vφ := by
  obtain ⟨a, as, bs, hlocal, _, _⟩ := sim.forget.down_heads hm hw
  refine { toPrimedSimActive := sim.forget.step_down hm hu hw, LR_root := ?_ }
  simpa only [kmswMissingRootStage, hu, kmswStep, kmswCodeStep,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    ↓reduceIte, kmswStepOfStep, hlocal] using sim.LR_root

/-- Exact UL alignment synchronizes the left-step allocation branch. -/
theorem PrimedSimActive.left_predecessors {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    (kmswMissingRootStage u m).UL.dropLast.reverse.map eφ =
      (kmswStage w n).UL.dropLast.reverse := by
  have hh := congrArg (fun es => es.dropLast.reverse) sim.UL_alignment
  rw [← List.map_dropLast, ← List.map_reverse] at hh
  exact hh

/-- Empty-predecessor left-step branch. Partial helper, not -/
theorem PrimedSimActive.left_empty_incidence {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hu : u m = 0) (hw : w n = 0)
    (hUL : (kmswMissingRootStage u m).UL.dropLast.reverse = []) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    let vψ := kmswShiftUpVertexMap (kmswMissingRootStage u m) (kmswStage w n) vφ
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = true →
      (kmswStage w (n + 1)).west (eψ e) =
        vψ ((kmswMissingRootStage u (m + 1)).west e) ∧
      (kmswStage w (n + 1)).east (eψ e) =
        vψ ((kmswMissingRootStage u (m + 1)).east e)) ∧
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = false →
      ({(kmswStage w (n + 1)).west (eψ e),
        (kmswStage w (n + 1)).east (eψ e)} : Multiset ℕ) =
        {vψ ((kmswMissingRootStage u (m + 1)).west e),
          vψ ((kmswMissingRootStage u (m + 1)).east e)}) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .left := by
    simp only [kmswStage, hw]; rfl
  have hsUL : sh.UL.dropLast.reverse = [] := hUL
  have hgUL : gl.UL.dropLast.reverse = [] := by
    have hh := sim.left_predecessors
    rw [hUL] at hh
    exact hh.symm
  have hgULactual : (kmswStage w n).UL.dropLast.reverse = [] := hgUL
  obtain ⟨ha, _, hend⟩ := local_bounds u m
  have hi := sim.present_incidence sh.active ha (active_present sim)
  rw [sim.active_alignment] at hi
  have hact := hend sh.active ha
  dsimp only
  constructor
  · intro e he hp
    rw [hl] at he hp ⊢
    rw [hg]
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp only [kmswStepOfStep, hsUL, State.addEdge] at he
      omega
    rcases hc with he | rfl | rfl
    · have hb : eφ e < gl.nextEdge := sim.edge_bound e he
      have hv := hend e he
      have hpold : sh.present e = true := by
        simpa [sh, gl, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega] using hp
      have hh := sim.present_incidence e he hpold
      simpa [sh, gl, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, kmswShiftUpEdgeMap,
        kmswShiftUpVertexMap, show e ≠ sh.nextEdge from by omega,
        show e ≠ sh.nextEdge + 1 from by omega,
        show eφ e ≠ gl.nextEdge from by omega,
        show eφ e ≠ gl.nextEdge + 1 from by omega,
        ne_of_lt hv.1, ne_of_lt hv.2] using hh
    · simpa [sh, gl, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, kmswShiftUpEdgeMap,
        kmswShiftUpVertexMap, ne_of_lt hact.2] using And.intro
          (rfl : gl.nextVertex = gl.nextVertex) hi.2
    · simp [sh, kmswStepOfStep, hUL, State.addEdge] at hp
  · intro e he hp
    rw [hl] at he hp ⊢
    rw [hg]
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp only [kmswStepOfStep, hsUL, State.addEdge] at he
      omega
    rcases hc with he | rfl | rfl
    · have hb : eφ e < gl.nextEdge := sim.edge_bound e he
      have hv := hend e he
      have hpold : sh.present e = false := by
        simpa [sh, gl, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega] using hp
      have hh := sim.missing_incidence e he hpold
      simpa [sh, gl, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, kmswShiftUpEdgeMap,
        kmswShiftUpVertexMap, show e ≠ sh.nextEdge from by omega,
        show e ≠ sh.nextEdge + 1 from by omega,
        show eφ e ≠ gl.nextEdge from by omega,
        show eφ e ≠ gl.nextEdge + 1 from by omega,
        ne_of_lt hv.1, ne_of_lt hv.2] using hh
    · simp [sh, kmswStepOfStep, hUL, State.addEdge] at hp
    · simp [sh, gl, kmswStepOfStep, hUL, hgUL, State.addEdge, kmswShiftUpEdgeMap,
        kmswShiftUpVertexMap, ne_of_lt hact.1, hi.1]

/-- Empty-predecessor left-step branch. Partial helper, not -/
theorem PrimedSimActive.left_empty_complement_root {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 0) (hw : w n = 0)
    (hUL : (kmswMissingRootStage u m).UL.dropLast.reverse = []) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = true →
      (kmswStage w (n + 1)).present (eψ e) = true ∧
        eψ e ∉ stageReachablePresentEdges w (n + 1)) ∧
    ((kmswMissingRootStage u (m + 1)).present 0 = false ∧
      (kmswStage w (n + 1)).present (eψ 0) = false ∧
      eψ 0 ∈ (kmswStage w (n + 1)).LL) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .left := by
    simp only [kmswStage, hw]; rfl
  have hsUL : sh.UL.dropLast.reverse = [] := hUL
  have hgUL : gl.UL.dropLast.reverse = [] := by
    have hh := sim.left_predecessors
    rw [hUL] at hh
    exact hh.symm
  have hgULactual : (kmswStage w n).UL.dropLast.reverse = [] := hgUL
  have hbounds := sim.ordinary_bounds hm
  have hreach := lPhase_reachablePresentEdges_succ_eq w h k n hbounds.1 hbounds.2
  have hnot : gl.nextEdge ∉ stageReachablePresentEdges w (n + 1) := by
    have hun := lPhase_activeWest_unreachable w h k (n + 1) (by omega) hbounds.2
    have hactive : act w (n + 1) = gl.nextEdge := by
      simp only [act, hg, kmswStepOfStep, hgUL]
    rw [hactive] at hun
    intro he
    exact hun he.2.2.1
  dsimp only
  constructor
  · intro e he hp
    rw [hl] at he hp
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp only [kmswStepOfStep, hsUL, State.addEdge] at he
      omega
    rcases hc with he | rfl | rfl
    · have hb : eφ e < gl.nextEdge := sim.edge_bound e he
      have hpold : sh.present e = true := by
        simpa [kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega] using hp
      have hh := sim.present_complement e he hpold
      constructor
      · simpa [sh, gl, hg, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, kmswShiftUpEdgeMap,
          show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega,
          show eφ e ≠ gl.nextEdge from by omega,
          show eφ e ≠ gl.nextEdge + 1 from by omega] using hh.1
      · simpa [sh, gl, kmswShiftUpEdgeMap,
          show e ≠ sh.nextEdge from by omega,
          show e ≠ sh.nextEdge + 1 from by omega, hreach] using hh.2
    · constructor
      · simp [sh, gl, hg, kmswStepOfStep, hgUL, State.addEdge, kmswShiftUpEdgeMap]
      · simpa [sh, gl, kmswShiftUpEdgeMap] using hnot
    · simp [kmswStepOfStep, hsUL, State.addEdge] at hp
  · have ha : 0 < sh.nextEdge := by have hh := (local_bounds u m).1; change sh.active < sh.nextEdge at hh; omega
    have hb : eφ 0 < gl.nextEdge := sim.edge_bound 0 ha
    refine ⟨kmswMissingRootStage_present_zero u (m + 1), ?_, ?_⟩
    · simpa [sh, gl, hg, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, kmswShiftUpEdgeMap,
        show 0 ≠ sh.nextEdge from by omega,
        show 0 ≠ sh.nextEdge + 1 from by omega,
        show eφ 0 ≠ gl.nextEdge from by omega,
        show eφ 0 ≠ gl.nextEdge + 1 from by omega] using sim.missing_root.2.1
    · simpa [sh, gl, hg, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge, kmswShiftUpEdgeMap,
        show 0 ≠ sh.nextEdge from by omega,
        show 0 ≠ sh.nextEdge + 1 from by omega] using Or.inr sim.missing_root.2.2

/-- Empty-predecessor left-step branch. Partial helper, not -/
theorem PrimedSimActive.left_empty_triangles {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hu : u m = 0) (hw : w n = 0)
    (hUL : (kmswMissingRootStage u m).UL.dropLast.reverse = []) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    ∀ a b c, (a, b, c) ∈ (kmswMissingRootStage u (m + 1)).triangles →
      ∃ x y z, (x, y, z) ∈ (kmswStage w (n + 1)).triangles ∧
        ({eψ a, eψ b, eψ c} : Multiset ℕ) = {x, y, z} := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .left := by
    simp only [kmswStage, hw]; rfl
  have hsUL : sh.UL.dropLast.reverse = [] := hUL
  have hgUL : gl.UL.dropLast.reverse = [] := by
    have hh := sim.left_predecessors
    rw [hUL] at hh
    exact hh.symm
  have hgULactual : (kmswStage w n).UL.dropLast.reverse = [] := hgUL
  dsimp only
  intro a b c ht
  rw [hl] at ht
  simp only [kmswStepOfStep, hsUL, List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | ht
  · obtain ⟨x, y, z, hxyz, hi⟩ := sim.triangle_incidence a b c ht
    obtain ⟨_, he, _, _, _, htri, _⟩ := kmswMissingRootStage_agree u m
    have ht' : (a, b, c) ∈ (kmswStage u m).triangles := htri ▸ ht
    obtain ⟨ha, hb, hc⟩ := stage_triangle_bounds u m a b c ht'
    have hext := (primedUp_maps_extend sh gl eφ vφ).1
    refine ⟨x, y, z, ?_, ?_⟩
    · rw [hg]
      simp only [kmswStepOfStep, hgUL]
      exact List.mem_append_left _ hxyz
    · change ({kmswShiftUpEdgeMap sh gl eφ a, kmswShiftUpEdgeMap sh gl eφ b,
          kmswShiftUpEdgeMap sh gl eφ c} : Multiset ℕ) = {x, y, z}
      simpa only [hext a (he.symm ▸ ha), hext b (he.symm ▸ hb), hext c (he.symm ▸ hc)] using hi
  · cases ht
    refine ⟨gl.active, gl.nextEdge, gl.nextEdge + 1, ?_, ?_⟩
    · rw [hg]
      simp [kmswStepOfStep, hgUL]
    · change ({kmswShiftUpEdgeMap sh gl eφ sh.active, kmswShiftUpEdgeMap sh gl eφ sh.nextEdge,
          kmswShiftUpEdgeMap sh gl eφ (sh.nextEdge + 1)} : Multiset ℕ) =
          {gl.active, gl.nextEdge, gl.nextEdge + 1}
      have ha := (local_bounds u m).1
      have hext := (primedUp_maps_extend sh gl eφ vφ).1 sh.active ha
      simp only [hext]
      simp [sh, gl, kmswShiftUpEdgeMap, sim.active_alignment]


/-- Empty-predecessor left steps retain the oriented common UR prefix. -/
theorem PrimedSimActive.left_empty_UR {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hu : u m = 0) (hw : w n = 0)
    (hUL : (kmswMissingRootStage u m).UL.dropLast.reverse = []) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    let vψ := kmswShiftUpVertexMap (kmswMissingRootStage u m) (kmswStage w n) vφ
    ∃ xs ys zs : List ℕ,
      (kmswMissingRootStage u (m + 1)).UR = xs ++ ys ∧
      (kmswStage w (n + 1)).UR = xs.map eψ ++ zs ∧
      (xs.length : ℤ) = R w (n + 1) - R w (walkNL w h k) ∧
      ∀ e ∈ xs,
        (kmswStage w (n + 1)).west (eψ e) =
          vψ ((kmswMissingRootStage u (m + 1)).west e) ∧
        (kmswStage w (n + 1)).east (eψ e) =
          vψ ((kmswMissingRootStage u (m + 1)).east e) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .left := by
    simp only [kmswStage, hw]; rfl
  have hsUL : sh.UL.dropLast.reverse = [] := hUL
  have hgUL : gl.UL.dropLast.reverse = [] := by
    have hh := sim.left_predecessors
    rw [hUL] at hh
    exact hh.symm
  have hgULactual : (kmswStage w n).UL.dropLast.reverse = [] := hgUL
  obtain ⟨xs, ys, zs, hxs, hgs, hlen, hi⟩ := sim.UR_alignment
  have hb (e : ℕ) (he : e ∈ xs) : e < sh.nextEdge := by
    apply (local_bounds u m).2.1
    simp only [primedGlobalFrontier, List.mem_append]
    exact Or.inr (Or.inl (hxs ▸ List.mem_append_left _ he))
  have hmap : xs.map (kmswShiftUpEdgeMap sh gl eφ) = xs.map eφ := by
    apply List.map_congr_left
    intro e he
    exact (primedUp_maps_extend sh gl eφ vφ).1 e (hb e he)
  dsimp only
  refine ⟨xs, ys, zs, ?_, ?_, ?_, ?_⟩
  · simpa only [hl, kmswStepOfStep, hsUL, State.addEdge] using hxs
  · simp only [hg, kmswStepOfStep, hgUL, State.addEdge]
    change gl.UR = xs.map (kmswShiftUpEdgeMap sh gl eφ) ++ zs
    rw [hmap]
    exact hgs
  · have hr : R w (n + 1) = R w n := by
      simp [R, Finset.sum_range_succ, hw, lazyTwoDimensionalStep]
    rw [hr]
    exact hlen
  · intro e he
    have heold := hb e he
    have hgeb : eφ e < gl.nextEdge := sim.edge_bound e heold
    have hv := (local_bounds u m).2.2 e heold
    simpa [sh, gl, hl, hg, kmswStepOfStep, hUL, hsUL, hgUL, hgULactual, State.addEdge,
        kmswShiftUpEdgeMap, kmswShiftUpVertexMap,
        show e ≠ sh.nextEdge from by omega,
        show e ≠ sh.nextEdge + 1 from by omega,
        show eφ e ≠ gl.nextEdge from by omega,
        show eφ e ≠ gl.nextEdge + 1 from by omega,
        ne_of_lt hv.1, ne_of_lt hv.2] using hi e he


/-- Empty-predecessor left steps preserve surviving boundary images under
the local LR strengthening. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActiveRootLR.left_empty_boundary {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hu : u m = 0) (hw : w n = 0)
    (hUL : (kmswMissingRootStage u m).UL.dropLast.reverse = []) :
    let eψ := kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    ∀ e, e ∈ primedGlobalFrontier (kmswMissingRootStage u (m + 1)) →
      eψ e ∈ primedGlobalFrontier (kmswStage w (n + 1)) ∨ eψ e ∈ cutAtExit w h k := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftUpEdgeMap sh gl eφ
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .left := by
    simp only [kmswStage, hw]; rfl
  have hsUL : sh.UL.dropLast.reverse = [] := hUL
  have hgUL : gl.UL.dropLast.reverse = [] := by
    have hh := sim.forget.left_predecessors
    rw [hUL] at hh
    exact hh.symm
  have hgULactual : (kmswStage w n).UL.dropLast.reverse = [] := hgUL
  have hULone : gl.UL = [gl.active] := by
    obtain ⟨xs, hx⟩ := kmswStage_UL_last w n
    have hh := hgUL
    change (kmswStage w n).UL.dropLast.reverse = [] at hh
    simp only [hx, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at hh
    have hxnil : xs = [] := List.reverse_eq_nil_iff.mp hh
    simpa only [hxnil, List.nil_append] using hx
  have hold (e : ℕ) (he : e ∈ sh.UR ∨ e ∈ sh.LL) :
      eψ e ∈ primedGlobalFrontier (kmswStage w (n + 1)) ∨ eψ e ∈ cutAtExit w h k := by
    have hf : e ∈ primedGlobalFrontier sh := by
      simp only [primedGlobalFrontier, List.mem_append]
      exact Or.inr (he.elim (fun hh => Or.inl hh) (fun hh => Or.inr (Or.inl hh)))
    have hb := (local_bounds u m).2.1 e hf
    have hext : eψ e = eφ e := (primedUp_maps_extend sh gl eφ vφ).1 e hb
    rw [hext]
    rcases sim.frontier_image e hf with hh | hh
    · have hne : eφ e ≠ gl.active := by
        intro ha
        have heq : e = sh.active := sim.edge_injective e sh.active hb (local_bounds u m).1
          (ha.trans sim.active_alignment.symm)
        exact local_missing_ne_active u m e he heq
      have hh' : eφ e ∈ primedGlobalFrontier gl := hh
      simp only [primedGlobalFrontier, hULone, List.mem_append, List.mem_singleton] at hh'
      rcases hh' with ha | hur | hll | hlr
      · exact (hne ha).elim
      · left; simp [hg, primedGlobalFrontier, kmswStepOfStep, hgUL, State.addEdge, hur]
      · left; simp [hg, primedGlobalFrontier, kmswStepOfStep, hgUL, State.addEdge, hll]
      · left; simp [hg, primedGlobalFrontier, kmswStepOfStep, hgUL, State.addEdge, hlr]
    · exact Or.inr hh
  dsimp only
  intro e he
  simp only [primedGlobalFrontier, List.mem_append] at he
  rcases he with he | he | he | he
  · have heE : e = sh.nextEdge := by
      simpa only [hl, kmswStepOfStep, hsUL, List.mem_singleton] using he
    subst e
    left
    simp [sh, gl, hg, primedGlobalFrontier, kmswStepOfStep, hgUL,
      State.addEdge, kmswShiftUpEdgeMap]
  · have heold : e ∈ sh.UR := by
      simpa only [hl, kmswStepOfStep, hsUL, State.addEdge] using he
    exact hold e (Or.inl heold)
  · have hecases : e = sh.nextEdge + 1 ∨ e ∈ sh.LL := by
      simpa only [hl, kmswStepOfStep, hsUL, List.mem_cons] using he
    rcases hecases with rfl | heold
    · left
      simp [sh, gl, hg, primedGlobalFrontier, kmswStepOfStep, hgUL,
        State.addEdge, kmswShiftUpEdgeMap]
    · exact hold e (Or.inr heold)
  · have he0 : e = 0 := by simpa only [hl, kmswStepOfStep, hsUL, State.addEdge, sh, sim.LR_root,
        List.mem_singleton] using he
    subst e
    left
    have hb0 : 0 < sh.nextEdge := by have hh := (local_bounds u m).1; change sh.active < sh.nextEdge at hh; omega
    have hext := (primedUp_maps_extend sh gl eφ vφ).1 0 hb0
    change kmswShiftUpEdgeMap sh gl eφ 0 ∈ primedGlobalFrontier (kmswStage w (n + 1))
    rw [hext, hg]
    simp only [primedGlobalFrontier, kmswStepOfStep, hgUL, State.addEdge, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inr (Or.inl (Or.inr sim.missing_root.2.2)))


/-- Empty-predecessor ordinary left transition with the explicit two-edge,
one-vertex allocation maps. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActiveRootLR.step_left_empty {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 0) (hw : w n = 0)
    (hUL : (kmswMissingRootStage u m).UL.dropLast.reverse = []) :
    PrimedSimActiveRootLR u w h k (m + 1) (n + 1)
      (kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ)
      (kmswShiftUpVertexMap (kmswMissingRootStage u m) (kmswStage w n) vφ) := by
  have hl : kmswMissingRootStage u (m + 1) =
      kmswStepOfStep (kmswMissingRootStage u m) .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep (kmswStage w n) .left := by
    simp only [kmswStage, hw]; rfl
  have hb := sim.forget.up_allocation
  have hi := sim.forget.left_empty_incidence hu hw hUL
  have hc := sim.forget.left_empty_complement_root hm hu hw hUL
  have hgUL : (kmswStage w n).UL.dropLast.reverse = [] := by
    have hh := sim.forget.left_predecessors
    rw [hUL] at hh
    exact hh.symm
  refine {
    edge_bound := ?_, edge_injective := ?_, vertex_bound := ?_, vertex_injective := ?_
    present_incidence := hi.1, missing_incidence := hi.2
    present_complement := hc.1, missing_root := hc.2
    triangle_incidence := sim.forget.left_empty_triangles hu hw hUL
    boundary_image := ?_
    after_base := ?_, time_alignment := ?_
    active_alignment := ?_, UL_alignment := ?_
    UR_alignment := sim.forget.left_empty_UR hu hw hUL
    LR_root := ?_ }
  · simpa only [hl, hg, kmswStepOfStep, hUL, hgUL, State.addEdge, Nat.add_assoc] using hb.1
  · simpa only [hl, kmswStepOfStep, hUL, hgUL, State.addEdge, Nat.add_assoc] using hb.2.1
  · simpa only [hl, hg, kmswStepOfStep, hUL, hgUL, State.addEdge] using hb.2.2.1
  · simpa only [hl, kmswStepOfStep, hUL, hgUL, State.addEdge] using hb.2.2.2
  · intro e he
    apply sim.left_empty_boundary hu hw hUL e
    simpa only [primedGlobalFrontier, List.mem_append, or_assoc] using he
  · have hh := sim.after_base
    omega
  · have ht := sim.time_alignment
    have hh := sim.after_base
    omega
  · simp [hl, hg, kmswStepOfStep, hUL, hgUL, kmswShiftUpEdgeMap]
  · simp [hl, hg, kmswStepOfStep, hUL, hgUL, kmswShiftUpEdgeMap]
  · simpa only [hl, kmswStepOfStep, hUL, State.addEdge] using sim.LR_root


/-- Explicit edge allocation map for an ordinary left step. The empty
predecessor branch allocates two edges; the other branch allocates one. -/
@[expose] def primedOrdinaryLeftEdgeMap (sh gl : State) (eφ : ℕ → ℕ) : ℕ → ℕ :=
  if sh.UL.dropLast.reverse = [] then kmswShiftUpEdgeMap sh gl eφ
  else kmswShiftFreshEdgeMap sh gl eφ

/-- Explicit vertex allocation map for an ordinary left step; only the
empty-predecessor branch allocates a vertex. Partial helper, not -/
@[expose] def primedOrdinaryLeftVertexMap (sh gl : State) (vφ : ℕ → ℕ) : ℕ → ℕ :=
  if sh.UL.dropLast.reverse = [] then kmswShiftUpVertexMap sh gl vφ else vφ

/-- Both branches of the explicit left maps fix all old allocated IDs. -/
theorem primedLeft_maps_extend (sh gl : State) (eφ vφ : ℕ → ℕ) :
    (∀ e, e < sh.nextEdge → primedOrdinaryLeftEdgeMap sh gl eφ e = eφ e) ∧
    (∀ v, v < sh.nextVertex → primedOrdinaryLeftVertexMap sh gl vφ v = vφ v) := by
  by_cases hh : sh.UL.dropLast.reverse = []
  · simpa only [primedOrdinaryLeftEdgeMap, primedOrdinaryLeftVertexMap, ite_eq_left hh] using
      primedUp_maps_extend sh gl eφ vφ
  · constructor
    · intro e he
      simp only [primedOrdinaryLeftEdgeMap, ite_eq_right hh, kmswShiftFreshEdgeMap,
        ite_eq_right (ne_of_lt he)]
    · intro v _
      simp only [primedOrdinaryLeftVertexMap, ite_eq_right hh]

/-- A left step sends the fresh active edge to the fresh global active edge;
the empty branch also sends the fresh missing side and vertex to their global
counterparts. Partial helper, not `lem-quad-kmsw` -/
theorem primedLeft_maps_fresh (sh gl : State) (eφ vφ : ℕ → ℕ) :
    primedOrdinaryLeftEdgeMap sh gl eφ sh.nextEdge = gl.nextEdge ∧
    (sh.UL.dropLast.reverse = [] →
      primedOrdinaryLeftEdgeMap sh gl eφ (sh.nextEdge + 1) = gl.nextEdge + 1 ∧
      primedOrdinaryLeftVertexMap sh gl vφ sh.nextVertex = gl.nextVertex) := by
  constructor
  · by_cases hh : sh.UL.dropLast.reverse = [] <;>
      simp [primedOrdinaryLeftEdgeMap, hh, kmswShiftUpEdgeMap, kmswShiftFreshEdgeMap]
  · intro hh
    simp [primedOrdinaryLeftEdgeMap, primedOrdinaryLeftVertexMap, hh,
      kmswShiftUpEdgeMap, kmswShiftUpVertexMap]

/-- Every local UL edge is present under active simulation: the missing root
cannot occur there because its image is a globally missing LL edge. -/
theorem PrimedSimActive.UL_present {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) (e : ℕ)
    (he : e ∈ (kmswMissingRootStage u m).UL) :
    (kmswMissingRootStage u m).present e = true := by
  have he0 : e ≠ 0 := by
    intro hz
    subst e
    have hh : eφ 0 ∈ (kmswStage w n).UL := by
      rw [← sim.UL_alignment]
      exact List.mem_map.mpr ⟨0, he, rfl⟩
    have hp := (kmswStage_status w n).2.1 _ hh
    rw [sim.missing_root.2.1] at hp
    cases hp
  obtain ⟨_, _, _, _, hp, _, _, hul, _⟩ := kmswMissingRootStage_agree u m
  rw [hp e he0]
  exact (kmswStage_status u m).2.1 e (hul ▸ he)

/-- In the nonempty left branch, the consumed UL predecessor has an aligned
head and ordered endpoints. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.left_head_incidence {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n a : ℕ} {as : List ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hpred : (kmswMissingRootStage u m).UL.dropLast.reverse = a :: as) :
    (kmswStage w n).UL.dropLast.reverse = eφ a :: as.map eφ ∧
    (kmswStage w n).west (eφ a) = vφ ((kmswMissingRootStage u m).west a) ∧
    (kmswStage w n).east (eφ a) = vφ ((kmswMissingRootStage u m).east a) := by
  have hh := sim.left_predecessors
  rw [hpred, List.map_cons] at hh
  have hmem : a ∈ (kmswMissingRootStage u m).UL := by
    apply List.mem_of_mem_dropLast
    apply List.mem_reverse.mp
    rw [hpred]
    simp
  have hb := (local_bounds u m).2.1 a (by
    simp only [primedGlobalFrontier, List.mem_append]
    exact Or.inl hmem)
  exact ⟨hh.symm, sim.present_incidence a hb (sim.UL_present a hmem)⟩

/-- Extension-form empty-predecessor left transition, with both explicit
allocation maps fixing old IDs. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActiveRootLR.step_left_empty_extends {u w : ℕ → Fin 3}
    {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 0) (hw : w n = 0)
    (hUL : (kmswMissingRootStage u m).UL.dropLast.reverse = []) :
    ∃ eφ' vφ',
      (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
      (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
      PrimedSimActiveRootLR u w h k (m + 1) (n + 1) eφ' vφ' := by
  exact ⟨_, _, (primedUp_maps_extend _ _ eφ vφ).1,
    (primedUp_maps_extend _ _ eφ vφ).2, sim.step_left_empty hm hu hw hUL⟩

/- ## Remaining goals, not Lean declarations

both `c = 1` and `c = 0`:

```
(sim : PrimedSimActive u w h k m n eφ vφ)
(hm : m < primedIntervalBase (primedSimInput w) h k +
  primedIntervalWidth (primedSimInput w) h k)
(hu : u m = c) (hw : w n = c)
⊢ ∃ eφ' vφ',
    (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
    (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
    PrimedSimActive u w h k (m+1) (n+1) eφ' vφ'
```

For up, all clauses except the original surviving-boundary clause have been
proved above without `LR_root`. One unresolved case of that clause is:

```
(sh := kmswMissingRootStage u m) (gl := kmswStage w n)
(he : e ∈ sh.LR) (ha : eφ e = gl.active)
⊢ eφ e ∈ primedGlobalFrontier (kmswStepOfStep gl .up) ∨ eφ e ∈ cutAtExit w h k
```

The stronger local condition `sh.LR = [0]` resolves this case using the
existing missing-root LL membership. It is established at the first triangle
and preserved by the complete up, down and empty-predecessor left steps above.
No derivation of this condition from the original invariant, and no concrete
counterexample to the original invariant, is claimed.

The remaining ordinary left goal even with the strengthening is the
nonempty-predecessor branch:

```
(sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
(hm : m < primedIntervalBase (primedSimInput w) h k +
  primedIntervalWidth (primedSimInput w) h k)
(hu : u m = 0) (hw : w n = 0)
(hpred : (kmswMissingRootStage u m).UL.dropLast.reverse = a :: as)
⊢ PrimedSimActiveRootLR u w h k (m+1) (n+1)
    (kmswShiftFreshEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ) vφ
```

The aligned consumed head and its ordered incidence are proved by
`left_head_incidence`; preservation of the full invariant in this branch
has not been proved here.

`w i = ω (i+1)`, `m = primedIntervalBase ω h (k+1)`,
`n = walkNR w h (k+1)-1`, and `n' = walkNL w h (k+1)`, its goal is

```
(sim : PrimedSimActive u w h k m n eφ vφ)
⊢ ∃ eφ' vφ',
    (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
    (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
    PrimedSimActive u w h (k+1) (m+1) n' eφ' vφ'
```

For `E = (kmswMissingRootStage u m).nextEdge`,
`V = (kmswMissingRootStage u m).nextVertex`, and
`s = kmswStage w (n'-1)`, its required fresh images are
`eφ' E = s.nextEdge`, `eφ' (E+1) = s.active`, `vφ' V = s.east s.active`.
Cut change, surviving boundary images, LL persistence of the missing root,
non-reachability across the omitted excursion, and common-prefix restart
remain obligations. The ordinary-step reachable-set equality proved here
cannot be substituted across that excursion. No numbered paper result,
P2 simulation, or Section 6 recursion is completed by this file. -/

end DirectedDistances.KMSW
