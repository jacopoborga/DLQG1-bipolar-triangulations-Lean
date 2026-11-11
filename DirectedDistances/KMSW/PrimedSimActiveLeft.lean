module

public import DirectedDistances.KMSW.PrimedSimActiveSteps

/-! # Nonempty-predecessor ordinary primed left simulation

Partial P2 helpers toward `lem-quad-kmsw`
These helpers do not count as Lemma 5.13 or the full primed simulation. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk

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


private theorem fresh_eq_up (sh gl : State) (eφ : ℕ → ℕ)
    (e : ℕ) (he : e < sh.nextEdge + 1) :
    kmswShiftFreshEdgeMap sh gl eφ e = kmswShiftUpEdgeMap sh gl eφ e := by
  simp only [kmswShiftFreshEdgeMap, kmswShiftUpEdgeMap]
  split <;> simp_all only [ite_eq_right (by omega : e ≠ sh.nextEdge + 1)]

/-- One-edge allocation preserves bounds and injectivity. Partial P2 helper, -/
private theorem PrimedSimActive.left_nonempty_allocation {u w : ℕ → Fin 3}
    {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w n
    let eψ := kmswShiftFreshEdgeMap sh gl eφ
    (∀ e, e < sh.nextEdge + 1 → eψ e < gl.nextEdge + 1) ∧
    (∀ e f, e < sh.nextEdge + 1 → f < sh.nextEdge + 1 →
      eψ e = eψ f → e = f) := by
  dsimp only
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  change (∀ e, e < sh.nextEdge + 1 → kmswShiftFreshEdgeMap sh gl eφ e < gl.nextEdge + 1) ∧
    (∀ e f, e < sh.nextEdge + 1 → f < sh.nextEdge + 1 →
      kmswShiftFreshEdgeMap sh gl eφ e = kmswShiftFreshEdgeMap sh gl eφ f → e = f)
  constructor
  · intro e he
    by_cases hh : e = sh.nextEdge
    · subst e; simp [kmswShiftFreshEdgeMap]
    · have heold : e < sh.nextEdge := by omega
      have hb := sim.edge_bound e heold
      change eφ e < gl.nextEdge at hb
      simpa only [kmswShiftFreshEdgeMap, ite_eq_right hh] using
        (show eφ e < gl.nextEdge + 1 by omega)
  · intro e f he hf hef
    rw [fresh_eq_up sh gl eφ e he, fresh_eq_up sh gl eφ f hf] at hef
    exact sim.up_allocation.2.1 e f (by change e < sh.nextEdge + 2; omega)
      (by change f < sh.nextEdge + 2; omega) hef

/-- The one-edge left allocation fixes all old edge and vertex images.
Partial P2 helper, not `lem-quad-kmsw` -/
theorem primedLeft_nonempty_maps_extend (sh gl : State) (eφ vφ : ℕ → ℕ) :
    (∀ e, e < sh.nextEdge → kmswShiftFreshEdgeMap sh gl eφ e = eφ e) ∧
    (∀ v, v < sh.nextVertex → vφ v = vφ v) := by
  exact ⟨fun e he => by simp only [kmswShiftFreshEdgeMap, ite_eq_right (ne_of_lt he)],
    fun _ _ => rfl⟩

private theorem local_missing (u : ℕ → Fin 3) (m e : ℕ)
    (he : e ∈ (kmswMissingRootStage u m).UR ∨
      e ∈ (kmswMissingRootStage u m).LL) :
    (kmswMissingRootStage u m).present e = false := by
  obtain ⟨_, hE, _, _, hp, _, _, _, hUR, hLL, _⟩ := kmswMissingRootStage_agree u m
  by_cases hz : e = 0
  · subst e; exact kmswMissingRootStage_present_zero u m
  · rw [hp e hz]
    apply ((kmswStage_status u m).1 e ?_).mpr
    · simpa only [hUR, hLL] using he
    · rw [← hE]
      exact (local_bounds u m).2.1 e (by
        simp only [primedGlobalFrontier, List.mem_append]
        exact Or.inr (he.elim (fun hh => Or.inl hh) (fun hh => Or.inr (Or.inl hh))))

/-- Nonempty-predecessor left steps preserve surviving boundary images.
Partial P2 helper, not `lem-quad-kmsw` -/
private theorem PrimedSimActiveRootLR.left_nonempty_boundary {u w : ℕ → Fin 3}
    {h : HasFlowLineHits w} {k m n a : ℕ} {as : List ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hu : u m = 0) (hw : w n = 0)
    (hpred : (kmswMissingRootStage u m).UL.dropLast.reverse = a :: as) :
    let eψ := kmswShiftFreshEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ
    ∀ e, e ∈ primedGlobalFrontier (kmswMissingRootStage u (m + 1)) →
      eψ e ∈ primedGlobalFrontier (kmswStage w (n + 1)) ∨ eψ e ∈ cutAtExit w h k := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftFreshEdgeMap sh gl eφ
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .left := by
    simp only [kmswStage, hw]; rfl
  have hs : sh.UL.dropLast.reverse = a :: as := hpred
  have hgs : gl.UL.dropLast.reverse = eφ a :: as.map eφ :=
    (sim.forget.left_head_incidence hpred).1
  have htail (e : ℕ) (he : e ∈ as) : e < sh.nextEdge := by
    apply (local_bounds u m).2.1
    simp only [primedGlobalFrontier, List.mem_append]
    apply Or.inl
    apply List.mem_of_mem_dropLast
    apply List.mem_reverse.mp
    rw [hs]
    exact List.mem_cons_of_mem a he
  have hmap : as.map eψ = as.map eφ := by
    apply List.map_congr_left
    intro e he
    exact (primedLeft_nonempty_maps_extend sh gl eφ vφ).1 e (htail e he)
  have hul : (kmswMissingRootStage u (m + 1)).UL.map eψ =
      (kmswStage w (n + 1)).UL := by
    simp only [hl, hg, kmswStepOfStep, hs, hgs, List.map_append, List.map_cons,
      List.map_nil, List.map_reverse, hmap]
    simp [eψ, kmswShiftFreshEdgeMap]
  have hold (e : ℕ) (he : e ∈ sh.UR ∨ e ∈ sh.LL) :
      eψ e ∈ primedGlobalFrontier (kmswStage w (n + 1)) ∨ eψ e ∈ cutAtExit w h k := by
    have hf : e ∈ primedGlobalFrontier sh := by
      simp only [primedGlobalFrontier, List.mem_append]
      exact Or.inr (he.elim (fun hh => Or.inl hh) (fun hh => Or.inr (Or.inl hh)))
    have hb := (local_bounds u m).2.1 e hf
    rw [show eψ e = eφ e from (primedLeft_nonempty_maps_extend sh gl eφ vφ).1 e hb]
    rcases sim.forget.frontier_image e hf with hh | hh
    · have hnUL : eφ e ∉ gl.UL := by
        intro hhUL
        rw [← sim.UL_alignment] at hhUL
        obtain ⟨f, hfUL, hfe⟩ := List.mem_map.mp hhUL
        have hfb := (local_bounds u m).2.1 f (by
          simp only [primedGlobalFrontier, List.mem_append]; exact Or.inl hfUL)
        have hfe' := sim.edge_injective f e hfb hb hfe
        subst f
        have hp := sim.forget.UL_present e hfUL
        rw [local_missing u m e he] at hp
        cases hp
      have hh' : eφ e ∈ gl.UR ∨ eφ e ∈ gl.LL ∨ eφ e ∈ gl.LR := by
        have hhgl : eφ e ∈ primedGlobalFrontier gl := hh
        simpa only [primedGlobalFrontier, List.mem_append, hnUL, false_or] using hhgl
      left
      simp only [hg, primedGlobalFrontier, kmswStepOfStep, hgs, State.addEdge,
        List.mem_append]
      exact Or.inr hh'
    · exact Or.inr hh
  dsimp only
  change ∀ e, e ∈ primedGlobalFrontier (kmswMissingRootStage u (m + 1)) →
    eψ e ∈ primedGlobalFrontier (kmswStage w (n + 1)) ∨ eψ e ∈ cutAtExit w h k
  intro e he
  simp only [primedGlobalFrontier, List.mem_append] at he
  rcases he with he | he | he | he
  · left
    have hh : eψ e ∈ (kmswStage w (n + 1)).UL := by
      rw [← hul]; exact List.mem_map.mpr ⟨e, he, rfl⟩
    simp only [primedGlobalFrontier, List.mem_append]
    exact Or.inl hh
  · apply hold e (Or.inl ?_)
    simpa only [hl, kmswStepOfStep, hs, State.addEdge] using he
  · apply hold e (Or.inr ?_)
    simpa only [hl, kmswStepOfStep, hs, State.addEdge] using he
  · have hz : e = 0 := by
      simpa only [hl, kmswStepOfStep, hs, State.addEdge, sh, sim.LR_root,
        List.mem_singleton] using he
    subst e
    have hb : 0 < sh.nextEdge := by have hh := (local_bounds u m).1; change sh.active < sh.nextEdge at hh; omega
    rw [show eψ 0 = eφ 0 from (primedLeft_nonempty_maps_extend sh gl eφ vφ).1 0 hb]
    left
    simp only [hg, primedGlobalFrontier, kmswStepOfStep, hgs, State.addEdge, List.mem_append]
    exact Or.inr (Or.inr (Or.inl sim.missing_root.2.2))

/-- An ordinary left step with a nonempty predecessor stack preserves the
root-LR simulation, using the explicit one-edge allocation and unchanged
vertex map. Partial P2 helper, not `lem-quad-kmsw` -/
theorem primedSimActiveRootLR_left_nonempty {u w : ℕ → Fin 3}
    {h : HasFlowLineHits w} {k m n a : ℕ} {as : List ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 0) (hw : w n = 0)
    (hpred : (kmswMissingRootStage u m).UL.dropLast.reverse = a :: as) :
    PrimedSimActiveRootLR u w h k (m + 1) (n + 1)
      (kmswShiftFreshEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ) vφ := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftFreshEdgeMap sh gl eφ
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep gl .left := by
    simp only [kmswStage, hw]; rfl
  have hs : sh.UL.dropLast.reverse = a :: as := hpred
  obtain ⟨hgs, hwest, heast⟩ := sim.forget.left_head_incidence hpred
  change gl.UL.dropLast.reverse = eφ a :: as.map eφ at hgs
  change gl.west (eφ a) = vφ (sh.west a) at hwest
  have hactive := sim.present_incidence sh.active (local_bounds u m).1
    (by
      have hp := kmswStage_active_present u m
      obtain ⟨_, _, _, _, hp', _, ha, _, _, _, _⟩ := kmswMissingRootStage_agree u m
      have hne : sh.active ≠ 0 := by
        intro hz
        have hh := sim.forget.UL_present 0 (by
          obtain ⟨xs, hxs⟩ := kmswStage_UL_last u m
          obtain ⟨_, _, _, _, _, _, ha', hul, _⟩ := kmswMissingRootStage_agree u m
          rw [hul, hxs]
          have hzero : (kmswStage u m).active = 0 := ha'.symm.trans hz
          simp [hzero])
        rw [sim.missing_root.1] at hh
        cases hh
      rw [hp' sh.active hne, ha]
      exact hp)
  rw [sim.active_alignment] at hactive
  change gl.west gl.active = vφ (sh.west sh.active) ∧
    gl.east gl.active = vφ (sh.east sh.active) at hactive
  have hb := sim.forget.left_nonempty_allocation
  have ext (e : ℕ) (he : e < sh.nextEdge) : eψ e = eφ e :=
    (primedLeft_nonempty_maps_extend sh gl eφ vφ).1 e he
  have ha : 0 < sh.nextEdge := by have hh := (local_bounds u m).1; change sh.active < sh.nextEdge at hh; omega
  have hzero := sim.edge_bound 0 ha
  change eφ 0 < gl.nextEdge at hzero
  have hactiveMap : eφ sh.active = gl.active := sim.active_alignment
  have hbounds := sim.forget.ordinary_bounds hm
  have hreach := lPhase_reachablePresentEdges_succ_eq w h k n hbounds.1 hbounds.2
  have hnot : gl.nextEdge ∉ stageReachablePresentEdges w (n + 1) := by
    have hun := lPhase_activeWest_unreachable w h k (n + 1) (by omega) hbounds.2
    have hact : act w (n + 1) = gl.nextEdge := by
      simp only [act, hg, kmswStepOfStep, hgs]
    rw [hact] at hun
    intro he
    exact hun he.2.2.1
  have htail (e : ℕ) (he : e ∈ as) : e < sh.nextEdge := by
    apply (local_bounds u m).2.1
    simp only [primedGlobalFrontier, List.mem_append]
    apply Or.inl
    apply List.mem_of_mem_dropLast
    apply List.mem_reverse.mp
    rw [hs]
    exact List.mem_cons_of_mem a he
  have hmap : as.map eψ = as.map eφ := by
    apply List.map_congr_left
    intro e he
    exact ext e (htail e he)
  change PrimedSimActiveRootLR u w h k (m + 1) (n + 1) eψ vφ
  refine {
    edge_bound := ?_, edge_injective := ?_, vertex_bound := ?_, vertex_injective := ?_
    present_incidence := ?_, missing_incidence := ?_
    present_complement := ?_, missing_root := ?_
    triangle_incidence := ?_, boundary_image := ?_
    after_base := ?_, time_alignment := ?_
    active_alignment := ?_, UL_alignment := ?_, UR_alignment := ?_, LR_root := ?_ }
  · simpa only [hl, hg, kmswStepOfStep, hs, hgs, State.addEdge] using hb.1
  · simpa only [hl, kmswStepOfStep, hs, State.addEdge] using hb.2
  · simpa only [hl, hg, kmswStepOfStep, hs, hgs, State.addEdge] using sim.vertex_bound
  · simpa only [hl, kmswStepOfStep, hs, State.addEdge] using sim.vertex_injective
  · intro e he hp
    rw [hl] at he hp ⊢
    rw [hg]
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hs, State.addEdge] at he; omega
    rcases hc with heold | rfl
    · have heb := sim.edge_bound e heold
      change eφ e < gl.nextEdge at heb
      have hpold : sh.present e = true := by
        simpa only [kmswStepOfStep, hs, State.addEdge, ite_eq_right (ne_of_lt heold)] using hp
      simpa only [kmswStepOfStep, hs, hgs, State.addEdge, ext e heold,
        ite_eq_right (ne_of_lt heold), ite_eq_right (ne_of_lt heb)] using
        sim.present_incidence e heold hpold
    · simpa only [kmswStepOfStep, hs, hgs, State.addEdge, eψ,
        kmswShiftFreshEdgeMap, ite_true] using And.intro hwest hactive.2
  · intro e he hp
    rw [hl] at he hp ⊢
    rw [hg]
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hs, State.addEdge] at he; omega
    rcases hc with heold | rfl
    · have heb := sim.edge_bound e heold
      change eφ e < gl.nextEdge at heb
      have hpold : sh.present e = false := by
        simpa only [kmswStepOfStep, hs, State.addEdge, ite_eq_right (ne_of_lt heold)] using hp
      simpa only [kmswStepOfStep, hs, hgs, State.addEdge, ext e heold,
        ite_eq_right (ne_of_lt heold), ite_eq_right (ne_of_lt heb)] using
        sim.missing_incidence e heold hpold
    · simp only [kmswStepOfStep, hs, State.addEdge, ite_true] at hp
      cases hp
  · intro e he hp
    rw [hl] at he hp
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hs, State.addEdge] at he; omega
    rcases hc with heold | rfl
    · have heb := sim.edge_bound e heold
      change eφ e < gl.nextEdge at heb
      have hpold : sh.present e = true := by
        simpa only [kmswStepOfStep, hs, State.addEdge, ite_eq_right (ne_of_lt heold)] using hp
      have hh := sim.present_complement e heold hpold
      constructor
      · simpa only [hg, kmswStepOfStep, hgs, State.addEdge, ext e heold,
          ite_eq_right (ne_of_lt heb)] using hh.1
      · rw [ext e heold, hreach]; exact hh.2
    · constructor
      · simp only [hg, kmswStepOfStep, hgs, State.addEdge, eψ,
          kmswShiftFreshEdgeMap, ite_true]
      · simpa only [eψ, kmswShiftFreshEdgeMap, ite_true] using hnot
  · refine ⟨kmswMissingRootStage_present_zero u (m + 1), ?_, ?_⟩
    · simpa only [hg, kmswStepOfStep, hgs, State.addEdge, ext 0 ha,
        ite_eq_right (ne_of_lt hzero)] using sim.missing_root.2.1
    · simpa only [hg, kmswStepOfStep, hgs, State.addEdge, ext 0 ha] using sim.missing_root.2.2
  · intro b c d ht
    rw [hl] at ht
    simp only [kmswStepOfStep, hs, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht
    · obtain ⟨x, y, z, hxyz, hi⟩ := sim.triangle_incidence b c d ht
      obtain ⟨_, hE, _, _, _, htri, _⟩ := kmswMissingRootStage_agree u m
      have ht' : (b, c, d) ∈ (kmswStage u m).triangles := htri ▸ ht
      obtain ⟨hb, hc, hd⟩ := stage_triangle_bounds u m b c d ht'
      refine ⟨x, y, z, ?_, ?_⟩
      · rw [hg]
        simp only [kmswStepOfStep, hgs]
        exact List.mem_append_left _ hxyz
      · simpa only [ext b (hE.symm ▸ hb), ext c (hE.symm ▸ hc),
          ext d (hE.symm ▸ hd)] using hi
    · cases ht
      refine ⟨gl.active, gl.nextEdge, eφ a, ?_, ?_⟩
      · rw [hg]; simp [kmswStepOfStep, hgs]
      · have hab : a < sh.nextEdge := by
          apply (local_bounds u m).2.1
          simp only [primedGlobalFrontier, List.mem_append]
          apply Or.inl
          apply List.mem_of_mem_dropLast
          apply List.mem_reverse.mp
          rw [hs]; simp
        simp only [ext sh.active (local_bounds u m).1, ext a hab,
          hactiveMap, eψ, kmswShiftFreshEdgeMap, ite_true]
  · intro e he
    apply sim.left_nonempty_boundary hu hw hpred e
    simpa only [primedGlobalFrontier, List.mem_append, or_assoc] using he
  · have hh := sim.after_base; omega
  · have hh := sim.after_base
    have ht := sim.time_alignment
    omega
  · simp only [hl, hg, kmswStepOfStep, hs, hgs, eψ, kmswShiftFreshEdgeMap, ite_true]
  · simp only [hl, hg, kmswStepOfStep, hs, hgs, List.map_append,
      List.map_cons, List.map_nil, List.map_reverse, hmap]
    simp only [eψ, kmswShiftFreshEdgeMap, ite_true]
  · obtain ⟨xs, ys, zs, hxs, hgsUR, hlen, hi⟩ := sim.UR_alignment
    have hxb (e : ℕ) (he : e ∈ xs) : e < sh.nextEdge := by
      apply (local_bounds u m).2.1
      simp only [primedGlobalFrontier, List.mem_append]
      exact Or.inr (Or.inl (hxs ▸ List.mem_append_left _ he))
    have hxm : xs.map eψ = xs.map eφ := by
      apply List.map_congr_left
      intro e he
      exact ext e (hxb e he)
    refine ⟨xs, ys, zs, ?_, ?_, ?_, ?_⟩
    · simpa only [hl, kmswStepOfStep, hs, State.addEdge] using hxs
    · simpa only [hg, kmswStepOfStep, hgs, State.addEdge, hxm] using hgsUR
    · have hr : R w (n + 1) = R w n := by
        simp [R, Finset.sum_range_succ, hw, lazyTwoDimensionalStep]
      rw [hr]; exact hlen
    · intro e he
      have heb := hxb e he
      have hgeb := sim.edge_bound e heb
      change eφ e < gl.nextEdge at hgeb
      simpa only [hl, hg, kmswStepOfStep, hs, hgs, State.addEdge, ext e heb,
        ite_eq_right (ne_of_lt heb), ite_eq_right (ne_of_lt hgeb)] using hi e he
  · simpa only [hl, kmswStepOfStep, hs, State.addEdge] using sim.LR_root

/-- Extension-form nonempty-predecessor left transition. The witnesses are
`kmswShiftFreshEdgeMap` and the unchanged vertex map, fixing every old ID.
Partial P2 helper, not `lem-quad-kmsw` -/
theorem primedSimActiveRootLR_left_nonempty_extends {u w : ℕ → Fin 3}
    {h : HasFlowLineHits w} {k m n a : ℕ} {as : List ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 0) (hw : w n = 0)
    (hpred : (kmswMissingRootStage u m).UL.dropLast.reverse = a :: as) :
    ∃ eφ' vφ',
      (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
      (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
      PrimedSimActiveRootLR u w h k (m + 1) (n + 1) eφ' vφ' := by
  exact ⟨_, _, (primedLeft_nonempty_maps_extend (kmswMissingRootStage u m) (kmswStage w n) eφ vφ).1,
    (primedLeft_nonempty_maps_extend (kmswMissingRootStage u m) (kmswStage w n) eφ vφ).2,
    primedSimActiveRootLR_left_nonempty sim hm hu hw hpred⟩

/-- All three ordinary codes extend the root-LR simulation within a block.
The left branch splits on its predecessor stack; no compressed crossing is
asserted. Partial P2 helper, not `lem-quad-kmsw` -/
theorem primedSimActiveRootLR_ordinary_step {u w : ℕ → Fin 3}
    {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (c : Fin 3) (hu : u m = c) (hw : w n = c) :
    ∃ eφ' vφ',
      (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
      (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
      PrimedSimActiveRootLR u w h k (m + 1) (n + 1) eφ' vφ' := by
  fin_cases c
  · cases hpred : (kmswMissingRootStage u m).UL.dropLast.reverse with
    | nil => exact sim.step_left_empty_extends hm hu hw hpred
    | cons a as =>
      exact primedSimActiveRootLR_left_nonempty_extends sim hm hu hw hpred
  · exact sim.step_up_extends hm hu hw
  · exact ⟨eφ, vφ, fun _ _ => rfl, fun _ _ => rfl, sim.step_down hm hu hw⟩

end DirectedDistances.KMSW
