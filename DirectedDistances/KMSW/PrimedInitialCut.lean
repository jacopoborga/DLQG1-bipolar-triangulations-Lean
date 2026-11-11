module

public import DirectedDistances.KMSW.PrimedInitialStage
public import DirectedDistances.KMSW.PrimedCutInterface

/- # Partial primed complement bookkeeping at a finite cut

The boundary convention is at line 415 in the supplied source, rather than
paper result is asserted here. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/-- Partial complement bookkeeping toward `lem-quad-kmsw`
incidence for missing geometric edges. The boundary membership clause is
explicitly PARTIAL bookkeeping: it does not fix run order, direction, or
boundary attachment. The exact ordered exterior-word correspondence is a
later obligation. This helper is not counted as `lem-quad-kmsw`. -/
structure PrimedComplementSimCut (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k m n : ℕ) (eφ vφ : ℕ → ℕ) : Prop where
  edge_bound : ∀ e, e < (kmswMissingRootStage u m).nextEdge →
    eφ e < (kmswStage w n).nextEdge
  edge_injective : ∀ e f, e < (kmswMissingRootStage u m).nextEdge →
    f < (kmswMissingRootStage u m).nextEdge → eφ e = eφ f → e = f
  vertex_bound : ∀ v, v < (kmswMissingRootStage u m).nextVertex →
    vφ v < (kmswStage w n).nextVertex
  vertex_injective : ∀ v z,
    v < (kmswMissingRootStage u m).nextVertex →
    z < (kmswMissingRootStage u m).nextVertex → vφ v = vφ z → v = z
  present_incidence : ∀ e, e < (kmswMissingRootStage u m).nextEdge →
    (kmswMissingRootStage u m).present e = true →
    (kmswStage w n).west (eφ e) = vφ ((kmswMissingRootStage u m).west e) ∧
    (kmswStage w n).east (eφ e) = vφ ((kmswMissingRootStage u m).east e)
  missing_incidence : ∀ e, e < (kmswMissingRootStage u m).nextEdge →
    (kmswMissingRootStage u m).present e = false →
    ({(kmswStage w n).west (eφ e), (kmswStage w n).east (eφ e)} : Multiset ℕ) =
      {vφ ((kmswMissingRootStage u m).west e),
        vφ ((kmswMissingRootStage u m).east e)}
  present_complement : ∀ e,
    e < (kmswMissingRootStage u m).nextEdge →
    (kmswMissingRootStage u m).present e = true →
    (kmswStage w n).present (eφ e) = true ∧
      eφ e ∉ stageReachablePresentEdges w n
  missing_root :
    (kmswMissingRootStage u m).present 0 = false ∧
    (kmswStage w n).present (eφ 0) = false ∧
    eφ 0 ∈ (kmswStage w n).LL
  triangle_incidence : ∀ a b c,
    (a, b, c) ∈ (kmswMissingRootStage u m).triangles →
    ∃ x y z, (x, y, z) ∈ (kmswStage w n).triangles ∧
      ({eφ a, eφ b, eφ c} : Multiset ℕ) = {x, y, z}
  boundary_image : ∀ e,
    e ∈ (kmswMissingRootStage u m).UL ++ (kmswMissingRootStage u m).UR ++
      (kmswMissingRootStage u m).LL ++ (kmswMissingRootStage u m).LR →
    eφ e ∈ primedGlobalFrontier (kmswStage w n) ∨ eφ e ∈ cutAtExit w h k

/-- The old global-frontier proxy implies the partial cut bookkeeping
for every chosen exit. Helper toward `lem-quad-kmsw` -/
theorem PrimedComplementSim.toCut {u w : ℕ → Fin 3}
    {m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedComplementSim u w m n eφ vφ)
    (h : HasFlowLineHits w) (k : ℕ) :
    PrimedComplementSimCut u w h k m n eφ vφ where
  edge_bound := sim.edge_bound
  edge_injective := sim.edge_injective
  vertex_bound := sim.vertex_bound
  vertex_injective := sim.vertex_injective
  present_incidence := sim.present_incidence
  missing_incidence := sim.missing_incidence
  present_complement := sim.present_complement
  missing_root := sim.missing_root
  triangle_incidence := sim.triangle_incidence
  boundary_image := by
    intro e he
    simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · exact Or.inl (sim.UL_frontier e he)
    · exact Or.inl (sim.UR_frontier e he)
    · exact Or.inl (sim.LL_frontier e he)
    · exact Or.inl (sim.LR_frontier e he)

/- initial simulation therefore supplies this partial cut simulation directly.
The first triangle and its cut side occur at local stage one, not zero. -/
theorem primedInitial_complementSimCut (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    PrimedComplementSimCut u w h 0 0 (walkNL w h 0)
      (primedInitialEdgeMap w (walkNL w h 0))
      (primedInitialVertexMap w (walkNL w h 0)) := by
  exact (primedInitial_complementSim u w h).toCut h 0

/-- Edge map for the first C13 triangle: root to global missing side,
present side to new active, missing third side to old active. Finite helper -/
@[expose] def primedFirstStepEdgeMap (w : ℕ → Fin 3) (n : ℕ) : ℕ → ℕ :=
  fun e => if e = 0 then (kmswStage w (n - 1)).nextEdge + 1
    else if e = 1 then (kmswStage w (n - 1)).nextEdge
    else if e = 2 then (kmswStage w (n - 1)).active else e

/-- Vertex map for the first C13 triangle, retaining the missing-root
endpoints and attaching its new vertex at the old active terminal vertex. -/
@[expose] def primedFirstStepVertexMap (w : ℕ → Fin 3) (n : ℕ) : ℕ → ℕ :=
  fun v => if v = 0 then (kmswStage w (n - 1)).nextVertex
    else if v = 1 then
      (kmswStage w (n - 1)).west (kmswStage w (n - 1)).active
    else if v = 2 then
      (kmswStage w (n - 1)).east (kmswStage w (n - 1)).active else v

/-- The first C13 up step produces the partial complement invariant at the
same global exit stage. Its missing third side maps into the selected cut,
rather than necessarily into the global frontier. This is finite membership
and incidence bookkeeping only, not an ordered exterior-word correspondence -/
theorem primedFirstStep_complementSimCut (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu : u 0 = 1) :
    PrimedComplementSimCut u w h 0 1 (walkNL w h 0)
      (primedFirstStepEdgeMap w (walkNL w h 0))
      (primedFirstStepVertexMap w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have hdrop : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have hstep : kmswStage w n = kmswStepOfStep s .left :=
    primedInitial_globalExitTransition w h
  have ha : s.active < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
  have hv := kmswStage_endpoints_lt_nextVertex w (n - 1) s.active ha
  change s.west s.active < s.nextVertex ∧ s.east s.active < s.nextVertex at hv
  have hne : s.east s.active ≠ s.west s.active := by
    have hn := activeEast_ne_activeInitial w (j := n - 1) (n := n - 1) le_rfl
    have hw := (edge_endpoints_eq w ha).1
    change s.east s.active ≠ edgeWest w s.active at hn
    rw [← hw] at hn
    exact hn
  have hlocal : kmswMissingRootStage u 1 = kmswStepOfStep kmswMissingRootInit .up := by
    simp only [kmswMissingRootStage, hu]
    rfl
  have hnot : s.nextEdge ∉ stageReachablePresentEdges w n := by
    have hg := (quadrantFirstR_exit_gluingTriangle w h).2.1
    have hh := (quadrantFirstRStage_exit_active_not_reachable w h).2
    rwa [hg] at hh
  have hcut : s.active ∈ cutAtExit w h 0 := active_mem_cutAtExit w h 0
  have hemap (e : ℕ) : primedFirstStepEdgeMap w n e =
      if e = 0 then s.nextEdge + 1 else if e = 1 then s.nextEdge
        else if e = 2 then s.active else e := rfl
  have hvmap (v : ℕ) : primedFirstStepVertexMap w n v =
      if v = 0 then s.nextVertex else if v = 1 then s.west s.active
        else if v = 2 then s.east s.active else v := rfl
  change PrimedComplementSimCut u w h 0 1 n
    (primedFirstStepEdgeMap w n) (primedFirstStepVertexMap w n)
  constructor
  · intro e he
    rw [hlocal] at he
    have he3 : e < 3 := he
    have hecases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases hecases with rfl | rfl | rfl <;>
      simp [hemap, hstep, kmswStepOfStep, hdrop, State.addEdge]
    omega
  · intro e f he hf hef
    rw [hlocal] at he hf
    have he3 : e < 3 := he
    have hf3 : f < 3 := hf
    have hecases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    have hfcases : f = 0 ∨ f = 1 ∨ f = 2 := by omega
    rcases hecases with rfl | rfl | rfl <;>
      rcases hfcases with rfl | rfl | rfl <;>
      simp [hemap] at hef ⊢ <;> omega
  · intro v hvb
    rw [hlocal] at hvb
    have hv3 : v < 3 := hvb
    have hvcases : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases hvcases with rfl | rfl | rfl <;>
      simp [hvmap, hstep, kmswStepOfStep, hdrop, State.addEdge] <;> omega
  · intro v z hvb hzb hvz
    rw [hlocal] at hvb hzb
    have hv3 : v < 3 := hvb
    have hz3 : z < 3 := hzb
    have hvcases : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    have hzcases : z = 0 ∨ z = 1 ∨ z = 2 := by omega
    rcases hvcases with rfl | rfl | rfl <;>
      rcases hzcases with rfl | rfl | rfl <;>
      simp [hvmap] at hvz ⊢ <;> omega
  · intro e he hp
    rw [hlocal] at he hp ⊢
    have he3 : e < 3 := he
    have hecases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases hecases with rfl | rfl | rfl <;>
      simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    simp [hemap, hvmap, hstep, kmswStepOfStep, hdrop, State.addEdge,
      kmswMissingRootInit, kmswInit]
  · intro e he hp
    rw [hlocal] at he hp ⊢
    have he3 : e < 3 := he
    have hecases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases hecases with rfl | rfl | rfl
    · simp [hemap, hvmap, hstep, kmswStepOfStep, hdrop, State.addEdge,
        kmswMissingRootInit, kmswInit]
    · simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    · have ha0 : s.active ≠ s.nextEdge := by omega
      have ha1 : s.active ≠ s.nextEdge + 1 := by omega
      simp [hemap, hvmap, hstep, kmswStepOfStep, hdrop, State.addEdge,
        kmswMissingRootInit, kmswInit, ha0, ha1]
      exact Multiset.pair_comm _ _
  · intro e he hp
    rw [hlocal] at he hp
    have he3 : e < 3 := he
    have hecases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases hecases with rfl | rfl | rfl <;>
      simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    constructor
    · simp [hemap, hstep, kmswStepOfStep, hdrop, State.addEdge]
    · simpa [hemap] using hnot
  · rw [hlocal]
    simp [hemap, hstep, kmswStepOfStep, hdrop,
      kmswMissingRootInit, kmswInit, State.addEdge]
  · intro a b c hab
    rw [hlocal] at hab
    have habc : (a, b, c) = (0, 1, 2) := by
      simpa [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] using hab
    cases habc
    refine ⟨s.active, s.nextEdge, s.nextEdge + 1, ?_, ?_⟩
    · rw [hstep]
      simp [kmswStepOfStep, hdrop]
    · simp [hemap, Multiset.cons_swap]
      exact Multiset.pair_comm _ _
  · intro e he
    rw [hlocal] at he
    have hecases : e = 0 ∨ e = 1 ∨ e = 2 := by
      simpa [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge,
        or_comm, or_left_comm] using he
    rcases hecases with rfl | rfl | rfl
    · left
      have hr : s.nextEdge + 1 ∈ (kmswStage w n).LL := by
        rw [hstep]
        simp [kmswStepOfStep, hdrop]
      simp only [hemap, ↓reduceIte, primedGlobalFrontier, List.mem_append]
      exact Or.inr (Or.inr (Or.inl hr))
    · left
      rw [hemap]
      simp [primedGlobalFrontier, hstep, kmswStepOfStep, hdrop]
    · right
      simpa [hemap] using hcut

/-- The first-triangle maps preserve every allocated stage-zero image.
Together with `primedFirstStep_complementSimCut`, this records preservation
of the partial invariant across the first local step. Helper toward -/
theorem primedFirstStep_maps_extend (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    (∀ e, e < (kmswMissingRootStage u 0).nextEdge →
      primedFirstStepEdgeMap w (walkNL w h 0) e =
        primedInitialEdgeMap w (walkNL w h 0) e) ∧
    (∀ v, v < (kmswMissingRootStage u 0).nextVertex →
      primedFirstStepVertexMap w (walkNL w h 0) v =
        primedInitialVertexMap w (walkNL w h 0) v) := by
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have hdrop : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have hstep : kmswStage w n = kmswStepOfStep s .left :=
    primedInitial_globalExitTransition w h
  have hrootId : kmswLLCreatedEdge w n = s.nextEdge + 1 := by
    change (kmswStage w n).nextEdge - 1 = s.nextEdge + 1
    rw [hstep]
    simp [kmswStepOfStep, hdrop, State.addEdge]
  change (∀ e, e < (kmswMissingRootStage u 0).nextEdge →
      primedFirstStepEdgeMap w n e = primedInitialEdgeMap w n e) ∧
    (∀ v, v < (kmswMissingRootStage u 0).nextVertex →
      primedFirstStepVertexMap w n v = primedInitialVertexMap w n v)
  constructor
  · intro e he
    have he0 : e = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using he
    subst e
    simp only [primedFirstStepEdgeMap, primedInitialEdgeMap, ↓reduceIte, hrootId]
    rfl
  · intro v hv
    have hv2 : v < 2 := hv
    have hvCases : v = 0 ∨ v = 1 := by omega
    rcases hvCases with rfl | rfl <;>
      simp [primedFirstStepVertexMap, primedInitialVertexMap, hrootId,
        hstep, kmswStepOfStep, hdrop, State.addEdge, s]

end DirectedDistances.KMSW
