module

public import DirectedDistances.KMSW.KMSWMissingRoot
public import DirectedDistances.KMSW.PrimedLPhaseRecode
public import DirectedDistances.KMSW.QuadKMSWHatFlipped
public import DirectedDistances.KMSW.QuadKMSWHatAllStages
public import DirectedDistances.KMSW.FlowLineTimes
public import DirectedDistances.KMSW.FlowLineBeta

/-! # Initial complement simulation data for the primed map

The initial C18 missing-root state and the first C13 code in the P2
with the first-triangle description at 441–446 and 480–482). This helper
records incidence, directed presence outside the hatted reachable part,
retained root geometry, and boundary-list membership. It does not assert the -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open scoped Classical

/-- The union of the four ordered boundary lists of a finite KMSW state.
It is the target carrier for the entrywise primed-boundary correspondence. -/
@[expose] def primedGlobalFrontier (s : State) : List ℕ :=
  s.UL ++ (s.UR ++ (s.LL ++ s.LR))

/-- Stagewise C18 complement simulation data for the primed KMSW state.
Every allocated geometric edge and vertex is mapped injectively. Present
primed edges preserve their west/east orientation; missing primed edges
preserve their unordered endpoint pairs, since they have geometric endpoints
but no directed orientation. In particular, the flow-line edges on β₀ can
be present global edges while missing as primed directed edges, and their
traversal direction need not agree. Triangle faces are preserved by their
edge sets because KMSW's stored tuple order distinguishes the old active edge.
Present primed edges map to present global edges outside the hatted
reachable-present set. The missing root retains its geometry and maps to the
missing global lower-left boundary edge created at the first left exit. Every
entry of each primed boundary list maps into the global frontier. This relation
is helper data for the first P2 simulation step; the global frontier-membership
clause is the available finite-state proxy for the source interface, not an
identification with the unformalized path β₀. -/
structure PrimedComplementSim (u w : ℕ → Fin 3)
    (m n : ℕ) (eφ vφ : ℕ → ℕ) : Prop where
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
  UL_frontier : ∀ e, e ∈ (kmswMissingRootStage u m).UL →
    eφ e ∈ primedGlobalFrontier (kmswStage w n)
  UR_frontier : ∀ e, e ∈ (kmswMissingRootStage u m).UR →
    eφ e ∈ primedGlobalFrontier (kmswStage w n)
  LL_frontier : ∀ e, e ∈ (kmswMissingRootStage u m).LL →
    eφ e ∈ primedGlobalFrontier (kmswStage w n)
  LR_frontier : ∀ e, e ∈ (kmswMissingRootStage u m).LR →
    eφ e ∈ primedGlobalFrontier (kmswStage w n)

/-- Map the primed missing root edge to the global missing lower-left edge
created at the first left exit (`lem-flow-line-times`, -/
@[expose] def primedInitialEdgeMap (_w : ℕ → Fin 3) (_n : ℕ) : ℕ → ℕ :=
  fun e => if e = 0 then kmswLLCreatedEdge _w _n else e

/-- The C18 primed root edge ID `0` is sent to the global first lower-left
missing edge. -/
@[simp] theorem primedInitialEdgeMap_root (w : ℕ → Fin 3) (n : ℕ) :
    primedInitialEdgeMap w n 0 = kmswLLCreatedEdge w n := by
  simp [primedInitialEdgeMap]

/-- The primed initial vertices map to the endpoints of the global missing
lower-left root edge. -/
@[expose] def primedInitialVertexMap (_w : ℕ → Fin 3) (_n : ℕ) : ℕ → ℕ :=
  fun v =>
    if v = 0 then
      (kmswStage _w _n).west (kmswLLCreatedEdge _w _n)
    else if v = 1 then
      (kmswStage _w _n).east (kmswLLCreatedEdge _w _n)
    else v

/-- The first L-phase exit creates the strict first lower-left record edge. -/
private theorem primedInitial_leftRecord (w : ℕ → Fin 3)
    (h : (∀ t, ∃ m, t + 1 ≤ m ∧ L w m = L w t - 1) ∧
      ∀ t, ∃ m, t + 1 ≤ m ∧ R w m = R w t - 1) :
    let n := walkNL w h 0
    0 < n ∧ ∀ j < n, L w n < L w j := by
  change (∀ t, ∃ m, t + 1 ≤ m ∧ L w m = L w t - 1) ∧
    (∀ t, ∃ m, t + 1 ≤ m ∧ R w m = R w t - 1) at h
  let n := walkNL w h 0
  have hn : n = firstFlowLHit w h 0 := by
    simp [n, walkNL, flowLineTimes]
  have hfind : firstFlowLHit w h 0 = Nat.find (h.1 0) := rfl
  have hspec := firstFlowLHit_spec w h 0
  have hpos : 0 < n := by rw [hn]; exact hspec.1
  have hlevel : L w n = -1 := by
    have hzero : L w 0 = 0 := by simp [L]
    calc
      L w n = L w (firstFlowLHit w h 0) := by rw [hn]
      _ = L w 0 - 1 := hspec.2
      _ = -1 := by rw [hzero]; norm_num
  have hno : ∀ j, 0 < j → j < n → L w j ≠ -1 := by
    intro j hj hjn heq
    have hjlt : j < firstFlowLHit w h 0 := by rw [← hn]; exact hjn
    have hjfind : j < Nat.find (h.1 0) := by
      rw [← hfind]
      exact hjlt
    have hmin := Nat.find_min (h.1 0) hjfind
    apply hmin
    constructor
    · omega
    · have hzero : L w 0 = 0 := by simp [L]
      rw [hzero]
      exact heq
  have hstep (j : ℕ) : L w j - 1 ≤ L w (j + 1) := by
    have hsum : L w (j + 1) = L w j +
        (RandomWalk.lazyTwoDimensionalStep (w j)).1 := by
      simp [L, Finset.sum_range_succ]
    have hdelta : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w j)).1 := by
      have haux (c : Fin 3) : -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).1 := by
        fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]
      exact haux (w j)
    rw [hsum]
    omega
  have hnonneg : ∀ j < n, 0 ≤ L w j := by
    intro j hj
    induction j with
    | zero => simp [L]
    | succ j ih =>
      have hprev : 0 ≤ L w j := ih (by omega)
      have hnext : -1 ≤ L w (j + 1) := by
        have hs := hstep j
        omega
      by_contra hlt
      have heq : L w (j + 1) = -1 := by omega
      exact hno (j + 1) (by omega) hj heq
  refine ⟨hpos, ?_⟩
  intro j hj
  have hjnonneg := hnonneg j hj
  change L w n < L w j
  rw [hlevel]
  omega

/-- The missing-root initial state simulates the global stage at the first
L-phase exit time. Its root maps to the missing global lower-left edge west
of `λ₀`, while the first primed active edge corresponds to the new global
active edge `λ_{N₁ᴸ}` (`lem-flow-line-times`, -/
theorem primedInitial_complementSim (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    PrimedComplementSim u w 0 (walkNL w h 0)
      (primedInitialEdgeMap w (walkNL w h 0))
      (primedInitialVertexMap w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let gl := kmswStage w n
  let root := kmswLLCreatedEdge w n
  have hrecord := primedInitial_leftRecord w h
  change 0 < n ∧ ∀ j < n, L w n < L w j at hrecord
  have hrootLL : root ∈ gl.LL := by
    rw [kmswStage_LL_eq]
    apply List.mem_map.mpr
    refine ⟨n, ?_, rfl⟩
    apply List.mem_reverse.mpr
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_range.mpr (by omega)
    · simp only [decide_eq_true_eq]
      exact hrecord
  have hrootBound : root < gl.nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 root
    simp only [List.mem_append]
    tauto
  have hrootMissing : gl.present root = false := by
    exact kmswLLCreatedEdge_missing w hrecord.1 hrecord.2
  have hrootVertexBounds := kmswStage_endpoints_lt_nextVertex w n root hrootBound
  have hrootFront : root ∈ primedGlobalFrontier gl := by
    have hm : root ∈ gl.UL ++ (gl.UR ++ (gl.LL ++ gl.LR)) :=
      List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hrootLL))
    simpa [primedGlobalFrontier] using hm
  have hrootEnds : gl.west root ≠ gl.east root := by
    let prev := kmswStage w (n - 1)
    have hpos : 0 < n := hrecord.1
    have hcode : w (n - 1) = 0 := walkNL_previous_code w h 0
    have hstep : kmswStage w n = kmswStep prev 0 := by
      have hi : n - 1 + 1 = n := by omega
      rw [← hi]
      change kmswStep (kmswStage w (n - 1)) (w (n - 1)) = _
      rw [hcode]
    have hdrop : prev.UL.dropLast.reverse = [] := by
      cases hp : prev.UL.dropLast.reverse with
      | nil => rfl
      | cons e es =>
        have hid : root = prev.nextEdge := by
          change (kmswStage w n).nextEdge - 1 = prev.nextEdge
          rw [hstep]
          simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
        have hpresent : gl.present root = true := by
          change (kmswStage w n).present root = true
          rw [hstep, hid]
          simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
        rw [hpresent] at hrootMissing
        contradiction
    have hrootId : root = prev.nextEdge + 1 := by
      change (kmswStage w n).nextEdge - 1 = prev.nextEdge + 1
      rw [hstep]
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hdrop, State.addEdge]
    have hw : gl.west root = prev.nextVertex := by
      change (kmswStage w n).west root = prev.nextVertex
      rw [hstep, hrootId]
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hdrop, State.addEdge]
    have he : gl.east root = prev.west prev.active := by
      change (kmswStage w n).east root = prev.west prev.active
      rw [hstep, hrootId]
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hdrop, State.addEdge]
    rw [hw, he]
    have ha : prev.active < prev.nextEdge := by
      exact (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
    have hb := kmswStage_endpoints_lt_nextVertex w (n - 1) prev.active ha
    change prev.west prev.active < prev.nextVertex ∧
      prev.east prev.active < prev.nextVertex at hb
    exact (ne_of_lt hb.1).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have he0 : e = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using he
    subst e
    simpa [primedInitialEdgeMap, root, n] using hrootBound
  · intro e f he hf heq
    have he0 : e = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using he
    have hf0 : f = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using hf
    omega
  · intro v hv
    have hv2 : v < 2 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using hv
    by_cases hv0 : v = 0
    · subst v
      simpa [primedInitialVertexMap, n, gl, root] using hrootVertexBounds.1
    · have hv1 : v = 1 := by omega
      subst v
      simpa [primedInitialVertexMap, n, gl, root] using hrootVertexBounds.2
  · intro v z hv hz hvz
    have hv2 : v < 2 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using hv
    have hz2 : z < 2 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using hz
    by_cases hv0 : v = 0 <;> by_cases hz0 : z = 0
    · subst v
      subst z
      rfl
    · have hz1 : z = 1 := by omega
      subst z
      simp [primedInitialVertexMap, hv0, hz0] at hvz
      exact False.elim (hrootEnds hvz)
    · have hv1 : v = 1 := by omega
      subst v
      simp [primedInitialVertexMap, hv0, hz0] at hvz
      exact False.elim (hrootEnds hvz.symm)
    · have hv1 : v = 1 := by omega
      have hz1 : z = 1 := by omega
      subst v z
      rfl
  · intro e he hp
    have he0 : e = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using he
    subst e
    simp [kmswMissingRootStage, kmswMissingRootInit, kmswInit] at hp
  · intro e he hp
    have he0 : e = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using he
    subst e
    simp [primedInitialEdgeMap, primedInitialVertexMap,
      kmswMissingRootStage, kmswMissingRootInit, kmswInit]
  · intro e he hp
    have he0 : e = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using he
    subst e
    have hfalse : (kmswMissingRootStage u 0).present 0 = false :=
      kmswMissingRootInit_present_zero
    simp [hfalse] at hp
  · exact ⟨kmswMissingRootInit_present_zero, by simpa [gl, root] using hrootMissing,
      by simpa [gl, root] using hrootLL⟩
  · intro a b c hab
    simp [kmswMissingRootStage, kmswMissingRootInit, kmswInit] at hab
  · intro e he
    have he0 : e = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using he
    subst e
    simpa [primedInitialEdgeMap, root, n, gl] using hrootFront
  · simp [kmswMissingRootStage, kmswMissingRootInit, kmswInit]
  · simp [kmswMissingRootStage, kmswMissingRootInit, kmswInit]
  · intro e he
    have he0 : e = 0 := by
      simpa [kmswMissingRootStage, kmswMissingRootInit, kmswInit] using he
    subst e
    simpa [primedInitialEdgeMap, root, n, gl] using hrootFront

/-- The first corrected primed code is C13 code `1`; its corresponding global
code is the left step immediately before `walkNL`, by the interval indexing -/
theorem primedInitial_code_alignment (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    primedCode ω h 0 = 1 ∧
      (fun i => ω (i + 1)) (walkNL (fun i => ω (i + 1)) h 0 - 1) = 0 := by
  constructor
  · exact primedCode_zero ω h
  · exact walkNL_previous_code (fun i => ω (i + 1)) h 0

/-- The global transition producing the first L-phase triangle is the step
from stage `walkNL - 1` to stage `walkNL`, with code `0`. Thus the first
primed code `1` is aligned to this transition, rather than to the subsequent
global transition (`lem-flow-line-times`, -/
theorem primedInitial_globalExitTransition (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    kmswStage w (walkNL w h 0) =
      kmswStep (kmswStage w (walkNL w h 0 - 1)) 0 := by
  have hpos : 0 < walkNL w h 0 := by
    have hs := (walkNL_spec w h 0).1
    rw [walkNR_zero] at hs
    omega
  have hcode : w (walkNL w h 0 - 1) = 0 :=
    walkNL_previous_code w h 0
  have hidx : walkNL w h 0 - 1 + 1 = walkNL w h 0 := by omega
  rw [← hidx]
  have hidx' : walkNL w h 0 - 1 + 1 - 1 = walkNL w h 0 - 1 := by omega
  rw [hidx']
  change kmswStep (kmswStage w (walkNL w h 0 - 1))
      (w (walkNL w h 0 - 1)) = _
  rw [hcode]

/-- The first local C13 up step advances the missing-root state once. This
records its exact finite KMSW geometry before any identification with a -/
theorem primedInitial_firstStep_geometry (u : ℕ → Fin 3) (hu : u 0 = 1) :
    let s := kmswMissingRootStage u 0
    let t := kmswMissingRootStage u 1
    t = kmswStep s 1 ∧
      t.active = s.nextEdge ∧
      t.present s.nextEdge = true ∧
      t.present (s.nextEdge + 1) = false ∧
      t.triangles = s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)] := by
  simp [kmswMissingRootStage, kmswStep, kmswCodeStep, kmswStepOfStep,
    kmswMissingRootInit, kmswInit, State.addEdge, hu]

end DirectedDistances.KMSW
