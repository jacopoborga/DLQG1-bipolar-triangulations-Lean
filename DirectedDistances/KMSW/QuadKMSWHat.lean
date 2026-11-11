/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FirstPhaseReach
public import DirectedDistances.KMSW.FlowLineStageReach
public import DirectedDistances.KMSW.KMSWShiftEmbedding
public import DirectedDistances.RandomWalk.QuadrantSplit
import Mathlib.Tactic.FinCases
meta import Lean.Elab.Tactic.Omega

/-! # First R-phase bookkeeping for the reachable KMSW map

The first R-phase code prefix and its equality with the global finite run
(`lem-flow-line-times` and `eqn-quad-pre`,
code is included in its R stream; the source reachable interval stops just
before the gluing step, so the finite identity result below uses a strict
cutoff. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open Quiver

/-- Put the deterministic time-zero code in front of a KMSW stage code word,
so `phaseSplit` reads stage code `w n` at its input index `n + 1`. -/
@[expose] def quadrantTrajectoryOfStageCodes (w : ℕ → Fin 3) : ℕ → Fin 3
  | 0 => 0
  | n + 1 => w n

/-- Reindex the R component of `phaseSplit` as a KMSW stage input. -/
@[expose] noncomputable def quadrantRStageCodes (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun n => (phaseSplit ω).1 (n + 1)

private theorem codeWalk_succ_add_quad (ω : ℕ → Fin 3) (n : ℕ) :
    codeWalk ω (n + 1) = codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1)) := by
  have h := codeWalk_succ_sub ω n
  calc
    codeWalk ω (n + 1) =
        (codeWalk ω (n + 1) - codeWalk ω n) + codeWalk ω n := by abel
    _ = lazyTwoDimensionalStep (ω (n + 1)) + codeWalk ω n := by rw [h]
    _ = codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1)) := by abel

/-- If the first-coordinate walk has stayed nonnegative through time `n`,
the splitter has remained in its initial R phase and its R state is the
unmodified input prefix (`lem-quadrant-walk`, -/
theorem quadrantSplitState_firstR_of_nonneg (ω : ℕ → Fin 3) :
    ∀ n, (∀ j ≤ n, 0 ≤ (codeWalk ω j).1) →
      quadrantSplitState ω n =
        { phase := .r, rCount := n, lCount := 0,
          rWalk := codeWalk ω n, lWalk := (0, 0), rLMin := 0, lRMin := 0 } := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [quadrantSplitState, quadrantSplitStart, codeWalk_zero]
  | succ n ih =>
      intro hn
      have hnprev : ∀ j ≤ n, 0 ≤ (codeWalk ω j).1 := by
        intro j hj
        exact hn j (by omega)
      have hwalk := codeWalk_succ_add_quad ω n
      have hcoord : 0 ≤ (codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1))).1 := by
        rw [← hwalk]
        exact hn (n + 1) le_rfl
      rw [quadrantSplitState, ih hnprev]
      simp only [quadrantSplitAdvance]
      simp only [hwalk]
      simp only [Prod.fst_add] at hcoord ⊢
      by_cases hhit :
          (codeWalk ω n).1 + (lazyTwoDimensionalStep (ω (n + 1))).1 < 0
      · omega
      · simp [hhit]

/-- At every input index still in the first R phase, the extracted code is
the original code at that stage index. The splitter assigns the exit code to
the phase it terminates (`eqn-quad-pre`, -/
theorem quadrantRStageCodes_eq_of_nonneg (ω : ℕ → Fin 3) {n : ℕ}
    (hn : ∀ j ≤ n, 0 ≤ (codeWalk ω j).1) (i : ℕ) (hi : i ≤ n) :
    quadrantRStageCodes ω i = ω (i + 1) := by
  have hs := quadrantSplitState_firstR_of_nonneg ω i (by
    intro j hj
    exact hn j (by omega))
  have hp : (quadrantSplitState ω i).phase = .r := by
    rw [hs]
  have hc := phaseSplit_rCode_at_step ω i hp
  have hcount : (quadrantSplitState ω i).rCount = i := by rw [hs]
  rw [hcount] at hc
  simpa [quadrantRStageCodes] using hc

/-- Equal code prefixes give equal finite KMSW states. -/
private theorem kmswStage_eq_of_code_prefix (u v : ℕ → Fin 3) :
    ∀ m, (∀ i < m, u i = v i) → kmswStage u m = kmswStage v m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro h
      rw [kmswStage, kmswStage, ih (fun i hi => h i (by omega)), h m (by omega)]

/-- Before the first strict drop of `L` from zero, the horizontal walk stays
nonnegative (`lem-flow-line-times`, -/
theorem firstRPhase_L_nonneg_before_exit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {j : ℕ} (hj : j < walkNL w h 0) :
    0 ≤ L w j := by
  induction j with
  | zero => simp [L]
  | succ j ih =>
      have hjlt : j < walkNL w h 0 := by omega
      have hjval := ih hjlt
      have hstep : L w (j + 1) =
          L w j + (lazyTwoDimensionalStep (w j)).1 := by
        simp only [L, Finset.sum_range_succ]
      have hlow : -1 ≤ (lazyTwoDimensionalStep (w j)).1 := by
        change (-1 : ℤ) ≤ (w j : ℤ) - 1
        omega
      by_contra hneg
      have hminus : L w (j + 1) = -1 := by omega
      have hmin : j + 1 < walkNL w h 0 := by omega
      have hfind : walkNL w h 0 = Nat.find (h.1 0) := rfl
      rw [hfind] at hmin
      have hfirst := Nat.find_min (h.1 0) hmin
      have hzero : L w 0 = 0 := by simp [L]
      apply hfirst
      constructor
      · omega
      · simpa [hzero] using hminus

private theorem quadrantTrajectory_firstCoord_nonneg_before_exit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {j : ℕ} (hj : j < walkNL w h 0) :
    0 ≤ (codeWalk (quadrantTrajectoryOfStageCodes w) j).1 := by
  have hLj := firstRPhase_L_nonneg_before_exit w h hj
  have hcode : (codeWalk (quadrantTrajectoryOfStageCodes w) j).1 = L w j := by
    simp only [codeWalk, L, Prod.fst_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [quadrantTrajectoryOfStageCodes]
  rw [hcode]
  exact hLj

/-- Before the first horizontal flow-line exit, the reindexed R-phase run is
literally the global KMSW stage. In the source time convention this covers
`0 ≤ m < N₁ᴸ`; the terminal `(-1,0)` gluing step is excluded -/
theorem quadrantFirstRStage_eq (w : ℕ → Fin 3) (h : HasFlowLineHits w) {m : ℕ}
    (hm : m < walkNL w h 0) :
    kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m =
      kmswStage w m := by
  apply kmswStage_eq_of_code_prefix
  intro i hi
  have hnonneg : ∀ j ≤ m, 0 ≤ (codeWalk (quadrantTrajectoryOfStageCodes w) j).1 := by
    intro j hji
    have hjstop : j < walkNL w h 0 := by omega
    exact quadrantTrajectory_firstCoord_nonneg_before_exit w h hjstop
  have hcode := quadrantRStageCodes_eq_of_nonneg
    (quadrantTrajectoryOfStageCodes w) hnonneg i (by omega)
  simpa [quadrantRStageCodes, quadrantTrajectoryOfStageCodes] using hcode

/-- The splitter includes the code that first crosses the horizontal
boundary in its terminating R phase. This is the boundary code whose map
triangle is handled separately in `eqn-quad-pre2` -/
theorem quadrantRStageCodes_terminal_exit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
        (walkNL w h 0 - 1) = w (walkNL w h 0 - 1) := by
  have hNpos : 0 < walkNL w h 0 := by
    have := (walkNL_spec w h 0).1
    omega
  have hnonneg : ∀ j ≤ walkNL w h 0 - 1,
      0 ≤ (codeWalk (quadrantTrajectoryOfStageCodes w) j).1 := by
    intro j hj
    exact quadrantTrajectory_firstCoord_nonneg_before_exit w h (by omega)
  have hcode := quadrantRStageCodes_eq_of_nonneg
    (quadrantTrajectoryOfStageCodes w) hnonneg (walkNL w h 0 - 1) le_rfl
  simpa [quadrantRStageCodes, quadrantTrajectoryOfStageCodes] using hcode

/-- The reindexed raw R stream reproduces even the global exit stage; its
vertex image therefore includes the fresh vertex proved unreachable below. -/
theorem quadrantFirstRStage_eq_through_exit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : m ≤ walkNL w h 0) :
    kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m =
      kmswStage w m := by
  apply kmswStage_eq_of_code_prefix
  intro i hi
  have hNpos : 0 < walkNL w h 0 := by
    have := (walkNL_spec w h 0).1
    omega
  have hnonneg : ∀ j ≤ walkNL w h 0 - 1,
      0 ≤ (codeWalk (quadrantTrajectoryOfStageCodes w) j).1 := by
    intro j hj
    exact quadrantTrajectory_firstCoord_nonneg_before_exit w h (by omega)
  have hindex : i ≤ walkNL w h 0 - 1 := by omega
  have hcode := quadrantRStageCodes_eq_of_nonneg
    (quadrantTrajectoryOfStageCodes w) hnonneg i hindex
  simpa [quadrantRStageCodes, quadrantTrajectoryOfStageCodes] using hcode

/-- On the first R-phase prefix the identity maps are a `Sim` in the sense
of `KMSWShiftEmbedding.Sim`; the finite stages themselves agree exactly. -/
theorem quadrantFirstRStage_identitySim (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {m : ℕ} (hm : m < walkNL w h 0) :
    Sim (kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)) m)
      (kmswStage w m) id id := by
  rw [quadrantFirstRStage_eq w h hm]
  let s := kmswStage w m
  refine {
    edge_bound := ?_
    edge_injective := ?_
    vertex_bound := ?_
    vertex_injective := ?_
    active := ?_
    incidence := ?_
    present := ?_
    ur_prefix := ?_
    ul_predecessors_prefix := ?_ }
  · intro e he
    exact he
  · intro e f _ _ hef
    exact hef
  · intro v hv
    exact hv
  · intro v z _ _ hvz
    exact hvz
  · rfl
  · intro e _
    exact ⟨rfl, rfl⟩
  · intro e _ hp
    exact hp
  · simp
  · simp

private theorem allocatedVertex_activeEndpoint (w : ℕ → Fin 3) :
    ∀ n v, v < (kmswStage w n).nextVertex →
      ∃ t ≤ n, v = (kmswStage w t).west (act w t) ∨
        v = (kmswStage w t).east (act w t) := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hv' : v = 0 ∨ v = 1 := by simp [kmswStage, kmswInit] at hv; omega
      rcases hv' with hv0 | hv1
      · subst v
        exact ⟨0, le_rfl, Or.inl (by simp [kmswStage, kmswInit, act])⟩
      · subst v
        exact ⟨0, le_rfl, Or.inr (by simp [kmswStage, kmswInit, act])⟩
  | succ n ih =>
      intro v hv
      let s := kmswStage w n
      have hcode : (w n).val = 0 ∨ (w n).val = 1 ∨ (w n).val = 2 := by
        have := (w n).isLt
        omega
      by_cases hOld : v < s.nextVertex
      · obtain ⟨t, ht, hendpoint⟩ := ih v hOld
        exact ⟨t, by omega, hendpoint⟩
      · rcases hcode with h0 | h1 | h2
        · have hc : w n = 0 := Fin.ext h0
          cases hu : s.UL.dropLast.reverse with
          | nil =>
              have hnext : (kmswStage w (n + 1)).nextVertex = s.nextVertex + 1 := by
                simp [s, kmswStage, kmswStep, kmswCodeStep, hc,
                  kmswStepOfStep, hu, State.addEdge]
              have hwest : (kmswStage w (n + 1)).west (act w (n + 1)) = s.nextVertex := by
                simp [act, s, kmswStage, kmswStep, kmswCodeStep, hc,
                  kmswStepOfStep, hu, State.addEdge]
              have hvnew : v = s.nextVertex := by omega
              exact ⟨n + 1, le_rfl, Or.inl (by rw [hwest, hvnew])⟩
          | cons e es =>
              have hnext : (kmswStage w (n + 1)).nextVertex = s.nextVertex := by
                simp [s, kmswStage, kmswStep, kmswCodeStep, hc,
                  kmswStepOfStep, hu, State.addEdge]
              omega
        · have hc : w n = 1 := Fin.ext h1
          have hnext : (kmswStage w (n + 1)).nextVertex = s.nextVertex + 1 := by
            simp [s, kmswStage, kmswStep, kmswCodeStep, hc,
              kmswStepOfStep, State.addEdge]
          have heast : (kmswStage w (n + 1)).east (act w (n + 1)) = s.nextVertex := by
            simp [act, s, kmswStage, kmswStep, kmswCodeStep, hc,
              kmswStepOfStep, State.addEdge]
          have hvnew : v = s.nextVertex := by omega
          exact ⟨n + 1, le_rfl, Or.inr (by rw [heast, hvnew])⟩
        · have hc : w n = 2 := Fin.ext h2
          cases hu : s.UR with
          | nil =>
              have hnext : (kmswStage w (n + 1)).nextVertex = s.nextVertex + 1 := by
                simp [s, kmswStage, kmswStep, kmswCodeStep, hc,
                  kmswStepOfStep, hu, State.addEdge]
              have heast : (kmswStage w (n + 1)).east (act w (n + 1)) = s.nextVertex := by
                simp [act, s, kmswStage, kmswStep, kmswCodeStep, hc,
                  kmswStepOfStep, hu, State.addEdge]
              have hvnew : v = s.nextVertex := by omega
              exact ⟨n + 1, le_rfl, Or.inr (by rw [heast, hvnew])⟩
          | cons e es =>
              have hnext : (kmswStage w (n + 1)).nextVertex = s.nextVertex := by
                simp [s, kmswStage, kmswStep, kmswCodeStep, hc,
                  kmswStepOfStep, hu]
              omega

/-- Every vertex allocated by a stage strictly before the first R-phase exit
is reachable from the global root. This follows from active-west reachability
through the first phase, and the fact that each new vertex is an endpoint of
the active edge at its allocation stage (`lem-flow-line-times`, -/
theorem quadrantFirstRStage_vertices_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : m < walkNL w h 0)
    (v : ℕ) (hv : v < (kmswStage w m).nextVertex) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩ := by
  obtain ⟨t, htm, hendpoint | hendpoint⟩ := allocatedVertex_activeEndpoint w m v hv
  · have ht : t < walkNL w h 0 := htm.trans_lt hm
    have hr := firstPhase_walkNL_reachable w h t ht
    simpa [hendpoint] using hr
  · have ht : t < walkNL w h 0 := htm.trans_lt hm
    have hr := firstPhase_walkNL_reachable w h t ht
    have he := kmswStage_activeEast_reachable w t hr
    simpa [hendpoint] using he

/-- Within the allocated stage prefix, the identity vertex map has exactly
the root-reachable vertices as its image during the first R phase. -/
theorem quadrantFirstRStage_vertex_image (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : m < walkNL w h 0) :
    Set.range (fun v : {v : ℕ // v < (kmswStage w m).nextVertex} => v.val) =
      {v | v < (kmswStage w m).nextVertex ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩} := by
  ext v
  constructor
  · rintro ⟨⟨v', hv'⟩, rfl⟩
    exact ⟨hv', quadrantFirstRStage_vertices_reachable w h hm v' hv'⟩
  · rintro ⟨hv, _⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-- Both endpoints of every edge allocated in the first R-phase stage are
root-reachable, including the geometric endpoints of missing edges. -/
theorem quadrantFirstRStage_edges_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : m < walkNL w h 0)
    (e : ℕ) (he : e < (kmswStage w m).nextEdge) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w m).west e⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w m).east e⟩ := by
  have hend := kmswStage_endpoints_lt_nextVertex w m e he
  exact ⟨quadrantFirstRStage_vertices_reachable w h hm _ hend.1,
    quadrantFirstRStage_vertices_reachable w h hm _ hend.2⟩

/-- The identity edge map has exactly the geometric edges of the global stage
whose two endpoints are root-reachable. Missing edges remain in this image
when their endpoints are reachable (`def-kmsw`, -/
theorem quadrantFirstRStage_edge_image (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {m : ℕ} (hm : m < walkNL w h 0) :
    Set.range (fun e : {e : ℕ // e < (kmswStage w m).nextEdge} => e.val) =
      {e | e < (kmswStage w m).nextEdge ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w m).west e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w m).east e⟩} := by
  ext e
  constructor
  · rintro ⟨⟨e', he'⟩, rfl⟩
    exact ⟨he', (quadrantFirstRStage_edges_reachable w h hm e' he').1,
      (quadrantFirstRStage_edges_reachable w h hm e' he').2⟩
  · rintro ⟨he, _, _⟩
    exact ⟨⟨e, he⟩, rfl⟩

private theorem runningMin_nonneg_of_prefix {f : ℕ → ℤ} :
    ∀ n, (∀ j ≤ n, 0 ≤ f j) → 0 ≤ runningMin f n := by
  intro n
  induction n with
  | zero =>
      intro hn
      simpa [runningMin] using hn 0 le_rfl
  | succ n ih =>
      intro hn
      have hprev : ∀ j ≤ n, 0 ≤ f j := by
        intro j hj
        exact hn j (by omega)
      rw [runningMin]
      exact le_min (ih hprev) (hn (n + 1) le_rfl)

/-- Immediately before the first horizontal exit, the active edge has no
upper-left predecessor. Thus the exit is the fresh-vertex gluing step from -/
theorem quadrantFirstR_exit_predecessor_emptyUL (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    0 < walkNL w h 0 ∧
      w (walkNL w h 0 - 1) = 0 ∧
      L w (walkNL w h 0 - 1) = 0 ∧
      (kmswStage w (walkNL w h 0 - 1)).UL.dropLast.reverse = [] := by
  let N := walkNL w h 0
  have hN := walkNL_spec w h 0
  have hNpos : 0 < N := by dsimp [N]; omega
  have hcode : w (N - 1) = 0 := by
    simpa [N] using walkNL_previous_code w h 0
  have hindex : N - 1 + 1 = N := by omega
  have hstep : L w N = L w (N - 1) - 1 := by
    have hs : L w ((N - 1) + 1) =
        L w (N - 1) + (lazyTwoDimensionalStep (w (N - 1))).1 := by
      simp only [L, Finset.sum_range_succ]
    rw [hindex] at hs
    rw [hcode, lazyTwoDimensionalStep_zero] at hs
    omega
  have hLexit : L w N = -1 := by
    have hspec := walkNL_spec w h 0
    have hNzero : walkNR w h 0 = 0 := walkNR_zero w h
    have hzero : L w 0 = 0 := by simp [L]
    have hh : L w (walkNL w h 0) = -1 := by rw [hspec.2, hNzero, hzero]; rfl
    simpa [N] using hh
  have hLprev : L w (N - 1) = 0 := by omega
  have hprefix : ∀ j ≤ N - 1, 0 ≤ L w j := by
    intro j hj
    have hjlt : j < N := by omega
    exact firstRPhase_L_nonneg_before_exit w h (by simpa [N] using hjlt)
  have hminlow : 0 ≤ minL w (N - 1) := by
    change 0 ≤ runningMin (L w) (N - 1)
    exact runningMin_nonneg_of_prefix (f := L w) (N - 1) hprefix
  have hminupper : minL w (N - 1) ≤ 0 := by
    have hh := runningMin_le (L w) (N - 1) 0 (by omega)
    change minL w (N - 1) ≤ L w 0 at hh
    simpa [L] using hh
  have hmin : minL w (N - 1) = 0 := le_antisymm hminupper hminlow
  have hlenInt := kmswStage_UL_length w (N - 1)
  rw [hLprev, hmin] at hlenInt
  have hlen : (kmswStage w (N - 1)).UL.length = 1 := by omega
  obtain ⟨es, hes⟩ := kmswStage_UL_last w (N - 1)
  have hlenEs : es.length = 0 := by
    rw [hes] at hlen
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  have hesNil : es = [] := List.length_eq_zero_iff.mp hlenEs
  have hUL : (kmswStage w (N - 1)).UL =
      [(kmswStage w (N - 1)).active] := by
    simp [hes, hesNil]
  have hempty : (kmswStage w (N - 1)).UL.dropLast.reverse = [] := by
    simp [hUL]
  exact ⟨hNpos, by simpa [N] using hcode, by simpa [N] using hLprev,
    by simpa [N] using hempty⟩

/-- The first exit step creates the gluing triangle from the old active edge,
the new active edge, and a geometrically allocated but missing edge. Its new
active west endpoint is fresh (`lem-flow-line-times` item (ii), -/
theorem quadrantFirstR_exit_gluingTriangle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    let N := walkNL w h 0
    let s := kmswStage w (N - 1)
    (kmswStage w N).triangles = s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)] ∧
      act w N = s.nextEdge ∧
      (kmswStage w N).west (act w N) = s.nextVertex ∧
      (kmswStage w N).west s.nextEdge = s.nextVertex ∧
      (kmswStage w N).east s.nextEdge = s.east s.active ∧
      (kmswStage w N).west (s.nextEdge + 1) = s.nextVertex ∧
      (kmswStage w N).east (s.nextEdge + 1) = s.west s.active ∧
      (kmswStage w N).present s.nextEdge = true ∧
      (kmswStage w N).present (s.nextEdge + 1) = false := by
  let N := walkNL w h 0
  let s := kmswStage w (N - 1)
  obtain ⟨hpos, hcode, hLprev, hUL⟩ :=
    quadrantFirstR_exit_predecessor_emptyUL w h
  have hNsucc : N - 1 + 1 = N := by dsimp [N]; omega
  have hcode' : w (N - 1) = 0 := by simpa [N] using hcode
  have hUL' : s.UL.dropLast.reverse = [] := by simpa [s, N] using hUL
  have hstep : kmswStage w N = kmswStepOfStep s .left := by
    rw [← hNsucc]
    change kmswStep s (w (N - 1)) = kmswStepOfStep s .left
    rw [hcode']
    rfl
  have htri : (kmswStage w N).triangles =
      s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)] := by
    rw [hstep]
    simp [kmswStepOfStep, hUL']
  have hactive : act w N = s.nextEdge := by
    change (kmswStage w N).active = s.nextEdge
    rw [hstep]
    simp [kmswStepOfStep, hUL']
  have hwestAct : (kmswStage w N).west (act w N) = s.nextVertex := by
    rw [hstep, hactive]
    simp [kmswStepOfStep, hUL', State.addEdge]
  have hwestNew : (kmswStage w N).west s.nextEdge = s.nextVertex := by
    rw [hstep]
    simp [kmswStepOfStep, hUL', State.addEdge]
  have heastNew : (kmswStage w N).east s.nextEdge = s.east s.active := by
    rw [hstep]
    simp [kmswStepOfStep, hUL', State.addEdge]
  have hwestMissing : (kmswStage w N).west (s.nextEdge + 1) = s.nextVertex := by
    rw [hstep]
    simp [kmswStepOfStep, hUL', State.addEdge]
  have heastMissing : (kmswStage w N).east (s.nextEdge + 1) = s.west s.active := by
    rw [hstep]
    simp [kmswStepOfStep, hUL', State.addEdge]
  have hpNew : (kmswStage w N).present s.nextEdge = true := by
    rw [hstep]
    simp [kmswStepOfStep, hUL', State.addEdge]
  have hpMissing : (kmswStage w N).present (s.nextEdge + 1) = false := by
    rw [hstep]
    simp [kmswStepOfStep, hUL', State.addEdge]
  exact ⟨htri, hactive, hwestAct, hwestNew, heastNew,
    hwestMissing, heastMissing, hpNew, hpMissing⟩

private theorem path_target_id_or_last_edge {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) :
    a.id = b.id ∨ ∃ e, e ∈ pathEdgeList p ∧ edgeEast w e = b.id := by
  induction p with
  | nil => exact Or.inl rfl
  | @cons a b p e _ =>
      right
      refine ⟨e.val, ?_, e.property.2.2⟩
      simp [pathEdgeList]

/-- The new active west vertex created by the first exit step is not reachable
from the global root. Every path into it would have to use an earlier active
edge, whose endpoints are among the vertices allocated before the exit -/
theorem quadrantFirstR_exit_activeWest_unreachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (walkNL w h 0)).west (act w (walkNL w h 0))⟩ := by
  let N := walkNL w h 0
  let s := kmswStage w (N - 1)
  have hglue := quadrantFirstR_exit_gluingTriangle w h
  have hfresh : (kmswStage w N).west (act w N) = s.nextVertex := by
    simpa [N, s] using hglue.2.2.1
  have hnot : s.nextVertex ∉ actReachableBefore w N := by
    intro hv
    change s.nextVertex = 0 ∨
      ∃ p : Path (⟨0⟩ : PresentVertex w) ⟨s.nextVertex⟩,
        ∀ e ∈ pathEdgeList p, ∃ j < N, e = act w j at hv
    rcases hv with hroot | ⟨p, hp⟩
    · have htwo : 2 ≤ s.nextVertex := by
        have hmono := CutConverse.nextVertex_mono w (Nat.zero_le (N - 1))
        simpa [s, kmswStage, kmswInit] using hmono
      omega
    · have htwo : 2 ≤ s.nextVertex := by
        have hmono := CutConverse.nextVertex_mono w (Nat.zero_le (N - 1))
        simpa [s, kmswStage, kmswInit] using hmono
      rcases path_target_id_or_last_edge p with hEq | ⟨e, he, htarget⟩
      · have hval : 0 = s.nextVertex := by simpa using hEq
        omega
      · obtain ⟨j, hj, hje⟩ := hp e he
        have hjle : j ≤ N - 1 := by omega
        have hact := act_lt_nextEdge w (Nat.le_refl j)
        have hend := kmswStage_endpoints_lt_nextVertex w j (act w j) hact
        have hstable := (edge_endpoints_eq w hact).2
        have heastlt : edgeEast w (act w j) < s.nextVertex := by
          calc
            edgeEast w (act w j) = (kmswStage w j).east (act w j) := hstable.symm
            _ < (kmswStage w j).nextVertex := hend.2
            _ ≤ s.nextVertex := by
              simpa [s] using CutConverse.nextVertex_mono w hjle
        have htarget' : edgeEast w (act w j) = s.nextVertex := by
          rw [← hje]
          exact htarget
        omega
  intro hr
  have hm := (actReachableBefore_activeWest_iff w N).2 hr
  have hm' : s.nextVertex ∈ actReachableBefore w N := by
    rw [← hfresh]
    exact hm
  exact hnot hm'

/-- At the terminal code included by `phaseSplit`, the raw R-run contains the
fresh exit vertex. Hence its identity image is no longer the root-reachable
part, even though the finite KMSW states still agree. -/
theorem quadrantFirstR_terminalCode_notInReachableImage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w))
          (walkNL w h 0)).west
        (act (quadrantRStageCodes (quadrantTrajectoryOfStageCodes w))
          (walkNL w h 0))⟩ := by
  let N := walkNL w h 0
  let u := quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
  have hstage : kmswStage u N = kmswStage w N :=
    quadrantFirstRStage_eq_through_exit w h le_rfl
  have hwest : (kmswStage u N).west (act u N) =
      (kmswStage w N).west (act w N) := by
    simpa [act] using congrArg (fun s : State => s.west s.active) hstage
  intro hr
  apply quadrantFirstR_exit_activeWest_unreachable w h
  rw [← hwest]
  exact hr

/-- In the first gluing triangle, the old active edge has reachable endpoints;
each new geometric edge has the fresh unreachable vertex as its west endpoint.
Thus the old edge is the part of the triangle retained by the reachable
induced submap (`lem-flow-line-times` item (ii), -/
theorem quadrantFirstR_exit_triangle_reachability (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    let N := walkNL w h 0
    let s := kmswStage w (N - 1)
    Reachable (⟨0⟩ : PresentVertex w) ⟨s.west s.active⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨s.east s.active⟩ ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w N).west (act w N)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w N).east (act w N)⟩ ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w N).west (s.nextEdge + 1)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w N).east (s.nextEdge + 1)⟩ := by
  let N := walkNL w h 0
  let s := kmswStage w (N - 1)
  have hNpos : 0 < N := by
    have := (walkNL_spec w h 0).1
    dsimp [N]
    omega
  have hpre : N - 1 < walkNL w h 0 := by dsimp [N]; omega
  have hOldWest : Reachable (⟨0⟩ : PresentVertex w) ⟨s.west s.active⟩ := by
    have hh := firstPhase_walkNL_reachable w h (N - 1) hpre
    simpa [s, N, act] using hh
  have hOldEast : Reachable (⟨0⟩ : PresentVertex w) ⟨s.east s.active⟩ := by
    have hh := firstPhase_walkNL_reachable w h (N - 1) hpre
    have he := kmswStage_activeEast_reachable w (N - 1) hh
    simpa [s, N, act] using he
  have hglue := quadrantFirstR_exit_gluingTriangle w h
  rcases hglue with ⟨_, hactive, hwestAct, _, heastNew,
      hwestMissing, heastMissing, _, _⟩
  have hnot := quadrantFirstR_exit_activeWest_unreachable w h
  have heastAct : (kmswStage w N).east (act w N) = s.east s.active := by
    rw [hactive, heastNew]
  have hmissingWest :
      (kmswStage w N).west (s.nextEdge + 1) =
        (kmswStage w N).west (act w N) := by
    rw [hwestMissing, hwestAct]
  exact ⟨hOldWest, hOldEast, hnot,
    by rw [heastAct]; exact hOldEast,
    by rw [hmissingWest]; exact hnot,
    by rw [heastMissing]; exact hOldWest⟩

/-- Immediately after the first gluing triangle, the upper-left boundary
contains only its new active edge. This is the boundary condition used by the
local left/up preservation lemma (`eqn-quad-pre2`, -/
theorem quadrantFirstR_exit_UL_singleton (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    let N := walkNL w h 0
    (kmswStage w N).UL = [act w N] := by
  let N := walkNL w h 0
  let s := kmswStage w (N - 1)
  obtain ⟨_, hcode, _, hUL⟩ := quadrantFirstR_exit_predecessor_emptyUL w h
  have hNsucc : N - 1 + 1 = N := by dsimp [N]; omega
  have hcode' : w (N - 1) = 0 := by simpa [N] using hcode
  have hUL' : s.UL.dropLast.reverse = [] := by simpa [s, N] using hUL
  have hstep : kmswStage w N = kmswStepOfStep s .left := by
    rw [← hNsucc]
    change kmswStep s (w (N - 1)) = kmswStepOfStep s .left
    rw [hcode']
    rfl
  have hactive : act w N = s.nextEdge :=
    (quadrantFirstR_exit_gluingTriangle w h).2.1
  change (kmswStage w N).UL = [act w N]
  rw [hstep, hactive]
  simp [kmswStepOfStep, hUL', State.addEdge]

private theorem actReachableBefore_lt_nextVertex (w : ℕ → Fin 3) (n : ℕ)
    {v : ℕ} (hv : v ∈ actReachableBefore w n) :
    v < (kmswStage w n).nextVertex := by
  rcases hv with hroot | ⟨p, hp⟩
  · subst v
    have hmono := CutConverse.nextVertex_mono w (Nat.zero_le n)
    have hinit : 2 ≤ (kmswStage w 0).nextVertex := by
      simp [kmswStage, kmswInit]
    omega
  · rcases path_target_id_or_last_edge p with hroot | ⟨e, he, htarget⟩
    · have hv0 : v = 0 := hroot.symm
      subst v
      have hmono := CutConverse.nextVertex_mono w (Nat.zero_le n)
      have hinit : 2 ≤ (kmswStage w 0).nextVertex := by
        simp [kmswStage, kmswInit]
      omega
    · obtain ⟨j, hj, hje⟩ := hp e he
      have hjn : j ≤ n := by omega
      have hact := act_lt_nextEdge w (Nat.le_refl j)
      have hstable := (edge_endpoints_eq w hact).2
      have hend := kmswStage_endpoints_lt_nextVertex w j (act w j) hact
      have htarget' : v = (kmswStage w j).east (act w j) := by
        calc
          v = edgeEast w e := htarget.symm
          _ = edgeEast w (act w j) := congrArg (edgeEast w) hje
          _ = (kmswStage w j).east (act w j) := hstable.symm
      have hmono := CutConverse.nextVertex_mono w hjn
      omega

/-- A left or up stage cannot extend the root-reachable vertex set from the
exit configuration: it leaves the active west vertex unreachable and keeps
the upper-left boundary a singleton. This isolates the part of the skipped
phase that follows directly from the local KMSW rules; down steps still need -/
theorem kmswLeftOrUp_preserves_unreachable_activeWest (w : ℕ → Fin 3)
    (n : ℕ) (hc : w n = 0 ∨ w n = 1)
    (hUL : (kmswStage w n).UL = [act w n])
    (hnot : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    actReachableBefore w (n + 1) = actReachableBefore w n ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ ∧
      (kmswStage w (n + 1)).UL = [act w (n + 1)] := by
  have hnotMem : (kmswStage w n).west (act w n) ∉ actReachableBefore w n := by
    intro hm
    exact hnot ((actReachableBefore_activeWest_iff w n).1 hm)
  have hset : actReachableBefore w (n + 1) = actReachableBefore w n := by
    rw [actReachableBefore_succ]
    simp [hnotMem]
  rcases hc with hleft | hup
  · have hwest := kmswStage_left_activeWest_eq w n hleft
    have hempty : (kmswStage w n).UL.dropLast.reverse = [] := by
      rw [hUL]
      rfl
    rw [hempty] at hwest
    have hnew : (kmswStage w (n + 1)).west (act w (n + 1)) =
        (kmswStage w n).nextVertex := hwest
    have hfresh : (kmswStage w n).nextVertex ∉ actReachableBefore w n := by
      intro hm
      have hbound := actReachableBefore_lt_nextVertex w n hm
      omega
    have hnotNext : (kmswStage w (n + 1)).west (act w (n + 1)) ∉
        actReachableBefore w (n + 1) := by
      rw [hset, hnew]
      exact hfresh
    have hULnext : (kmswStage w (n + 1)).UL = [act w (n + 1)] := by
      simp [act, kmswStage, kmswStep, kmswCodeStep, hleft,
        kmswStepOfStep, hempty, State.addEdge]
    refine ⟨hset, ?_, hULnext⟩
    intro hr
    exact hnotNext ((actReachableBefore_activeWest_iff w (n + 1)).2 hr)
  · have hwest : (kmswStage w (n + 1)).west (act w (n + 1)) =
        (kmswStage w n).west (act w n) := by
      simp [act, kmswStage, kmswStep, kmswCodeStep, hup,
        kmswStepOfStep, State.addEdge]
    have hnotNext : (kmswStage w (n + 1)).west (act w (n + 1)) ∉
        actReachableBefore w (n + 1) := by
      rw [hset, hwest]
      exact hnotMem
    have hULnext : (kmswStage w (n + 1)).UL = [act w (n + 1)] := by
      simp [act, kmswStage, kmswStep, kmswCodeStep, hup,
        kmswStepOfStep, hUL, State.addEdge]
    refine ⟨hset, ?_, hULnext⟩
    intro hr
    exact hnotNext ((actReachableBefore_activeWest_iff w (n + 1)).2 hr)

end DirectedDistances.KMSW
