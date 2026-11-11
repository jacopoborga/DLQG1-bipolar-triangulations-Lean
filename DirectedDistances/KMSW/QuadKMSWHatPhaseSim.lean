module

public import DirectedDistances.KMSW.QuadKMSWHatFlipped
public import DirectedDistances.KMSW.KMSWShiftAllTimes
import DirectedDistances.KMSW.StageSubgraph

/-! # Depth-limited simulation inside an R phase

Partial M-hat simulation helpers for `lem-quad-kmsw`, `eqn-quad-pre`, and
The predecessor prefix stops at the current phase floor. The UR stacks are
mapped exactly, so common steps have no down mismatch. This is not
`lem-quad-kmsw`, and does not identify `hatCodes` with `rCodeSequence`.

The all-stage assembly is in `QuadKMSWHatAllStages`. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped Classical

/-- Incidence simulation with exactly the first `d` nearest UL predecessors
identified. The depth bound makes a positive-depth left step consume an
actual predecessor. Exact UR matching rules out down mismatches. Helper for
`lem-quad-kmsw` and `eqn-quad-pre` -/
structure HatPhaseSim (sh gl : State) (eφ vφ : ℕ → ℕ) (d : ℕ) : Prop where
  incidenceSim : HatIncidenceSim sh gl eφ vφ
  depth_le : d ≤ sh.UL.dropLast.reverse.length
  ul_depth_prefix : (List.map eφ sh.UL.dropLast.reverse).take d =
    gl.UL.dropLast.reverse.take d
  ur_eq : List.map eφ sh.UR = gl.UR

/-- The splitter's height above its current R-stream minimum, measured before
reading a code. At an R entrance this is zero (`lem-flow-line-times`, -/
@[expose] def hatPhaseDepth (w : ℕ → Fin 3) (n : ℕ) : ℕ :=
  let s := quadrantSplitState (quadrantTrajectoryOfStageCodes w) n
  (s.rWalk.1 - s.rLMin).toNat

/-- The depth resets at every R entrance (`lem-flow-line-times`, -/
theorem hatPhaseDepth_at_walkNR (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    hatPhaseDepth w (walkNR w h k) = 0 := by
  have hm := (quadrantSplitState_at_walkNR (quadrantTrajectoryOfStageCodes w) h k).2.1
  change (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
    (walkNR w h k)).rLMin =
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
      (walkNR w h k)).rWalk.1 at hm
  simp [hatPhaseDepth, hm]

private def phaseTrim (s : State) (d : ℕ) : State :=
  { s with UL := (s.UL.dropLast.reverse.take d).reverse ++ [s.active] }

private theorem phaseTrim_pred (s : State) (d : ℕ) :
    (phaseTrim s d).UL.dropLast.reverse = s.UL.dropLast.reverse.take d := by
  simp [phaseTrim]

private theorem phaseTrim_sim {sh gl : State} {eφ vφ : ℕ → ℕ} {d : ℕ}
    (hs : HatPhaseSim sh gl eφ vφ d) : Sim (phaseTrim sh d) gl eφ vφ := by
  refine ⟨hs.incidenceSim.edge_bound, hs.incidenceSim.edge_injective,
    hs.incidenceSim.vertex_bound, hs.incidenceSim.vertex_injective,
    hs.incidenceSim.active, hs.incidenceSim.incidence,
    hs.incidenceSim.present, hs.incidenceSim.ur_prefix, ?_⟩
  rw [phaseTrim_pred, List.map_take, hs.ul_depth_prefix]
  exact List.take_prefix _ _

private theorem phaseTrim_sim_to_phase {sh gl : State} {eφ vφ : ℕ → ℕ} {d : ℕ}
    (hs : Sim (phaseTrim sh d) gl eφ vφ)
    (hd : d ≤ sh.UL.dropLast.reverse.length)
    (hur : sh.UR.length = gl.UR.length) : HatPhaseSim sh gl eφ vφ d := by
  refine ⟨⟨hs.edge_bound, hs.edge_injective, hs.vertex_bound, hs.vertex_injective,
    hs.active, hs.incidence, hs.present, hs.ur_prefix⟩, hd, ?_, ?_⟩
  · have hp := hs.ul_predecessors_prefix
    rw [phaseTrim_pred, List.map_take] at hp
    have heq := List.prefix_iff_eq_take.mp hp
    simpa only [List.length_take, List.length_map, Nat.min_eq_left hd] using heq
  · exact hs.ur_prefix.eq_of_length (by simpa [phaseTrim] using hur)

private theorem phaseTrim_up (s : State) (d : ℕ) :
    kmswStep (phaseTrim s d) 1 = phaseTrim (kmswStep s 1) d := by
  simp [phaseTrim, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  constructor
  · rfl
  constructor
  · rfl
  funext e
  by_cases h1 : e = s.nextEdge + 1 <;> by_cases h0 : e = s.nextEdge <;> simp [h1, h0]

private theorem phaseTrim_down (s : State) (d : ℕ)
    (hlast : ∃ xs, s.UL = xs ++ [s.active]) :
    kmswStep (phaseTrim s d) 2 = phaseTrim (kmswStep s 2) (d + 1) := by
  obtain ⟨xs, hx⟩ := hlast
  cases hur : s.UR <;>
    simp [phaseTrim, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge,
      hur, hx, List.reverse_append, List.append_assoc]

private theorem phaseTrim_left (s : State) (d a : ℕ) (as : List ℕ)
    (hp : s.UL.dropLast.reverse = a :: as) :
    kmswStep (phaseTrim s (d + 1)) 0 = phaseTrim (kmswStep s 0) d := by
  simp [phaseTrim, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge, hp]

private theorem stage_ur_bound (u : ℕ → Fin 3) (m : ℕ) :
    ∀ e ∈ (kmswStage u m).UR, e < (kmswStage u m).nextEdge := by
  intro e he
  apply (kmswStage_boundary_ids_lt_nextEdge u m).2
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr he))

private theorem stage_pred_bound (u : ℕ → Fin 3) (m : ℕ) :
    ∀ e ∈ (kmswStage u m).UL.dropLast.reverse,
      e < (kmswStage u m).nextEdge := by
  intro e he
  apply (kmswStage_boundary_ids_lt_nextEdge u m).2
  have hm : e ∈ (kmswStage u m).UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp he)
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl hm))

/-- A common up step preserves depth and the truncated simulation
within-phase helper, not a proof of the paper lemma. -/
theorem hatPhaseSim_step_up (u w : ℕ → Fin 3) (m n d : ℕ)
    (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage u m) (kmswStage w n) eφ vφ d) :
    HatPhaseSim (kmswStep (kmswStage u m) 1) (kmswStep (kmswStage w n) 1)
      (kmswShiftUpEdgeMap (kmswStage u m) (kmswStage w n) eφ)
      (kmswShiftUpVertexMap (kmswStage u m) (kmswStage w n) vφ) d := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  have hpred : ∀ e ∈ (phaseTrim sh d).UL.dropLast.reverse, e < sh.nextEdge := by
    intro e he
    rw [phaseTrim_pred] at he
    exact stage_pred_bound u m e (List.mem_of_mem_take he)
  have hh := kmswShiftSim_step_up (phaseTrim sh d) gl eφ vφ
    (act_lt_nextEdge u le_rfl) (kmswStage_endpoints_lt_nextVertex u m)
    (stage_ur_bound u m) hpred (phaseTrim_sim hs)
  rw [phaseTrim_up] at hh
  apply phaseTrim_sim_to_phase hh
  · simpa [kmswStep, kmswCodeStep, kmswStepOfStep] using hs.depth_le
  · have hl := congrArg List.length hs.ur_eq
    simpa [kmswStep, kmswCodeStep, kmswStepOfStep, List.length_map] using
      congrArg Nat.succ hl

/-- A matched down step increases depth by one. Exact UR matching includes
both the allocation and nonempty-stack cases, with no mismatch assumption -/
theorem hatPhaseSim_step_down (u w : ℕ → Fin 3) (m n d : ℕ)
    (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage u m) (kmswStage w n) eφ vφ d) :
    HatPhaseSim (kmswStep (kmswStage u m) 2) (kmswStep (kmswStage w n) 2)
      (kmswShiftNextEdgeMap (kmswStage u m) (kmswStage w n) .down eφ)
      (kmswShiftNextVertexMap (kmswStage u m) (kmswStage w n) .down vφ) (d + 1) := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  change HatPhaseSim (kmswStep sh 2) (kmswStep gl 2)
    (kmswShiftNextEdgeMap sh gl .down eφ)
    (kmswShiftNextVertexMap sh gl .down vφ) (d + 1)
  have hshlast := kmswStage_UL_last u m
  have hgllast := kmswStage_UL_last w n
  have htrimlast : ∃ xs, (phaseTrim sh d).UL = xs ++ [(phaseTrim sh d).active] :=
    ⟨_, rfl⟩
  have hpred : ∀ e ∈ (phaseTrim sh d).UL.dropLast.reverse, e < sh.nextEdge := by
    intro e he
    rw [phaseTrim_pred] at he
    exact stage_pred_bound u m e (List.mem_of_mem_take he)
  have hsim := phaseTrim_sim hs
  have hlen := congrArg List.length hs.ur_eq
  have hdepth : d + 1 ≤ (kmswStep sh 2).UL.dropLast.reverse.length := by
    obtain ⟨xs, hx⟩ := hshlast
    have hd := hs.depth_le
    change d ≤ sh.UL.dropLast.reverse.length at hd
    change sh.UL = _ at hx
    cases hur : sh.UR <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge, hur, hx] at * <;>
      omega
  cases hshUR : sh.UR with
  | nil =>
    have hglUR : gl.UR = [] := by simpa [sh, gl, hshUR] using hs.ur_eq.symm
    have hh := kmswShiftSim_step_down_empty (phaseTrim sh d) gl eφ vφ
      (act_lt_nextEdge u le_rfl) (kmswStage_endpoints_lt_nextVertex u m)
      hshUR hglUR htrimlast hgllast hpred hsim
    rw [phaseTrim_down sh d hshlast] at hh
    have hemap : kmswShiftFreshEdgeMap (phaseTrim sh d) gl eφ =
        kmswShiftFreshEdgeMap sh gl eφ := by
      unfold kmswShiftFreshEdgeMap phaseTrim
      rfl
    have hvmap : kmswShiftUpVertexMap (phaseTrim sh d) gl vφ =
        kmswShiftUpVertexMap sh gl vφ := by
      unfold kmswShiftUpVertexMap phaseTrim
      rfl
    rw [hemap, hvmap] at hh
    simpa only [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, hshUR, hglUR] using
      phaseTrim_sim_to_phase hh hdepth (by
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge, hshUR, hglUR])
  | cons a as =>
    have hglUR : gl.UR = eφ a :: List.map eφ as := by
      simpa [sh, gl, hshUR] using hs.ur_eq.symm
    have hh := kmswShiftSim_step_down_nonempty (phaseTrim sh d) gl eφ vφ
      ⟨a, as, hshUR⟩ htrimlast hgllast hsim
    rw [phaseTrim_down sh d hshlast] at hh
    simpa [kmswShiftNextEdgeMap, kmswShiftNextVertexMap, hshUR, hglUR] using
      phaseTrim_sim_to_phase hh hdepth (by
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hshUR, hglUR])

/-- A common left step at positive depth consumes one identified predecessor
and decreases depth by one (`lem-quad-kmsw`, `eqn-quad-pre`, -/
theorem hatPhaseSim_step_left (u w : ℕ → Fin 3) (m n d : ℕ)
    (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage u m) (kmswStage w n) eφ vφ (d + 1)) :
    HatPhaseSim (kmswStep (kmswStage u m) 0) (kmswStep (kmswStage w n) 0)
      (kmswShiftFreshEdgeMap (kmswStage u m) (kmswStage w n) eφ) vφ d := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  have hne : sh.UL.dropLast.reverse ≠ [] := by
    intro he
    have hd := hs.depth_le
    change d + 1 ≤ sh.UL.dropLast.reverse.length at hd
    simp [he] at hd
  obtain ⟨a, as, hp⟩ := List.exists_cons_of_ne_nil hne
  have hpred : ∀ e ∈ (phaseTrim sh (d + 1)).UL.dropLast.reverse,
      e < sh.nextEdge := by
    intro e he
    rw [phaseTrim_pred] at he
    exact stage_pred_bound u m e (List.mem_of_mem_take he)
  have htrimPred : ∃ e es, (phaseTrim sh (d + 1)).UL.dropLast.reverse = e :: es := by
    rw [phaseTrim_pred, hp]
    exact ⟨a, as.take d, rfl⟩
  have hh := kmswShiftSim_step_left_nonempty (phaseTrim sh (d + 1)) gl eφ vφ
    (act_lt_nextEdge u le_rfl) htrimPred hpred (stage_ur_bound u m) (phaseTrim_sim hs)
  rw [phaseTrim_left sh d a as hp] at hh
  have hglne : gl.UL.dropLast.reverse ≠ [] := by
    intro he
    have heq := hs.ul_depth_prefix
    change (List.map eφ sh.UL.dropLast.reverse).take (d + 1) =
      gl.UL.dropLast.reverse.take (d + 1) at heq
    simp [hp, he] at heq
  obtain ⟨b, bs, hgp⟩ := List.exists_cons_of_ne_nil hglne
  apply phaseTrim_sim_to_phase hh
  · have hd := hs.depth_le
    change d + 1 ≤ sh.UL.dropLast.reverse.length at hd
    simpa [kmswStep, kmswCodeStep, kmswStepOfStep, hp] using
      (show d ≤ as.length by simpa [hp] using hd)
  · have hl := congrArg List.length hs.ur_eq
    simpa [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge, hp, hgp,
      List.length_map] using hl

/-- Explicit edge map across an L excursion: old IDs are retained; if the
local down step allocates, its fresh edge maps to the global fresh edge -/
@[expose] noncomputable def hatExcursionEdgeMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : ℕ → ℕ :=
  let sh := kmswStage w (walkNL w h k - 1)
  let gl := kmswStage w (walkNR w h (k + 1) - 1)
  if sh.UR = [] then kmswShiftFreshEdgeMap sh gl id else id

/-- Explicit vertex map across an arbitrary L excursion, using the fresh global
vertex only when the local down step allocates (`lem-quad-kmsw`, -/
@[expose] noncomputable def hatExcursionVertexMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) : ℕ → ℕ :=
  let sh := kmswStage w (walkNL w h k - 1)
  let gl := kmswStage w (walkNR w h (k + 1) - 1)
  if sh.UR = [] then kmswShiftUpVertexMap sh gl id else id

private theorem hatExcursion_incidence_nonempty
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ)
    (hne : (kmswStage w (walkNL w h k - 1)).UR ≠ []) :
    HatIncidenceSim (kmswStep (kmswStage w (walkNL w h k - 1)) 2)
      (kmswStage w (walkNR w h (k + 1))) id id := by
  let u := walkNL w h k - 1
  let q := walkNR w h (k + 1) - 1
  let r := walkNR w h (k + 1)
  have hgap : walkNL w h k + 1 ≤ walkNR w h (k + 1) := (walkNR_succ_spec w h k).1
  have hpos := (walkNL_spec w h k).1
  have hur : u ≤ r := by dsimp [u, r]; omega
  have hr : q + 1 = r := by dsimp [q, r]; omega
  have hcode : w q = 2 := walkNR_succ_previous_code w h k
  obtain ⟨a, es, ha⟩ : ∃ a es, (kmswStage w u).UR = a :: es := by
    cases hx : (kmswStage w u).UR with
    | nil => exact (hne hx).elim
    | cons a es => exact ⟨a, es, rfl⟩
  have hqa : (kmswStage w q).UR = a :: es := (hatLPhase_right_boundary w h k).1.trans ha
  have hrstage : kmswStage w r = kmswStepOfStep (kmswStage w q) .down := by
    rw [← hr]
    change kmswStep (kmswStage w q) (w q) = _
    rw [hcode]
    rfl
  have hactive : (kmswStage w r).active = a := by rw [hrstage]; simp [kmswStepOfStep, hqa]
  have hglpres : (kmswStage w r).present a = true := by
    rw [hrstage]; simp [kmswStepOfStep, hqa]
  change HatIncidenceSim (kmswStepOfStep (kmswStage w u) .down) (kmswStage w r) id id
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have he' : e < (kmswStage w u).nextEdge := by simpa [kmswStepOfStep, ha] using he
    exact he'.trans_le (kmswStage_nextEdge_mono w hur)
  · intro e f _ _ heq
    exact heq
  · intro v hv
    have hv' : v < (kmswStage w u).nextVertex := by simpa [kmswStepOfStep, ha] using hv
    exact hv'.trans_le (CutConverse.nextVertex_mono w hur)
  · intro v z _ _ heq
    exact heq
  · simpa [kmswStepOfStep, ha] using hactive.symm
  · intro e he
    have he' : e < (kmswStage w u).nextEdge := by simpa [kmswStepOfStep, ha] using he
    simpa [kmswStepOfStep, ha] using kmswStage_endpoints_stable w hur he'
  · intro e he hp
    by_cases hea : e = a
    · simpa [hea] using hglpres
    · have he' : e < (kmswStage w u).nextEdge := by simpa [kmswStepOfStep, ha] using he
      have hp' : (kmswStage w u).present e = true := by
        simpa [kmswStepOfStep, ha, hea] using hp
      exact (present_mono w he' hp' r hur).2
  · rw [hrstage]
    simp [kmswStepOfStep, ha, hqa]

private theorem hatExcursion_incidence_empty
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ)
    (hnil : (kmswStage w (walkNL w h k - 1)).UR = []) :
    HatIncidenceSim (kmswStep (kmswStage w (walkNL w h k - 1)) 2)
      (kmswStage w (walkNR w h (k + 1)))
      (hatExcursionEdgeMap w h k) (hatExcursionVertexMap w h k) := by
  let u := walkNL w h k - 1
  let q := walkNR w h (k + 1) - 1
  let r := walkNR w h (k + 1)
  let sh := kmswStage w u
  let gl := kmswStage w q
  let ep := kmswShiftFreshEdgeMap sh gl id
  let vp := kmswShiftUpVertexMap sh gl id
  have hgap : walkNL w h k + 1 ≤ walkNR w h (k + 1) := (walkNR_succ_spec w h k).1
  have huq : u ≤ q := by dsimp [u, q]; omega
  have hur : u ≤ r := by dsimp [u, r]; omega
  have hr : q + 1 = r := by dsimp [q, r]; omega
  have hshUR : sh.UR = [] := hnil
  have hglUR : gl.UR = [] := (hatLPhase_right_boundary w h k).1.trans hnil
  have hEast : gl.east gl.active = sh.east sh.active := (hatLPhase_right_boundary w h k).2
  have hEdge : sh.nextEdge ≤ gl.nextEdge := kmswStage_nextEdge_mono w huq
  have hVertex : sh.nextVertex ≤ gl.nextVertex := CutConverse.nextVertex_mono w huq
  have hcode : w q = 2 := walkNR_succ_previous_code w h k
  have hrstage : kmswStage w r = kmswStepOfStep gl .down := by
    rw [← hr]
    change kmswStep gl (w q) = _
    rw [hcode]
    rfl
  have hmapsE : hatExcursionEdgeMap w h k = ep := by
    simp [hatExcursionEdgeMap, hnil, ep, sh, gl, u, q]
  have hmapsV : hatExcursionVertexMap w h k = vp := by
    simp [hatExcursionVertexMap, hnil, vp, sh, gl, u, q]
  rw [hmapsE, hmapsV]
  change HatIncidenceSim (kmswStepOfStep sh .down) (kmswStage w r) ep vp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hshUR, State.addEdge] at he
      omega
    rcases hc with hold | rfl
    · have hne : e ≠ sh.nextEdge := by omega
      have hb := hold.trans_le (kmswStage_nextEdge_mono w hur)
      simpa [ep, kmswShiftFreshEdgeMap, hne] using hb
    · simp [ep, kmswShiftFreshEdgeMap, hrstage, kmswStepOfStep, hglUR, State.addEdge]

  · intro e f he hf heq
    have he' : e ≤ sh.nextEdge := by simpa [kmswStepOfStep, hshUR, State.addEdge] using he
    have hf' : f ≤ sh.nextEdge := by simpa [kmswStepOfStep, hshUR, State.addEdge] using hf
    by_cases hen : e = sh.nextEdge <;> by_cases hfn : f = sh.nextEdge
    · omega
    · simp [ep, kmswShiftFreshEdgeMap, hen, hfn] at heq
      omega
    · simp [ep, kmswShiftFreshEdgeMap, hen, hfn] at heq
      omega
    · simpa [ep, kmswShiftFreshEdgeMap, hen, hfn] using heq
  · intro v hv
    have hc : v < sh.nextVertex ∨ v = sh.nextVertex := by
      simp only [kmswStepOfStep, hshUR, State.addEdge] at hv
      omega
    rcases hc with hold | rfl
    · have hne : v ≠ sh.nextVertex := by omega
      have hb := hold.trans_le (CutConverse.nextVertex_mono w hur)
      simpa [vp, kmswShiftUpVertexMap, hne] using hb
    · simp [vp, kmswShiftUpVertexMap, hrstage, kmswStepOfStep, hglUR, State.addEdge]
  · intro v z hv hz heq
    have hv' : v ≤ sh.nextVertex := by simpa [kmswStepOfStep, hshUR, State.addEdge] using hv
    have hz' : z ≤ sh.nextVertex := by simpa [kmswStepOfStep, hshUR, State.addEdge] using hz
    by_cases hvn : v = sh.nextVertex <;> by_cases hzn : z = sh.nextVertex
    · omega
    · simp [vp, kmswShiftUpVertexMap, hvn, hzn] at heq
      omega
    · simp [vp, kmswShiftUpVertexMap, hvn, hzn] at heq
      omega
    · simpa [vp, kmswShiftUpVertexMap, hvn, hzn] using heq
  · simp [kmswStepOfStep, hshUR, hrstage, hglUR, ep, kmswShiftFreshEdgeMap]
  · intro e he
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hshUR, State.addEdge] at he
      omega
    rcases hc with hold | rfl
    · have hne : e ≠ sh.nextEdge := by omega
      have hends := kmswStage_endpoints_lt_nextVertex w u e hold
      have hw : sh.west e ≠ sh.nextVertex := by exact ne_of_lt hends.1
      have he' : sh.east e ≠ sh.nextVertex := by exact ne_of_lt hends.2
      simpa [ep, vp, kmswShiftFreshEdgeMap, kmswShiftUpVertexMap,
        kmswStepOfStep, hshUR, State.addEdge, hne, hw, he'] using
        kmswStage_endpoints_stable w hur hold
    · have hae := (kmswStage_endpoints_lt_nextVertex w u sh.active
        (act_lt_nextEdge w (Nat.le_refl u))).2
      have hvne : sh.east sh.active ≠ sh.nextVertex := ne_of_lt hae
      constructor
      · simpa [ep, vp, kmswShiftFreshEdgeMap, kmswShiftUpVertexMap,
          kmswStepOfStep, hshUR, hglUR, State.addEdge, hrstage, hvne] using hEast
      · simp [ep, vp, kmswShiftFreshEdgeMap, kmswShiftUpVertexMap,
          kmswStepOfStep, hshUR, hglUR, State.addEdge, hrstage]
  · intro e he hp
    have hc : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp only [kmswStepOfStep, hshUR, State.addEdge] at he
      omega
    rcases hc with hold | rfl
    · have hne : e ≠ sh.nextEdge := by omega
      have hp' : sh.present e = true := by
        simpa [kmswStepOfStep, hshUR, State.addEdge, hne] using hp
      simpa [ep, kmswShiftFreshEdgeMap, hne] using (present_mono w hold hp' r hur).2
    · simp [ep, kmswShiftFreshEdgeMap, hrstage, kmswStepOfStep, hglUR, State.addEdge]
  · simp [kmswStepOfStep, hshUR, State.addEdge]

/-- Incidence embedding across any L excursion, using the arriving down
code at the pre-exit state. Partial helper for `lem-quad-kmsw` and -/
theorem hatExcursion_incidenceSim (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    HatIncidenceSim (kmswStep (kmswStage w (walkNL w h k - 1)) 2)
      (kmswStage w (walkNR w h (k + 1)))
      (hatExcursionEdgeMap w h k) (hatExcursionVertexMap w h k) := by
  by_cases hnil : (kmswStage w (walkNL w h k - 1)).UR = []
  · exact hatExcursion_incidence_empty w h k hnil
  · have hmE : hatExcursionEdgeMap w h k = id := by
      simp [hatExcursionEdgeMap, hnil]
    have hmV : hatExcursionVertexMap w h k = id := by
      simp [hatExcursionVertexMap, hnil]
    rw [hmE, hmV]
    exact hatExcursion_incidence_nonempty w h k hnil

private theorem incidence_comp {s t r : State} {e₁ v₁ e₂ v₂ : ℕ → ℕ}
    (h₁ : HatIncidenceSim s t e₁ v₁) (h₂ : HatIncidenceSim t r e₂ v₂) :
    HatIncidenceSim s r (e₂ ∘ e₁) (v₂ ∘ v₁) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact h₂.edge_bound _ (h₁.edge_bound _ he)
  · intro e f he hf hef
    exact h₁.edge_injective e f he hf
      (h₂.edge_injective _ _ (h₁.edge_bound _ he) (h₁.edge_bound _ hf) hef)
  · intro v hv
    exact h₂.vertex_bound _ (h₁.vertex_bound _ hv)
  · intro v z hv hz hvz
    exact h₁.vertex_injective v z hv hz
      (h₂.vertex_injective _ _ (h₁.vertex_bound _ hv) (h₁.vertex_bound _ hz) hvz)
  · change e₂ (e₁ s.active) = r.active
    rw [h₁.active, h₂.active]
  · intro e he
    have hinc := h₂.incidence _ (h₁.edge_bound _ he)
    have hinc₁ := h₁.incidence e he
    exact ⟨hinc.1.trans (congrArg v₂ hinc₁.1),
      hinc.2.trans (congrArg v₂ hinc₁.2)⟩
  · intro e he hp
    exact h₂.present _ (h₁.edge_bound _ he) (h₁.present e he hp)
  · simpa only [List.map_map] using (h₁.ur_prefix.map e₂).trans h₂.ur_prefix

/-- Every replaced exit advances a preceding depth-zero simulation across the
whole L excursion and resets to depth zero. The maps are explicit compositions
of the common down-step and excursion maps. Partial M-hat simulation for
`lem-quad-kmsw`, `eqn-quad-pre`, `lem-flow-line-times` -/
theorem hatPhaseSim_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ)
    (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage (hatCodes w h) (hatExitIndex w h k))
      (kmswStage w (walkNL w h k - 1)) eφ vφ 0) :
    HatPhaseSim (kmswStage (hatCodes w h) (hatExitIndex w h k + 1))
      (kmswStage w (walkNR w h (k + 1)))
      (hatExcursionEdgeMap w h k ∘
        kmswShiftNextEdgeMap (kmswStage (hatCodes w h) (hatExitIndex w h k))
          (kmswStage w (walkNL w h k - 1)) .down eφ)
      (hatExcursionVertexMap w h k ∘
        kmswShiftNextVertexMap (kmswStage (hatCodes w h) (hatExitIndex w h k))
          (kmswStage w (walkNL w h k - 1)) .down vφ) 0 := by
  have hd := hatPhaseSim_step_down (hatCodes w h) w (hatExitIndex w h k)
    (walkNL w h k - 1) 0 eφ vφ hs
  have hj := hatExcursion_incidenceSim w h k
  have hi := incidence_comp hd.incidenceSim hj
  have hlocal : kmswStage (hatCodes w h) (hatExitIndex w h k + 1) =
      kmswStep (kmswStage (hatCodes w h) (hatExitIndex w h k)) 2 := by
    rw [kmswStage, hatCodes_at_exit]
  rw [hlocal]
  refine ⟨hi, Nat.zero_le _, by simp, ?_⟩
  apply hi.ur_prefix.eq_of_length
  simp only [List.length_map]
  have hgap := (walkNR_succ_spec w h k).1
  have hr : walkNR w h (k + 1) - 1 + 1 = walkNR w h (k + 1) := by omega
  have hb := (hatLPhase_right_boundary w h k).1
  have hc := walkNR_succ_previous_code w h k
  have hlen := congrArg List.length hs.ur_eq
  rw [← hr, kmswStage, hc]
  cases hl : (kmswStage (hatCodes w h) (hatExitIndex w h k)).UR <;>
    cases hg : (kmswStage w (walkNL w h k - 1)).UR <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge, hl, hb, hg,
        List.length_map] at *; omega

private theorem split_rMin_le (ω : ℕ → Fin 3) (n : ℕ) :
    (quadrantSplitState ω n).rLMin ≤ (quadrantSplitState ω n).rWalk.1 := by
  induction n with
  | zero => simp [quadrantSplitState, quadrantSplitStart]
  | succ n ih =>
    rw [quadrantSplitState]
    cases hp : (quadrantSplitState ω n).phase with
    | r =>
      simp only [quadrantSplitAdvance, hp]
      split_ifs <;> simp_all
    | l => simpa only [quadrantSplitAdvance, hp] using ih

/-- A left code in an R phase exits exactly when its current depth is zero
(`lem-flow-line-times`, `eqn-quad-pre`, -/
theorem hatPhaseDepth_left_exit_iff (w : ℕ → Fin 3) (n : ℕ)
    (hp : (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .r)
    (hc : w n = 0) :
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w) (n + 1)).phase = .l ↔
      hatPhaseDepth w n = 0 := by
  have hm := split_rMin_le (quadrantTrajectoryOfStageCodes w) n
  simp only [quadrantSplitState, quadrantTrajectoryOfStageCodes,
    quadrantSplitAdvance, hp, hc, lazyTwoDimensionalStep_zero,
    Prod.fst_add, Int.reduceNeg, hatPhaseDepth]
  split_ifs <;> simp_all

/-- Within an R phase, left lowers depth by one, up preserves it, and down
raises it by one (`lem-flow-line-times`, `eqn-quad-pre`, -/
theorem hatPhaseDepth_step (w : ℕ → Fin 3) (n : ℕ)
    (hp : (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .r)
    (hn : (quadrantSplitState (quadrantTrajectoryOfStageCodes w) (n + 1)).phase = .r) :
    hatPhaseDepth w (n + 1) =
      if w n = 0 then hatPhaseDepth w n - 1
      else if w n = 1 then hatPhaseDepth w n else hatPhaseDepth w n + 1 := by
  let s := quadrantSplitState (quadrantTrajectoryOfStageCodes w) n
  have hm : s.rLMin ≤ s.rWalk.1 := split_rMin_le _ _
  have hnext : (quadrantSplitAdvance s (w n)).phase = .r := hn
  have hno : ¬ s.rWalk.1 + (lazyTwoDimensionalStep (w n)).1 < s.rLMin := by
    intro hh
    simp [quadrantSplitAdvance, show s.phase = .r from hp, hh] at hnext
  have hd : hatPhaseDepth w (n + 1) =
      (s.rWalk.1 + (lazyTwoDimensionalStep (w n)).1 - s.rLMin).toNat := by
    simp [hatPhaseDepth, quadrantSplitState, quadrantTrajectoryOfStageCodes,
      quadrantSplitAdvance, hp, s, hno]
  rw [hd]
  change _ = if w n = 0 then (s.rWalk.1 - s.rLMin).toNat - 1
    else if w n = 1 then (s.rWalk.1 - s.rLMin).toNat
    else (s.rWalk.1 - s.rLMin).toNat + 1
  generalize hc : w n = c at *
  fin_cases c <;> simp [lazyTwoDimensionalStep] at * <;> omega

/-- A non-exit hatted code advances one global step within its R phase,
with the standard explicit next maps and the splitter's actual next depth.
No global UL-prefix or mismatch premise is required. Partial helper for
`lem-quad-kmsw`, `eqn-quad-pre`, `lem-flow-line-times` -/
theorem hatPhaseSim_step (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (hm : ¬ ∃ k, hatExitIndex w h k = m) (eφ vφ : ℕ → ℕ)
    (hs : HatPhaseSim (kmswStage (hatCodes w h) m)
      (kmswStage w (quadrantRStageTime w h m)) eφ vφ
      (hatPhaseDepth w (quadrantRStageTime w h m))) :
    HatPhaseSim (kmswStage (hatCodes w h) (m + 1))
      (kmswStage w (quadrantRStageTime w h (m + 1)))
      (kmswShiftNextEdgeMap (kmswStage (hatCodes w h) m)
        (kmswStage w (quadrantRStageTime w h m)) (kmswCodeStep (hatCodes w h m)) eφ)
      (kmswShiftNextVertexMap (kmswStage (hatCodes w h) m)
        (kmswStage w (quadrantRStageTime w h m)) (kmswCodeStep (hatCodes w h m)) vφ)
      (hatPhaseDepth w (quadrantRStageTime w h (m + 1))) := by
  let n := quadrantRStageTime w h m
  have ht : quadrantRStageTime w h (m + 1) = n + 1 := by
    rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hm]
  have hp := (quadrantRStageTime_spec w h m).1
  have hn := (quadrantRStageTime_spec w h (m + 1)).1
  rw [ht] at hn
  have hc : hatCodes w h m = w n := by
    rw [hatCodes, hatCodeTime_of_not_exit w h m hm]
  have hd := hatPhaseDepth_step w n hp hn
  rw [ht, kmswStage, hc]
  change HatPhaseSim (kmswStep (kmswStage (hatCodes w h) m) (w n))
    (kmswStep (kmswStage w n) (w n))
    (kmswShiftNextEdgeMap (kmswStage (hatCodes w h) m) (kmswStage w n)
      (kmswCodeStep (w n)) eφ)
    (kmswShiftNextVertexMap (kmswStage (hatCodes w h) m) (kmswStage w n)
      (kmswCodeStep (w n)) vφ) (hatPhaseDepth w (n + 1))
  by_cases h0 : w n = 0
  · have hpos : hatPhaseDepth w n ≠ 0 := by
      intro hz
      have he := (hatPhaseDepth_left_exit_iff w n hp h0).2 hz
      rw [hn] at he
      contradiction
    obtain ⟨d, he⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hs' := hs
    change HatPhaseSim _ _ _ _ (hatPhaseDepth w n) at hs'
    rw [he] at hs'
    have hh := hatPhaseSim_step_left (hatCodes w h) w m n d eφ vφ hs'
    cases hpred : (kmswStage (hatCodes w h) m).UL.dropLast.reverse with
    | nil =>
      have hb := hs'.depth_le
      simp [hpred] at hb
    | cons a as =>
      simpa [h0, hd, he, kmswCodeStep, kmswShiftNextEdgeMap,
        kmswShiftNextVertexMap, hpred] using hh
  · by_cases h1 : w n = 1
    · simpa [h0, h1, hd, kmswCodeStep, kmswShiftNextEdgeMap,
        kmswShiftNextVertexMap] using
        hatPhaseSim_step_up (hatCodes w h) w m n (hatPhaseDepth w n) eφ vφ hs
    · have h2 : w n = 2 := by
        have hb := (w n).isLt
        have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
        have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
        apply Fin.ext
        omega
      simpa [h0, h1, h2, hd, kmswCodeStep] using
        hatPhaseSim_step_down (hatCodes w h) w m n (hatPhaseDepth w n) eφ vφ hs



end DirectedDistances.KMSW
