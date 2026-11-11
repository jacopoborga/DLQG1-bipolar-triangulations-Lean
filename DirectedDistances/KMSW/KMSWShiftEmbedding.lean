module

public import DirectedDistances.KMSW.KMSWShift
import Mathlib.Data.List.Infix

/-! # Embedding a shifted KMSW run into a global run

The simulation tracks allocation, incidence, presence, and the two stacks
whose heads determine future updates in `def-kmsw`
not asserted to map into the global lower-right list: already at the initial
shifted state, its root maps to the global active edge, which need not be in
the global lower-right list. -/

public section
namespace DirectedDistances.KMSW

/-- A state-level simulation of the shifted and global `def-kmsw` runs
nearest-first shifted `UL.dropLast` stack are prefixes of their global
counterparts. These are the stack directions used by the down and left step
definitions. -/
structure Sim (sh gl : State) (eφ vφ : ℕ → ℕ) : Prop where
  edge_bound : ∀ e, e < sh.nextEdge → eφ e < gl.nextEdge
  edge_injective : ∀ e f, e < sh.nextEdge → f < sh.nextEdge →
    eφ e = eφ f → e = f
  vertex_bound : ∀ v, v < sh.nextVertex → vφ v < gl.nextVertex
  vertex_injective : ∀ v z, v < sh.nextVertex → z < sh.nextVertex →
    vφ v = vφ z → v = z
  active : eφ sh.active = gl.active
  incidence : ∀ e, e < sh.nextEdge →
    gl.west (eφ e) = vφ (sh.west e) ∧ gl.east (eφ e) = vφ (sh.east e)
  present : ∀ e, e < sh.nextEdge → sh.present e = true →
    gl.present (eφ e) = true
  ur_prefix : List.map eφ sh.UR <+: gl.UR
  ul_predecessors_prefix : List.map eφ (sh.UL.dropLast.reverse) <+:
    gl.UL.dropLast.reverse

/-- Edge map for the shifted root, regarded as a map on natural edge IDs. -/
@[expose] def kmswShiftRootEdgeNatMap (w : ℕ → Fin 3) (t : ℕ) : ℕ → ℕ :=
  fun _ => act w t

/-- Vertex map for the shifted root, regarded as a map on natural vertex IDs.
Only the two allocated root vertices are relevant. -/
@[expose] def kmswShiftRootVertexNatMap (w : ℕ → Fin 3) (t : ℕ) : ℕ → ℕ :=
  fun v =>
    if v = 0 then (kmswShiftRootVertexMap w t ⟨0, by omega⟩).val
    else if v = 1 then (kmswShiftRootVertexMap w t ⟨1, by omega⟩).val
    else 0

/-- The root embedding from `KMSWShift` satisfies the simulation at shifted -/
theorem kmswShiftSim_init (w : ℕ → Fin 3) (t : ℕ) :
    Sim kmswInit (kmswStage w t)
      (kmswShiftRootEdgeNatMap w t) (kmswShiftRootVertexNatMap w t) := by
  let eφ := kmswShiftRootEdgeNatMap w t
  let vφ := kmswShiftRootVertexNatMap w t
  have hact : act w t < (kmswStage w t).nextEdge :=
    act_lt_nextEdge w (Nat.le_refl t)
  have hactStage : (kmswStage w t).active < (kmswStage w t).nextEdge := by
    simpa [act] using hact
  have hend := kmswStage_endpoints_lt_nextVertex w t
    (kmswStage w t).active hactStage
  have hactiveMem : (kmswStage w t).active ∈ (kmswStage w t).UL := by
    obtain ⟨xs, hx⟩ := kmswStage_UL_last w t
    rw [hx]
    simp
  have hactivePresent := (kmswStage_status w t).2.1 _ hactiveMem
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
    have he0 : e = 0 := by simp [kmswInit] at he ⊢; omega
    subst e
    simpa [eφ, kmswShiftRootEdgeNatMap] using hact
  · intro e f he hf hef
    have he0 : e = 0 := by simp [kmswInit] at he; omega
    have hf0 : f = 0 := by simp [kmswInit] at hf; omega
    omega
  · intro v hv
    have hvCases : v = 0 ∨ v = 1 := by simp [kmswInit] at hv; omega
    rcases hvCases with hv0 | hv1
    · subst v
      simpa [vφ, kmswShiftRootVertexNatMap, kmswShiftRootVertexMap] using hend.1
    · subst v
      simpa [vφ, kmswShiftRootVertexNatMap, kmswShiftRootVertexMap] using hend.2
  · intro v z hv hz hvz
    have hvCases : v = 0 ∨ v = 1 := by simp [kmswInit] at hv; omega
    have hzCases : z = 0 ∨ z = 1 := by simp [kmswInit] at hz; omega
    rcases hvCases with hv0 | hv1 <;> rcases hzCases with hz0 | hz1
    · subst v; subst z; rfl
    · subst v; subst z
      have heqVal :
          (kmswShiftRootVertexMap w t ⟨0, by omega⟩).val =
            (kmswShiftRootVertexMap w t ⟨1, by omega⟩).val := by
        simpa [vφ, kmswShiftRootVertexNatMap] using hvz
      have heqFin : kmswShiftRootVertexMap w t ⟨0, by omega⟩ =
          kmswShiftRootVertexMap w t ⟨1, by omega⟩ := Fin.ext heqVal
      have hidx := kmswShiftRootVertexMap_injective w t heqFin
      have : (0 : ℕ) = 1 := congrArg Fin.val hidx
      omega
    · subst v; subst z
      have heqVal :
          (kmswShiftRootVertexMap w t ⟨1, by omega⟩).val =
            (kmswShiftRootVertexMap w t ⟨0, by omega⟩).val := by
        simpa [vφ, kmswShiftRootVertexNatMap] using hvz
      have heqFin : kmswShiftRootVertexMap w t ⟨1, by omega⟩ =
          kmswShiftRootVertexMap w t ⟨0, by omega⟩ := Fin.ext heqVal
      have hidx := kmswShiftRootVertexMap_injective w t heqFin
      have : (1 : ℕ) = 0 := congrArg Fin.val hidx
      omega
    · subst v; subst z; rfl
  · change act w t = (kmswStage w t).active
    rfl
  · intro e he
    have he0 : e = 0 := by simp [kmswInit] at he; omega
    subst e
    have hi := kmswShiftRoot_incidence w t
    constructor
    · simpa [eφ, kmswShiftRootEdgeNatMap, kmswShiftRootEdgeMap,
        vφ, kmswShiftRootVertexNatMap, kmswInit] using hi.1
    · simpa [eφ, kmswShiftRootEdgeNatMap, kmswShiftRootEdgeMap,
        vφ, kmswShiftRootVertexNatMap, kmswInit] using hi.2
  · intro e he hp
    have he0 : e = 0 := by simp [kmswInit] at he; omega
    subst e
    simpa [eφ, kmswShiftRootEdgeNatMap, act] using hactivePresent
  · simp [kmswInit]
  · simp [kmswInit]

/-- Edge-map update for an up step, which allocates an active edge followed
by a missing upper-right edge on both sides. -/
@[expose] def kmswShiftUpEdgeMap (sh gl : State) (eφ : ℕ → ℕ) : ℕ → ℕ :=
  fun e => if e = sh.nextEdge then gl.nextEdge
    else if e = sh.nextEdge + 1 then gl.nextEdge + 1 else eφ e

/-- Vertex-map update for an up step, which allocates one fresh vertex on
both sides. -/
@[expose] def kmswShiftUpVertexMap (sh gl : State) (vφ : ℕ → ℕ) : ℕ → ℕ :=
  fun v => if v = sh.nextVertex then gl.nextVertex else vφ v

/-- The up-code case of one-step simulation. The auxiliary bounds are the
finite-stage facts that allocated edges have allocated endpoints and that
the two control stacks contain allocated edge IDs -/
theorem kmswShiftSim_step_up (sh gl : State) (eφ vφ : ℕ → ℕ)
    (hshActive : sh.active < sh.nextEdge)
    (hshEndpoints : ∀ e, e < sh.nextEdge →
      sh.west e < sh.nextVertex ∧ sh.east e < sh.nextVertex)
    (hshUR : ∀ e ∈ sh.UR, e < sh.nextEdge)
    (hshUL : ∀ e ∈ sh.UL.dropLast.reverse, e < sh.nextEdge)
    (hsim : Sim sh gl eφ vφ) :
    Sim (kmswStep sh 1) (kmswStep gl 1)
      (kmswShiftUpEdgeMap sh gl eφ) (kmswShiftUpVertexMap sh gl vφ) := by
  change Sim (kmswStepOfStep sh .up) (kmswStepOfStep gl .up)
    (kmswShiftUpEdgeMap sh gl eφ) (kmswShiftUpVertexMap sh gl vφ)
  let eψ := kmswShiftUpEdgeMap sh gl eφ
  let vψ := kmswShiftUpVertexMap sh gl vφ
  have hnewActiveInc := hsim.incidence sh.active hshActive
  rw [hsim.active] at hnewActiveInc
  have hwestActive := hshEndpoints sh.active hshActive
  have heastActive := hshEndpoints sh.active hshActive
  have hmapUR : List.map eψ sh.UR = List.map eφ sh.UR := by
    apply List.map_congr_left
    intro e he
    have hb := hshUR e he
    have hne0 : e ≠ sh.nextEdge := by omega
    have hne1 : e ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftUpEdgeMap, hne0, hne1]
  have hmapUL : List.map eψ (sh.UL.dropLast.reverse) =
      List.map eφ (sh.UL.dropLast.reverse) := by
    apply List.map_congr_left
    intro e he
    have hb := hshUL e he
    have hne0 : e ≠ sh.nextEdge := by omega
    have hne1 : e ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftUpEdgeMap, hne0, hne1]
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
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp only [kmswStepOfStep, State.addEdge] at he
      omega
    rcases heOld with heOld | he0 | he1
    · have hbound := hsim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      have hpost : eφ e < (kmswStepOfStep gl .up).nextEdge := by
        simp [kmswStepOfStep, State.addEdge]
        omega
      simpa [eψ, kmswShiftUpEdgeMap, hne0, hne1] using hpost
    · subst e
      simp [kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap]
    · subst e
      simp [kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap]
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
      exact hsim.edge_injective e f heOld hfOld heq
    · subst f
      have hbound := hsim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst f
      have hbound := hsim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e
      have hbound := hsim.edge_bound f hfOld
      have hne0 : f ≠ sh.nextEdge := by omega
      have hne1 : f ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e; subst f; rfl
    · subst e; subst f
      simp [kmswShiftUpEdgeMap] at hef
    · subst e
      have hbound := hsim.edge_bound f hfOld
      have hne0 : f ≠ sh.nextEdge := by omega
      have hne1 : f ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e; subst f
      simp [kmswShiftUpEdgeMap] at hef
    · subst e; subst f; rfl
  · intro v hv
    have hvOld : v < sh.nextVertex ∨ v = sh.nextVertex := by
      simp only [kmswStepOfStep, State.addEdge] at hv
      omega
    rcases hvOld with hvOld | hvNew
    · have hbound := hsim.vertex_bound v hvOld
      have hne : v ≠ sh.nextVertex := by omega
      simpa [kmswStepOfStep, State.addEdge, vψ,
        kmswShiftUpVertexMap, hne] using Nat.lt_succ_of_lt hbound
    · subst v
      simp [kmswStepOfStep, State.addEdge, kmswShiftUpVertexMap]
  · intro v z hv hz hvz
    have hclass (x : ℕ) (hx : x < sh.nextVertex + 1) :
        x < sh.nextVertex ∨ x = sh.nextVertex := by omega
    rcases hclass v hv with hvOld | hvNew <;>
      rcases hclass z hz with hzOld | hzNew
    · have hneV : v ≠ sh.nextVertex := by omega
      have hneZ : z ≠ sh.nextVertex := by omega
      have heq : vφ v = vφ z := by
        simpa [vψ, kmswShiftUpVertexMap, hneV, hneZ] using hvz
      exact hsim.vertex_injective v z hvOld hzOld heq
    · subst z
      have hbound := hsim.vertex_bound v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      simp [kmswShiftUpVertexMap, hneV] at hvz
      omega
    · subst v
      have hbound := hsim.vertex_bound z hzOld
      have hneZ : z ≠ sh.nextVertex := by omega
      simp [kmswShiftUpVertexMap, hneZ] at hvz
      omega
    · subst v; subst z; rfl
  · simp [kmswStepOfStep, kmswShiftUpEdgeMap]
  · intro e he
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp only [kmswStepOfStep, State.addEdge] at he
      omega
    rcases heOld with heOld | he0 | he1
    · have hbound := hsim.edge_bound e heOld
      have hinc := hsim.incidence e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      have hng0 : eφ e ≠ gl.nextEdge := by omega
      have hng1 : eφ e ≠ gl.nextEdge + 1 := by omega
      have hvw := (hshEndpoints e heOld).1
      have hve := (hshEndpoints e heOld).2
      have hnewVW : sh.west e ≠ sh.nextVertex := by omega
      have hnewVE : sh.east e ≠ sh.nextVertex := by omega
      constructor
      · simpa [kmswStepOfStep, State.addEdge, eψ, vψ,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap, hne0, hne1, hng0, hng1,
          hnewVW]
          using hinc.1
      · simpa [kmswStepOfStep, State.addEdge, eψ, vψ,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap, hne0, hne1, hng0, hng1,
          hnewVE]
          using hinc.2
    · subst e
      have hvwest := hwestActive.1
      have hveast := hwestActive.2
      have hvwNew : sh.west sh.active < sh.nextVertex := hvwest
      have hveNew : sh.east sh.active < sh.nextVertex := hveast
      constructor
      · simpa [kmswStepOfStep, State.addEdge,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap, hsim.active,
          ne_of_lt hvwNew] using
          hnewActiveInc.1
      · simp [kmswStepOfStep, State.addEdge,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap]
    · subst e
      have hvwest := hwestActive.1
      have hveast := hwestActive.2
      have hveNew : sh.east sh.active < sh.nextVertex := hveast
      constructor
      · simp [kmswStepOfStep, State.addEdge,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap]
      · simpa [kmswStepOfStep, State.addEdge,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap, hsim.active,
          ne_of_lt hveNew] using
          hnewActiveInc.2
  · intro e he hp
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp only [kmswStepOfStep, State.addEdge] at he
      omega
    rcases heOld with heOld | he0 | he1
    · have hbound := hsim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      have hng0 : eφ e ≠ gl.nextEdge := by omega
      have hng1 : eφ e ≠ gl.nextEdge + 1 := by omega
      have hpres := hsim.present e heOld (by
        simpa [kmswStepOfStep, State.addEdge, hne0, hne1] using hp)
      simpa [kmswStepOfStep, State.addEdge, eψ,
        kmswShiftUpEdgeMap, hne0, hne1, hng0, hng1] using hpres
    · subst e
      simp [kmswStepOfStep, State.addEdge, kmswShiftUpEdgeMap]
    · subst e
      simp [kmswStepOfStep, State.addEdge] at hp
  · change List.map eψ ((sh.nextEdge + 1) :: sh.UR) <+:
      (gl.nextEdge + 1) :: gl.UR
    rw [List.map_cons, hmapUR]
    apply List.cons_prefix_cons.mpr
    constructor
    · simp [eψ, kmswShiftUpEdgeMap]
    · exact hsim.ur_prefix
  · have hshUL : (kmswStepOfStep sh .up).UL.dropLast.reverse =
        sh.UL.dropLast.reverse := by simp [kmswStepOfStep]
    have hglUL : (kmswStepOfStep gl .up).UL.dropLast.reverse =
        gl.UL.dropLast.reverse := by simp [kmswStepOfStep]
    rw [hshUL, hglUL, hmapUL]
    exact hsim.ul_predecessors_prefix

/-- The down-code case where both states already have an upper-right edge.
The stack-prefix invariant identifies their heads, so both runs activate the
same mapped edge and remove one entry from each stack -/
theorem kmswShiftSim_step_down_nonempty (sh gl : State) (eφ vφ : ℕ → ℕ)
    (hshUR : ∃ e es, sh.UR = e :: es)
    (hshUL : ∃ xs, sh.UL = xs ++ [sh.active])
    (hglUL : ∃ ys, gl.UL = ys ++ [gl.active])
    (hsim : Sim sh gl eφ vφ) :
    Sim (kmswStep sh 2) (kmswStep gl 2) eφ vφ := by
  change Sim (kmswStepOfStep sh .down) (kmswStepOfStep gl .down) eφ vφ
  obtain ⟨a, as, hshUR⟩ := hshUR
  cases hglUR : gl.UR with
  | nil =>
      have hfalse := hsim.ur_prefix
      simp [hshUR, hglUR] at hfalse
  | cons b bs =>
    have hprefix : eφ a :: List.map eφ as <+: b :: bs := by
      simpa [hshUR, hglUR] using hsim.ur_prefix
    have hparts := List.cons_prefix_cons.mp hprefix
    obtain ⟨xs, hshUL⟩ := hshUL
    obtain ⟨ys, hglUL⟩ := hglUL
    have hshPred :
        (kmswStepOfStep sh .down).UL.dropLast.reverse =
          sh.active :: sh.UL.dropLast.reverse := by
      simp [kmswStepOfStep, hshUR, hshUL, List.reverse_append]
    have hglPred :
        (kmswStepOfStep gl .down).UL.dropLast.reverse =
          gl.active :: gl.UL.dropLast.reverse := by
      simp [kmswStepOfStep, hglUR, hglUL, List.reverse_append]
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
    · simpa [kmswStepOfStep, hshUR, hglUR] using hsim.edge_bound
    · simpa [kmswStepOfStep, hshUR, hglUR] using hsim.edge_injective
    · simpa [kmswStepOfStep, hshUR, hglUR] using hsim.vertex_bound
    · simpa [kmswStepOfStep, hshUR, hglUR] using hsim.vertex_injective
    · simpa [kmswStepOfStep, hshUR, hglUR] using hparts.1
    · intro e he
      have heOld : e < sh.nextEdge := by
        simpa [kmswStepOfStep, hshUR] using he
      simpa [kmswStepOfStep, hshUR, hglUR] using hsim.incidence e heOld
    · intro e he hp
      by_cases hea : e = a
      · subst e
        simp [kmswStepOfStep, hglUR, hparts.1]
      · have hpOld : sh.present e = true := by
          simpa [kmswStepOfStep, hshUR, hea] using hp
        have heOld : e < sh.nextEdge := by
          simpa [kmswStepOfStep, hshUR] using he
        have hpres := hsim.present e heOld hpOld
        by_cases hmap : eφ e = b
        · simp [kmswStepOfStep, hglUR, hmap]
        · simpa [kmswStepOfStep, hglUR, hmap] using hpres
    · simpa [kmswStepOfStep, hshUR, hglUR] using hparts.2
    · rw [hshPred, hglPred, List.map_cons]
      exact List.cons_prefix_cons.mpr ⟨hsim.active, hsim.ul_predecessors_prefix⟩

/-- Edge-map update when the shifted step allocates one edge that matches a
new global edge. -/
@[expose] def kmswShiftFreshEdgeMap (sh gl : State) (eφ : ℕ → ℕ) : ℕ → ℕ :=
  fun e => if e = sh.nextEdge then gl.nextEdge else eφ e

/-- The down-code case where both upper-right stacks are empty. Both runs
allocate a corresponding present edge and fresh east vertex -/
theorem kmswShiftSim_step_down_empty (sh gl : State) (eφ vφ : ℕ → ℕ)
    (hshActive : sh.active < sh.nextEdge)
    (hshEndpoints : ∀ e, e < sh.nextEdge →
      sh.west e < sh.nextVertex ∧ sh.east e < sh.nextVertex)
    (hshUR : sh.UR = []) (hglUR : gl.UR = [])
    (hshUL : ∃ xs, sh.UL = xs ++ [sh.active])
    (hglUL : ∃ ys, gl.UL = ys ++ [gl.active])
    (hshULBound : ∀ e ∈ sh.UL.dropLast.reverse, e < sh.nextEdge)
    (hsim : Sim sh gl eφ vφ) :
    Sim (kmswStep sh 2) (kmswStep gl 2)
      (kmswShiftFreshEdgeMap sh gl eφ) (kmswShiftUpVertexMap sh gl vφ) := by
  change Sim (kmswStepOfStep sh .down) (kmswStepOfStep gl .down)
    (kmswShiftFreshEdgeMap sh gl eφ) (kmswShiftUpVertexMap sh gl vφ)
  obtain ⟨xs, hshUL⟩ := hshUL
  obtain ⟨ys, hglUL⟩ := hglUL
  have hactiveInc := hsim.incidence sh.active hshActive
  rw [hsim.active] at hactiveInc
  have hactiveEndpoints := hshEndpoints sh.active hshActive
  have hmapPred : List.map (kmswShiftFreshEdgeMap sh gl eφ)
      (sh.UL.dropLast.reverse) = List.map eφ (sh.UL.dropLast.reverse) := by
    apply List.map_congr_left
    intro e he
    have heBound := hshULBound e he
    have hne : e ≠ sh.nextEdge := by omega
    simp [kmswShiftFreshEdgeMap, hne]
  have hshPred :
      (kmswStepOfStep sh .down).UL.dropLast.reverse =
        sh.active :: sh.UL.dropLast.reverse := by
    simp [kmswStepOfStep, hshUR, hshUL, List.reverse_append]
  have hglPred :
      (kmswStepOfStep gl .down).UL.dropLast.reverse =
        gl.active :: gl.UL.dropLast.reverse := by
    simp [kmswStepOfStep, hglUR, hglUL, List.reverse_append]
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
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at he
      omega
    rcases heOld with heOld | heNew
    · have hb := hsim.edge_bound e heOld
      have hne : e ≠ sh.nextEdge := by omega
      have hpost : eφ e < (kmswStepOfStep gl .down).nextEdge := by
        simp [kmswStepOfStep, State.addEdge, hglUR]
        omega
      simpa [kmswShiftFreshEdgeMap, hne] using hpost
    · subst e
      simp [kmswStepOfStep, State.addEdge, hglUR,
        kmswShiftFreshEdgeMap]
  · intro e f he hf hef
    have hclass (x : ℕ) (hx : x < sh.nextEdge + 1) :
        x < sh.nextEdge ∨ x = sh.nextEdge := by omega
    have he' : e < sh.nextEdge + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at he
      omega
    have hf' : f < sh.nextEdge + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at hf
      omega
    rcases hclass e he' with heOld | heNew <;>
      rcases hclass f hf' with hfOld | hfNew
    · have hneE : e ≠ sh.nextEdge := by omega
      have hneF : f ≠ sh.nextEdge := by omega
      have heq : eφ e = eφ f := by
        simpa [kmswShiftFreshEdgeMap, hneE, hneF] using hef
      exact hsim.edge_injective e f heOld hfOld heq
    · subst f
      have hb := hsim.edge_bound e heOld
      have hneE : e ≠ sh.nextEdge := by omega
      simp [kmswShiftFreshEdgeMap, hneE] at hef
      omega
    · subst e
      have hb := hsim.edge_bound f hfOld
      have hneF : f ≠ sh.nextEdge := by omega
      simp [kmswShiftFreshEdgeMap, hneF] at hef
      omega
    · subst e; subst f; rfl
  · intro v hv
    have hvOld : v < sh.nextVertex ∨ v = sh.nextVertex := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hv
      omega
    rcases hvOld with hvOld | hvNew
    · have hb := hsim.vertex_bound v hvOld
      have hne : v ≠ sh.nextVertex := by omega
      simpa [kmswStepOfStep, hshUR, hglUR, State.addEdge,
        kmswShiftUpVertexMap, hne] using Nat.lt_succ_of_lt hb
    · subst v
      simp [kmswStepOfStep, hglUR, State.addEdge,
        kmswShiftUpVertexMap]
  · intro v z hv hz hvz
    have hclass (x : ℕ) (hx : x < sh.nextVertex + 1) :
        x < sh.nextVertex ∨ x = sh.nextVertex := by omega
    have hv' : v < sh.nextVertex + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at hv
      omega
    have hz' : z < sh.nextVertex + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at hz
      omega
    rcases hclass v hv' with hvOld | hvNew <;>
      rcases hclass z hz' with hzOld | hzNew
    · have hneV : v ≠ sh.nextVertex := by omega
      have hneZ : z ≠ sh.nextVertex := by omega
      have heq : vφ v = vφ z := by
        simpa [kmswShiftUpVertexMap, hneV, hneZ] using hvz
      exact hsim.vertex_injective v z hvOld hzOld heq
    · subst z
      have hb := hsim.vertex_bound v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      simp [kmswShiftUpVertexMap, hneV] at hvz
      omega
    · subst v
      have hb := hsim.vertex_bound z hzOld
      have hneZ : z ≠ sh.nextVertex := by omega
      simp [kmswShiftUpVertexMap, hneZ] at hvz
      omega
    · subst v; subst z; rfl
  · simp [kmswStepOfStep, hshUR, hglUR,
      kmswShiftFreshEdgeMap]
  · intro e he
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at he
      omega
    rcases heOld with heOld | heNew
    · have hb := hsim.edge_bound e heOld
      have hneE : e ≠ sh.nextEdge := by omega
      have hneT : eφ e ≠ gl.nextEdge := by omega
      have hinc := hsim.incidence e heOld
      have hneVW : sh.west e ≠ sh.nextVertex := by
        have hv := (hshEndpoints e heOld).1
        omega
      have hneVE : sh.east e ≠ sh.nextVertex := by
        have hv := (hshEndpoints e heOld).2
        omega
      constructor
      · simpa [kmswStepOfStep, State.addEdge, hshUR, hglUR,
          kmswShiftFreshEdgeMap, kmswShiftUpVertexMap, hneE, hneT,
          hneVW] using hinc.1
      · simpa [kmswStepOfStep, State.addEdge, hshUR, hglUR,
          kmswShiftFreshEdgeMap, kmswShiftUpVertexMap, hneE, hneT,
          hneVE] using hinc.2
    · subst e
      have hneEast : sh.east sh.active ≠ sh.nextVertex := by omega
      constructor
      · simpa [kmswStepOfStep, State.addEdge, hshUR, hglUR,
          kmswShiftFreshEdgeMap, kmswShiftUpVertexMap, hsim.active,
          hneEast] using hactiveInc.2
      · simp [kmswStepOfStep, State.addEdge, hshUR, hglUR,
          kmswShiftFreshEdgeMap, kmswShiftUpVertexMap]
  · intro e he hp
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge := by
      simp [kmswStepOfStep, State.addEdge, hshUR] at he
      omega
    rcases heOld with heOld | heNew
    · have hb := hsim.edge_bound e heOld
      have hneE : e ≠ sh.nextEdge := by omega
      have hneT : eφ e ≠ gl.nextEdge := by omega
      have hpres := hsim.present e heOld (by
        simpa [kmswStepOfStep, State.addEdge, hshUR, hneE] using hp)
      simpa [kmswStepOfStep, State.addEdge, hshUR, hglUR,
        kmswShiftFreshEdgeMap, hneE, hneT] using hpres
    · subst e
      simp [kmswStepOfStep, State.addEdge, hglUR,
        kmswShiftFreshEdgeMap]
  · simp [kmswStepOfStep, State.addEdge, hshUR, hglUR]
  · rw [hshPred, hglPred, List.map_cons, hmapPred]
    have hactiveMap : kmswShiftFreshEdgeMap sh gl eφ sh.active = gl.active := by
      have hne : sh.active ≠ sh.nextEdge := by omega
      simpa [kmswShiftFreshEdgeMap, hne] using hsim.active
    exact List.cons_prefix_cons.mpr ⟨hactiveMap, hsim.ul_predecessors_prefix⟩

/-- The left-code case where both nearest-first predecessor stacks are empty.
Both runs allocate a new active edge, a new missing edge, and a fresh vertex -/
theorem kmswShiftSim_step_left_empty (sh gl : State) (eφ vφ : ℕ → ℕ)
    (hshActive : sh.active < sh.nextEdge)
    (hshEndpoints : ∀ e, e < sh.nextEdge →
      sh.west e < sh.nextVertex ∧ sh.east e < sh.nextVertex)
    (hshPred : sh.UL.dropLast.reverse = [])
    (hglPred : gl.UL.dropLast.reverse = [])
    (hshURBound : ∀ e ∈ sh.UR, e < sh.nextEdge)
    (hsim : Sim sh gl eφ vφ) :
    Sim (kmswStep sh 0) (kmswStep gl 0)
      (kmswShiftUpEdgeMap sh gl eφ) (kmswShiftUpVertexMap sh gl vφ) := by
  change Sim (kmswStepOfStep sh .left) (kmswStepOfStep gl .left)
    (kmswShiftUpEdgeMap sh gl eφ) (kmswShiftUpVertexMap sh gl vφ)
  have hactiveInc := hsim.incidence sh.active hshActive
  rw [hsim.active] at hactiveInc
  have hactiveEndpoints := hshEndpoints sh.active hshActive
  have hmapUR : List.map (kmswShiftUpEdgeMap sh gl eφ) sh.UR =
      List.map eφ sh.UR := by
    apply List.map_congr_left
    intro e he
    have heBound := hshURBound e he
    have hne0 : e ≠ sh.nextEdge := by omega
    have hne1 : e ≠ sh.nextEdge + 1 := by omega
    simp [kmswShiftUpEdgeMap, hne0, hne1]
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
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshPred] at he
      omega
    rcases heOld with heOld | he0 | he1
    · have hb := hsim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      have hpost : eφ e < (kmswStepOfStep gl .left).nextEdge := by
        simp [kmswStepOfStep, State.addEdge, hglPred]
        omega
      simpa [kmswShiftUpEdgeMap, hne0, hne1] using hpost
    · subst e
      simp [kmswStepOfStep, State.addEdge, hglPred,
        kmswShiftUpEdgeMap]
    · subst e
      simp [kmswStepOfStep, State.addEdge, hglPred,
        kmswShiftUpEdgeMap]
  · intro e f he hf hef
    have hclass (x : ℕ) (hx : x < sh.nextEdge + 2) :
        x < sh.nextEdge ∨ x = sh.nextEdge ∨ x = sh.nextEdge + 1 := by omega
    have he' : e < sh.nextEdge + 2 := by
      simp [kmswStepOfStep, State.addEdge, hshPred] at he
      omega
    have hf' : f < sh.nextEdge + 2 := by
      simp [kmswStepOfStep, State.addEdge, hshPred] at hf
      omega
    rcases hclass e he' with heOld | he0 | he1 <;>
      rcases hclass f hf' with hfOld | hf0 | hf1
    · have hneE0 : e ≠ sh.nextEdge := by omega
      have hneE1 : e ≠ sh.nextEdge + 1 := by omega
      have hneF0 : f ≠ sh.nextEdge := by omega
      have hneF1 : f ≠ sh.nextEdge + 1 := by omega
      have heq : eφ e = eφ f := by
        simpa [kmswShiftUpEdgeMap, hneE0, hneE1, hneF0, hneF1] using hef
      exact hsim.edge_injective e f heOld hfOld heq
    · subst f
      have hb := hsim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst f
      have hb := hsim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e
      have hb := hsim.edge_bound f hfOld
      have hne0 : f ≠ sh.nextEdge := by omega
      have hne1 : f ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e; subst f; rfl
    · subst e; subst f
      simp [kmswShiftUpEdgeMap] at hef
    · subst e
      have hb := hsim.edge_bound f hfOld
      have hne0 : f ≠ sh.nextEdge := by omega
      have hne1 : f ≠ sh.nextEdge + 1 := by omega
      simp [kmswShiftUpEdgeMap, hne0, hne1] at hef
      omega
    · subst e; subst f
      simp [kmswShiftUpEdgeMap] at hef
    · subst e; subst f; rfl
  · intro v hv
    have hvOld : v < sh.nextVertex ∨ v = sh.nextVertex := by
      simp [kmswStepOfStep, State.addEdge, hshPred] at hv
      omega
    rcases hvOld with hvOld | hvNew
    · have hb := hsim.vertex_bound v hvOld
      have hne : v ≠ sh.nextVertex := by omega
      simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
        kmswShiftUpVertexMap, hne] using Nat.lt_succ_of_lt hb
    · subst v
      simp [kmswStepOfStep, State.addEdge, hglPred,
        kmswShiftUpVertexMap]
  · intro v z hv hz hvz
    have hclass (x : ℕ) (hx : x < sh.nextVertex + 1) :
        x < sh.nextVertex ∨ x = sh.nextVertex := by omega
    have hv' : v < sh.nextVertex + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshPred] at hv
      omega
    have hz' : z < sh.nextVertex + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshPred] at hz
      omega
    rcases hclass v hv' with hvOld | hvNew <;>
      rcases hclass z hz' with hzOld | hzNew
    · have hneV : v ≠ sh.nextVertex := by omega
      have hneZ : z ≠ sh.nextVertex := by omega
      have heq : vφ v = vφ z := by
        simpa [kmswShiftUpVertexMap, hneV, hneZ] using hvz
      exact hsim.vertex_injective v z hvOld hzOld heq
    · subst z
      have hb := hsim.vertex_bound v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      simp [kmswShiftUpVertexMap, hneV] at hvz
      omega
    · subst v
      have hb := hsim.vertex_bound z hzOld
      have hneZ : z ≠ sh.nextVertex := by omega
      simp [kmswShiftUpVertexMap, hneZ] at hvz
      omega
    · subst v; subst z; rfl
  · simp [kmswStepOfStep, State.addEdge, hshPred, hglPred,
      kmswShiftUpEdgeMap]
  · intro e he
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshPred] at he
      omega
    rcases heOld with heOld | he0 | he1
    · have hb := hsim.edge_bound e heOld
      have hinc := hsim.incidence e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      have hng0 : eφ e ≠ gl.nextEdge := by omega
      have hng1 : eφ e ≠ gl.nextEdge + 1 := by omega
      have hneVW : sh.west e ≠ sh.nextVertex := by
        have hv := (hshEndpoints e heOld).1
        omega
      have hneVE : sh.east e ≠ sh.nextVertex := by
        have hv := (hshEndpoints e heOld).2
        omega
      constructor
      · simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap, hne0, hne1, hng0,
          hng1, hneVW] using hinc.1
      · simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap, hne0, hne1, hng0,
          hng1, hneVE] using hinc.2
    · subst e
      have hneEast : sh.east sh.active ≠ sh.nextVertex := by omega
      constructor
      · simp [kmswStepOfStep, State.addEdge, hshPred, hglPred,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap]
      · simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap, hsim.active,
          hneEast] using hactiveInc.2
    · subst e
      have hneWest : sh.west sh.active ≠ sh.nextVertex := by omega
      constructor
      · simp [kmswStepOfStep, State.addEdge, hshPred, hglPred,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap]
      · simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
          kmswShiftUpEdgeMap, kmswShiftUpVertexMap, hsim.active,
          hneWest] using hactiveInc.1
  · intro e he hp
    have heOld : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by
      simp [kmswStepOfStep, State.addEdge, hshPred] at he
      omega
    rcases heOld with heOld | he0 | he1
    · have hb := hsim.edge_bound e heOld
      have hne0 : e ≠ sh.nextEdge := by omega
      have hne1 : e ≠ sh.nextEdge + 1 := by omega
      have hng0 : eφ e ≠ gl.nextEdge := by omega
      have hng1 : eφ e ≠ gl.nextEdge + 1 := by omega
      have hpres := hsim.present e heOld (by
        simpa [kmswStepOfStep, State.addEdge, hshPred, hne0, hne1] using hp)
      simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
        kmswShiftUpEdgeMap, hne0, hne1, hng0, hng1] using hpres
    · subst e
      simp [kmswStepOfStep, State.addEdge, hglPred,
        kmswShiftUpEdgeMap]
    · subst e
      simp [kmswStepOfStep, State.addEdge, hshPred] at hp
  · have hshURPost : (kmswStepOfStep sh .left).UR = sh.UR := by
      simp [kmswStepOfStep, State.addEdge, hshPred]
    have hglURPost : (kmswStepOfStep gl .left).UR = gl.UR := by
      simp [kmswStepOfStep, State.addEdge, hglPred]
    rw [hshURPost, hglURPost, hmapUR]
    exact hsim.ur_prefix
  · simp [kmswStepOfStep, State.addEdge, hshPred, hglPred]

/-- The left-code case where both states have a predecessor immediately west
of their active edge. The predecessor-stack prefix identifies the consumed
edges; each run allocates one corresponding new active edge -/
theorem kmswShiftSim_step_left_nonempty (sh gl : State) (eφ vφ : ℕ → ℕ)
    (hshActive : sh.active < sh.nextEdge)
    (hshPred : ∃ e es, sh.UL.dropLast.reverse = e :: es)
    (hshPredBound : ∀ e ∈ sh.UL.dropLast.reverse, e < sh.nextEdge)
    (hshURBound : ∀ e ∈ sh.UR, e < sh.nextEdge)
    (hsim : Sim sh gl eφ vφ) :
    Sim (kmswStep sh 0) (kmswStep gl 0)
      (kmswShiftFreshEdgeMap sh gl eφ) vφ := by
  change Sim (kmswStepOfStep sh .left) (kmswStepOfStep gl .left)
    (kmswShiftFreshEdgeMap sh gl eφ) vφ
  obtain ⟨a, as, hshPred⟩ := hshPred
  cases hglPred : gl.UL.dropLast.reverse with
  | nil =>
      have hfalse := hsim.ul_predecessors_prefix
      simp [hshPred, hglPred] at hfalse
  | cons b bs =>
    have hprefix : eφ a :: List.map eφ as <+: b :: bs := by
      simpa [hshPred, hglPred] using hsim.ul_predecessors_prefix
    have hparts := List.cons_prefix_cons.mp hprefix
    have hheadBound : a < sh.nextEdge := hshPredBound a (by rw [hshPred]; simp)
    have htargetBound : eφ a < gl.nextEdge := hsim.edge_bound a hheadBound
    have hactiveInc := hsim.incidence sh.active hshActive
    rw [hsim.active] at hactiveInc
    have hmapTail : List.map (kmswShiftFreshEdgeMap sh gl eφ) as =
        List.map eφ as := by
      apply List.map_congr_left
      intro e he
      have heBound : e < sh.nextEdge := hshPredBound e (by
        rw [hshPred]
        exact List.mem_cons_of_mem _ he)
      have hne : e ≠ sh.nextEdge := by omega
      simp [kmswShiftFreshEdgeMap, hne]
    have hmapUR : List.map (kmswShiftFreshEdgeMap sh gl eφ) sh.UR =
        List.map eφ sh.UR := by
      apply List.map_congr_left
      intro e he
      have hb := hshURBound e he
      have hne : e ≠ sh.nextEdge := by omega
      simp [kmswShiftFreshEdgeMap, hne]
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
      have heOld : e < sh.nextEdge ∨ e = sh.nextEdge := by
        simp [kmswStepOfStep, State.addEdge, hshPred] at he
        omega
      rcases heOld with heOld | heNew
      · have hb := hsim.edge_bound e heOld
        have hne : e ≠ sh.nextEdge := by omega
        have hpost : eφ e < (kmswStepOfStep gl .left).nextEdge := by
          simp [kmswStepOfStep, State.addEdge, hglPred]
          omega
        simpa [kmswShiftFreshEdgeMap, hne] using hpost
      · subst e
        simp [kmswStepOfStep, State.addEdge, hglPred,
          kmswShiftFreshEdgeMap]
    · intro e f he hf hef
      have hclass (x : ℕ) (hx : x < sh.nextEdge + 1) :
          x < sh.nextEdge ∨ x = sh.nextEdge := by omega
      have he' : e < sh.nextEdge + 1 := by
        simp [kmswStepOfStep, State.addEdge, hshPred] at he
        omega
      have hf' : f < sh.nextEdge + 1 := by
        simp [kmswStepOfStep, State.addEdge, hshPred] at hf
        omega
      rcases hclass e he' with heOld | heNew <;>
        rcases hclass f hf' with hfOld | hfNew
      · have hneE : e ≠ sh.nextEdge := by omega
        have hneF : f ≠ sh.nextEdge := by omega
        have heq : eφ e = eφ f := by
          simpa [kmswShiftFreshEdgeMap, hneE, hneF] using hef
        exact hsim.edge_injective e f heOld hfOld heq
      · subst f
        have hb := hsim.edge_bound e heOld
        have hneE : e ≠ sh.nextEdge := by omega
        simp [kmswShiftFreshEdgeMap, hneE] at hef
        omega
      · subst e
        have hb := hsim.edge_bound f hfOld
        have hneF : f ≠ sh.nextEdge := by omega
        simp [kmswShiftFreshEdgeMap, hneF] at hef
        omega
      · subst e; subst f; rfl
    · intro v hv
      have hvPre : v < sh.nextVertex := by
        simp [kmswStepOfStep, State.addEdge, hshPred] at hv
        exact hv
      simpa [kmswStepOfStep, State.addEdge, hglPred] using hsim.vertex_bound v hvPre
    · intro v z hv hz hvz
      have hvPre : v < sh.nextVertex := by
        simp [kmswStepOfStep, State.addEdge, hshPred] at hv
        exact hv
      have hzPre : z < sh.nextVertex := by
        simp [kmswStepOfStep, State.addEdge, hshPred] at hz
        exact hz
      exact hsim.vertex_injective v z hvPre hzPre hvz
    · simp [kmswStepOfStep, State.addEdge, hshPred, hglPred,
        kmswShiftFreshEdgeMap]
    · intro e he
      have heOld : e < sh.nextEdge ∨ e = sh.nextEdge := by
        simp [kmswStepOfStep, State.addEdge, hshPred] at he
        omega
      rcases heOld with heOld | heNew
      · have hb := hsim.edge_bound e heOld
        have hneE : e ≠ sh.nextEdge := by omega
        have hneT : eφ e ≠ gl.nextEdge := by omega
        have hinc := hsim.incidence e heOld
        simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
          kmswShiftFreshEdgeMap,
          hneE, hneT] using hinc
      · subst e
        constructor
        · have hinc := hsim.incidence a hheadBound
          rw [hparts.1] at hinc
          simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
            kmswShiftFreshEdgeMap] using hinc.1
        · simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
            kmswShiftFreshEdgeMap] using hactiveInc.2
    · intro e he hp
      have heOld : e < sh.nextEdge ∨ e = sh.nextEdge := by
        simp [kmswStepOfStep, State.addEdge, hshPred] at he
        omega
      rcases heOld with heOld | heNew
      · have hb := hsim.edge_bound e heOld
        have hneE : e ≠ sh.nextEdge := by omega
        have hneT : eφ e ≠ gl.nextEdge := by omega
        have hpres := hsim.present e heOld (by
          simpa [kmswStepOfStep, State.addEdge, hshPred, hneE] using hp)
        simpa [kmswStepOfStep, State.addEdge, hshPred, hglPred,
          kmswShiftFreshEdgeMap,
          hneE, hneT] using hpres
      · subst e
        simp [kmswStepOfStep, State.addEdge, hglPred,
          kmswShiftFreshEdgeMap]
    · have hshURPost : (kmswStepOfStep sh .left).UR = sh.UR := by
        simp [kmswStepOfStep, hshPred, State.addEdge]
      have hglURPost : (kmswStepOfStep gl .left).UR = gl.UR := by
        simp [kmswStepOfStep, hglPred, State.addEdge]
      rw [hshURPost, hglURPost, hmapUR]
      exact hsim.ur_prefix
    · have hshPost :
          (kmswStepOfStep sh .left).UL.dropLast.reverse = as := by
        simp [kmswStepOfStep, hshPred]
      have hglPost :
          (kmswStepOfStep gl .left).UL.dropLast.reverse = bs := by
        simp [kmswStepOfStep, hglPred]
      rw [hshPost, hglPost, hmapTail]
      exact hparts.2

end DirectedDistances.KMSW
