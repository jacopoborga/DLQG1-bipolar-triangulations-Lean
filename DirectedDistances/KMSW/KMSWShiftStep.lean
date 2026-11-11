module

public import DirectedDistances.KMSW.KMSWShiftMismatch
import DirectedDistances.KMSW.StageIncidenceChains

/-! # Stage-wise preservation of shifted KMSW simulations

The mismatch cases are handled on genuine finite stages, where boundary
incidence, endpoint allocation, and missing-edge status are available -/

public section
namespace DirectedDistances.KMSW

private theorem kmswShift_stage_UR_bound (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UR) : e < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
  simp only [List.mem_append]
  tauto

private theorem kmswShift_stage_ULpred_bound (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UL.dropLast.reverse) :
    e < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
  have heUL : e ∈ (kmswStage w n).UL :=
    List.dropLast_subset _ (List.mem_reverse.mp he)
  simp only [List.mem_append]
  tauto

private theorem kmswShift_stage_ULpred_head_incidence
    (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hpred : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).east e = (kmswStage w n).west (kmswStage w n).active := by
  let s := kmswStage w n
  obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
  have hrev : xs.reverse = e :: es := by
    simpa [s, hUL, List.reverse_append] using hpred
  have hxs : xs = es.reverse ++ [e] := by
    have h := congrArg List.reverse hrev
    simpa only [List.reverse_reverse, List.reverse_cons, List.reverse_append,
      List.reverse_nil] using h
  have hUL' : s.UL = es.reverse ++ [e, s.active] := by
    rw [hUL, hxs]
    simp [s, List.append_assoc]
  have hchain : List.IsChain (fun a b => s.east a = s.west b) s.UL :=
    (kmswStage_boundary_chain_invariant w n).1.left_of_append
  rw [hUL'] at hchain
  have hrel := (List.isChain_append_cons_cons.mp hchain).2.1
  exact hrel

/-- The down mismatch step preserves `Sim` when the shifted stage has an
empty UR stack and the global stage consumes its first UR edge -/
theorem kmswShiftSim_step_down_mismatch
    (u w : ℕ → Fin 3) (m n : ℕ) (e : ℕ) (es : List ℕ)
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshUR : (kmswStage u m).UR = [])
    (hglUR : (kmswStage w n).UR = e :: es) :
    Sim (kmswStepOfStep (kmswStage u m) .down)
      (kmswStepOfStep (kmswStage w n) .down)
      (kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ)
      (kmswShiftDownMismatchVertexMap (kmswStage u m) (kmswStage w n) e vφ) := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftDownMismatchEdgeMap sh e eφ
  let vψ := kmswShiftDownMismatchVertexMap sh gl e vφ
  change sh.UR = [] at hshUR
  change gl.UR = e :: es at hglUR
  change Sim (kmswStepOfStep sh .down) (kmswStepOfStep gl .down) eψ vψ
  have hact : sh.active < sh.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u m).1
  have heBound : e < gl.nextEdge := by
    apply kmswShift_stage_UR_bound w n e
    rw [hglUR]
    simp
  have heGlobal : e ∈ gl.UR := by rw [hglUR]; simp
  have heNotMap : e ∉ List.map eφ sh.UR := by simp [hshUR]
  have hshPred : (kmswStepOfStep sh .down).UL.dropLast.reverse =
      sh.active :: sh.UL.dropLast.reverse := by
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last u m
    simpa [sh, kmswStepOfStep, hshUR, hUL, List.reverse_append]
  have hglPred : (kmswStepOfStep gl .down).UL.dropLast.reverse =
      gl.active :: gl.UL.dropLast.reverse := by
    obtain ⟨ys, hUL⟩ := kmswStage_UL_last w n
    simpa [gl, kmswStepOfStep, hglUR, hUL, List.reverse_append]
  have hURrel : gl.west e = gl.east gl.active := by
    exact (kmswStage_boundary_chain_invariant w n).2.2.2.2.2.1 e es hglUR
  have hactiveInc := hsim.sim.incidence sh.active hact
  rw [hsim.sim.active] at hactiveInc
  have hshEndpoints := kmswStage_endpoints_lt_nextVertex u m sh.active hact
  have hmapPredTail : List.map eψ (sh.UL.dropLast.reverse) =
      List.map eφ (sh.UL.dropLast.reverse) := by
    apply List.map_congr_left
    intro f hf
    have hfBound := kmswShift_stage_ULpred_bound u m f hf
    change f < sh.nextEdge at hfBound
    have hne : f ≠ sh.nextEdge := by omega
    simp [eψ, kmswShiftDownMismatchEdgeMap, hne]
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
  · intro f hf
    have hfCases : f < sh.nextEdge ∨ f = sh.nextEdge := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hf
      omega
    rcases hfCases with hfOld | rfl
    · have hbound := hsim.sim.edge_bound f hfOld
      have hne : f ≠ sh.nextEdge := by omega
      simpa [kmswStepOfStep, hglUR, State.addEdge, eψ,
        kmswShiftDownMismatchEdgeMap, hne] using hbound
    · simpa [kmswStepOfStep, hglUR, State.addEdge, eψ,
        kmswShiftDownMismatchEdgeMap] using heBound
  · intro f g hf hg hEq
    have hfCases : f < sh.nextEdge ∨ f = sh.nextEdge := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hf
      omega
    have hgCases : g < sh.nextEdge ∨ g = sh.nextEdge := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hg
      omega
    rcases hfCases with hfOld | rfl <;> rcases hgCases with hgOld | rfl
    · have hneF : f ≠ sh.nextEdge := by omega
      have hneG : g ≠ sh.nextEdge := by omega
      have hEqOld : eφ f = eφ g := by
        simpa [eψ, kmswShiftDownMismatchEdgeMap, hneF, hneG] using hEq
      exact hsim.sim.edge_injective f g hfOld hgOld hEqOld
    · have havoid := hsim.ur_edge_avoid e heGlobal heNotMap f hfOld
      have hneF : f ≠ sh.nextEdge := by omega
      have hEq' : eφ f = e := by
        simpa [eψ, kmswShiftDownMismatchEdgeMap, hneF] using hEq
      exact False.elim (havoid hEq')
    · have havoid := hsim.ur_edge_avoid e heGlobal heNotMap g hgOld
      have hneG : g ≠ sh.nextEdge := by omega
      have hEq' : eφ g = e := by
        simpa [eψ, kmswShiftDownMismatchEdgeMap, hneG] using hEq.symm
      exact False.elim (havoid hEq')
    · rfl
  · intro v hv
    have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hv
      omega
    rcases hvCases with hvOld | rfl
    · have hbound := hsim.sim.vertex_bound v hvOld
      have hne : v ≠ sh.nextVertex := by omega
      simpa [kmswStepOfStep, hglUR, State.addEdge, vψ,
        kmswShiftDownMismatchVertexMap, hne] using hbound
    · have heEnds := kmswStage_endpoints_lt_nextVertex w n e heBound
      simpa [kmswStepOfStep, hglUR, State.addEdge, vψ,
        kmswShiftDownMismatchVertexMap] using heEnds.2
  · intro v z hv hz hEq
    have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hv
      omega
    have hzCases : z < sh.nextVertex ∨ z = sh.nextVertex := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hz
      omega
    rcases hvCases with hvOld | rfl <;> rcases hzCases with hzOld | rfl
    · have hneV : v ≠ sh.nextVertex := by omega
      have hneZ : z ≠ sh.nextVertex := by omega
      have hEqOld : vφ v = vφ z := by
        simpa [vψ, kmswShiftDownMismatchVertexMap, hneV, hneZ] using hEq
      exact hsim.sim.vertex_injective v z hvOld hzOld hEqOld
    · have havoid := hsim.ur_east_avoid e heGlobal heNotMap v hvOld
      have hneV : v ≠ sh.nextVertex := by omega
      have hEq' : vφ v = gl.east e := by
        simpa [vψ, kmswShiftDownMismatchVertexMap, hneV] using hEq
      exact False.elim (havoid hEq')
    · have havoid := hsim.ur_east_avoid e heGlobal heNotMap z hzOld
      have hneZ : z ≠ sh.nextVertex := by omega
      have hEq' : vφ z = gl.east e := by
        simpa [vψ, kmswShiftDownMismatchVertexMap, hneZ] using hEq.symm
      exact False.elim (havoid hEq')
    · rfl
  · simp [kmswStepOfStep, hshUR, hglUR, eψ,
      kmswShiftDownMismatchEdgeMap]
  · intro f hf
    have hfCases : f < sh.nextEdge ∨ f = sh.nextEdge := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hf
      omega
    rcases hfCases with hfOld | rfl
    · have hfEndpoints := kmswStage_endpoints_lt_nextVertex u m f hfOld
      change sh.west f < sh.nextVertex ∧ sh.east f < sh.nextVertex at hfEndpoints
      have hneEdge : f ≠ sh.nextEdge := by omega
      have hneWest : sh.west f ≠ sh.nextVertex := by omega
      have hneEast : sh.east f ≠ sh.nextVertex := by omega
      simpa [kmswStepOfStep, hshUR, hglUR, State.addEdge, eψ, vψ,
        kmswShiftDownMismatchEdgeMap, kmswShiftDownMismatchVertexMap,
        hneEdge, hneWest, hneEast] using hsim.sim.incidence f hfOld
    · constructor
      · have hneEast : sh.east sh.active ≠ sh.nextVertex := by
          change (kmswStage u m).east sh.active ≠ (kmswStage u m).nextVertex
          omega
        simp only [kmswStepOfStep, hglUR, hshUR, eψ,
          kmswShiftDownMismatchEdgeMap, State.addEdge, vψ,
          kmswShiftDownMismatchVertexMap, hneEast]
        simp [hneEast]
        calc
          gl.west e = gl.east gl.active := hURrel
          _ = vφ (sh.east sh.active) := hactiveInc.2
      · simp [kmswStepOfStep, hglUR, hshUR, eψ,
          kmswShiftDownMismatchEdgeMap, State.addEdge, vψ,
          kmswShiftDownMismatchVertexMap]
  · intro f hf hp
    have hfCases : f < sh.nextEdge ∨ f = sh.nextEdge := by
      simp [kmswStepOfStep, hshUR, State.addEdge] at hf
      omega
    rcases hfCases with hfOld | rfl
    · have havoid := hsim.ur_edge_avoid e heGlobal heNotMap f hfOld
      have hneEdge : f ≠ sh.nextEdge := by omega
      have hpres := hsim.sim.present f hfOld (by
        simpa [kmswStepOfStep, hshUR, State.addEdge, hneEdge] using hp)
      have hneMap : eφ f ≠ e := by
        intro hEq
        exact havoid hEq
      simpa [kmswStepOfStep, hglUR, eψ,
        kmswShiftDownMismatchEdgeMap, hneEdge, hneMap] using hpres
    · simp [kmswStepOfStep, hshUR, hglUR, State.addEdge,
        eψ, kmswShiftDownMismatchEdgeMap]
  · simp [kmswStepOfStep, hshUR, hglUR, State.addEdge, eψ]
  · rw [hshPred, hglPred, List.map_cons, hmapPredTail]
    have hactiveMap : eψ sh.active = gl.active := by
      have hne : sh.active ≠ sh.nextEdge := by omega
      simpa [eψ, kmswShiftDownMismatchEdgeMap, hne] using hsim.sim.active
    exact List.cons_prefix_cons.mpr
      ⟨hactiveMap, hsim.sim.ul_predecessors_prefix⟩

/-- The down mismatch preserves the full avoidance-aware simulation -/
theorem kmswShiftSim2_step_down_mismatch
    (u w : ℕ → Fin 3) (m n : ℕ) (e : ℕ) (es : List ℕ)
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshUR : (kmswStage u m).UR = [])
    (hglUR : (kmswStage w n).UR = e :: es) :
    Sim2 (kmswStepOfStep (kmswStage u m) .down)
      (kmswStepOfStep (kmswStage w n) .down)
      (kmswShiftDownMismatchEdgeMap (kmswStage u m) e eφ)
      (kmswShiftDownMismatchVertexMap (kmswStage u m) (kmswStage w n) e vφ) := by
  refine ⟨kmswShiftSim_step_down_mismatch u w m n e es eφ vφ hsim hshUR hglUR,
    ?_, ?_, ?_, ?_⟩
  · exact (kmswShiftDownMismatch_ur_avoidance u w m n eφ vφ hsim e es hshUR hglUR).1
  · exact (kmswShiftDownMismatch_ur_avoidance u w m n eφ vφ hsim e es hshUR hglUR).2
  · exact (kmswShiftDownMismatch_ul_avoidance u w m n eφ vφ hsim e es hshUR hglUR).1
  · exact (kmswShiftDownMismatch_ul_avoidance u w m n eφ vφ hsim e es hshUR hglUR).2

/-- In a matched down step with empty UR stacks, the fresh-edge simulation
also preserves both boundary avoidance clauses (`def-kmsw`, -/
theorem kmswShiftSim2_step_down_empty
    (u w : ℕ → Fin 3) (m n : ℕ) (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshUR : (kmswStage u m).UR = [])
    (hglUR : (kmswStage w n).UR = []) :
    Sim2 (kmswStepOfStep (kmswStage u m) .down)
      (kmswStepOfStep (kmswStage w n) .down)
      (kmswShiftFreshEdgeMap (kmswStage u m) (kmswStage w n) eφ)
      (kmswShiftUpVertexMap (kmswStage u m) (kmswStage w n) vφ) := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftFreshEdgeMap sh gl eφ
  let vψ := kmswShiftUpVertexMap sh gl vφ
  change sh.UR = [] at hshUR
  change gl.UR = [] at hglUR
  have hact : sh.active < sh.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u m).1
  have hEndpoints : ∀ e, e < sh.nextEdge →
      sh.west e < sh.nextVertex ∧ sh.east e < sh.nextVertex := by
    intro e he
    exact kmswStage_endpoints_lt_nextVertex u m e he
  have hshUL : ∃ xs, sh.UL = xs ++ [sh.active] := kmswStage_UL_last u m
  have hglUL : ∃ ys, gl.UL = ys ++ [gl.active] := kmswStage_UL_last w n
  have hshULBound : ∀ e ∈ sh.UL.dropLast.reverse, e < sh.nextEdge := by
    intro e he
    exact kmswShift_stage_ULpred_bound u m e he
  have hsim' : Sim (kmswStepOfStep sh .down) (kmswStepOfStep gl .down) eψ vψ := by
    exact kmswShiftSim_step_down_empty sh gl eφ vφ hact hEndpoints hshUR hglUR
      hshUL hglUL hshULBound hsim.sim
  have hshPred : (kmswStepOfStep sh .down).UL.dropLast.reverse =
      sh.active :: sh.UL.dropLast.reverse := by
    obtain ⟨xs, hUL⟩ := hshUL
    simp [kmswStepOfStep, hshUR, hUL, List.reverse_append]
  have hglPred : (kmswStepOfStep gl .down).UL.dropLast.reverse =
      gl.active :: gl.UL.dropLast.reverse := by
    obtain ⟨ys, hUL⟩ := hglUL
    simp [kmswStepOfStep, hglUR, hUL, List.reverse_append]
  have hmapPred : List.map eψ ((kmswStepOfStep sh .down).UL.dropLast.reverse) =
      gl.active :: List.map eφ (sh.UL.dropLast.reverse) := by
    rw [hshPred, List.map_cons]
    have hactive : eψ sh.active = gl.active := by
      have hne : sh.active ≠ sh.nextEdge := by omega
      simpa [eψ, kmswShiftFreshEdgeMap, hne] using hsim.sim.active
    rw [hactive]
    have htail : List.map eψ (sh.UL.dropLast.reverse) =
        List.map eφ (sh.UL.dropLast.reverse) := by
      apply List.map_congr_left
      intro f hf
      have hfBound := hshULBound f hf
      have hne : f ≠ sh.nextEdge := by omega
      simp [eψ, kmswShiftFreshEdgeMap, hne]
    exact congrArg (List.cons gl.active) htail
  refine ⟨hsim', ?_, ?_, ?_, ?_⟩
  · intro f hf hnot x hx
    change f ∈ (kmswStepOfStep gl .down).UR at hf
    simp [kmswStepOfStep, hglUR, State.addEdge] at hf
  · intro f hf hnot v hv
    change f ∈ (kmswStepOfStep gl .down).UR at hf
    simp [kmswStepOfStep, hglUR, State.addEdge] at hf
  · intro f hf hnot x hx
    change f ∈ (kmswStepOfStep gl .down).UL.dropLast.reverse at hf
    change f ∉ List.map eψ ((kmswStepOfStep sh .down).UL.dropLast.reverse) at hnot
    rw [hglPred] at hf
    simp only [List.mem_cons] at hf
    have hparts : f = gl.active ∨ f ∈ gl.UL.dropLast.reverse := hf
    rcases hparts with hhead | htail
    · subst f
      have hmem : gl.active ∈ List.map eψ
          ((kmswStepOfStep sh .down).UL.dropLast.reverse) := by
        rw [hmapPred]
        simp
      exact False.elim (hnot hmem)
    · have hnotTail : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
        intro hm
        apply hnot
        rw [hmapPred]
        exact List.mem_cons_of_mem _ hm
      have hclass : x < sh.nextEdge ∨ x = sh.nextEdge := by
        change x < (kmswStepOfStep sh .down).nextEdge at hx
        simp [kmswStepOfStep, hshUR, State.addEdge] at hx
        omega
      rcases hclass with hxOld | rfl
      · have havoid := hsim.ul_edge_avoid f htail hnotTail x hxOld
        have hmapOld : eψ x = eφ x := by
          simp [eψ, kmswShiftFreshEdgeMap, ne_of_lt hxOld]
        change eψ x ≠ f
        simpa [hmapOld] using havoid
      · have hbound := kmswShift_stage_ULpred_bound w n f htail
        change f < gl.nextEdge at hbound
        have hmapFresh : eψ sh.nextEdge = gl.nextEdge := by
          simp [eψ, kmswShiftFreshEdgeMap]
        have hne := ne_of_lt hbound
        change eψ sh.nextEdge ≠ f
        rw [hmapFresh]
        exact hne.symm
  · intro f hf hnot v hv
    change f ∈ (kmswStepOfStep gl .down).UL.dropLast.reverse at hf
    change f ∉ List.map eψ ((kmswStepOfStep sh .down).UL.dropLast.reverse) at hnot
    rw [hglPred] at hf
    simp only [List.mem_cons] at hf
    have hparts : f = gl.active ∨ f ∈ gl.UL.dropLast.reverse := hf
    rcases hparts with hhead | htail
    · subst f
      have hmem : gl.active ∈ List.map eψ
          ((kmswStepOfStep sh .down).UL.dropLast.reverse) := by
        rw [hmapPred]
        simp
      exact False.elim (hnot hmem)
    · have hnotTail : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
        intro hm
        apply hnot
        rw [hmapPred]
        exact List.mem_cons_of_mem _ hm
      have hclass : v < sh.nextVertex ∨ v = sh.nextVertex := by
        change v < (kmswStepOfStep sh .down).nextVertex at hv
        simp [kmswStepOfStep, hshUR, State.addEdge] at hv
        omega
      rcases hclass with hvOld | rfl
      · have havoid := hsim.ul_west_avoid f htail hnotTail v hvOld
        have hfBound := kmswShift_stage_ULpred_bound w n f htail
        change f < gl.nextEdge at hfBound
        have hneF : f ≠ gl.nextEdge := ne_of_lt hfBound
        have hmapOld : vψ v = vφ v := by
          simp [vψ, kmswShiftUpVertexMap, ne_of_lt hvOld]
        change vψ v ≠ (kmswStepOfStep gl .down).west f
        simpa [vψ, kmswShiftUpVertexMap, kmswStepOfStep, hglUR,
          State.addEdge, hmapOld, hneF] using havoid
      · have hbound := kmswStage_endpoints_lt_nextVertex w n f
          (kmswShift_stage_ULpred_bound w n f htail)
        change gl.west f < gl.nextVertex ∧ gl.east f < gl.nextVertex at hbound
        have hmapFresh : vψ sh.nextVertex = gl.nextVertex := by
          simp [vψ, kmswShiftUpVertexMap]
        have hne : gl.nextVertex ≠ gl.west f := (ne_of_lt hbound.1).symm
        have hneF : f ≠ gl.nextEdge := by
          have hfBound := kmswShift_stage_ULpred_bound w n f htail
          change f < gl.nextEdge at hfBound
          exact ne_of_lt hfBound
        change vψ sh.nextVertex ≠ (kmswStepOfStep gl .down).west f
        simpa [vψ, kmswShiftUpVertexMap, kmswStepOfStep, hglUR,
          State.addEdge, hmapFresh, hneF] using hne

/-- A matched down step with nonempty UR stacks preserves `Sim2`: the
consumed head is removed on both sides, and the remaining avoidance clauses
restrict to the two stack tails (`def-kmsw`, -/
theorem kmswShiftSim2_step_down_nonempty
    (u w : ℕ → Fin 3) (m n : ℕ) (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshUR : ∃ a as, (kmswStage u m).UR = a :: as)
    (hglUR : ∃ b bs, (kmswStage w n).UR = b :: bs) :
    Sim2 (kmswStepOfStep (kmswStage u m) .down)
      (kmswStepOfStep (kmswStage w n) .down) eφ vφ := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  obtain ⟨a, as, hshUR⟩ := hshUR
  obtain ⟨b, bs, hglUR⟩ := hglUR
  change sh.UR = a :: as at hshUR
  change gl.UR = b :: bs at hglUR
  have hshUL : ∃ xs, sh.UL = xs ++ [sh.active] := kmswStage_UL_last u m
  have hglUL : ∃ ys, gl.UL = ys ++ [gl.active] := kmswStage_UL_last w n
  have hSimStep : Sim (kmswStepOfStep sh .down) (kmswStepOfStep gl .down) eφ vφ :=
    kmswShiftSim_step_down_nonempty sh gl eφ vφ ⟨a, as, hshUR⟩ hshUL hglUL hsim.sim
  have hprefix : List.map eφ (a :: as) <+: b :: bs := by
    have hp : List.map eφ sh.UR <+: gl.UR := hsim.sim.ur_prefix
    simpa [hshUR, hglUR] using hp
  have hprefixParts := List.cons_prefix_cons.mp hprefix
  have hglobalNodup : gl.UR.Nodup := (kmswStage_status w n).2.2.2.1
  rw [hglUR] at hglobalNodup
  have hbNotTail : b ∉ bs := (List.nodup_cons.mp hglobalNodup).1
  have hnotPre (f : ℕ) (hnot : f ∉ List.map eφ as) (hf : f ∈ bs) :
      f ∉ List.map eφ (a :: as) := by
    intro hmem
    have hparts : f = eφ a ∨ f ∈ List.map eφ as := by simpa using hmem
    rcases hparts with hhead | htail
    · have hEq : f = b := hhead.trans hprefixParts.1
      exact hbNotTail (hEq ▸ hf)
    · exact hnot htail
  have hshPred : (kmswStepOfStep sh .down).UL.dropLast.reverse =
      sh.active :: sh.UL.dropLast.reverse := by
    obtain ⟨xs, hUL⟩ := hshUL
    simp [kmswStepOfStep, hshUR, hUL, List.reverse_append]
  have hglPred : (kmswStepOfStep gl .down).UL.dropLast.reverse =
      gl.active :: gl.UL.dropLast.reverse := by
    obtain ⟨ys, hUL⟩ := hglUL
    simp [kmswStepOfStep, hglUR, hUL, List.reverse_append]
  have hmapPred : List.map eφ ((kmswStepOfStep sh .down).UL.dropLast.reverse) =
      gl.active :: List.map eφ (sh.UL.dropLast.reverse) := by
    rw [hshPred, List.map_cons, hsim.sim.active]
  refine ⟨hSimStep, ?_, ?_, ?_, ?_⟩
  · intro f hf hnot x hx
    change f ∈ (kmswStepOfStep gl .down).UR at hf
    have hfTail : f ∈ bs := by simpa [kmswStepOfStep, hglUR] using hf
    change f ∉ List.map eφ ((kmswStepOfStep sh .down).UR) at hnot
    have hnotTail : f ∉ List.map eφ as := by
      simpa [kmswStepOfStep, hshUR] using hnot
    have hfGlobal : f ∈ gl.UR := by rw [hglUR]; exact List.mem_cons_of_mem _ hfTail
    have hnotPre' := hnotPre f hnotTail hfTail
    have hnotPreGlobal : f ∉ List.map eφ sh.UR := by
      simpa [hshUR] using hnotPre'
    have hxOld : x < sh.nextEdge := by
      change x < (kmswStepOfStep sh .down).nextEdge at hx
      simpa [kmswStepOfStep, hshUR] using hx
    exact hsim.ur_edge_avoid f hfGlobal hnotPreGlobal x hxOld
  · intro f hf hnot v hv
    change f ∈ (kmswStepOfStep gl .down).UR at hf
    have hfTail : f ∈ bs := by simpa [kmswStepOfStep, hglUR] using hf
    change f ∉ List.map eφ ((kmswStepOfStep sh .down).UR) at hnot
    have hnotTail : f ∉ List.map eφ as := by
      simpa [kmswStepOfStep, hshUR] using hnot
    have hfGlobal : f ∈ gl.UR := by rw [hglUR]; exact List.mem_cons_of_mem _ hfTail
    have hnotPre' := hnotPre f hnotTail hfTail
    have hnotPreGlobal : f ∉ List.map eφ sh.UR := by
      simpa [hshUR] using hnotPre'
    have hvOld : v < sh.nextVertex := by
      change v < (kmswStepOfStep sh .down).nextVertex at hv
      simpa [kmswStepOfStep, hshUR] using hv
    have havoid := hsim.ur_east_avoid f hfGlobal hnotPreGlobal v hvOld
    change vφ v ≠ (kmswStepOfStep gl .down).east f
    simpa [kmswStepOfStep, hglUR, State.addEdge] using havoid
  · intro f hf hnot x hx
    change f ∈ (kmswStepOfStep gl .down).UL.dropLast.reverse at hf
    change f ∉ List.map eφ ((kmswStepOfStep sh .down).UL.dropLast.reverse) at hnot
    rw [hglPred] at hf
    simp only [List.mem_cons] at hf
    rcases hf with hhead | htail
    · subst f
      have hmem : gl.active ∈ List.map eφ
          ((kmswStepOfStep sh .down).UL.dropLast.reverse) := by
        rw [hmapPred]
        simp
      exact False.elim (hnot hmem)
    · have hnotTail : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
        intro hm
        apply hnot
        rw [hmapPred]
        exact List.mem_cons_of_mem _ hm
      have hxOld : x < sh.nextEdge := by
        change x < (kmswStepOfStep sh .down).nextEdge at hx
        simpa [kmswStepOfStep, hshUR] using hx
      exact hsim.ul_edge_avoid f htail hnotTail x hxOld
  · intro f hf hnot v hv
    change f ∈ (kmswStepOfStep gl .down).UL.dropLast.reverse at hf
    change f ∉ List.map eφ ((kmswStepOfStep sh .down).UL.dropLast.reverse) at hnot
    rw [hglPred] at hf
    simp only [List.mem_cons] at hf
    rcases hf with hhead | htail
    · subst f
      have hmem : gl.active ∈ List.map eφ
          ((kmswStepOfStep sh .down).UL.dropLast.reverse) := by
        rw [hmapPred]
        simp
      exact False.elim (hnot hmem)
    · have hnotTail : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
        intro hm
        apply hnot
        rw [hmapPred]
        exact List.mem_cons_of_mem _ hm
      have hvOld : v < sh.nextVertex := by
        change v < (kmswStepOfStep sh .down).nextVertex at hv
        simpa [kmswStepOfStep, hshUR] using hv
      have havoid := hsim.ul_west_avoid f htail hnotTail v hvOld
      change vφ v ≠ (kmswStepOfStep gl .down).west f
      simpa [kmswStepOfStep, hglUR, State.addEdge] using havoid

/-- A matched up step preserves the full avoidance-aware simulation at finite
stages. The new mapped IDs lie beyond every edge in either old boundary -/
theorem kmswShiftSim2_step_up
    (u w : ℕ → Fin 3) (m n : ℕ) (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ) :
    Sim2 (kmswStepOfStep (kmswStage u m) .up)
      (kmswStepOfStep (kmswStage w n) .up)
      (kmswShiftUpEdgeMap (kmswStage u m) (kmswStage w n) eφ)
      (kmswShiftUpVertexMap (kmswStage u m) (kmswStage w n) vφ) := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftUpEdgeMap sh gl eφ
  let vψ := kmswShiftUpVertexMap sh gl vφ
  have hshActive : sh.active < sh.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u m).1
  have hshEndpoints : ∀ e, e < sh.nextEdge →
      sh.west e < sh.nextVertex ∧ sh.east e < sh.nextVertex := by
    intro e he
    exact kmswStage_endpoints_lt_nextVertex u m e he
  have hshUR : ∀ e ∈ sh.UR, e < sh.nextEdge := by
    intro e he
    exact kmswShift_stage_UR_bound u m e he
  have hshPred : ∀ e ∈ sh.UL.dropLast.reverse, e < sh.nextEdge := by
    intro e he
    exact kmswShift_stage_ULpred_bound u m e he
  have hsimStep : Sim (kmswStepOfStep sh .up) (kmswStepOfStep gl .up) eψ vψ :=
    kmswShiftSim_step_up sh gl eφ vφ hshActive hshEndpoints hshUR hshPred hsim.sim
  have hshURPost : (kmswStepOfStep sh .up).UR = (sh.nextEdge + 1) :: sh.UR := by
    simp [kmswStepOfStep, State.addEdge]
  have hglURPost : (kmswStepOfStep gl .up).UR = (gl.nextEdge + 1) :: gl.UR := by
    simp [kmswStepOfStep, State.addEdge]
  have hshPredPost : (kmswStepOfStep sh .up).UL.dropLast.reverse =
      sh.UL.dropLast.reverse := by
    simp [kmswStepOfStep, State.addEdge]
  have hglPredPost : (kmswStepOfStep gl .up).UL.dropLast.reverse =
      gl.UL.dropLast.reverse := by
    simp [kmswStepOfStep, State.addEdge]
  have hmapUR : List.map eψ sh.UR = List.map eφ sh.UR := by
    apply List.map_congr_left
    intro e he
    have hb := hshUR e he
    have hne0 : e ≠ sh.nextEdge := by omega
    have hne1 : e ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftUpEdgeMap, hne0, hne1]
  have hmapPred : List.map eψ (sh.UL.dropLast.reverse) =
      List.map eφ (sh.UL.dropLast.reverse) := by
    apply List.map_congr_left
    intro e he
    have hb := hshPred e he
    have hne0 : e ≠ sh.nextEdge := by omega
    have hne1 : e ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftUpEdgeMap, hne0, hne1]
  refine ⟨hsimStep, ?_, ?_, ?_, ?_⟩
  · intro f hf hnot x hx
    change f ∈ (kmswStepOfStep gl .up).UR at hf
    change f ∉ List.map eψ ((kmswStepOfStep sh .up).UR) at hnot
    have hfParts : f = gl.nextEdge + 1 ∨ f ∈ gl.UR := by
      rw [hglURPost] at hf
      simpa using hf
    have hnotParts : f ≠ gl.nextEdge + 1 ∧ f ∉ List.map eφ sh.UR := by
      rw [hshURPost, List.map_cons, hmapUR] at hnot
      simpa [eψ, kmswShiftUpEdgeMap] using hnot
    rcases hfParts with hfHead | hfTail
    · exact False.elim (hnotParts.1 hfHead)
    · have hxCases : x < sh.nextEdge ∨ x = sh.nextEdge ∨
          x = sh.nextEdge + 1 := by
        change x < (kmswStepOfStep sh .up).nextEdge at hx
        simp [kmswStepOfStep, State.addEdge] at hx
        omega
      rcases hxCases with hxOld | hxActive | hxUR
      · have hxNotSecond : x ≠ sh.nextEdge + 1 := by omega
        have hAvoid := hsim.ur_edge_avoid f hfTail hnotParts.2 x hxOld
        change eψ x ≠ f
        simpa [eψ, kmswShiftUpEdgeMap, ne_of_lt hxOld, hxNotSecond] using hAvoid
      · subst x
        have hbound := kmswShift_stage_UR_bound w n f hfTail
        change eψ sh.nextEdge ≠ f
        simpa [eψ, kmswShiftUpEdgeMap] using (ne_of_lt hbound).symm
      · subst x
        have hbound := kmswShift_stage_UR_bound w n f hfTail
        change eψ (sh.nextEdge + 1) ≠ f
        simpa [eψ, kmswShiftUpEdgeMap] using
          (ne_of_lt (Nat.lt_succ_of_lt hbound)).symm
  · intro f hf hnot v hv
    change f ∈ (kmswStepOfStep gl .up).UR at hf
    change f ∉ List.map eψ ((kmswStepOfStep sh .up).UR) at hnot
    have hfParts : f = gl.nextEdge + 1 ∨ f ∈ gl.UR := by
      rw [hglURPost] at hf
      simpa using hf
    have hnotParts : f ≠ gl.nextEdge + 1 ∧ f ∉ List.map eφ sh.UR := by
      rw [hshURPost, List.map_cons, hmapUR] at hnot
      simpa [eψ, kmswShiftUpEdgeMap] using hnot
    rcases hfParts with hfHead | hfTail
    · exact False.elim (hnotParts.1 hfHead)
    · have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
        change v < (kmswStepOfStep sh .up).nextVertex at hv
        simp [kmswStepOfStep, State.addEdge] at hv
        omega
      rcases hvCases with hvOld | hvNew
      · have hfBound := kmswShift_stage_UR_bound w n f hfTail
        have hfNotG : f ≠ gl.nextEdge := ne_of_lt hfBound
        have hfNotG1 : f ≠ gl.nextEdge + 1 :=
          ne_of_lt (Nat.lt_succ_of_lt hfBound)
        have hAvoid := hsim.ur_east_avoid f hfTail hnotParts.2 v hvOld
        change vψ v ≠ (kmswStepOfStep gl .up).east f
        simpa [vψ, kmswShiftUpVertexMap, kmswStepOfStep, State.addEdge,
          ne_of_lt hvOld, hfNotG, hfNotG1] using hAvoid
      · subst v
        have hfBound := kmswShift_stage_UR_bound w n f hfTail
        have hend := kmswStage_endpoints_lt_nextVertex w n f hfBound
        have hfNotG : f ≠ gl.nextEdge := ne_of_lt hfBound
        have hfNotG1 : f ≠ gl.nextEdge + 1 :=
          ne_of_lt (Nat.lt_succ_of_lt hfBound)
        change vψ sh.nextVertex ≠ (kmswStepOfStep gl .up).east f
        simpa [vψ, kmswShiftUpVertexMap, kmswStepOfStep, State.addEdge,
          hfNotG, hfNotG1] using
          (ne_of_lt hend.2).symm
  · intro f hf hnot x hx
    change f ∈ (kmswStepOfStep gl .up).UL.dropLast.reverse at hf
    change f ∉ List.map eψ ((kmswStepOfStep sh .up).UL.dropLast.reverse) at hnot
    rw [hglPredPost] at hf
    rw [hshPredPost, hmapPred] at hnot
    have hnotOld : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
      exact hnot
    have hxCases : x < sh.nextEdge ∨ x = sh.nextEdge ∨
        x = sh.nextEdge + 1 := by
      change x < (kmswStepOfStep sh .up).nextEdge at hx
      simp [kmswStepOfStep, State.addEdge] at hx
      omega
    rcases hxCases with hxOld | hxActive | hxUR
    · have hxNotSecond : x ≠ sh.nextEdge + 1 := by omega
      have hAvoid := hsim.ul_edge_avoid f hf hnotOld x hxOld
      change eψ x ≠ f
      simpa [eψ, kmswShiftUpEdgeMap, ne_of_lt hxOld, hxNotSecond] using hAvoid
    · subst x
      have hfBound := kmswShift_stage_ULpred_bound w n f hf
      change eψ sh.nextEdge ≠ f
      simpa [eψ, kmswShiftUpEdgeMap] using (ne_of_lt hfBound).symm
    · subst x
      have hfBound := kmswShift_stage_ULpred_bound w n f hf
      change eψ (sh.nextEdge + 1) ≠ f
      simpa [eψ, kmswShiftUpEdgeMap] using
        (ne_of_lt (Nat.lt_succ_of_lt hfBound)).symm
  · intro f hf hnot v hv
    change f ∈ (kmswStepOfStep gl .up).UL.dropLast.reverse at hf
    change f ∉ List.map eψ ((kmswStepOfStep sh .up).UL.dropLast.reverse) at hnot
    rw [hglPredPost] at hf
    rw [hshPredPost, hmapPred] at hnot
    have hnotOld : f ∉ List.map eφ (sh.UL.dropLast.reverse) := by
      exact hnot
    have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
      change v < (kmswStepOfStep sh .up).nextVertex at hv
      simp [kmswStepOfStep, State.addEdge] at hv
      omega
    rcases hvCases with hvOld | hvNew
    · have hfBound := kmswShift_stage_ULpred_bound w n f hf
      have hfNotG : f ≠ gl.nextEdge := ne_of_lt hfBound
      have hfNotG1 : f ≠ gl.nextEdge + 1 :=
        ne_of_lt (Nat.lt_succ_of_lt hfBound)
      have hAvoid := hsim.ul_west_avoid f hf hnotOld v hvOld
      change vψ v ≠ (kmswStepOfStep gl .up).west f
      simpa [vψ, kmswShiftUpVertexMap, kmswStepOfStep, State.addEdge,
        ne_of_lt hvOld, hfNotG, hfNotG1] using hAvoid
    · subst v
      have hfBound := kmswShift_stage_ULpred_bound w n f hf
      have hend := kmswStage_endpoints_lt_nextVertex w n f hfBound
      have hfNotG : f ≠ gl.nextEdge := ne_of_lt hfBound
      have hfNotG1 : f ≠ gl.nextEdge + 1 :=
        ne_of_lt (Nat.lt_succ_of_lt hfBound)
      change vψ sh.nextVertex ≠ (kmswStepOfStep gl .up).west f
      simpa [vψ, kmswShiftUpVertexMap, kmswStepOfStep, State.addEdge,
        hfNotG, hfNotG1] using
        (ne_of_lt hend.1).symm

/-- The left mismatch step preserves `Sim` when the shifted stage has no UL
predecessor and the global stage consumes its nearest predecessor -/
theorem kmswShiftSim_step_left_mismatch
    (u w : ℕ → Fin 3) (m n : ℕ) (e : ℕ) (es : List ℕ)
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim2 (kmswStage u m) (kmswStage w n) eφ vφ)
    (hshPred : (kmswStage u m).UL.dropLast.reverse = [])
    (hglPred : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    Sim (kmswStepOfStep (kmswStage u m) .left)
      (kmswStepOfStep (kmswStage w n) .left)
      (kmswShiftLeftMismatchEdgeMap (kmswStage u m) (kmswStage w n) e eφ)
      (kmswShiftLeftMismatchVertexMap (kmswStage u m) (kmswStage w n) e vφ) := by
  let sh := kmswStage u m
  let gl := kmswStage w n
  let eψ := kmswShiftLeftMismatchEdgeMap sh gl e eφ
  let vψ := kmswShiftLeftMismatchVertexMap sh gl e vφ
  change sh.UL.dropLast.reverse = [] at hshPred
  change gl.UL.dropLast.reverse = e :: es at hglPred
  change Sim (kmswStepOfStep sh .left) (kmswStepOfStep gl .left) eψ vψ
  have hact : sh.active < sh.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u m).1
  have heBound : e < gl.nextEdge := by
    have heMem : e ∈ gl.UL.dropLast.reverse := by rw [hglPred]; simp
    exact kmswShift_stage_ULpred_bound w n e heMem
  have heNotMap : e ∉ List.map eφ sh.UL.dropLast.reverse := by
    simp [hshPred]
  have hactiveInc := hsim.sim.incidence sh.active hact
  rw [hsim.sim.active] at hactiveInc
  have hshEndpoints := kmswStage_endpoints_lt_nextVertex u m sh.active hact
  have heEndpoints := kmswStage_endpoints_lt_nextVertex w n e heBound
  have hpredInc := kmswShift_stage_ULpred_head_incidence w n e es hglPred
  have hmapUR : List.map eψ sh.UR = List.map eφ sh.UR := by
    apply List.map_congr_left
    intro f hf
    have hfBound := kmswShift_stage_UR_bound u m f hf
    change f < sh.nextEdge at hfBound
    have hne0 : f ≠ sh.nextEdge := by omega
    have hne1 : f ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftLeftMismatchEdgeMap, hne0, hne1]
  have hshPostPred : (kmswStepOfStep sh .left).UL.dropLast.reverse = [] := by
    simp [kmswStepOfStep, hshPred, State.addEdge]
  have hglPostPred : (kmswStepOfStep gl .left).UL.dropLast.reverse = es := by
    simp [kmswStepOfStep, hglPred, State.addEdge]
  have hmapOldEdge (f : ℕ) (hf : f < sh.nextEdge) : eψ f = eφ f := by
    have hne0 : f ≠ sh.nextEdge := by omega
    have hne1 : f ≠ sh.nextEdge + 1 := by omega
    simp [eψ, kmswShiftLeftMismatchEdgeMap, hne0, hne1]
  have hmapActiveEdge : eψ sh.nextEdge = gl.nextEdge := by
    simp [eψ, kmswShiftLeftMismatchEdgeMap]
  have hmapMissingEdge : eψ (sh.nextEdge + 1) = e := by
    simp [eψ, kmswShiftLeftMismatchEdgeMap]
  have hmapOldVertex (v : ℕ) (hv : v < sh.nextVertex) : vψ v = vφ v := by
    have hne : v ≠ sh.nextVertex := by omega
    simp [vψ, kmswShiftLeftMismatchVertexMap, hne]
  have hmapFreshVertex : vψ sh.nextVertex = gl.west e := by
    simp [vψ, kmswShiftLeftMismatchVertexMap]
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
  · intro f hf
    have hfCases : f < sh.nextEdge ∨ f = sh.nextEdge ∨ f = sh.nextEdge + 1 := by
      simp [kmswStepOfStep, hshPred, State.addEdge] at hf
      omega
    rcases hfCases with hfOld | hfActive | hfMissing
    · have hb := hsim.sim.edge_bound f hfOld
      have hpost := Nat.lt_succ_of_lt hb
      simpa [kmswStepOfStep, hglPred, State.addEdge, hmapOldEdge f hfOld] using hpost
    · subst f
      have hpost : gl.nextEdge < gl.nextEdge + 1 := Nat.lt_succ_self _
      simpa [kmswStepOfStep, hshPred, hglPred, State.addEdge,
        hmapActiveEdge] using hpost
    · subst f
      have hpost : e < gl.nextEdge + 1 := Nat.lt_succ_of_lt heBound
      simpa [kmswStepOfStep, hshPred, hglPred, State.addEdge,
        hmapMissingEdge] using hpost
  · intro f g hf hg hEq
    have hclass (x : ℕ) (hx : x < sh.nextEdge + 2) :
        x < sh.nextEdge ∨ x = sh.nextEdge ∨ x = sh.nextEdge + 1 := by omega
    have hf' : f < sh.nextEdge + 2 := by
      simp [kmswStepOfStep, hshPred, State.addEdge] at hf
      omega
    have hg' : g < sh.nextEdge + 2 := by
      simp [kmswStepOfStep, hshPred, State.addEdge] at hg
      omega
    rcases hclass f hf' with hfOld | hfActive | hfMissing <;>
      rcases hclass g hg' with hgOld | hgActive | hgMissing
    · have hneF0 : f ≠ sh.nextEdge := by omega
      have hneF1 : f ≠ sh.nextEdge + 1 := by omega
      have hneG0 : g ≠ sh.nextEdge := by omega
      have hneG1 : g ≠ sh.nextEdge + 1 := by omega
      have hEqOld : eφ f = eφ g := by
        calc
          eφ f = eψ f := (hmapOldEdge f hfOld).symm
          _ = eψ g := hEq
          _ = eφ g := hmapOldEdge g hgOld
      exact hsim.sim.edge_injective f g hfOld hgOld hEqOld
    · have hEq' : eφ f = gl.nextEdge := by
        calc
          eφ f = eψ f := (hmapOldEdge f hfOld).symm
          _ = eψ g := hEq
          _ = gl.nextEdge := by simpa [hgActive] using hmapActiveEdge
      have hb := hsim.sim.edge_bound f hfOld
      exact False.elim ((ne_of_lt hb) hEq')
    · have hEq' : eφ f = e := by
        calc
          eφ f = eψ f := (hmapOldEdge f hfOld).symm
          _ = eψ g := hEq
          _ = e := by simpa [hgMissing] using hmapMissingEdge
      have havoid := hsim.ul_edge_avoid e (by rw [hglPred]; simp) heNotMap f hfOld
      exact False.elim (havoid hEq')
    · have hEq' : eφ g = gl.nextEdge := by
        calc
          eφ g = eψ g := (hmapOldEdge g hgOld).symm
          _ = eψ f := hEq.symm
          _ = gl.nextEdge := by simpa [hfActive] using hmapActiveEdge
      have hb := hsim.sim.edge_bound g hgOld
      exact False.elim ((ne_of_lt hb) hEq')
    · cases hfActive; cases hgActive; rfl
    · have hEq' : gl.nextEdge = e := by
        calc
          gl.nextEdge = eψ f := by simpa [hfActive] using hmapActiveEdge.symm
          _ = eψ g := hEq
          _ = e := by simpa [hgMissing] using hmapMissingEdge
      exact False.elim ((ne_of_lt heBound) hEq'.symm)
    · have hEq' : eφ g = e := by
        calc
          eφ g = eψ g := (hmapOldEdge g hgOld).symm
          _ = eψ f := hEq.symm
          _ = e := by simpa [hfMissing] using hmapMissingEdge
      have havoid := hsim.ul_edge_avoid e (by rw [hglPred]; simp) heNotMap g hgOld
      exact False.elim (havoid hEq')
    · have hEq' : gl.nextEdge = e := by
        calc
          gl.nextEdge = eψ g := by simpa [hgActive] using hmapActiveEdge.symm
          _ = eψ f := hEq.symm
          _ = e := by simpa [hfMissing] using hmapMissingEdge
      exact False.elim ((ne_of_lt heBound).symm hEq')
    · cases hfMissing; cases hgMissing; rfl
  · intro v hv
    have hvCases : v < sh.nextVertex ∨ v = sh.nextVertex := by
      simp [kmswStepOfStep, hshPred, State.addEdge] at hv
      omega
    rcases hvCases with hvOld | rfl
    · have hb := hsim.sim.vertex_bound v hvOld
      simpa [kmswStepOfStep, hglPred, State.addEdge, hmapOldVertex v hvOld] using hb
    · have heW : gl.west e < gl.nextVertex := by
        change (kmswStage w n).west e < (kmswStage w n).nextVertex
        exact heEndpoints.1
      simpa [kmswStepOfStep, hglPred, State.addEdge, hmapFreshVertex] using heW
  · intro v z hv hz hEq
    have hclass (x : ℕ) (hx : x < sh.nextVertex + 1) :
        x < sh.nextVertex ∨ x = sh.nextVertex := by omega
    have hv' : v < sh.nextVertex + 1 := by
      simp [kmswStepOfStep, hshPred, State.addEdge] at hv
      omega
    have hz' : z < sh.nextVertex + 1 := by
      simp [kmswStepOfStep, hshPred, State.addEdge] at hz
      omega
    rcases hclass v hv' with hvOld | hvNew <;>
      rcases hclass z hz' with hzOld | hzNew
    · have hneV : v ≠ sh.nextVertex := by omega
      have hneZ : z ≠ sh.nextVertex := by omega
      have hEqOld : vφ v = vφ z := by
        calc
          vφ v = vψ v := (hmapOldVertex v hvOld).symm
          _ = vψ z := hEq
          _ = vφ z := hmapOldVertex z hzOld
      exact hsim.sim.vertex_injective v z hvOld hzOld hEqOld
    · have hEq' : vφ v = gl.west e := by
        calc
          vφ v = vψ v := (hmapOldVertex v hvOld).symm
          _ = vψ z := hEq
          _ = gl.west e := by simpa [hzNew] using hmapFreshVertex
      have havoid := hsim.ul_west_avoid e (by rw [hglPred]; simp) heNotMap v hvOld
      exact False.elim (havoid hEq')
    · have hEq' : vφ z = gl.west e := by
        calc
          vφ z = vψ z := (hmapOldVertex z hzOld).symm
          _ = vψ v := hEq.symm
          _ = gl.west e := by simpa [hvNew] using hmapFreshVertex
      have havoid := hsim.ul_west_avoid e (by rw [hglPred]; simp) heNotMap z hzOld
      exact False.elim (havoid hEq')
    · omega
  · simp [kmswStepOfStep, hshPred, hglPred, eψ,
      kmswShiftLeftMismatchEdgeMap, State.addEdge]
  · intro f hf
    have hfCases : f < sh.nextEdge ∨ f = sh.nextEdge ∨ f = sh.nextEdge + 1 := by
      simp [kmswStepOfStep, hshPred, State.addEdge] at hf
      omega
    rcases hfCases with hfOld | hfActive | hfMissing
    · have hfEnds := kmswStage_endpoints_lt_nextVertex u m f hfOld
      change sh.west f < sh.nextVertex ∧ sh.east f < sh.nextVertex at hfEnds
      have hne0 : f ≠ sh.nextEdge := by omega
      have hne1 : f ≠ sh.nextEdge + 1 := by omega
      have hneW : sh.west f ≠ sh.nextVertex := by omega
      have hneE : sh.east f ≠ sh.nextVertex := by omega
      have hbound := hsim.sim.edge_bound f hfOld
      have hneTarget : eφ f ≠ gl.nextEdge := ne_of_lt hbound
      have hwestMap := hmapOldVertex (sh.west f) hfEnds.1
      have heastMap := hmapOldVertex (sh.east f) hfEnds.2
      simpa [kmswStepOfStep, hshPred, hglPred, State.addEdge, eψ, vψ,
        kmswShiftLeftMismatchEdgeMap, kmswShiftLeftMismatchVertexMap,
        hne0, hne1, hneW, hneE, hneTarget, hmapOldEdge f hfOld,
        hwestMap, heastMap] using hsim.sim.incidence f hfOld
    · subst f
      have hneEast : sh.east sh.active ≠ sh.nextVertex := by
        change (kmswStage u m).east sh.active ≠ (kmswStage u m).nextVertex
        omega
      constructor
      · simp only [kmswStepOfStep, hshPred, hglPred, State.addEdge, eψ,
          kmswShiftLeftMismatchEdgeMap, vψ, kmswShiftLeftMismatchVertexMap]
        simp [hneEast]
      · simp [kmswStepOfStep, hshPred, hglPred, State.addEdge, eψ,
          kmswShiftLeftMismatchEdgeMap, vψ, kmswShiftLeftMismatchVertexMap,
          hneEast]
        exact hactiveInc.2
    · subst f
      have hneFresh : sh.nextEdge + 1 ≠ sh.nextEdge := by omega
      have hneE : e ≠ gl.nextEdge := by omega
      have hneW : sh.west sh.active ≠ sh.nextVertex := by
        change (kmswStage u m).west sh.active ≠ (kmswStage u m).nextVertex
        omega
      constructor
      · simp [kmswStepOfStep, hshPred, hglPred, State.addEdge, eψ,
          kmswShiftLeftMismatchEdgeMap, vψ, kmswShiftLeftMismatchVertexMap,
          hneFresh, hneE, hneW]
      · have hleft : (kmswStepOfStep gl .left).east (eψ (sh.nextEdge + 1)) =
            gl.east e := by
          simp [kmswStepOfStep, hglPred, State.addEdge, eψ,
            kmswShiftLeftMismatchEdgeMap, hneFresh, hneE]
        have hright : vψ ((kmswStepOfStep sh .left).east (sh.nextEdge + 1)) =
            vφ (sh.west sh.active) := by
          simp [kmswStepOfStep, hshPred, State.addEdge, vψ,
            kmswShiftLeftMismatchVertexMap, hneFresh, hneW]
        rw [hleft, hright]
        exact hpredInc.trans hactiveInc.1
  · intro f hf hp
    have hfCases : f < sh.nextEdge ∨ f = sh.nextEdge ∨ f = sh.nextEdge + 1 := by
      simp [kmswStepOfStep, hshPred, State.addEdge] at hf
      omega
    rcases hfCases with hfOld | hfActive | hfMissing
    · have hne0 : f ≠ sh.nextEdge := by omega
      have hne1 : f ≠ sh.nextEdge + 1 := by omega
      have hpresOld : sh.present f = true := by
        simpa [kmswStepOfStep, hshPred, State.addEdge, hne0, hne1] using hp
      have hpres := hsim.sim.present f hfOld (by
        exact hpresOld)
      have hbound := hsim.sim.edge_bound f hfOld
      have hneTarget : eφ f ≠ gl.nextEdge := ne_of_lt hbound
      simpa [kmswStepOfStep, hglPred, State.addEdge, eψ,
        kmswShiftLeftMismatchEdgeMap, hne0, hne1, hneTarget,
        hmapOldEdge f hfOld] using hpres
    · subst f
      simp [kmswStepOfStep, hshPred, hglPred, State.addEdge, eψ,
        kmswShiftLeftMismatchEdgeMap]
    · subst f
      simp [kmswStepOfStep, hshPred, State.addEdge] at hp
  · simp only [kmswStepOfStep, hshPred, hglPred, State.addEdge]
    rw [hmapUR]
    exact hsim.sim.ur_prefix
  · rw [hshPostPred, hglPostPred]
    exact List.nil_prefix

end DirectedDistances.KMSW
