/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWBoundaryPrefix
public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier
public import DirectedDistances.PlanarMap.KMSWMapChanneled
public import DirectedDistances.KMSW.KMSWForwardClass
import DirectedDistances.KMSW.StageSubgraph

/-! # Final lower-right boundary prefix

result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem kmswStep_LR_append (s : State) (c : Fin 3) :
    ∃ xs, (kmswStep s c).LR = s.LR ++ xs := by
  fin_cases c
  · cases h : s.UL.dropLast.reverse with
    | nil => exact ⟨[], by simp [kmswStep, kmswCodeStep, kmswStepOfStep,
        h, State.addEdge]⟩
    | cons e es => exact ⟨[], by
        change (kmswStepOfStep s .left).LR = s.LR ++ []
        rw [kmswStepOfStep, h]
        simp only [State.addEdge, List.append_nil]⟩
  · exact ⟨[], by simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]⟩
  · cases h : s.UR with
    | nil => exact ⟨[s.nextEdge], by simp [kmswStep, kmswCodeStep,
        kmswStepOfStep, h, State.addEdge]⟩
    | cons e es => exact ⟨[], by simp [kmswStep, kmswCodeStep,
        kmswStepOfStep, h]⟩

private theorem kmswStage_LR_append (w : ℕ → Fin 3) :
    ∀ m k, m ≤ k → ∃ xs, (kmswStage w k).LR = (kmswStage w m).LR ++ xs := by
  intro m k
  induction k generalizing m with
  | zero =>
      intro hmk
      have hm : m = 0 := by omega
      subst m
      exact ⟨[], by simp [kmswStage]⟩
  | succ k ih =>
      intro hmk
      by_cases hmk' : m ≤ k
      · obtain ⟨xs, hxs⟩ := ih m hmk'
        obtain ⟨ys, hys⟩ := kmswStep_LR_append (kmswStage w k) (w k)
        refine ⟨xs ++ ys, ?_⟩
        simp [kmswStage, hys, hxs, List.append_assoc]
      · have hm : m = k + 1 := by omega
        subst m
        exact ⟨[], by simp [kmswStage]⟩

private theorem kmswWalkClass_r_le_N {r N : ℕ} (hn : 1 ≤ N)
    (c : KMSWWalkClass 1 r N) :
    r ≤ N := by
  have hstep (i : ℕ) :
      -1 ≤ (RandomWalk.lazyTwoDimensionalStep (codeExtend c i)).2 := by
    change -1 ≤ if codeExtend c i = 0 then 0 else
      if codeExtend c i = 1 then 1 else -1
    by_cases h0 : codeExtend c i = 0 <;>
      by_cases h1 : codeExtend c i = 1 <;> simp [h0, h1]
  have hsum : -((N - 1 : ℕ) : ℤ) ≤
      (RandomWalk.integrateCodes (codeExtend c) (N - 1)).2 := by
    have hsum' : -((N - 1 : ℕ) : ℤ) ≤
        ∑ i ∈ Finset.range (N - 1),
          (RandomWalk.lazyTwoDimensionalStep (codeExtend c i)).2 := by
      calc
        -((N - 1 : ℕ) : ℤ) =
            ∑ i ∈ Finset.range (N - 1), (-1 : ℤ) := by simp
        _ ≤ ∑ i ∈ Finset.range (N - 1),
              (RandomWalk.lazyTwoDimensionalStep (codeExtend c i)).2 := by
            apply Finset.sum_le_sum
            intro i hi
            exact hstep i
    simpa [RandomWalk.integrateCodes, Prod.snd_sum] using hsum'
  have hend := congrArg Prod.snd c.property.1
  change (RandomWalk.integrateCodes (codeExtend c) (N - 1)).2 =
      -(r : ℤ) + 1 at hend
  omega

/-- The final lower-right edge list is exactly the chain of IDs `0,…,r−1`
when the walk starts with the required `r−1` code-2 steps. Equivalently, the
right boundary path in the walk-class representative has precisely those
result. -/
theorem kmswWalkClassBase_LR_eq_range_of_downPrefix
    {r N : ℕ} (hn : 1 ≤ N) (hr : 1 ≤ r)
    (c : KMSWWalkClass 1 r N)
    (hpre : ∀ i : Fin (N - 1), i.val < r - 1 → c.1 i = 2) :
    (kmswStage (codeExtend c) (N - 1)).LR = List.range r := by
  have hlength : r - 1 ≤ N - 1 := by
    have hbound := kmswWalkClass_r_le_N hn c
    omega
  have hcodes : ∀ i < r - 1, codeExtend c i = 2 := by
    intro i hi
    rw [codeExtend_of_lt c i (by omega)]
    exact hpre ⟨i, by omega⟩ hi
  have hprefix := kmswStage_allDown_prefix_exactLR (codeExtend c) (r - 1) hcodes
  have hstage : (kmswStage (codeExtend c) (r - 1)).LR = List.range r := by
    simpa [Nat.sub_add_cancel hr] using hprefix.2.2.2.2.1
  obtain ⟨xs, hxs⟩ := kmswStage_LR_append (codeExtend c) (r - 1) (N - 1)
    (by omega)
  have hrunLength :
      (kmswStageLRDartRun (codeExtend c) (N - 1)).length = r :=
    kmswWalkClassBase_rightDartRun_length hn c
  have hlengthFinal : (kmswStage (codeExtend c) (N - 1)).LR.length = r := by
    simpa [kmswStageLRDartRun, stageDarts] using hrunLength
  have hxsLength : xs.length = 0 := by
    rw [hxs, hstage, List.length_append, List.length_range] at hlengthFinal
    omega
  have hxsNil : xs = [] := List.length_eq_zero_iff.mp hxsLength
  rw [hxs, hstage, hxsNil]
  simp

/-- Every edge in that forced lower-right chain keeps its geometric endpoint
labels in the final stage: edge `e` runs from label `e` to label `e+1`.
This identifies the boundary vertices `0,…,r` as well as the edge IDs.
result. -/
theorem kmswWalkClassBase_LR_endpoint_labels_of_downPrefix
    {r N : ℕ} (hn : 1 ≤ N) (hr : 1 ≤ r)
    (c : KMSWWalkClass 1 r N)
    (hpre : ∀ i : Fin (N - 1), i.val < r - 1 → c.1 i = 2)
    (e : ℕ) (he : e < r) :
    (kmswStage (codeExtend c) (N - 1)).west e = e ∧
      (kmswStage (codeExtend c) (N - 1)).east e = e + 1 := by
  have hlength : r - 1 ≤ N - 1 := by
    have hbound := kmswWalkClass_r_le_N hn c
    omega
  have hcodes : ∀ i < r - 1, codeExtend c i = 2 := by
    intro i hi
    rw [codeExtend_of_lt c i (by omega)]
    exact hpre ⟨i, by omega⟩ hi
  have hprefix := kmswStage_allDown_prefix_exactLR (codeExtend c) (r - 1) hcodes
  have hgeometry := hprefix.2.2.2.2.2.2.2 e (by rw [hprefix.1]; omega)
  rcases hgeometry with ⟨_, hw, heast, _⟩
  have hstable := kmswStage_endpoints_stable (codeExtend c)
    (m := r - 1) (n := N - 1) (e := e) (by omega)
    (by rw [hprefix.1]; omega)
  exact ⟨hstable.1.trans hw, hstable.2.trans heast⟩

/-- The representative's right boundary path is exactly the lower-right run
after opposing and reversing its path darts, and that run is the forced chain
with edge IDs `0,…,r−1`. Together with
`kmswWalkClassBase_LR_endpoint_labels_of_downPrefix`, this identifies the
chain's geometric endpoints. Helper toward `lem-kmsw-left`
S7-count: `r−1` forced steps); not the paper result. -/
theorem kmswWalkClassBase_rightPath_run_of_downPrefix
    {r N : ℕ} (hn : 1 ≤ N) (hr : 1 ≤ r)
    (c : KMSWWalkClass 1 r N)
    (hpre : ∀ i : Fin (N - 1), i.val < r - 1 → c.1 i = 2) :
    ∃ Q : SimpleDirectedDartPath
        (kmswStageDirectedMap (codeExtend c) (N - 1))
        (kmswWalkClassBaseSource c) (kmswWalkClassBaseSink c) r,
      Q.darts.reverse.map
        (kmswStageDirectedMap (codeExtend c) (N - 1)).toCombinatorialMap.edgeInv =
          kmswStageLRDartRun (codeExtend c) (N - 1) ∧
      (kmswStage (codeExtend c) (N - 1)).LR = List.range r := by
  obtain ⟨_, Q, _, hQ⟩ := kmswWalkClassBase_paths hn c
  exact ⟨Q, hQ, kmswWalkClassBase_LR_eq_range_of_downPrefix hn hr c hpre⟩

private theorem kmswStage_prefix_UR_ids_ge (w : ℕ → Fin 3) {r : ℕ}
    (hr : 1 ≤ r) (hcodes : ∀ i < r - 1, w i = 2)
    {m : ℕ} (hm : r - 1 ≤ m) {e : ℕ}
    (heUR : e ∈ (kmswStage w m).UR) : r ≤ e := by
  by_contra he
  have helow : e < r := by omega
  obtain ⟨hnext, _, _, _, _, _, _, hedge⟩ :=
    kmswStage_allDown_prefix_exactLR w (r - 1) hcodes
  have heprev : e < (kmswStage w (r - 1)).nextEdge := by
    rw [hnext]
    omega
  have hp0 : (kmswStage w (r - 1)).present e = true := (hedge e heprev).2.2.2
  have hp := (present_mono w heprev hp0 m hm).2
  have hefinal : e < (kmswStage w m).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w m).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr heUR)))
  have hfalse := ((kmswStage_status w m).1 e hefinal).2 (Or.inl heUR)
  rw [hp] at hfalse
  cases hfalse

private theorem kmswStep_prefix_east_lower_bound {r : ℕ} (s : State)
    (t : Step) (hrActive : r ≤ s.east s.active)
    (hrVertex : r ≤ s.nextVertex)
    (hURbound : ∀ e ∈ s.UR, e < s.nextEdge)
    (hOld : ∀ e, e < s.nextEdge →
      ((r ≤ e ∧ s.present e = true) ∨ e ∈ s.UR) → r ≤ s.east e) :
    r ≤ (kmswStepOfStep s t).east (kmswStepOfStep s t).active ∧
      ∀ e, r ≤ e → e < (kmswStepOfStep s t).nextEdge →
        ((kmswStepOfStep s t).present e = true ∨ e ∈ (kmswStepOfStep s t).UR) →
          r ≤ (kmswStepOfStep s t).east e := by
  cases t with
  | down =>
      cases hUR : s.UR with
      | nil =>
          constructor
          · simpa [kmswStepOfStep, hUR, State.addEdge] using hrVertex
          · intro e hre he hmem
            by_cases hnew : e = s.nextEdge
            · subst e
              simp [kmswStepOfStep, hUR, State.addEdge] at hmem ⊢
              exact hrVertex
            · have heOld : e < s.nextEdge := by
                have he' := he
                simp [kmswStepOfStep, hUR, State.addEdge] at he'
                omega
              have hp : s.present e = true := by
                rcases hmem with hp | hm
                · simpa [kmswStepOfStep, hUR, State.addEdge, hnew] using hp
                · simp [kmswStepOfStep, hUR, State.addEdge] at hm
              have h := hOld e heOld (Or.inl ⟨hre, hp⟩)
              simpa [kmswStepOfStep, hUR, State.addEdge, hnew] using h
      | cons a as =>
          have ha : a < s.nextEdge := hURbound a (by simp [hUR])
          have hActive := hOld a ha (Or.inr (by simp [hUR]))
          constructor
          · simpa [kmswStepOfStep, hUR, State.addEdge] using hActive
          · intro e hre he hmem
            have heOld : e < s.nextEdge := by
              have he' : e < (kmswStepOfStep s Step.down).nextEdge := he
              simpa [kmswStepOfStep, hUR, State.addEdge] using he'
            have hmem' : s.present e = true ∨ e ∈ s.UR := by
              rcases hmem with hp | hm
              · by_cases hnew : e = a
                · subst e
                  exact Or.inr (by simp [hUR])
                · left
                  simpa [kmswStepOfStep, hUR, hnew] using hp
              · right
                have hm' : e ∈ as := by
                  simpa [kmswStepOfStep, hUR, State.addEdge] using hm
                rw [hUR]
                exact List.mem_cons_of_mem a hm'
            have hOld' : ((r ≤ e ∧ s.present e = true) ∨ e ∈ s.UR) := by
              rcases hmem' with hp | hm
              · exact Or.inl ⟨hre, hp⟩
              · exact Or.inr hm
            have h := hOld e heOld hOld'
            simpa [kmswStepOfStep, hUR] using h
  | left =>
      cases hUL : s.UL.dropLast.reverse with
      | nil =>
          constructor
          · simpa [kmswStepOfStep, hUL, State.addEdge] using hrActive
          · intro e hre he hmem
            by_cases hnew : e = s.nextEdge
            · subst e
              simp [kmswStepOfStep, hUL, State.addEdge] at hmem ⊢
              exact hrActive
            · by_cases hpend : e = s.nextEdge + 1
              · subst e
                rcases hmem with hp | hm
                · have hp' : (kmswStepOfStep s Step.left).present (s.nextEdge + 1) = false := by
                    simp [kmswStepOfStep, hUL, State.addEdge]
                  rw [hp'] at hp
                  cases hp
                · have hm' : s.nextEdge + 1 ∈ s.UR := by
                    simpa [kmswStepOfStep, hUL, State.addEdge] using hm
                  have := hURbound _ hm'
                  omega
              · have heOld : e < s.nextEdge := by
                  have he' := he
                  simp [kmswStepOfStep, hUL, State.addEdge] at he'
                  omega
                have hmem' : ((r ≤ e ∧ s.present e = true) ∨ e ∈ s.UR) := by
                  rcases hmem with hp | hm
                  · exact Or.inl ⟨hre, by simpa [kmswStepOfStep, hUL, State.addEdge, hnew, hpend] using hp⟩
                  · exact Or.inr (by simpa [kmswStepOfStep, hUL, State.addEdge] using hm)
                have h := hOld e heOld hmem'
                simpa [kmswStepOfStep, hUL, State.addEdge, hnew, hpend] using h
      | cons a as =>
          constructor
          · simpa [kmswStepOfStep, hUL, State.addEdge] using hrActive
          · intro e hre he hmem
            by_cases hnew : e = s.nextEdge
            · subst e
              simp [kmswStepOfStep, hUL, State.addEdge] at hmem ⊢
              exact hrActive
            · have heOld : e < s.nextEdge := by
                have he' := he
                simp [kmswStepOfStep, hUL, State.addEdge] at he'
                omega
              have hmem' : ((r ≤ e ∧ s.present e = true) ∨ e ∈ s.UR) := by
                rcases hmem with hp | hm
                · exact Or.inl ⟨hre, by simpa [kmswStepOfStep, hUL, State.addEdge, hnew] using hp⟩
                · exact Or.inr (by simpa [kmswStepOfStep, hUL, State.addEdge] using hm)
              have h := hOld e heOld hmem'
              simpa [kmswStepOfStep, hUL, State.addEdge, hnew] using h
  | up =>
      constructor
      · simpa [kmswStepOfStep, State.addEdge] using hrVertex
      · intro e hre he hmem
        by_cases hnew : e = s.nextEdge
        · subst e
          simp [kmswStepOfStep, State.addEdge] at hmem ⊢
          exact hrVertex
        · by_cases hpend : e = s.nextEdge + 1
          · subst e
            simp [kmswStepOfStep, State.addEdge] at hmem ⊢
            exact hrActive
          · have heOld : e < s.nextEdge := by
              have he' := he
              simp [kmswStepOfStep, State.addEdge] at he'
              omega
            have hmem' : ((r ≤ e ∧ s.present e = true) ∨ e ∈ s.UR) := by
              rcases hmem with hp | hm
              · exact Or.inl ⟨hre, by simpa [kmswStepOfStep, State.addEdge, hnew, hpend] using hp⟩
              · exact Or.inr (by simpa [kmswStepOfStep, State.addEdge, hnew, hpend] using hm)
            have h := hOld e heOld hmem'
            simpa [kmswStepOfStep, State.addEdge, hnew, hpend] using h

/-- After the forced `r−1` down steps, the active head and every later
edges are included in the stage induction so that activating one preserves
result. -/
theorem kmswStage_activeEast_and_presentEast_ge_of_downPrefix
    (w : ℕ → Fin 3) {r : ℕ}
    (hr : 1 ≤ r) (hcodes : ∀ i < r - 1, w i = 2)
    (m : ℕ) (hm : r - 1 ≤ m) :
    r ≤ (kmswStage w m).east (kmswStage w m).active ∧
      ∀ e, r ≤ e → e < (kmswStage w m).nextEdge →
        ((kmswStage w m).present e = true ∨ e ∈ (kmswStage w m).UR) →
          r ≤ (kmswStage w m).east e := by
  induction m, hm using Nat.le_induction with
  | base =>
      obtain ⟨hnext, _, hactive, _, _, _, _, hedge⟩ :=
        kmswStage_allDown_prefix_exactLR w (r - 1) hcodes
      constructor
      · have he := (hedge (r - 1) (by rw [hnext]; omega)).2.2.1
        rw [hactive]
        omega
      · intro e hre he _
        rw [hnext] at he
        omega
  | succ m hm ih =>
      let s := kmswStage w m
      have hactiveBound : s.active < s.nextEdge := by
        exact (kmswStage_boundary_ids_lt_nextEdge w m).1
      have hvertex : r ≤ s.nextVertex := by
        have hactive : r ≤ s.east s.active := by simpa [s] using ih.1
        have hends := kmswStage_endpoints_lt_nextVertex w m s.active hactiveBound
        have heastBound : s.east s.active < s.nextVertex := by
          simpa [s] using hends.2
        exact (hactive.trans_lt heastBound).le
      have hURbound : ∀ e ∈ s.UR, e < s.nextEdge := by
        intro e he
        exact (kmswStage_boundary_ids_lt_nextEdge w m).2 e (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr he)))
      have hURid : ∀ e ∈ s.UR, r ≤ e := by
        intro e he
        exact kmswStage_prefix_UR_ids_ge w hr hcodes hm he
      have hOld : ∀ e, e < s.nextEdge →
          ((r ≤ e ∧ s.present e = true) ∨ e ∈ s.UR) → r ≤ s.east e := by
        intro e he hmem
        rcases hmem with ⟨hre, hp⟩ | hUR
        · exact ih.2 e hre he (Or.inl hp)
        · exact ih.2 e (hURid e hUR) he (Or.inr hUR)
      have hstep := kmswStep_prefix_east_lower_bound s (kmswCodeStep (w m))
        ih.1 hvertex hURbound hOld
      constructor
      · simpa [s, kmswStage, kmswStep] using hstep.1
      · intro e hre he hmem
        have he' : e < (kmswStepOfStep s (kmswCodeStep (w m))).nextEdge := by
          simpa [s, kmswStage, kmswStep] using he
        have hmem' : (kmswStepOfStep s (kmswCodeStep (w m))).present e = true ∨
            e ∈ (kmswStepOfStep s (kmswCodeStep (w m))).UR := by
          simpa [s, kmswStage, kmswStep] using hmem
        have h := hstep.2 e hre he' hmem'
        simpa [s, kmswStage, kmswStep] using h

/-- The forced lower-right chain keeps labels `e → e+1` at all later stages,
including on edges that have been reactivated after the prefix. Helper toward -/
theorem kmswStage_prefix_edge_labels_of_downPrefix
    (w : ℕ → Fin 3) {r : ℕ} (hr : 1 ≤ r)
    (hcodes : ∀ i < r - 1, w i = 2) {m : ℕ}
    (hm : r - 1 ≤ m) (e : ℕ) (he : e < r) :
    (kmswStage w m).west e = e ∧ (kmswStage w m).east e = e + 1 := by
  obtain ⟨hnext, _, _, _, _, _, _, hedge⟩ :=
    kmswStage_allDown_prefix_exactLR w (r - 1) hcodes
  have he0 : e < (kmswStage w (r - 1)).nextEdge := by
    rw [hnext]
    omega
  have hbase := hedge e he0
  have hstable := kmswStage_endpoints_stable w hm he0
  exact ⟨hstable.1.trans hbase.2.1, hstable.2.trans hbase.2.2.1⟩

end DirectedDistances.KMSW
