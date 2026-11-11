module

public import DirectedDistances.KMSW.PrimedInitialCut
public import DirectedDistances.KMSW.PrimedLPhaseRecode

/-! # Primed within-block step bookkeeping

Partial invariant helpers toward `lem-quad-kmsw`
with β₀, establish ordered boundary correspondence, or prove the paper lemma. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/-- A positive block offset copies a single global code. Offset zero is
the C13 replacement and is deliberately excluded. Partial invariant helper
not the paper lemma. -/
theorem primedCode_positive_offset (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k j : ℕ)
    (hj : 0 < j) (hwidth : j < primedIntervalWidth ω h k) :
    primedCode ω h (primedIntervalBase ω h k + j) =
      (fun i => ω (i + 1)) (primedIntervalLeft ω h k + j - 1) := by
  rw [primedCode_block ω h k j hwidth, ite_eq_right (by omega)]

/-- At a positive offset the next local stage corresponds to global time
`n + 1`, with `n = L_k + j - 1`. Both raw KMSW transitions use the same
letter, for all three letters. This is a time/code helper only, not a
transition of the partial complement invariant or `lem-quad-kmsw` -/
theorem primed_positive_offset_transitions (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k j : ℕ)
    (hj : 0 < j) (hwidth : j < primedIntervalWidth ω h k) :
    let u := primedCode ω h
    let w := fun i => ω (i + 1)
    let m := primedIntervalBase ω h k + j
    let n := primedIntervalLeft ω h k + j - 1
    n + 1 = primedIntervalLeft ω h k + j ∧
    u m = w n ∧
    kmswMissingRootStage u (m + 1) =
      kmswStepOfStep (kmswMissingRootStage u m) (kmswCodeStep (w n)) ∧
    kmswStage w (n + 1) =
      kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n)) := by
  dsimp only
  have hc := primedCode_positive_offset ω h k j hj hwidth
  refine ⟨by omega, hc, ?_, rfl⟩
  rw [kmswMissingRootStage, hc]
  rfl

/-- Coherent allocation maps for the first ordinary triangle following the
C13 triangle. Partial invariant helper for `lem-quad-kmsw` -/
@[expose] def primedSecondTriangleEdgeMap (u w : ℕ → Fin 3) (n : ℕ) : ℕ → ℕ :=
  kmswShiftUpEdgeMap (kmswMissingRootStage u 1) (kmswStage w n)
    (primedFirstStepEdgeMap w n)

/-- Vertex allocation map paired with `primedSecondTriangleEdgeMap`. Partial
invariant helper for `lem-quad-kmsw` -/
@[expose] def primedSecondTriangleVertexMap (u w : ℕ → Fin 3) (n : ℕ) : ℕ → ℕ :=
  kmswShiftUpVertexMap (kmswMissingRootStage u 1) (kmswStage w n)
    (primedFirstStepVertexMap w n)

/-- The first ordinary triangle allocation maps preserve all old images.
Partial invariant helper for `lem-quad-kmsw` -/
theorem primedSecondTriangle_maps_extend (u w : ℕ → Fin 3) (n : ℕ) :
    (∀ e, e < (kmswMissingRootStage u 1).nextEdge →
      primedSecondTriangleEdgeMap u w n e = primedFirstStepEdgeMap w n e) ∧
    (∀ v, v < (kmswMissingRootStage u 1).nextVertex →
      primedSecondTriangleVertexMap u w n v = primedFirstStepVertexMap w n v) := by
  constructor
  · intro e he
    simp only [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro v hv
    simp only [primedSecondTriangleVertexMap, kmswShiftUpVertexMap]
    rw [ite_eq_right (by omega)]

/-- One ordinary up step after the initial C13 triangle preserves the partial
cut invariant. Old cut edges remain on the cut; the two new boundary edges
are global frontier edges. This is only the stages `1 → 2` up case, not an
arbitrary-stage transition, an ordered boundary correspondence, or -/
theorem primedSecondUp_complementSimCut (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu0 : u 0 = 1) (hu1 : u 1 = 1)
    (hw : w (walkNL w h 0) = 1) :
    PrimedComplementSimCut u w h 0 2 (walkNL w h 0 + 1)
      (primedSecondTriangleEdgeMap u w (walkNL w h 0))
      (primedSecondTriangleVertexMap u w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have hdrop : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have hstep : kmswStage w n = kmswStepOfStep s .left :=
    primedInitial_globalExitTransition w h
  have hnext : kmswStage w (n + 1) =
      kmswStepOfStep (kmswStepOfStep s .left) .up := by
    change kmswStep (kmswStage w n) (w n) = _
    rw [hw, hstep]
    rfl
  have ha : s.active < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
  have hv := kmswStage_endpoints_lt_nextVertex w (n - 1) s.active ha
  change s.west s.active < s.nextVertex ∧ s.east s.active < s.nextVertex at hv
  have hne : s.east s.active ≠ s.west s.active := by
    have hn := activeEast_ne_activeInitial w (j := n - 1) (n := n - 1) le_rfl
    have hw' := (edge_endpoints_eq w ha).1
    change s.east s.active ≠ edgeWest w s.active at hn
    rw [← hw'] at hn
    exact hn
  have hlocal : kmswMissingRootStage u 2 =
      kmswStepOfStep (kmswStepOfStep kmswMissingRootInit .up) .up := by
    simp only [kmswMissingRootStage, hu0, hu1]
    rfl
  have hcut : s.active ∈ cutAtExit w h 0 := active_mem_cutAtExit w h 0
  have hemap (e : ℕ) : primedSecondTriangleEdgeMap u w n e =
      if e = 3 then s.nextEdge + 2 else if e = 4 then s.nextEdge + 3
      else if e = 0 then s.nextEdge + 1 else if e = 1 then s.nextEdge
      else if e = 2 then s.active else e := by
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hstep, hdrop, primedFirstStepEdgeMap]
    rfl
  have hvmap (v : ℕ) : primedSecondTriangleVertexMap u w n v =
      if v = 3 then s.nextVertex + 1 else if v = 0 then s.nextVertex
      else if v = 1 then s.west s.active else if v = 2 then s.east s.active
      else v := by
    simp [primedSecondTriangleVertexMap, kmswShiftUpVertexMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hstep, hdrop, primedFirstStepVertexMap]
    rfl
  have hnot : ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w) ⟨s.nextVertex⟩ := by
    have hh := walkNL_activeWest_unreachable w h 0
    change ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (kmswStage w n).active⟩ at hh
    simpa [act, hstep, kmswStepOfStep, hdrop, State.addEdge] using hh
  change PrimedComplementSimCut u w h 0 2 (n + 1)
    (primedSecondTriangleEdgeMap u w n) (primedSecondTriangleVertexMap u w n)
  constructor
  · intro e he
    rw [hlocal] at he
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [hemap, hnext, kmswStepOfStep, hdrop, State.addEdge] <;> omega
  · intro e f he hf hef
    rw [hlocal] at he hf
    have he5 : e < 5 := he
    have hf5 : f < 5 := hf
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    have hd : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      simp [hemap] at hef ⊢ <;> omega
  · intro v hvb
    rw [hlocal] at hvb
    have hv4 : v < 4 := hvb
    have hc : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [hvmap, hnext, kmswStepOfStep, hdrop, State.addEdge] <;> omega
  · intro v z hvb hzb hvz
    rw [hlocal] at hvb hzb
    have hv4 : v < 4 := hvb
    have hz4 : z < 4 := hzb
    have hc : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    have hd : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl <;>
      simp [hvmap] at hvz ⊢ <;> omega
  · intro e he hp
    rw [hlocal] at he hp ⊢
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals simp [hemap, hvmap, hnext, kmswStepOfStep, hdrop, State.addEdge,
      kmswMissingRootInit, kmswInit, Nat.add_assoc]
  · intro e he hp
    rw [hlocal] at he hp ⊢
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    have ha0 : s.active ≠ s.nextEdge := by omega
    have ha1 : s.active ≠ s.nextEdge + 1 := by omega
    have ha2 : s.active ≠ s.nextEdge + 2 := by omega
    have ha3 : s.active ≠ s.nextEdge + 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals simp [hemap, hvmap, hnext, kmswStepOfStep, hdrop, State.addEdge,
      kmswMissingRootInit, kmswInit, ha0, ha1, ha2, ha3]
    exact Multiset.pair_comm _ _
  · intro e he hp
    rw [hlocal] at he hp
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals constructor
    all_goals try { solve | simp [hemap, hnext, kmswStepOfStep, hdrop,
      State.addEdge, Nat.add_assoc] }
    all_goals intro hh
    all_goals apply hnot
    all_goals simpa [hemap, hnext, kmswStepOfStep, hdrop, State.addEdge,
      Nat.add_assoc] using hh.2.2.1
  · rw [hlocal]
    simp [hemap, hnext, kmswStepOfStep, hdrop, kmswMissingRootInit, kmswInit,
      State.addEdge]
  · intro a b c hab
    rw [hlocal] at hab
    have hc : (a, b, c) = (0, 1, 2) ∨ (a, b, c) = (1, 3, 4) := by
      simpa [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] using hab
    rcases hc with hc | hc <;> cases hc
    · refine ⟨s.active, s.nextEdge, s.nextEdge + 1, ?_, ?_⟩
      · simp [hnext, kmswStepOfStep, hdrop]
      · simp [hemap, Multiset.cons_swap]
        exact Multiset.pair_comm _ _
    · refine ⟨s.nextEdge, s.nextEdge + 2, s.nextEdge + 3, ?_, ?_⟩
      · simp [hnext, kmswStepOfStep, hdrop, State.addEdge]
      · simp [hemap]
  · intro e he
    rw [hlocal] at he
    have hc : e = 0 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by
      simpa [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge,
        or_comm, or_left_comm, or_assoc] using he
    rcases hc with rfl | rfl | rfl | rfl
    · left
      simp [hemap, primedGlobalFrontier, hnext, kmswStepOfStep, hdrop, State.addEdge]
    · right
      simpa [hemap] using hcut
    · left
      simp [hemap, primedGlobalFrontier, hnext, kmswStepOfStep, hdrop, State.addEdge]
    · left
      simp [hemap, primedGlobalFrontier, hnext, kmswStepOfStep, hdrop, State.addEdge]

/-- One ordinary left step after the initial C13 triangle preserves the partial
cut invariant. Old cut edges remain on the cut; the two new boundary edges
are global frontier edges. This is only the stages `1 → 2` left case, not an
arbitrary-stage transition, an ordered boundary correspondence, or -/
theorem primedSecondLeft_complementSimCut (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu0 : u 0 = 1) (hu1 : u 1 = 0)
    (hw : w (walkNL w h 0) = 0) :
    PrimedComplementSimCut u w h 0 2 (walkNL w h 0 + 1)
      (primedSecondTriangleEdgeMap u w (walkNL w h 0))
      (primedSecondTriangleVertexMap u w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have hdrop : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have hstep : kmswStage w n = kmswStepOfStep s .left :=
    primedInitial_globalExitTransition w h
  have hnext : kmswStage w (n + 1) =
      kmswStepOfStep (kmswStepOfStep s .left) .left := by
    change kmswStep (kmswStage w n) (w n) = _
    rw [hw, hstep]
    rfl
  have ha : s.active < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
  have hv := kmswStage_endpoints_lt_nextVertex w (n - 1) s.active ha
  change s.west s.active < s.nextVertex ∧ s.east s.active < s.nextVertex at hv
  have hne : s.east s.active ≠ s.west s.active := by
    have hn := activeEast_ne_activeInitial w (j := n - 1) (n := n - 1) le_rfl
    have hw' := (edge_endpoints_eq w ha).1
    change s.east s.active ≠ edgeWest w s.active at hn
    rw [← hw'] at hn
    exact hn
  have hlocal : kmswMissingRootStage u 2 =
      kmswStepOfStep (kmswStepOfStep kmswMissingRootInit .up) .left := by
    simp only [kmswMissingRootStage, hu0, hu1]
    rfl
  have hcut : s.active ∈ cutAtExit w h 0 := active_mem_cutAtExit w h 0
  have hemap (e : ℕ) : primedSecondTriangleEdgeMap u w n e =
      if e = 3 then s.nextEdge + 2 else if e = 4 then s.nextEdge + 3
      else if e = 0 then s.nextEdge + 1 else if e = 1 then s.nextEdge
      else if e = 2 then s.active else e := by
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hstep, hdrop, primedFirstStepEdgeMap]
    rfl
  have hvmap (v : ℕ) : primedSecondTriangleVertexMap u w n v =
      if v = 3 then s.nextVertex + 1 else if v = 0 then s.nextVertex
      else if v = 1 then s.west s.active else if v = 2 then s.east s.active
      else v := by
    simp [primedSecondTriangleVertexMap, kmswShiftUpVertexMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hstep, hdrop, primedFirstStepVertexMap]
    rfl
  have hnot : ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w) ⟨s.nextVertex⟩ := by
    have hh := walkNL_activeWest_unreachable w h 0
    change ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (kmswStage w n).active⟩ at hh
    simpa [act, hstep, kmswStepOfStep, hdrop, State.addEdge] using hh
  have hphase : n + 1 < walkNR w h 1 := by
    have hs := (walkNR_succ_spec w h 0).1
    by_contra hn
    have heq : walkNR w h 1 = n + 1 := by
      change n + 1 ≤ walkNR w h 1 at hs
      omega
    have hc := walkNR_succ_previous_code w h 0
    have hc' : w n = 2 := by simpa [heq] using hc
    rw [hw] at hc'
    contradiction
  have hnotFresh : ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨s.nextVertex + 1⟩ := by
    have hh := lPhase_activeWest_unreachable w h 0 (n + 1) (by
      change n ≤ n + 1
      omega) hphase
    change ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (kmswStage w (n + 1)).active⟩ at hh
    simpa [hnext, kmswStepOfStep, hdrop, State.addEdge, Nat.add_assoc] using hh
  change PrimedComplementSimCut u w h 0 2 (n + 1)
    (primedSecondTriangleEdgeMap u w n) (primedSecondTriangleVertexMap u w n)
  constructor
  · intro e he
    rw [hlocal] at he
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [hemap, hnext, kmswStepOfStep, hdrop, State.addEdge] <;> omega
  · intro e f he hf hef
    rw [hlocal] at he hf
    have he5 : e < 5 := he
    have hf5 : f < 5 := hf
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    have hd : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      simp [hemap] at hef ⊢ <;> omega
  · intro v hvb
    rw [hlocal] at hvb
    have hv4 : v < 4 := hvb
    have hc : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [hvmap, hnext, kmswStepOfStep, hdrop, State.addEdge] <;> omega
  · intro v z hvb hzb hvz
    rw [hlocal] at hvb hzb
    have hv4 : v < 4 := hvb
    have hz4 : z < 4 := hzb
    have hc : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    have hd : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl <;>
      simp [hvmap] at hvz ⊢ <;> omega
  · intro e he hp
    rw [hlocal] at he hp ⊢
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals simp [hemap, hvmap, hnext, kmswStepOfStep, hdrop, State.addEdge,
      kmswMissingRootInit, kmswInit, Nat.add_assoc]
  · intro e he hp
    rw [hlocal] at he hp ⊢
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    have ha0 : s.active ≠ s.nextEdge := by omega
    have ha1 : s.active ≠ s.nextEdge + 1 := by omega
    have ha2 : s.active ≠ s.nextEdge + 2 := by omega
    have ha3 : s.active ≠ s.nextEdge + 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals simp [hemap, hvmap, hnext, kmswStepOfStep, hdrop, State.addEdge,
      kmswMissingRootInit, kmswInit, ha0, ha1, ha2, ha3]
    exact Multiset.pair_comm _ _
  · intro e he hp
    rw [hlocal] at he hp
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals constructor
    all_goals try { solve | simp [hemap, hnext, kmswStepOfStep, hdrop,
      State.addEdge, Nat.add_assoc] }
    all_goals intro hh
    all_goals first
      | exact hnot (by simpa [hemap, hnext, kmswStepOfStep, hdrop,
          State.addEdge, Nat.add_assoc] using hh.2.2.1)
      | exact hnotFresh (by simpa [hemap, hnext, kmswStepOfStep, hdrop,
          State.addEdge, Nat.add_assoc] using hh.2.2.1)
  · rw [hlocal]
    simp [hemap, hnext, kmswStepOfStep, hdrop, kmswMissingRootInit, kmswInit,
      State.addEdge]
  · intro a b c hab
    rw [hlocal] at hab
    have hc : (a, b, c) = (0, 1, 2) ∨ (a, b, c) = (1, 3, 4) := by
      simpa [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] using hab
    rcases hc with hc | hc <;> cases hc
    · refine ⟨s.active, s.nextEdge, s.nextEdge + 1, ?_, ?_⟩
      · simp [hnext, kmswStepOfStep, hdrop]
      · simp [hemap, Multiset.cons_swap]
        exact Multiset.pair_comm _ _
    · refine ⟨s.nextEdge, s.nextEdge + 2, s.nextEdge + 3, ?_, ?_⟩
      · simp [hnext, kmswStepOfStep, hdrop, State.addEdge]
      · simp [hemap]
  · intro e he
    rw [hlocal] at he
    have hc : e = 0 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by
      simpa [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge,
        or_comm, or_left_comm, or_assoc] using he
    rcases hc with rfl | rfl | rfl | rfl
    · left
      simp [hemap, primedGlobalFrontier, hnext, kmswStepOfStep, hdrop, State.addEdge]
    · right
      simpa [hemap] using hcut
    · left
      simp [hemap, primedGlobalFrontier, hnext, kmswStepOfStep, hdrop, State.addEdge]
    · left
      simp [hemap, primedGlobalFrontier, hnext, kmswStepOfStep, hdrop, State.addEdge]

/-- An ordinary down step after the first ordinary up step activates the
matching temporary missing side and allocates nothing. The selected cut
side stays missing and belongs to the same finite cut. Partial invariant
covering only the local prefix `1,1,2`, not the paper lemma. -/
theorem primedThirdDown_complementSimCut (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu0 : u 0 = 1) (hu1 : u 1 = 1) (hu2 : u 2 = 2)
    (hw0 : w (walkNL w h 0) = 1) (hw1 : w (walkNL w h 0 + 1) = 2) :
    PrimedComplementSimCut u w h 0 3 (walkNL w h 0 + 2)
      (primedSecondTriangleEdgeMap u w (walkNL w h 0))
      (primedSecondTriangleVertexMap u w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have sim := primedSecondUp_complementSimCut u w h hu0 hu1 hw0
  change PrimedComplementSimCut u w h 0 2 (n + 1)
    (primedSecondTriangleEdgeMap u w n) (primedSecondTriangleVertexMap u w n) at sim
  have hdrop : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have hstep : kmswStage w n = kmswStepOfStep s .left :=
    primedInitial_globalExitTransition w h
  have hnext : kmswStage w (n + 1) =
      kmswStepOfStep (kmswStepOfStep s .left) .up := by
    change kmswStep (kmswStage w n) (w n) = _
    rw [hw0, hstep]
    rfl
  have hlast : kmswStage w (n + 2) =
      kmswStepOfStep (kmswStepOfStep (kmswStepOfStep s .left) .up) .down := by
    change kmswStep (kmswStage w (n + 1)) (w (n + 1)) = _
    rw [hw1, hnext]
    rfl
  have hlocal2 : kmswMissingRootStage u 2 =
      kmswStepOfStep (kmswStepOfStep kmswMissingRootInit .up) .up := by
    simp only [kmswMissingRootStage, hu0, hu1]
    rfl
  have hlocal3 : kmswMissingRootStage u 3 =
      kmswStepOfStep (kmswStepOfStep (kmswStepOfStep kmswMissingRootInit .up)
        .up) .down := by
    simp only [kmswMissingRootStage, hu0, hu1, hu2]
    rfl
  have ha : s.active < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
  have hemap (e : ℕ) : primedSecondTriangleEdgeMap u w n e =
      if e = 3 then s.nextEdge + 2 else if e = 4 then s.nextEdge + 3
      else if e = 0 then s.nextEdge + 1 else if e = 1 then s.nextEdge
      else if e = 2 then s.active else e := by
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hstep, hdrop, primedFirstStepEdgeMap]
    rfl
  have hvmap (v : ℕ) : primedSecondTriangleVertexMap u w n v =
      if v = 3 then s.nextVertex + 1 else if v = 0 then s.nextVertex
      else if v = 1 then s.west s.active else if v = 2 then s.east s.active
      else v := by
    simp [primedSecondTriangleVertexMap, kmswShiftUpVertexMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hstep, hdrop, primedFirstStepVertexMap]
    rfl
  have hnot : ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w) ⟨s.nextVertex⟩ := by
    have hh := walkNL_activeWest_unreachable w h 0
    change ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (kmswStage w n).active⟩ at hh
    simpa [hstep, kmswStepOfStep, hdrop, State.addEdge] using hh
  have hR1 : R w (n + 1) = R w n + 1 := by
    calc
      R w (n + 1) = R w n + (lazyTwoDimensionalStep (w n)).2 :=
        Finset.sum_range_succ _ _
      _ = R w n + 1 := by rw [show w n = 1 from hw0]; rfl
  have hR2 : R w (n + 2) = R w n := by
    have hs : R w (n + 2) = R w (n + 1) - 1 := by
      calc
        R w (n + 2) = R w (n + 1) + (lazyTwoDimensionalStep (w (n + 1))).2 :=
          Finset.sum_range_succ _ _
        _ = R w (n + 1) - 1 := by rw [show w (n + 1) = 2 from hw1]; rfl
    omega
  have hphase : n + 2 < walkNR w h 1 := by
    have hs := walkNR_succ_spec w h 0
    change n + 1 ≤ walkNR w h 1 ∧ R w (walkNR w h 1) = R w n - 1 at hs
    by_contra hn
    have hc : walkNR w h 1 = n + 1 ∨ walkNR w h 1 = n + 2 := by omega
    rcases hc with hc | hc <;> rw [hc] at hs <;> omega
  have hnotFresh : ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨s.nextVertex + 1⟩ := by
    have hh := lPhase_activeWest_unreachable w h 0 (n + 2) (by
      change n ≤ n + 2
      omega) hphase
    change ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 2)).west (kmswStage w (n + 2)).active⟩ at hh
    simpa [hlast, kmswStepOfStep, hdrop, State.addEdge, Nat.add_assoc] using hh
  change PrimedComplementSimCut u w h 0 3 (n + 2)
    (primedSecondTriangleEdgeMap u w n) (primedSecondTriangleVertexMap u w n)
  constructor
  · simpa only [hlocal2, hlocal3, hnext, hlast, kmswStepOfStep, hdrop] using sim.edge_bound
  · simpa only [hlocal2, hlocal3, kmswStepOfStep] using sim.edge_injective
  · simpa only [hlocal2, hlocal3, hnext, hlast, kmswStepOfStep, hdrop] using sim.vertex_bound
  · simpa only [hlocal2, hlocal3, kmswStepOfStep] using sim.vertex_injective
  · intro e he hp
    rw [hlocal3] at he hp ⊢
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals simp [hemap, hvmap, hlast, kmswStepOfStep, hdrop, State.addEdge,
      kmswMissingRootInit, kmswInit, Nat.add_assoc]
  · intro e he hp
    rw [hlocal3] at he hp ⊢
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    have ha0 : s.active ≠ s.nextEdge := by omega
    have ha1 : s.active ≠ s.nextEdge + 1 := by omega
    have ha2 : s.active ≠ s.nextEdge + 2 := by omega
    have ha3 : s.active ≠ s.nextEdge + 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals simp [hemap, hvmap, hlast, kmswStepOfStep, hdrop, State.addEdge,
      kmswMissingRootInit, kmswInit, ha0, ha1, ha2, ha3]
    exact Multiset.pair_comm _ _
  · intro e he hp
    rw [hlocal3] at he hp
    have he5 : e < 5 := he
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] at hp
    all_goals constructor
    all_goals try { solve | simp [hemap, hlast, kmswStepOfStep, hdrop,
      State.addEdge, Nat.add_assoc] }
    all_goals intro hh
    all_goals first
      | exact hnot (by simpa [hemap, hlast, kmswStepOfStep, hdrop,
          State.addEdge, Nat.add_assoc] using hh.2.2.1)
      | exact hnotFresh (by simpa [hemap, hlast, kmswStepOfStep, hdrop,
          State.addEdge, Nat.add_assoc] using hh.2.2.1)
  · rw [hlocal3]
    simp [hemap, hlast, kmswStepOfStep, hdrop, kmswMissingRootInit, kmswInit,
      State.addEdge]
  · simpa only [hlocal2, hlocal3, hnext, hlast, kmswStepOfStep, hdrop] using sim.triangle_incidence
  · intro e he
    rw [hlocal3] at he
    have hc : e = 0 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by
      simpa [kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge,
        or_comm, or_left_comm, or_assoc] using he
    rcases hc with rfl | rfl | rfl | rfl
    · left
      simp [hemap, primedGlobalFrontier, hlast, kmswStepOfStep, hdrop, State.addEdge]
    · right
      simpa [hemap] using active_mem_cutAtExit w h 0
    · left
      simp [hemap, primedGlobalFrontier, hlast, kmswStepOfStep, hdrop, State.addEdge]
    · left
      simp [hemap, primedGlobalFrontier, hlast, kmswStepOfStep, hdrop, State.addEdge]

/-- A down step does not remove any old geometric frontier edge: a consumed
UR head is appended to UL. Partial invariant helper for `lem-quad-kmsw`
theorem. This holds for both the allocation and activation branches. -/
theorem primedGlobalFrontier_down_mono (s : State) (e : ℕ)
    (he : e ∈ primedGlobalFrontier s) :
    e ∈ primedGlobalFrontier (kmswStepOfStep s .down) := by
  cases hur : s.UR with
  | nil =>
    simp only [primedGlobalFrontier, kmswStepOfStep, hur, State.addEdge,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at he ⊢
    rcases he with he | he | he
    · exact Or.inl (Or.inl he)
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl he))
  | cons a as =>
    simp only [primedGlobalFrontier, kmswStepOfStep, hur, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    rcases he with he | (he | he) | he | he
    · exact Or.inl (Or.inl he)
    · exact Or.inl (Or.inr he)
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr he))

/-- The only geometric frontier edge an up step can lose is its old active
edge. Whether its image must remain on the primed boundary is a separate
question. Partial invariant helper for `lem-quad-kmsw`
lemma. -/
theorem primedGlobalFrontier_up_loss (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ primedGlobalFrontier (kmswStage w n))
    (hgone : e ∉ primedGlobalFrontier (kmswStepOfStep (kmswStage w n) .up)) :
    e = (kmswStage w n).active := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  by_contra hne
  apply hgone
  simp only [primedGlobalFrontier, List.mem_append] at he
  rcases he with he | he | he | he
  · have hx : e ∈ xs := by simpa [hxs, hne] using he
    simp [primedGlobalFrontier, kmswStepOfStep, State.addEdge, hxs, hx]
  · simp [primedGlobalFrontier, kmswStepOfStep, State.addEdge, he]
  · simp [primedGlobalFrontier, kmswStepOfStep, State.addEdge, he]
  · simp [primedGlobalFrontier, kmswStepOfStep, State.addEdge, he]

/-- The code prefix `1,0,1` loses global frontier edge `3` at times `2 → 3`,
but that edge is not in the first cut. Thus blanket persistence of *all*
old frontier edges into the cut is false. This does not refute persistence
for images which remain on the local boundary: that surviving-image
restriction is essential. Finite-prefix helper for `lem-quad-kmsw` -/
theorem primedFrontier_loss_outside_cut (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hw0 : w 0 = 1) (hw1 : w 1 = 0) (hw2 : w 2 = 1) :
    walkNL w h 0 = 2 ∧
    3 ∈ primedGlobalFrontier (kmswStage w 2) ∧
    3 ∉ primedGlobalFrontier (kmswStage w 3) ∧
    3 ∉ cutAtExit w h 0 := by
  have hL0 : L w 0 = 0 := by simp [L]
  have hL1 : L w 1 = 0 := by
    simp [L, hw0, lazyTwoDimensionalStep]
  have hL2 : L w 2 = -1 := by
    simp [L, Finset.sum_range_succ, hw0, hw1, lazyTwoDimensionalStep]
  have hupper : walkNL w h 0 ≤ 2 := by
    change firstFlowLHit w h 0 ≤ 2
    unfold firstFlowLHit
    apply Nat.find_min'
    exact ⟨by omega, by rw [hL0, hL2]; rfl⟩
  have hs := walkNL_spec w h 0
  rw [walkNR_zero, hL0] at hs
  have hneq : walkNL w h 0 ≠ 1 := by
    intro hn
    rw [hn, hL1] at hs
    omega
  have hn : walkNL w h 0 = 2 := by omega
  refine ⟨hn, ?_, ?_, ?_⟩
  · simp [primedGlobalFrontier, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hw0, hw1]
  · simp [primedGlobalFrontier, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge, hw0, hw1, hw2]
  · intro he
    have hb := cutAtExit_edge_bound w h 0 3 he
    rw [hn] at hb
    simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit,
      State.addEdge, hw0] at hb

/- For an ordinary step let
`u = primedCode ω h`, `w i = ω (i+1)`,
`m = primedIntervalBase ω h k + j`,
`n = primedIntervalLeft ω h k + j - 1`, with `0 < j` and
`j < primedIntervalWidth ω h k`. The remaining general goal is

```
PrimedComplementSimCut u w h k m n eφ vφ →
  ∃ eφ' vφ',
    (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
    (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
    PrimedComplementSimCut u w h k (m+1) (n+1) eφ' vφ'
```

The time/code part is proved above. The general incidence proof still needs
to identify the active edge and the relevant stack heads from coherent
geometric data; these are not fields of `PrimedComplementSimCut`.
For the boundary clause, every surviving local boundary edge whose old
image disappears from the global frontier must have its image in
`cutAtExit w h k`. The loss lemma above isolates the up-step hazard;
down steps lose no old global frontier edge. The finite-prefix example
shows why the surviving-local-boundary restriction cannot be omitted.

For a compressed crossing between blocks `k` and `k+1`, put
`m = primedIntervalBase ω h (k+1)`, `n = walkNR w h (k+1)-1`, and
`n' = walkNL w h (k+1)`. The needed lemma must extend maps from a
`PrimedComplementSimCut u w h k m n` simulation to a
`PrimedComplementSimCut u w h (k+1) (m+1) n'` simulation. Writing
`E = (kmswMissingRootStage u m).nextEdge`,
`V = (kmswMissingRootStage u m).nextVertex`, and
`s = kmswStage w (n'-1)`, its new images must satisfy
`eφ' E = s.nextEdge`, `eφ' (E+1) = s.active`, and
`vφ' V = s.east s.active`, while preserving every old allocated image.
In particular the new local missing side maps to an existing geometric
cut edge, rather than necessarily to a freshly allocated global edge.
The old boundary images must persist through the omitted R excursion
into the new frontier or the selected next cut. No identification of an
arbitrary full hatted UL with β₀, and no cut-prefix persistence hypothesis,
has been assumed here. None of these general obligations is a declaration
or a completed result in this module. -/

end DirectedDistances.KMSW
