module

public import DirectedDistances.PaperProofs.Section5.FlowLineTimes
public import DirectedDistances.KMSW.Beta0BoundarySuccessor

/-! # Local source-time consequences for Lemma 5.12

initial triangle convention first triangle. Source index `k + 1` is represented by `sourceFlowNR k`
and `sourceFlowNL k`. The interface edges belong to the actual ordered
stream `β₀`. Identifying the triangle with a face of the cut-completed
primed plane map remains separate, so this module does not claim Lemma 5.12. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open Quiver

/-- Helper toward Lemma 5.12; not a paper result.
jointly with the initial value and the active-edge membership minima. -/
theorem flow_line_times_source_minima (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    sourceFlowNR w h 0 = 0 ∧
      (∀ k, IsLeast
        {n | sourceFlowLeftCandidate w (sourceFlowNR w h k) n}
        (sourceFlowNL w h k)) ∧
      (∀ k, IsLeast
        {n | sourceFlowRightCandidate w (sourceFlowNL w h k) n}
        (sourceFlowNR w h (k + 1))) ∧
      (∀ k, IsLeast
        {n | sourceFlowNR w h k + 1 ≤ n ∧
          L w n = L w (sourceFlowNR w h k) - 1}
        (sourceFlowNL w h k)) ∧
      (∀ k, IsLeast
        {n | sourceFlowNL w h k + 1 ≤ n ∧
          R w n = R w (sourceFlowNL w h k) - 1}
        (sourceFlowNR w h (k + 1))) := by
  exact ⟨sourceFlowNR_zero w h, sourceFlowNL_candidate_isLeast w h,
    sourceFlowNR_succ_candidate_isLeast w h, sourceFlowNL_level_isLeast w h,
    sourceFlowNR_succ_level_isLeast w h⟩

/-- Proposed provider for Lemma 5.12 (lem-flow-line-times, initial triangle convention); not a paper result.
triangle, and the new present active edge, retaining both allocation cases. -/
theorem flow_line_times_source_item_i (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 2 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let s := kmswStage w (r - 1)
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w r).west (act w r)⟩ ∧
      (L w r - L w (r - 1), R w r - R w (r - 1)) = (1, -1) ∧
      (kmswStage w r).triangles = s.triangles ∧
      ((s.UR = [] ∧
          (kmswStage w r).nextEdge = s.nextEdge + 1 ∧
          (kmswStage w r).nextVertex = s.nextVertex + 1 ∧
          act w r = s.nextEdge ∧
          (kmswStage w r).west (act w r) = s.east s.active ∧
          (kmswStage w r).east (act w r) = s.nextVertex ∧
          (kmswStage w r).present (act w r) = true) ∨
        ∃ e es, s.UR = e :: es ∧ s.present e = false ∧
          (kmswStage w r).nextEdge = s.nextEdge ∧
          act w r = e ∧
          (kmswStage w r).west e = s.east s.active ∧
          (kmswStage w r).east e = s.east e ∧
          (kmswStage w r).present e = true) := by
  exact sourceFlow_rightEntry_singleEdge w h k hk





theorem flow_line_times_source_item_ii_first_geometry (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    let t := sourceFlowNL w h 0
    let s := kmswStage w (t - 1)
    (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
      (kmswStage w t).triangles =
        s.triangles ++ [(act w (t - 1), act w t, s.nextEdge + 1)] ∧
      act w t = s.nextEdge ∧
      (kmswStage w t).present (act w t) = true ∧
      (kmswStage w t).nextEdge = s.nextEdge + 2 ∧
      s.nextEdge ≤ s.nextEdge + 1 ∧
      s.nextEdge + 1 < (kmswStage w t).nextEdge ∧
      (kmswStage w t).present (s.nextEdge + 1) = false ∧
      ({(kmswStage w t).west (s.nextEdge + 1),
        (kmswStage w t).east (s.nextEdge + 1)} : Set ℕ) =
        {(kmswStage w t).west (act w t), s.west (act w (t - 1))} ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w t).west (act w t)⟩ ∧
      sourceFlowMhatInterfaceEdge w t (act w (t - 1)) := by
  obtain ⟨hbase, hnext, hallocated, hnew, hpresent, _, _, hends,
    hnot, _, _, hinter, _⟩ := sourceFlow_firstLeftExit_triangle w h
  exact ⟨hbase.1, hbase.2.2.2.2.1, hbase.2.2.2.2.2.1, hpresent,
    hnext, Nat.le_add_right _ _, hallocated, hbase.2.2.2.2.2.2,
    hends, hnot, hinter⟩




theorem flow_line_times_source_item_ii_later_geometry (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 2 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let s := kmswStage w (t - 1)
    (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
      (kmswStage w t).triangles =
        s.triangles ++ [(act w (t - 1), act w t, act w (r - 1))] ∧
      act w t = s.nextEdge ∧
      (kmswStage w t).present (act w t) = true ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w t).west (act w t)⟩ ∧
      sourceFlowMhatInterfaceEdge w t (act w (t - 1)) := by
  obtain ⟨hbase, hnot, _, _, hinter⟩ := sourceFlow_leftExit_triangle w h k hk
  obtain ⟨_, _, hstep, _, _, _, htri, hact, hpresent, _, _⟩ := hbase
  exact ⟨hstep, htri, hact, hpresent, hnot, hinter⟩

/-- Helper toward Lemma 5.12; not a paper result.
The arriving step and appended triangle for every `k ≥ 1`, with precisely
retains the first triangle without truncating a negative chronological index.
The primed-map face identification remains separate; stream membership is supplied below. -/
theorem flow_line_times_source_item_ii_geometry (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 1 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let s := kmswStage w (t - 1)
    (L w t - L w (t - 1), R w t - R w (t - 1)) = (-1, 0) ∧
      ∃ e,
        (kmswStage w t).triangles =
          s.triangles ++ [(act w (t - 1), act w t, e)] ∧
        act w t = s.nextEdge ∧
        (kmswStage w t).present (act w t) = true ∧
        ¬ Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w t).west (act w t)⟩ ∧
        sourceFlowMhatInterfaceEdge w t (act w (t - 1)) ∧
        ((k = 1 ∧ e = s.nextEdge + 1 ∧
            (kmswStage w t).nextEdge = s.nextEdge + 2 ∧
            s.nextEdge ≤ e ∧ e < (kmswStage w t).nextEdge ∧
            (kmswStage w t).present e = false ∧
            ({(kmswStage w t).west e, (kmswStage w t).east e} : Set ℕ) =
              {(kmswStage w t).west (act w t), s.west (act w (t - 1))}) ∨
          (2 ≤ k ∧ e = act w (r - 1))) := by
  by_cases hfirst : k = 1
  · subst k
    obtain ⟨hstep, htri, hact, hpresent, hnext, hlow, hhigh, hmissing,
      hends, hnot, hinter⟩ := flow_line_times_source_item_ii_first_geometry w h
    exact ⟨hstep, _, htri, hact, hpresent, hnot, hinter,
      Or.inl ⟨rfl, rfl, hnext, hlow, hhigh, hmissing, hends⟩⟩
  · have hlater : 2 ≤ k := by omega
    obtain ⟨hstep, htri, hact, hpresent, hnot, hinter⟩ :=
      flow_line_times_source_item_ii_later_geometry w h k hlater
    exact ⟨hstep, _, htri, hact, hpresent, hnot, hinter,
      Or.inr ⟨hlater, rfl⟩⟩

/-- Helper toward Lemma 5.12; not a paper result.
The initial triangle convention edge is the first lower-left missing geometric edge and never
Its incidence and unordered endpoints are in the first-geometry theorem. -/
theorem flow_line_times_source_first_missing_persistent (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    let t := sourceFlowNL w h 0
    let s := kmswStage w (t - 1)
    let e := s.nextEdge + 1
    s.LL = [] ∧ (kmswStage w t).LL = [e] ∧
      (∀ n, t ≤ n → e ∈ (kmswStage w n).LL ∧
        (kmswStage w n).present e = false) ∧
      ¬ EdgePresent w e := by
  rw [sourceFlowNL_eq_walkNL]
  let t := walkNL w h 0
  let s := kmswStage w (t - 1)
  let e := s.nextEdge + 1
  obtain ⟨htpos, hcode, _, hUL⟩ := quadrantFirstR_exit_predecessor_emptyUL w h
  have ht : t - 1 + 1 = t := by dsimp [t]; omega
  have hprefix : ∀ j < t, 0 ≤ L w j := by
    intro j hj
    exact firstRPhase_L_nonneg_before_exit w h hj
  obtain ⟨j, hj, hmin⟩ := runningMin_attained (L w) (t - 1)
  have hnonneg := hprefix j (by omega)
  have hlength := kmswStage_LL_length w (t - 1)
  have hmin' : minL w (t - 1) = L w j := hmin
  have hLL : s.LL = [] := by
    apply List.length_eq_zero_iff.mp
    change (kmswStage w (t - 1)).LL.length = 0
    omega
  have hstep : kmswStage w t = kmswStepOfStep s .left := by
    rw [← ht]
    change kmswStep s (w (t - 1)) = kmswStepOfStep s .left
    rw [show w (t - 1) = 0 from hcode]
    rfl
  have hLLt : (kmswStage w t).LL = [e] := by
    rw [hstep]
    simp only [kmswStepOfStep, show s.UL.dropLast.reverse = [] from hUL,
      State.addEdge, hLL, e]
  have hnext : (kmswStage w t).nextEdge = s.nextEdge + 2 := by
    rw [hstep]
    simp only [kmswStepOfStep, show s.UL.dropLast.reverse = [] from hUL,
      State.addEdge]
  have he : kmswLLCreatedEdge w t = e := by
    dsimp only [kmswLLCreatedEdge]
    rw [hnext]
    dsimp [e]
  have hLt : L w t = -1 := by
    have hs := (walkNL_spec w h 0).2
    rw [walkNR_zero] at hs
    simpa only [L, Finset.sum_range_zero, zero_sub] using hs
  have hrecord : ∀ j < t, L w t < L w j := by
    intro j hj
    have hjnonneg := hprefix j hj
    omega
  have hpersist : ∀ n, t ≤ n → e ∈ (kmswStage w n).LL ∧
      (kmswStage w n).present e = false := by
    intro n hn
    have hmem : e ∈ (kmswStage w n).LL := by
      rw [kmswStage_LL_eq]
      apply List.mem_map.mpr
      refine ⟨t, List.mem_reverse.mpr ?_, he⟩
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr (by omega), decide_eq_true ⟨htpos, hrecord⟩⟩
    have hbound : e < (kmswStage w n).nextEdge := by
      have hmono := kmswStage_nextEdge_mono w hn
      rw [hnext] at hmono
      dsimp [e]
      omega
    exact ⟨hmem, ((kmswStage_status w n).1 e hbound).mpr (Or.inr hmem)⟩
  refine ⟨hLL, hLLt, hpersist, ?_⟩
  intro hpresent
  obtain ⟨N, hN⟩ := hpresent.eventually_present
  have htrue := (hN (max N t) (Nat.le_max_left _ _)).2
  have hfalse := (hpersist (max N t) (Nat.le_max_right _ _)).2
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

/-- Helper toward Lemma 5.12; not a paper result.
At every source left exit the previously active edge belongs to the actual -/
theorem flow_line_times_source_left_exit_mem_beta0 (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) (k : ℕ) (hk : 1 ≤ k) :
    ∃ j : ℕ, (kmswBeta0Stream w hfin hb j).1 =
      act w (sourceFlowNL w h (k - 1) - 1) := by
  exact beta0_westBoundary_reached w hfin hb _
    (mhatWestBoundaryEdge_leftExit w h k hk)

end DirectedDistances.PaperProofs.Section5
