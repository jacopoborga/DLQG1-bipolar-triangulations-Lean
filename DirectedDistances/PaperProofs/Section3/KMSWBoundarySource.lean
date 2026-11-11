module

public import DirectedDistances.KMSW.BoundaryVertexVisits
public import DirectedDistances.KMSW.StageBoundaryMap
public import DirectedDistances.KMSW.StageVertices
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! Supporting lemmas for paper labels `def-kmsw`, `defn:bound-edges`, `lem-kmsw-bdy` (see CORRESPONDENCE.md). -/



























































public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open scoped Classical

private theorem filtered_last (P : ℕ → Bool) (f : ℕ → ℕ) {t n k : ℕ}
    (htn : t ≤ n) (hP : P t = true)
    (hlen : (((List.range (t + 1)).filter P).map f).length = k + 1) :
    (((List.range (n + 1)).filter P).map f)[k]? = some (f t) := by
  induction n, htn using Nat.le_induction with
  | base =>
    rw [List.range_succ, List.filter_append, List.map_append] at hlen ⊢
    simp only [List.filter_cons, hP, List.filter_nil, ite_true,
      List.map_cons, List.map_nil] at hlen ⊢
    have hlength : (((List.range t).filter P).map f).length = k := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    rw [List.getElem?_append_right (by omega), hlength, Nat.sub_self]
    rfl
  | succ n _ ih =>
    rw [List.range_succ, List.filter_append, List.map_append]
    have hlt : k < (((List.range (n + 1)).filter P).map f).length :=
      (List.getElem?_eq_some_iff.mp ih).1
    rw [List.getElem?_append_left hlt]
    exact ih



@[expose] noncomputable def kmswBoundaryVertex (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) (side : Bool) :
    (kmswMap w n).VertexQuotient :=
  (stageVertexEquiv w n).symm
    ⟨stageEndpoint (kmswStage w n) (e, side), stageEndpoint_lt_nextVertex w n (e, side)⟩

private theorem vertex_eq_iff (w : ℕ → Fin 3) (n : ℕ)
    (e f : Fin (kmswStage w n).nextEdge) (side : Bool) :
    kmswBoundaryVertex w n e side = kmswBoundaryVertex w n f side ↔
      stageEndpoint (kmswStage w n) (e, side) =
        stageEndpoint (kmswStage w n) (f, side) := by
  unfold kmswBoundaryVertex
  rw [(stageVertexEquiv w n).symm.injective.eq_iff]
  exact Fin.ext_iff

private theorem L_step_bound (w : ℕ → Fin 3) (i : ℕ) :
    |L w (i + 1) - L w i| ≤ 1 := by
  have hs : L w (i + 1) =
      L w i + (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w i)).1 :=
    Finset.sum_range_succ _ _
  rw [hs]
  generalize hw : w i = c
  fin_cases c <;> simp [DirectedDistances.RandomWalk.lazyTwoDimensionalStep]

private theorem R_step_bound (w : ℕ → Fin 3) (i : ℕ) :
    |R w (i + 1) - R w i| ≤ 1 := by
  have hs : R w (i + 1) =
      R w i + (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w i)).2 :=
    Finset.sum_range_succ _ _
  rw [hs]
  generalize hw : w i = c
  fin_cases c <;> simp [DirectedDistances.RandomWalk.lazyTwoDimensionalStep]

private theorem first_L_record (w : ℕ → Fin 3) (k : ℕ) (hk : 1 ≤ k)
    (hhit : ∃ t, L w t = -(k : ℤ)) :
    0 < Nat.find hhit ∧ ∀ j < Nat.find hhit, L w (Nat.find hhit) < L w j := by
  have h := (strict_running_minimum_iff_first_hit (L w) (by simp [L])
    (L_step_bound w) (Nat.find hhit) (Nat.find hhit) (-(k : ℤ))
    (by omega) hhit).2 ⟨le_rfl, Nat.find_spec hhit, rfl⟩
  exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp h.1).1).1,
    (Finset.mem_filter.mp h.1).2⟩

private theorem first_R_record (w : ℕ → Fin 3) (k : ℕ)
    (hhit : ∃ t, R w t = -(k : ℤ)) :
    ∀ j < Nat.find hhit, R w (Nat.find hhit) < R w j := by
  have h := (weak_first_minimum_iff_first_hit (R w) (by simp [R])
    (R_step_bound w) (Nat.find hhit) (Nat.find hhit) (-(k : ℤ))
    (by omega) hhit).2 ⟨le_rfl, Nat.find_spec hhit, rfl⟩
  exact (Finset.mem_filter.mp h.1).2

private theorem root_tip (w : ℕ → Fin 3) (n : ℕ) :
    (CutConverse.pendingVertices (kmswStage w n)).getLast? = some 1 ↔
      minR w n = 0 := by
  induction n with
  | zero => simp [CutConverse.pendingVertices, kmswStage, kmswInit, minR, runningMin, R]
  | succ n ih =>
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    by_cases hreset : w n = 2 ∧ s.UR = []
    · obtain ⟨hc, hu⟩ := hreset
      have htip : (CutConverse.pendingVertices t).getLast? = some s.nextVertex := by
        simp [t, s, CutConverse.pendingVertices, kmswStage, kmswStep,
          kmswCodeStep, hc, kmswStepOfStep, hu, State.addEdge]
      have hv : 2 ≤ s.nextVertex :=
        CutConverse.nextVertex_mono w (Nat.zero_le n)
      have hlen := kmswStage_UR_length w n
      change (s.UR.length : ℤ) = R w n - minR w n at hlen
      rw [hu] at hlen
      have hstep : R w (n + 1) = R w n - 1 := by
        rw [show R w (n + 1) = R w n +
          (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w n)).2 from
          Finset.sum_range_succ _ _, hc]
        rfl
      have hmin0 := runningMin_le (R w) n 0 (Nat.zero_le n)
      have hnext : minR w (n + 1) = min (minR w n) (R w (n + 1)) := rfl
      have hneg : minR w (n + 1) < 0 := by
        have hle := min_le_right (minR w n) (R w (n + 1))
        simp only [List.length_nil, Nat.cast_zero] at hlen
        change minR w n ≤ 0 at hmin0
        omega
      change (CutConverse.pendingVertices t).getLast? = some 1 ↔ _
      rw [htip]
      simp only [Option.some.injEq]
      constructor <;> intro h <;> omega
    · have hLR : t.LR = s.LR := by
        change (kmswStep s (w n)).LR = s.LR
        generalize hc : w n = c at *
        fin_cases c
        · cases hu : s.UL.dropLast.reverse <;>
            simp [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge]
        · rfl
        · have hu : s.UR ≠ [] := fun hu => hreset ⟨rfl, hu⟩
          cases hs : s.UR with
          | nil => exact (hu hs).elim
          | cons e es => simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs]
      have hmaps : s.LR.map t.east = s.LR.map s.east := by
        apply List.map_congr_left
        intro e he
        exact (kmswStage_endpoints_stable w (Nat.le_succ n)
          (stageRun_edge_bound w n e (Or.inr he))).2
      have htip : (CutConverse.pendingVertices t).getLast? =
          (CutConverse.pendingVertices s).getLast? := by
        rw [CutConverse.pending_terminal_eq_LR, CutConverse.pending_terminal_eq_LR]
        change (t.LR.map t.east).getLast? = (s.LR.map s.east).getLast?
        rw [hLR, hmaps]
      have ha := kmswStage_LR_length w n
      change (s.LR.length : ℤ) = _ at ha
      have hb := kmswStage_LR_length w (n + 1)
      change (t.LR.length : ℤ) = _ at hb
      rw [hLR] at hb
      have hmin : minR w (n + 1) = minR w n := by omega
      change (CutConverse.pendingVertices t).getLast? = some 1 ↔ _
      rw [htip, hmin]
      exact ih

private theorem root_visits (w : ℕ → Fin 3) (m : ℕ) :
    (kmswStage w m).east (act w m) = 1 ↔
      R w m = 0 ∧ ∀ j ≤ m, 0 ≤ R w j := by
  have hroot : 0 ∈ (kmswStage w 0).LR := by simp [kmswStage, kmswInit]
  constructor
  · intro hv
    have hu : (kmswStage w m).UR = [] := by
      cases hs : (kmswStage w m).UR with
      | nil => rfl
      | cons e es =>
        have hmem : 1 ∈ (CutConverse.pendingVertices (kmswStage w m)).dropLast := by
          simp [CutConverse.pendingVertices, hs, act] at hv ⊢
          exact Or.inl hv.symm
        have hne := (CutConverse.pending_interior_ne_LR_endpoints w m 0 hmem hroot).2
        exact (hne (by rfl)).elim
    have htip : (CutConverse.pendingVertices (kmswStage w m)).getLast? = some 1 := by
      simp only [CutConverse.pendingVertices, hu, List.map_nil, List.getLast?_singleton]
      exact congrArg some hv
    have hmin := (root_tip w m).1 htip
    have hlen := kmswStage_UR_length w m
    rw [hu] at hlen
    refine ⟨by simp only [List.length_nil, Nat.cast_zero] at hlen; omega, ?_⟩
    intro j hj
    have hle := runningMin_le (R w) m j hj
    change minR w m ≤ R w j at hle
    omega
  · rintro ⟨hlev, habove⟩
    have hmin : minR w m = 0 := by
      obtain ⟨j, hj, he⟩ := runningMin_attained (R w) m
      have hlo := habove j hj
      have hhi := runningMin_le (R w) m m le_rfl
      change minR w m = R w j at he
      change minR w m ≤ R w m at hhi
      omega
    have hu : (kmswStage w m).UR = [] := by
      apply List.length_eq_zero_iff.mp
      have hlen := kmswStage_UR_length w m
      omega
    have htip := (root_tip w m).2 hmin
    simpa [CutConverse.pendingVertices, hu, act] using htip

private theorem lower_left_clause (w : ℕ → Fin 3) (n : ℕ) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (hhit : ∃ t, L w t = -(k : ℤ)),
      Nat.find hhit ≤ n →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = kmswLLCreatedEdge w (Nat.find hhit) ∧
        (kmswStage w n).LL.reverse[k - 1]? = some e.val ∧
        (kmswStageDirectedMap w n).missing (e, true) ∧
        (kmswStageDirectedMap w n).IsOuter (e, true) ∧
        (∀ m (hm : m ≤ n),
          kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false =
              kmswBoundaryVertex w n e false ↔
            L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j) ∧
        IsLeast {m | ∃ hm : m ≤ n,
          kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false =
            kmswBoundaryVertex w n e false} (Nat.find hhit) := by
  intro k hk hhit htn
  let t := Nat.find hhit
  have hlevel : L w t = -(k : ℤ) := Nat.find_spec hhit
  obtain ⟨ht, hrec⟩ := first_L_record w k hk hhit
  change ∀ j < t, L w t < L w j at hrec
  have hmin : minL w t = -(k : ℤ) := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) t
    change minL w t = L w j at he
    by_cases hjt : j < t
    · have hp := hrec j hjt
      have hlo := runningMin_le (L w) t t le_rfl
      change minL w t ≤ L w t at hlo
      omega
    · have hjt : j = t := by omega
      simpa only [hjt, hlevel] using he
  let P := fun m => decide (0 < m ∧ ∀ j < m, L w m < L w j)
  have hlen : (((List.range (t + 1)).filter P).map
      (kmswLLCreatedEdge w)).length = (k - 1) + 1 := by
    have h := kmswStage_LL_length w t
    rw [kmswStage_LL_eq] at h
    simp only [List.length_map, List.length_reverse] at h
    dsimp only [P]
    simp only [List.length_map]
    omega
  have hnth (N : ℕ) (htN : t ≤ N) :
      (kmswStage w N).LL.reverse[k - 1]? = some (kmswLLCreatedEdge w t) := by
    rw [kmswStage_LL_eq]
    simp only [List.map_reverse, List.reverse_reverse]
    exact filtered_last P (kmswLLCreatedEdge w) htN (decide_eq_true ⟨ht, hrec⟩) hlen
  have het : kmswLLCreatedEdge w t < (kmswStage w t).nextEdge :=
    stageRun_edge_bound w t _ (Or.inl (Or.inr
      (List.mem_reverse.mp (List.mem_of_getElem? (hnth t le_rfl)))))
  have hen : kmswLLCreatedEdge w t < (kmswStage w n).nextEdge :=
    het.trans_le (kmswStage_nextEdge_mono w htn)
  let e : Fin (kmswStage w n).nextEdge := ⟨kmswLLCreatedEdge w t, hen⟩
  have hgeo := (kmswStageDirectedMap_LL_east w n e).2
    (List.mem_reverse.mp (List.mem_of_getElem? (hnth n htn)))
  have hvis := kmswLL_first_hit_vertex_visits w k hk hhit
  have hvisits (m : ℕ) (hm : m ≤ n) :
      kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false =
          kmswBoundaryVertex w n e false ↔
        L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j := by
    rw [vertex_eq_iff]
    change (kmswStage w n).west (act w m) =
      (kmswStage w n).west (kmswLLCreatedEdge w t) ↔ _
    rw [(kmswStage_endpoints_stable w hm (act_lt_nextEdge w le_rfl)).1,
      (kmswStage_endpoints_stable w htn het).1]
    exact hvis.2.1 m
  refine ⟨e, rfl, hnth n htn, hgeo.1, hgeo.2, hvisits, ?_⟩
  constructor
  · exact ⟨htn, (hvisits t htn).2 ((hvis.2.1 t).1 hvis.1)⟩
  · rintro m ⟨hm, hv⟩
    exact Nat.find_min' hhit ((hvisits m hm).1 hv).1

private theorem lower_right_clause (w : ℕ → Fin 3) (n : ℕ) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (hhit : ∃ t, R w t = -(k : ℤ)), Nat.find hhit ≤ n →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = act w (Nat.find hhit) ∧
        (kmswStage w n).LR[(k + 1) - 1]? = some e.val ∧
        (e, true) ∈ (kmswStageDirectedMap w n).lrDarts ∧
        (∀ m (hm : m ≤ n),
          kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ true =
              kmswBoundaryVertex w n e true ↔
            R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j) ∧
        IsLeast {m | ∃ hm : m ≤ n,
          kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ true =
            kmswBoundaryVertex w n e true} (Nat.find hhit) := by
  intro k hk hhit htn
  let t := Nat.find hhit
  have hlevel : R w t = -(k : ℤ) := Nat.find_spec hhit
  have hrec := first_R_record w k hhit
  change ∀ j < t, R w t < R w j at hrec
  have hlen := ((kmswStage_LR_first_hitting w k t).1
    ⟨hlevel, fun j hj => by have := hrec j hj; omega⟩).1
  have hnth : (kmswStage w n).LR[k]? = some (act w t) := by
    rw [kmswStage_LR_eq]
    apply filtered_last (fun m => decide (∀ j, j < m → R w m < R w j)) (act w)
      htn (decide_eq_true hrec)
    simpa only [kmswStage_LR_eq] using hlen
  let e : Fin (kmswStage w n).nextEdge := ⟨act w t, act_lt_nextEdge w htn⟩
  have hgeo := (kmswStageDirectedMap_LR_bridge w n e).1 (List.mem_of_getElem? hnth)
  have hvis (m : ℕ) :
      (kmswStage w m).east (act w m) = (kmswStage w t).east (act w t) ↔
        R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j := by
    exact (kmswLR_first_hit_vertex_visits w k hk hhit).2.1 m
  have hvisits (m : ℕ) (hm : m ≤ n) :
      kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ true =
          kmswBoundaryVertex w n e true ↔
        R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j := by
    rw [vertex_eq_iff]
    change (kmswStage w n).east (act w m) =
      (kmswStage w n).east (act w t) ↔ _
    rw [(kmswStage_endpoints_stable w hm (act_lt_nextEdge w le_rfl)).2,
      (kmswStage_endpoints_stable w htn (act_lt_nextEdge w le_rfl)).2]
    exact hvis m
  refine ⟨e, rfl, ?_, hgeo, hvisits, ?_⟩
  · simpa only [Nat.add_sub_cancel] using hnth
  · constructor
    · refine ⟨htn, (hvisits t htn).2 ⟨hlevel, ?_⟩⟩
      intro j hj
      by_cases hjt : j < t
      · have := hrec j hjt
        omega
      · have hjt : j = t := by omega
        rw [hjt, hlevel]
    · rintro m ⟨hm, hv⟩
      exact Nat.find_min' hhit ((hvisits m hm).1 hv).1

private theorem upper_left_clause (w : ℕ → Fin 3) (n : ℕ) :
    ∀ (k m : ℕ), 1 ≤ k →
      ((List.range (n + 1)).filter (fun t => decide
        (∀ j, t + 1 ≤ j → j ≤ n → L w t + 1 ≤ L w j)))[k - 1]? = some m →
      ∃ hm : m ≤ n,
        (kmswStage w n).UL[k - 1]? = some (act w m) ∧
        (⟨act w m, act_lt_nextEdge w hm⟩, false) ∈
          (kmswStageDirectedMap w n).ulDarts ∧
        ∀ m' (hm' : m' ≤ m), L w m' = L w m →
          (∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) →
          kmswBoundaryVertex w n
              ⟨act w m', act_lt_nextEdge w (hm'.trans hm)⟩ false =
            kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false := by
  intro k m _ hkth
  have hmem := List.mem_filter.mp (List.mem_of_getElem? hkth)
  have hm : m ≤ n := by have := List.mem_range.mp hmem.1; omega
  have hlist : (kmswStage w n).UL =
      ((List.range (n + 1)).filter (fun t => decide
        (∀ j, t + 1 ≤ j → j ≤ n → L w t + 1 ≤ L w j))).map (act w) := by
    rw [kmswStage_UL_eq]
    congr 2
    funext t
    congr 1
  have hnth : (kmswStage w n).UL[k - 1]? = some (act w m) := by
    rw [hlist, List.getElem?_map, hkth]
    rfl
  refine ⟨hm, hnth, (kmswStageDirectedMap_UL_bridge w n _).1
    (List.mem_of_getElem? hnth), ?_⟩
  intro m' hm' hlev habove
  rw [vertex_eq_iff]
  change (kmswStage w n).west (act w m') = (kmswStage w n).west (act w m)
  rw [(kmswStage_endpoints_stable w hm (act_lt_nextEdge w hm')).1,
    (kmswStage_endpoints_stable w hm (act_lt_nextEdge w le_rfl)).1]
  exact kmsw_west_act_eq_of_level w hm' hlev habove

private theorem upper_right_clause (w : ℕ → Fin 3) (n : ℕ) :
    ∀ (k m : ℕ), 1 ≤ k →
      ((List.range (n + 1)).filter (fun t => decide
        (0 < t ∧ t ≤ n ∧ ∀ j, t ≤ j → j ≤ n →
          R w (t - 1) + 1 ≤ R w j)))[k - 1]? = some m →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = kmswURCreatedEdge w m ∧
        (kmswStage w n).UR.reverse[k - 1]? = some e.val ∧
        (kmswStageDirectedMap w n).missing (e, false) ∧
        (kmswStageDirectedMap w n).IsOuter (e, false) := by
  intro k m _ hkth
  have hnth : (kmswStage w n).UR.reverse[k - 1]? =
      some (kmswURCreatedEdge w m) := by
    rw [kmswStage_UR_eq]
    simp only [List.map_reverse, List.reverse_reverse, List.getElem?_map, hkth]
    rfl
  have he := List.mem_reverse.mp (List.mem_of_getElem? hnth)
  let e : Fin (kmswStage w n).nextEdge :=
    ⟨kmswURCreatedEdge w m, stageRun_edge_bound w n _ (Or.inl (Or.inl (Or.inr he)))⟩
  have hgeo := (kmswStageDirectedMap_UR_west w n e).2 he
  exact ⟨e, rfl, hnth, hgeo⟩

/-- The literal positive-time reading of `lem-kmsw-bdy`(iii),
the positive record list is `[1]`, but the upper-left boundary is `[0,1]`.
The ℕ₀ statement in `kmsw_bdy_source` matches `eqn-kmsw-bdy`; a manuscript -/
theorem kmsw_bdy_item_iii_literal_counterexample :
    ∃ (w : ℕ → Fin 3) (n k m : ℕ), 1 ≤ k ∧
      ((List.range (n + 1)).filter (fun t => decide
        (0 < t ∧ ∀ j, t + 1 ≤ j → j ≤ n → L w t + 1 ≤ L w j)))[k - 1]? = some m ∧
      (kmswStage w n).UL[k - 1]? ≠ some (act w m) := by
  refine ⟨fun _ => 2, 1, 1, 1, by decide, ?_, ?_⟩
  · have hrecord : ∀ j : ℕ, 1 + 1 ≤ j → j ≤ 1 →
        L (fun _ => (2 : Fin 3)) 1 + 1 ≤ L (fun _ => (2 : Fin 3)) j := by
      intro j hj hn
      omega
    change ((List.filter _ [0, 1])[0]? = some 1)
    rw [List.filter_cons_of_neg (by simp)]
    rw [List.filter_cons_of_pos (p := fun t => decide
      (0 < t ∧ ∀ j, t + 1 ≤ j → j ≤ 1 →
        L (fun _ => (2 : Fin 3)) t + 1 ≤ L (fun _ => (2 : Fin 3)) j))
      (decide_eq_true ⟨by decide, hrecord⟩)]
    rfl
  · decide

 
theorem kmsw_bdy_source_counts (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStageULDartsFinset w n).card : ℤ) = L w n - minL w n + 1 ∧
    ((kmswStageURDartsFinset w n).card : ℤ) = R w n - minR w n ∧
    ((kmswStageLLDartsFinset w n).card : ℤ) = -minL w n ∧
    ((kmswStageLRDartsFinset w n).card : ℤ) = -minR w n + 1 :=
  kmswStage_boundary_dart_cardinalities w n






theorem kmsw_bdy_source (w : ℕ → Fin 3) (n : ℕ) :
    (
    (kmswStage w n).LL.reverse =
      ((List.range (n + 1)).filter (fun m => decide
        (0 < m ∧ ∀ j < m, L w m < L w j))).map (kmswLLCreatedEdge w)
    ) ∧
    (
    ∀ (k : ℕ), 1 ≤ k → ∀ (hhit : ∃ t, L w t = -(k : ℤ)),
      Nat.find hhit ≤ n →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = kmswLLCreatedEdge w (Nat.find hhit) ∧
        (kmswStage w n).LL.reverse[k - 1]? = some e.val ∧
        (kmswStageDirectedMap w n).missing (e, true) ∧
        (kmswStageDirectedMap w n).IsOuter (e, true) ∧
        (∀ m (hm : m ≤ n),
          kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false =
              kmswBoundaryVertex w n e false ↔
            L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j) ∧
        IsLeast {m | ∃ hm : m ≤ n,
          kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false =
            kmswBoundaryVertex w n e false} (Nat.find hhit)
    ) ∧
    (
    (kmswStage w n).LR =
      ((List.range (n + 1)).filter (fun m => decide
        (∀ j, j < m → R w m < R w j))).map (act w)
    ) ∧
    (
    ∀ (k : ℕ), 1 ≤ k → ∀ (hhit : ∃ t, R w t = -(k : ℤ)), Nat.find hhit ≤ n →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = act w (Nat.find hhit) ∧
        (kmswStage w n).LR[(k + 1) - 1]? = some e.val ∧
        (e, true) ∈ (kmswStageDirectedMap w n).lrDarts ∧
        (∀ m (hm : m ≤ n),
          kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ true =
              kmswBoundaryVertex w n e true ↔
            R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j) ∧
        IsLeast {m | ∃ hm : m ≤ n,
          kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ true =
            kmswBoundaryVertex w n e true} (Nat.find hhit)
    ) ∧
    (
    (kmswStage w n).UL =
      ((List.range (n + 1)).filter (fun m => decide
        (∀ j, m + 1 ≤ j → j ≤ n → L w m + 1 ≤ L w j))).map (act w)
    ) ∧
    (
    ∀ (k m : ℕ), 1 ≤ k →
      ((List.range (n + 1)).filter (fun t => decide
        (∀ j, t + 1 ≤ j → j ≤ n → L w t + 1 ≤ L w j)))[k - 1]? = some m →
      ∃ hm : m ≤ n,
        (kmswStage w n).UL[k - 1]? = some (act w m) ∧
        (⟨act w m, act_lt_nextEdge w hm⟩, false) ∈
          (kmswStageDirectedMap w n).ulDarts ∧
        ∀ m' (hm' : m' ≤ m), L w m' = L w m →
          (∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) →
          kmswBoundaryVertex w n
              ⟨act w m', act_lt_nextEdge w (hm'.trans hm)⟩ false =
            kmswBoundaryVertex w n ⟨act w m, act_lt_nextEdge w hm⟩ false
    ) ∧
    (
    (kmswStage w n).UR.reverse =
      ((List.range (n + 1)).filter (fun m => decide
        (0 < m ∧ m ≤ n ∧ ∀ j, m ≤ j → j ≤ n →
          R w (m - 1) + 1 ≤ R w j))).map (kmswURCreatedEdge w)
    ) ∧
    (
    ∀ (k m : ℕ), 1 ≤ k →
      ((List.range (n + 1)).filter (fun t => decide
        (0 < t ∧ t ≤ n ∧ ∀ j, t ≤ j → j ≤ n →
          R w (t - 1) + 1 ≤ R w j)))[k - 1]? = some m →
      ∃ e : Fin (kmswStage w n).nextEdge,
        e.val = kmswURCreatedEdge w m ∧
        (kmswStage w n).UR.reverse[k - 1]? = some e.val ∧
        (kmswStageDirectedMap w n).missing (e, false) ∧
        (kmswStageDirectedMap w n).IsOuter (e, false)
    ) ∧
    (
    stageOuterWordVal w n =
      ((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false)) ++
      ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
      ((kmswStage w n).LL.reverse.map fun e => (e, true)) ∧
    ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d
    ) ∧
    (
    ∀ d : StageDart (kmswStage w n).nextEdge,
      (d ∈ kmswStageULDartsFinset w n ↔
        d ∈ (kmswStageDirectedMap w n).ulDarts) ∧
      (d ∈ kmswStageLRDartsFinset w n ↔
        d ∈ (kmswStageDirectedMap w n).lrDarts) ∧
      (d ∈ kmswStageLLDartsFinset w n ↔
        (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = true) ∧
      (d ∈ kmswStageURDartsFinset w n ↔
        (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = false)
    ) ∧
    (
    ((kmswStageULDartsFinset w n).card : ℤ) = L w n - minL w n + 1 ∧
    ((kmswStageURDartsFinset w n).card : ℤ) = R w n - minR w n ∧
    ((kmswStageLLDartsFinset w n).card : ℤ) = -minL w n ∧
    ((kmswStageLRDartsFinset w n).card : ℤ) = -minR w n + 1
    ) := by
  refine ⟨?_, lower_left_clause w n, kmswStage_LR_eq w n,
    lower_right_clause w n, ?_, upper_left_clause w n, ?_,
    upper_right_clause w n, kmswStage_outer_face_orbit_runs w n, ?_,
    kmsw_bdy_source_counts w n⟩
  · rw [kmswStage_LL_eq]
    simp only [List.map_reverse, List.reverse_reverse]
  · rw [kmswStage_UL_eq]
    congr 2
    funext m
    congr 1
  · rw [kmswStage_UR_eq]
    simp only [List.map_reverse, List.reverse_reverse]
  · intro d
    exact ⟨kmswStageULDartsFinset_map_mem w n d, kmswStageLRDartsFinset_map_mem w n d,
      kmswStageLLDartsFinset_map_mem w n d, kmswStageURDartsFinset_map_mem w n d⟩

end DirectedDistances.PaperProofs.Section3
