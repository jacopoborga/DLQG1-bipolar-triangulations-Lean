module

public import DirectedDistances.KMSW.CutEquivalenceConverse
import DirectedDistances.KMSW.WalkRecordCounts
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort

/-! # Stopped left-boundary mark helpers

Helper toward `lem-uiqbot-boltzmann` / Lemma 7.9
the stage before the first R-hit is indexed by the post-hit minimum of L (not
the earlier minimum displayed in `eqn-left-bdy-time`); deterministic; the
marked law assembly is not treated; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open Filter
open scoped Classical

private def stoppedRecordPred (w : ℕ → Fin 3) (n m : ℕ) : Prop :=
  ∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j

private noncomputable def stoppedRecordTimes (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun m => decide (stoppedRecordPred w n m))

private def stoppedHeightRange (N : ℕ) : List ℤ :=
  List.map Int.ofNat (List.range N)

private theorem stopped_L_step_abs_le_one (w : ℕ → Fin 3) (i : ℕ) :
    |L w (i + 1) - L w i| ≤ 1 := by
  have hL : L w (i + 1) = L w i +
      (RandomWalk.lazyTwoDimensionalStep (w i)).1 := Finset.sum_range_succ _ _
  rw [hL]
  have hc : w i = 0 ∨ w i = 1 ∨ w i = 2 := by
    have := (w i).isLt
    omega
  rcases hc with hc | hc | hc <;> rw [hc] <;>
    norm_num [RandomWalk.lazyTwoDimensionalStep]

private theorem stoppedRecordTimes_pairwise_height (w : ℕ → Fin 3) (n : ℕ) :
    ((stoppedRecordTimes w n).map (L w)).Pairwise (· < ·) := by
  classical
  have hraw : (List.range (n + 1)).Pairwise
      (fun a b => stoppedRecordPred w n a →
        stoppedRecordPred w n b → L w a < L w b) := by
    have hrange : (List.range (n + 1)).Pairwise (· < ·) :=
      List.pairwise_lt_range
    apply hrange.imp_of_mem
    intro a b ha hb hab hpa _
    have hbn : b ≤ n := by
      have hb' := List.mem_range.mp hb
      omega
    exact hpa b hab hbn
  unfold stoppedRecordTimes
  rw [List.pairwise_map, List.pairwise_filter]
  simpa only [decide_eq_true_eq] using hraw

private theorem stoppedRecordHeights_mem_iff (w : ℕ → Fin 3) (n : ℕ)
    (hL0 : ∀ s, 0 ≤ L w s) (x : ℤ) :
    x ∈ (stoppedRecordTimes w n).map (L w) ↔
      x ∈ stoppedHeightRange ((L w n).toNat + 1) := by
  classical
  constructor
  · intro hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    have hparts := List.mem_filter.mp hm
    have hpred := of_decide_eq_true hparts.2
    have hmn : m ≤ n := by
      have hmr := List.mem_range.mp hparts.1
      omega
    have hle : L w m ≤ L w n := by
      by_cases hEq : m = n
      · simp [hEq]
      · have hlt : m < n := by omega
        have hh := hpred n hlt le_rfl
        omega
    have hcast := Int.toNat_of_nonneg (hL0 m)
    have hbound : (L w m).toNat < (L w n).toNat + 1 := by
      have hNcast := Int.toNat_of_nonneg (hL0 n)
      omega
    change L w m ∈ List.map Int.ofNat
      (List.range ((L w n).toNat + 1))
    exact List.mem_map.mpr ⟨(L w m).toNat,
      List.mem_range.mpr hbound, by simpa using hcast⟩
  · intro hx
    change x ∈ List.map Int.ofNat
      (List.range ((L w n).toNat + 1)) at hx
    obtain ⟨k, hk, hxk⟩ := List.mem_map.mp hx
    have hNcast := Int.toNat_of_nonneg (hL0 n)
    have hkbound : (k : ℤ) ≤ L w n := by
      have hk' := List.mem_range.mp hk
      omega
    have hglobal : RandomWalk.globalLazyRunningMinimum (L w) n = 0 := by
      apply le_antisymm
      · have hzero : L w 0 = 0 := by simp [L]
        exact (RandomWalk.globalLazyRunningMinimum_le (L w) (Nat.zero_le n)).trans_eq
          hzero
      · apply RandomWalk.le_globalLazyRunningMinimum
        intro i hi
        exact hL0 i
    obtain ⟨m, hm, _⟩ := future_strict_record_level_unique (L w)
      (stopped_L_step_abs_le_one w) n (k : ℤ) (by rw [hglobal]; omega) hkbound
    have hparts := Finset.mem_filter.mp hm.1
    have hmList : m ∈ stoppedRecordTimes w n := by
      unfold stoppedRecordTimes
      apply List.mem_filter.mpr
      refine ⟨List.mem_range.mpr (Finset.mem_range.mp hparts.1), ?_⟩
      exact decide_eq_true hparts.2
    apply List.mem_map.mpr
    exact ⟨m, hmList, hm.2.trans hxk⟩

private theorem stoppedRecordHeights_eq_range (w : ℕ → Fin 3) (n : ℕ)
    (hL0 : ∀ s, 0 ≤ L w s) :
    (stoppedRecordTimes w n).map (L w) =
      stoppedHeightRange ((L w n).toNat + 1) := by
  have hleft : ((stoppedRecordTimes w n).map (L w)).SortedLT :=
    (stoppedRecordTimes_pairwise_height w n).sortedLT
  have hright : (stoppedHeightRange ((L w n).toNat + 1)).SortedLT := by
    change (List.map Int.ofNat (List.range ((L w n).toNat + 1))).SortedLT
    have hpair : (List.map Int.ofNat
        (List.range ((L w n).toNat + 1))).Pairwise (· < ·) :=
      List.Pairwise.map Int.ofNat (fun a b hab => Int.ofNat_lt.mpr hab)
        (List.sortedLT_range _).pairwise
    exact hpair.sortedLT
  exact hleft.eq_of_mem_iff hright (stoppedRecordHeights_mem_iff w n hL0)

/-- Ordered vertex IDs on the upper-left stage path through its terminal -/
@[expose] def stoppedLeftBoundaryVertices (w : ℕ → Fin 3) (t : ℕ) : List ℕ :=
  let s := kmswStage w (t - 1)
  s.UL.map s.west ++ [s.east (act w (t - 1))]

private theorem stopped_hit_before_strict {w : ℕ → Fin 3} {r t : ℕ}
    (hr : 1 ≤ r) (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ)) :
    ∀ s < t, -(r : ℤ) < R w s := by
  intro s hs
  induction s with
  | zero =>
    have hzero : R w 0 = 0 := by simp [R]
    rw [hzero]
    omega
  | succ s ih =>
    have hprev := ih (by omega)
    have hstepLower : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w s)).2 := by
      have hc : w s = 0 ∨ w s = 1 ∨ w s = 2 := by
        have := (w s).isLt
        omega
      rcases hc with hc | hc | hc <;> rw [hc] <;>
        simp [RandomWalk.lazyTwoDimensionalStep]
    have hR : R w (s + 1) = R w s +
        (RandomWalk.lazyTwoDimensionalStep (w s)).2 :=
      Finset.sum_range_succ _ _
    by_contra hbad
    have hle : R w (s + 1) ≤ -(r : ℤ) := by omega
    have hge : -(r : ℤ) ≤ R w (s + 1) := by rw [hR]; omega
    have heq : R w (s + 1) = -(r : ℤ) := by omega
    exact (hfirst (s + 1) hs) heq

private theorem stopped_hit_down {w : ℕ → Fin 3} {r t : ℕ}
    (hr : 1 ≤ r) (ht : 0 < t) (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ)) :
    w (t - 1) = 2 := by
  have hidx : t - 1 + 1 = t := by omega
  have hR : R w t = R w (t - 1) +
      (RandomWalk.lazyTwoDimensionalStep (w (t - 1))).2 := by
    rw [← hidx]
    exact Finset.sum_range_succ _ _
  have hprev := stopped_hit_before_strict hr hhit hfirst (t - 1) (by omega)
  have hc : w (t - 1) = 0 ∨ w (t - 1) = 1 ∨ w (t - 1) = 2 := by
    have := (w (t - 1)).isLt
    omega
  rcases hc with hc | hc | hc
  · rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hR
    omega
  · rw [hc, RandomWalk.lazyTwoDimensionalStep_one] at hR
    omega
  · exact hc

private theorem stopped_minL_eq_zero {w : ℕ → Fin 3} (n : ℕ)
    (hL0 : ∀ s, 0 ≤ L w s) : minL w n = 0 := by
  obtain ⟨i, hi, hmin⟩ := runningMin_attained (L w) n
  have hmin' : minL w n = L w i := hmin
  have hle := runningMin_le (L w) n 0 (by omega)
  change minL w n ≤ L w 0 at hle
  have hzero : L w 0 = 0 := by simp [L]
  rw [hzero] at hle
  exact le_antisymm hle (by rw [hmin']; exact hL0 i)

/-- The finite list includes exactly `L(w,t)+1` vertices when `t` is the -/
theorem stoppedLeftBoundaryVertices_length (w : ℕ → Fin 3) {r t : ℕ}
    (hr : 1 ≤ r) (ht : 0 < t) (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ))
    (hL0 : ∀ s, 0 ≤ L w s) :
    (stoppedLeftBoundaryVertices w t).length = (L w t).toNat + 1 := by
  let n := t - 1
  have hidx : n + 1 = t := by dsimp [n]; omega
  have hdown : w n = 2 := stopped_hit_down hr ht hhit hfirst
  have hLstep : L w t = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    rw [← hidx]
    exact Finset.sum_range_succ _ _
  have hLinc : L w t = L w n + 1 := by
    rw [hdown, RandomWalk.lazyTwoDimensionalStep_two] at hLstep
    exact hLstep
  have hmin : minL w n = 0 := stopped_minL_eq_zero n hL0
  have hlenInt : ((kmswStage w n).UL.length : ℤ) = L w t := by
    rw [kmswStage_UL_length, hmin, hLinc]
    omega
  have hnonneg : 0 ≤ L w t := hL0 t
  have hnat : ((L w t).toNat : ℤ) = L w t := Int.toNat_of_nonneg hnonneg
  have hlenCast : ((kmswStage w n).UL.length : ℤ) =
      ((L w t).toNat : ℤ) := hlenInt.trans hnat.symm
  have hlen : (kmswStage w n).UL.length = (L w t).toNat := by exact_mod_cast hlenCast
  simp [stoppedLeftBoundaryVertices, n, List.length_append, hlen]

private theorem stopped_down_initial (w : ℕ → Fin 3) (n : ℕ)
    (hw : w n = 2) :
    activeInitial w (n + 1) = (kmswStage w n).east (act w n) := by
  rw [CutConverse.activeInitial_eq]
  cases hu : (kmswStage w n).UR with
  | nil =>
    simp [act, kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      hu, State.addEdge]
  | cons e es =>
    have hc := (CutConverse.frontier_history w n).1
    have he : (kmswStage w n).west e = (kmswStage w n).east (act w n) := by
      have hh := congrArg List.head? hc
      simpa [CutConverse.FrontierCoherent, CutConverse.pendingVertices,
        hu, act] using hh
    simpa [act, kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      hu] using he

/-- The terminal vertex in the ordered list is the active initial vertex at -/
theorem stoppedLeftBoundaryVertices_sink_eq_activeInitial (w : ℕ → Fin 3)
    {r t : ℕ} (hr : 1 ≤ r) (ht : 0 < t)
    (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ)) :
    (stoppedLeftBoundaryVertices w t).getLast? =
      some (activeInitial w t) := by
  let n := t - 1
  have hidx : n + 1 = t := by dsimp [n]; omega
  have hdown : w n = 2 := stopped_hit_down hr ht hhit hfirst
  have hhandoff : activeInitial w t =
      (kmswStage w n).east (act w n) := by
    rw [← hidx]
    exact stopped_down_initial w n hdown
  simp [stoppedLeftBoundaryVertices, n, hhandoff]

/-- The ordered finite upper-left path has no repeated vertex IDs -/
theorem stoppedLeftBoundaryVertices_nodup (w : ℕ → Fin 3) (t : ℕ) :
    (stoppedLeftBoundaryVertices w t).Nodup := by
  let n := t - 1
  have h := CutConverse.ul_path_vertices_nodup w n
  have hrev := List.nodup_reverse.mpr h
  simpa [stoppedLeftBoundaryVertices, n, CutConverse.westStack,
    List.reverse_cons, List.reverse_append, List.map_reverse,
    List.reverse_reverse] using hrev

private theorem stoppedUL_vertices_eq_records (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.map (kmswStage w n).west =
      (stoppedRecordTimes w n).map (activeInitial w) := by
  rw [kmswStage_UL_eq]
  unfold stoppedRecordTimes
  simp only [List.map_map]
  apply List.map_congr_left
  intro m hm
  have hparts := List.mem_filter.mp hm
  have hmn : m ≤ n := by
    have hmr := List.mem_range.mp hparts.1
    omega
  have hstable := kmswStage_endpoints_stable w hmn
    (act_lt_nextEdge w (m := m) (n := m) le_rfl)
  rw [CutConverse.activeInitial_eq]
  exact hstable.1

/-- A vertex before the terminal sink has its ordered height and survives -/
theorem stoppedLeftBoundaryVertices_prefix_height (w : ℕ → Fin 3)
    {r t j : ℕ} (hr : 1 ≤ r) (ht : 0 < t)
    (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ))
    (hL0 : ∀ s, 0 ≤ L w s) (hj : j < (L w t).toNat) :
    ∃ a, a ≤ t ∧ L w a = (j : ℤ) ∧
      (∀ s, a ≤ s → s ≤ t → (j : ℤ) ≤ L w s) ∧
      (stoppedLeftBoundaryVertices w t).getD j (activeInitial w 0) =
        activeInitial w a := by
  let n := t - 1
  let times := stoppedRecordTimes w n
  have hidx : n + 1 = t := by dsimp [n]; omega
  have hdown : w n = 2 := stopped_hit_down hr ht hhit hfirst
  have hLinc : L w t = L w n + 1 := by
    have hstep : L w t = L w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
      rw [← hidx]
      exact Finset.sum_range_succ _ _
    rw [hdown, RandomWalk.lazyTwoDimensionalStep_two] at hstep
    exact hstep
  have hlenList := stoppedLeftBoundaryVertices_length w hr ht hhit hfirst hL0
  have hULlen : (kmswStage w n).UL.length = (L w t).toNat := by
    simp [stoppedLeftBoundaryVertices, List.length_append] at hlenList
    omega
  have hcastT : ((L w t).toNat : ℤ) = L w t := Int.toNat_of_nonneg (hL0 t)
  have hcastN : ((L w n).toNat : ℤ) = L w n := Int.toNat_of_nonneg (hL0 n)
  have hnatLen : (L w t).toNat = (L w n).toNat + 1 := by
    have hcast : ((L w t).toNat : ℤ) = ((L w n).toNat : ℤ) + 1 := by
      rw [hcastT, hcastN, hLinc]
    exact_mod_cast hcast
  have htimesLen : times.length = (L w t).toNat := by
    have hmaplen := congrArg List.length (stoppedRecordHeights_eq_range w n hL0)
    have htimesLen' : times.length = (L w n).toNat + 1 := by
      simpa [stoppedHeightRange] using hmaplen
    simpa [times, hnatLen] using htimesLen'
  have hjtime : j < times.length := by rw [htimesLen]; exact hj
  let a := times.getD j 0
  have haMem : a ∈ times := by
    have hget : times.getD j 0 = times.get ⟨j, hjtime⟩ :=
      List.getD_eq_get times 0 ⟨j, hjtime⟩
    change times.getD j 0 ∈ times
    rw [hget]
    exact List.get_mem times ⟨j, hjtime⟩
  have haMem' : a ∈ (List.range (n + 1)).filter
      (fun m => decide (stoppedRecordPred w n m)) := by
    simpa [times, stoppedRecordTimes] using haMem
  have haparts := List.mem_filter.mp haMem'
  have hpred : stoppedRecordPred w n a := of_decide_eq_true haparts.2
  have han : a ≤ n := by
    have harange := List.mem_range.mp haparts.1
    omega
  have hgetHeight : L w a = (j : ℤ) := by
    have hheights := stoppedRecordHeights_eq_range w n hL0
    have hget := congrArg (fun xs : List ℤ => xs.getD j 0) hheights
    have hgetRange : (List.range ((L w n).toNat + 1)).getD j 0 = j := by
      have hjrange : j < (List.range ((L w n).toNat + 1)).length := by
        simp
        omega
      rw [List.getD_eq_get (List.range ((L w n).toNat + 1)) 0
        ⟨j, hjrange⟩]
      simp
    change (times.map (L w)).getD j (L w 0) =
      (List.map Int.ofNat (List.range ((L w n).toNat + 1))).getD j 0 at hget
    have hgetRangeInt : (List.map Int.ofNat
        (List.range ((L w n).toNat + 1))).getD j 0 = (j : ℤ) := by
      change (List.map Int.ofNat
        (List.range ((L w n).toNat + 1))).getD j (Int.ofNat 0) = _
      rw [List.getD_map, hgetRange]
      rfl
    change (times.map (L w)).getD j (L w 0) =
      (List.map Int.ofNat (List.range ((L w n).toNat + 1))).getD j
        (Int.ofNat 0) at hget
    rw [List.getD_map] at hget
    have hgetRangeInt' : (List.map Int.ofNat
        (List.range ((L w n).toNat + 1))).getD j (Int.ofNat 0) =
          (j : ℤ) := by simpa using hgetRangeInt
    rw [hgetRangeInt'] at hget
    simpa [times, a] using hget
  have hgetVertex :
      ((kmswStage w n).UL.map (kmswStage w n).west).getD j
        (activeInitial w 0) = activeInitial w a := by
    have hvertices := stoppedUL_vertices_eq_records w n
    rw [hvertices, List.getD_map]
  have hvertexIndex : j < ((kmswStage w n).UL.map (kmswStage w n).west).length := by
    simp only [List.length_map]
    rw [hULlen]
    exact hj
  have hlistGet : (stoppedLeftBoundaryVertices w t).getD j
      (activeInitial w 0) =
        ((kmswStage w n).UL.map (kmswStage w n).west).getD j
          (activeInitial w 0) := by
    simpa [stoppedLeftBoundaryVertices, n] using
      (List.getD_append _ _ _ j hvertexIndex)
  have hbarrier : ∀ s, a ≤ s → s ≤ t → (j : ℤ) ≤ L w s := by
    intro s has hst
    by_cases hsn : s ≤ n
    · by_cases hEq : s = a
      · subst s
        rw [hgetHeight]
      · have hlt : a < s := by omega
        have hh := hpred s hlt (by omega)
        rw [hgetHeight] at hh
        omega
    · have hs : s = t := by dsimp [n] at hsn; omega
      subst s
      have hlt : (j : ℤ) < L w t := by
        exact (Int.ofNat_lt.mpr hj).trans_eq hcastT
      exact hlt.le
  exact ⟨a, by omega, hgetHeight, hbarrier, hlistGet.trans hgetVertex⟩

/-- Every ordered stage vertex is represented by its height and survives from
that visit through the first R-hit, including the terminal sink -/
theorem stoppedLeftBoundaryVertices_ordered_height (w : ℕ → Fin 3)
    {r t j : ℕ} (hr : 1 ≤ r) (ht : 0 < t)
    (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ))
    (hL0 : ∀ s, 0 ≤ L w s) (hj : j < (L w t).toNat + 1) :
    ∃ a, a ≤ t ∧ L w a = (j : ℤ) ∧
      (∀ s, a ≤ s → s ≤ t → (j : ℤ) ≤ L w s) ∧
      (stoppedLeftBoundaryVertices w t).getD j (activeInitial w 0) =
        activeInitial w a := by
  by_cases hjlt : j < (L w t).toNat
  · obtain ⟨a, ha, hlevel, hbarrier, hvertex⟩ :=
      stoppedLeftBoundaryVertices_prefix_height w hr ht hhit hfirst hL0 hjlt
    exact ⟨a, ha, hlevel, hbarrier, hvertex⟩
  · have hjEq : j = (L w t).toNat := by omega
    let n := t - 1
    have hidx : n + 1 = t := by dsimp [n]; omega
    have hdown : w n = 2 := stopped_hit_down hr ht hhit hfirst
    have hhandoff : activeInitial w t =
        (kmswStage w n).east (act w n) := by
      rw [← hidx]
      exact stopped_down_initial w n hdown
    have hlistLen := stoppedLeftBoundaryVertices_length w hr ht hhit hfirst hL0
    have hULlen : (kmswStage w n).UL.length = (L w t).toNat := by
      simp [stoppedLeftBoundaryVertices, List.length_append] at hlistLen
      omega
    have hvertex :
        (stoppedLeftBoundaryVertices w t).getD j (activeInitial w 0) =
          activeInitial w t := by
      have happend :
          ((kmswStage w n).UL.map (kmswStage w n).west ++
            [(kmswStage w n).east (act w n)]).getD j (activeInitial w 0) =
              (kmswStage w n).east (act w n) := by
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, hULlen, hjEq])]
        simp [hjEq, hULlen]
      simpa [stoppedLeftBoundaryVertices, n, hhandoff] using happend
    have hlevel : L w t = (j : ℤ) := by
      rw [hjEq]
      exact (Int.toNat_of_nonneg (hL0 t)).symm
    have hbarrier : ∀ s, t ≤ s → s ≤ t → (j : ℤ) ≤ L w s := by
      intro s hts hst
      have : s = t := by omega
      subst s
      rw [← hlevel]
    exact ⟨t, le_rfl, hlevel, hbarrier, hvertex⟩

/-- Infinite left-boundary incidence of any visited initial vertex is exactly
its weak all-future horizontal barrier (`lem-cut-equiv`, -/
theorem onLeftBoundary_activeInitial_iff_barrier (w : ℕ → Fin 3)
    (htrans : Tendsto (L w) atTop atTop) (a : ℕ) :
    OnLeftBoundary w (activeInitial w a) ↔
      ∀ s, a ≤ s → L w a ≤ L w s := by
  constructor
  · rintro ⟨e, he, hv⟩ s has
    obtain ⟨J, hJ, hJnot⟩ := he.exists_notMem_finset (Finset.range s)
    have hsJ : s ≤ J := by
      simpa only [Finset.mem_range, not_lt] using hJnot
    have hmem := CutConverse.westStack_mem_of_UL_incidence w
      (has.trans hsJ) hJ hv
    exact CutConverse.barrier_of_westStack_mem w (has.trans hsJ) hmem
      s has hsJ
  · exact onLeftBoundary_activeInitial_of_barrier w htrans a

/-- Infinite left-boundary incidence of each ordered stopped vertex is exactly -/
theorem stoppedLeftBoundaryVertices_onLeftBoundary_iff (w : ℕ → Fin 3)
    {r t j : ℕ} (hr : 1 ≤ r) (ht : 0 < t)
    (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ))
    (hL0 : ∀ s, 0 ≤ L w s)
    (htrans : Tendsto (L w) atTop atTop)
    (hj : j < (L w t).toNat + 1) :
    OnLeftBoundary w
        ((stoppedLeftBoundaryVertices w t).getD j (activeInitial w 0)) ↔
      ∀ s, t ≤ s → (j : ℤ) ≤ L w s := by
  obtain ⟨a, hat, hlevel, hprefix, hvertex⟩ :=
    stoppedLeftBoundaryVertices_ordered_height w hr ht hhit hfirst hL0 hj
  rw [hvertex, onLeftBoundary_activeInitial_iff_barrier w htrans a]
  rw [hlevel]
  constructor
  · intro h s hts
    exact h s (hat.trans hts)
  · intro h s has
    by_cases hst : s ≤ t
    · exact hprefix s has hst
    · exact h s (by omega)

/-- The shared ordered vertices are exactly those at or below the attained -/
theorem stoppedLeftBoundaryVertices_shared_indices (w : ℕ → Fin 3)
    {r t : ℕ} (hr : 1 ≤ r) (ht : 0 < t)
    (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ))
    (hL0 : ∀ s, 0 ≤ L w s)
    (htrans : Tendsto (L w) atTop atTop) :
    ∃ m ≤ (L w t).toNat,
      (∃ u, t ≤ u ∧ L w u = (m : ℤ)) ∧
      (∀ s, t ≤ s → (m : ℤ) ≤ L w s) ∧
      ∀ j, j ≤ (L w t).toNat →
        (OnLeftBoundary w
          ((stoppedLeftBoundaryVertices w t).getD j (activeInitial w 0)) ↔ j ≤ m) := by
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp htrans (L w t + 1)
  let M := max N t
  have htM : t ≤ M := le_max_right N t
  let S := Finset.Icc t M
  have htS : t ∈ S := Finset.mem_Icc.mpr ⟨le_rfl, htM⟩
  let z := S.inf' ⟨t, htS⟩ (L w)
  obtain ⟨u, huS, huz⟩ := Finset.exists_mem_eq_inf'
    (s := S) ⟨t, htS⟩ (L w)
  have hzEq : z = L w u := by simpa [z] using huz
  have hzle : z ≤ L w t := Finset.inf'_le (L w) htS
  have hz0 : 0 ≤ z := by
    change 0 ≤ S.inf' ⟨t, htS⟩ (L w)
    rw [huz]
    exact hL0 u
  have hzbarrier : ∀ s, t ≤ s → z ≤ L w s := by
    intro s hts
    by_cases hsM : s ≤ M
    · exact Finset.inf'_le (L w) (Finset.mem_Icc.mpr ⟨hts, hsM⟩)
    · have hNs : N ≤ s := by dsimp [M] at hsM; omega
      have := hN s hNs
      omega
  let m := z.toNat
  have hmcast : (m : ℤ) = z := Int.toNat_of_nonneg hz0
  have hmbound : m ≤ (L w t).toNat := by
    have hcast := Int.toNat_of_nonneg (hL0 t)
    omega
  refine ⟨m, hmbound, ⟨u, (Finset.mem_Icc.mp huS).1, ?_⟩,
    ?_, ?_⟩
  · exact huz.symm.trans hmcast.symm
  · intro s hts
    calc
      (m : ℤ) = z := hmcast
      _ ≤ L w s := hzbarrier s hts
  · intro j hj
    have hj' : j < (L w t).toNat + 1 := Nat.lt_succ_of_le hj
    have hcrit := stoppedLeftBoundaryVertices_onLeftBoundary_iff w hr ht
      hhit hfirst hL0 htrans (hj := hj')
    rw [hcrit]
    constructor
    · intro hjbar
      have hju := hjbar u (Finset.mem_Icc.mp huS).1
      have hjz : (j : ℤ) ≤ z := hju.trans (le_of_eq hzEq.symm)
      rw [← hmcast] at hjz
      exact_mod_cast hjz
    · intro hjm s hts
      have hjle : (j : ℤ) ≤ z := by rw [← hmcast]; exact_mod_cast hjm
      exact hjle.trans (hzbarrier s hts)

end DirectedDistances.KMSW
