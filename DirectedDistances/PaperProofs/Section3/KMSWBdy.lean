/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageBoundaryMap
public import DirectedDistances.KMSW.BoundaryRecordsUL
public import DirectedDistances.KMSW.BoundaryRecordsMissing
public import DirectedDistances.KMSW.WalkRecordCounts
import DirectedDistances.KMSW.BoundaryVertexVisits

/-! Supporting lemmas for paper labels `lem-kmsw-bdy` (see CORRESPONDENCE.md). -/

/- # Candidate provider for Lemma 3.6 boundary bookkeeping

This file is a candidate provider and is not counted as a proved paper result -/

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped Classical

/-- In an increasing filtered initial segment, the zero-based rank of `m` is
the number of qualifying times before `m`. This supplies the order-to-rank -/
theorem kmsw_bdy_range_filter_getElem_at_rank {p : ℕ → Bool} {n m : ℕ}
    (hmn : m ≤ n) (hp : p m = true) :
    ∃ h : ((List.range m).filter p).length < ((List.range (n + 1)).filter p).length,
      ((List.range (n + 1)).filter p)[((List.range m).filter p).length]'h = m := by
  have hsplit : List.range (n + 1) =
      List.range m ++ (List.range (n + 1 - m)).map (m + ·) := by
    have hsum : m + (n + 1 - m) = n + 1 := by omega
    calc
      List.range (n + 1) = List.range (m + (n + 1 - m)) := by rw [hsum]
      _ = List.range m ++ (List.range (n + 1 - m)).map (m + ·) := List.range_add
  have hlen : n + 1 - m = n - m + 1 := by omega
  have htail : (List.range (n + 1 - m)).map (m + ·) =
      m :: ((List.range (n - m)).map (fun i => m + i.succ)) := by
    rw [hlen, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
  have hfiltered : (List.range (n + 1)).filter p =
      (List.range m).filter p ++ m ::
        (((List.range (n - m)).map (fun i => m + i.succ)).filter p) := by
    simp only [hsplit, List.filter_append, htail, List.filter_cons, hp, ↓reduceIte]
  have hidx : ((List.range m).filter p).length < ((List.range (n + 1)).filter p).length := by
    rw [hfiltered]
    simp
  refine ⟨hidx, ?_⟩
  have hget := List.getElem_append_right' ((List.range m).filter p)
    (by simp : 0 < (m :: (((List.range (n - m)).map (fun i => m + i.succ)).filter p)).length)
  simp [hfiltered]

private theorem kmswStep_active_not_present_before (s : State) (c : Fin 3)
    (hids : ∀ e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR, e < s.nextEdge)
    (hmissing : ∀ e < s.nextEdge,
      (s.present e = false ↔ e ∈ s.UR ∨ e ∈ s.LL)) :
    ¬ ((kmswStep s c).active < s.nextEdge ∧
      s.present (kmswStep s c).active = true) := by
  by_cases h0 : c = 0
  · subst c
    cases hstack : s.UL.dropLast.reverse with
    | nil => simp [kmswStep, kmswCodeStep, kmswStepOfStep, hstack, State.addEdge]
    | cons e es => simp [kmswStep, kmswCodeStep, kmswStepOfStep, hstack, State.addEdge]
  · by_cases h1 : c = 1
    · subst c
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
    · have h2 : c = 2 := by
        apply Fin.ext
        have hc := c.isLt
        have hc0 : c.val ≠ 0 := by intro h; exact h0 (Fin.ext h)
        have hc1 : c.val ≠ 1 := by intro h; exact h1 (Fin.ext h)
        omega
      subst c
      cases hur : s.UR with
      | nil =>
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hur, State.addEdge]
      | cons e es =>
        have he : e < s.nextEdge := by
          apply hids
          simp [hur]
        have hfalse : s.present e = false :=
          (hmissing e he).2 (Or.inl (by simp [hur]))
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hur, hfalse]

private theorem kmswStage_active_not_present_previous (w : ℕ → Fin 3) (n : ℕ) :
    ¬ ((kmswStage w (n + 1)).active < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present (act w (n + 1)) = true) := by
  exact kmswStep_active_not_present_before (kmswStage w n) (w n)
    (kmswStage_boundary_ids_lt_nextEdge w n).2 (kmswStage_status w n).1

private theorem kmswStage_active_present_local (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).present (act w n) = true := by
  obtain ⟨es, hlast⟩ := kmswStage_UL_last w n
  have hmem : act w n ∈ (kmswStage w n).UL := by
    rw [hlast]
    simp [act]
  exact (kmswStage_status w n).2.1 _ hmem

private theorem kmsw_step_coordinate_bounds (c : Fin 3) :
    (-1 ≤ (RandomWalk.lazyTwoDimensionalStep c).1 ∧
      (RandomWalk.lazyTwoDimensionalStep c).1 ≤ 1) ∧
    (-1 ≤ (RandomWalk.lazyTwoDimensionalStep c).2 ∧
      (RandomWalk.lazyTwoDimensionalStep c).2 ≤ 1) := by
  by_cases h0 : c = 0
  · simp [h0, RandomWalk.lazyTwoDimensionalStep_zero]
  · by_cases h1 : c = 1
    · simp [h1, RandomWalk.lazyTwoDimensionalStep_one]
    · have h2 : c = 2 := by
        apply Fin.ext
        have hc := c.isLt
        have hc0 : c.val ≠ 0 := by intro h; exact h0 (Fin.ext h)
        have hc1 : c.val ≠ 1 := by intro h; exact h1 (Fin.ext h)
        omega
      simp [h2, RandomWalk.lazyTwoDimensionalStep_two]

private theorem kmsw_L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem kmsw_R_succ (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem kmsw_L_walk_step_bound (w : ℕ → Fin 3) (n : ℕ) :
    |L w (n + 1) - L w n| ≤ 1 := by
  rw [kmsw_L_succ]
  have h := (kmsw_step_coordinate_bounds (w n)).1
  have heq : L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 - L w n =
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by omega
  rw [heq]
  exact abs_le.mpr h

private theorem kmsw_R_walk_step_bound (w : ℕ → Fin 3) (n : ℕ) :
    |R w (n + 1) - R w n| ≤ 1 := by
  rw [kmsw_R_succ]
  have h := (kmsw_step_coordinate_bounds (w n)).2
  have heq : R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 - R w n =
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by omega
  rw [heq]
  exact abs_le.mpr h

private theorem kmsw_bdy_runningMin_eq_global (p : ℕ → ℤ) (n : ℕ) :
    globalLazyRunningMinimum p n = runningMin p n := by
  apply le_antisymm
  · obtain ⟨j, hj, hval⟩ := runningMin_attained p n
    rw [hval]
    exact globalLazyRunningMinimum_le p hj
  · apply le_globalLazyRunningMinimum
    intro j hj
    exact runningMin_le p n j hj

/-- Every level down to the closed-prefix minimum is hit by the left -/
theorem kmsw_bdy_lower_left_hit_exists (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkmin : (k : ℤ) ≤ -minL w n) :
    ∃ hhit : ∃ t, L w t = -(k : ℤ), Nat.find hhit ≤ n := by
  have hmin : globalLazyRunningMinimum (L w) n ≤ -(k : ℤ) := by
    have hmin' : minL w n ≤ -(k : ℤ) := by omega
    simpa [minL, kmsw_bdy_runningMin_eq_global] using hmin'
  have hkneg : -(k : ℤ) < 0 := by omega
  obtain ⟨t, ⟨htmem, htval⟩, _⟩ :=
    strict_running_minimum_level_unique (L w) (by simp [L])
      (kmsw_L_walk_step_bound w) n (-(k : ℤ)) hmin hkneg
  have htn : t ≤ n := by
    have := Finset.mem_Icc.mp (Finset.mem_filter.mp htmem).1
    omega
  let hhit : ∃ i, L w i = -(k : ℤ) := ⟨t, htval⟩
  have hfirst : Nat.find hhit ≤ n := by
    have hfind := Nat.find_min' hhit htval
    omega
  exact ⟨hhit, hfirst⟩

/-- Every level down to the closed-prefix minimum is hit by the right -/
theorem kmsw_bdy_lower_right_hit_exists (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkmin : (k : ℤ) ≤ -minR w n) :
    ∃ hhit : ∃ t, R w t = -(k : ℤ), Nat.find hhit ≤ n := by
  have hmin : globalLazyRunningMinimum (R w) n ≤ -(k : ℤ) := by
    have hmin' : minR w n ≤ -(k : ℤ) := by omega
    simpa [minR, kmsw_bdy_runningMin_eq_global] using hmin'
  have hkneg : -(k : ℤ) < 0 := by omega
  obtain ⟨t, ⟨htmem, htval⟩, _⟩ :=
    strict_running_minimum_level_unique (R w) (by simp [R])
      (kmsw_R_walk_step_bound w) n (-(k : ℤ)) hmin hkneg
  have htn : t ≤ n := by
    have := Finset.mem_Icc.mp (Finset.mem_filter.mp htmem).1
    omega
  let hhit : ∃ i, R w i = -(k : ℤ) := ⟨t, htval⟩
  have hfirst : Nat.find hhit ≤ n := by
    have hfind := Nat.find_min' hhit htval
    omega
  exact ⟨hhit, hfirst⟩

private theorem kmsw_runningMin_prev_of_strict_record
    (p : ℕ → ℤ) (m : ℕ) (ℓ : ℤ)
    (hm : 0 < m) (hpm : p m = ℓ)
    (hrec : ∀ j, j < m → ℓ < p j)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) :
    runningMin p (m - 1) = ℓ + 1 := by
  have hprevrec : ℓ < p (m - 1) := hrec (m - 1) (by omega)
  have hstep' := hstep (m - 1)
  have hprev : p (m - 1) = ℓ + 1 := by
    rw [show (m - 1) + 1 = m by omega] at hstep'
    rw [hpm] at hstep'
    have hbounds := abs_le.mp hstep'
    omega
  obtain ⟨j, hj, hjmin⟩ := runningMin_attained p (m - 1)
  have hlow : ℓ + 1 ≤ p j := by
    have hjrec := hrec j (by omega)
    omega
  have hlowmin : ℓ + 1 ≤ runningMin p (m - 1) := by
    rw [hjmin]
    exact hlow
  have hu := runningMin_le p (m - 1) (m - 1) (le_rfl)
  rw [hprev] at hu
  omega

private theorem kmswLLCreatedEdge_allocated_at_record (w : ℕ → Fin 3) {m : ℕ}
    (hm : 0 < m) (hrec : ∀ j, j < m → L w m < L w j) :
    (kmswStage w (m - 1)).nextEdge ≤ kmswLLCreatedEdge w m ∧
      kmswLLCreatedEdge w m < (kmswStage w m).nextEdge := by
  cases m with
  | zero => omega
  | succ n =>
    have hrec' : ∀ j ≤ n, L w (n + 1) < L w j := by
      intro j hj
      exact hrec j (by omega)
    have hc : w n = 0 := by
      by_cases h0 : w n = 0
      · exact h0
      · by_cases h1 : w n = 1
        · have hs := kmsw_L_succ w n
          rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hs
          have hh := hrec' n (le_refl _)
          omega
        · have h2 : w n = 2 := by
            apply Fin.ext
            have hv := (w n).isLt
            have hn0 : (w n).val ≠ 0 := by intro h; exact h0 (Fin.ext h)
            have hn1 : (w n).val ≠ 1 := by intro h; exact h1 (Fin.ext h)
            omega
          have hs := kmsw_L_succ w n
          rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hs
          have hh := hrec' n (le_refl _)
          omega
    have hmin : minL w n = L w n := by
      have hrecStrict : ∀ j, j < n + 1 → L w (n + 1) < L w j := by
        intro j hj
        exact hrec' j (by omega)
      have hrun := kmsw_runningMin_prev_of_strict_record
        (L w) (n + 1) (L w (n + 1)) (by omega) rfl hrecStrict
        (kmsw_L_walk_step_bound w)
      have hs := kmsw_L_succ w n
      rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hs
      have hrun' : minL w n = L w (n + 1) + 1 := by simpa [minL] using hrun
      rw [hrun']
      omega
    have hULlen : (kmswStage w n).UL.length = 1 := by
      have hlen := kmswStage_UL_length w n
      rw [hmin] at hlen
      have hs := kmsw_L_succ w n
      rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hs
      omega
    obtain ⟨es, hes⟩ := kmswStage_UL_last w n
    have hesLen : es.length = 0 := by
      rw [hes] at hULlen
      simp only [List.length_append, List.length_singleton] at hULlen
      omega
    have hesNil : es = [] := List.length_eq_zero_iff.mp hesLen
    have hstack : (kmswStage w n).UL.dropLast.reverse = [] := by
      rw [hes, hesNil]
      simp
    have hcreated : kmswLLCreatedEdge w (n + 1) = (kmswStage w n).nextEdge + 1 := by
      simp [kmswLLCreatedEdge, kmswStage, hc, kmswCodeStep, kmswStep,
        kmswStepOfStep, hstack, State.addEdge]
    have hnext : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 := by
      simp [kmswStage, hc, kmswCodeStep, kmswStep, kmswStepOfStep, hstack, State.addEdge]
    simp only [Nat.succ_sub_one]
    rw [hcreated, hnext]
    omega

/-- Clause (iii) as an increasing zero-based rank statement. The record-time
filter includes time zero, so this uses the recommended `ℕ₀` reading of the
positive record time, the active edge is present at that stage and was either
missing or unallocated at the preceding stage; same-step allocation is not
asserted. -/
theorem kmsw_bdy_upper_left_ranked_record (w : ℕ → Fin 3) (n m : ℕ)
    (hmn : m ≤ n)
    (hrec : ∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j) :
    ∃ h : ((List.range m).filter (fun r => decide
          (∀ j, r < j → j ≤ n → L w r + 1 ≤ L w j))).length <
        (kmswStage w n).UL.length,
      (kmswStage w n).UL[((List.range m).filter (fun r => decide
          (∀ j, r < j → j ≤ n → L w r + 1 ≤ L w j))).length]'h = act w m ∧
      (kmswStage w m).present (act w m) = true ∧
      (m = 0 → act w m = 0 ∧ (kmswStage w 0).present 0 = true) ∧
      (0 < m → ¬ ((act w m < (kmswStage w (m - 1)).nextEdge) ∧
        (kmswStage w (m - 1)).present (act w m) = true)) := by
  let p : ℕ → Bool := fun r => decide
    (∀ j, r < j → j ≤ n → L w r + 1 ≤ L w j)
  have hp : p m = true := decide_eq_true hrec
  obtain ⟨hfilter, htime⟩ :=
    kmsw_bdy_range_filter_getElem_at_rank (p := p) hmn hp
  have hbound : ((List.range m).filter p).length < (kmswStage w n).UL.length := by
    simpa [kmswStage_UL_eq, p] using hfilter
  have hedge : (kmswStage w n).UL[((List.range m).filter p).length]'hbound = act w m := by
    simpa [p, kmswStage_UL_eq] using congrArg (act w) htime
  refine ⟨hbound, hedge, kmswStage_active_present_local w m, ?_, ?_⟩
  · intro hm0
    subst m
    simp [act, kmswStage, kmswInit]
  · intro hmpos
    cases m with
    | zero => omega
    | succ q =>
      simpa [act] using kmswStage_active_not_present_previous w q

/- The four geometric boundary segments, counted by their unique outer-face
The dart classes identify the present UL/LR edges and the missing UR/LL edges -/
theorem kmsw_bdy_geometric_segment_cardinalities (w : ℕ → Fin 3) (n : ℕ) :
    ((Finset.card (kmswStageULDartsFinset w n) : ℤ) = L w n - minL w n + 1) ∧
    ((Finset.card (kmswStageURDartsFinset w n) : ℤ) = R w n - minR w n) ∧
    ((Finset.card (kmswStageLLDartsFinset w n) : ℤ) = -minL w n) ∧
    ((Finset.card (kmswStageLRDartsFinset w n) : ℤ) = -minR w n + 1) := by
  exact kmswStage_boundary_dart_cardinalities w n

/- Exact source-time indexing of the four boundary lists. Each item is
ordered as in `lem-kmsw-bdy` (i)–(iv): LL and UR are reversed from their
newest-first state lists, while UL and LR follow their source record order -/
theorem kmsw_bdy_source_ordered_boundary_lists (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL =
      ((List.range (n + 1)).filter (fun m => decide
        (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j))).map (act w) ∧
    ((kmswStage w n).LL).reverse =
      ((List.range (n + 1)).filter (fun m => decide
        (0 < m ∧ ∀ j < m, L w m < L w j))).map (kmswLLCreatedEdge w) ∧
    (kmswStage w n).LR =
      ((List.range (n + 1)).filter (fun m => decide
        (∀ j, j < m → R w m < R w j))).map (act w) ∧
    ((kmswStage w n).UR).reverse =
      ((List.range (n + 1)).filter (fun m => decide
        (0 < m ∧ m ≤ n ∧ ∀ j, m ≤ j → j ≤ n →
          R w (m - 1) + 1 ≤ R w j))).map (kmswURCreatedEdge w) := by
  constructor
  · exact kmswStage_UL_eq w n
  constructor
  · rw [kmswStage_LL_eq]
    simp only [List.map_reverse, List.reverse_reverse]
  constructor
  · exact kmswStage_LR_eq w n
  · rw [kmswStage_UR_eq]
    simp only [List.map_reverse, List.reverse_reverse]



theorem kmsw_bdy_lower_left_first_hit (w : ℕ → Fin 3) (n k t : ℕ)
    (hk : 1 ≤ k) (_hkmin : (k : ℤ) ≤ -minL w n)
    (htn : t ≤ n) (ht : L w t = -(k : ℤ))
    (hfirst : ∀ j, j < t → L w j ≠ -(k : ℤ)) :
    ∃ h : k - 1 < ((kmswStage w n).LL.reverse).length,
      ((kmswStage w n).LL.reverse)[k - 1]'h = kmswLLCreatedEdge w t ∧
      (kmswStage w (t - 1)).nextEdge ≤ kmswLLCreatedEdge w t ∧
      kmswLLCreatedEdge w t < (kmswStage w t).nextEdge ∧
      (kmswStage w t).present (kmswLLCreatedEdge w t) = false ∧
      ∀ j, j < t → L w t < L w j := by
  let hhit : ∃ i, L w i = -(k : ℤ) := ⟨t, ht⟩
  have hfind : Nat.find hhit = t := by
    apply (Nat.find_eq_iff hhit).2
    exact ⟨ht, fun j hj heq => hfirst j hj heq⟩
  have hrecordPair :=
    (strict_running_minimum_iff_first_hit (L w) (by simp [L])
      (kmsw_L_walk_step_bound w) n t (-(k : ℤ)) (by omega) hhit).2
      ⟨htn, ht, hfind.symm⟩
  have hrecord := (Finset.mem_filter.mp hrecordPair.1).2
  have htpos : 0 < t := by
    by_contra h
    have htzero : t = 0 := by omega
    rw [htzero] at ht
    simp [L] at ht
    omega
  have hmin := kmsw_runningMin_prev_of_strict_record
    (L w) t (-(k : ℤ)) htpos ht (by simpa [ht] using hrecord)
    (kmsw_L_walk_step_bound w)
  have hminL : minL w (t - 1) = -(k : ℤ) + 1 := by
    simpa [minL] using hmin
  let p : ℕ → Bool := fun r => decide (0 < r ∧ ∀ j < r, L w r < L w j)
  let prefixTimes := (List.range t).filter p
  have hprefixList : (kmswStage w (t - 1)).LL.reverse =
      prefixTimes.map (kmswLLCreatedEdge w) := by
    simpa [prefixTimes, p, Nat.sub_add_cancel htpos] using
      (kmsw_bdy_source_ordered_boundary_lists w (t - 1)).2.1
  have hprefixLen : prefixTimes.length = k - 1 := by
    have hlenEq := congrArg List.length hprefixList
    simp only [List.length_reverse, List.length_map] at hlenEq
    have hcast : (prefixTimes.length : ℤ) = (k : ℤ) - 1 := by
      rw [← hlenEq, kmswStage_LL_length, hminL]
      omega
    omega
  have hp : p t = true := decide_eq_true ⟨htpos, hrecord⟩
  obtain ⟨hfilter, htime⟩ :=
    kmsw_bdy_range_filter_getElem_at_rank (p := p) htn hp
  have hfull : (kmswStage w n).LL.reverse =
      ((List.range (n + 1)).filter p).map (kmswLLCreatedEdge w) := by
    simpa [p] using (kmsw_bdy_source_ordered_boundary_lists w n).2.1
  have hboundPrefix : prefixTimes.length < ((kmswStage w n).LL.reverse).length := by
    rw [hfull]
    simpa [prefixTimes, List.length_map] using hfilter
  have hedgePrefix : ((kmswStage w n).LL.reverse)[prefixTimes.length]'hboundPrefix =
      kmswLLCreatedEdge w t := by
    simpa [hfull, p, prefixTimes] using congrArg (kmswLLCreatedEdge w) htime
  have hbound : k - 1 < ((kmswStage w n).LL.reverse).length := by
    simpa [hprefixLen] using hboundPrefix
  have hedge : ((kmswStage w n).LL.reverse)[k - 1]'hbound =
      kmswLLCreatedEdge w t := by
    simpa [hprefixLen] using hedgePrefix
  have halloc := kmswLLCreatedEdge_allocated_at_record w htpos hrecord
  have hmissing := kmswLLCreatedEdge_missing w htpos hrecord
  exact ⟨hbound, hedge, halloc.1, halloc.2, hmissing, hrecord⟩

/-- Clause (ii), including the root edge as the zeroth LR item. For
`1 ≤ k ≤ -minR`, the first hit of `-k` is the `k`th item in zero-based
indexing, and the corresponding edge becomes present at that stage; at a
positive time it was missing or unallocated immediately before the step -/
theorem kmsw_bdy_lower_right_first_hit (w : ℕ → Fin 3) (n k t : ℕ)
    (hk : 1 ≤ k) (_hkmin : (k : ℤ) ≤ -minR w n)
    (htn : t ≤ n) (ht : R w t = -(k : ℤ))
    (hfirst : ∀ j, j < t → R w j ≠ -(k : ℤ)) :
    (kmswStage w n).LR[0]? = some 0 ∧
    ∃ h : k < (kmswStage w n).LR.length,
      (kmswStage w n).LR[k]'h = act w t ∧
      (kmswStage w t).present (act w t) = true ∧
      (0 < t → ¬ ((act w t < (kmswStage w (t - 1)).nextEdge) ∧
        (kmswStage w (t - 1)).present (act w t) = true)) := by
  let hhit : ∃ i, R w i = -(k : ℤ) := ⟨t, ht⟩
  have hfind : Nat.find hhit = t := by
    apply (Nat.find_eq_iff hhit).2
    exact ⟨ht, fun j hj heq => hfirst j hj heq⟩
  have hrecordPair :=
    (weak_first_minimum_iff_first_hit (R w) (by simp [R])
      (kmsw_R_walk_step_bound w) n t (-(k : ℤ)) (by omega) hhit).2
      ⟨htn, ht, hfind.symm⟩
  have hrecordBool := (List.mem_filter.mp hrecordPair.1).2
  have hrecord : ∀ j, j < t → R w t < R w j := of_decide_eq_true hrecordBool
  have htpos : 0 < t := by
    by_contra h
    have htzero : t = 0 := by omega
    rw [htzero] at ht
    simp [R] at ht
    omega
  have hmin := kmsw_runningMin_prev_of_strict_record
    (R w) t (-(k : ℤ)) htpos ht (by simpa [ht] using hrecord)
    (kmsw_R_walk_step_bound w)
  have hminR : minR w (t - 1) = -(k : ℤ) + 1 := by
    simpa [minR] using hmin
  let p : ℕ → Bool := fun r => decide (∀ j < r, R w r < R w j)
  let prefixTimes := (List.range t).filter p
  have hprefixList : (kmswStage w (t - 1)).LR = prefixTimes.map (act w) := by
    simpa [prefixTimes, p, Nat.sub_add_cancel htpos] using
      (kmsw_bdy_source_ordered_boundary_lists w (t - 1)).2.2.1
  have hprefixLen : prefixTimes.length = k := by
    have hlenEq := congrArg List.length hprefixList
    simp only [List.length_map] at hlenEq
    have hcast : (prefixTimes.length : ℤ) = k := by
      rw [← hlenEq, kmswStage_LR_length, hminR]
      omega
    omega
  have hp : p t = true := decide_eq_true (by simpa [p] using hrecord)
  obtain ⟨hfilter, htime⟩ :=
    kmsw_bdy_range_filter_getElem_at_rank (p := p) htn hp
  have hfull : (kmswStage w n).LR = ((List.range (n + 1)).filter p).map (act w) := by
    simpa [p] using (kmsw_bdy_source_ordered_boundary_lists w n).2.2.1
  have hboundPrefix : prefixTimes.length < (kmswStage w n).LR.length := by
    rw [hfull]
    simpa [prefixTimes, List.length_map] using hfilter
  have hedgePrefix : (kmswStage w n).LR[prefixTimes.length]'hboundPrefix = act w t := by
    simpa [hfull, p, prefixTimes] using congrArg (act w) htime
  have hbound : k < (kmswStage w n).LR.length := by
    simpa [hprefixLen] using hboundPrefix
  have hedge : (kmswStage w n).LR[k]'hbound = act w t := by
    simpa [hprefixLen] using hedgePrefix
  have hroot : (kmswStage w n).LR[0]? = some 0 := by
    rw [kmswStage_LR_eq]
    rw [List.getElem?_map]
    have htime0 :
        ((List.range (n + 1)).filter
          (fun m => decide (∀ j, j < m → R w m < R w j)))[0]? = some 0 := by
      simp [List.range_succ_eq_map]
    rw [htime0]
    simp [act, kmswStage, kmswInit]
  have hprevious : 0 < t →
      ¬ ((act w t < (kmswStage w (t - 1)).nextEdge) ∧
        (kmswStage w (t - 1)).present (act w t) = true) := by
    intro htpos'
    cases t with
    | zero => omega
    | succ q => simpa [act, Nat.succ_sub_one] using
        (kmswStage_active_not_present_previous w q)
  exact ⟨hroot, hbound, hedge, kmswStage_active_present_local w t, hprevious⟩

/-- Source-domain left-boundary clause, including its actual missing edge,
first active west-vertex visit, and all visits in the finite prefix -/
theorem kmsw_bdy_lower_left (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkmin : (k : ℤ) ≤ -minL w n) :
    ∃ hhit : ∃ t, L w t = -(k : ℤ),
      Nat.find hhit ≤ n ∧
      ∃ h : k - 1 < ((kmswStage w n).LL.reverse).length,
        ((kmswStage w n).LL.reverse)[k - 1]'h =
            kmswLLCreatedEdge w (Nat.find hhit) ∧
        (kmswStage w (Nat.find hhit - 1)).nextEdge ≤
            kmswLLCreatedEdge w (Nat.find hhit) ∧
        kmswLLCreatedEdge w (Nat.find hhit) <
            (kmswStage w (Nat.find hhit)).nextEdge ∧
        (kmswStage w (Nat.find hhit)).present
            (kmswLLCreatedEdge w (Nat.find hhit)) = false ∧
        (kmswStage w (Nat.find hhit)).west (act w (Nat.find hhit)) =
            (kmswStage w (Nat.find hhit)).west
              (kmswLLCreatedEdge w (Nat.find hhit)) ∧
        (∀ m, m ≤ n →
          ((kmswStage w m).west (act w m) =
              (kmswStage w (Nat.find hhit)).west
                (kmswLLCreatedEdge w (Nat.find hhit)) ↔
            L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j)) ∧
        IsLeast {m | (kmswStage w m).west (act w m) =
          (kmswStage w (Nat.find hhit)).west
            (kmswLLCreatedEdge w (Nat.find hhit))} (Nat.find hhit) := by
  obtain ⟨hhit, hbound⟩ := kmsw_bdy_lower_left_hit_exists w n k hk hkmin
  have ht : L w (Nat.find hhit) = -(k : ℤ) := Nat.find_spec hhit
  have hfirst : ∀ j, j < Nat.find hhit → L w j ≠ -(k : ℤ) := by
    intro j hj heq
    have hmin := Nat.find_min' hhit heq
    omega
  obtain ⟨hidx, hedge, hallocLo, hallocHi, hmissing, _hrecord⟩ :=
    kmsw_bdy_lower_left_first_hit w n k (Nat.find hhit) hk hkmin hbound ht hfirst
  have hvisits := kmswLL_first_hit_vertex_visits w k hk hhit
  refine ⟨hhit, hbound, hidx, hedge, hallocLo, hallocHi, hmissing,
    hvisits.1, ?_, hvisits.2.2⟩
  intro m hm
  exact hvisits.2.1 m

/-- Source-domain right-boundary clause, including the root edge offset, the
ranked present edge, its first active east-vertex visit, and all visits in the -/
theorem kmsw_bdy_lower_right (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkmin : (k : ℤ) ≤ -minR w n) :
    ∃ hhit : ∃ t, R w t = -(k : ℤ),
      Nat.find hhit ≤ n ∧
      (kmswStage w n).LR[0]? = some 0 ∧
      ∃ h : k < (kmswStage w n).LR.length,
        (kmswStage w n).LR[k]'h = act w (Nat.find hhit) ∧
        (kmswStage w (Nat.find hhit)).present (act w (Nat.find hhit)) = true ∧
        (0 < Nat.find hhit →
          ¬ ((act w (Nat.find hhit) <
              (kmswStage w (Nat.find hhit - 1)).nextEdge) ∧
            (kmswStage w (Nat.find hhit - 1)).present
              (act w (Nat.find hhit)) = true)) ∧
        (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) =
          (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ∧
        (∀ m, m ≤ n →
          ((kmswStage w m).east (act w m) =
              (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ↔
            R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j)) ∧
        IsLeast {m | (kmswStage w m).east (act w m) =
          (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit))}
          (Nat.find hhit) := by
  obtain ⟨hhit, hbound⟩ := kmsw_bdy_lower_right_hit_exists w n k hk hkmin
  have ht : R w (Nat.find hhit) = -(k : ℤ) := Nat.find_spec hhit
  have hfirst : ∀ j, j < Nat.find hhit → R w j ≠ -(k : ℤ) := by
    intro j hj heq
    have hmin := Nat.find_min' hhit heq
    omega
  obtain ⟨hroot, hidx, hedge, hpresent, hprevious⟩ :=
    kmsw_bdy_lower_right_first_hit w n k (Nat.find hhit) hk hkmin
      hbound ht hfirst
  have hvisits := kmswLR_first_hit_vertex_visits w k hk hhit
  refine ⟨hhit, hbound, hroot, hidx, hedge, hpresent, hprevious,
    hvisits.1, ?_, hvisits.2.2⟩
  intro m hm
  exact hvisits.2.1 m

private theorem kmswURCreatedEdge_allocated_at_record (w : ℕ → Fin 3)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hrec : ∀ j, m ≤ j → j ≤ n → R w (m - 1) + 1 ≤ R w j) :
    (kmswStage w (m - 1)).nextEdge ≤ kmswURCreatedEdge w m ∧
      kmswURCreatedEdge w m < (kmswStage w m).nextEdge := by
  cases m with
  | zero => omega
  | succ q =>
    have hthreshold := hrec (q + 1) (le_rfl) (by omega)
    simp only [Nat.succ_sub_one] at hthreshold
    have hc : w q = 1 := by
      by_cases h0 : w q = 0
      · have hs := kmsw_R_succ w q
        rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hs
        omega
      · by_cases h1 : w q = 1
        · exact h1
        · have h2 : w q = 2 := by
            apply Fin.ext
            have hv := (w q).isLt
            have hn0 : (w q).val ≠ 0 := by intro h; exact h0 (Fin.ext h)
            have hn1 : (w q).val ≠ 1 := by intro h; exact h1 (Fin.ext h)
            omega
          have hs := kmsw_R_succ w q
          rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hs
          omega
    have hcreated : kmswURCreatedEdge w (q + 1) =
        (kmswStage w q).nextEdge + 1 := by
      simp [kmswURCreatedEdge, kmswStage, hc, kmswCodeStep, kmswStep,
        kmswStepOfStep, State.addEdge]
    have hnext : (kmswStage w (q + 1)).nextEdge =
        (kmswStage w q).nextEdge + 2 := by
      simp [kmswStage, hc, kmswCodeStep, kmswStep, kmswStepOfStep, State.addEdge]
    simp only [Nat.succ_sub_one]
    rw [hcreated, hnext]
    omega




theorem kmsw_bdy_upper_right_ranked_record (w : ℕ → Fin 3) (n m : ℕ)
    (hm : 0 < m) (hmn : m ≤ n)
    (hrec : ∀ j, m ≤ j → j ≤ n → R w (m - 1) + 1 ≤ R w j) :
    let p : ℕ → Bool := fun r => decide
      (0 < r ∧ r ≤ n ∧ ∀ j, r ≤ j → j ≤ n → R w (r - 1) + 1 ≤ R w j)
    let prefixTimes := (List.range m).filter p
    ∃ h : prefixTimes.length < ((kmswStage w n).UR.reverse).length,
      ((kmswStage w n).UR.reverse)[prefixTimes.length]'h = kmswURCreatedEdge w m ∧
      ((prefixTimes.length + 1 : ℕ) : ℤ) ≤ R w n - minR w n ∧
      (kmswStage w (m - 1)).nextEdge ≤ kmswURCreatedEdge w m ∧
      kmswURCreatedEdge w m < (kmswStage w m).nextEdge ∧
      (kmswStage w n).present (kmswURCreatedEdge w m) = false := by
  let p : ℕ → Bool := fun r => decide
    (0 < r ∧ r ≤ n ∧ ∀ j, r ≤ j → j ≤ n → R w (r - 1) + 1 ≤ R w j)
  let prefixTimes := (List.range m).filter p
  have hp : p m = true := decide_eq_true ⟨hm, hmn, hrec⟩
  obtain ⟨hfilter, htime⟩ :=
    kmsw_bdy_range_filter_getElem_at_rank (p := p) hmn hp
  have hfull : (kmswStage w n).UR.reverse =
      ((List.range (n + 1)).filter p).map (kmswURCreatedEdge w) := by
    simpa [p] using (kmsw_bdy_source_ordered_boundary_lists w n).2.2.2
  have hbound : prefixTimes.length < ((kmswStage w n).UR.reverse).length := by
    rw [hfull]
    simpa [prefixTimes, List.length_map] using hfilter
  have hedge : ((kmswStage w n).UR.reverse)[prefixTimes.length]'hbound =
      kmswURCreatedEdge w m := by
    simpa [hfull, p, prefixTimes] using congrArg (kmswURCreatedEdge w) htime
  have hrankNat : prefixTimes.length + 1 ≤ (kmswStage w n).UR.length := by
    have hlen : prefixTimes.length + 1 ≤ ((kmswStage w n).UR.reverse).length := by omega
    simpa using hlen
  have hrankInt : ((prefixTimes.length + 1 : ℕ) : ℤ) ≤
      ((kmswStage w n).UR.length : ℤ) := by exact_mod_cast hrankNat
  have hcount : ((prefixTimes.length + 1 : ℕ) : ℤ) ≤ R w n - minR w n := by
    rw [kmswStage_UR_length] at hrankInt
    exact hrankInt
  have halloc := kmswURCreatedEdge_allocated_at_record w hm hmn hrec
  have hmemRev : kmswURCreatedEdge w m ∈ (kmswStage w n).UR.reverse := by
    rw [← hedge]
    exact List.getElem_mem hbound
  have hmemUR : kmswURCreatedEdge w m ∈ (kmswStage w n).UR :=
    List.mem_reverse.mp hmemRev
  have hboundEdge := stageRun_edge_bound w n (kmswURCreatedEdge w m)
    (Or.inl (Or.inl (Or.inr hmemUR)))
  have hmissing := ((kmswStage_status w n).1 (kmswURCreatedEdge w m) hboundEdge).2
    (Or.inl hmemUR)
  exact ⟨hbound, hedge, hcount, halloc.1, halloc.2, hmissing⟩

/- The upper-left active edges at two times have the same initial vertex
whenever the walk stays at or above their common level between those times.
This is the vertex clause in `lem-kmsw-bdy` (iii), -/
theorem kmsw_bdy_upper_left_initial_vertex (w : ℕ → Fin 3) {m' m : ℕ}
    (hm : m' ≤ m) (hlev : L w m' = L w m)
    (habove : ∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) :
    (kmswStage w m).west (act w m') =
      (kmswStage w m).west (act w m) :=
  kmsw_west_act_eq_of_level w hm hlev habove






theorem kmsw_bdy_UL_record_activation_counterexample :
    let w : ℕ → Fin 3 := fun i => if i = 0 then 1 else 2;
    (∀ j, 2 < j → j ≤ 3 → L w 2 + 1 ≤ L w j) ∧
    act w 2 = 2 ∧
    (kmswStage w 1).nextEdge = 3 ∧
    (kmswStage w 2).nextEdge = 3 := by
  dsimp only
  constructor
  · intro j hj hjn
    have hj3 : j = 3 := by omega
    subst j
    norm_num [L, RandomWalk.lazyTwoDimensionalStep, Finset.sum_range_succ]
  constructor
  · norm_num [act, kmswStage, kmswInit, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge]
  constructor
  · norm_num [kmswStage, kmswInit, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge]
  · norm_num [kmswStage, kmswInit, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge]



theorem kmsw_bdy_candidate (w : ℕ → Fin 3) (n : ℕ) :
    (∀ (k : ℕ), ∀ (_hk : 1 ≤ k), ∀ (_hkmin : (k : ℤ) ≤ -minL w n),
      ∃ hhit : ∃ t, L w t = -(k : ℤ),
        Nat.find hhit ≤ n ∧
        ∃ h : k - 1 < ((kmswStage w n).LL.reverse).length,
          ((kmswStage w n).LL.reverse)[k - 1]'h =
              kmswLLCreatedEdge w (Nat.find hhit) ∧
          (kmswStage w (Nat.find hhit - 1)).nextEdge ≤
              kmswLLCreatedEdge w (Nat.find hhit) ∧
          kmswLLCreatedEdge w (Nat.find hhit) <
              (kmswStage w (Nat.find hhit)).nextEdge ∧
          (kmswStage w (Nat.find hhit)).present
              (kmswLLCreatedEdge w (Nat.find hhit)) = false ∧
          (kmswStage w (Nat.find hhit)).west (act w (Nat.find hhit)) =
              (kmswStage w (Nat.find hhit)).west
                (kmswLLCreatedEdge w (Nat.find hhit)) ∧
          (∀ m, m ≤ n →
            ((kmswStage w m).west (act w m) =
                (kmswStage w (Nat.find hhit)).west
                  (kmswLLCreatedEdge w (Nat.find hhit)) ↔
              L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j)) ∧
          IsLeast {m | (kmswStage w m).west (act w m) =
            (kmswStage w (Nat.find hhit)).west
              (kmswLLCreatedEdge w (Nat.find hhit))} (Nat.find hhit)) ∧
    (∀ (k : ℕ), ∀ (_hk : 1 ≤ k), ∀ (_hkmin : (k : ℤ) ≤ -minR w n),
      ∃ hhit : ∃ t, R w t = -(k : ℤ),
        Nat.find hhit ≤ n ∧
        (kmswStage w n).LR[0]? = some 0 ∧
        ∃ h : k < (kmswStage w n).LR.length,
          (kmswStage w n).LR[k]'h = act w (Nat.find hhit) ∧
          (kmswStage w (Nat.find hhit)).present (act w (Nat.find hhit)) = true ∧
          (0 < Nat.find hhit →
            ¬ ((act w (Nat.find hhit) <
                (kmswStage w (Nat.find hhit - 1)).nextEdge) ∧
              (kmswStage w (Nat.find hhit - 1)).present
                (act w (Nat.find hhit)) = true)) ∧
          (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) =
            (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ∧
          (∀ m, m ≤ n →
            ((kmswStage w m).east (act w m) =
                (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ↔
              R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j)) ∧
          IsLeast {m | (kmswStage w m).east (act w m) =
            (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit))}
            (Nat.find hhit)) ∧
    ((kmswStage w n).UL =
      ((List.range (n + 1)).filter (fun m => decide
        (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j))).map (act w)) ∧
    (∀ m' m, m' ≤ m → m ≤ n → L w m' = L w m →
      (∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) →
      (kmswStage w m).west (act w m') = (kmswStage w m).west (act w m)) ∧
    (((kmswStage w n).UR).reverse =
      ((List.range (n + 1)).filter (fun m => decide
        (0 < m ∧ m ≤ n ∧ ∀ j, m ≤ j → j ≤ n →
          R w (m - 1) + 1 ≤ R w j))).map (kmswURCreatedEdge w)) ∧
    ((Finset.card (kmswStageULDartsFinset w n) : ℤ) =
        L w n - minL w n + 1) ∧
      ((Finset.card (kmswStageURDartsFinset w n) : ℤ) =
        R w n - minR w n) ∧
      ((Finset.card (kmswStageLLDartsFinset w n) : ℤ) = -minL w n) ∧
      ((Finset.card (kmswStageLRDartsFinset w n) : ℤ) = -minR w n + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hkmin
    exact kmsw_bdy_lower_left w n k hk hkmin
  · intro k hk hkmin
    exact kmsw_bdy_lower_right w n k hk hkmin
  · exact (kmsw_bdy_source_ordered_boundary_lists w n).1
  · intro m' m hm'm hmn hlev habove
    exact kmsw_bdy_upper_left_initial_vertex w hm'm hlev habove
  · exact (kmsw_bdy_source_ordered_boundary_lists w n).2.2.2
  · exact kmsw_bdy_geometric_segment_cardinalities w n

end DirectedDistances.PaperProofs.Section3
