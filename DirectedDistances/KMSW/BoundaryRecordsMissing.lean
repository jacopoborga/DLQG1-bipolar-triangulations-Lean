module

public import DirectedDistances.KMSW.BoundaryDynamics

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Max

/-! # Missing KMSW boundary records

Record descriptions for the lower-left and upper-right missing boundary edges -/

public section
namespace DirectedDistances.KMSW

open scoped Classical

/-- The ID allocated to the missing edge at a lower-left creation time.
Creation times are positive, and the new edge is the final allocation in -/
@[expose] def kmswLLCreatedEdge (w : ℕ → Fin 3) (m : ℕ) : ℕ :=
  (kmswStage w m).nextEdge - 1

/-- The ID allocated to the missing edge at an upper-right creation time.
Creation times are positive, and the new edge is the final allocation in -/
@[expose] def kmswURCreatedEdge (w : ℕ → Fin 3) (m : ℕ) : ℕ :=
  (kmswStage w m).nextEdge - 1

private abbrev kmswURRecord (w : ℕ → Fin 3) (n m : ℕ) : Prop :=
  0 < m ∧ m ≤ n ∧ ∀ j, m ≤ j → j ≤ n → R w (m - 1) + 1 ≤ R w j

private abbrev kmswURThreshold (w : ℕ → Fin 3) (m : ℕ) : ℤ :=
  R w (m - 1) + 1

private theorem L_succ_missing (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem R_succ_missing (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem R_increment_bounds (w : ℕ → Fin 3) (n : ℕ) :
    -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 ∧
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 ≤ 1 := by
  by_cases h0 : w n = 0
  · simp [h0, RandomWalk.lazyTwoDimensionalStep_zero]
  · by_cases h1 : w n = 1
    · simp [h1, RandomWalk.lazyTwoDimensionalStep_one]
    · have h2 : w n = 2 := by
        apply Fin.ext
        have hv := (w n).isLt
        have hn0 : (w n).val ≠ 0 := by intro h; exact h0 (Fin.ext h)
        have hn1 : (w n).val ≠ 1 := by intro h; exact h1 (Fin.ext h)
        omega
      simp [h2, RandomWalk.lazyTwoDimensionalStep_two]

/-- Last crossing above a level: after the last time below `q`, the walk
crosses to `q` and stays there or above through `n`. -/
private theorem exists_latest_below (w : ℕ → Fin 3) (n : ℕ) (q : ℤ)
    (hmin : minR w n < q) (hend : q ≤ R w n) :
    ∃ t, t < n ∧ R w t + 1 = q ∧
      ∀ j, t < j → j ≤ n → q ≤ R w j := by
  obtain ⟨i, hi, hmi⟩ := runningMin_attained (R w) n
  change minR w n = R w i at hmi
  let s : Finset ℕ := (Finset.range (n + 1)).filter (fun j => decide (R w j < q))
  have hs : s.Nonempty := by
    have hri : R w i < q := by rw [← hmi]; exact hmin
    refine ⟨i, ?_⟩
    simp [s, hi, hri]
  let t := s.max' hs
  have htmem : t ∈ s := Finset.max'_mem s hs
  have htle : t ≤ n := by
    have h := (Finset.mem_filter.mp htmem).1
    simpa [s] using (Finset.mem_range.mp h)
  have hlow : R w t < q := by
    simpa [s] using (Finset.mem_filter.mp htmem).2
  have htn : t < n := by
    by_contra h
    have htnEq : t = n := by omega
    rw [htnEq] at hlow
    omega
  have hmax : ∀ j ∈ s, j ≤ t := by
    intro j hj
    exact Finset.le_max' s j hj
  have hfuture : ∀ j, t < j → j ≤ n → q ≤ R w j := by
    intro j htj hjn
    by_contra hq
    have hjmem : j ∈ s := by
      have hrange : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hbelow : R w j < q := by omega
      simp [s, hrange, hbelow]
    have := hmax j hjmem
    omega
  have hnext : q ≤ R w (t + 1) := hfuture (t + 1) (by omega) (by omega)
  have hstep := R_succ_missing w t
  have hbounds := R_increment_bounds w t
  have hcross : R w t + 1 = q := by
    rw [hstep] at hnext
    omega
  exact ⟨t, htn, hcross, hfuture⟩

private theorem kmswURRecord_threshold_bounds (w : ℕ → Fin 3) {n m : ℕ}
    (hgood : kmswURRecord w n m) :
    minR w n < kmswURThreshold w m ∧ kmswURThreshold w m ≤ R w n := by
  rcases hgood with ⟨hm, hmn, hfuture⟩
  constructor
  · have hle := runningMin_le (R w) n (m - 1) (by omega)
    change minR w n ≤ R w (m - 1) at hle
    dsimp [kmswURThreshold]
    omega
  · have h := hfuture n (by omega) le_rfl
    exact h

private theorem kmswURRecord_top (w : ℕ → Fin 3) (n : ℕ)
    (hheight : minR w n < R w n) :
    ∃ m, kmswURRecord w n m ∧ kmswURThreshold w m = R w n ∧
      ∀ m', kmswURRecord w n m' → m' ≤ m := by
  obtain ⟨t, htn, hcross, hfuture⟩ :=
    exists_latest_below w n (R w n) hheight le_rfl
  refine ⟨t + 1, ?_, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_⟩
    intro j hj hjn
    have := hfuture j (by omega) hjn
    simpa [Nat.sub_add_cancel (by omega : 0 < t + 1), hcross] using this
  · dsimp [kmswURThreshold]
    simpa [Nat.sub_add_cancel (by omega : 0 < t + 1)] using hcross
  · intro m' hgood
    have hbounds := kmswURRecord_threshold_bounds w hgood
    by_cases hq : kmswURThreshold w m' = R w n
    · change R w (m' - 1) + 1 = R w n at hq
      have hmpos := hgood.1
      have hmle := hgood.2.1
      have hprevlt : R w (m' - 1) < R w n := by
        omega
      have hnotAfter : m' - 1 ≤ t := by
        by_contra h
        have hfuture' := hfuture (m' - 1) (by omega) (by omega)
        omega
      have hnotBefore : t ≤ m' - 1 := by
        by_contra h
        have hbad := hgood.2.2 t (by omega) (by omega)
        omega
      have : m' - 1 = t := by omega
      omega
    · have hq' : kmswURThreshold w m' < R w n := by omega
      change R w (m' - 1) + 1 < R w n at hq'
      have hmle := hgood.2.1
      have hprevlt : R w (m' - 1) < R w n := by omega
      have hnotAfter : m' - 1 ≤ t := by
        by_contra h
        have hfuture' := hfuture (m' - 1) (by omega) (by omega)
        omega
      omega

private theorem filter_range_last (P : ℕ → Bool) (n m : ℕ) (hm : m ≤ n)
    (hPm : P m = true) (hno : ∀ j, m < j → j ≤ n → P j = false) :
    (List.range (n + 1)).filter P = ((List.range m).filter P) ++ [m] := by
  induction n with
  | zero =>
    have hm0 : m = 0 := by omega
    subst m
    simp [hPm]
  | succ n ih =>
    by_cases hmn : m = n + 1
    · subst m
      have hb : P (n + 1) = true := hPm
      rw [List.range_succ, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, hb, ite_true]
    · have hmn' : m ≤ n := by omega
      have hno' : ∀ j, m < j → j ≤ n → P j = false := by
        intro j hj hjn
        exact hno j hj (by omega)
      rw [List.range_succ, List.filter_append, ih hmn' hno']
      have hb : P (n + 1) = false := hno (n + 1) (by omega) le_rfl
      simp [hb]

private abbrev kmswURRecords (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  ((List.range (n + 1)).filter (fun m => decide (kmswURRecord w n m))).reverse.map
    (kmswURCreatedEdge w)

private theorem decide_eq_of_iff {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) : decide P = decide Q := by
  by_cases hp : P
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · have hq : ¬ Q := fun hq => hp (h.mpr hq)
    rw [decide_eq_false hp, decide_eq_false hq]

private theorem filter_range_prefix (P Q : ℕ → Bool) (m n : ℕ) (hm : m ≤ n)
    (heq : ∀ j, j < m → Q j = P j)
    (hfalse : ∀ j, m ≤ j → j ≤ n → Q j = false) :
    (List.range (n + 1)).filter Q = (List.range m).filter P := by
  induction n with
  | zero =>
    have hm0 : m = 0 := by omega
    subst m
    have hzero := hfalse 0 le_rfl le_rfl
    rw [List.range_succ, List.range_zero, List.nil_append, List.filter_cons, List.filter_nil]
    have hcond : ¬ Q 0 = true := by rw [hzero]; decide
    rw [ite_eq_right hcond]
    rfl
  | succ n ih =>
    by_cases hmn : m = n + 1
    · subst m
      rw [List.range_succ, List.filter_append]
      have hlast := hfalse (n + 1) le_rfl le_rfl
      rw [List.filter_cons, List.filter_nil]
      have hcond : ¬ Q (n + 1) = true := by rw [hlast]; decide
      rw [ite_eq_right hcond, List.append_nil]
      apply List.filter_congr
      intro j hj
      exact heq j (by have := List.mem_range.mp hj; omega)
    · have hm' : m ≤ n := by omega
      rw [List.range_succ, List.filter_append]
      have hlast := hfalse (n + 1) (by omega) le_rfl
      rw [List.filter_cons, List.filter_nil]
      have hcond : ¬ Q (n + 1) = true := by rw [hlast]; decide
      rw [ite_eq_right hcond, List.append_nil]
      exact ih hm' (by
        intro j hj hjn
        exact hfalse j hj (by omega))

private theorem kmswURRecord_succ_iff_of_level (w : ℕ → Fin 3) {n m : ℕ}
    (hm : m ≤ n) (hlevel : R w n ≤ R w (n + 1)) :
    kmswURRecord w (n + 1) m ↔ kmswURRecord w n m := by
  constructor
  · rintro ⟨hmpos, hmn, hfuture⟩
    refine ⟨hmpos, by omega, ?_⟩
    intro j hj hjn
    exact hfuture j hj (by omega)
  · rintro ⟨hmpos, hmn, hfuture⟩
    have hbound := kmswURRecord_threshold_bounds w ⟨hmpos, hmn, hfuture⟩
    rcases hbound with ⟨_, hbound⟩
    change R w (m - 1) + 1 ≤ R w n at hbound
    refine ⟨hmpos, by omega, ?_⟩
    intro j hj hjn
    by_cases hjn' : j ≤ n
    · exact hfuture j hj hjn'
    · have hj' : j = n + 1 := by omega
      subst j
      omega

private theorem kmswURRecord_new_iff (w : ℕ → Fin 3) (n : ℕ) :
    kmswURRecord w (n + 1) (n + 1) ↔ R w n + 1 ≤ R w (n + 1) := by
  constructor
  · intro h
    exact h.2.2 (n + 1) le_rfl le_rfl
  · intro h
    refine ⟨by omega, le_rfl, ?_⟩
    intro j hj₁ hj₂
    have hj : j = n + 1 := by omega
    subst j
    simpa [Nat.sub_add_cancel (by omega : 0 < n + 1)] using h

private theorem kmswURRecords_succ_of_level (w : ℕ → Fin 3) (n : ℕ)
    (hlevel : R w n ≤ R w (n + 1)) :
    kmswURRecords w (n + 1) =
      if R w n + 1 ≤ R w (n + 1) then
        [kmswURCreatedEdge w (n + 1)] ++ kmswURRecords w n
      else kmswURRecords w n := by
  unfold kmswURRecords
  rw [List.range_succ, List.filter_append]
  have hprefix :
      (List.range (n + 1)).filter
          (fun m => decide (kmswURRecord w (n + 1) m)) =
        (List.range (n + 1)).filter (fun m => decide (kmswURRecord w n m)) := by
    apply List.filter_congr
    intro m hm
    have hmn : m ≤ n := by
      have := List.mem_range.mp hm
      omega
    exact decide_eq_of_iff (kmswURRecord_succ_iff_of_level w hmn hlevel)
  rw [hprefix]
  by_cases hnew : R w n + 1 ≤ R w (n + 1)
  · have hlast :
        (List.filter (fun m => decide (kmswURRecord w (n + 1) m)) [n + 1]) =
          [n + 1] := by
      rw [List.filter_cons, List.filter_nil,
        decide_eq_true (kmswURRecord_new_iff w n |>.2 hnew)]
      rfl
    rw [hlast, List.reverse_append, List.map_append, ite_eq_left hnew]
    rfl
  · have hlast :
        (List.filter (fun m => decide (kmswURRecord w (n + 1) m)) [n + 1]) =
          [] := by
      have hnot : ¬ kmswURRecord w (n + 1) (n + 1) := by
        intro h
        exact hnew ((kmswURRecord_new_iff w n).1 h)
      rw [List.filter_cons, List.filter_nil, decide_eq_false hnot]
      rfl
    rw [hlast, ite_eq_right hnew, List.append_nil]

private theorem kmswURRecord_unique_level (w : ℕ → Fin 3) (n m₁ m₂ : ℕ)
    (h₁ : kmswURRecord w n m₁) (h₂ : kmswURRecord w n m₂)
    (hq : kmswURThreshold w m₁ = kmswURThreshold w m₂) : m₁ = m₂ := by
  by_contra hne
  have hpos₁ := h₁.1
  have hpos₂ := h₂.1
  have hle₁ := h₁.2.1
  have hle₂ := h₂.2.1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hbad := h₁.2.2 (m₂ - 1) (by omega) (by omega)
    dsimp [kmswURThreshold] at hq
    omega
  · have hbad := h₂.2.2 (m₁ - 1) (by omega) (by omega)
    dsimp [kmswURThreshold] at hq
    omega

private theorem kmswURRecord_down_cases (w : ℕ → Fin 3) {n m₀ : ℕ}
    (hdown : R w (n + 1) = R w n - 1)
    (htop : kmswURRecord w n m₀)
    (htopLevel : kmswURThreshold w m₀ = R w n)
    (hmax : ∀ m', kmswURRecord w n m' → m' ≤ m₀) :
    (∀ j, j < m₀ →
      (kmswURRecord w (n + 1) j ↔ kmswURRecord w n j)) ∧
    (∀ j, m₀ ≤ j → j ≤ n + 1 → ¬ kmswURRecord w (n + 1) j) := by
  constructor
  · intro j hj
    constructor
    · rintro ⟨hjpos, hjle, hfuture⟩
      refine ⟨hjpos, by omega, ?_⟩
      intro k hkj hkn
      exact hfuture k hkj (by omega)
    · rintro ⟨hjpos, hjle, hfuture⟩
      have hbounds := kmswURRecord_threshold_bounds w ⟨hjpos, hjle, hfuture⟩
      rcases hbounds with ⟨_, hbound⟩
      have hneq : kmswURThreshold w j ≠ R w n := by
        intro heq
        have hsame := kmswURRecord_unique_level w n j m₀
          ⟨hjpos, hjle, hfuture⟩ htop (heq.trans htopLevel.symm)
        omega
      have hstrict : kmswURThreshold w j < R w n := by
        change kmswURThreshold w j ≤ R w n at hbound
        omega
      refine ⟨hjpos, by omega, ?_⟩
      intro k hkj hkn
      by_cases hkn' : k ≤ n
      · exact hfuture k hkj hkn'
      · have hk : k = n + 1 := by omega
        subst k
        change kmswURThreshold w j ≤ R w (n + 1)
        omega
  · intro j hjm hjn hrecord
    have hjle : j ≤ n := by
      by_contra h
      have hj : j = n + 1 := by omega
      subst j
      have hnew := (kmswURRecord_new_iff w n).1 hrecord
      rw [hdown] at hnew
      omega
    have hprior : kmswURRecord w n j := by
      rcases hrecord with ⟨hjpos, _, hfuture⟩
      refine ⟨hjpos, hjle, ?_⟩
      intro k hkj hkn
      exact hfuture k hkj (by omega)
    have hbound : j ≤ m₀ := hmax j hprior
    have hjEq : j = m₀ := by omega
    subst j
    have hfinal := hrecord.2.2 (n + 1) (by omega) le_rfl
    change R w (m₀ - 1) + 1 ≤ R w (n + 1) at hfinal
    change R w (m₀ - 1) + 1 = R w n at htopLevel
    rw [htopLevel] at hfinal
    omega

private theorem kmswURRecords_succ_down (w : ℕ → Fin 3) {n m₀ : ℕ}
    (hdown : R w (n + 1) = R w n - 1)
    (htop : kmswURRecord w n m₀)
    (htopLevel : kmswURThreshold w m₀ = R w n)
    (hmax : ∀ m', kmswURRecord w n m' → m' ≤ m₀) :
    kmswURRecords w (n + 1) =
      ((List.range m₀).filter (fun j => decide (kmswURRecord w n j))).reverse.map
        (kmswURCreatedEdge w) := by
  have hcases := kmswURRecord_down_cases w hdown htop htopLevel hmax
  have hfilter :
      (List.range (n + 1 + 1)).filter
          (fun j => decide (kmswURRecord w (n + 1) j)) =
        (List.range m₀).filter (fun j => decide (kmswURRecord w n j)) := by
    apply filter_range_prefix
    · omega
    · intro j hj
      exact decide_eq_of_iff (hcases.1 j hj)
    · intro j hj hjn
      exact decide_eq_false (hcases.2 j hj hjn)
  unfold kmswURRecords
  rw [hfilter]

/-- The upper-right list is the newest-first list of missing sides created at
the times whose level is never crossed below through time `n` (`lem-kmsw-bdy`(iv), -/
theorem kmswStage_UR_eq (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UR =
      (((List.range (n + 1)).filter (fun m => decide
        (0 < m ∧ m ≤ n ∧ ∀ j, m ≤ j → j ≤ n →
          R w (m - 1) + 1 ≤ R w j))).reverse.map (kmswURCreatedEdge w)) := by
  change (kmswStage w n).UR = kmswURRecords w n
  induction n with
  | zero =>
    simp [kmswStage, kmswInit, kmswURRecords]
  | succ n ih =>
    by_cases hc0 : w n = 0
    · have hlevel : R w n ≤ R w (n + 1) := by
        rw [R_succ_missing, hc0, RandomWalk.lazyTwoDimensionalStep_zero]
        omega
      have hsame : R w (n + 1) = R w n := by
        rw [R_succ_missing, hc0, RandomWalk.lazyTwoDimensionalStep_zero]
        omega
      have hnew : ¬ R w n + 1 ≤ R w (n + 1) := by
        rw [hsame]
        omega
      have hstate : (kmswStage w (n + 1)).UR = (kmswStage w n).UR := by
        rw [kmswStage, hc0]
        simp only [kmswCodeStep, kmswStep, kmswStepOfStep]
        cases hUL : (kmswStage w n).UL.dropLast.reverse <;>
          simp [State.addEdge]
      calc
        (kmswStage w (n + 1)).UR = (kmswStage w n).UR := hstate
        _ = kmswURRecords w n := ih
        _ = kmswURRecords w (n + 1) := by
          rw [kmswURRecords_succ_of_level w n hlevel, ite_eq_right hnew]
    · by_cases hc1 : w n = 1
      · have hlevel : R w n ≤ R w (n + 1) := by
          rw [R_succ_missing, hc1, RandomWalk.lazyTwoDimensionalStep_one]
          omega
        have hnew : R w n + 1 ≤ R w (n + 1) := by
          rw [R_succ_missing, hc1, RandomWalk.lazyTwoDimensionalStep_one]
        have hstate : (kmswStage w (n + 1)).UR =
            [kmswURCreatedEdge w (n + 1)] ++ (kmswStage w n).UR := by
          simp [kmswStage, hc1, kmswCodeStep, kmswStep, kmswStepOfStep,
            kmswURCreatedEdge, State.addEdge]
        calc
          (kmswStage w (n + 1)).UR =
              [kmswURCreatedEdge w (n + 1)] ++ (kmswStage w n).UR := hstate
          _ = [kmswURCreatedEdge w (n + 1)] ++ kmswURRecords w n := by rw [ih]
          _ = kmswURRecords w (n + 1) := by
            rw [kmswURRecords_succ_of_level w n hlevel, ite_eq_left hnew]
      · have hc2 : w n = 2 := by
          apply Fin.ext
          have hv := (w n).isLt
          have hn0 : (w n).val ≠ 0 := by intro h; exact hc0 (Fin.ext h)
          have hn1 : (w n).val ≠ 1 := by intro h; exact hc1 (Fin.ext h)
          omega
        have hdown : R w (n + 1) = R w n - 1 := by
          rw [R_succ_missing, hc2, RandomWalk.lazyTwoDimensionalStep_two]
          omega
        cases hUR : (kmswStage w n).UR with
        | nil =>
          have hmin : minR w n = R w n := by
            have hlen := kmswStage_UR_length w n
            rw [hUR] at hlen
            simp only [List.length_nil, Nat.cast_zero] at hlen
            omega
          have hminNext : minR w (n + 1) = R w (n + 1) := by
            rw [show minR w (n + 1) = min (minR w n) (R w (n + 1)) from rfl, hmin,
              hdown]
            exact min_eq_right (by omega)
          have hnoRecord : ∀ m, ¬ kmswURRecord w (n + 1) m := by
            intro m hm
            have hbounds := kmswURRecord_threshold_bounds w hm
            rw [hminNext] at hbounds
            omega
          have hrecords : kmswURRecords w (n + 1) = [] := by
            unfold kmswURRecords
            have hfilter :
                (List.range (n + 1 + 1)).filter
                    (fun m => decide (kmswURRecord w (n + 1) m)) =
                  (List.range (n + 1 + 1)).filter (fun _ => false) := by
              apply List.filter_congr
              intro m hm
              exact decide_eq_false (hnoRecord m)
            rw [hfilter]
            simp
          calc
            (kmswStage w (n + 1)).UR = [] := by
              simp [kmswStage, hc2, kmswCodeStep, kmswStep, kmswStepOfStep,
                State.addEdge, hUR]
            _ = kmswURRecords w (n + 1) := hrecords.symm
        | cons e es =>
          have hlen := kmswStage_UR_length w n
          rw [hUR] at hlen
          simp only [List.length_cons, Nat.cast_succ] at hlen
          have hheight : minR w n < R w n := by omega
          obtain ⟨m, hmrec, htopLevel, hmax⟩ := kmswURRecord_top w n hheight
          have hno : ∀ j, m < j → j ≤ n → ¬ kmswURRecord w n j := by
            intro j hj hjn hjrec
            have := hmax j hjrec
            omega
          have hPm : decide (kmswURRecord w n m) = true := decide_eq_true hmrec
          have hnoBool : ∀ j, m < j → j ≤ n →
              decide (kmswURRecord w n j) = false := by
            intro j hj hjn
            exact decide_eq_false (hno j hj hjn)
          have hfilterOld := filter_range_last
            (fun j => decide (kmswURRecord w n j)) n m hmrec.2.1 hPm hnoBool
          let tailRecords : List ℕ :=
            ((List.range m).filter (fun j => decide (kmswURRecord w n j))).reverse.map
              (kmswURCreatedEdge w)
          have hshapeOld : kmswURRecords w n = kmswURCreatedEdge w m :: tailRecords := by
            unfold kmswURRecords
            change
              ((List.range (n + 1)).filter
                (fun j => decide (kmswURRecord w n j))).reverse.map
                  (kmswURCreatedEdge w) =
                kmswURCreatedEdge w m ::
                  ((List.range m).filter
                    (fun j => decide (kmswURRecord w n j))).reverse.map
                      (kmswURCreatedEdge w)
            calc
              _ = (((List.range m).filter
                    (fun j => decide (kmswURRecord w n j)) ++ [m]).reverse).map
                      (kmswURCreatedEdge w) := by
                exact congrArg (fun l : List ℕ => l.reverse.map (kmswURCreatedEdge w))
                  hfilterOld
              _ = kmswURCreatedEdge w m ::
                    ((List.range m).filter
                      (fun j => decide (kmswURRecord w n j))).reverse.map
                        (kmswURCreatedEdge w) := by
                rw [List.reverse_append, List.map_append]
                rfl
          have hshapeNew : kmswURRecords w (n + 1) = tailRecords :=
            kmswURRecords_succ_down w hdown hmrec htopLevel hmax
          have htail : es = tailRecords := by
            have h := ih
            rw [hUR, hshapeOld] at h
            injection h with hhead htail
          calc
            (kmswStage w (n + 1)).UR = es := by
              simp [kmswStage, hc2, kmswCodeStep, kmswStep, kmswStepOfStep, hUR]
            _ = tailRecords := htail
            _ = kmswURRecords w (n + 1) := hshapeNew.symm

private theorem ll_stack_empty_iff_length_one (s : State)
    (hlast : ∃ es, s.UL = es ++ [s.active]) :
    s.UL.dropLast.reverse = [] ↔ s.UL.length = 1 := by
  constructor
  · intro h
    have hlen : (s.UL.dropLast).length = 0 := by
      have := congrArg List.length h
      simpa using this
    rw [List.length_dropLast] at hlen
    have hne : s.UL ≠ [] := by
      rcases hlast with ⟨es, he⟩
      rw [he]
      simp
    have hpos : 0 < s.UL.length := List.length_pos_iff.mpr hne
    omega
  · intro h
    have hlen : (s.UL.dropLast).length = 0 := by
      simp [List.length_dropLast, h]
    cases hd : s.UL.dropLast with
    | nil => rfl
    | cons a as => simp [hd] at hlen

private theorem kmswLLRecord_succ_iff (w : ℕ → Fin 3) (n : ℕ) :
    (∀ j ≤ n, L w (n + 1) < L w j) ↔
      w n = 0 ∧ (kmswStage w n).UL.length = 1 := by
  constructor
  · intro hrec
    have hlast := hrec n (by omega)
    have hstep := L_succ_missing w n
    have hc : w n = 0 := by
      change L w (n + 1) = L w n + ((w n : ℤ) - 1) at hstep
      rw [hstep] at hlast
      have hv : (w n : ℤ) - 1 < 0 := by omega
      apply Fin.ext
      omega
    rw [hc] at hstep
    simp [RandomWalk.lazyTwoDimensionalStep_zero] at hstep
    have hmin : minL w n = L w n := by
      obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
      change minL w n = L w j at he
      have hjrec := hrec j hj
      have hLj : L w n ≤ L w j := by omega
      have hle := runningMin_le (L w) n n (le_refl _)
      change minL w n ≤ L w n at hle
      omega
    have hlen := kmswStage_UL_length w n
    refine ⟨hc, ?_⟩
    omega
  · rintro ⟨hc, hlen⟩
    intro j hj
    have hmin := kmswStage_UL_length w n
    have hle := runningMin_le (L w) n j (by omega)
    change minL w n ≤ L w j at hle
    have hstep := L_succ_missing w n
    rw [hc] at hstep
    simp [RandomWalk.lazyTwoDimensionalStep_zero] at hstep
    omega

private theorem kmswStage_LL_update (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w (n + 1)).LL =
      if ∀ j ≤ n, L w (n + 1) < L w j then
        [kmswLLCreatedEdge w (n + 1)] ++ (kmswStage w n).LL
      else (kmswStage w n).LL := by
  have hlast := kmswStage_UL_last w n
  have hstack := ll_stack_empty_iff_length_one (kmswStage w n) hlast
  rw [kmswStage]
  by_cases hc : w n = 0
  · rw [hc]
    simp only [kmswCodeStep, kmswStep, kmswStepOfStep]
    cases hrev : (kmswStage w n).UL.dropLast.reverse with
    | nil =>
      have hlen : (kmswStage w n).UL.length = 1 := hstack.mp hrev
      have hrec : ∀ j ≤ n, L w (n + 1) < L w j :=
        (kmswLLRecord_succ_iff w n).mpr ⟨hc, hlen⟩
      have hid : kmswLLCreatedEdge w (n + 1) = (kmswStage w n).nextEdge + 1 := by
        simp [kmswLLCreatedEdge, kmswStage, hc, kmswCodeStep, kmswStep,
          kmswStepOfStep, hrev, State.addEdge]
      simp [hid, State.addEdge]
      exact hrec
    | cons e es =>
      have hrec : ¬ (∀ j ≤ n, L w (n + 1) < L w j) := by
        intro hr
        have hlen := (kmswLLRecord_succ_iff w n).mp hr |>.2
        have hnot : (kmswStage w n).UL.dropLast.reverse ≠ [] := by simp [hrev]
        exact hnot (hstack.mpr hlen)
      simp [hrec, State.addEdge]
  · have hnrec : ¬ (∀ j ≤ n, L w (n + 1) < L w j) := by
      intro hr
      exact hc ((kmswLLRecord_succ_iff w n).mp hr).1
    by_cases hc1 : w n = 1
    · rw [hc1]
      simp [kmswCodeStep, kmswStep, kmswStepOfStep, State.addEdge, hnrec]
    · have hc2 : w n = 2 := by
        apply Fin.ext
        have hv := (w n).isLt
        have hn0 : (w n).val ≠ 0 := by intro h; exact hc (Fin.ext h)
        have hn1 : (w n).val ≠ 1 := by intro h; exact hc1 (Fin.ext h)
        omega
      rw [hc2]
      cases hUR : (kmswStage w n).UR <;>
        simp [kmswCodeStep, kmswStep, kmswStepOfStep, State.addEdge, hUR, hnrec]

/-- The lower-left list is the newest-first list of missing edges created at
strict new minima of `L`, for the times in `[1,n]` (item (i) of -/
theorem kmswStage_LL_eq (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LL =
      (((List.range (n + 1)).filter (fun m => decide (0 < m ∧ ∀ j < m, L w m < L w j))).reverse.map
        (kmswLLCreatedEdge w)) := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
    rw [kmswStage_LL_update, ih]
    simp only [List.range_succ, List.filter_append, List.map_append,
      List.reverse_append]
    by_cases hrec : ∀ j < n + 1, L w (n + 1) < L w j
    · have hrecLe : ∀ j ≤ n, L w (n + 1) < L w j := by
        intro j hj
        exact hrec j (by omega)
      rw [ite_eq_left hrecLe]
      have hfilter : (List.filter
          (fun m => decide (0 < m ∧ ∀ j < m, L w m < L w j)) [n + 1]) = [n + 1] := by
        have hbool : decide (0 < n + 1 ∧
            ∀ j < n + 1, L w (n + 1) < L w j) = true :=
          decide_eq_true ⟨by omega, hrec⟩
        simp only [List.filter_cons, List.filter_nil]
        rw [hbool]
        simp
      rw [hfilter]
      simp
    · have hrecLe : ¬ (∀ j ≤ n, L w (n + 1) < L w j) := by
        intro h
        apply hrec
        intro j hj
        exact h j (by omega)
      rw [ite_eq_right hrecLe]
      have hfilter : (List.filter
          (fun m => decide (0 < m ∧ ∀ j < m, L w m < L w j)) [n + 1]) = [] := by
        have hfalse : ¬ (0 < n + 1 ∧
            ∀ j < n + 1, L w (n + 1) < L w j) := by
          rintro ⟨_, h⟩
          exact hrec h
        have hbool : decide (0 < n + 1 ∧
            ∀ j < n + 1, L w (n + 1) < L w j) = false :=
          decide_eq_false hfalse
        simp only [List.filter_cons, List.filter_nil]
        rw [hbool]
        simp
      rw [hfilter]
      simp

/-- A lower-left record edge is missing when its creating left step allocates -/
theorem kmswLLCreatedEdge_missing (w : ℕ → Fin 3) {m : ℕ}
    (hm : 0 < m) (hrec : ∀ j < m, L w m < L w j) :
    (kmswStage w m).present (kmswLLCreatedEdge w m) = false := by
  cases m with
  | zero => omega
  | succ k =>
    have hrec' : ∀ j ≤ k, L w (k + 1) < L w j := by
      intro j hj
      exact hrec j (by omega)
    have hchar := (kmswLLRecord_succ_iff w k).mp hrec'
    have hc : w k = 0 := hchar.1
    have hlen : (kmswStage w k).UL.length = 1 := hchar.2
    have hlast := kmswStage_UL_last w k
    have hstack := (ll_stack_empty_iff_length_one (kmswStage w k) hlast).mpr hlen
    simp [kmswStage, kmswLLCreatedEdge, hc, kmswCodeStep, kmswStep,
      kmswStepOfStep, hstack, State.addEdge]

/-- The upper-right edge allocated by an upward record step is missing at the -/
theorem kmswURCreatedEdge_missing (w : ℕ → Fin 3) {n m : ℕ}
    (hm : 0 < m) (hmn : m ≤ n)
    (hrec : ∀ j, m ≤ j → j ≤ n → R w (m - 1) + 1 ≤ R w j) :
    (kmswStage w m).present (kmswURCreatedEdge w m) = false := by
  have hcreation := hrec m (le_rfl) hmn
  have hprev : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hstep := R_succ_missing w (m - 1)
  rw [hprev] at hstep
  have hc : w (m - 1) = 1 := by
    by_cases h0 : w (m - 1) = 0
    · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hstep
      omega
    · by_cases h1 : w (m - 1) = 1
      · exact h1
      · have h2 : w (m - 1) = 2 := by
          apply Fin.ext
          have hv := (w (m - 1)).isLt
          have hn0 : (w (m - 1)).val ≠ 0 := by intro h; exact h0 (Fin.ext h)
          have hn1 : (w (m - 1)).val ≠ 1 := by intro h; exact h1 (Fin.ext h)
          omega
        rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hstep
        omega
  have hnewid : kmswURCreatedEdge w m = (kmswStage w (m - 1)).nextEdge + 1 := by
    rw [← hprev]
    simp [kmswURCreatedEdge, kmswStage, hc, kmswCodeStep,
      kmswStep, kmswStepOfStep, State.addEdge]
  rw [← hprev]
  simp [kmswStage, hc, kmswCodeStep, kmswStep, kmswStepOfStep,
    kmswURCreatedEdge, State.addEdge]

end DirectedDistances.KMSW
