module

public import DirectedDistances.KMSW.StageStackInvariantUR
public import DirectedDistances.KMSW.BoundaryRecordsUL
import Mathlib.Data.List.Range

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

/-! Helper toward Lemma 7.8 (lem-cell-sdp-upper) and Theorem 1.4 (KMSW reversal
correspondence); not a paper result. These definitions and claims use -/

public section
namespace DirectedDistances.KMSW




@[expose] def kmswLpair (w : ℕ → Fin 3) (t t' : ℕ) : Prop :=
  t < t' ∧ L w (t' + 1) = L w t ∧
    ∀ j, t < j → j ≤ t' → L w t < L w j




@[expose] noncomputable def kmswUlTime (w : ℕ → Fin 3) (t p : ℕ) : ℕ :=
  Nat.findGreatest (fun r => L w r - minL w r + 1 = (p : ℤ)) t




theorem kmswL_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
  exact Finset.sum_range_succ _ _




theorem kmswLpair_codes (w : ℕ → Fin 3) {t t' : ℕ}
    (h : kmswLpair w t t') : w t = 2 ∧ w t' = 0 := by
  rcases h with ⟨htt', hlevel, hstrict⟩
  have hdown := hstrict (t + 1) (by omega) (by omega)
  have hstep := kmswL_succ w t
  have hcode : w t = 2 := by
    have hcases : (w t).val = 0 ∨ (w t).val = 1 ∨ (w t).val = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have hc : w t = 0 := Fin.ext h0
      rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hstep
      omega
    · have hc : w t = 1 := Fin.ext h1
      rw [hc, RandomWalk.lazyTwoDimensionalStep_one] at hstep
      omega
    · exact Fin.ext h2
  have hleft : L w (t' + 1) < L w t' := by rw [hlevel]; exact hstrict t' htt' le_rfl
  have hstep' := kmswL_succ w t'
  have hcode' : w t' = 0 := by
    have hcases : (w t').val = 0 ∨ (w t').val = 1 ∨ (w t').val = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exact Fin.ext h0
    · have hc : w t' = 1 := Fin.ext h1
      rw [hc, RandomWalk.lazyTwoDimensionalStep_one] at hstep'
      omega
    · have hc : w t' = 2 := Fin.ext h2
      rw [hc, RandomWalk.lazyTwoDimensionalStep_two] at hstep'
      omega
  exact ⟨hcode, hcode'⟩




theorem kmswLpair_left_unique (w : ℕ → Fin 3) {s r t : ℕ}
    (hs : kmswLpair w s t) (hr : kmswLpair w r t) : s = r := by
  rcases hs with ⟨hst, hse, hsi⟩
  rcases hr with ⟨hrt, hre, hri⟩
  rcases lt_trichotomy s r with h | h | h
  · have := hsi r h (by omega)
    omega
  · exact h
  · have := hri s h (by omega)
    omega



theorem kmswLpair_right_unique (w : ℕ → Fin 3) {s t u : ℕ}
    (ht : kmswLpair w s t) (hu : kmswLpair w s u) : t = u := by
  rcases ht with ⟨hst, hte, hti⟩
  rcases hu with ⟨hsu, hue, hui⟩
  rcases lt_trichotomy t u with h | h | h
  · have := hui (t + 1) (by omega) (by omega)
    omega
  · exact h
  · have := hti (u + 1) (by omega) (by omega)
    omega



private theorem ul_stack_update (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w (t + 1)).UL.dropLast.reverse =
      if w t = 0 then (kmswStage w t).UL.dropLast.reverse.tail
      else if w t = 1 then (kmswStage w t).UL.dropLast.reverse
      else (kmswStage w t).active :: (kmswStage w t).UL.dropLast.reverse := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
  have hrev : (kmswStage w t).UL.reverse = (kmswStage w t).active :: xs.reverse := by
    simp [hxs]
  have hdrop : (kmswStage w t).UL.dropLast.reverse = xs.reverse := by simp [hxs]
  by_cases h0 : w t = 0
  · cases hh : (kmswStage w t).UL.dropLast.reverse <;>
      simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep, hh, State.addEdge]
  · by_cases h1 : w t = 1
    · simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
    · have h2 : w t = 2 := by
        apply Fin.ext
        have hv := (w t).isLt
        have hn0 : (w t).val ≠ 0 := fun hh => h0 (Fin.ext hh)
        have hn1 : (w t).val ≠ 1 := fun hh => h1 (Fin.ext hh)
        omega
      cases hh : (kmswStage w t).UR <;>
        simp [kmswStage, kmswStep, kmswCodeStep, h2, kmswStepOfStep, hh,
          State.addEdge, hrev, hdrop]



private theorem ul_entry (w : ℕ → Fin 3) (t : ℕ) :
    ∀ (i e : ℕ), (kmswStage w t).UL.dropLast.reverse[i]? = some e →
      ∃ s, s < t ∧ L w s + 1 + (i : ℤ) = L w t ∧
        (∀ j, s < j → j ≤ t → L w s < L w j) ∧
        e = (kmswStage w s).active := by
  induction t with
  | zero =>
    intro i e h
    simp [kmswStage, kmswInit] at h
  | succ t ih =>
    intro i e h
    rw [ul_stack_update] at h
    have hL := kmswL_succ w t
    by_cases h0 : w t = 0
    · have hlevel : L w (t + 1) = L w t - 1 := by simpa [h0, sub_eq_add_neg] using hL
      simp only [h0, ite_true, List.getElem?_tail] at h
      obtain ⟨s, hst, hsi, hfuture, he⟩ := ih (i + 1) e h
      refine ⟨s, by omega, by push_cast at hsi; omega, ?_, he⟩
      intro j hsj hj
      by_cases hjt : j ≤ t
      · exact hfuture j hsj hjt
      · have : j = t + 1 := by omega
        subst j
        push_cast at hsi
        omega
    · by_cases h1 : w t = 1
      · have hlevel : L w (t + 1) = L w t := by simpa [h1] using hL
        simp only [h1, ite_true] at h
        obtain ⟨s, hst, hsi, hfuture, he⟩ := ih i e h
        refine ⟨s, by omega, by omega, ?_, he⟩
        intro j hsj hj
        by_cases hjt : j ≤ t
        · exact hfuture j hsj hjt
        · have : j = t + 1 := by omega
          subst j
          omega
      · have h2 : w t = 2 := by
          apply Fin.ext
          have hv := (w t).isLt
          have hn0 : (w t).val ≠ 0 := fun hh => h0 (Fin.ext hh)
          have hn1 : (w t).val ≠ 1 := fun hh => h1 (Fin.ext hh)
          omega
        have hlevel : L w (t + 1) = L w t + 1 := by simpa [h2] using hL
        simp only [h0, h1, ite_false] at h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          refine ⟨t, by omega, by simp [hlevel], ?_, h.symm⟩
          intro j htj hj
          have : j = t + 1 := by omega
          subst j
          omega
        | succ i =>
          simp only [List.getElem?_cons_succ] at h
          obtain ⟨s, hst, hsi, hfuture, he⟩ := ih i e h
          refine ⟨s, by omega, by push_cast; omega, ?_, he⟩
          intro j hsj hj
          by_cases hjt : j ≤ t
          · exact hfuture j hsj hjt
          · have : j = t + 1 := by omega
            subst j
            omega



theorem kmswStage_left_head_pair (w : ℕ → Fin 3) (t e : ℕ) (es : List ℕ)
    (hc : w t = 0) (h : (kmswStage w t).UL.dropLast.reverse = e :: es) :
    ∃ r, kmswLpair w r t ∧ e = (kmswStage w r).active := by
  have hentry : (kmswStage w t).UL.dropLast.reverse[0]? = some e := by simp [h]
  obtain ⟨r, hrt, hlevel, hfuture, he⟩ := ul_entry w t 0 e hentry
  have hL : L w (t + 1) = L w t - 1 := by simpa [hc, sub_eq_add_neg] using kmswL_succ w t
  exact ⟨r, ⟨hrt, by omega, hfuture⟩, he⟩



theorem kmswStage_left_head_nil_iff (w : ℕ → Fin 3) (t : ℕ) (hc : w t = 0) :
    (kmswStage w t).UL.dropLast.reverse = [] ↔ ¬ ∃ r, kmswLpair w r t := by
  constructor
  · intro hnil ⟨r, hrt, _, hfuture⟩
    have hlt := hfuture t hrt le_rfl
    have hmin := runningMin_le (L w) t r (by omega)
    have hlen := kmswStage_UL_length w t
    have hempty := congrArg List.length hnil
    change minL w t ≤ L w r at hmin
    simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hempty
    omega
  · intro hno
    cases hh : (kmswStage w t).UL.dropLast.reverse with
    | nil => rfl
    | cons e es =>
      obtain ⟨r, hr, _⟩ := kmswStage_left_head_pair w t e es hc hh
      exact (hno ⟨r, hr⟩).elim



private theorem lr_update (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w (t + 1)).LR =
      if w t = 2 ∧ R w t = minR w t then
        (kmswStage w t).LR ++ [(kmswStage w (t + 1)).active]
      else (kmswStage w t).LR := by
  have hlen := kmswStage_UR_length w t
  by_cases h0 : w t = 0
  · cases hh : (kmswStage w t).UL.dropLast.reverse <;>
      simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep, hh, State.addEdge]
  · by_cases h1 : w t = 1
    · simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
    · have h2 : w t = 2 := by
        apply Fin.ext
        have hv := (w t).isLt
        have hn0 : (w t).val ≠ 0 := fun hh => h0 (Fin.ext hh)
        have hn1 : (w t).val ≠ 1 := fun hh => h1 (Fin.ext hh)
        omega
      cases hh : (kmswStage w t).UR with
      | nil =>
        have hrec : R w t = minR w t := by simp only [hh, List.length_nil] at hlen; omega
        simp [kmswStage, kmswStep, kmswCodeStep, h2, kmswStepOfStep, hh,
          State.addEdge, hrec]
      | cons e es =>
        have hnrec : R w t ≠ minR w t := by
          simp only [hh, List.length_cons] at hlen
          omega
        simp [kmswStage, kmswStep, kmswCodeStep, h2, kmswStepOfStep, hh, hnrec]



theorem kmswStage_LR_eq_unmatchedDowns (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).LR = (kmswStage w 0).active ::
      ((List.range t).filter
        (fun s => decide (w s = 2 ∧ R w s = minR w s))).map
        (fun s => (kmswStage w (s + 1)).active) := by
  classical
  induction t with
  | zero => simp [kmswStage, kmswInit]
  | succ t ih =>
    rw [lr_update, ih, List.range_succ, List.filter_append, List.map_append]
    by_cases hrec : w t = 2 ∧ R w t = minR w t <;> simp [hrec]



private theorem minL_excursion (w : ℕ → Fin 3) {r t : ℕ} (hrt : r ≤ t)
    (hfuture : ∀ j, r < j → j ≤ t → L w r < L w j) : minL w r = minL w t := by
  obtain ⟨i, hi, hei⟩ := runningMin_attained (L w) r
  obtain ⟨j, hj, hej⟩ := runningMin_attained (L w) t
  change minL w r = L w i at hei
  change minL w t = L w j at hej
  have hle := runningMin_le (L w) t i (by omega)
  change minL w t ≤ L w i at hle
  by_cases hjr : j ≤ r
  · have hle' := runningMin_le (L w) r j hjr
    change minL w r ≤ L w j at hle'
    omega
  · have hlt := hfuture j (by omega) hj
    have hle' := runningMin_le (L w) r r le_rfl
    change minL w r ≤ L w r at hle'
    omega



private theorem ul_height_entry (w : ℕ → Fin 3) (t i : ℕ)
    (hi : i < (kmswStage w t).UL.length) :
    ∃ r, r ≤ t ∧ L w r - minL w r + 1 = ((i + 1 : ℕ) : ℤ) ∧
      (∀ j, r < j → j ≤ t → L w r - minL w r < L w j - minL w j) ∧
      (kmswStage w t).UL[i] = (kmswStage w r).active := by
  have hlen := kmswStage_UL_length w t
  by_cases hlast : i + 1 = (kmswStage w t).UL.length
  · refine ⟨t, le_rfl, by push_cast; omega, ?_, ?_⟩
    · intro j htj hj
      omega
    · obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
      have hidx : i = xs.length := by
        rw [hxs, List.length_append, List.length_singleton] at hlast
        omega
      simp only [hxs, List.getElem_concat_length hidx]
  · let k := (kmswStage w t).UL.length - 2 - i
    have hindex : k + i + 1 = (kmswStage w t).UL.dropLast.length := by
      simp only [List.length_dropLast]
      dsimp [k]
      omega
    have hentry : (kmswStage w t).UL.dropLast.reverse[k]? =
        some ((kmswStage w t).UL[i]) := by
      rw [List.getElem?_reverse' hindex, List.getElem?_dropLast]
      rw [ite_eq_left (by omega), List.getElem?_eq_getElem hi]
    obtain ⟨r, hrt, hlevel, hfuture, he⟩ := ul_entry w t k _ hentry
    have hmin := minL_excursion w (by omega : r ≤ t) hfuture
    refine ⟨r, by omega, ?_, ?_, he⟩
    · dsimp [k] at hlevel
      push_cast
      omega
    · intro j hrj hjt
      have hminj := minL_excursion w (by omega : r ≤ j)
        (fun u hru huj => hfuture u hru (by omega))
      have hlt := hfuture j hrj hjt
      omega



theorem kmswStage_UL_eq_lastHeight (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).UL =
      (List.range (L w t - minL w t + 1).toNat).map
        (fun i => (kmswStage w (kmswUlTime w t (i + 1))).active) := by
  apply List.ext_getElem
  · have hlen := kmswStage_UL_length w t
    simp only [List.length_map, List.length_range]
    omega
  · intro i hi _
    obtain ⟨r, hrt, hheight, hfuture, he⟩ := ul_height_entry w t i hi
    have htime : kmswUlTime w t (i + 1) = r := by
      unfold kmswUlTime
      apply Nat.findGreatest_eq_iff.mpr
      refine ⟨hrt, fun _ => hheight, ?_⟩
      intro j hrj hjt hbad
      have := hfuture j hrj hjt
      omega
    simp only [List.getElem_map, List.getElem_range]
    rw [htime]
    exact he

end DirectedDistances.KMSW
