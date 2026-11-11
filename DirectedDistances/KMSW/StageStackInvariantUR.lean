module

public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.KMSW.StageActiveEdges
public import DirectedDistances.KMSW.BoundaryRecordsMissing
import Mathlib.Data.Nat.Find

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW



@[expose] def kmswRpair (w : ℕ → Fin 3) (s t : ℕ) : Prop :=
  s < t ∧ R w (t + 1) = R w s ∧
    ∀ j, s < j → j ≤ t → R w s < R w j



@[expose] noncomputable def kmswUrTime (w : ℕ → Fin 3) (t i : ℕ) : ℕ :=
  Nat.findGreatest (fun s => R w s + 1 + (i : ℤ) = R w t) t



theorem kmswRpair_left_unique (w : ℕ → Fin 3) {s r t : ℕ}
    (hs : kmswRpair w s t) (hr : kmswRpair w r t) : s = r := by
  rcases hs with ⟨hst, hse, hsi⟩
  rcases hr with ⟨hrt, hre, hri⟩
  rcases lt_trichotomy s r with h | h | h
  · have := hsi r h (by omega)
    omega
  · exact h
  · have := hri s h (by omega)
    omega



theorem kmswRpair_right_unique (w : ℕ → Fin 3) {s t u : ℕ}
    (ht : kmswRpair w s t) (hu : kmswRpair w s u) : t = u := by
  rcases ht with ⟨hst, hte, hti⟩
  rcases hu with ⟨hsu, hue, hui⟩
  rcases lt_trichotomy t u with h | h | h
  · have := hui (t + 1) (by omega) (by omega)
    omega
  · exact h
  · have := hti (u + 1) (by omega) (by omega)
    omega



private theorem ur_entry (w : ℕ → Fin 3) (t : ℕ) :
    ∀ (i e : ℕ), (kmswStage w t).UR[i]? = some e →
      ∃ s, s < t ∧ R w s + 1 + (i : ℤ) = R w t ∧
        (∀ j, s < j → j ≤ t → R w s < R w j) ∧
        e = (kmswStage w s).nextEdge + 1 := by
  induction t with
  | zero =>
    intro i e h
    simp [kmswStage, kmswInit] at h
  | succ t ih =>
    intro i e h
    have hR : R w (t + 1) =
        R w t + (RandomWalk.lazyTwoDimensionalStep (w t)).2 :=
      Finset.sum_range_succ _ _
    by_cases hc0 : w t = 0
    · have hlevel : R w (t + 1) = R w t := by simpa [hc0] using hR
      have hstack : (kmswStage w (t + 1)).UR = (kmswStage w t).UR := by
        cases hh : (kmswStage w t).UL.dropLast.reverse <;>
          simp [kmswStage, kmswStep, kmswCodeStep, hc0, kmswStepOfStep, hh,
            State.addEdge]
      rw [hstack] at h
      obtain ⟨s, hst, hsi, hfuture, he⟩ := ih i e h
      refine ⟨s, by omega, by omega, ?_, he⟩
      intro j hsj hj
      by_cases hjt : j ≤ t
      · exact hfuture j hsj hjt
      · have : j = t + 1 := by omega
        subst j
        omega
    · by_cases hc1 : w t = 1
      · have hlevel : R w (t + 1) = R w t + 1 := by simpa [hc1] using hR
        have hstack : (kmswStage w (t + 1)).UR =
            ((kmswStage w t).nextEdge + 1) :: (kmswStage w t).UR := by
          simp [kmswStage, kmswStep, kmswCodeStep, hc1, kmswStepOfStep, State.addEdge]
        rw [hstack] at h
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
      · have hc2 : w t = 2 := by
          apply Fin.ext
          have hv := (w t).isLt
          have hn0 : (w t).val ≠ 0 := by intro hv; exact hc0 (Fin.ext hv)
          have hn1 : (w t).val ≠ 1 := by intro hv; exact hc1 (Fin.ext hv)
          omega
        have hlevel : R w (t + 1) = R w t - 1 := by
          simpa [hc2, sub_eq_add_neg] using hR
        cases hUR : (kmswStage w t).UR with
        | nil =>
          simp [kmswStage, kmswStep, kmswCodeStep, hc2, kmswStepOfStep, hUR,
            State.addEdge] at h
        | cons a es =>
          have hstack : (kmswStage w (t + 1)).UR = es := by
            simp [kmswStage, kmswStep, kmswCodeStep, hc2, kmswStepOfStep, hUR]
          rw [hstack] at h
          have hold : (kmswStage w t).UR[i + 1]? = some e := by
            simpa [hUR] using h
          obtain ⟨s, hst, hsi, hfuture, he⟩ := ih (i + 1) e hold
          refine ⟨s, by omega, by push_cast at hsi; omega, ?_, he⟩
          intro j hsj hj
          by_cases hjt : j ≤ t
          · exact hfuture j hsj hjt
          · have : j = t + 1 := by omega
            subst j
            push_cast at hsi
            omega



theorem kmswStage_down_head_pair (w : ℕ → Fin 3) (t e : ℕ) (es : List ℕ)
    (hc : w t = 2) (h : (kmswStage w t).UR = e :: es) :
    ∃ s, kmswRpair w s t ∧ e = (kmswStage w s).nextEdge + 1 := by
  have hentry : (kmswStage w t).UR[0]? = some e := by simp [h]
  obtain ⟨s, hst, hlevel, hfuture, he⟩ := ur_entry w t 0 e hentry
  have hR : R w (t + 1) = R w t - 1 := by
    have hh : R w (t + 1) =
        R w t + (RandomWalk.lazyTwoDimensionalStep (w t)).2 :=
      Finset.sum_range_succ _ _
    simpa [hc, sub_eq_add_neg] using hh
  exact ⟨s, ⟨hst, by omega, hfuture⟩, he⟩



theorem kmswStage_down_head_nil_iff (w : ℕ → Fin 3) (t : ℕ) (hc : w t = 2) :
    (kmswStage w t).UR = [] ↔ ¬ ∃ s, kmswRpair w s t := by
  constructor
  · intro hnil ⟨s, hst, _, hfuture⟩
    have hlt := hfuture t hst le_rfl
    have hmin := runningMin_le (R w) t s (by omega)
    have hlen := kmswStage_UR_length w t
    rw [hnil] at hlen
    change minR w t ≤ R w s at hmin
    simp only [List.length_nil, Nat.cast_zero] at hlen
    omega
  · intro hno
    cases hUR : (kmswStage w t).UR with
    | nil => rfl
    | cons e es =>
      obtain ⟨s, hs, _⟩ := kmswStage_down_head_pair w t e es hc hUR
      exact (hno ⟨s, hs⟩).elim




theorem kmswStage_UR_eq_lastCrossing (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).UR =
      (List.range (R w t - minR w t).toNat).map
        (fun i => (kmswStage w (kmswUrTime w t i)).nextEdge + 1) := by
  apply List.ext_getElem
  · have hlen := kmswStage_UR_length w t
    simp only [List.length_map, List.length_range]
    omega
  · intro i hi _
    have hentry : (kmswStage w t).UR[i]? = some ((kmswStage w t).UR[i]) :=
      List.getElem?_eq_getElem hi
    obtain ⟨s, hst, hlevel, hfuture, he⟩ := ur_entry w t i _ hentry
    have htime : kmswUrTime w t i = s := by
      unfold kmswUrTime
      apply Nat.findGreatest_eq_iff.mpr
      refine ⟨by omega, fun _ => hlevel, ?_⟩
      intro j hsj hj hbad
      have := hfuture j hsj hj
      omega
    simp only [List.getElem_map, List.getElem_range]
    rw [htime]
    exact he



private theorem ll_empty_iff_record (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).UL.dropLast.reverse = [] ↔ L w t = minL w t := by
  have hlen := kmswStage_UL_length w t
  obtain ⟨es, hes⟩ := kmswStage_UL_last w t
  have hpos : 0 < (kmswStage w t).UL.length := by
    rw [hes]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hl
    omega
  · intro h
    apply List.length_eq_zero_iff.mp
    simp only [List.length_reverse, List.length_dropLast]
    omega



private theorem ll_update (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w (t + 1)).LL =
      if w t = 0 ∧ L w t = minL w t then
        ((kmswStage w t).nextEdge + 1) :: (kmswStage w t).LL
      else (kmswStage w t).LL := by
  by_cases hc0 : w t = 0
  · cases hh : (kmswStage w t).UL.dropLast.reverse with
    | nil =>
      have hrecord := (ll_empty_iff_record w t).mp hh
      simp [kmswStage, kmswStep, kmswCodeStep, hc0, kmswStepOfStep, hh,
        State.addEdge, hrecord]
    | cons e es =>
      have hnrecord : L w t ≠ minL w t := by
        intro hrec
        have hempty := (ll_empty_iff_record w t).mpr hrec
        rw [hh] at hempty
        contradiction
      simp [kmswStage, kmswStep, kmswCodeStep, hc0, kmswStepOfStep, hh,
        State.addEdge, hnrecord]
  · by_cases hc1 : w t = 1
    · simp [kmswStage, kmswStep, kmswCodeStep, hc1, kmswStepOfStep, State.addEdge]
    · have hc2 : w t = 2 := by
        apply Fin.ext
        have hv := (w t).isLt
        have hn0 : (w t).val ≠ 0 := by intro hv; exact hc0 (Fin.ext hv)
        have hn1 : (w t).val ≠ 1 := by intro hv; exact hc1 (Fin.ext hv)
        omega
      cases hUR : (kmswStage w t).UR <;>
        simp [kmswStage, kmswStep, kmswCodeStep, hc2, kmswStepOfStep, hUR, State.addEdge]




theorem kmswStage_LL_eq_unmatchedLefts (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).LL =
      (((List.range t).filter (fun s => decide
        (w s = 0 ∧ L w s = minL w s))).reverse.map
          (fun s => (kmswStage w s).nextEdge + 1)) := by
  classical
  induction t with
  | zero => simp [kmswStage, kmswInit]
  | succ t ih =>
    rw [ll_update, ih, List.range_succ, List.filter_append,
      List.reverse_append, List.map_append]
    by_cases hrec : w t = 0 ∧ L w t = minL w t <;> simp [hrec]

end DirectedDistances.KMSW
