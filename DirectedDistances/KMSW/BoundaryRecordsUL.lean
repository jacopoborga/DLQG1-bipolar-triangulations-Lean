module

public import DirectedDistances.KMSW.BoundaryDynamics
import Mathlib.Data.List.Range

/-! # Active-edge boundary records

Stack bookkeeping for `lem-kmsw-bdy`(ii),(iii), -/

public section
namespace DirectedDistances.KMSW
open scoped Classical

 
@[expose] def act (w : ℕ → Fin 3) (m : ℕ) : ℕ := (kmswStage w m).active

private theorem allocated_step (s : State) (c : Fin 3)
    (_ha : s.active < s.nextEdge)
    (hb : ∀ e ∈ s.UL ++ s.UR, e < s.nextEdge) :
    (kmswStep s c).active < (kmswStep s c).nextEdge ∧
      (∀ e ∈ (kmswStep s c).UL ++ (kmswStep s c).UR,
        e < (kmswStep s c).nextEdge) ∧
      s.nextEdge ≤ (kmswStep s c).nextEdge := by
  have hu : ∀ e ∈ s.UL, e < s.nextEdge := by
    intro e he; exact hb e (List.mem_append_left _ he)
  have hr : ∀ e ∈ s.UR, e < s.nextEdge := by
    intro e he; exact hb e (List.mem_append_right _ he)
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
    dsimp only [kmswStepOfStep]
    split <;> simp_all [State.addEdge, List.mem_append]
    all_goals grind
  | left =>
    dsimp only [kmswStepOfStep]
    split
    next e es hs =>
      have hrest : ∀ f ∈ es.reverse, f < s.nextEdge := by
        intro f hf
        apply hu f
        have hmem : f ∈ s.UL.dropLast.reverse := by
          rw [hs]
          exact List.mem_cons_of_mem _ (List.mem_reverse.mp hf)
        exact List.dropLast_subset _ (List.mem_reverse.mp hmem)
      simp only [State.addEdge]
      constructor
      · omega
      constructor
      · intro f hf
        simp only [List.mem_append, List.mem_singleton] at hf
        rcases hf with (hf | hf) | hf
        · exact (hrest f hf).trans_le (by omega)
        · omega
        · exact (hr f hf).trans_le (by omega)
      · omega
    next hs =>
      simp only [State.addEdge]
      constructor
      · omega
      constructor
      · intro f hf
        simp only [List.mem_append, List.mem_singleton] at hf
        rcases hf with hf | hf
        · omega
        · exact (hr f hf).trans_le (by omega)
      · omega
  | up =>
    simp only [kmswStepOfStep, State.addEdge]
    constructor
    · omega
    constructor
    · intro e he
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (he | he) | (he | he)
      · exact (hu e (List.dropLast_subset _ he)).trans_le (by omega)
      · omega
      · omega
      · exact (hr e he).trans_le (by omega)
    · omega

private theorem allocated_stage (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).active < (kmswStage w n).nextEdge ∧
      ∀ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
        e < (kmswStage w n).nextEdge := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih => exact ⟨(allocated_step _ _ ih.1 ih.2).1,
      (allocated_step _ _ ih.1 ih.2).2.1⟩

 
theorem kmswStage_nextEdge_mono (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    (kmswStage w m).nextEdge ≤ (kmswStage w n).nextEdge := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih =>
    exact ih.trans (allocated_step _ _ (allocated_stage w n).1
      (allocated_stage w n).2).2.2

/-- An earlier active edge remains allocated (`def-kmsw`, -/
theorem act_lt_nextEdge (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    act w m < (kmswStage w n).nextEdge :=
  (allocated_stage w m).1.trans_le (kmswStage_nextEdge_mono w hmn)

private theorem step_endpoints (s : State) (c : Fin 3) {e : ℕ} (he : e < s.nextEdge) :
    (kmswStep s c).west e = s.west e ∧ (kmswStep s c).east e = s.east e := by
  have h0 : e ≠ s.nextEdge := by omega
  have h1 : e ≠ s.nextEdge + 1 := by omega
  unfold kmswStep
  cases kmswCodeStep c <;> dsimp only [kmswStepOfStep]
  · split <;> simp [State.addEdge, h0]
  · split <;> simp [State.addEdge, h0, h1]
  · simp [State.addEdge, h0, h1]

/-- Allocated edge endpoints persist through all subsequent stages of -/
theorem kmswStage_endpoints_stable (w : ℕ → Fin 3) {m n e : ℕ}
    (hmn : m ≤ n) (he : e < (kmswStage w m).nextEdge) :
    (kmswStage w n).west e = (kmswStage w m).west e ∧
      (kmswStage w n).east e = (kmswStage w m).east e := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ n hmn ih =>
    have hs := step_endpoints (kmswStage w n) (w n)
      (he.trans_le (kmswStage_nextEdge_mono w hmn))
    exact ⟨hs.1.trans ih.1, hs.2.trans ih.2⟩

/-- Existing status flags only change by activating the new active edge in -/
theorem kmswStep_present_existing (s : State) (c : Fin 3) {e : ℕ}
    (he : e < s.nextEdge) :
    (kmswStep s c).present e =
      if e = (kmswStep s c).active then true else s.present e := by
  have h0 : e ≠ s.nextEdge := by omega
  have h1 : e ≠ s.nextEdge + 1 := by omega
  unfold kmswStep
  cases kmswCodeStep c with
  | down => cases hs : s.UR <;> simp [kmswStepOfStep, hs, State.addEdge, h0]
  | left => cases hs : s.UL.dropLast.reverse <;>
      simp [kmswStepOfStep, hs, State.addEdge, h0, h1]
  | up => simp [kmswStepOfStep, State.addEdge, h0, h1]

private theorem coord_L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem coord_R_succ (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem new_min_iff (w : ℕ → Fin 3) (n : ℕ) :
    (∀ j, j < n + 1 → R w (n + 1) < R w j) ↔
      w n = 2 ∧ (kmswStage w n).UR = [] := by
  have hlen := kmswStage_UR_length w n
  have hle := runningMin_le (R w) n n (le_refl _)
  change minR w n ≤ R w n at hle
  obtain ⟨i, hi, he⟩ := runningMin_attained (R w) n
  change minR w n = R w i at he
  have hc := coord_R_succ w n
  constructor
  · intro h
    have hn := h n (by omega)
    have hh := h i (by omega)
    have hw : w n = 2 := by
      by_contra h2
      have hcases : w n = 0 ∨ w n = 1 := by
        have := (w n).isLt
        have : (w n).val ≠ 2 := fun hh => h2 (Fin.ext hh)
        rcases Nat.lt_or_ge (w n).val 1 with hv | hv
        · exact Or.inl (Fin.ext (by omega))
        · exact Or.inr (Fin.ext (by omega))
      rcases hcases with h0 | h1
      · simp [h0] at hc; omega
      · simp [h1] at hc; omega
    refine ⟨hw, ?_⟩
    rw [hw, RandomWalk.lazyTwoDimensionalStep_two] at hc
    have : (kmswStage w n).UR.length = 0 := by dsimp at hc; omega
    exact List.length_eq_zero_iff.mp this
  · rintro ⟨hw, hu⟩ j hj
    have hmin := runningMin_le (R w) n j (by omega)
    change minR w n ≤ R w j at hmin
    rw [hu] at hlen
    rw [hw, RandomWalk.lazyTwoDimensionalStep_two] at hc
    simp only [List.length_nil, Nat.cast_zero] at hlen
    dsimp at hc
    omega

/-- Lower-right edges are exactly the active edges at strict new vertical
minima, including time zero (`lem-kmsw-bdy`(ii), -/
theorem kmswStage_LR_eq (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR =
      ((List.range (n + 1)).filter
        (fun m => decide (∀ j, j < m → R w m < R w j))).map (act w) := by
  induction n with
  | zero => simp [kmswStage, kmswInit, act]
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append]
    rw [← ih]
    by_cases hnew : ∀ j, j < n + 1 → R w (n + 1) < R w j
    · obtain ⟨hw, hu⟩ := (new_min_iff w n).mp hnew
      have hf : ([n + 1] : List ℕ).filter
          (fun m => decide (∀ j, j < m → R w m < R w j)) = [n + 1] := by
        apply List.filter_eq_self.mpr
        intro a ha
        have : a = n + 1 := by simpa only [List.mem_singleton] using ha
        subst a
        exact decide_eq_true hnew
      rw [hf]
      simp only [List.map_cons, List.map_nil]
      simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, hu,
        State.addEdge, act]
    · simp only [List.filter_cons, decide_eq_true_eq, hnew,
        ↓reduceIte, List.filter_nil, List.map_nil, List.append_nil]
      change (kmswStep (kmswStage w n) (w n)).LR = (kmswStage w n).LR
      unfold kmswStep
      cases hcode : kmswCodeStep (w n) with
      | left => dsimp only [kmswStepOfStep]; split <;> rfl
      | up => rfl
      | down =>
        dsimp only [kmswStepOfStep]
        have hw : w n = 2 := by
          unfold kmswCodeStep at hcode
          split at hcode
          · contradiction
          · split at hcode
            · contradiction
            · apply Fin.ext
              have := (w n).isLt
              rename_i h0 h1
              have hn0 : (w n).val ≠ 0 := fun hh => h0 (Fin.ext hh)
              have hn1 : (w n).val ≠ 1 := fun hh => h1 (Fin.ext hh)
              omega
        have hu : (kmswStage w n).UR ≠ [] := by
          intro hu; exact hnew ((new_min_iff w n).mpr ⟨hw, hu⟩)
        split
        · rfl
        · contradiction

private theorem reverse_dropLast (xs : List ℕ) :
    xs.dropLast.reverse = xs.reverse.tail := by
  simpa only [List.reverse_reverse] using
    congrArg List.reverse (List.dropLast_reverse (l := xs.reverse))

private theorem step_UL_reverse (s : State) (c : Fin 3) :
    (kmswStep s c).UL.reverse = (kmswStep s c).active ::
      (if c = 0 then s.UL.reverse.tail.tail
        else if c = 1 then s.UL.reverse.tail else s.UL.reverse) := by
  fin_cases c
  · change (kmswStepOfStep s .left).UL.reverse =
      (kmswStepOfStep s .left).active :: s.UL.reverse.tail.tail
    cases hs : s.UL.dropLast.reverse <;>
      simp only [kmswStepOfStep, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append, List.reverse_reverse,
        ← reverse_dropLast, hs, List.tail_cons, List.tail_nil]
  · change (kmswStepOfStep s .up).UL.reverse =
      (kmswStepOfStep s .up).active :: s.UL.reverse.tail
    simp only [kmswStepOfStep, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append, reverse_dropLast]
  · change (kmswStepOfStep s .down).UL.reverse =
      (kmswStepOfStep s .down).active :: s.UL.reverse
    cases hs : s.UR <;> simp [kmswStepOfStep, hs]

private noncomputable def recordTimes (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  ((List.range (n + 1)).filter
    (fun m => decide (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j))).reverse

private theorem recordTimes_succ (w : ℕ → Fin 3) (n : ℕ) :
    recordTimes w (n + 1) = (n + 1) ::
      (recordTimes w n).filter (fun m => decide (L w m < L w (n + 1))) := by
  have hp (m : ℕ) (hm : m < n + 1) :
      (∀ j, m < j → j ≤ n + 1 → L w m + 1 ≤ L w j) ↔
        ((∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j) ∧
          L w m < L w (n + 1)) := by
    constructor
    · intro h
      exact ⟨fun j hj hn => h j hj (by omega), by have := h (n + 1) hm (le_refl _); omega⟩
    · rintro ⟨h, ht⟩ j hj hn
      by_cases hjn : j ≤ n
      · exact h j hj hjn
      · have : j = n + 1 := by omega
        subst j
        omega
  have hf :
      (List.range (n + 1)).filter
        (fun m => decide (∀ j, m < j → j ≤ n + 1 → L w m + 1 ≤ L w j)) =
      ((List.range (n + 1)).filter
        (fun m => decide (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j))).filter
        (fun m => decide (L w m < L w (n + 1))) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro m hm
    have hm' : m < n + 1 := List.mem_range.mp hm
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact (hp m hm').trans and_comm
  unfold recordTimes
  rw [List.range_succ, List.filter_append, hf]
  have hlast : ∀ j, n + 1 < j → j ≤ n + 1 → L w (n + 1) + 1 ≤ L w j := by
    intro j hj hn; omega
  have hfLast : ([n + 1] : List ℕ).filter
      (fun m => decide (∀ j, m < j → j ≤ n + 1 → L w m + 1 ≤ L w j)) = [n + 1] := by
    apply List.filter_eq_self.mpr
    intro a ha
    have : a = n + 1 := List.mem_singleton.mp ha
    subst a
    exact decide_eq_true hlast
  rw [hfLast]
  simp only [List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, ← List.filter_reverse]

private theorem recordTimes_zero (w : ℕ → Fin 3) : recordTimes w 0 = [0] := by
  unfold recordTimes
  change (List.filter _ [0]).reverse = [0]
  rw [List.filter_cons_of_pos (p := fun m =>
    decide (∀ j, m < j → j ≤ 0 → L w m + 1 ≤ L w j)) (by
      apply decide_eq_true
      intro j hj hn
      omega)]
  rfl

private def Levels (f : ℕ → ℤ) : List ℕ → ℤ → Prop
  | [], _ => True
  | a :: xs, t => f a = t ∧ Levels f xs (t - 1)

private theorem levels_le {f : ℕ → ℤ} {xs : List ℕ} {t : ℤ}
    (h : Levels f xs t) : ∀ a ∈ xs, f a ≤ t := by
  induction xs generalizing t with
  | nil => simp
  | cons a xs ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1.le
    · exact (ih h.2 b hb).trans (by omega)

private theorem levels_filter_down {f : ℕ → ℤ} {xs : List ℕ} {t : ℤ}
    (h : Levels f xs t) :
    xs.filter (fun a => decide (f a < t + 1)) = xs := by
  apply List.filter_eq_self.mpr
  intro a ha
  simp only [decide_eq_true_eq]
  have := levels_le h a ha
  omega

private theorem levels_filter_up {f : ℕ → ℤ} {xs : List ℕ} {t : ℤ}
    (h : Levels f xs t) :
    xs.filter (fun a => decide (f a < t)) = xs.tail := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    have hnot : ¬ f a < t := by have := h.1; omega
    simp only [List.filter_cons, decide_eq_true_eq, hnot, ↓reduceIte, List.tail_cons]
    have he : t = (t - 1) + 1 := by omega
    rw [he]
    exact levels_filter_down h.2

private theorem levels_filter_left {f : ℕ → ℤ} {xs : List ℕ} {t : ℤ}
    (h : Levels f xs t) :
    xs.filter (fun a => decide (f a < t - 1)) = xs.tail.tail := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    have hnot : ¬ f a < t - 1 := by have := h.1; omega
    simp only [List.filter_cons, decide_eq_true_eq, hnot, ↓reduceIte, List.tail_cons]
    exact levels_filter_up h.2

private theorem levels_tail {f : ℕ → ℤ} {xs : List ℕ} {t : ℤ}
    (h : Levels f xs t) : Levels f xs.tail (t - 1) := by
  cases xs with
  | nil => trivial
  | cons a xs => exact h.2

private theorem UL_records_and_levels (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.reverse = (recordTimes w n).map (act w) ∧
      Levels (L w) (recordTimes w n) (L w n) := by
  induction n with
  | zero => rw [recordTimes_zero]; exact ⟨rfl, ⟨rfl, trivial⟩⟩
  | succ n ih =>
    have hc := coord_L_succ w n
    have hs := step_UL_reverse (kmswStage w n) (w n)
    change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
    rw [recordTimes_succ]
    by_cases h0 : w n = 0
    · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hc
      change L w (n + 1) = L w n - 1 at hc
      rw [hc, levels_filter_left ih.2]
      constructor
      · simpa only [h0, ↓reduceIte, ih.1, List.map_cons, List.map_tail] using hs
      · exact ⟨hc, by simpa only [hc] using levels_tail (levels_tail ih.2)⟩
    · by_cases h1 : w n = 1
      · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hc
        dsimp at hc
        rw [add_zero] at hc
        rw [hc, levels_filter_up ih.2]
        constructor
        · simpa only [h1, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, ih.1, List.map_cons, List.map_tail] using hs
        · exact ⟨hc, by simpa only [hc] using levels_tail ih.2⟩
      · have h2 : w n = 2 := by
          apply Fin.ext
          have := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
          have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
          omega
        rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hc
        dsimp at hc
        rw [hc, levels_filter_down ih.2]
        constructor
        · simpa only [h0, h1, ↓reduceIte, ih.1, List.map_cons] using hs
        · exact ⟨hc, by simpa only [add_sub_cancel_right] using ih.2⟩

/-- Upper-left edges are the active edges at strict future horizontal records,
in increasing time order (`lem-kmsw-bdy`(iii), -/
theorem kmswStage_UL_eq (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL =
      ((List.range (n + 1)).filter
        (fun m => decide (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j))).map (act w) := by
  have h := (UL_records_and_levels w n).1
  apply List.reverse_inj.mp
  simpa only [recordTimes, List.map_reverse] using h

private def westStack (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  (kmswStage w n).UL.reverse.map (kmswStage w n).west

private theorem westStack_old_map (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.reverse.map (kmswStage w (n + 1)).west = westStack w n := by
  apply List.map_congr_left
  intro e he
  exact (step_endpoints _ _ ((allocated_stage w n).2 e
    (List.mem_append_left _ (List.mem_reverse.mp he)))).1

private theorem westStack_down (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2) :
    (westStack w (n + 1)).tail = westStack w n := by
  have hs := step_UL_reverse (kmswStage w n) (w n)
  change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  simp only [hc, h0, h1, ↓reduceIte] at hs
  change ((kmswStage w (n + 1)).UL.reverse.map
    (kmswStage w (n + 1)).west).tail = _
  rw [hs]
  simp only [List.map_cons, List.tail_cons]
  exact westStack_old_map w n

private theorem westStack_up (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    westStack w (n + 1) = westStack w n := by
  have hs := step_UL_reverse (kmswStage w n) (w n)
  change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
  have h0 : (1 : Fin 3) ≠ 0 := by decide
  simp only [hc, h0, ↓reduceIte] at hs
  have ht := congrArg List.tail (westStack_old_map w n)
  simp only [← List.map_tail] at ht
  have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).west (act w n) := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
  unfold westStack
  rw [hs, List.map_cons]
  change (kmswStage w (n + 1)).west (act w (n + 1)) :: _ = _
  rw [ht, hw]
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  simp [westStack, hes, act]

private theorem westStack_left (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hlen : 2 ≤ (kmswStage w n).UL.length) :
    westStack w (n + 1) = (westStack w n).tail := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  have hnon : es.reverse ≠ [] := by
    intro he
    have hlen' := congrArg List.length he
    rw [hes] at hlen
    simp only [List.length_reverse, List.length_nil] at hlen'
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  cases he : es.reverse with
  | nil => exact (hnon he).elim
  | cons e rest =>
    have hrev : (kmswStage w n).UL.reverse = act w n :: e :: rest := by
      simp only [hes, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, he, act]
    have hdrop : (kmswStage w n).UL.dropLast.reverse = e :: rest := by
      rw [reverse_dropLast, hrev, List.tail_cons]
    have hs := step_UL_reverse (kmswStage w n) (w n)
    change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
    simp only [hc, ↓reduceIte, hrev, List.tail_cons] at hs
    have ht := congrArg (fun xs : List ℕ => xs.tail.tail) (westStack_old_map w n)
    simp only [← List.map_tail, hrev, List.tail_cons] at ht
    have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
        (kmswStage w n).west e := by
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
        hdrop, State.addEdge]
    unfold westStack
    rw [hs, List.map_cons]
    change (kmswStage w (n + 1)).west (act w (n + 1)) :: _ = _
    rw [hw, ht]
    simp [westStack, hrev]

private theorem westStack_excursion (w : ℕ → Fin 3) {a n : ℕ} (han : a ≤ n)
    (habove : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j) :
    (westStack w n).drop (L w n - L w a).toNat = westStack w a := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ n han ih =>
    have hprior : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j :=
      fun j haj hjn => habove j haj (by omega)
    have hi := ih hprior
    have hn := habove n han (by omega)
    have hnext := habove (n + 1) (by omega) (le_refl _)
    have hc := coord_L_succ w n
    by_cases h0 : w n = 0
    · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hc
      change L w (n + 1) = L w n - 1 at hc
      have hlen := kmswStage_UL_length w n
      have hmin := runningMin_le (L w) n a han
      change minL w n ≤ L w a at hmin
      have hlen2 : 2 ≤ (kmswStage w n).UL.length := by omega
      rw [westStack_left w n h0 hlen2]
      have hidx : (L w n - L w a).toNat = (L w (n + 1) - L w a).toNat + 1 := by
        omega
      rw [hidx] at hi
      simpa only [List.drop_tail] using hi
    · by_cases h1 : w n = 1
      · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hc
        dsimp at hc
        rw [add_zero] at hc
        rw [westStack_up w n h1, hc]
        exact hi
      · have h2 : w n = 2 := by
          apply Fin.ext
          have := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
          have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
          omega
        rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hc
        dsimp at hc
        have hidx : (L w (n + 1) - L w a).toNat = (L w n - L w a).toNat + 1 := by
          omega
        rw [hidx, ← List.drop_tail, westStack_down w n h2]
        exact hi

/-- The initial vertex persists along a weak horizontal excursion returning
to its initial level (`lem-kmsw-bdy`(iii), -/
theorem kmsw_west_act_eq_of_level (w : ℕ → Fin 3) {m' m : ℕ}
    (hm : m' ≤ m) (hlev : L w m' = L w m)
    (habove : ∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) :
    (kmswStage w m).west (act w m') = (kmswStage w m).west (act w m) := by
  have hs := westStack_excursion w hm habove
  rw [← hlev] at hs
  simp only [sub_self, Int.toNat_zero, List.drop_zero] at hs
  obtain ⟨es, hes⟩ := kmswStage_UL_last w m
  obtain ⟨es', hes'⟩ := kmswStage_UL_last w m'
  have hh := congrArg List.head? hs
  simp only [westStack, hes, hes', List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, List.map_cons,
    List.head?_cons, Option.some.injEq] at hh
  have hstable := (kmswStage_endpoints_stable w hm (act_lt_nextEdge w (le_refl m'))).1
  exact hstable.trans hh.symm

end DirectedDistances.KMSW
