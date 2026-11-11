module

public import DirectedDistances.KMSW.StageReversalPhi
public import DirectedDistances.KMSW.StageIncidenceChains

public section
namespace DirectedDistances.KMSW

open scoped Classical




theorem kmswStage_reverse_nextEdge (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    (kmswStage wr n).nextEdge = (kmswStage w n).nextEdge := by
  rw [CutConverse.allocation_count, CutConverse.allocation_count,
    kmswStage_reverse_UR_length wr w n hrev, kmswStage_reverse_LL_length wr w n hrev]
  omega




theorem kmswStage_present_unique_active (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) (hp : (kmswStage w n).present e = true) :
    ∃! t, t ≤ n ∧ (kmswStage w t).active = e := by
  obtain ⟨t, ht, heq⟩ := kmswStage_present_eq_active w n e he hp
  refine ⟨t, ⟨ht, heq⟩, ?_⟩
  intro s hs
  exact kmswStage_active_injOn w n s t hs.1 ht (hs.2.trans heq.symm)




theorem kmswStage_missing_iff_UR_or_LL (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    (kmswStage w n).present e = false ↔
      e ∈ (kmswStage w n).UR ∨ e ∈ (kmswStage w n).LL :=
  (kmswStage_status w n).1 e he




theorem kmswStage_UR_LL_not_present (w : ℕ → Fin 3) (n e : ℕ)
    (hm : e ∈ (kmswStage w n).UR ∨ e ∈ (kmswStage w n).LL) :
    (kmswStage w n).present e ≠ true := by
  have he : e < (kmswStage w n).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [List.mem_append]
    tauto
  have hf := (kmswStage_missing_iff_UR_or_LL w n e he).mpr hm
  rw [hf]
  decide




def kmswRevUpRecord (w : ℕ → Fin 3) (n e s : ℕ) : Prop :=
  s < n ∧ w s = 1 ∧ (∀ j, s < j → j ≤ n → R w s < R w j) ∧
    e = (kmswStage w s).nextEdge + 1




def kmswRevLeftRecord (w : ℕ → Fin 3) (n e s : ℕ) : Prop :=
  s < n ∧ w s = 0 ∧ L w s = minL w s ∧
    e = (kmswStage w s).nextEdge + 1




theorem kmswStage_UR_exists_revUpRecord (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UR) : ∃ s, kmswRevUpRecord w n e s := by
  rw [kmswStage_UR_eq] at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  simp only [List.mem_reverse, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at hm
  obtain ⟨_, hmpos, hmn, hfuture⟩ := hm
  let s := m - 1
  have hms : m = s + 1 := by dsimp [s]; omega
  have hsn : s < n := by omega
  have hstep : R w (s + 1) = R w s +
      (RandomWalk.lazyTwoDimensionalStep (w s)).2 := Finset.sum_range_succ _ _
  have hnext := hfuture m le_rfl hmn
  rw [hms] at hnext
  change R w s + 1 ≤ R w (s + 1) at hnext
  have hc : w s = 1 := by
    have hv := (w s).isLt
    have hcases : w s = 0 ∨ w s = 1 ∨ w s = 2 := by
      have h : (w s).val = 0 ∨ (w s).val = 1 ∨ (w s).val = 2 := by omega
      rcases h with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases hcases with h | h | h
    · simp [h, RandomWalk.lazyTwoDimensionalStep] at hstep
      omega
    · exact h
    · simp [h, RandomWalk.lazyTwoDimensionalStep] at hstep
      omega
  refine ⟨s, hsn, hc, ?_, ?_⟩
  · intro j hj hjn
    have := hfuture j (by omega) hjn
    change R w s + 1 ≤ R w j at this
    omega
  · rw [hms]
    simp [kmswURCreatedEdge, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, State.addEdge]




theorem kmswStage_LL_exists_revLeftRecord (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).LL) : ∃ s, kmswRevLeftRecord w n e s := by
  rw [kmswStage_LL_eq_unmatchedLefts] at he
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
  simp only [List.mem_reverse, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at hs
  exact ⟨s, hs.1, hs.2.1, hs.2.2, rfl⟩




noncomputable def kmswRevEdge (w wr : ℕ → Fin 3) (n e : ℕ) : ℕ :=
  if h : ∃ s, s ≤ n ∧ (kmswStage wr s).active = e then
    (kmswStage w (n - Classical.choose h)).active
  else if h : ∃ s, kmswRevUpRecord wr n e s then
    (kmswStage w (n - 1 - Classical.choose h)).nextEdge + 1
  else if h : ∃ s, kmswRevLeftRecord wr n e s then
    (kmswStage w (n - 1 - Classical.choose h)).nextEdge + 1
  else e




theorem kmswRevEdge_active (w wr : ℕ → Fin 3) (n s : ℕ) (hs : s ≤ n) :
    kmswRevEdge w wr n (kmswStage wr s).active = (kmswStage w (n - s)).active := by
  have h : ∃ t, t ≤ n ∧ (kmswStage wr t).active = (kmswStage wr s).active :=
    ⟨s, hs, rfl⟩
  have ht : Classical.choose h = s :=
    kmswStage_active_injOn wr n _ s (Classical.choose_spec h).1 hs
      (Classical.choose_spec h).2
  rw [kmswRevEdge, dite_eq_left h, ht]




theorem kmswRevEdge_present_endpoints (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (e : ℕ) (he : e < (kmswStage wr n).nextEdge)
    (hp : (kmswStage wr n).present e = true) :
    (kmswStage w n).west (kmswRevEdge w wr n e) =
        kmswReversalPhi wr w n ((kmswStage wr n).east e) ∧
      (kmswStage w n).east (kmswRevEdge w wr n e) =
        kmswReversalPhi wr w n ((kmswStage wr n).west e) := by
  obtain ⟨s, hs, rfl⟩ := kmswStage_present_eq_active wr n e he hp
  rw [kmswRevEdge_active w wr n s hs]
  have hw := kmswStage_endpoints_stable w (Nat.sub_le n s)
    (kmswStage_active_lt w (n - s))
  have hr := kmswStage_endpoints_stable wr hs (kmswStage_active_lt wr s)
  constructor
  · rw [hw.1, hr.2]
    exact (kmswReversalPhi_slot wr w n hrev (.east s) hs).symm
  · rw [hw.2, hr.1]
    exact (kmswReversalPhi_slot wr w n hrev (.west s) hs).symm




theorem kmswRevEdge_up_slots (w : ℕ → Fin 3) (n s : ℕ) (hs : s < n)
    (hc : w s = 1) :
    (kmswStage w n).west ((kmswStage w s).nextEdge + 1) =
        kmswSlotVertex w (.east (s + 1)) ∧
      (kmswStage w n).east ((kmswStage w s).nextEdge + 1) =
        kmswSlotVertex w (.east s) := by
  have hm := kmswSlot_up_missing_endpoints w s hc
  have hstable := kmswStage_endpoints_stable w (by omega : s + 1 ≤ n) hm.2.2
  exact ⟨hstable.1.trans (hm.1.trans (kmswStage_up_active_endpoints w s hc).2.symm),
    hstable.2.trans hm.2.1⟩




theorem kmswRevEdge_left_slots (w : ℕ → Fin 3) (n s : ℕ) (hs : s < n)
    (hc : w s = 0) (hm : L w s = minL w s) :
    (kmswStage w n).west ((kmswStage w s).nextEdge + 1) =
        kmswSlotVertex w (.west (s + 1)) ∧
      (kmswStage w n).east ((kmswStage w s).nextEdge + 1) =
        kmswSlotVertex w (.west s) := by
  have hlen := kmswStage_UL_length w s
  have hnil : (kmswStage w s).UL.dropLast.reverse = [] := by
    apply List.length_eq_zero_iff.mp
    simp only [List.length_reverse, List.length_dropLast]
    omega
  have hnew : (kmswStage w s).nextEdge + 1 < (kmswStage w (s + 1)).nextEdge := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hnil, State.addEdge]
  have he : (kmswStage w (s + 1)).west ((kmswStage w s).nextEdge + 1) =
      kmswSlotVertex w (.west (s + 1)) ∧
      (kmswStage w (s + 1)).east ((kmswStage w s).nextEdge + 1) =
        kmswSlotVertex w (.west s) := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hnil,
      State.addEdge, kmswSlotVertex]
  have hstable := kmswStage_endpoints_stable w (by omega : s + 1 ≤ n) hnew
  exact ⟨hstable.1.trans he.1, hstable.2.trans he.2⟩




theorem kmswRevEdge_up_record_endpoints (wr w : ℕ → Fin 3) (n e s : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (hs : kmswRevUpRecord wr n e s) :
    (kmswStage w n).west ((kmswStage w (n - 1 - s)).nextEdge + 1) =
        kmswReversalPhi wr w n ((kmswStage wr n).east e) ∧
      (kmswStage w n).east ((kmswStage w (n - 1 - s)).nextEdge + 1) =
        kmswReversalPhi wr w n ((kmswStage wr n).west e) := by
  obtain ⟨hsn, hc, hf, rfl⟩ := hs
  have hrec := (kmswURRecord_reverse_iff w wr n
    (kmswReversal_letters_symm wr w n hrev) hsn).mp ⟨hc, hf⟩
  let q := n - 1 - s
  have hqn : q < n := by dsimp [q]; omega
  change w q = 0 ∧ ∀ j, j ≤ q → L w q ≤ L w j at hrec
  have hm : L w q = minL w q := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) q
    have := hrec.2 j hj
    have := runningMin_le (L w) q q le_rfl
    change L w q = runningMin (L w) q
    omega
  have hr := kmswRevEdge_up_slots wr n s hsn hc
  have hw := kmswRevEdge_left_slots w n q hqn hrec.1 hm
  have hi : n - (s + 1) = q := by dsimp [q]; omega
  have hi' : n - s = q + 1 := by dsimp [q]; omega
  constructor
  · rw [hr.2, kmswReversalPhi_slot wr w n hrev (.east s) (by
      change s ≤ n; omega)]
    simpa only [KMSWSlot.mirror, hi'] using hw.1
  · rw [hr.1, kmswReversalPhi_slot wr w n hrev (.east (s + 1)) (by
      change s + 1 ≤ n; omega)]
    simpa only [KMSWSlot.mirror, hi] using hw.2




theorem kmswRevEdge_left_record_endpoints (wr w : ℕ → Fin 3) (n e s : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (hs : kmswRevLeftRecord wr n e s) :
    (kmswStage w n).west ((kmswStage w (n - 1 - s)).nextEdge + 1) =
        kmswReversalPhi wr w n ((kmswStage wr n).east e) ∧
      (kmswStage w n).east ((kmswStage w (n - 1 - s)).nextEdge + 1) =
        kmswReversalPhi wr w n ((kmswStage wr n).west e) := by
  obtain ⟨hsn, hc, hm, rfl⟩ := hs
  have hpast : ∀ j, j ≤ s → L wr s ≤ L wr j := by
    intro j hj
    rw [hm]
    exact runningMin_le (L wr) s j hj
  have hrec := (kmswLLRecord_reverse_iff w wr n
    (kmswReversal_letters_symm wr w n hrev) hsn).mp ⟨hc, hpast⟩
  let q := n - 1 - s
  have hqn : q < n := by dsimp [q]; omega
  have hr := kmswRevEdge_left_slots wr n s hsn hc hm
  have hw := kmswRevEdge_up_slots w n q hqn hrec.1
  have hi : n - (s + 1) = q := by dsimp [q]; omega
  have hi' : n - s = q + 1 := by dsimp [q]; omega
  constructor
  · rw [hr.2, kmswReversalPhi_slot wr w n hrev (.west s) (by
      change s ≤ n; omega)]
    simpa only [KMSWSlot.mirror, hi'] using hw.1
  · rw [hr.1, kmswReversalPhi_slot wr w n hrev (.west (s + 1)) (by
      change s + 1 ≤ n; omega)]
    simpa only [KMSWSlot.mirror, hi] using hw.2




theorem kmswRevEdge_endpoints (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (e : ℕ) (he : e < (kmswStage wr n).nextEdge) :
    (kmswStage w n).west (kmswRevEdge w wr n e) =
        kmswReversalPhi wr w n ((kmswStage wr n).east e) ∧
      (kmswStage w n).east (kmswRevEdge w wr n e) =
        kmswReversalPhi wr w n ((kmswStage wr n).west e) := by
  by_cases hp : (kmswStage wr n).present e = true
  · exact kmswRevEdge_present_endpoints wr w n hrev e he hp
  have ha : ¬ ∃ s, s ≤ n ∧ (kmswStage wr s).active = e := by
    rintro ⟨s, hs, rfl⟩
    exact hp (kmswStage_active_present_mono wr hs)
  rw [kmswRevEdge, dite_eq_right ha]
  split
  · rename_i hu
    exact kmswRevEdge_up_record_endpoints wr w n e _ hrev (Classical.choose_spec hu)
  · rename_i hu
    split
    · rename_i hl
      exact kmswRevEdge_left_record_endpoints wr w n e _ hrev (Classical.choose_spec hl)
    · rename_i hl
      have hf : (kmswStage wr n).present e = false := by
        cases h : (kmswStage wr n).present e <;> simp_all
      rcases (kmswStage_missing_iff_UR_or_LL wr n e he).mp hf with h | h
      · exact (hu (kmswStage_UR_exists_revUpRecord wr n e h)).elim
      · exact (hl (kmswStage_LL_exists_revLeftRecord wr n e h)).elim




theorem kmswRevUpRecord_mem_UR (w : ℕ → Fin 3) (n e s : ℕ)
    (hs : kmswRevUpRecord w n e s) : e ∈ (kmswStage w n).UR := by
  obtain ⟨hsn, hc, hf, rfl⟩ := hs
  rw [kmswStage_UR_eq]
  apply List.mem_map.mpr
  refine ⟨s + 1, ?_, ?_⟩
  · simp only [List.mem_reverse, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro j hj hjn
    have := hf j (by omega) hjn
    simpa only [Nat.add_sub_cancel] using (show R w s + 1 ≤ R w j by omega)
  · simp [kmswURCreatedEdge, kmswStage, kmswStep, kmswCodeStep, hc,
      kmswStepOfStep, State.addEdge]




theorem kmswRevLeftRecord_mem_LL (w : ℕ → Fin 3) (n e s : ℕ)
    (hs : kmswRevLeftRecord w n e s) : e ∈ (kmswStage w n).LL := by
  obtain ⟨hsn, hc, hm, rfl⟩ := hs
  rw [kmswStage_LL_eq_unmatchedLefts]
  apply List.mem_map.mpr
  refine ⟨s, ?_, rfl⟩
  simp only [List.mem_reverse, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨hsn, hc, hm⟩




theorem kmswRevRecord_allocated (w : ℕ → Fin 3) (n e s : ℕ)
    (hs : kmswRevUpRecord w n e s ∨ kmswRevLeftRecord w n e s) :
    e = (kmswStage w s).nextEdge + 1 ∧ e < (kmswStage w (s + 1)).nextEdge := by
  rcases hs with ⟨_, hc, _, rfl⟩ | ⟨_, hc, hm, rfl⟩
  · exact ⟨rfl, (kmswSlot_up_missing_endpoints w s hc).2.2⟩
  · have hlen := kmswStage_UL_length w s
    have hnil : (kmswStage w s).UL.dropLast.reverse = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_reverse, List.length_dropLast]
      omega
    refine ⟨rfl, ?_⟩
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hnil, State.addEdge]




theorem kmswRevRecord_time_unique (w : ℕ → Fin 3) (n e s t : ℕ)
    (hs : kmswRevUpRecord w n e s ∨ kmswRevLeftRecord w n e s)
    (ht : kmswRevUpRecord w n e t ∨ kmswRevLeftRecord w n e t) : s = t := by
  have hs' := kmswRevRecord_allocated w n e s hs
  have ht' := kmswRevRecord_allocated w n e t ht
  rcases lt_trichotomy s t with h | h | h
  · have := kmswStage_nextEdge_mono w (show s + 1 ≤ t by omega)
    omega
  · exact h
  · have := kmswStage_nextEdge_mono w (show t + 1 ≤ s by omega)
    omega




theorem kmswRevEdge_up (w wr : ℕ → Fin 3) (n e s : ℕ)
    (hs : kmswRevUpRecord wr n e s) :
    kmswRevEdge w wr n e = (kmswStage w (n - 1 - s)).nextEdge + 1 := by
  have hm := kmswRevUpRecord_mem_UR wr n e s hs
  have hp := kmswStage_UR_LL_not_present wr n e (Or.inl hm)
  have ha : ¬ ∃ t, t ≤ n ∧ (kmswStage wr t).active = e := by
    rintro ⟨t, ht, rfl⟩
    exact hp (kmswStage_active_present_mono wr ht)
  have hu : ∃ t, kmswRevUpRecord wr n e t := ⟨s, hs⟩
  have ht := kmswRevRecord_time_unique wr n e (Classical.choose hu) s
    (Or.inl (Classical.choose_spec hu)) (Or.inl hs)
  rw [kmswRevEdge, dite_eq_right ha, dite_eq_left hu, ht]




theorem kmswRevEdge_left (w wr : ℕ → Fin 3) (n e s : ℕ)
    (hs : kmswRevLeftRecord wr n e s) :
    kmswRevEdge w wr n e = (kmswStage w (n - 1 - s)).nextEdge + 1 := by
  have hm := kmswRevLeftRecord_mem_LL wr n e s hs
  have hp := kmswStage_UR_LL_not_present wr n e (Or.inr hm)
  have ha : ¬ ∃ t, t ≤ n ∧ (kmswStage wr t).active = e := by
    rintro ⟨t, ht, rfl⟩
    exact hp (kmswStage_active_present_mono wr ht)
  have hu : ¬ ∃ t, kmswRevUpRecord wr n e t := by
    rintro ⟨t, ht⟩
    exact (kmswStage_status wr n).2.2.2.2.2 e
      (kmswRevUpRecord_mem_UR wr n e t ht) hm
  have hl : ∃ t, kmswRevLeftRecord wr n e t := ⟨s, hs⟩
  have ht := kmswRevRecord_time_unique wr n e (Classical.choose hl) s
    (Or.inr (Classical.choose_spec hl)) (Or.inr hs)
  rw [kmswRevEdge, dite_eq_right ha, dite_eq_right hu, dite_eq_left hl, ht]




theorem kmswRevUpRecord_reverse (wr w : ℕ → Fin 3) (n e s : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (hs : kmswRevUpRecord wr n e s) :
    kmswRevLeftRecord w n ((kmswStage w (n - 1 - s)).nextEdge + 1)
      (n - 1 - s) := by
  obtain ⟨hsn, hc, hf, _⟩ := hs
  have hrec := (kmswURRecord_reverse_iff w wr n
    (kmswReversal_letters_symm wr w n hrev) hsn).mp ⟨hc, hf⟩
  have hm : L w (n - 1 - s) = minL w (n - 1 - s) := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) (n - 1 - s)
    have := hrec.2 j hj
    have := runningMin_le (L w) (n - 1 - s) (n - 1 - s) le_rfl
    change L w (n - 1 - s) = runningMin (L w) (n - 1 - s)
    omega
  exact ⟨by omega, hrec.1, hm, rfl⟩




theorem kmswRevLeftRecord_reverse (wr w : ℕ → Fin 3) (n e s : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (hs : kmswRevLeftRecord wr n e s) :
    kmswRevUpRecord w n ((kmswStage w (n - 1 - s)).nextEdge + 1)
      (n - 1 - s) := by
  obtain ⟨hsn, hc, hm, _⟩ := hs
  have hpast : ∀ j, j ≤ s → L wr s ≤ L wr j := by
    intro j hj
    rw [hm]
    exact runningMin_le (L wr) s j hj
  have hrec := (kmswLLRecord_reverse_iff w wr n
    (kmswReversal_letters_symm wr w n hrev) hsn).mp ⟨hc, hpast⟩
  exact ⟨by omega, hrec.1, hrec.2, rfl⟩




theorem kmswRevEdge_mapsTo (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    Set.MapsTo (kmswRevEdge w wr n) (Set.Iio (kmswStage wr n).nextEdge)
      (Set.Iio (kmswStage w n).nextEdge) := by
  intro e he
  by_cases hp : (kmswStage wr n).present e = true
  · obtain ⟨s, hs, rfl⟩ := kmswStage_present_eq_active wr n e he hp
    rw [kmswRevEdge_active w wr n s hs]
    exact act_lt_nextEdge w (Nat.sub_le n s)
  · have hf : (kmswStage wr n).present e = false := by
      cases h : (kmswStage wr n).present e <;> simp_all
    rcases (kmswStage_missing_iff_UR_or_LL wr n e he).mp hf with hu | hl
    · obtain ⟨s, hs⟩ := kmswStage_UR_exists_revUpRecord wr n e hu
      rw [kmswRevEdge_up w wr n e s hs]
      have hm := kmswRevLeftRecord_mem_LL w n _ _ (kmswRevUpRecord_reverse wr w n e s
        hrev hs)
      exact (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
        simp only [List.mem_append]; tauto)
    · obtain ⟨s, hs⟩ := kmswStage_LL_exists_revLeftRecord wr n e hl
      rw [kmswRevEdge_left w wr n e s hs]
      have hm := kmswRevUpRecord_mem_UR w n _ _ (kmswRevLeftRecord_reverse wr w n e s
        hrev hs)
      exact (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
        simp only [List.mem_append]; tauto)




theorem kmswRevEdge_inverse (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (e : ℕ) (he : e < (kmswStage wr n).nextEdge) :
    kmswRevEdge wr w n (kmswRevEdge w wr n e) = e := by
  by_cases hp : (kmswStage wr n).present e = true
  · obtain ⟨s, hs, rfl⟩ := kmswStage_present_eq_active wr n e he hp
    rw [kmswRevEdge_active w wr n s hs,
      kmswRevEdge_active wr w n (n - s) (Nat.sub_le n s), Nat.sub_sub_self hs]
  · have hf : (kmswStage wr n).present e = false := by
      cases h : (kmswStage wr n).present e <;> simp_all
    rcases (kmswStage_missing_iff_UR_or_LL wr n e he).mp hf with hu | hl
    · obtain ⟨s, hs⟩ := kmswStage_UR_exists_revUpRecord wr n e hu
      rw [kmswRevEdge_up w wr n e s hs,
        kmswRevEdge_left wr w n _ _ (kmswRevUpRecord_reverse wr w n e s hrev hs)]
      have hidx : n - 1 - (n - 1 - s) = s := by have := hs.1; omega
      rw [hidx]
      exact hs.2.2.2.symm
    · obtain ⟨s, hs⟩ := kmswStage_LL_exists_revLeftRecord wr n e hl
      rw [kmswRevEdge_left w wr n e s hs,
        kmswRevEdge_up wr w n _ _ (kmswRevLeftRecord_reverse wr w n e s hrev hs)]
      have hidx : n - 1 - (n - 1 - s) = s := by have := hs.1; omega
      rw [hidx]
      exact hs.2.2.2.symm




theorem kmswRevEdge_bijOn (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    Set.BijOn (kmswRevEdge w wr n) (Set.Iio (kmswStage wr n).nextEdge)
      (Set.Iio (kmswStage w n).nextEdge) := by
  refine ⟨kmswRevEdge_mapsTo wr w n hrev, ?_, ?_⟩
  · intro e he f hf hef
    have hh := congrArg (kmswRevEdge wr w n) hef
    rwa [kmswRevEdge_inverse wr w n hrev e he,
      kmswRevEdge_inverse wr w n hrev f hf] at hh
  · intro e he
    have hr := kmswReversal_letters_symm wr w n hrev
    exact ⟨kmswRevEdge wr w n e, kmswRevEdge_mapsTo w wr n hr he,
      kmswRevEdge_inverse w wr n hr e he⟩




theorem kmswRevEdge_present_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (e : ℕ) (he : e < (kmswStage wr n).nextEdge) :
    (kmswStage w n).present (kmswRevEdge w wr n e) = true ↔
      (kmswStage wr n).present e = true := by
  have forward (a b : ℕ → Fin 3) (f : ℕ) (hf : f < (kmswStage a n).nextEdge)
      (hp : (kmswStage a n).present f = true) :
      (kmswStage b n).present (kmswRevEdge b a n f) = true := by
    obtain ⟨s, hs, rfl⟩ := kmswStage_present_eq_active a n f hf hp
    rw [kmswRevEdge_active b a n s hs]
    exact kmswStage_active_present_mono b (Nat.sub_le n s)
  constructor
  · intro hp
    have hh := forward w wr _ (kmswRevEdge_mapsTo wr w n hrev he) hp
    rwa [kmswRevEdge_inverse wr w n hrev e he] at hh
  · exact forward wr w e he




private theorem kmswRevEdge_UL_LR (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {s : ℕ} (hs : s ≤ n)
    (hf : ∀ j, s < j → j ≤ n → L wr s + 1 ≤ L wr j) :
    (kmswStage w (n - s)).active ∈ (kmswStage w n).LR := by
  by_cases hterminal : s = n
  · subst s
    rw [Nat.sub_self, kmswStage_LR_eq_unmatchedDowns]
    exact List.mem_cons_self
  have ht : s < n := by omega
  have hnext := hf (s + 1) (by omega) (by omega)
  have hstep := kmswL_succ wr s
  have hc : wr s = 2 := by
    have hcodes : wr s = 0 ∨ wr s = 1 ∨ wr s = 2 := by
      have hv := (wr s).isLt
      have h : (wr s).val = 0 ∨ (wr s).val = 1 ∨ (wr s).val = 2 := by omega
      rcases h with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases hcodes with hc | hc | hc
    · simp [hc] at hstep; omega
    · simp [hc] at hstep; omega
    · exact hc
  have hrec : s = n ∨ (wr s = 2 ∧
      ∀ j, s < j → j ≤ n → L wr s < L wr j) :=
    Or.inr ⟨hc, fun j hj hjn => by have := hf j hj hjn; omega⟩
  have hr := (kmswLRRecord_reverse_iff wr w n hrev hs).mp hrec
  rcases hr with he | ⟨hcode, hpast⟩
  · exact (hterminal he).elim
  · have hmin : R w (n - s - 1) = minR w (n - s - 1) := by
      obtain ⟨j, hj, he⟩ := runningMin_attained (R w) (n - s - 1)
      have := hpast j hj
      have := runningMin_le (R w) (n - s - 1) (n - s - 1) le_rfl
      change R w (n - s - 1) = runningMin (R w) (n - s - 1)
      omega
    rw [kmswStage_LR_eq_unmatchedDowns]
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨n - s - 1, ?_, ?_⟩
    · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, hcode, hmin⟩
    · rw [show n - s - 1 + 1 = n - s by omega]




theorem kmswRevEdge_upper_mem (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (e : ℕ) (he : e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR) :
    kmswRevEdge w wr n e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR := by
  rcases List.mem_append.mp he with hu | hu
  · rw [kmswStage_UL_eq] at hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hs
    have hsn : s ≤ n := by omega
    change kmswRevEdge w wr n (kmswStage wr s).active ∈ _
    rw [kmswRevEdge_active w wr n s hsn]
    exact List.mem_append_right _ (kmswRevEdge_UL_LR wr w n hrev hsn hs.2)
  · obtain ⟨s, hs⟩ := kmswStage_UR_exists_revUpRecord wr n e hu
    rw [kmswRevEdge_up w wr n e s hs]
    exact List.mem_append_left _ (kmswRevLeftRecord_mem_LL w n _ _
      (kmswRevUpRecord_reverse wr w n e s hrev hs))




private theorem kmswRevEdge_chain_eq (w : ℕ → Fin 3) (n : ℕ) (es fs : List ℕ)
    (hes : ∀ e ∈ es, e < (kmswStage w n).nextEdge)
    (hfs : ∀ e ∈ fs, e < (kmswStage w n).nextEdge)
    (hce : WestEastChain (kmswStage w n) es)
    (hcf : WestEastChain (kmswStage w n) fs)
    (hsub : es ⊆ fs) (hlen : es.length = fs.length) : es = fs := by
  let r : ℕ → ℕ → Prop := fun a b =>
    kmswStageRank w n ((kmswStage w n).west a) <
      kmswStageRank w n ((kmswStage w n).west b)
  have : Trans r r r := ⟨fun h h' => lt_trans h h'⟩
  have pair (xs : List ℕ) (hb : ∀ e ∈ xs, e < (kmswStage w n).nextEdge)
      (hc : WestEastChain (kmswStage w n) xs) : xs.Pairwise r := by
    apply List.IsChain.pairwise
    apply hc.imp_of_mem_imp
    intro a b ha _ hab
    change kmswStageRank w n ((kmswStage w n).west a) <
      kmswStageRank w n ((kmswStage w n).west b)
    rw [← hab]
    exact kmswStageRank_strict w n a (hb a ha)
  have pe := pair es hes hce
  have pf := pair fs hfs hcf
  have : Std.Irrefl r := ⟨fun a => lt_irrefl _⟩
  have hp := (List.subperm_of_subset pe.nodup hsub).perm_of_length_le (by omega)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ h h' => (lt_asymm h h').elim) pe pf hp




theorem kmswRevEdge_upper_boundary (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ((kmswStage wr n).UL ++ (kmswStage wr n).UR).map (kmswRevEdge w wr n) =
      ((kmswStage w n).LL ++ (kmswStage w n).LR).reverse := by
  let us := (kmswStage wr n).UL ++ (kmswStage wr n).UR
  let ls := (kmswStage w n).LL ++ (kmswStage w n).LR
  have hub : ∀ e ∈ us, e < (kmswStage wr n).nextEdge := by
    intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge wr n).2
    dsimp [us] at he
    simp only [List.mem_append] at he ⊢
    tauto
  have hlb : ∀ e ∈ ls, e < (kmswStage w n).nextEdge := by
    intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    dsimp [ls] at he
    simp only [List.mem_append] at he ⊢
    tauto
  have hsub : (us.map (kmswRevEdge w wr n)).reverse ⊆ ls := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    exact kmswRevEdge_upper_mem wr w n hrev f hf
  have hc : WestEastChain (kmswStage w n) (us.map (kmswRevEdge w wr n)).reverse := by
    apply List.isChain_reverse.mpr
    apply (List.isChain_map _).mpr
    apply (kmswStage_boundary_chain_invariant wr n).1.imp_of_mem_imp
    intro a b ha hb hab
    have hea := kmswRevEdge_endpoints wr w n hrev a (hub a ha)
    have heb := kmswRevEdge_endpoints wr w n hrev b (hub b hb)
    rw [hea.1, heb.2, hab]
  have hlen : (us.map (kmswRevEdge w wr n)).reverse.length = ls.length := by
    dsimp [us, ls]
    simp only [List.length_reverse, List.length_map, List.length_append]
    rw [kmswStage_reverse_UL_length wr w n hrev,
      kmswStage_reverse_UR_length wr w n hrev]
    omega
  have hh := kmswRevEdge_chain_eq w n _ ls (fun e he => hlb e (hsub he)) hlb hc
    (kmswStage_boundary_chain_invariant w n).2.1 hsub hlen
  apply List.reverse_inj.mp
  simpa only [List.reverse_reverse] using hh




theorem kmswRevEdge_lower_boundary (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ((kmswStage wr n).LL ++ (kmswStage wr n).LR).map (kmswRevEdge w wr n) =
      ((kmswStage w n).UL ++ (kmswStage w n).UR).reverse := by
  have hr := kmswReversal_letters_symm wr w n hrev
  have h := congrArg (List.map (kmswRevEdge w wr n))
    (kmswRevEdge_upper_boundary w wr n hr)
  have hinv :
      (((kmswStage w n).UL ++ (kmswStage w n).UR).map (kmswRevEdge wr w n)).map
        (kmswRevEdge w wr n) = (kmswStage w n).UL ++ (kmswStage w n).UR := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id ((kmswStage w n).UL ++ (kmswStage w n).UR)]
    apply List.map_congr_left
    intro e he
    apply kmswRevEdge_inverse w wr n hr
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [List.mem_append] at he ⊢
    tauto
  rw [hinv, List.map_reverse] at h
  have hh := congrArg List.reverse h
  simpa only [List.reverse_reverse] using hh.symm




theorem kmswStage_edge_classification (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    ((kmswStage w n).present e = true ∧
      ∃! t, t ≤ n ∧ (kmswStage w t).active = e) ∨
    ((kmswStage w n).present e = false ∧
      (e ∈ (kmswStage w n).UR ∨ e ∈ (kmswStage w n).LL)) := by
  cases hp : (kmswStage w n).present e with
  | false => exact Or.inr ⟨rfl, (kmswStage_missing_iff_UR_or_LL w n e he).mp hp⟩
  | true => exact Or.inl ⟨rfl, kmswStage_present_unique_active w n e he hp⟩




theorem kmswRevEdge_spec (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    (kmswStage wr n).nextEdge = (kmswStage w n).nextEdge ∧
    Set.BijOn (kmswRevEdge w wr n) (Set.Iio (kmswStage wr n).nextEdge)
      (Set.Iio (kmswStage w n).nextEdge) ∧
    (∀ e < (kmswStage wr n).nextEdge,
      (kmswStage w n).present (kmswRevEdge w wr n e) = true ↔
        (kmswStage wr n).present e = true) ∧
    (∀ s ≤ n, kmswRevEdge w wr n (kmswStage wr s).active =
      (kmswStage w (n - s)).active) ∧
    (∀ e < (kmswStage wr n).nextEdge,
      (kmswStage w n).west (kmswRevEdge w wr n e) =
          kmswReversalPhi wr w n ((kmswStage wr n).east e) ∧
        (kmswStage w n).east (kmswRevEdge w wr n e) =
          kmswReversalPhi wr w n ((kmswStage wr n).west e)) ∧
    ((kmswStage wr n).LL ++ (kmswStage wr n).LR).map (kmswRevEdge w wr n) =
      ((kmswStage w n).UL ++ (kmswStage w n).UR).reverse ∧
    ((kmswStage wr n).UL ++ (kmswStage wr n).UR).map (kmswRevEdge w wr n) =
      ((kmswStage w n).LL ++ (kmswStage w n).LR).reverse :=
  ⟨kmswStage_reverse_nextEdge wr w n hrev, kmswRevEdge_bijOn wr w n hrev,
    kmswRevEdge_present_iff wr w n hrev, kmswRevEdge_active w wr n,
    kmswRevEdge_endpoints wr w n hrev, kmswRevEdge_lower_boundary wr w n hrev,
    kmswRevEdge_upper_boundary wr w n hrev⟩

end DirectedDistances.KMSW
