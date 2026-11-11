module

public import DirectedDistances.KMSW.StageSlotForest
public import DirectedDistances.KMSW.StageReversalPairs

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW

open scoped Classical



@[expose] def KMSWSlot.mirror (n : ℕ) : KMSWSlot → KMSWSlot
  | .west s => .east (n - s)
  | .east s => .west (n - s)



theorem KMSWSlot.time_mirror (n : ℕ) (S : KMSWSlot) :
    (S.mirror n).time = n - S.time := by
  cases S <;> rfl



theorem KMSWSlot.mirror_mirror (n : ℕ) (S : KMSWSlot) (hS : S.time ≤ n) :
    (S.mirror n).mirror n = S := by
  cases S <;> simp only [mirror, time] at * <;> congr 1 <;> omega



theorem kmswReversal_letters_symm (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ∀ i < n, w i = Equiv.swap (0 : Fin 3) 1 (wr (n - 1 - i)) := by
  intro i hi
  rw [hrev (n - 1 - i) (by omega), show n - 1 - (n - 1 - i) = i by omega]
  simp only [Equiv.swap_apply_self]



theorem kmswSlotLink_mirror (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {S T : KMSWSlot} (hS : S.time ≤ n) (hlink : kmswSlotLink wr S T) :
    kmswSlotLink w (T.mirror n) (S.mirror n) := by
  have letter (t : ℕ) (ht : t < n) :
      w (n - 1 - t) = Equiv.swap (0 : Fin 3) 1 (wr t) := by
    rw [hrev t ht]
    simp only [Equiv.swap_apply_self]
  cases S with
  | west t =>
    cases t with
    | zero => exact hlink.elim
    | succ t =>
      change t + 1 ≤ n at hS
      have ha : n - (t + 1) = n - 1 - t := by omega
      have hb : n - t = (n - 1 - t) + 1 := by omega
      rcases hlink with ⟨hc, rfl⟩ | ⟨hc, rfl⟩ | ⟨_, r, hp, rfl⟩
      · simp only [KMSWSlot.mirror, ha, hb, kmswSlotLink]
        exact Or.inl ⟨by simpa [hc, Equiv.swap_apply_def] using letter t (by omega),
          True.intro⟩
      · simp only [KMSWSlot.mirror, ha, hb, kmswSlotLink]
        exact Or.inr (Or.inl
          ⟨by simpa [hc, Equiv.swap_apply_def] using letter t (by omega), True.intro⟩)
      · have hp' : kmswRpair w (n - 1 - t) (n - 1 - r) :=
          (kmswLpairBody_reverse_iff wr w n hrev (by omega)).mp hp
        have hr : n - r = (n - 1 - r) + 1 := by have := hp.1; omega
        simp only [KMSWSlot.mirror, ha, hr, kmswSlotLink]
        exact Or.inr ⟨(kmswRpair_codes w hp').2, n - 1 - t, hp', rfl⟩
  | east t =>
    cases t with
    | zero => exact hlink.elim
    | succ t =>
      change t + 1 ≤ n at hS
      have ha : n - (t + 1) = n - 1 - t := by omega
      have hb : n - t = (n - 1 - t) + 1 := by omega
      rcases hlink with ⟨hc, rfl⟩ | ⟨_, s, hp, rfl⟩
      · simp only [KMSWSlot.mirror, ha, hb, kmswSlotLink]
        exact Or.inl ⟨by simpa [hc, Equiv.swap_apply_def] using letter t (by omega),
          True.intro⟩
      · have hp' : kmswLpair w (n - 1 - t) (n - 1 - s) :=
          (kmswRpairBody_reverse_iff wr w n hrev (by omega)).mp hp
        have hs : n - s = (n - 1 - s) + 1 := by have := hp.1; omega
        simp only [KMSWSlot.mirror, ha, hs, kmswSlotLink]
        exact Or.inr (Or.inr
          ⟨(kmswLpair_codes w hp').2, n - 1 - t, hp', rfl⟩)



theorem kmswSlotLink_mirror_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {S T : KMSWSlot} (hS : S.time ≤ n) (hT : T.time ≤ n) :
    kmswSlotLink wr S T ↔ kmswSlotLink w (T.mirror n) (S.mirror n) := by
  constructor
  · exact kmswSlotLink_mirror wr w n hrev hS
  · intro h
    have hh := kmswSlotLink_mirror w wr n (kmswReversal_letters_symm wr w n hrev)
      (S := T.mirror n) (by rw [KMSWSlot.time_mirror]; omega) h
    simpa only [KMSWSlot.mirror_mirror n S hS, KMSWSlot.mirror_mirror n T hT] using hh



private theorem mirror_vertex_eq (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {S T : KMSWSlot} (hS : S.time ≤ n) (hT : T.time ≤ n)
    (hv : kmswSlotVertex wr S = kmswSlotVertex wr T) :
    kmswSlotVertex w (S.mirror n) = kmswSlotVertex w (T.mirror n) := by
  have hconn := (kmswSlotVertex_eq_iff wr n S T hS hT).mp hv
  clear hv hS hT
  induction hconn with
  | rel A B h =>
    exact (kmswSlotLink_vertex w (kmswSlotLink_mirror wr w n hrev h.2.1 h.1)).symm
  | refl A => rfl
  | symm A B _ ih => exact ih.symm
  | trans A B C _ _ ih ih' => exact ih.trans ih'



theorem kmswSlotVertex_mirror_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {S T : KMSWSlot} (hS : S.time ≤ n) (hT : T.time ≤ n) :
    kmswSlotVertex wr S = kmswSlotVertex wr T ↔
      kmswSlotVertex w (S.mirror n) = kmswSlotVertex w (T.mirror n) := by
  constructor
  · exact mirror_vertex_eq wr w n hrev hS hT
  · intro h
    have hh := mirror_vertex_eq w wr n (kmswReversal_letters_symm wr w n hrev)
      (S := S.mirror n) (T := T.mirror n)
      (by rw [KMSWSlot.time_mirror]; omega) (by rw [KMSWSlot.time_mirror]; omega) h
    simpa only [KMSWSlot.mirror_mirror n S hS, KMSWSlot.mirror_mirror n T hT] using hh



@[expose] noncomputable def kmswReversalPhi (wr w : ℕ → Fin 3) (n v : ℕ) : ℕ :=
  if h : ∃ S, S.time ≤ n ∧ kmswSlotVertex wr S = v then
    kmswSlotVertex w ((Classical.choose h).mirror n)
  else v



theorem kmswReversalPhi_slot (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (S : KMSWSlot) (hS : S.time ≤ n) :
    kmswReversalPhi wr w n (kmswSlotVertex wr S) = kmswSlotVertex w (S.mirror n) := by
  have h : ∃ T, T.time ≤ n ∧ kmswSlotVertex wr T = kmswSlotVertex wr S :=
    ⟨S, hS, rfl⟩
  rw [kmswReversalPhi, dite_eq_left h]
  exact (kmswSlotVertex_mirror_iff wr w n hrev (Classical.choose_spec h).1 hS).mp
    (Classical.choose_spec h).2




theorem kmswReversalPhi_present (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ∀ e < (kmswStage wr n).nextEdge, (kmswStage wr n).present e = true →
      ∃ f < (kmswStage w n).nextEdge, (kmswStage w n).present f = true ∧
        (kmswStage w n).west f = kmswReversalPhi wr w n ((kmswStage wr n).east e) ∧
        (kmswStage w n).east f = kmswReversalPhi wr w n ((kmswStage wr n).west e) := by
  intro e he hp
  obtain ⟨s, hs, rfl⟩ := kmswStage_present_eq_active wr n e he hp
  have hs' : n - s ≤ n := Nat.sub_le _ _
  have hw := kmswStage_endpoints_stable w hs' (kmswStage_active_lt w (n - s))
  have hr := kmswStage_endpoints_stable wr hs (kmswStage_active_lt wr s)
  refine ⟨(kmswStage w (n - s)).active,
    (kmswStage_active_lt w (n - s)).trans_le (kmswStage_nextEdge_mono w hs'),
    kmswStage_active_present_mono w hs', ?_, ?_⟩
  · rw [hw.1, hr.2]
    exact (kmswReversalPhi_slot wr w n hrev (.east s) hs).symm
  · rw [hw.2, hr.1]
    exact (kmswReversalPhi_slot wr w n hrev (.west s) hs).symm



private theorem reversal_codes (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  have hv := c.isLt
  have h : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))




private theorem reversal_UL_LR (wr w : ℕ → Fin 3) (n : ℕ)
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
    rcases reversal_codes (wr s) with hc | hc | hc
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




private theorem reversal_up_slots (w : ℕ → Fin 3) (n s : ℕ) (hs : s < n)
    (hc : w s = 1) :
    (kmswStage w n).west ((kmswStage w s).nextEdge + 1) =
        kmswSlotVertex w (.east (s + 1)) ∧
      (kmswStage w n).east ((kmswStage w s).nextEdge + 1) =
        kmswSlotVertex w (.east s) := by
  have hm := kmswSlot_up_missing_endpoints w s hc
  have hstable := kmswStage_endpoints_stable w (by omega : s + 1 ≤ n) hm.2.2
  exact ⟨hstable.1.trans (hm.1.trans (kmswStage_up_active_endpoints w s hc).2.symm),
    hstable.2.trans hm.2.1⟩




private theorem reversal_left_slots (w : ℕ → Fin 3) (n s : ℕ) (hs : s < n)
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




theorem kmswReversalPhi_upper (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ∀ x, (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
      (kmswStage wr n).west e = x ∨ (kmswStage wr n).east e = x) →
    ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
      (kmswStage w n).west e = kmswReversalPhi wr w n x ∨
        (kmswStage w n).east e = kmswReversalPhi wr w n x := by
  rintro x ⟨e, he, hx⟩
  rcases List.mem_append.mp he with hu | hu
  · rw [kmswStage_UL_eq] at hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hs
    have hsn : s ≤ n := by omega
    have hmem := reversal_UL_LR wr w n hrev hsn hs.2
    have hr := kmswStage_endpoints_stable wr hsn (kmswStage_active_lt wr s)
    have hw := kmswStage_endpoints_stable w (Nat.sub_le n s)
      (kmswStage_active_lt w (n - s))
    change (kmswStage wr n).west (kmswStage wr s).active = x ∨
      (kmswStage wr n).east (kmswStage wr s).active = x at hx
    rw [hr.1, hr.2] at hx
    refine ⟨(kmswStage w (n - s)).active, List.mem_append_right _ hmem, ?_⟩
    rcases hx with hx | hx
    · right
      rw [← hx, hw.2]
      exact (kmswReversalPhi_slot wr w n hrev (.west s) hsn).symm
    · left
      rw [← hx, hw.1]
      exact (kmswReversalPhi_slot wr w n hrev (.east s) hsn).symm
  · rw [kmswStage_UR_eq] at hu
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hu
    simp only [List.mem_reverse, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hm
    obtain ⟨_, hmpos, hmn, hfuture⟩ := hm
    let s := m - 1
    have hms : m = s + 1 := by dsimp [s]; omega
    have hsn : s < n := by omega
    have hstep : R wr (s + 1) = R wr s +
        (RandomWalk.lazyTwoDimensionalStep (wr s)).2 := Finset.sum_range_succ _ _
    have hnext := hfuture m le_rfl hmn
    have hc : wr s = 1 := by
      rw [hms] at hnext
      change R wr s + 1 ≤ R wr (s + 1) at hnext
      rcases reversal_codes (wr s) with hc | hc | hc
      · simp [hc] at hstep; omega
      · exact hc
      · simp [hc] at hstep; omega
    have hrecord : wr s = 1 ∧ ∀ j, s < j → j ≤ n → R wr s < R wr j := by
      refine ⟨hc, fun j hj hjn => ?_⟩
      have := hfuture j (by omega) hjn
      change R wr s + 1 ≤ R wr j at this
      omega
    have hrec := (kmswURRecord_reverse_iff w wr n
      (kmswReversal_letters_symm wr w n hrev) hsn).mp hrecord
    let q := n - 1 - s
    have hqn : q < n := by dsimp [q]; omega
    change w q = 0 ∧ ∀ j, j ≤ q → L w q ≤ L w j at hrec
    have hmin : L w q = minL w q := by
      obtain ⟨j, hj, he⟩ := runningMin_attained (L w) q
      have := hrec.2 j hj
      have := runningMin_le (L w) q q le_rfl
      change L w q = runningMin (L w) q
      omega
    have hmem : (kmswStage w q).nextEdge + 1 ∈ (kmswStage w n).LL := by
      rw [kmswStage_LL_eq_unmatchedLefts]
      apply List.mem_map.mpr
      refine ⟨q, ?_, rfl⟩
      simp only [List.mem_reverse, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hqn, hrec.1, hmin⟩
    have he : kmswURCreatedEdge wr m = (kmswStage wr s).nextEdge + 1 := by
      rw [hms]
      simp [kmswURCreatedEdge, kmswStage, kmswStep, kmswCodeStep, hc,
        kmswStepOfStep, State.addEdge]
    rw [he] at hx
    have hr := reversal_up_slots wr n s hsn hc
    have hw := reversal_left_slots w n q hqn hrec.1 hmin
    rw [hr.1, hr.2] at hx
    have hi : n - (s + 1) = q := by dsimp [q]; omega
    have hi' : n - s = q + 1 := by dsimp [q]; omega
    refine ⟨(kmswStage w q).nextEdge + 1, List.mem_append_left _ hmem, ?_⟩
    rcases hx with hx | hx
    · right
      rw [← hx, hw.2, kmswReversalPhi_slot wr w n hrev (.east (s + 1)) (by
        change s + 1 ≤ n; omega)]
      simp only [KMSWSlot.mirror, hi]
    · left
      rw [← hx, hw.1, kmswReversalPhi_slot wr w n hrev (.east s) (by
        change s ≤ n; omega)]
      simp only [KMSWSlot.mirror, hi']




theorem kmswReversalPhi_inverse (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (v : ℕ) (hv : v < (kmswStage wr n).nextVertex) :
    kmswReversalPhi w wr n (kmswReversalPhi wr w n v) = v := by
  obtain ⟨S, hS, rfl⟩ := kmswSlotVertex_surjective wr n v hv
  rw [kmswReversalPhi_slot wr w n hrev S hS,
    kmswReversalPhi_slot w wr n (kmswReversal_letters_symm wr w n hrev)
      (S.mirror n) (by rw [KMSWSlot.time_mirror]; omega), KMSWSlot.mirror_mirror n S hS]




theorem kmswReversalPhi_lower_preimage (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ∀ y, (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
      (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
    ∃ yr, (∃ e ∈ (kmswStage wr n).LL ++ (kmswStage wr n).LR,
      (kmswStage wr n).west e = yr ∨ (kmswStage wr n).east e = yr) ∧
      kmswReversalPhi wr w n yr = y := by
  intro y hy
  have hsymm := kmswReversal_letters_symm wr w n hrev
  refine ⟨kmswReversalPhi w wr n y, kmswReversalPhi_upper w wr n hsymm y hy, ?_⟩
  apply kmswReversalPhi_inverse w wr n hsymm
  obtain ⟨e, he, heq⟩ := hy
  have hb := (kmswStage_boundary_ids_lt_nextEdge w n).2
  have he' : e < (kmswStage w n).nextEdge := by
    apply hb
    simp only [List.mem_append] at he ⊢
    tauto
  have hv := kmswStage_endpoints_lt_nextVertex w n e he'
  rcases heq with rfl | rfl
  · exact hv.1
  · exact hv.2




theorem kmswStage_exists_reversal_phi (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ∃ phi : ℕ → ℕ,
      (∀ e < (kmswStage wr n).nextEdge, (kmswStage wr n).present e = true →
        ∃ f < (kmswStage w n).nextEdge, (kmswStage w n).present f = true ∧
          (kmswStage w n).west f = phi ((kmswStage wr n).east e) ∧
          (kmswStage w n).east f = phi ((kmswStage wr n).west e)) ∧
      (∀ y, (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
          (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
        ¬ (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
          (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
        ∃ yr, (∃ e ∈ (kmswStage wr n).LL ++ (kmswStage wr n).LR,
          (kmswStage wr n).west e = yr ∨ (kmswStage wr n).east e = yr) ∧ phi yr = y) ∧
      (∀ x, (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
          (kmswStage wr n).west e = x ∨ (kmswStage wr n).east e = x) →
        ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
          (kmswStage w n).west e = phi x ∨ (kmswStage w n).east e = phi x) := by
  refine ⟨kmswReversalPhi wr w n, kmswReversalPhi_present wr w n hrev, ?_,
    kmswReversalPhi_upper wr w n hrev⟩
  intro y hy _
  exact kmswReversalPhi_lower_preimage wr w n hrev y hy

end DirectedDistances.KMSW
