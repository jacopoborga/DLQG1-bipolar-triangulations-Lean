module

public import DirectedDistances.KMSW.StageReversalLengths

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW




private def RpairBody (w : ℕ → Fin 3) (s t : ℕ) : Prop :=
  s < t ∧ R w (t + 1) = R w s ∧
    ∀ j, s < j → j ≤ t → R w s < R w j




private def LpairBody (w : ℕ → Fin 3) (t t' : ℕ) : Prop :=
  t < t' ∧ L w (t' + 1) = L w t ∧
    ∀ j, t < j → j ≤ t' → L w t < L w j




private theorem kmswRpairBody_reverse_core (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {s t : ℕ} (ht : t < n) :
    RpairBody wr s t ↔ LpairBody w (n - 1 - t) (n - 1 - s) := by
  have hR : ∀ k ≤ n, R wr k = L w (n - k) - L w n := by
    intro k hk
    exact kmswStage_reverse_R wr w n hrev hk
  constructor
  · rintro ⟨hst, heq, hmin⟩
    have hab : n - 1 - t < n - 1 - s := by omega
    have ha : n - (t + 1) = n - 1 - t := by omega
    have hb : n - s = (n - 1 - s) + 1 := by omega
    have heq' : L w ((n - 1 - s) + 1) = L w (n - 1 - t) := by
      have h1 := hR (t + 1) (by omega)
      have h2 := hR s (by omega)
      rw [h1, h2, ha, hb] at heq
      omega
    refine ⟨hab, heq', ?_⟩
    intro u hau hub
    let j := n - u
    have hsj : s < j := by dsimp [j]; omega
    have hjt : j ≤ t := by dsimp [j]; omega
    have hjn : j ≤ n := by omega
    have hval := hmin j hsj hjt
    have h1 := hR s (by omega)
    have h2 := hR j hjn
    have hidx : n - j = u := by dsimp [j]; omega
    rw [h1, h2, hb, hidx] at hval
    omega
  · rintro ⟨hab, heq, hmin⟩
    have hst : s < t := by omega
    have ha : n - (t + 1) = n - 1 - t := by omega
    have hb : n - s = (n - 1 - s) + 1 := by omega
    have heq' : R wr (t + 1) = R wr s := by
      have h1 := hR (t + 1) (by omega)
      have h2 := hR s (by omega)
      rw [h1, h2, ha, hb]
      omega
    refine ⟨hst, heq', ?_⟩
    intro j hsj hjt
    let u := n - j
    have hau : n - 1 - t < u := by dsimp [u]; omega
    have hub : u ≤ n - 1 - s := by dsimp [u]; omega
    have hval := hmin u hau hub
    have h1 := hR s (by omega)
    have h2 := hR j (by omega)
    have hidx : n - j = u := by dsimp [u]
    rw [h1, h2, hb, hidx]
    omega





private theorem kmswSwap_involutive (c : Fin 3) :
    Equiv.swap (0 : Fin 3) 1 (Equiv.swap (0 : Fin 3) 1 c) = c := by
  fin_cases c <;> simp [Equiv.swap_apply_def]




private theorem kmswSwap_two_iff (c : Fin 3) :
    Equiv.swap (0 : Fin 3) 1 c = 2 ↔ c = 2 := by
  fin_cases c <;> simp [Equiv.swap_apply_def]




private theorem kmswSwap_zero_iff (c : Fin 3) :
    Equiv.swap (0 : Fin 3) 1 c = 0 ↔ c = 1 := by
  fin_cases c <;> simp [Equiv.swap_apply_def]




private theorem kmswReverse_involutive (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ∀ i < n, w i = Equiv.swap (0 : Fin 3) 1 (wr (n - 1 - i)) := by
  intro i hi
  have hidx : n - 1 - (n - 1 - i) = i := by omega
  rw [hrev (n - 1 - i) (by omega), hidx]
  exact (kmswSwap_involutive (w i)).symm




private theorem kmswLpairBody_reverse_core (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {t t' : ℕ} (ht' : t' < n) :
    LpairBody wr t t' ↔ RpairBody w (n - 1 - t') (n - 1 - t) := by
  have hrev' := kmswReverse_involutive wr w n hrev
  by_cases ht : t < n
  · have hcore := kmswRpairBody_reverse_core w wr n hrev'
      (s := n - 1 - t') (t := n - 1 - t) (by omega)
    have hidx : n - 1 - (n - 1 - t) = t := by omega
    have hidx' : n - 1 - (n - 1 - t') = t' := by omega
    simpa only [hidx, hidx'] using hcore.symm
  · constructor
    · rintro ⟨htt', _, _⟩
      omega
    · rintro ⟨hab, _, _⟩
      omega





private theorem kmswULRecord_reverse_core (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {t : ℕ} (ht : t < n) :
    (w t = 2 ∧ ∀ j, t < j → j ≤ n → L w t < L w j) ↔
      (wr (n - 1 - t) = 2 ∧
        ∀ j, j ≤ n - 1 - t → R wr (n - 1 - t) ≤ R wr j) := by
  let q := n - 1 - t
  have hqn : q < n := by dsimp [q]; omega
  have hletter : wr q = 2 ↔ w t = 2 := by
    change wr (n - 1 - t) = 2 ↔ w t = 2
    rw [hrev (n - 1 - t) hqn]
    rw [show n - 1 - (n - 1 - t) = t by omega]
    exact kmswSwap_two_iff (w t)
  have hR (j : ℕ) (hj : j ≤ n) :
      R wr j = L w (n - j) - L w n :=
    kmswStage_reverse_R wr w n hrev hj
  have hLstep (hw : w t = 2) : L w (t + 1) = L w t + 1 := by
    rw [show L w (t + 1) = L w t +
      (RandomWalk.lazyTwoDimensionalStep (w t)).1 by
        exact Finset.sum_range_succ _ _, hw]
    norm_num [RandomWalk.lazyTwoDimensionalStep]
  have hqidx : n - q = t + 1 := by dsimp [q]; omega
  have hqwalk (hw : w t = 2) : R wr q = L w (t + 1) - L w n := by
    rw [hR q (by dsimp [q]; omega), hqidx]
  constructor
  · rintro ⟨hw, hfuture⟩
    refine ⟨hletter.mpr hw, ?_⟩
    intro j hj
    have hu : t < n - j := by omega
    have hun : n - j ≤ n := by omega
    have hval := hfuture (n - j) hu hun
    have hjwalk := hR j (by omega)
    rw [hqwalk hw, hjwalk, hLstep hw]
    omega
  · rintro ⟨hr, hpast⟩
    have hw := hletter.mp hr
    refine ⟨hw, ?_⟩
    intro j hj hjn
    have hqj : n - j ≤ q := by omega
    have hjwalk := hR (n - j) (by omega)
    have hval := hpast (n - j) hqj
    have hidx : n - (n - j) = j := by omega
    rw [hqwalk hw, hjwalk, hidx, hLstep hw] at hval
    omega





private theorem kmswURRecord_reverse_core (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {s : ℕ} (hs : s < n) :
    (w s = 1 ∧ ∀ j, s < j → j ≤ n → R w s < R w j) ↔
      (wr (n - 1 - s) = 0 ∧
        ∀ j, j ≤ n - 1 - s → L wr (n - 1 - s) ≤ L wr j) := by
  let q := n - 1 - s
  have hqn : q < n := by dsimp [q]; omega
  have hletter : wr q = 0 ↔ w s = 1 := by
    change wr (n - 1 - s) = 0 ↔ w s = 1
    rw [hrev (n - 1 - s) hqn]
    rw [show n - 1 - (n - 1 - s) = s by omega]
    exact kmswSwap_zero_iff (w s)
  have hL (j : ℕ) (hj : j ≤ n) :
      L wr j = R w (n - j) - R w n :=
    kmswStage_reverse_L wr w n hrev hj
  have hRstep (hw : w s = 1) : R w (s + 1) = R w s + 1 := by
    rw [show R w (s + 1) = R w s +
      (RandomWalk.lazyTwoDimensionalStep (w s)).2 by
        exact Finset.sum_range_succ _ _, hw]
    norm_num [RandomWalk.lazyTwoDimensionalStep]
  have hqidx : n - q = s + 1 := by dsimp [q]; omega
  have hqwalk (hw : w s = 1) : L wr q = R w (s + 1) - R w n := by
    rw [hL q (by dsimp [q]; omega), hqidx]
  constructor
  · rintro ⟨hw, hfuture⟩
    refine ⟨hletter.mpr hw, ?_⟩
    intro j hj
    have hu : s < n - j := by omega
    have hun : n - j ≤ n := by omega
    have hval := hfuture (n - j) hu hun
    have hjwalk := hL j (by omega)
    rw [hqwalk hw, hjwalk, hRstep hw]
    omega
  · rintro ⟨hr, hpast⟩
    have hw := hletter.mp hr
    refine ⟨hw, ?_⟩
    intro j hj hjn
    have hjwalk := hL (n - j) (by omega)
    have hval := hpast (n - j) (by omega)
    have hidx : n - (n - j) = j := by omega
    rw [hqwalk hw, hjwalk, hidx, hRstep hw] at hval
    omega




private theorem kmswReversal_swap_hyp (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    ∀ i < n, w i = Equiv.swap (0 : Fin 3) 1 (wr (n - 1 - i)) :=
  kmswReverse_involutive wr w n hrev




theorem kmswRpairBody_reverse_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {s t : ℕ} (ht : t < n) :
    (s < t ∧ R wr (t + 1) = R wr s ∧
      ∀ j, s < j → j ≤ t → R wr s < R wr j) ↔
    (n - 1 - t < n - 1 - s ∧
      L w (n - 1 - s + 1) = L w (n - 1 - t) ∧
      ∀ j, n - 1 - t < j → j ≤ n - 1 - s →
        L w (n - 1 - t) < L w j) := by
  exact kmswRpairBody_reverse_core wr w n hrev ht




theorem kmswLpairBody_reverse_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {t t' : ℕ} (ht' : t' < n) :
    (t < t' ∧ L wr (t' + 1) = L wr t ∧
      ∀ j, t < j → j ≤ t' → L wr t < L wr j) ↔
    (n - 1 - t' < n - 1 - t ∧
      R w (n - 1 - t + 1) = R w (n - 1 - t') ∧
      ∀ j, n - 1 - t' < j → j ≤ n - 1 - t →
        R w (n - 1 - t') < R w j) := by
  exact kmswLpairBody_reverse_core wr w n hrev ht'





theorem kmswULRecord_reverse_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {t : ℕ} (ht : t ≤ n) :
    (t = n ∨ (w t = 2 ∧
      ∀ j, t < j → j ≤ n → L w t < L w j)) ↔
    (t = n ∨ (wr (n - t - 1) = 2 ∧
      ∀ j, j ≤ n - t - 1 → R wr (n - t - 1) ≤ R wr j)) := by
  by_cases htn : t = n
  · subst t
    simp
  · have htlt : t < n := by omega
    have hidx : n - t - 1 = n - 1 - t := by omega
    simpa [htn, hidx] using kmswULRecord_reverse_core wr w n hrev htlt





theorem kmswURRecord_reverse_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {s : ℕ} (hs : s < n) :
    (w s = 1 ∧ ∀ j, s < j → j ≤ n → R w s < R w j) ↔
    (wr (n - 1 - s) = 0 ∧
      ∀ j, j ≤ n - 1 - s → L wr (n - 1 - s) ≤ L wr j) := by
  exact kmswURRecord_reverse_core wr w n hrev hs





theorem kmswLRRecord_reverse_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {t : ℕ} (ht : t ≤ n) :
    (t = n ∨ (wr t = 2 ∧
      ∀ j, t < j → j ≤ n → L wr t < L wr j)) ↔
    (t = n ∨ (w (n - t - 1) = 2 ∧
      ∀ j, j ≤ n - t - 1 → R w (n - t - 1) ≤ R w j)) := by
  have hrev' := kmswReversal_swap_hyp wr w n hrev
  exact kmswULRecord_reverse_iff w wr n hrev' ht





theorem kmswLLRecord_reverse_iff (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n,
      wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {s : ℕ} (hs : s < n) :
    (w s = 0 ∧ ∀ j, j ≤ s → L w s ≤ L w j) ↔
    (wr (n - 1 - s) = 1 ∧
      ∀ j, n - 1 - s < j → j ≤ n →
        R wr (n - 1 - s) < R wr j) := by
  have hrev' := kmswReversal_swap_hyp wr w n hrev
  have hcore := kmswURRecord_reverse_core w wr n hrev'
    (s := n - 1 - s) (by omega)
  have hidx : n - 1 - (n - 1 - s) = s := by omega
  simpa only [hidx] using hcore.symm

end DirectedDistances.KMSW
