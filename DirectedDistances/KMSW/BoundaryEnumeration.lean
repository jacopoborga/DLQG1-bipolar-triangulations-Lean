module

public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.StageIncidenceChains

/-! # Hit-indexed enumeration of the KMSW lower boundary

The deterministic boundary edges indexed by the first coordinate hits in
`eqn-bdy-vertex-hit` and `eqn-bdy-vertex-kmsw`
lower-right chain. Negative indices use the unconditioned KMSW lower-left
missing chain, recorded by `kmswStage_LL_eq`. -/

public section
namespace DirectedDistances.KMSW

open scoped Classical

private theorem coordinate_succ_ge_R (w : ℕ → Fin 3) (n : ℕ) :
    R w n - 1 ≤ R w (n + 1) := by
  have hR : R w (n + 1) = R w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    split_ifs <;> omega
  rw [hR]
  omega

private theorem coordinate_succ_ge_L (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) := by
  have hL : L w (n + 1) = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    omega
  rw [hL]
  omega

private theorem exists_coordinate_eq_of_le (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  classical
  let m := Nat.find (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hma : f m ≤ a := Nat.find_spec (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hmn : m ≤ n := Nat.find_min' (⟨n, hn⟩ : ∃ j, f j ≤ a) hn
  by_cases hm0 : m = 0
  · rw [hm0, hzero] at hma
    omega
  · obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hprev : a < f p := by
      have hnot := Nat.find_min (⟨n, hn⟩ : ∃ j, f j ≤ a) (by omega : p < m)
      omega
    refine ⟨m, hmn, ?_⟩
    rw [hp] at hma ⊢
    have hnext := hstep p
    omega

private theorem first_coordinate_hit_is_strict_record (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) (h : ∃ n, f n = a) :
    ∀ j < Nat.find h, a < f j := by
  intro j hj
  by_contra hnot
  have hjle : f j ≤ a := by omega
  obtain ⟨m, hmj, hma⟩ := exists_coordinate_eq_of_le f hstep hzero ha hjle
  have hmn : m < Nat.find h := hmj.trans_lt hj
  exact (Nat.find_min h hmn) hma

private theorem boundaryHitTime_right_eq_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
  unfold boundaryHitTime
  simp only [dite_eq_right (by omega : k ≠ 0), dite_eq_left (by omega : 0 < k)]

private theorem boundaryHitTime_left_eq_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
  unfold boundaryHitTime
  simp only [dite_eq_right (by omega : k ≠ 0), dite_eq_right (by omega : ¬ 0 < k)]

private theorem boundaryHitTime_strict_right (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∀ j < boundaryHitTime w h k, -k < R w j := by
  have htime := boundaryHitTime_right_eq_find w h hk
  have hzero : R w 0 = 0 := by simp [R]
  have hstrict := first_coordinate_hit_is_strict_record (R w)
    (coordinate_succ_ge_R w) hzero (by omega : -k < 0) (h.rightHit k hk)
  intro j hj
  rw [htime] at hj
  exact hstrict j hj

private theorem boundaryHitTime_strict_left (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k, k < L w j := by
  have htime := boundaryHitTime_left_eq_find w h hk
  have hzero : L w 0 = 0 := by simp [L]
  have hstrict := first_coordinate_hit_is_strict_record (L w)
    (coordinate_succ_ge_L w) hzero (by omega : k < 0) (h.leftHit k hk)
  intro j hj
  rw [htime] at hj
  exact hstrict j hj

private theorem boundaryHitTime_left_previous (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∃ m, boundaryHitTime w h k = m + 1 ∧ L w m = k + 1 ∧
      w m = 0 ∧ (kmswStage w m).UL.length = 1 := by
  let n := boundaryHitTime w h k
  have hhit : L w n = k := boundaryHitTime_left_spec w h hk
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hhit
    simp [L] at hhit
    omega
  let m := n - 1
  have hnm : n = m + 1 := by dsimp [m]; omega
  have hm_lt : m < n := by omega
  have hprevlo : k + 1 ≤ L w m := by
    have := boundaryHitTime_strict_left w h hk m hm_lt
    omega
  have hLstep : L w n = L w m +
      (RandomWalk.lazyTwoDimensionalStep (w m)).1 := by
    rw [hnm]
    exact Finset.sum_range_succ _ _
  have hstepLower : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w m)).1 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    omega
  have hprevhi : L w m ≤ k + 1 := by rw [hLstep] at hhit; omega
  have hprev : L w m = k + 1 := by omega
  have hstep : (RandomWalk.lazyTwoDimensionalStep (w m)).1 = -1 := by
    rw [hLstep, hprev] at hhit
    omega
  have hw : w m = 0 := by
    have hval : (w m).val = 0 := by
      have hbound := (w m).isLt
      simp only [RandomWalk.lazyTwoDimensionalStep] at hstep
      omega
    exact Fin.ext hval
  have hmin : minL w m = k + 1 := by
    obtain ⟨i, him, hi⟩ := runningMin_attained (L w) m
    change minL w m = L w i at hi
    have hlow : k + 1 ≤ L w i := by
      have := boundaryHitTime_strict_left w h hk i (by omega)
      omega
    have hle := runningMin_le (L w) m m (le_refl m)
    change minL w m ≤ L w m at hle
    rw [hprev] at hle
    omega
  have hULcast : ((kmswStage w m).UL.length : ℤ) = 1 := by
    rw [kmswStage_UL_length, hprev, hmin]
    norm_num
  have hULlen : (kmswStage w m).UL.length = 1 := by exact_mod_cast hULcast
  exact ⟨m, hnm, hprev, hw, hULlen⟩

private theorem boundaryHitTime_right_previous (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∃ m, boundaryHitTime w h k = m + 1 ∧ R w m = -k + 1 ∧
      w m = 2 ∧ (kmswStage w m).UR = [] := by
  let n := boundaryHitTime w h k
  have hhit : R w n = -k := boundaryHitTime_right_spec w h hk
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hhit
    simp [R] at hhit
    omega
  let m := n - 1
  have hnm : n = m + 1 := by dsimp [m]; omega
  have hm_lt : m < n := by omega
  have hprevlo : -k + 1 ≤ R w m := by
    have := boundaryHitTime_strict_right w h hk m hm_lt
    omega
  have hRstep : R w n = R w m +
      (RandomWalk.lazyTwoDimensionalStep (w m)).2 := by
    rw [hnm]
    exact Finset.sum_range_succ _ _
  have hstepLower : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w m)).2 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    split_ifs <;> omega
  have hprevhi : R w m ≤ -k + 1 := by rw [hRstep] at hhit; omega
  have hprev : R w m = -k + 1 := by omega
  have hstep : (RandomWalk.lazyTwoDimensionalStep (w m)).2 = -1 := by
    rw [hRstep, hprev] at hhit
    omega
  have hw : w m = 2 := by
    have hval : (w m).val = 2 := by
      have hbound := (w m).isLt
      simp only [RandomWalk.lazyTwoDimensionalStep] at hstep
      omega
    exact Fin.ext hval
  have hmin : minR w m = -k + 1 := by
    obtain ⟨i, him, hi⟩ := runningMin_attained (R w) m
    change minR w m = R w i at hi
    have hlow : -k + 1 ≤ R w i := by
      have := boundaryHitTime_strict_right w h hk i (by omega)
      omega
    have hle := runningMin_le (R w) m m (le_refl m)
    change minR w m ≤ R w m at hle
    rw [hprev] at hle
    omega
  have hURcast : ((kmswStage w m).UR.length : ℤ) = 0 := by
    rw [kmswStage_UR_length, hprev, hmin]
    norm_num
  have hURlen : (kmswStage w m).UR.length = 0 := by exact_mod_cast hURcast
  exact ⟨m, hnm, hprev, hw, List.length_eq_zero_iff.mp hURlen⟩

private theorem boundaryHitTime_left_mono (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {a b : ℤ}
    (ha : a ≤ -1) (hab : a ≤ b) (hb : b ≤ -1) :
    boundaryHitTime w h b ≤ boundaryHitTime w h a := by
  have haHit := boundaryHitTime_left_spec w h ha
  obtain ⟨m, hm, hmb⟩ := exists_coordinate_eq_of_le (L w)
    (coordinate_succ_ge_L w) (by simp [L]) (by omega : b < 0)
    (by omega : L w (boundaryHitTime w h a) ≤ b)
  have htime := boundaryHitTime_left_eq_find w h hb
  rw [htime]
  calc
    Nat.find (h.leftHit b hb) ≤ m := Nat.find_min' (h.leftHit b hb) hmb
    _ ≤ boundaryHitTime w h a := hm

private theorem boundaryHitTime_right_mono (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {a b : ℤ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    boundaryHitTime w h a ≤ boundaryHitTime w h b := by
  have hb : 1 ≤ b := by omega
  have hbHit := boundaryHitTime_right_spec w h hb
  obtain ⟨m, hm, hmb⟩ := exists_coordinate_eq_of_le (R w)
    (coordinate_succ_ge_R w) (by simp [R]) (by omega : -a < 0)
    (by rw [hbHit]; omega)
  have htime := boundaryHitTime_right_eq_find w h ha
  rw [htime]
  calc
    Nat.find (h.rightHit a ha) ≤ m := Nat.find_min' (h.rightHit a ha) hmb
    _ ≤ boundaryHitTime w h b := hm

private theorem kmswStage_LR_mem_of_mem (w : ℕ → Fin 3) {m n e : ℕ}
    (hmn : m ≤ n) (he : e ∈ (kmswStage w m).LR) :
    e ∈ (kmswStage w n).LR := by
  induction n, hmn using Nat.le_induction with
  | base => exact he
  | succ n _ ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w n
    rw [ht]
    exact List.mem_append_left _ ih

private theorem filter_range_last_local (P : ℕ → Bool) (n m : ℕ) (hm : m ≤ n)
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
      rw [List.range_succ, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, hPm, ite_true]
    · have hmn' : m ≤ n := by omega
      have hno' : ∀ j, m < j → j ≤ n → P j = false := by
        intro j hj hjn
        exact hno j hj (by omega)
      rw [List.range_succ, List.filter_append, ih hmn' hno']
      have hb : P (n + 1) = false := hno (n + 1) (by omega) le_rfl
      simp [hb]

private theorem boundaryHitTime_right_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∀ j < boundaryHitTime w h k, R w (boundaryHitTime w h k) < R w j := by
  intro j hj
  rw [boundaryHitTime_right_spec w h hk]
  have hstrict := boundaryHitTime_strict_right w h hk j hj
  omega

private theorem boundaryHitTime_left_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k, L w (boundaryHitTime w h k) < L w j := by
  intro j hj
  rw [boundaryHitTime_left_spec w h hk]
  exact boundaryHitTime_strict_left w h hk j hj

/-! ### The missing lower-left chain -/

/-- At the first hit of `L = k`, the new lower-left geometric edge joins the
hit-indexed vertex `x_k` to `x_{k+1}`. It is a missing edge, so these endpoints
are not asserted to be connected by a directed edge. This includes the root
adjacency `x_{-1}`--`x_0` at `k = -1` (`eqn-bdy-vertex-kmsw`, -/
theorem boundaryVertex_left_missing_edge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    let n := boundaryHitTime w h k
    let e := kmswLLCreatedEdge w n
    (kmswStage w n).west e = boundaryVertex w h k ∧
      (kmswStage w n).east e = boundaryVertex w h (k + 1) ∧
      (kmswStage w n).present e = false := by
  obtain ⟨m, hnm, hprev, hw, hULlen⟩ := boundaryHitTime_left_previous w h hk
  let s := kmswStage w m
  have hlast := kmswStage_UL_last w m
  obtain ⟨es, hes⟩ := hlast
  have hesEmpty : es = [] := by
    have hlen : es.length + 1 = 1 := by
      rw [hes] at hULlen
      simpa only [List.length_append, List.length_cons, List.length_nil] using hULlen
    exact List.length_eq_zero_iff.mp (by omega)
  have hUL : s.UL = [s.active] := by
    rw [hes, hesEmpty]
    rfl
  have hdrop : s.UL.dropLast.reverse = [] := by
    rw [hUL]
    rfl
  have hstage : kmswStage w (m + 1) = kmswStepOfStep s .left := by
    change kmswStep (kmswStage w m) (w m) = _
    rw [hw]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, s, hdrop]
  have hnew : activeInitial w (m + 1) = s.nextVertex := by
    rw [CutConverse.activeInitial_eq w (m + 1)]
    change (kmswStage w (m + 1)).west (kmswStage w (m + 1)).active = _
    rw [hstage]
    simp [kmswStepOfStep, hdrop, State.addEdge]
  have hxwest : boundaryVertex w h k = s.nextVertex := by
    rw [boundaryVertex_left_hit_eq w h hk, hnm]
    exact hnew
  have hid : kmswLLCreatedEdge w (m + 1) = s.nextEdge + 1 := by
    simp [kmswLLCreatedEdge, hstage, s, kmswStepOfStep, hdrop, State.addEdge]
  have hwest : (kmswStage w (m + 1)).west (kmswLLCreatedEdge w (m + 1)) =
      boundaryVertex w h k := by
    rw [hid, hstage]
    simp [kmswStepOfStep, s, hdrop, State.addEdge, hxwest]
  have hqvertex : boundaryVertex w h (k + 1) =
      activeInitial w (boundaryHitTime w h (k + 1)) := by
    by_cases hq0 : k + 1 = 0
    · rw [hq0, boundaryVertex_zero, boundaryHitTime_zero]
      rfl
    · have hq : k + 1 ≤ -1 := by omega
      exact boundaryVertex_left_hit_eq w h hq
  have hqtime : boundaryHitTime w h (k + 1) ≤ m := by
    by_cases hq0 : k + 1 = 0
    · rw [hq0, boundaryHitTime_zero]
      omega
    · have horder := boundaryHitTime_left_mono w h
        (a := k) (b := k + 1) hk (by omega) (by omega)
      have hneq : boundaryHitTime w h (k + 1) ≠ boundaryHitTime w h k := by
        intro heq
        have hqspec := boundaryHitTime_left_spec w h (by omega : k + 1 ≤ -1)
        rw [heq] at hqspec
        have hkspec := boundaryHitTime_left_spec w h hk
        omega
      rw [hnm] at horder
      rw [hnm] at hneq
      omega
  have hqlevel : L w (boundaryHitTime w h (k + 1)) = k + 1 := by
    by_cases hq0 : k + 1 = 0
    · rw [hq0, boundaryHitTime_zero]
      simp [L]
    · exact boundaryHitTime_left_spec w h (by omega)
  have habove : ∀ j, boundaryHitTime w h (k + 1) ≤ j → j ≤ m →
      L w (boundaryHitTime w h (k + 1)) ≤ L w j := by
    intro j _ hjm
    have hjn : j < boundaryHitTime w h k := by rw [hnm]; omega
    have hstrict := boundaryHitTime_strict_left w h hk j hjn
    rw [hqlevel]
    omega
  have hwestlevel := kmsw_west_act_eq_of_level w hqtime
    (by rw [hqlevel, hprev]) habove
  have hstable := kmswStage_endpoints_stable w hqtime
    (act_lt_nextEdge w (Nat.le_refl (boundaryHitTime w h (k + 1))))
  have hAI : activeInitial w m = activeInitial w (boundaryHitTime w h (k + 1)) := by
    calc
      activeInitial w m = (kmswStage w m).west (act w m) := CutConverse.activeInitial_eq w m
      _ = (kmswStage w m).west (act w (boundaryHitTime w h (k + 1))) := hwestlevel.symm
      _ = (kmswStage w (boundaryHitTime w h (k + 1))).west
          (act w (boundaryHitTime w h (k + 1))) := hstable.1
      _ = activeInitial w (boundaryHitTime w h (k + 1)) :=
        (CutConverse.activeInitial_eq w _).symm
  have hS : s.west s.active = activeInitial w m := by
    dsimp [s]
    exact (CutConverse.activeInitial_eq w m).symm
  have heast : (kmswStage w (m + 1)).east (kmswLLCreatedEdge w (m + 1)) =
      boundaryVertex w h (k + 1) := by
    rw [hid, hstage]
    simp only [kmswStepOfStep, hdrop, ↓reduceIte, State.addEdge]
    exact hS.trans (hAI.trans hqvertex.symm)
  have hrecord := boundaryHitTime_left_record w h hk
  have hmissing := kmswLLCreatedEdge_missing w (Nat.succ_pos _)
    (by simpa [hnm] using hrecord)
  change (kmswStage w (boundaryHitTime w h k)).west
      (kmswLLCreatedEdge w (boundaryHitTime w h k)) = boundaryVertex w h k ∧
    (kmswStage w (boundaryHitTime w h k)).east
      (kmswLLCreatedEdge w (boundaryHitTime w h k)) = boundaryVertex w h (k + 1) ∧
    (kmswStage w (boundaryHitTime w h k)).present
      (kmswLLCreatedEdge w (boundaryHitTime w h k)) = false
  rw [hnm]
  exact ⟨hwest, heast, hmissing⟩

/-! ### The present lower-right chain -/

/-- Consecutive positive hit-indexed vertices are the west and east endpoints
of one present lower-right edge. The edge is already in the stage LR list at
some finite stage and remains there, with these endpoints and present status,
at every later stage. This establishes the directed-order enumeration
`x₁, x₂, …` beginning at `x₁ = 1` (`eqn-bdy-vertex-hit`, -/
theorem boundaryVertex_right_edge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∃ N, boundaryHitTime w h k ≤ N ∧ ∀ n, N ≤ n →
      act w (boundaryHitTime w h k) ∈ (kmswStage w n).LR ∧
      (kmswStage w n).present (act w (boundaryHitTime w h k)) = true ∧
      (kmswStage w n).west (act w (boundaryHitTime w h k)) = boundaryVertex w h k ∧
      (kmswStage w n).east (act w (boundaryHitTime w h k)) = boundaryVertex w h (k + 1) := by
  let r := boundaryHitTime w h k
  obtain ⟨p, hnext, hRp, hcode, hUR⟩ :=
    boundaryHitTime_right_previous w h (by omega : 1 ≤ k + 1)
  have hrleNext : r ≤ boundaryHitTime w h (k + 1) :=
    boundaryHitTime_right_mono w h hk (by omega)
  have hrneNext : r ≠ boundaryHitTime w h (k + 1) := by
    intro heq
    have hrval := boundaryHitTime_right_spec w h hk
    have hnval := boundaryHitTime_right_spec w h (by omega : 1 ≤ k + 1)
    have heq' : boundaryHitTime w h k = boundaryHitTime w h (k + 1) := by
      simpa [r] using heq
    rw [heq'] at hrval
    omega
  have hrp : r ≤ p := by
    have hrlt : r < boundaryHitTime w h (k + 1) := by omega
    rw [hnext] at hrlt
    dsimp [r] at hrlt
    omega
  have hrecord : ∀ j < r, R w r < R w j := by
    exact boundaryHitTime_right_record w h hk
  let P : ℕ → Bool := fun m => decide (∀ j, j < m → R w m < R w j)
  have hPr : P r = true := decide_eq_true hrecord
  have hno : ∀ j, r < j → j ≤ p → P j = false := by
    intro j hrj hjp
    apply decide_eq_false
    intro hrec
    have hjlt : j < boundaryHitTime w h (k + 1) := by
      rw [hnext]
      omega
    have hjlevel := boundaryHitTime_strict_right w h (by omega : 1 ≤ k + 1) j hjlt
    have hrlevel := boundaryHitTime_right_spec w h hk
    have hrlevel' : R w r = -k := by dsimp [r]; exact hrlevel
    have hbad := hrec r hrj
    omega
  have hfilter := filter_range_last_local P p r hrp hPr hno
  have hLRlist : (kmswStage w p).LR =
      ((List.range r).filter P).map (act w) ++ [act w r] := by
    rw [kmswStage_LR_eq, hfilter, List.map_append]
    rfl
  rcases kmswStage_boundary_chain_invariant w p with
    ⟨_, _, _, _, hLRne, _, hURempty⟩
  have hlast : (kmswStage w p).LR.getLast hLRne = act w r := by
    have hlast? : (kmswStage w p).LR.getLast? = some (act w r) := by
      rw [hLRlist]
      simp
    have hget := List.getLast?_eq_getLast_of_ne_nil hLRne
    rw [hget] at hlast?
    exact Option.some.inj hlast?
  have hmem : act w r ∈ (kmswStage w p).LR := by
    rw [hLRlist]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hpresent : (kmswStage w p).present (act w r) = true :=
    (kmswStage_status w p).2.2.1 (act w r) hmem
  have hstable := kmswStage_endpoints_stable w hrp
    (act_lt_nextEdge w (Nat.le_refl r))
  have hwestAtP : (kmswStage w p).west (act w r) = boundaryVertex w h k := by
    calc
      (kmswStage w p).west (act w r) = (kmswStage w r).west (act w r) := hstable.1
      _ = activeInitial w r := (CutConverse.activeInitial_eq w r).symm
      _ = boundaryVertex w h k := (boundaryVertex_right_hit_eq w h hk).symm
  have hlastEast := hURempty hLRne hUR
  rw [hlast] at hlastEast
  have hstage : kmswStage w (p + 1) = kmswStepOfStep (kmswStage w p) .down := by
    change kmswStep (kmswStage w p) (w p) = _
    rw [hcode]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hnewActive : activeInitial w (p + 1) =
      (kmswStage w p).east (kmswStage w p).active := by
    rw [CutConverse.activeInitial_eq w (p + 1)]
    change (kmswStage w (p + 1)).west (kmswStage w (p + 1)).active = _
    rw [hstage]
    simp [kmswStepOfStep, hUR, State.addEdge]
  have hnextVertex : boundaryVertex w h (k + 1) = activeInitial w (p + 1) := by
    have heq := boundaryVertex_right_hit_eq w h (by omega : 1 ≤ k + 1)
    rw [hnext] at heq
    exact heq
  have heastAtP : (kmswStage w p).east (act w r) = boundaryVertex w h (k + 1) := by
    calc
      (kmswStage w p).east (act w r) =
        (kmswStage w p).east (kmswStage w p).active := hlastEast.symm
      _ = activeInitial w (p + 1) := hnewActive.symm
      _ = boundaryVertex w h (k + 1) := hnextVertex.symm
  refine ⟨p, hrp, fun n hpn => ?_⟩
  have hmemN : act w r ∈ (kmswStage w n).LR :=
    kmswStage_LR_mem_of_mem w hpn hmem
  have hstableN := kmswStage_endpoints_stable w hpn
    (act_lt_nextEdge w hrp)
  exact ⟨hmemN, (kmswStage_status w n).2.2.1 _ hmemN,
    hstableN.1.trans hwestAtP, hstableN.2.trans heastAtP⟩

/-! ### The root edge -/

/-- The root edge `λ₀` is the initial present edge, ordered from `x₀ = 0` to -/
theorem boundaryVertex_root_edge (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    (kmswStage w 0).LR = [0] ∧
      (kmswStage w 0).west 0 = boundaryVertex w h 0 ∧
      (kmswStage w 0).east 0 = boundaryVertex w h 1 ∧
      (kmswStage w 0).present 0 = true := by
  simp [kmswStage, kmswInit, boundaryVertex_zero, boundaryVertex_one]

private theorem boundaryVertex_eq_activeInitial_nonzero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk0 : k ≠ 0) :
    boundaryVertex w h k = activeInitial w (boundaryHitTime w h k) := by
  by_cases hkpos : 1 ≤ k
  · exact boundaryVertex_right_hit_eq w h hkpos
  · exact boundaryVertex_left_hit_eq w h (by omega)

private theorem boundaryVertex_first_visit_nonzero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk0 : k ≠ 0) :
    ∀ j, j < boundaryHitTime w h k →
      boundaryVertex w h k ≠ activeInitial w j := by
  by_cases hkpos : 1 ≤ k
  · exact boundaryVertex_first_visit_right w h hkpos
  · exact boundaryVertex_first_visit_left w h (by omega)

private theorem activeInitial_zero (w : ℕ → Fin 3) : activeInitial w 0 = 0 := by
  simp [activeInitial, edgeWest, act, kmswStage, kmswInit]

private theorem boundaryVertex_ne_zero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk0 : k ≠ 0) :
    boundaryVertex w h k ≠ 0 := by
  have htimepos : 0 < boundaryHitTime w h k := by
    by_cases hkpos : 1 ≤ k
    · obtain ⟨m, htime, _, _, _⟩ := boundaryHitTime_right_previous w h hkpos
      rw [htime]
      omega
    · obtain ⟨m, htime, _, _, _⟩ :=
        boundaryHitTime_left_previous w h (k := k) (by omega)
      rw [htime]
      omega
  intro hz
  have hfirst := boundaryVertex_first_visit_nonzero w h hk0 0 htimepos
  exact hfirst (hz.trans (activeInitial_zero w).symm)

/-- The hit-indexed vertex map is injective (`eqn-bdy-vertex-hit`, -/
theorem boundaryVertex_injective (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : Function.Injective (boundaryVertex w h) := by
  intro k l heq
  by_cases hk0 : k = 0
  · subst k
    by_cases hl0 : l = 0
    · exact hl0.symm
    · exact False.elim (boundaryVertex_ne_zero w h hl0 (by
        rw [boundaryVertex_zero] at heq
        exact heq.symm))
  · by_cases hl0 : l = 0
    · subst l
      exact False.elim (boundaryVertex_ne_zero w h hk0 heq)
    · let tk := boundaryHitTime w h k
      let tl := boundaryHitTime w h l
      have hkAI : boundaryVertex w h k = activeInitial w tk := by
        dsimp [tk]
        exact boundaryVertex_eq_activeInitial_nonzero w h hk0
      have hlAI : boundaryVertex w h l = activeInitial w tl := by
        dsimp [tl]
        exact boundaryVertex_eq_activeInitial_nonzero w h hl0
      by_cases hkl : tk < tl
      · have hfirst := boundaryVertex_first_visit_nonzero w h hl0 tk hkl
        have hcontra : boundaryVertex w h l = activeInitial w tk :=
          heq.symm.trans hkAI
        exact False.elim (hfirst hcontra)
      · by_cases hlk : tl < tk
        · have hfirst := boundaryVertex_first_visit_nonzero w h hk0 tl hlk
          have hcontra : boundaryVertex w h k = activeInitial w tl :=
            heq.trans hlAI
          exact False.elim (hfirst hcontra)
        · have htimes : tk = tl := by omega
          dsimp [tk, tl] at htimes
          by_cases hkpos : 1 ≤ k
          · by_cases hlpos : 1 ≤ l
            · have hkr := boundaryHitTime_right_spec w h hkpos
              have hlr := boundaryHitTime_right_spec w h hlpos
              rw [← htimes] at hlr
              rw [hkr] at hlr
              omega
            · obtain ⟨m, hkm, _, hkc, _⟩ := boundaryHitTime_right_previous w h hkpos
              obtain ⟨m', hlm, _, hlc, _⟩ :=
                boundaryHitTime_left_previous w h (k := l) (by omega)
              have hm : m = m' := by rw [hkm, hlm] at htimes; omega
              have hc := hkc.symm.trans (by simpa [hm] using hlc)
              exact False.elim ((by decide : (2 : Fin 3) ≠ 0) hc)
          · by_cases hlpos : 1 ≤ l
            · obtain ⟨m, hkm, _, hkc, _⟩ :=
                boundaryHitTime_left_previous w h (k := k) (by omega)
              obtain ⟨m', hlm, _, hlc, _⟩ := boundaryHitTime_right_previous w h hlpos
              have hm : m = m' := by rw [hkm, hlm] at htimes; omega
              have hc := hkc.symm.trans (by simpa [hm] using hlc)
              exact False.elim ((by decide : (0 : Fin 3) ≠ 2) hc)
            · have hklval := boundaryHitTime_left_spec w h (by omega : k ≤ -1)
              have hllval := boundaryHitTime_left_spec w h (by omega : l ≤ -1)
              rw [← htimes] at hllval
              rw [hklval] at hllval
              omega

/-- In the LL chain, the missing edge indexed by `k - 1` has endpoints
`x_{k-1}` and `x_k` for every `k ≤ -1`. Its geometric order is west to east;
the edge has no directed orientation (`kmswStage_LL_eq`, -/
theorem boundaryVertex_left_consecutive (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    let e := kmswLLCreatedEdge w (boundaryHitTime w h (k - 1))
    (kmswStage w (boundaryHitTime w h (k - 1))).west e = boundaryVertex w h (k - 1) ∧
      (kmswStage w (boundaryHitTime w h (k - 1))).east e = boundaryVertex w h k ∧
      (kmswStage w (boundaryHitTime w h (k - 1))).present e = false := by
  have hprev := boundaryVertex_left_missing_edge w h (k := k - 1) (by omega)
  have hindex : (k - 1) + 1 = k := by omega
  simpa only [hindex] using hprev

/-- The first lower-left missing edge joins `x_{-1}` to the root vertex -/
theorem boundaryVertex_left_root_missing_edge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    let e := kmswLLCreatedEdge w (boundaryHitTime w h (-1))
    (kmswStage w (boundaryHitTime w h (-1))).west e = boundaryVertex w h (-1) ∧
      (kmswStage w (boundaryHitTime w h (-1))).east e = 0 ∧
      (kmswStage w (boundaryHitTime w h (-1))).present e = false := by
  have hroot := boundaryVertex_left_missing_edge w h (k := -1) (by omega)
  simpa [boundaryVertex_zero] using hroot

private theorem boundaryHitTime_eq_left_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {m : ℕ} {q : ℤ}
    (hq : q ≤ -1) (hvalue : L w m = q)
    (hrecord : ∀ j < m, q < L w j) :
    boundaryHitTime w h q = m := by
  have hle : boundaryHitTime w h q ≤ m := by
    rw [boundaryHitTime_left_eq_find w h hq]
    exact Nat.find_min' (h.leftHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hfirst := boundaryHitTime_left_spec w h hq
    have hstrict := hrecord (boundaryHitTime w h q) hlt
    rw [hfirst] at hstrict
    exact (lt_irrefl q) hstrict
  omega

private theorem boundaryHitTime_eq_right_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {m : ℕ} {q : ℤ}
    (hq : 1 ≤ q) (hvalue : R w m = -q)
    (hrecord : ∀ j < m, R w m < R w j) :
    boundaryHitTime w h q = m := by
  have hle : boundaryHitTime w h q ≤ m := by
    rw [boundaryHitTime_right_eq_find w h hq]
    exact Nat.find_min' (h.rightHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hfirst := boundaryHitTime_right_spec w h hq
    have hstrict := hrecord (boundaryHitTime w h q) hlt
    rw [hvalue] at hstrict
    rw [hfirst] at hstrict
    exact (lt_irrefl (-q)) hstrict
  omega

/-- Every vertex incident to a finite lower boundary edge belongs to the
hit-indexed enumeration. In particular, every vertex on the limiting lower
outer-face chain, defined as an endpoint occurring in a finite LL or LR stage
list, is covered (`kmswStage_LL_eq` and `kmswStage_LR_eq`, -/
theorem boundaryVertex_covers_lowerBoundary (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : ℕ)
    (hv : ∃ n e, (e ∈ (kmswStage w n).LL ∨ e ∈ (kmswStage w n).LR) ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)) :
    ∃ k : ℤ, boundaryVertex w h k = v := by
  obtain ⟨n, e, he, hend⟩ := hv
  rcases he with heLL | heLR
  · rw [kmswStage_LL_eq] at heLL
    obtain ⟨m, hm, heq⟩ := List.mem_map.mp heLL
    have hm' := List.mem_reverse.mp hm
    have hcond : 0 < m ∧ ∀ j < m, L w m < L w j :=
      of_decide_eq_true (List.mem_filter.mp hm').2
    have hmle : m ≤ n := by
      have := List.mem_range.mp (List.mem_filter.mp hm').1
      omega
    let q := L w m
    have hq : q ≤ -1 := by
      have hzero : L w 0 = 0 := by simp [L]
      have hrec0 := hcond.2 0 (by omega)
      dsimp [q]
      omega
    have htime : boundaryHitTime w h q = m :=
      boundaryHitTime_eq_left_record w h hq rfl (by simpa [q] using hcond.2)
    have hleft : (kmswStage w m).west (kmswLLCreatedEdge w m) = boundaryVertex w h q ∧
        (kmswStage w m).east (kmswLLCreatedEdge w m) = boundaryVertex w h (q + 1) ∧
        (kmswStage w m).present (kmswLLCreatedEdge w m) = false := by
      simpa [htime] using boundaryVertex_left_missing_edge w h hq
    have heq' : e = kmswLLCreatedEdge w m := by simpa using heq.symm
    have hnextPositive : 0 < (kmswStage w m).nextEdge := by
      have hmono := kmswStage_nextEdge_mono w (Nat.zero_le m)
      simp [kmswStage, kmswInit] at hmono
      omega
    have hebound : kmswLLCreatedEdge w m < (kmswStage w m).nextEdge := by
      dsimp [kmswLLCreatedEdge]
      omega
    have hstable := kmswStage_endpoints_stable w hmle hebound
    rcases hend with hwest | heast
    · refine ⟨q, ?_⟩
      calc
        boundaryVertex w h q = (kmswStage w m).west (kmswLLCreatedEdge w m) := hleft.1.symm
        _ = (kmswStage w n).west e := by rw [heq']; exact hstable.1.symm
        _ = v := hwest
    · refine ⟨q + 1, ?_⟩
      calc
        boundaryVertex w h (q + 1) = (kmswStage w m).east (kmswLLCreatedEdge w m) := hleft.2.1.symm
        _ = (kmswStage w n).east e := by rw [heq']; exact hstable.2.symm
        _ = v := heast
  · rw [kmswStage_LR_eq] at heLR
    obtain ⟨m, hm, heq⟩ := List.mem_map.mp heLR
    have hrecord : ∀ j < m, R w m < R w j := of_decide_eq_true (List.mem_filter.mp hm).2
    have hmle : m ≤ n := by
      have := List.mem_range.mp (List.mem_filter.mp hm).1
      omega
    by_cases hm0 : m = 0
    · subst m
      have hroot := boundaryVertex_root_edge w h
      have heq' : e = 0 := by simpa [act, kmswStage, kmswInit] using heq.symm
      have hebound : e < (kmswStage w 0).nextEdge := by simp [heq', kmswStage, kmswInit]
      have hstable := kmswStage_endpoints_stable w hmle hebound
      rcases hend with hwest | heast
      · refine ⟨0, ?_⟩
        rw [boundaryVertex_zero]
        calc
          0 = (kmswStage w 0).west e := by rw [heq']; rfl
          _ = (kmswStage w n).west e := hstable.1.symm
          _ = v := hwest
      · refine ⟨1, ?_⟩
        rw [boundaryVertex_one]
        calc
          1 = (kmswStage w 0).east e := by rw [heq']; rfl
          _ = (kmswStage w n).east e := hstable.2.symm
          _ = v := heast
    · have hzero : R w 0 = 0 := by simp [R]
      have hrecord0 := hrecord 0 (by omega)
      let q := -R w m
      have hq : 1 ≤ q := by dsimp [q]; omega
      have hvalue : R w m = -q := by dsimp [q]; omega
      obtain ⟨N, hNbound, hN⟩ := boundaryVertex_right_edge w h hq
      have htime : boundaryHitTime w h q = m :=
        boundaryHitTime_eq_right_record w h hq hvalue hrecord
      have hqN : m ≤ N := by rw [← htime]; exact hNbound
      have hstableMN := kmswStage_endpoints_stable w hmle
        (act_lt_nextEdge w (Nat.le_refl m))
      have hstableMN' := kmswStage_endpoints_stable w hqN
        (act_lt_nextEdge w (Nat.le_refl m))
      have hNedge := hN N le_rfl
      have heq' : e = act w m := by simpa using heq.symm
      rcases hend with hwest | heast
      · refine ⟨q, ?_⟩
        calc
          boundaryVertex w h q = (kmswStage w N).west (act w m) := by
            rw [← htime]
            exact (hNedge.2.2.1).symm
          _ = (kmswStage w m).west (act w m) := hstableMN'.1
          _ = (kmswStage w n).west e := by rw [heq']; exact hstableMN.1.symm
          _ = v := hwest
      · refine ⟨q + 1, ?_⟩
        calc
          boundaryVertex w h (q + 1) = (kmswStage w N).east (act w m) := by
            rw [← htime]
            exact (hNedge.2.2.2).symm
          _ = (kmswStage w m).east (act w m) := hstableMN'.2
          _ = (kmswStage w n).east e := by rw [heq']; exact hstableMN.2.symm
          _ = v := heast

/-- Almost surely, the shifted iid KMSW code has the full hit-indexed lower
boundary enumeration: positive indices form the present LR chain, negative
indices use the missing LL chain, the indexing is injective, and every vertex
incident to a finite LL/LR boundary edge is covered. The sole probabilistic
input is `iidCodes_ae_boundaryHitWitnesses`; no Pitman or UIQBOT code is used -/
theorem iidCodes_ae_boundaryEnumeration :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        Function.Injective (boundaryVertex (fun i => ω (i + 1)) h) ∧
        (kmswStage (fun i => ω (i + 1)) 0).LR = [0] ∧
        (kmswStage (fun i => ω (i + 1)) 0).west 0 =
          boundaryVertex (fun i => ω (i + 1)) h 0 ∧
        (kmswStage (fun i => ω (i + 1)) 0).east 0 =
          boundaryVertex (fun i => ω (i + 1)) h 1 ∧
        (kmswStage (fun i => ω (i + 1)) 0).present 0 = true ∧
        (∀ k : ℤ, 1 ≤ k →
          ∃ N, boundaryHitTime (fun i => ω (i + 1)) h k ≤ N ∧
            ∀ n, N ≤ n →
              act (fun i => ω (i + 1))
                  (boundaryHitTime (fun i => ω (i + 1)) h k) ∈
                (kmswStage (fun i => ω (i + 1)) n).LR ∧
              (kmswStage (fun i => ω (i + 1)) n).present
                  (act (fun i => ω (i + 1))
                    (boundaryHitTime (fun i => ω (i + 1)) h k)) = true ∧
              (kmswStage (fun i => ω (i + 1)) n).west
                  (act (fun i => ω (i + 1))
                    (boundaryHitTime (fun i => ω (i + 1)) h k)) =
                boundaryVertex (fun i => ω (i + 1)) h k ∧
              (kmswStage (fun i => ω (i + 1)) n).east
                  (act (fun i => ω (i + 1))
                    (boundaryHitTime (fun i => ω (i + 1)) h k)) =
                boundaryVertex (fun i => ω (i + 1)) h (k + 1)) ∧
        (∀ k : ℤ, k ≤ -1 →
          let e := kmswLLCreatedEdge (fun i => ω (i + 1))
            (boundaryHitTime (fun i => ω (i + 1)) h (k - 1))
          (kmswStage (fun i => ω (i + 1))
              (boundaryHitTime (fun i => ω (i + 1)) h (k - 1))).west e =
              boundaryVertex (fun i => ω (i + 1)) h (k - 1) ∧
            (kmswStage (fun i => ω (i + 1))
              (boundaryHitTime (fun i => ω (i + 1)) h (k - 1))).east e =
              boundaryVertex (fun i => ω (i + 1)) h k ∧
            (kmswStage (fun i => ω (i + 1))
              (boundaryHitTime (fun i => ω (i + 1)) h (k - 1))).present e = false) ∧
        (∀ v : ℕ,
          (∃ n e, (e ∈ (kmswStage (fun i => ω (i + 1)) n).LL ∨
              e ∈ (kmswStage (fun i => ω (i + 1)) n).LR) ∧
            ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
              (kmswStage (fun i => ω (i + 1)) n).east e = v)) →
          ∃ k : ℤ, boundaryVertex (fun i => ω (i + 1)) h k = v) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω hω
  obtain ⟨h1, h2, h3, h4⟩ := boundaryVertex_root_edge (fun i => ω (i + 1)) hω
  exact ⟨hω,
    boundaryVertex_injective _ hω,
    h1, h2, h3, h4,
    (fun k hk => boundaryVertex_right_edge _ hω hk),
    (fun k hk => boundaryVertex_left_consecutive _ hω hk),
    (fun v hv => boundaryVertex_covers_lowerBoundary _ hω v hv)⟩

end DirectedDistances.KMSW
