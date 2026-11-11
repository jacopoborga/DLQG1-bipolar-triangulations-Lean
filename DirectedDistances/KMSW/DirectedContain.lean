module

public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.BoundaryRecordsMissing
public import DirectedDistances.RandomWalk.FutureCodesAtHits
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Hit-indexed vertices and their iid futures

Helpers toward `eqn-bdy-vertex-hit` / `eqn-bdy-vertex-kmsw` and the law part of
map. The code sequence convention is `w i = ω (i + 1)`; no Pitman transform is used.

Scope. `boundaryHitTime` / `boundaryVertex` are DEFINED by the first coordinate hits that
`eqn-bdy-vertex-kmsw` predicts (`x₀ = 0`, `x₁ = 1`; otherwise the active initial vertex at the
first hit of `R = -k` for `k ≥ 1`, resp. of `L = k` for `k ≤ -1`). This file does NOT prove that
these vertices are the boundary vertices of `M_{0,∞}` in directed order (the source's
definition, from which it derives `eqn-bdy-vertex-kmsw`). It also does not prove the
directed-path containment of `lem-directed-contain`, nor the bridge between `boundaryHitTime`
and `RandomWalk.codeSndFirstHit` / `codeFstFirstHit`. What is proved: the first-visit property
(the vertex is not an earlier active initial vertex), endpoint stability, the identification
`x₁ = 1` with the active initial vertex at the first hit of `R = -1`, the iid law of the future
codes at a first hit, and a.s. existence of all hits. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open scoped Classical

/-- The explicit coordinate-hit hypotheses needed to define the hit-indexed vertices -/
structure BoundaryHitWitnesses (w : ℕ → Fin 3) : Prop where
  rightHit : ∀ k : ℤ, 1 ≤ k → ∃ n, R w n = -k
  leftHit : ∀ k : ℤ, k ≤ -1 → ∃ n, L w n = k

/-- DEFINED as the first hit time of the coordinate level that `eqn-bdy-vertex-kmsw`
`τ_k` (defined via the directed-order boundary vertices) is not proved here. The definition takes
actual hit witnesses and therefore has no default value. -/
@[expose] noncomputable def boundaryHitTime (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ := by
  classical
  by_cases hk0 : k = 0
  · exact 0
  · by_cases hkpos : 0 < k
    · exact Nat.find (h.rightHit k (by omega))
    · exact Nat.find (h.leftHit k (by omega))

/-- Hit-indexed vertex, DEFINED by the hits: `x₀ = 0`, `x₁ = 1`, and for all other indices
the active initial vertex at the first coordinate hit of `boundaryHitTime`
vertices of `M_{0,∞}` in directed order is not proved here. -/
@[expose] noncomputable def boundaryVertex (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ := by
  classical
  by_cases hk0 : k = 0
  · exact 0
  · by_cases hk1 : k = 1
    · exact 1
    · exact activeInitial w (boundaryHitTime w h k)

theorem boundaryVertex_zero (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    boundaryVertex w h 0 = 0 := by
  simp [boundaryVertex]

theorem boundaryVertex_one (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    boundaryVertex w h 1 = 1 := by
  simp [boundaryVertex]

/-- Definitional unfolding: away from `k = 0, 1`, the hit-indexed vertex is the active initial
vertex at its hit time. -/
theorem boundaryVertex_eq_activeInitial (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    boundaryVertex w h k = activeInitial w (boundaryHitTime w h k) := by
  simp [boundaryVertex, hk0, hk1]

/-- Endpoints of an already allocated active edge are stable at all later -/
theorem boundaryHit_activeInitial_stable (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    {m : ℕ} (hm : boundaryHitTime w h k ≤ m) :
    (kmswStage w m).west (act w (boundaryHitTime w h k)) =
      boundaryVertex w h k := by
  rw [boundaryVertex_eq_activeInitial w h hk0 hk1]
  exact (kmswStage_endpoints_stable w hm
    (act_lt_nextEdge w (Nat.le_refl _))).1.trans
      (CutConverse.activeInitial_eq w (boundaryHitTime w h k)).symm

theorem boundaryHitTime_right_spec (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    R w (boundaryHitTime w h k) = -k := by
  unfold boundaryHitTime
  simp only [dif_neg (by omega : k ≠ 0), dif_pos (by omega : 0 < k)]
  exact Nat.find_spec (h.rightHit k hk)

theorem boundaryHitTime_left_spec (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    L w (boundaryHitTime w h k) = k := by
  unfold boundaryHitTime
  simp only [dif_neg (by omega : k ≠ 0), dif_neg (by omega : ¬ 0 < k)]
  exact Nat.find_spec (h.leftHit k hk)

theorem boundaryHitTime_zero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : boundaryHitTime w h 0 = 0 := by
  simp [boundaryHitTime]

private theorem boundaryHitTime_right_eq_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
  unfold boundaryHitTime
  simp only [dif_neg (by omega : k ≠ 0), dif_pos (by omega : 0 < k)]

private theorem boundaryHitTime_left_eq_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
  unfold boundaryHitTime
  simp only [dif_neg (by omega : k ≠ 0), dif_neg (by omega : ¬ 0 < k)]

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
    ∀ j < Nat.find h, a ≤ f j - 1 := by
  intro j hj
  by_contra hnot
  have hjle : f j ≤ a := by omega
  obtain ⟨m, hmj, hma⟩ := exists_coordinate_eq_of_le f hstep hzero ha hjle
  have hmn : m < Nat.find h := hmj.trans_lt hj
  exact (Nat.find_min h hmn) hma

private theorem root_right_hit_initial (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    activeInitial w (boundaryHitTime w h 1) = 1 := by
  let n := Nat.find (h.rightHit 1 (by norm_num))
  have htime : boundaryHitTime w h 1 = n := by
    unfold boundaryHitTime
    simp [n, show (1 : ℤ) ≠ 0 by norm_num, show (0 : ℤ) < 1 by norm_num]
  have hhit : R w n = -1 := by
    exact Nat.find_spec (h.rightHit 1 (by norm_num))
  have hstrict : ∀ j < n, -1 ≤ R w j - 1 := by
    have h0 : R w 0 = 0 := by simp [R]
    have hs := first_coordinate_hit_is_strict_record (R w)
      (coordinate_succ_ge_R w) h0 (by norm_num) (h.rightHit 1 (by norm_num))
    simpa [n] using hs
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hhit
    simp [R] at hhit
  let m := n - 1
  have hnm : n = m + 1 := by dsimp [m]; omega
  have hm_lt : m < n := by omega
  have hprevlo : 0 ≤ R w m := by
    have := hstrict m hm_lt
    omega
  have hRstep : R w n = R w m +
      (RandomWalk.lazyTwoDimensionalStep (w m)).2 := by
    rw [hnm]
    exact Finset.sum_range_succ _ _
  have hstephi : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w m)).2 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    split_ifs <;> omega
  have hprevhi : R w m ≤ 0 := by rw [hRstep] at hhit; omega
  have hprev : R w m = 0 := by omega
  have hstep : (RandomWalk.lazyTwoDimensionalStep (w m)).2 = -1 := by
    rw [hRstep, hprev] at hhit
    simpa using hhit
  have hw : w m = 2 := by
    have hcode : (w m).val = 2 := by
      have hval := (w m).isLt
      simp only [RandomWalk.lazyTwoDimensionalStep] at hstep
      split_ifs at hstep <;> omega
    exact Fin.ext hcode
  have hmin : minR w m = 0 := by
    obtain ⟨i, him, hi⟩ := runningMin_attained (R w) m
    change minR w m = R w i at hi
    have hlow : 0 ≤ R w i := by
      have := hstrict i (by omega)
      omega
    have hle := runningMin_le (R w) m 0 (Nat.zero_le _)
    change minR w m ≤ R w 0 at hle
    simp [R] at hle
    omega
  have hURlen := kmswStage_UR_length w m
  have hURcast : ((kmswStage w m).UR.length : ℤ) = 0 := by
    rw [hURlen, hprev, hmin]
    norm_num
  have hURlen0 : (kmswStage w m).UR.length = 0 := by
    exact_mod_cast hURcast
  have hUR : (kmswStage w m).UR = [] := List.length_eq_zero_iff.mp hURlen0
  have hLRlen := kmswStage_LR_length w m
  have hLRcast : ((kmswStage w m).LR.length : ℤ) = 1 := by
    rw [hLRlen, hmin]
    norm_num
  have hLRlen1 : (kmswStage w m).LR.length = 1 := by
    exact_mod_cast hLRcast
  have hrootmem : act w 0 ∈ (kmswStage w m).LR := by
    rw [kmswStage_LR_eq]
    apply List.mem_map.mpr
    refine ⟨0, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, rfl⟩
    simp
  have hLR : (kmswStage w m).LR = [act w 0] := by
    cases hlr : (kmswStage w m).LR with
    | nil => simp [hlr] at hLRlen1
    | cons e es =>
      have hes : es = [] := by
        have hlen : es.length + 1 = 1 := by
          simpa only [hlr, List.length_cons] using hLRlen1
        exact List.length_eq_zero_iff.mp (by omega)
      subst es
      have he : e = act w 0 := by
        have hrootmem' : act w 0 = e := by simpa [hlr] using hrootmem
        exact hrootmem'.symm
      simp [he]
  have hEast : (kmswStage w m).east (act w m) = 1 := by
    have h := CutConverse.east_active_eq_LR_terminal_of_UR_nil w m hUR
    rw [hLR] at h
    simp only [List.getLast?_singleton, Option.map_some] at h
    have h' := Option.some.inj h
    have hroot : (kmswStage w m).east (act w 0) = 1 := by
      have hs := (kmswStage_endpoints_stable w (Nat.zero_le m)
        (act_lt_nextEdge w (Nat.le_refl 0))).2
      simpa [kmswStage, kmswInit, act] using hs
    rw [hroot] at h'
    simpa [act] using h'
  have hstage : kmswStage w n = kmswStepOfStep (kmswStage w m) .down := by
    rw [hnm]
    change kmswStep (kmswStage w m) (w m) = _
    rw [hw]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hinit : activeInitial w n = (kmswStage w m).east (act w m) := by
    rw [CutConverse.activeInitial_eq]
    change (kmswStage w n).west (kmswStage w n).active = _
    rw [hstage]
    change (kmswStepOfStep (kmswStage w m) .down).west
      (kmswStepOfStep (kmswStage w m) .down).active = _
    simp [kmswStepOfStep, hUR, State.addEdge]
    simp only [act]
  rw [htime, hinit, hEast]

/-- The root terminal vertex is the initial vertex at the first hit of `R=-1`
(`eqn-bdy-vertex-hit` and `eqn-bdy-vertex-kmsw`, -/
theorem boundaryVertex_one_eq_activeInitial_hit (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    boundaryVertex w h 1 = activeInitial w (boundaryHitTime w h 1) := by
  rw [boundaryVertex_one, root_right_hit_initial]

/-- For `k ≥ 1` the hit-indexed vertex is the active initial vertex at its first
right-coordinate hit. This is definitional for `k ≥ 2`. For `k = 1` it is the genuine
identification `x₁ = 1` of `root_right_hit_initial` (`eqn-bdy-vertex-kmsw`, -/
theorem boundaryVertex_right_hit_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryVertex w h k = activeInitial w (boundaryHitTime w h k) := by
  by_cases hk1 : k = 1
  · subst k
    exact boundaryVertex_one_eq_activeInitial_hit w h
  · exact boundaryVertex_eq_activeInitial w h (by omega) hk1

/-- Definitional unfolding for `k ≤ -1`: the hit-indexed vertex is the active initial vertex
at its first left-coordinate hit. -/
theorem boundaryVertex_left_hit_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryVertex w h k = activeInitial w (boundaryHitTime w h k) := by
  exact boundaryVertex_eq_activeInitial w h (by omega) (by omega)

/-- The endpoint at a coordinate-hit time remains the same in every later
finite stage (`remark-kmsw-infinite`, -/
theorem boundaryHit_activeInitial_stable_of_ne_zero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk0 : k ≠ 0)
    {m : ℕ} (hm : boundaryHitTime w h k ≤ m) :
    (kmswStage w m).west (act w (boundaryHitTime w h k)) =
      boundaryVertex w h k := by
  have hx : boundaryVertex w h k = activeInitial w (boundaryHitTime w h k) := by
    by_cases hkpos : 1 ≤ k
    · exact boundaryVertex_right_hit_eq w h hkpos
    · exact boundaryVertex_left_hit_eq w h (by omega)
  calc
    (kmswStage w m).west (act w (boundaryHitTime w h k)) =
        (kmswStage w (boundaryHitTime w h k)).west
          (act w (boundaryHitTime w h k)) :=
      (kmswStage_endpoints_stable w hm
        (act_lt_nextEdge w (Nat.le_refl _))).1
    _ = activeInitial w (boundaryHitTime w h k) :=
      (CutConverse.activeInitial_eq w (boundaryHitTime w h k)).symm
    _ = boundaryVertex w h k := hx.symm

/-- For `k ≥ 1` the hit-indexed vertex is not the active initial vertex at any time before its -/
theorem boundaryVertex_first_visit_right (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∀ j, j < boundaryHitTime w h k →
      boundaryVertex w h k ≠ activeInitial w j := by
  let n := boundaryHitTime w h k
  have htime : n = Nat.find (h.rightHit k hk) :=
    boundaryHitTime_right_eq_find w h hk
  have hzero : R w 0 = 0 := by simp [R]
  have hstrict' := first_coordinate_hit_is_strict_record (R w)
    (coordinate_succ_ge_R w) hzero (by omega : -k < 0) (h.rightHit k hk)
  have hstrict : ∀ j < n, R w n ≤ R w j - 1 := by
    intro j hj
    calc
      R w n = -k := boundaryHitTime_right_spec w h hk
      _ ≤ R w j - 1 := hstrict' j (by simpa [htime] using hj)
  have hfirst := activeInitial_ne_of_right_record w n hstrict
  have hx : boundaryVertex w h k = activeInitial w n := by
    by_cases hk1 : k = 1
    · subst k
      exact boundaryVertex_one_eq_activeInitial_hit w h
    · exact boundaryVertex_eq_activeInitial w h (by omega) hk1
  intro j hj
  rw [hx]
  exact (hfirst j (by simpa [n] using hj)).symm

/-- For `k ≤ -1` the hit-indexed vertex is not the active initial vertex at any time before -/
theorem boundaryVertex_first_visit_left (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j, j < boundaryHitTime w h k →
      boundaryVertex w h k ≠ activeInitial w j := by
  let n := boundaryHitTime w h k
  have htime : n = Nat.find (h.leftHit k hk) :=
    boundaryHitTime_left_eq_find w h hk
  have hzero : L w 0 = 0 := by simp [L]
  have hstrict' := first_coordinate_hit_is_strict_record (L w)
    (coordinate_succ_ge_L w) hzero (by omega : k < 0) (h.leftHit k hk)
  have hstrict : ∀ j < n, k ≤ L w j - 1 := by
    intro j hj
    exact hstrict' j (by simpa [htime] using hj)
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
    have := hstrict m hm_lt
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
      simp only [RandomWalk.lazyTwoDimensionalStep, Prod.fst] at hstep
      omega
    exact Fin.ext hval
  have hmin : minL w m = k + 1 := by
    obtain ⟨i, him, hi⟩ := runningMin_attained (L w) m
    change minL w m = L w i at hi
    have hlow : k + 1 ≤ L w i := by
      have := hstrict i (by omega)
      omega
    have hle := runningMin_le (L w) m m (le_refl m)
    change minL w m ≤ L w m at hle
    rw [hprev] at hle
    omega
  have hULcast : ((kmswStage w m).UL.length : ℤ) = 1 := by
    rw [kmswStage_UL_length, hprev, hmin]
    norm_num
  have hULlen1 : (kmswStage w m).UL.length = 1 := by exact_mod_cast hULcast
  obtain ⟨es, hes⟩ := kmswStage_UL_last w m
  have hesEmpty : es = [] := by
    have hlen : es.length + 1 = 1 := by
      rw [hes] at hULlen1
      simpa only [List.length_append, List.length_cons, List.length_nil] using hULlen1
    exact List.length_eq_zero_iff.mp (by omega)
  have hUL : (kmswStage w m).UL = [(kmswStage w m).active] := by
    rw [hes, hesEmpty]
    rfl
  have hdrop : (kmswStage w m).UL.dropLast.reverse = [] := by
    rw [hUL]
    rfl
  have hstage : kmswStage w n = kmswStepOfStep (kmswStage w m) .left := by
    rw [hnm]
    change kmswStep (kmswStage w m) (w m) = _
    rw [hw]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hdrop]
  have hnew : activeInitial w n = (kmswStage w m).nextVertex := by
    rw [CutConverse.activeInitial_eq]
    change (kmswStage w n).west (kmswStage w n).active = _
    rw [hstage]
    change (kmswStepOfStep (kmswStage w m) .left).west
      (kmswStepOfStep (kmswStage w m) .left).active = _
    simp [kmswStepOfStep, hdrop, State.addEdge]
  have hx : boundaryVertex w h k = (kmswStage w m).nextVertex := by
    rw [boundaryVertex_eq_activeInitial w h (by omega) (by omega), hnew]
  have hfirst : ∀ j < n, activeInitial w j ≠ activeInitial w n := by
    intro j hj heq
    have hbound := kmswStage_endpoints_lt_nextVertex w m (act w j)
      (act_lt_nextEdge w (by omega : j ≤ m))
    have hstable := (kmswStage_endpoints_stable w (by omega : j ≤ m)
      (act_lt_nextEdge w (Nat.le_refl j))).1
    have hAI : activeInitial w j = (kmswStage w m).west (act w j) := by
      rw [CutConverse.activeInitial_eq, ← hstable]
    rw [hAI, hnew] at heq
    have hlt : activeInitial w j < (kmswStage w m).nextVertex := by
      rw [hAI]
      exact hbound.1
    omega
  intro j hj
  rw [hx]
  intro heq
  apply hfirst j (by simpa [n] using hj)
  calc
    activeInitial w j = (kmswStage w m).nextVertex := heq.symm
    _ = activeInitial w n := hnew.symm

/-- For the iid code law, the shifted source-code sequence at a second-coordinate
hit has the original law (law part of `lem-directed-contain`, -/
theorem iidCodeMeasure_map_futureCodes_at_rightHit (k : ℤ) :
    RandomWalk.iidCodeMeasure.map
        (fun ω => fun i => ω ((RandomWalk.codeSndFirstHit (-k) ω).toNat + i + 1)) =
      RandomWalk.iidCodeMeasure.map (fun ω => fun i => ω (i + 1)) := by
  have h := RandomWalk.map_comp_codeShift_codeSndFirstHit (-k)
    (F := fun ω => fun i => ω (i + 1)) (by fun_prop)
  simpa [RandomWalk.codeShift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- For the iid code law, the shifted source-code sequence at a first-coordinate
hit has the original law (law part of `lem-directed-contain`, -/
theorem iidCodeMeasure_map_futureCodes_at_leftHit (k : ℤ) :
    RandomWalk.iidCodeMeasure.map
        (fun ω => fun i => ω ((RandomWalk.codeFstFirstHit k ω).toNat + i + 1)) =
      RandomWalk.iidCodeMeasure.map (fun ω => fun i => ω (i + 1)) := by
  have h := RandomWalk.map_comp_codeShift_codeFstFirstHit k
    (F := fun ω => fun i => ω (i + 1)) (by fun_prop)
  simpa [RandomWalk.codeShift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Any measurable object built from the shifted future-code sequence has its
original pushforward law (law part of `lem-directed-contain`, -/
theorem iidCodeMeasure_map_futureObject_at_rightHit {β : Type*}
    [MeasurableSpace β] (F : (ℕ → Fin 3) → β) (hF : Measurable F) (k : ℤ) :
    RandomWalk.iidCodeMeasure.map
        (fun ω => F (fun i => ω ((RandomWalk.codeSndFirstHit (-k) ω).toNat + i + 1))) =
      RandomWalk.iidCodeMeasure.map (fun ω => F (fun i => ω (i + 1))) := by
  let future : (ℕ → Fin 3) → (ℕ → Fin 3) := fun ω i => ω (i + 1)
  have hfuture : Measurable future := by fun_prop
  have hcomp : Measurable (fun ω => F (future ω)) := hF.comp hfuture
  have h := RandomWalk.map_comp_codeShift_codeSndFirstHit (-k)
    (F := fun ω => F (future ω)) hcomp
  simpa [future, RandomWalk.codeShift, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using h

/-- Any measurable object built from the shifted future-code sequence at a
first-coordinate hit has its original pushforward law -/
theorem iidCodeMeasure_map_futureObject_at_leftHit {β : Type*}
    [MeasurableSpace β] (F : (ℕ → Fin 3) → β) (hF : Measurable F) (k : ℤ) :
    RandomWalk.iidCodeMeasure.map
        (fun ω => F (fun i => ω ((RandomWalk.codeFstFirstHit k ω).toNat + i + 1))) =
      RandomWalk.iidCodeMeasure.map (fun ω => F (fun i => ω (i + 1))) := by
  let future : (ℕ → Fin 3) → (ℕ → Fin 3) := fun ω i => ω (i + 1)
  have hfuture : Measurable future := by fun_prop
  have hcomp : Measurable (fun ω => F (future ω)) := hF.comp hfuture
  have h := RandomWalk.map_comp_codeShift_codeFstFirstHit k
    (F := fun ω => F (future ω)) hcomp
  simpa [future, RandomWalk.codeShift, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using h

/-- Almost surely, the positive boundary coordinate hit exists at each fixed -/
theorem iidCodes_ae_rightBoundaryHit (k : ℤ) (_hk : 1 ≤ k) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ n, R (fun i => ω (i + 1)) n = -k := by
  filter_upwards [RandomWalk.ae_exists_codeWalk_snd_eq_int (-k)] with ω hω
  obtain ⟨n, hn⟩ := hω
  exact ⟨n, by
    simpa [R, RandomWalk.codeWalk, Prod.snd_sum] using hn⟩

/-- Almost surely, the negative boundary coordinate hit exists at each fixed -/
theorem iidCodes_ae_leftBoundaryHit (k : ℤ) (_hk : k ≤ -1) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ n, L (fun i => ω (i + 1)) n = k := by
  filter_upwards [RandomWalk.ae_exists_codeWalk_fst_eq_int k] with ω hω
  obtain ⟨n, hn⟩ := hω
  exact ⟨n, by
    simpa [L, RandomWalk.codeWalk, Prod.fst_sum] using hn⟩

/-- Almost surely every integer coordinate level needed for the hit-indexed vertices is hit.
The countable intersection is taken before defining the choice-based vertices -/
theorem iidCodes_ae_boundaryHitWitnesses :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      BoundaryHitWitnesses (fun i => ω (i + 1)) := by
  have hR : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ k : ℤ, ∃ n, R (fun i => ω (i + 1)) n = -k := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [RandomWalk.ae_exists_codeWalk_snd_eq_int (-k)] with ω hω
    obtain ⟨n, hn⟩ := hω
    exact ⟨n, by simpa [R, RandomWalk.codeWalk, Prod.snd_sum] using hn⟩
  have hL : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ k : ℤ, ∃ n, L (fun i => ω (i + 1)) n = k := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [RandomWalk.ae_exists_codeWalk_fst_eq_int k] with ω hω
    obtain ⟨n, hn⟩ := hω
    exact ⟨n, by simpa [L, RandomWalk.codeWalk, Prod.fst_sum] using hn⟩
  filter_upwards [hR, hL] with ω hωL hωR
  exact ⟨fun k hk => hωL k, fun k hk => hωR k⟩

end DirectedDistances.KMSW
