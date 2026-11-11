module

public import DirectedDistances.RandomWalk.ConditionedStrongMarkov

/-! # First-hit barrier decomposition

decomposition of the barrier conditions at the first hit of R = −r (r ≥ 1)
into a measurable event of the uncentered future path; the renewal-time selection
paper result. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open scoped ENNReal

/-- The path stays to the right of its first-coordinate value at the first hit
of second-coordinate level `-s`. -/
@[expose] def firstHitBarrier (s : ℕ) (p : ℕ → ℤ × ℤ) : Prop :=
  ∃ t : ℕ, conditionedSecondCoordinateFirstHit s p = (t : ℕ∞) ∧
    ∀ n ≥ t, (p t).1 ≤ (p n).1

/-- The future-path event requiring the level-`ell` lower bound and excluding
later successful barriers through level `k`. -/
@[expose] def barrierFutureEvent (ell r k : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {q | (∀ n, (ell : ℤ) ≤ (q n).1) ∧
    ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s q}

private theorem firstHit_eq_nat_iff (r k : ℕ) (p : ℕ → ℤ × ℤ) :
    conditionedSecondCoordinateFirstHit r p = (k : ℕ∞) ↔
      (p k).2 = -(r : ℤ) ∧ ∀ j < k, (p j).2 ≠ -(r : ℤ) := by
  unfold conditionedSecondCoordinateFirstHit
  by_cases h : ∃ n, (p n).2 = -(r : ℤ)
  · rw [dite_eq_left h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [dite_eq_right h]
    constructor
    · intro he
      exact absurd he (ENat.top_ne_natCast k)
    · rintro ⟨hk, _⟩
      exact absurd ⟨k, hk⟩ h

private theorem measurableSet_of_conditionedVectorPast (k : ℕ)
    (C : Set (ℕ → ℤ × ℤ)) (hC : MeasurableSet[conditionedVectorPast k] C) :
    MeasurableSet C := by
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hC
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix k)

private theorem measurableSet_firstHit_level (s t : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      conditionedSecondCoordinateFirstHit s p = (t : ℕ∞)} := by
  exact measurableSet_of_conditionedVectorPast t _
    (measurableSet_conditionedVectorPast_firstHit_eq s t)

private theorem exists_level_hit_of_le (p : ℕ → ℤ × ℤ) (r n : ℕ)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0) (hn : (p n).2 ≤ -(r : ℤ)) :
    ∃ j ≤ n, (p j).2 = -(r : ℤ) := by
  induction n with
  | zero =>
      by_cases hr : r = 0
      · subst r
        exact ⟨0, le_rfl, by simpa using h0⟩
      · have : (0 : ℤ) ≤ -(r : ℤ) := by simpa [h0] using hn
        omega
  | succ n ih =>
      by_cases hprev : (p n).2 ≤ -(r : ℤ)
      · obtain ⟨j, hj, hhit⟩ := ih hprev
        exact ⟨j, by omega, hhit⟩
      · have hhit : (p (n + 1)).2 = -(r : ℤ) := by
          have := hstep n
          omega
        exact ⟨n + 1, le_rfl, hhit⟩

private theorem firstHitBarrier_iff_at_time (s : ℕ) (p : ℕ → ℤ × ℤ)
    (t : ℕ) (hτ : conditionedSecondCoordinateFirstHit s p = (t : ℕ∞)) :
    firstHitBarrier s p ↔ ∀ n ≥ t, (p t).1 ≤ (p n).1 := by
  constructor
  · rintro ⟨u, hu, hbar⟩ n hn
    have hut : u = t := by exact_mod_cast hu.symm.trans hτ
    subst u
    exact hbar n hn
  · intro hbar
    exact ⟨t, hτ, hbar⟩

/-- First-hit times of deeper levels split into the first hit of `-r` and the
first such hit on the uncentered shifted path. -/
theorem conditionedSecondCoordinateFirstHit_shift_add
    (p : ℕ → ℤ × ℤ) (r s t : ℕ)
    (hstep : ∀ n, (p n).2 - 1 ≤ (p (n + 1)).2)
    (h0 : (p 0).2 = 0)
    (hτ : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞))
    (hrs : r ≤ s) :
    conditionedSecondCoordinateFirstHit s p =
      (t : ℕ∞) + conditionedSecondCoordinateFirstHit s (conditionedVectorShift t p) := by
  classical
  let q := conditionedVectorShift t p
  have hhit_r := (firstHit_eq_nat_iff r t p).mp hτ
  have hno_s : ∀ n < t, (p n).2 ≠ -(s : ℤ) := by
    intro n hnt hns
    obtain ⟨j, hjn, hjr⟩ := exists_level_hit_of_le p r n hstep h0 (by omega)
    have htj : t ≤ j := Nat.le_of_not_gt (fun hjt => hhit_r.2 j hjt hjr)
    omega
  have hshift_rep (n : ℕ) : q n = p (t + n) := by
    rfl
  by_cases hq : ∃ n, (q n).2 = -(s : ℤ)
  · let u := Nat.find hq
    have huHit : (q u).2 = -(s : ℤ) := Nat.find_spec hq
    have hno_q : ∀ j < u, (q j).2 ≠ -(s : ℤ) := by
      intro j hju hhit
      have hmin := Nat.find_min' hq hhit
      omega
    have huFirst : conditionedSecondCoordinateFirstHit s q = (u : ℕ∞) :=
      (firstHit_eq_nat_iff s u q).2 ⟨huHit, hno_q⟩
    have hhit_p : (p (t + u)).2 = -(s : ℤ) := by
      have h := huHit
      rw [hshift_rep] at h
      exact h
    have hno_p : ∀ n < t + u, (p n).2 ≠ -(s : ℤ) := by
      intro n hnv hhit
      by_cases hnt : n < t
      · exact hno_s n hnt hhit
      · have hnrep : n = t + (n - t) := by omega
        have hju : n - t < u := by omega
        have hqhit : (q (n - t)).2 = -(s : ℤ) := by
          rw [hshift_rep, ← hnrep]
          exact hhit
        exact hno_q (n - t) hju hqhit
    have hpFirst : conditionedSecondCoordinateFirstHit s p =
        ((t + u : ℕ) : ℕ∞) :=
      (firstHit_eq_nat_iff s (t + u) p).2 ⟨hhit_p, hno_p⟩
    rw [hpFirst, huFirst]
    exact (ENat.natCast_add t u).symm
  · have hqnone : ∀ n, (q n).2 ≠ -(s : ℤ) := by
      intro n hn
      exact hq ⟨n, hn⟩
    have hpnone : ∀ n, (p n).2 ≠ -(s : ℤ) := by
      intro n hn
      by_cases hnt : n < t
      · exact hno_s n hnt hn
      · have hnrep : n = t + (n - t) := by omega
        have hqhit : (q (n - t)).2 = -(s : ℤ) := by
          rw [hshift_rep, ← hnrep]
          exact hn
        exact hqnone (n - t) hqhit
    have hpnoneEx : ¬ ∃ n, (p n).2 = -(s : ℤ) := by
      rintro ⟨n, hn⟩
      exact hpnone n hn
    have hqnoneEx : ¬ ∃ n, (q n).2 = -(s : ℤ) := by
      rintro ⟨n, hn⟩
      exact hqnone n hn
    have hpTop : conditionedSecondCoordinateFirstHit s p = ⊤ := by
      unfold conditionedSecondCoordinateFirstHit
      rw [dite_eq_right hpnoneEx]
    have hqTop : conditionedSecondCoordinateFirstHit s q = ⊤ := by
      unfold conditionedSecondCoordinateFirstHit
      rw [dite_eq_right hqnoneEx]
    rw [hpTop, hqTop]
    simp

/-- The first-hit barrier is invariant under the uncentered shift at the first
hit of any shallower level. -/
theorem firstHitBarrier_shift_iff
    (p : ℕ → ℤ × ℤ) (r s t : ℕ)
    (hstep : ∀ n, (p n).2 - 1 ≤ (p (n + 1)).2)
    (h0 : (p 0).2 = 0)
    (hτ : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞))
    (hrs : r ≤ s) :
    firstHitBarrier s p ↔ firstHitBarrier s (conditionedVectorShift t p) := by
  constructor
  · rintro ⟨v, hv, hbar⟩
    have htimes := conditionedSecondCoordinateFirstHit_shift_add p r s t
      hstep h0 hτ hrs
    have hqne : conditionedSecondCoordinateFirstHit s
        (conditionedVectorShift t p) ≠ ⊤ := by
      intro htop
      rw [htimes, htop] at hv
      simp at hv
    obtain ⟨u, huRev⟩ := ENat.ne_top_iff_exists.mp hqne
    have hu : conditionedSecondCoordinateFirstHit s
        (conditionedVectorShift t p) = (u : ℕ∞) := huRev.symm
    have hvtime : v = t + u := by
      have heq : (v : ℕ∞) = ((t + u : ℕ) : ℕ∞) := by
        calc
          (v : ℕ∞) = conditionedSecondCoordinateFirstHit s p := hv.symm
          _ = (t : ℕ∞) + conditionedSecondCoordinateFirstHit s
                (conditionedVectorShift t p) := htimes
          _ = ((t + u : ℕ) : ℕ∞) := by simp [hu]
      exact_mod_cast heq
    refine ⟨u, hu, ?_⟩
    intro n hn
    have hlarge : v ≤ t + n := by omega
    have h := hbar (t + n) hlarge
    simpa [conditionedVectorShift, hvtime] using h
  · rintro ⟨u, hu, hbar⟩
    have htimes := conditionedSecondCoordinateFirstHit_shift_add p r s t
      hstep h0 hτ hrs
    have hpTime : conditionedSecondCoordinateFirstHit s p =
        ((t + u : ℕ) : ℕ∞) := by
      rw [htimes, hu]
      simp
    refine ⟨t + u, hpTime, ?_⟩
    intro n hn
    have hrep : n = t + (n - t) := by omega
    have hlarge : u ≤ n - t := by omega
    have h := hbar (n - t) hlarge
    change (p (t + u)).1 ≤ (p (t + (n - t))).1 at h
    rw [← hrep] at h
    exact h

/-- decomposition of the barrier conditions at the first hit of R = −r (r ≥ 1) into a
measurable event of the uncentered future path; the renewal-time selection T_{m_k} -/
theorem firstHitBarrier_positive_decomposition
    (p : ℕ → ℤ × ℤ) (ell r k t : ℕ)
    (hstep : ∀ n, (p n).2 - 1 ≤ (p (n + 1)).2)
    (h0 : (p 0).2 = 0) (_hr : 1 ≤ r)
    (hτ : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞))
    (hend : (p t).1 = (ell : ℤ)) :
    (firstHitBarrier r p ∧
      ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s p) ↔
      conditionedVectorShift t p ∈ barrierFutureEvent ell r k := by
  classical
  constructor
  · rintro ⟨hbar, hlater⟩
    have hbarAt := (firstHitBarrier_iff_at_time r p t hτ).mp hbar
    change (∀ n, (ell : ℤ) ≤
      (conditionedVectorShift t p n).1) ∧
      ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s
        (conditionedVectorShift t p) at ⊢
    constructor
    · intro n
      have hn := hbarAt (t + n) (by omega)
      rw [hend] at hn
      change (ell : ℤ) ≤ (conditionedVectorShift t p n).1
      exact hn
    · intro s hrs hsk hs
      apply hlater s hrs hsk
      exact (firstHitBarrier_shift_iff p r s t hstep h0 hτ (by omega)).2 hs
  · intro hfuture
    change (∀ n, (ell : ℤ) ≤
      (conditionedVectorShift t p n).1) ∧
      ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s
        (conditionedVectorShift t p) at hfuture
    constructor
    · refine ⟨t, hτ, ?_⟩
      intro n hn
      have h := hfuture.1 (n - t)
      have hrep : n = t + (n - t) := by omega
      change (ell : ℤ) ≤ (p (t + (n - t))).1 at h
      rw [← hrep] at h
      rw [← hend] at h
      exact h
    · intro s hrs hsk hs
      have hshifted :=
        (firstHitBarrier_shift_iff p r s t hstep h0 hτ (by omega)).1 hs
      exact hfuture.2 s hrs hsk hshifted

private theorem measurableSet_first_coordinate_barrier (t : ℕ) :
    MeasurableSet {q : ℕ → ℤ × ℤ | ∀ n ≥ t, (q t).1 ≤ (q n).1} := by
  rw [show {q : ℕ → ℤ × ℤ | ∀ n ≥ t, (q t).1 ≤ (q n).1} =
      ⋂ n : ℕ, if t ≤ n then {q : ℕ → ℤ × ℤ | (q t).1 ≤ (q n).1} else Set.univ by
    ext q
    simp]
  apply MeasurableSet.iInter
  intro n
  by_cases hn : t ≤ n
  · simpa [hn] using measurableSet_le
      (measurable_fst.comp (measurable_pi_apply t))
      (measurable_fst.comp (measurable_pi_apply n))
  · simp [hn]

/-- Every first-hit barrier event is measurable in the product σ-algebra. -/
theorem measurableSet_firstHitBarrier (s : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ | firstHitBarrier s p} := by
  rw [show {p : ℕ → ℤ × ℤ | firstHitBarrier s p} =
      ⋃ t : ℕ, {p | conditionedSecondCoordinateFirstHit s p = (t : ℕ∞) ∧
        ∀ n ≥ t, (p t).1 ≤ (p n).1} by
    ext p
    simp [firstHitBarrier]]
  apply MeasurableSet.iUnion
  intro t
  exact (measurableSet_firstHit_level s t).inter
    (measurableSet_first_coordinate_barrier t)

/-- The future event is measurable in the product σ-algebra. -/
theorem measurableSet_barrierFutureEvent (ell r k : ℕ) :
    MeasurableSet (barrierFutureEvent ell r k) := by
  change MeasurableSet
    ({p : ℕ → ℤ × ℤ | ∀ n, (ell : ℤ) ≤ (p n).1} ∩
      {p | ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s p})
  apply MeasurableSet.inter
  · rw [show {p : ℕ → ℤ × ℤ | ∀ n, (ell : ℤ) ≤ (p n).1} =
      ⋂ n : ℕ, {p : ℕ → ℤ × ℤ | (ell : ℤ) ≤ (p n).1} by
    ext p
    simp]
    apply MeasurableSet.iInter
    intro n
    exact measurableSet_le (measurable_const :
      Measurable fun _ : ℕ → ℤ × ℤ => (ell : ℤ))
      (measurable_fst.comp (measurable_pi_apply n))
  · rw [show {p : ℕ → ℤ × ℤ | ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s p} =
      ⋂ s : ℕ,
        if r < s then
          if s ≤ k then ({p : ℕ → ℤ × ℤ | firstHitBarrier s p} : Set _)ᶜ
            else Set.univ
        else Set.univ by
    ext p
    simp]
    apply MeasurableSet.iInter
    intro s
    by_cases hrs : r < s
    · by_cases hsk : s ≤ k
      · simpa [hrs, hsk] using (measurableSet_firstHitBarrier s).compl
      · simp [hrs, hsk]
    · simp [hrs]

end DirectedDistances.RandomWalk
