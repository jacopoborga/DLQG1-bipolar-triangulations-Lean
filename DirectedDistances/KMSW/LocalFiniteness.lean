module

public import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Local finiteness gate for KMSW stages

Helpers toward the infinite-map carrier gate in -/

public section
namespace DirectedDistances.KMSW

private theorem coord_R_succ (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem vertical_increment_nonneg_of_ne_down (c : Fin 3) (hc : c ≠ 2) :
    0 ≤ (RandomWalk.lazyTwoDimensionalStep c).2 := by
  by_cases h0 : c = 0
  · subst c
    simp [RandomWalk.lazyTwoDimensionalStep_zero]
  · by_cases h1 : c = 1
    · subst c
      simp [RandomWalk.lazyTwoDimensionalStep_one]
    · have h2 : c = 2 := by
        apply Fin.ext
        have hv := c.isLt
        have hc0 : c.val ≠ 0 := fun hh => h0 (Fin.ext hh)
        have hc1 : c.val ≠ 1 := fun hh => h1 (Fin.ext hh)
        omega
      exact (hc h2).elim

/-- If the vertical coordinate is unbounded below, every tail contains a down -/
theorem exists_down_after (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (n : ℕ) :
    ∃ k, n ≤ k ∧ w k = 2 := by
  by_contra h
  have hno : ∀ k, n ≤ k → w k ≠ 2 := by
    intro k hk h2
    exact h ⟨k, hk, h2⟩
  have hmono : ∀ m, n ≤ m → R w n ≤ R w m := by
    intro m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hnm ih =>
      have hinc := vertical_increment_nonneg_of_ne_down (w m) (hno m hnm)
      rw [coord_R_succ]
      omega
  obtain ⟨q, hq⟩ := hR (minR w n - 1)
  have hnq : n < q := by
    by_contra hnot
    have hqn : q ≤ n := Nat.le_of_not_gt hnot
    have hmin := runningMin_le (R w) n q hqn
    change minR w n ≤ R w q at hmin
    omega
  have htail := hmono q (Nat.le_of_lt hnq)
  have hmin := runningMin_le (R w) n n (le_refl n)
  change minR w n ≤ R w n at hmin
  omega


/-- Unbounded descent forces a later strict vertical record, whose preceding -/
theorem exists_empty_ur_down_after (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (n : ℕ) :
    ∃ k, n ≤ k ∧ w k = 2 ∧ (kmswStage w k).UR = [] := by
  let P : ℕ → Prop := fun p => n < p ∧ R w p < minR w n
  obtain ⟨q, hq⟩ := hR (minR w n - 1)
  have hnq : n < q := by
    by_contra hnot
    have hqn : q ≤ n := Nat.le_of_not_gt hnot
    have hmin := runningMin_le (R w) n q hqn
    change minR w n ≤ R w q at hmin
    omega
  have hP : ∃ p, P p := ⟨q, hnq, by omega⟩
  let p := Nat.find hP
  have hp : n < p ∧ R w p < minR w n := Nat.find_spec hP
  have hprior : ∀ j < p, minR w n ≤ R w j := by
    intro j hj
    by_cases hjn : j ≤ n
    · exact runningMin_le (R w) n j hjn
    · have hlt : n < j := by omega
      by_contra hbad
      have hbad' : R w j < minR w n := by omega
      have hfind : p ≤ j := Nat.find_min' hP ⟨hlt, hbad'⟩
      omega
  have hrec : ∀ j < p, R w p ≤ R w j - 1 := by
    intro j hj
    have hlow := hprior j hj
    omega
  obtain ⟨k, hpk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (by omega : 0 < p))
  have hrecK : ∀ j < k + 1, R w (k + 1) ≤ R w j - 1 := by
    intro j hj
    have hrecJ := hrec j (by omega)
    simpa [hpk] using hrecJ
  have hc := coord_R_succ w k
  have hnk : n ≤ k := by omega
  have h2 : w k = 2 := by
    by_contra hbad
    have hinc := vertical_increment_nonneg_of_ne_down (w k) hbad
    rw [hc] at hrecK
    have h := hrecK k (by omega)
    omega
  obtain ⟨i, hi, hmi⟩ := runningMin_attained (R w) k
  change minR w k = R w i at hmi
  have hrecI := hrecK i (by omega)
  rw [hc, h2, RandomWalk.lazyTwoDimensionalStep_two] at hrecI
  have hle := runningMin_le (R w) k k (le_refl k)
  change minR w k ≤ R w k at hle
  have hge : R w k ≤ minR w k := by rw [hmi]; omega
  have hmin : minR w k = R w k := le_antisymm hle hge
  have hlen := kmswStage_UR_length w k
  rw [hmin] at hlen
  have hzero : (kmswStage w k).UR.length = 0 := by omega
  exact ⟨k, hnk, h2, List.length_eq_zero_iff.mp hzero⟩

end DirectedDistances.KMSW
