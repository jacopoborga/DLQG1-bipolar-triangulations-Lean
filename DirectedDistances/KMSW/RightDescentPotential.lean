module

public import DirectedDistances.KMSW.InfiniteBoundary

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/

/-! # Right descents reach strict right-boundary records

Purely discrete potential argument toward clause C4 of Lemma 3.10. -/

public section
namespace DirectedDistances.KMSW

open scoped Classical




theorem act_eq_rightBoundaryEdge_of_record (w : ℕ → Fin 3) {m : ℕ}
    (hm : ∀ j, j < m → R w m < R w j) :
    act w m = kmswRightBoundaryEdge w
      (Nat.count (fun m => ∀ j, j < m → R w m < R w j) m) := by
  unfold kmswRightBoundaryEdge
  rw [natSelect_count hm]




theorem firstDescent_record_of_min (w : ℕ → Fin 3) {t t' : ℕ}
    (hmin : ∀ q, q ≤ t → R w t ≤ R w q)
    (ht' : t < t' ∧ R w t' = R w t - 1 ∧
      ∀ q, t < q → q < t' → R w t - 1 < R w q) :
    ∀ j, j < t' → R w t' < R w j := by
  intro j hj
  by_cases hjt : j ≤ t
  · have hle := hmin j hjt
    rw [ht'.2.1]
    omega
  · have hgap := ht'.2.2 j (by omega) hj
    rw [ht'.2.1]
    exact hgap




theorem firstDescent_potential_drop (w : ℕ → Fin 3) {t t' : ℕ}
    (hnot : ∃ q, q ≤ t ∧ R w q < R w t)
    (ht' : t < t' ∧ R w t' = R w t - 1 ∧
      ∀ q, t < q → q < t' → R w t - 1 < R w q) :
    (∀ q, q ≤ t' → ∃ p, p ≤ t ∧ R w p ≤ R w q) ∧
      minR w t' = minR w t ∧
      R w t' - minR w t' = R w t - minR w t - 1 := by
  obtain ⟨p, hp, hple⟩ := hnot
  have hprior : ∀ q, q ≤ t → ∃ r, r ≤ t ∧ R w r ≤ R w q := by
    intro q hq
    exact ⟨q, hq, le_rfl⟩
  have hcover : ∀ q, q ≤ t' → ∃ r, r ≤ t ∧ R w r ≤ R w q := by
    intro q hq
    by_cases hqt : q ≤ t
    · exact hprior q hqt
    · have htq : t < q := by omega
      by_cases hqeq : q = t'
      · subst q
        exact ⟨p, hp, by rw [ht'.2.1]; omega⟩
      · have hqLt : q < t' := by omega
        have hgap := ht'.2.2 q htq hqLt
        exact ⟨p, hp, by omega⟩
  have hmin_le : minR w t' ≤ minR w t := by
    obtain ⟨q, hq, hqval⟩ := runningMin_attained (R w) t
    change minR w t = R w q at hqval
    have hle := runningMin_le (R w) t' q (by omega)
    change minR w t' ≤ R w q at hle
    calc
      minR w t' ≤ R w q := hle
      _ = minR w t := hqval.symm
  have hmin_ge : minR w t ≤ minR w t' := by
    obtain ⟨q, hq, hqval⟩ := runningMin_attained (R w) t'
    change minR w t' = R w q at hqval
    obtain ⟨p', hp', hpq⟩ := hcover q hq
    have hle := runningMin_le (R w) t p' hp'
    change minR w t ≤ R w p' at hle
    calc
      minR w t ≤ R w p' := hle
      _ ≤ R w q := hpq
      _ = minR w t' := hqval.symm
  refine ⟨hcover, le_antisymm hmin_le hmin_ge, ?_⟩
  rw [le_antisymm hmin_le hmin_ge, ht'.2.1]
  omega

private theorem descentChain_preserves_record (w : ℕ → Fin 3)
    (s : ℕ → ℕ)
    (hs : ∀ i, s i < s (i + 1) ∧ R w (s (i + 1)) = R w (s i) - 1 ∧
      ∀ q, s i < q → q < s (i + 1) → R w (s i) - 1 < R w q)
    {i : ℕ} (hrec : ∀ q, q < s i → R w (s i) < R w q) :
    ∀ d, ∀ q, q < s (i + d) → R w (s (i + d)) < R w q := by
  intro d
  induction d with
  | zero => simpa using hrec
  | succ d ih =>
    have hrec' : ∀ q, q < s (i + d) → R w (s (i + d)) < R w q := ih
    have hmin : ∀ q, q ≤ s (i + d) → R w (s (i + d)) ≤ R w q := by
      intro q hq
      by_cases hqt : q = s (i + d)
      · subst q
        exact le_rfl
      · exact (hrec' q (by omega)).le
    have hnext := firstDescent_record_of_min w hmin (hs (i + d))
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

private theorem descentChain_has_record_bound (w : ℕ → Fin 3) :
    ∀ (k : ℕ) (s : ℕ → ℕ),
      (∀ i, s i < s (i + 1) ∧ R w (s (i + 1)) = R w (s i) - 1 ∧
        ∀ q, s i < q → q < s (i + 1) → R w (s i) - 1 < R w q) →
      R w (s 0) - minR w (s 0) = (k : ℤ) →
      ∃ i, i ≤ k + 1 ∧ ∀ q, q < s i → R w (s i) < R w q := by
  intro k
  induction k with
  | zero =>
    intro s hs hphi
    have hmin : ∀ q, q ≤ s 0 → R w (s 0) ≤ R w q := by
      intro q hq
      have hle := runningMin_le (R w) (s 0) q hq
      change minR w (s 0) ≤ R w q at hle
      omega
    have hnext := firstDescent_record_of_min w hmin (hs 0)
    exact ⟨1, by omega, by simpa using hnext⟩
  | succ k ih =>
    intro s hs hphi
    have hnot : ∃ q, q ≤ s 0 ∧ R w q < R w (s 0) := by
      have hlt : minR w (s 0) < R w (s 0) := by omega
      obtain ⟨q, hq, hqval⟩ := runningMin_attained (R w) (s 0)
      refine ⟨q, hq, ?_⟩
      rw [← hqval]
      exact hlt
    have hdrop := firstDescent_potential_drop w hnot (hs 0)
    have hphi' : R w (s 1) - minR w (s 1) = (k : ℤ) := by
      rw [hdrop.2.2, hphi]
      omega
    obtain ⟨i, hi, hrec⟩ := ih (fun n => s (n + 1))
      (fun n => hs (n + 1)) hphi'
    refine ⟨i + 1, ?_, ?_⟩
    · omega
    · simpa using hrec




theorem descentChain_hits_record (w : ℕ → Fin 3) (s : ℕ → ℕ)
    (hs : ∀ i, s i < s (i + 1) ∧ R w (s (i + 1)) = R w (s i) - 1 ∧
      ∀ q, s i < q → q < s (i + 1) → R w (s i) - 1 < R w q) :
    ∃ i, i ≤ Int.toNat (R w (s 0) - minR w (s 0)) + 1 ∧
      ∀ i' ≥ i, ∃ j', act w (s i') = kmswRightBoundaryEdge w j' := by
  have hnonneg : 0 ≤ R w (s 0) - minR w (s 0) := by
    have hle := runningMin_le (R w) (s 0) (s 0) le_rfl
    change minR w (s 0) ≤ R w (s 0) at hle
    omega
  let k := Int.toNat (R w (s 0) - minR w (s 0))
  have hphi : R w (s 0) - minR w (s 0) = (k : ℤ) := by
    dsimp [k]
    exact (Int.toNat_of_nonneg hnonneg).symm
  obtain ⟨i, hi, hrec⟩ := descentChain_has_record_bound w k s hs hphi
  refine ⟨i, ?_, ?_⟩
  · exact hi
  · intro i' hi'
    have hrecord := descentChain_preserves_record w s hs hrec (i' - i)
    have hindex : i + (i' - i) = i' := by omega
    have hrecord' : ∀ q, q < s i' → R w (s i') < R w q := by
      simpa [hindex] using hrecord
    refine ⟨Nat.count (fun m => ∀ j, j < m → R w m < R w j) (s i'), ?_⟩
    exact act_eq_rightBoundaryEdge_of_record w hrecord'

end DirectedDistances.KMSW
