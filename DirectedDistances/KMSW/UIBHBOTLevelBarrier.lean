module

public import DirectedDistances.KMSW.UIBHBOTBlockStrictRecords

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem uibhbotBlockBoundary_nat_lower (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) (n : ℕ) :
    (n : ℤ) ≤ uibhbotBlockBoundary w (n : ℤ) := by
  induction n with
  | zero => simpa using (le_of_eq (uibhbotBlockBoundary_zero w).symm)
  | succ n ih =>
      have hn : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
      have hlen : (1 : ℤ) ≤ ((w (n : ℤ)).length : ℤ) := by
        exact_mod_cast (hw (n : ℤ)).1
      rw [hn, uibhbotBlockBoundary_succ]
      omega

private theorem uibhbotBlockBoundary_neg_nat_upper (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) (n : ℕ) :
    uibhbotBlockBoundary w (-(n : ℤ)) ≤ -(n : ℤ) := by
  induction n with
  | zero => simpa using (le_of_eq (uibhbotBlockBoundary_zero w))
  | succ n ih =>
      have hn : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 := by omega
      have hrec := uibhbotBlockBoundary_succ w (-(n : ℤ) - 1)
      have harg : (-(n : ℤ) - 1) + 1 = -(n : ℤ) := by omega
      rw [harg] at hrec
      have hlen : (1 : ℤ) ≤ ((w (-(n : ℤ) - 1)).length : ℤ) := by
        exact_mod_cast (hw (-(n : ℤ) - 1)).1
      rw [hn]
      omega

private theorem uibhbotBlockBoundary_le_of_nonpos (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) {k : ℤ} (hk : k ≤ 0) :
    uibhbotBlockBoundary w k ≤ k := by
  let n := (-k).toNat
  have hn : (n : ℤ) = -k := by
    dsimp [n]
    exact Int.toNat_of_nonneg (by omega)
  have hbound := uibhbotBlockBoundary_neg_nat_upper w hw n
  rw [hn] at hbound
  simpa only [Int.neg_neg] using hbound

private theorem uibhbotBlockBoundary_ge_of_nonneg (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) {k : ℤ} (hk : 0 ≤ k) :
    k ≤ uibhbotBlockBoundary w k := by
  let n := k.toNat
  have hn : (n : ℤ) = k := by
    dsimp [n]
    exact Int.toNat_of_nonneg hk
  have hbound := uibhbotBlockBoundary_nat_lower w hw n
  rw [hn] at hbound
  exact hbound

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^♭,
integer time lies in one block interval of the stopped-excursion concatenation; not a paper
result. -/
theorem uibhbotConcatWalk_exists_block (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) (t : ℤ) :
    ∃ j : ℤ, uibhbotBlockBoundary w j ≤ t ∧ t < uibhbotBlockBoundary w (j + 1) := by
  have hnonempty : ∃ z : ℤ, uibhbotBlockBoundary w z ≤ t := by
    by_cases ht : t < 0
    · exact ⟨t, uibhbotBlockBoundary_le_of_nonpos w hw (by omega)⟩
    · exact ⟨0, by rw [uibhbotBlockBoundary_zero]; omega⟩
  have hbounded : ∃ b : ℤ, ∀ z : ℤ, uibhbotBlockBoundary w z ≤ t → z ≤ b := by
    refine ⟨max t 0, ?_⟩
    intro z hz
    by_cases hz0 : 0 ≤ z
    · have h := uibhbotBlockBoundary_ge_of_nonneg w hw hz0
      omega
    · omega
  obtain ⟨j, hj, hjmax⟩ := Int.exists_greatest_of_bdd hbounded hnonempty
  refine ⟨j, hj, ?_⟩
  by_contra hnot
  have hjnext : uibhbotBlockBoundary w (j + 1) ≤ t := by omega
  have hmax := hjmax (j + 1) hjnext
  omega

private theorem uibhbotConcatWalk_level_le_of_block (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) {j t : ℤ}
    (hlo : uibhbotBlockBoundary w j ≤ t)
    (hhi : t < uibhbotBlockBoundary w (j + 1)) :
    -j ≤ (uibhbotConcatWalk w t).1 :=
  uibhbotConcatWalk_blockInterval_fst w hw j t hlo hhi

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^♭,
fixed time has a strict lower-level barrier at all sufficiently early times; not the paper
result. -/
theorem uibhbotConcatWalk_D2 (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) (t : ℤ) :
    ∃ s₀ : ℤ, ∀ s : ℤ, s < s₀ →
      (uibhbotConcatWalk w t).1 < (uibhbotConcatWalk w s).1 := by
  let J := max ((uibhbotConcatWalk w t).1) 0 + 2
  have hJ : max ((uibhbotConcatWalk w t).1) 0 + 1 < J := by
    dsimp [J]
    omega
  refine ⟨uibhbotBlockBoundary w (-J), ?_⟩
  intro s hs
  obtain ⟨j, hjlo, hjhi⟩ := uibhbotConcatWalk_exists_block w hw s
  have hmono := uibhbotBlockBoundary_strictMono w (fun k => (hw k).1)
  have hjlt : j < -J := by
    by_contra hnot
    have hle : -J ≤ j := by omega
    have hle' := hmono.monotone hle
    omega
  have hjbound : j ≤ -J - 1 := by omega
  have hlevel := uibhbotConcatWalk_level_le_of_block w hw hjlo hjhi
  have hstrict : (uibhbotConcatWalk w t).1 < -j := by omega
  exact hstrict.trans_le hlevel

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^♭,
endpoint is a strict global lower record relative to all earlier times; not the paper result. -/
theorem uibhbotConcatWalk_blockEndpoint_strictRecord (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) (k : ℤ) (s : ℤ)
    (hs : s < uibhbotBlockBoundary w (k + 1)) :
    (uibhbotConcatWalk w (uibhbotBlockBoundary w (k + 1))).1 <
      (uibhbotConcatWalk w s).1 := by
  obtain ⟨j, hjlo, hjhi⟩ := uibhbotConcatWalk_exists_block w hw s
  have hmono := uibhbotBlockBoundary_strictMono w (fun i => (hw i).1)
  have hjlt : j < k + 1 := by
    by_contra hnot
    have hle : k + 1 ≤ j := by omega
    have hle' := hmono.monotone hle
    omega
  have hjle : j ≤ k := by omega
  have hlevel := uibhbotConcatWalk_level_le_of_block w hw hjlo hjhi
  have hend :
      (uibhbotConcatWalk w (uibhbotBlockBoundary w (k + 1))).1 = -(k + 1) :=
    uibhbotConcatWalk_stopped_blockBoundary_fst w hw (k + 1)
  rw [hend]
  omega

end DirectedDistances.KMSW
