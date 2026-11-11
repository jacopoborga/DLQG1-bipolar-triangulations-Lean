module

public import DirectedDistances.RandomWalk.VectorPitman
public import DirectedDistances.RandomWalk.RecordBlockCount

/-! # A tube forces the Pitman image into the block event

Deterministic input for the block estimate in Lemma 4.12 -/

public section
namespace DirectedDistances.RandomWalk

private theorem tube_globalMinimum_bounds (z : ℕ → ℤ × ℤ) (N n : ℕ)
    (hN : 1 ≤ N) (hz0 : z 0 = (0, 0))
    (htubeL : ∀ k ≤ N,
      |((z k).1 : ℝ) - (k : ℝ) / N * Real.sqrt N| ≤ Real.sqrt N / 10)
    (hn : n ≤ N) :
    -Real.sqrt N / 10 ≤ (globalLazyRunningMinimum (fun k => (z k).1) n : ℝ) ∧
      (globalLazyRunningMinimum (fun k => (z k).1) n : ℝ) ≤ 0 := by
  classical
  let p : ℕ → ℤ := fun k => (z k).1
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (by omega : 0 < N))
  have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hnonempty : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨j, hj, hmin⟩ :=
    Finset.exists_mem_eq_inf' hnonempty (fun k => p k)
  have hjn : j ≤ n := by
    have hj' := Finset.mem_range.mp hj
    omega
  have hjN : j ≤ N := hjn.trans hn
  have hmin' : globalLazyRunningMinimum p n = p j := by
    simpa [globalLazyRunningMinimum, p] using hmin
  have hcenter : 0 ≤ (j : ℝ) / (N : ℝ) * Real.sqrt (N : ℝ) := by
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hNpos)) hs
  have hbound := abs_le.mp (htubeL j hjN)
  have hjlower : -Real.sqrt (N : ℝ) / 10 ≤ (p j : ℝ) := by
    dsimp [p] at hbound ⊢
    linarith
  have hlow : -Real.sqrt (N : ℝ) / 10 ≤
      (globalLazyRunningMinimum p n : ℝ) := by
    rw [hmin']
    exact hjlower
  have hzero : p 0 = 0 := by
    dsimp [p]
    have h := congrArg Prod.fst hz0
    simpa using h
  have hupperInt : globalLazyRunningMinimum p n ≤ 0 := by
    have h := globalLazyRunningMinimum_le p (i := 0) (Nat.zero_le n)
    simpa [hzero] using h
  have hupper : (globalLazyRunningMinimum p n : ℝ) ≤ 0 := by
    exact_mod_cast hupperInt
  exact ⟨hlow, hupper⟩

private theorem tube_vectorPitman_first_bounds (z : ℕ → ℤ × ℤ) (N n : ℕ)
    (hN : 1 ≤ N) (hz0 : z 0 = (0, 0))
    (htubeL : ∀ k ≤ N,
      |((z k).1 : ℝ) - (k : ℝ) / N * Real.sqrt N| ≤ Real.sqrt N / 10)
    (hnlow : (N : ℝ) / 2 ≤ n) (hnup : n ≤ N) :
    Real.sqrt n / 100 ≤ ((vectorPitman z n).1 : ℝ) ∧
      ((vectorPitman z n).1 : ℝ) ≤ 100 * Real.sqrt n := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (by omega : 0 < N))
  have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hnreal : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnup
  have hratioLow : (1 / 2 : ℝ) ≤ (n : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hNpos]
    nlinarith
  have hratioUp : (n : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  let c : ℝ := (n : ℝ) / (N : ℝ) * Real.sqrt (N : ℝ)
  have hcLow : Real.sqrt (N : ℝ) / 2 ≤ c := by
    dsimp [c]
    nlinarith
  have hcUp : c ≤ Real.sqrt (N : ℝ) := by
    dsimp [c]
    nlinarith
  obtain ⟨hmLow, hmUp⟩ := tube_globalMinimum_bounds z N n hN hz0 htubeL hnup
  have hraw := abs_le.mp (htubeL n hnup)
  have hrawLow : c - Real.sqrt (N : ℝ) / 10 ≤ ((z n).1 : ℝ) := by
    dsimp [c] at hraw ⊢
    linarith
  have hrawUp : ((z n).1 : ℝ) ≤ c + Real.sqrt (N : ℝ) / 10 := by
    dsimp [c] at hraw ⊢
    linarith
  have hpit : ((vectorPitman z n).1 : ℝ) =
      ((z n).1 : ℝ) - 2 *
        (globalLazyRunningMinimum (fun k => (z k).1) n : ℝ) := by
    simp [vectorPitman, globalLazyPhi]
  have hcoreLow : Real.sqrt (N : ℝ) * (2 / 5) ≤ ((vectorPitman z n).1 : ℝ) := by
    rw [hpit]
    linarith
  have hcoreUp : ((vectorPitman z n).1 : ℝ) ≤ Real.sqrt (N : ℝ) * (13 / 10) := by
    rw [hpit]
    linarith
  have hsqrtUp : Real.sqrt n ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt hnreal
  have hlow : Real.sqrt n / 100 ≤ ((vectorPitman z n).1 : ℝ) := by
    calc
      Real.sqrt n / 100 ≤ Real.sqrt (N : ℝ) / 100 := by
        exact div_le_div_of_nonneg_right hsqrtUp (by norm_num)
      _ ≤ Real.sqrt (N : ℝ) * (2 / 5) := by nlinarith
      _ ≤ ((vectorPitman z n).1 : ℝ) := hcoreLow
  have hnrootLow : Real.sqrt (N : ℝ) * (7 / 10) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    have hNlower : (N : ℝ) / 2 ≤ (n : ℝ) := by exact_mod_cast hnlow
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  have hupper : ((vectorPitman z n).1 : ℝ) ≤ 100 * Real.sqrt n := by
    calc
      ((vectorPitman z n).1 : ℝ) ≤ Real.sqrt (N : ℝ) * (13 / 10) := hcoreUp
      _ ≤ 100 * Real.sqrt n := by nlinarith
  exact ⟨hlow, hupper⟩

/-- A tube around the target profile sends its Pitman image into the block event -/
theorem vectorPitman_mem_block_of_tube (z : ℕ → ℤ × ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hz0 : z 0 = (0, 0))
    (htubeL : ∀ n ≤ N, |((z n).1 : ℝ) - (n : ℝ) / N * Real.sqrt N| ≤ Real.sqrt N / 10)
    (htubeR : ∀ n ≤ N, |((z n).2 : ℝ) - (-6 * max 0 ((n : ℝ) / N - 1 / 2)) * Real.sqrt N|
        ≤ Real.sqrt N / 10) :
    vectorPitman z ∈ {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by
  classical
  change
    (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
      Real.sqrt n / 100 ≤ ((vectorPitman z n).1 : ℝ) ∧
        ((vectorPitman z n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
    (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 →
      -Real.sqrt N ≤ ((vectorPitman z n).2 : ℝ)) ∧
    ((vectorPitman z N).2 : ℝ) ≤ -2 * Real.sqrt N
  refine ⟨?_, ?_, ?_⟩
  · intro n hnlow hnup
    exact tube_vectorPitman_first_bounds z N n hN hz0 htubeL hnlow hnup
  · intro n hnEarly
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt (by omega : 0 < N))
    have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have hnratio : (n : ℝ) / (N : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hNpos]
      nlinarith [hnEarly]
    have hmax : max 0 ((n : ℝ) / (N : ℝ) - 1 / 2) = 0 := by
      apply max_eq_left
      linarith
    have hnup : n ≤ N := by
      apply_mod_cast (le_trans hnEarly (by nlinarith [hNpos] : (N : ℝ) / 2 ≤ (N : ℝ)))
    have hmin := tube_globalMinimum_bounds z N n hN hz0 htubeL hnup
    have hrawTube := htubeR n hnup
    have hraw := abs_le.mp hrawTube
    have hcenter : (-6 * max 0 ((n : ℝ) / (N : ℝ) - 1 / 2)) *
        Real.sqrt (N : ℝ) = 0 := by
      rw [hmax]
      ring
    have hrawLow : -Real.sqrt (N : ℝ) / 10 ≤ ((z n).2 : ℝ) := by
      linarith [hraw.1, hcenter]
    have hpit : ((vectorPitman z n).2 : ℝ) =
        ((z n).2 : ℝ) +
          (globalLazyRunningMinimum (fun k => (z k).1) n : ℝ) := by
      simp [vectorPitman]
    rw [hpit]
    have hsum : -Real.sqrt (N : ℝ) / 5 ≤
        ((z n).2 : ℝ) +
          (globalLazyRunningMinimum (fun k => (z k).1) n : ℝ) := by
      rcases hmin with ⟨hmLow, _⟩
      linarith
    linarith
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt (by omega : 0 < N))
    have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have hratio : (N : ℝ) / (N : ℝ) = 1 := div_self hNpos.ne'
    have hmax : max 0 ((N : ℝ) / (N : ℝ) - 1 / 2) = 1 / 2 := by
      rw [hratio]
      norm_num
    have hrawTube := htubeR N le_rfl
    have hraw := abs_le.mp hrawTube
    have hcenter : (-6 * max 0 ((N : ℝ) / (N : ℝ) - 1 / 2)) *
        Real.sqrt (N : ℝ) = -3 * Real.sqrt (N : ℝ) := by
      rw [hmax]
      ring
    have hrawUp : ((z N).2 : ℝ) ≤ -Real.sqrt (N : ℝ) * (29 / 10) := by
      linarith [hraw.2, hcenter]
    have hpit : ((vectorPitman z N).2 : ℝ) =
        ((z N).2 : ℝ) +
          (globalLazyRunningMinimum (fun k => (z k).1) N : ℝ) := by
      simp [vectorPitman]
    rw [hpit]
    have hmup :
        (globalLazyRunningMinimum (fun k => (z k).1) N : ℝ) ≤ 0 := by
      exact (tube_globalMinimum_bounds z N N hN hz0 htubeL le_rfl).2
    linarith

end DirectedDistances.RandomWalk
