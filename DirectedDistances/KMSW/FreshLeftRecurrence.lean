module

public import DirectedDistances.KMSW.MonotoneLimitExternalDarts
public import DirectedDistances.RandomWalk.IIDCodeRelabel

/-! # Fresh-left recurrence from lower unboundedness

Helper (iid one-sided realization bundle); not a paper result. The bridge uses
strict new lower records of `L`; the iid statement packages the corresponding
one-sided realization. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk

private theorem freshLeft_of_strict_L_record (w : ℕ → Fin 3) (n : ℕ)
    (hrec : ∀ j ≤ n, L w (n + 1) < L w j) :
    w n = 0 ∧ (kmswStage w n).UL.dropLast.reverse = [] := by
  have hstep : L w (n + 1) =
      L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    exact Finset.sum_range_succ _ _
  have hlast := hrec n le_rfl
  have hc : w n = 0 := by
    change L w (n + 1) = L w n + ((w n : ℤ) - 1) at hstep
    rw [hstep] at hlast
    have hv : (w n : ℤ) - 1 < 0 := by omega
    apply Fin.ext
    omega
  rw [hc] at hstep
  simp [RandomWalk.lazyTwoDimensionalStep_zero] at hstep
  have hmin : minL w n = L w n := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
    have hjrec := hrec j hj
    have hle := runningMin_le (L w) n n le_rfl
    change minL w n = L w j at he
    change minL w n ≤ L w n at hle
    omega
  have hlen := kmswStage_UL_length w n
  have hlen' : (kmswStage w n).UL.length = 1 := by
    rw [hmin] at hlen
    omega
  have hdropLen : ((kmswStage w n).UL.dropLast).length = 0 := by
    rw [List.length_dropLast, hlen']
  have hdrop : (kmswStage w n).UL.dropLast = [] :=
    List.length_eq_zero_iff.mp hdropLen
  exact ⟨hc, by rw [hdrop]; rfl⟩

/-- Helper (iid one-sided realization bundle); not a paper result.
If `L` is unbounded below, every tail contains a strict new lower record,
and each such record is a fresh-left step. -/
theorem infinitelyManyFreshLeft_of_L_unbounded_below (w : ℕ → Fin 3)
    (hbelow : ∀ a : ℤ, ∃ n, L w n ≤ a) : InfinitelyManyFreshLeft w := by
  rw [InfinitelyManyFreshLeft, Set.infinite_iff_exists_gt]
  intro N
  let a : ℤ := minL w (N + 1) - 1
  obtain ⟨t, ht⟩ := hbelow a
  have hhit : ∃ n, L w n ≤ a := ⟨t, ht⟩
  have hfirst : N + 1 < Nat.find hhit := by
    by_contra h
    have hle : Nat.find hhit ≤ N + 1 := by omega
    have hmin := runningMin_le (L w) (N + 1) (Nat.find hhit) hle
    have hspec := Nat.find_spec hhit
    change minL w (N + 1) ≤ L w (Nat.find hhit) at hmin
    omega
  cases hfind : Nat.find hhit with
  | zero => omega
  | succ r =>
      have hspec : L w (r + 1) ≤ a := by
        simpa [hfind] using (Nat.find_spec hhit)
      have hrec : ∀ j ≤ r, L w (r + 1) < L w j := by
        intro j hj
        have hnot : ¬ L w j ≤ a := Nat.find_min hhit (by omega)
        omega
      have hfresh := freshLeft_of_strict_L_record w r hrec
      have hgt : N < r := by simpa [hfind] using hfirst
      exact ⟨r, by simpa using hfresh, hgt⟩

private theorem codeWalk_fst_eq_L_shifted (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).1 = L (fun i => ω (i + 1)) n := by
  induction n with
  | zero => simp [codeWalk_zero, L]
  | succ n ih =>
      have hc := congrArg Prod.fst (codeWalk_succ_sub ω n)
      have hl : L (fun i => ω (i + 1)) (n + 1) =
          L (fun i => ω (i + 1)) n +
            (RandomWalk.lazyTwoDimensionalStep (ω (n + 1))).1 := by
        exact Finset.sum_range_succ _ _
      simp only [Prod.fst_sub] at hc
      rw [hl, ← ih]
      omega

/-- Helper (iid one-sided realization bundle); not a paper result.
The first-coordinate lower-unboundedness of `codeWalk` yields infinitely many
fresh-left times for its literal shifted increment stream. -/
theorem ae_iidCode_freshLeft_of_fst_unbounded_below :
    ∀ᵐ ω ∂iidCodeMeasure,
      InfinitelyManyFreshLeft (fun i => ω (i + 1)) := by
  filter_upwards [ae_codeWalk_fst_unbounded_below] with ω hω
  apply infinitelyManyFreshLeft_of_L_unbounded_below
  intro a
  obtain ⟨n, hn⟩ := hω a
  exact ⟨n, by rw [← codeWalk_fst_eq_L_shifted]; exact hn⟩

end DirectedDistances.KMSW
