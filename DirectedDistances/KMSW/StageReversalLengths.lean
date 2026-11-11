module

public import DirectedDistances.KMSW.BoundaryDynamics
import Mathlib.Tactic.FinCases

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW





private theorem lazyTwoDimensionalStep_codeSwap (c : Fin 3) :
    RandomWalk.lazyTwoDimensionalStep (Equiv.swap (0 : Fin 3) 1 c) =
      -Prod.swap (RandomWalk.lazyTwoDimensionalStep c) := by
  fin_cases c <;> norm_num [Equiv.swap_apply_def,
    RandomWalk.lazyTwoDimensionalStep]





theorem runningMin_reverse (f : ℕ → ℤ) (n : ℕ) :
    runningMin f n = runningMin (fun j => f (n - j)) n := by
  apply le_antisymm
  · obtain ⟨i, hi, hmin⟩ := runningMin_attained (fun j => f (n - j)) n
    have hle := runningMin_le f n (n - i) (by omega)
    calc
      runningMin f n ≤ f (n - i) := hle
      _ = runningMin (fun j => f (n - j)) n := hmin.symm
  · obtain ⟨i, hi, hmin⟩ := runningMin_attained f n
    have hle := runningMin_le (fun j => f (n - j)) n (n - i) (by omega)
    have hidx : n - (n - i) = i := by omega
    rw [hidx] at hle
    calc
      runningMin (fun j => f (n - j)) n ≤ f i := hle
      _ = runningMin f n := hmin.symm





theorem kmswStage_reverse_L (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {j : ℕ} (hj : j ≤ n) :
    L wr j = R w (n - j) - R w n := by
  induction j with
  | zero => simp [L]
  | succ j ih =>
    have hjn : j < n := by omega
    have hidx : n - 1 - j = n - (j + 1) := by omega
    have hidx' : n - j = (n - (j + 1)) + 1 := by omega
    have hletter := hrev j hjn
    rw [show L wr (j + 1) =
      L wr j + (RandomWalk.lazyTwoDimensionalStep (wr j)).1 by
        exact Finset.sum_range_succ _ _, ih (by omega)]
    have hstep :
        (RandomWalk.lazyTwoDimensionalStep (wr j)).1 =
          -(RandomWalk.lazyTwoDimensionalStep (w (n - (j + 1)))).2 := by
      rw [hletter, hidx, lazyTwoDimensionalStep_codeSwap]
      simp [Prod.swap]
    rw [hidx', show R w ((n - (j + 1)) + 1) =
      R w (n - (j + 1)) +
        (RandomWalk.lazyTwoDimensionalStep (w (n - (j + 1)))).2 by
          exact Finset.sum_range_succ _ _, hstep]
    omega





theorem kmswStage_reverse_R (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    {j : ℕ} (hj : j ≤ n) :
    R wr j = L w (n - j) - L w n := by
  induction j with
  | zero => simp [R]
  | succ j ih =>
    have hjn : j < n := by omega
    have hidx : n - 1 - j = n - (j + 1) := by omega
    have hidx' : n - j = (n - (j + 1)) + 1 := by omega
    have hletter := hrev j hjn
    rw [show R wr (j + 1) =
      R wr j + (RandomWalk.lazyTwoDimensionalStep (wr j)).2 by
        exact Finset.sum_range_succ _ _, ih (by omega)]
    have hstep :
        (RandomWalk.lazyTwoDimensionalStep (wr j)).2 =
          -(RandomWalk.lazyTwoDimensionalStep (w (n - (j + 1)))).1 := by
      rw [hletter, hidx, lazyTwoDimensionalStep_codeSwap]
      simp [Prod.swap]
    rw [hidx', show L w ((n - (j + 1)) + 1) =
      L w (n - (j + 1)) +
        (RandomWalk.lazyTwoDimensionalStep (w (n - (j + 1)))).1 by
          exact Finset.sum_range_succ _ _, hstep]
    omega





private theorem runningMin_sub_const (f : ℕ → ℤ) (n : ℕ) (c : ℤ) :
    runningMin (fun j => f j - c) n = runningMin f n - c := by
  induction n with
  | zero => simp [runningMin]
  | succ n ih =>
    simp only [runningMin]
    rw [ih]
    by_cases h : runningMin f n ≤ f (n + 1)
    · rw [min_eq_left h, min_eq_left (by omega)]
    · have h' : f (n + 1) ≤ runningMin f n := le_of_not_ge h
      rw [min_eq_right h', min_eq_right (by omega)]





private theorem runningMin_congr {f g : ℕ → ℤ} (n : ℕ)
    (h : ∀ j ≤ n, f j = g j) : runningMin f n = runningMin g n := by
  induction n with
  | zero => simp [runningMin, h 0 (le_refl 0)]
  | succ n ih =>
    have hprev : ∀ j ≤ n, f j = g j := fun j hj => h j (by omega)
    simp only [runningMin, ih hprev, h (n + 1) (le_refl _)]





theorem kmswStage_reverse_minL (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    minL wr n = minR w n - R w n := by
  have hwalk : ∀ j ≤ n, L wr j = R w (n - j) - R w n := by
    intro j hj
    exact kmswStage_reverse_L wr w n hrev hj
  unfold minL minR
  rw [runningMin_congr n hwalk, runningMin_sub_const,
    ← runningMin_reverse (R w) n]





theorem kmswStage_reverse_minR (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    minR wr n = minL w n - L w n := by
  have hwalk : ∀ j ≤ n, R wr j = L w (n - j) - L w n := by
    intro j hj
    exact kmswStage_reverse_R wr w n hrev hj
  unfold minL minR
  rw [runningMin_congr n hwalk, runningMin_sub_const,
    ← runningMin_reverse (L w) n]





theorem kmswStage_reverse_UL_length (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    (kmswStage wr n).UL.length = (kmswStage w n).LR.length := by
  have hcast :
      ((kmswStage wr n).UL.length : ℤ) = ((kmswStage w n).LR.length : ℤ) := by
    rw [kmswStage_UL_length, kmswStage_LR_length,
      kmswStage_reverse_L wr w n hrev (le_refl n), kmswStage_reverse_minL wr w n hrev]
    have hzero : R w 0 = 0 := by simp [R]
    simp only [Nat.sub_self, hzero]
    omega
  exact_mod_cast hcast





theorem kmswStage_reverse_UR_length (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    (kmswStage wr n).UR.length = (kmswStage w n).LL.length := by
  have hcast :
      ((kmswStage wr n).UR.length : ℤ) = ((kmswStage w n).LL.length : ℤ) := by
    rw [kmswStage_UR_length, kmswStage_LL_length,
      kmswStage_reverse_R wr w n hrev (le_refl n), kmswStage_reverse_minR wr w n hrev]
    have hzero : L w 0 = 0 := by simp [L]
    simp only [Nat.sub_self, hzero]
    omega
  exact_mod_cast hcast





theorem kmswStage_reverse_LL_length (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    (kmswStage wr n).LL.length = (kmswStage w n).UR.length := by
  have hcast :
      ((kmswStage wr n).LL.length : ℤ) = ((kmswStage w n).UR.length : ℤ) := by
    rw [kmswStage_LL_length, kmswStage_UR_length,
      kmswStage_reverse_minL wr w n hrev]
    omega
  exact_mod_cast hcast





theorem kmswStage_reverse_LR_length (wr w : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    (kmswStage wr n).LR.length = (kmswStage w n).UL.length := by
  have hcast :
      ((kmswStage wr n).LR.length : ℤ) = ((kmswStage w n).UL.length : ℤ) := by
    rw [kmswStage_LR_length, kmswStage_UL_length,
      kmswStage_reverse_minR wr w n hrev]
    omega
  exact_mod_cast hcast

end DirectedDistances.KMSW
