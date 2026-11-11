module

public import DirectedDistances.RandomWalk.IIDVectorWalk
import Mathlib.Probability.Martingale.OptionalStopping

/-! # Maximal bounds for the iid vector walk

Analytic helpers for the block maximum estimate used in the tube argument for -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Each source step has both coordinates bounded by one in absolute value.
This records the bounded-increment input for the block maximum argument -/
theorem lazyTwoDimensionalStep_coord_abs_le_one (c : Fin 3) :
    |(lazyTwoDimensionalStep c).1| ≤ 1 ∧ |(lazyTwoDimensionalStep c).2| ≤ 1 := by
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

/-- The two integer coordinates of every one-step increment of `codeWalk` -/
theorem codeWalk_succ_sub_coord_abs_le_one (ω : ℕ → Fin 3) (i : ℕ) :
    |(codeWalk ω (i + 1) - codeWalk ω i).1| ≤ 1 ∧
    |(codeWalk ω (i + 1) - codeWalk ω i).2| ≤ 1 := by
  rw [codeWalk_succ_sub]
  exact lazyTwoDimensionalStep_coord_abs_le_one _

/-- Over any finite block, a coordinate displacement of `codeWalk` is the sum -/
theorem codeWalk_block_sub_eq_sum (ω : ℕ → Fin 3) (s k : ℕ) :
    codeWalk ω (s + k) - codeWalk ω s =
      ∑ i ∈ Finset.range k, lazyTwoDimensionalStep (ω (s + i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ]
      calc
        codeWalk ω (s + k + 1) - codeWalk ω s =
            (codeWalk ω (s + k + 1) - codeWalk ω (s + k)) +
              (codeWalk ω (s + k) - codeWalk ω s) := by abel
        _ = lazyTwoDimensionalStep (ω (s + k + 1)) +
              ∑ i ∈ Finset.range k, lazyTwoDimensionalStep (ω (s + i + 1)) := by
            rw [codeWalk_succ_sub, ih]
        _ = ∑ i ∈ Finset.range (k + 1), lazyTwoDimensionalStep (ω (s + i + 1)) := by
            rw [Finset.sum_range_succ]
            abel

/-- A block of length `m` moves either coordinate by at most `m` in absolute -/
theorem codeWalk_block_sub_coord_abs_le_length
    (ω : ℕ → Fin 3) (s m : ℕ) :
    |(codeWalk ω (s + m) - codeWalk ω s).1| ≤ m ∧
    |(codeWalk ω (s + m) - codeWalk ω s).2| ≤ m := by
  rw [codeWalk_block_sub_eq_sum, Prod.fst_sum, Prod.snd_sum]
  constructor
  · calc
      |∑ i ∈ Finset.range m, (lazyTwoDimensionalStep (ω (s + i + 1))).1| ≤
          ∑ i ∈ Finset.range m, |(lazyTwoDimensionalStep (ω (s + i + 1))).1| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ m := by
        calc
          ∑ i ∈ Finset.range m, |(lazyTwoDimensionalStep (ω (s + i + 1))).1| ≤
              ∑ i ∈ Finset.range m, (1 : ℤ) :=
                Finset.sum_le_sum fun i hi =>
                  lazyTwoDimensionalStep_coord_abs_le_one _ |>.1
          _ = (m : ℤ) := by simp
  · calc
      |∑ i ∈ Finset.range m, (lazyTwoDimensionalStep (ω (s + i + 1))).2| ≤
          ∑ i ∈ Finset.range m, |(lazyTwoDimensionalStep (ω (s + i + 1))).2| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ m := by
        calc
          ∑ i ∈ Finset.range m, |(lazyTwoDimensionalStep (ω (s + i + 1))).2| ≤
              ∑ i ∈ Finset.range m, (1 : ℤ) :=
                Finset.sum_le_sum fun i hi =>
                  lazyTwoDimensionalStep_coord_abs_le_one _ |>.2
          _ = (m : ℤ) := by simp

end DirectedDistances.RandomWalk
