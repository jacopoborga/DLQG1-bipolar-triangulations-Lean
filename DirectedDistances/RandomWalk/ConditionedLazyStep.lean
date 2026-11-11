/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring








public section
namespace DirectedDistances.RandomWalk

/-- At the lower boundary there are exactly two legal nonnegative targets. -/
theorem lazy_neighbor_zero_iff (y : ℕ) :
    |(y : ℤ) - (0 : ℤ)| ≤ 1 ↔ y = 0 ∨ y = 1 := by
  rw [abs_le]
  omega

/-- An interior state has exactly its predecessor, itself, and successor
as legal targets, with all three represented by actual natural states. -/
theorem lazy_neighbor_succ_iff (x y : ℕ) :
    |(y : ℤ) - ((x + 1 : ℕ) : ℤ)| ≤ 1 ↔ y = x ∨ y = x + 1 ∨ y = x + 2 := by
  rw [abs_le]
  omega

/-- Nonnegativity of the literal Doob weights on the nonnegative carrier. -/
theorem conditioned_lazy_weight_nonneg (x y : ℕ) :
    0 ≤ (if |(y : ℤ) - (x : ℤ)| ≤ 1 then
      ((y : ℝ) + 1) / (3 * ((x : ℝ) + 1)) else 0) := by
  split
  · exact div_nonneg (by positivity) (by positivity)
  · exact le_refl 0

/-- The scalar Doob weights have actual total mass one, including x=0. -/
theorem hasSum_conditioned_lazy_weight (x : ℕ) :
    HasSum (fun y : ℕ => if |(y : ℤ) - (x : ℤ)| ≤ 1 then
      ((y : ℝ) + 1) / (3 * ((x : ℝ) + 1)) else 0) 1 := by
  cases x with
  | zero =>
    have h := (hasSum_ite_eq 0 (1 / 3 : ℝ)).add (hasSum_ite_eq 1 (2 / 3 : ℝ))
    have he : (1 / 3 : ℝ) + 2 / 3 = 1 := by norm_num
    rw [he] at h
    apply h.congr_fun
    intro y
    simp only [Nat.cast_zero, lazy_neighbor_zero_iff]
    by_cases h0 : y = 0
    · subst y
      norm_num
    · by_cases h1 : y = 1
      · subst y
        norm_num
      · simp only [h0, h1, false_or, ↓reduceIte, add_zero]
  | succ x =>
    let d : ℝ := 3 * ((x : ℝ) + 2)
    have h := ((hasSum_ite_eq x (((x : ℝ) + 1) / d)).add
      (hasSum_ite_eq (x + 1) (((x : ℝ) + 2) / d))).add
      (hasSum_ite_eq (x + 2) (((x : ℝ) + 3) / d))
    have hd : d ≠ 0 := by dsimp [d]; positivity
    have he : (((x : ℝ) + 1) / d + ((x : ℝ) + 2) / d) + ((x : ℝ) + 3) / d = 1 := by
      dsimp [d]
      field_simp
      ring
    rw [he] at h
    apply h.congr_fun
    intro y
    simp only [lazy_neighbor_succ_iff]
    by_cases h0 : y = x
    · subst y
      simp only [↓reduceIte, Nat.cast_add, Nat.cast_one, d]
      simp only [show x ≠ x + 1 by omega, show x ≠ x + 2 by omega,
        ↓reduceIte, add_zero, true_or, ↓reduceIte]
      congr 1
      ring
    · by_cases h1 : y = x + 1
      · subst y
        simp only [h0, ↓reduceIte, zero_add,
          show x + 1 ≠ x + 2 by omega, add_zero, false_or, true_or,
          Nat.cast_add, Nat.cast_one, d]
        congr 1 <;> ring
      · by_cases h2 : y = x + 2
        · subst y
          simp only [h0, h1, ↓reduceIte, zero_add,
            false_or, Nat.cast_add, Nat.cast_ofNat, d]
          congr 1 <;> ring
        · simp only [h0, h1, h2, false_or, ↓reduceIte, add_zero]

/-- The exact scalar Doob transition weight from x to y on the nonnegative
carrier; no negative target state is represented. -/
@[expose] noncomputable def conditionedLazyWeight (x y : ℕ) : ℝ :=
  if |(y : ℤ) - (x : ℤ)| ≤ 1 then
    ((y : ℝ) + 1) / (3 * ((x : ℝ) + 1)) else 0

/-- The normalized real weights have an actual sum before PMF construction. -/
theorem conditionedLazyWeight_hasSum (x : ℕ) : HasSum (conditionedLazyWeight x) 1 :=
  hasSum_conditioned_lazy_weight x

/-- The exact ENNReal weights also have mass one. -/
theorem hasSum_ofReal_conditionedLazyWeight (x : ℕ) :
    HasSum (fun y => ENNReal.ofReal (conditionedLazyWeight x y)) 1 := by
  apply CompleteLattice.summable.hasSum_iff.mpr
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := conditionedLazyWeight x) (conditioned_lazy_weight_nonneg x)
    (conditionedLazyWeight_hasSum x).summable,
    (conditionedLazyWeight_hasSum x).tsum_eq, ENNReal.ofReal_one]

/-- The actual normalized one-step scalar conditioned lazy-walk law. -/
@[expose] noncomputable def conditionedLazyStep (x : ℕ) : PMF ℕ :=
  ⟨fun y => ENNReal.ofReal (conditionedLazyWeight x y), hasSum_ofReal_conditionedLazyWeight x⟩

/-- Whole-carrier characterization of the constructed PMF. -/
theorem conditionedLazyStep_apply (x y : ℕ) :
    conditionedLazyStep x y = ENNReal.ofReal
      (if |(y : ℤ) - (x : ℤ)| ≤ 1 then
        ((y : ℝ) + 1) / (3 * ((x : ℝ) + 1)) else 0) := rfl

/-- Real probabilities recover the literal kernel with no conversion default. -/
theorem conditionedLazyStep_toReal (x y : ℕ) :
    (conditionedLazyStep x y).toReal = conditionedLazyWeight x y :=
  ENNReal.toReal_ofReal (conditioned_lazy_weight_nonneg x y)

/-- The real transition weights are measurable in both natural coordinates. -/
theorem measurable_conditionedLazyWeight : Measurable
    (fun p : ℕ × ℕ => conditionedLazyWeight p.1 p.2) :=
  measurable_of_countable _

/-- The actual PMF weights are measurable in both natural coordinates. -/
theorem measurable_conditionedLazyStep : Measurable
    (fun p : ℕ × ℕ => conditionedLazyStep p.1 p.2) :=
  measurable_of_countable _

/-- At zero the holding probability is exactly one third. -/
theorem conditionedLazyWeight_zero_zero : conditionedLazyWeight 0 0 = 1 / 3 := by
  norm_num [conditionedLazyWeight]

/-- At zero the upward probability is exactly two thirds. -/
theorem conditionedLazyWeight_zero_one : conditionedLazyWeight 0 1 = 2 / 3 := by
  norm_num [conditionedLazyWeight]

/-- All other targets at zero have zero mass. -/
theorem conditionedLazyWeight_zero_of_two_le {y : ℕ} (hy : 2 ≤ y) :
    conditionedLazyWeight 0 y = 0 := by
  unfold conditionedLazyWeight
  apply ite_eq_right
  rw [Nat.cast_zero, lazy_neighbor_zero_iff]
  omega

/-- Products of the actual transition weights telescope along every
nonnegative nearest-neighbor path, with arbitrary nonnegative starting state. -/
theorem prod_range_conditionedLazyWeight (p : ℕ → ℕ) (n : ℕ)
    (hp : ∀ k < n, |(p (k + 1) : ℤ) - (p k : ℤ)| ≤ 1) :
    (∏ k ∈ Finset.range n, conditionedLazyWeight (p k) (p (k + 1))) =
      ((p n : ℝ) + 1) / ((p 0 : ℝ) + 1) * (1 / 3 : ℝ) ^ n := by
  induction n with
  | zero =>
    simp only [Finset.prod_range_zero, pow_zero, mul_one]
    exact (div_self (by positivity : (p 0 : ℝ) + 1 ≠ 0)).symm
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun k hk => hp k (Nat.lt_succ_of_lt hk))]
    unfold conditionedLazyWeight
    rw [ite_eq_left (hp n (Nat.lt_succ_self n)), pow_succ]
    have hmid : (p n : ℝ) + 1 ≠ 0 := by positivity
    have hstart : (p 0 : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-- The telescope specializes to a path starting at zero with exactly the
endpoint factor stated by the manuscript's Radon–Nikodym weight. -/
theorem prod_range_conditionedLazyWeight_of_start_zero (p : ℕ → ℕ) (n : ℕ)
    (hp0 : p 0 = 0) (hp : ∀ k < n, |(p (k + 1) : ℤ) - (p k : ℤ)| ≤ 1) :
    (∏ k ∈ Finset.range n, conditionedLazyWeight (p k) (p (k + 1))) =
      ((p n : ℝ) + 1) * (1 / 3 : ℝ) ^ n := by
  rw [prod_range_conditionedLazyWeight p n hp, hp0, Nat.cast_zero, zero_add, div_one]

/-- Finite-path version of the exact Doob product, compatible with the
`Fin (n+1)` path carrier. The start and endpoint factors are shared. -/
theorem prod_fin_conditionedLazyWeight {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : ∀ i : Fin n, |(p i.succ : ℤ) - (p i.castSucc : ℤ)| ≤ 1) :
    (∏ i : Fin n, conditionedLazyWeight (p i.castSucc) (p i.succ)) =
      ((p (Fin.last n) : ℝ) + 1) / ((p 0 : ℝ) + 1) * (1 / 3 : ℝ) ^ n := by
  have hterms (i : Fin n) : conditionedLazyWeight (p i.castSucc) (p i.succ) =
      (((p i.succ : ℝ) + 1) / ((p i.castSucc : ℝ) + 1)) * (1 / 3 : ℝ) := by
    unfold conditionedLazyWeight
    rw [ite_eq_left (hp i)]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  simp_rw [hterms]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  have hs : ((p 0 : ℝ) + 1) ≠ 0 := by positivity
  have hprod : (∏ i : Fin n, ((p i.castSucc : ℝ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by positivity)
  congr 1
  apply (div_eq_div_iff hprod hs).mpr
  have hleft := Fin.prod_univ_succ (fun i : Fin (n + 1) => (p i : ℝ) + 1)
  have hright := Fin.prod_univ_castSucc (fun i : Fin (n + 1) => (p i : ℝ) + 1)
  rw [hleft] at hright
  calc
    _ = ((p 0 : ℝ) + 1) * (∏ i : Fin n, ((p i.succ : ℝ) + 1)) := mul_comm _ _
    _ = (∏ i : Fin n, ((p i.castSucc : ℝ) + 1)) * ((p (Fin.last n) : ℝ) + 1) := hright
    _ = _ := mul_comm _ _

end DirectedDistances.RandomWalk
