/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyGamblerRuin
public import DirectedDistances.RandomWalk.LazyPathLaw
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.FieldSimp

/-! # Actual finite uniform lazy-word survival and killed moment

Finite-word probability and expectation producers for Lemma 4.10,
Words retain the actual three uniform increments. Survival tests every partial
sum, including the initial state. No hitting-law conclusion is assumed. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

/-- Literal nonnegative survival event for a finite increment word started at x. -/
@[expose] def LazyWordSurvives {n : ℕ} (x : ℤ) (w : Fin n → Fin 3) : Prop :=
  ∀ j : Fin (n + 1), 0 ≤ x + lazyWordValues w j

/-- Killed terminal payoff on the actual finite word, using its actual endpoint. -/
@[expose] noncomputable def lazyWordKilledPayoff {n : ℕ} (x : ℤ)
    (F : ℤ → ℝ) (w : Fin n → Fin 3) : ℝ :=
  by
    classical
    exact if LazyWordSurvives x w then F (x + lazyWordValues w (Fin.last n)) else 0

/-- Normalized counting expectation under the genuine uniform three-step word law. -/
@[expose] noncomputable def lazyWordKilledAverage (n : ℕ) (x : ℤ) (F : ℤ → ℝ) : ℝ :=
  (1 / 3 : ℝ) ^ n * ∑ w : Fin n → Fin 3, lazyWordKilledPayoff x F w

/-- A cons word's noninitial coordinates are its first increment plus tail coordinates. -/
theorem lazyWordValues_cons {n : ℕ} (a : Fin 3) (w : Fin n → Fin 3)
    (j : Fin (n + 1)) :
    lazyWordValues (Fin.cons a w) j.succ = (a : ℤ) - 1 + lazyWordValues w j := by
  simp only [lazyWordValues, Finset.sum_filter, Fin.sum_univ_succ,
    Fin.val_succ, Fin.val_zero, Nat.zero_lt_succ, Fin.cons_zero, ite_true,
    Fin.cons_succ, Nat.add_lt_add_iff_right]

/-- Survival of a cons word is precisely a legal initial state and tail survival. -/
theorem lazyWordSurvives_cons {n : ℕ} (x : ℤ) (a : Fin 3) (w : Fin n → Fin 3) :
    LazyWordSurvives x (Fin.cons a w) ↔
      0 ≤ x ∧ LazyWordSurvives (x + (a : ℤ) - 1) w := by
  simp only [LazyWordSurvives, Fin.forall_fin_succ, lazyWordValues_zero,
    add_zero, lazyWordValues_cons]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, by omega, ?_⟩
    intro i
    have := h2 i
    omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, by omega, ?_⟩
    intro i
    have := h2 i
    omega

/-- An initially negative word never survives, including at horizon zero. -/
theorem lazyWordKilledPayoff_of_neg {n : ℕ} {x : ℤ} (hx : x < 0)
    (F : ℤ → ℝ) (w : Fin n → Fin 3) : lazyWordKilledPayoff x F w = 0 := by
  classical
  unfold lazyWordKilledPayoff
  apply ite_eq_right
  intro h
  have h0 := h 0
  rw [lazyWordValues_zero, add_zero] at h0
  omega

/-- Actual first-step decomposition of the killed payoff. -/
theorem lazyWordKilledPayoff_cons {n : ℕ} (x : ℤ) (hx : 0 ≤ x)
    (F : ℤ → ℝ) (a : Fin 3) (w : Fin n → Fin 3) :
    lazyWordKilledPayoff x F (Fin.cons a w) =
      lazyWordKilledPayoff (x + (a : ℤ) - 1) F w := by
  classical
  unfold lazyWordKilledPayoff
  rw [lazyWordSurvives_cons]
  simp only [hx, true_and]
  congr 1
  rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl, lazyWordValues_cons]
  congr 1
  ring

/-- Split the actual uniform word sum into its three first increments. -/
theorem sum_lazyWordKilledPayoff_succ (n : ℕ) (x : ℤ) (hx : 0 ≤ x) (F : ℤ → ℝ) :
    (∑ w : Fin (n + 1) → Fin 3, lazyWordKilledPayoff x F w) =
      (∑ w : Fin n → Fin 3, lazyWordKilledPayoff (x - 1) F w) +
      (∑ w : Fin n → Fin 3, lazyWordKilledPayoff x F w) +
      (∑ w : Fin n → Fin 3, lazyWordKilledPayoff (x + 1) F w) := by
  have he := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3))
    (fun p : Fin 3 × (Fin n → Fin 3) => lazyWordKilledPayoff x F (Fin.cons p.1 p.2))
    (fun w => lazyWordKilledPayoff x F w) (fun _ => rfl)
  rw [← he, Fintype.sum_prod_type]
  simp only [lazyWordKilledPayoff_cons x hx]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, Nat.cast_one,
    Nat.cast_add, zero_add, add_zero]
  simp only [show x + 1 - 1 = x by omega, show x + 2 - 1 = x + 1 by omega]
  exact (add_assoc _ _ _).symm

/-- The actual normalized counting expectation has the lazy averaging recurrence. -/
theorem lazyWordKilledAverage_succ (n : ℕ) (x : ℤ) (hx : 0 ≤ x) (F : ℤ → ℝ) :
    lazyWordKilledAverage (n + 1) x F =
      (lazyWordKilledAverage n (x - 1) F + lazyWordKilledAverage n x F +
        lazyWordKilledAverage n (x + 1) F) / 3 := by
  unfold lazyWordKilledAverage
  rw [sum_lazyWordKilledPayoff_succ n x hx F, pow_succ]
  ring

/-- Initially negative starting values have zero killed average. -/
theorem lazyWordKilledAverage_of_neg (n : ℕ) {x : ℤ} (hx : x < 0) (F : ℤ → ℝ) :
    lazyWordKilledAverage n x F = 0 := by
  simp only [lazyWordKilledAverage, lazyWordKilledPayoff_of_neg hx, Finset.sum_const_zero,
    mul_zero]

/-- Horizon zero evaluates the payoff at the actual legal initial state. -/
theorem lazyWordKilledAverage_zero (x : ℤ) (hx : 0 ≤ x) (F : ℤ → ℝ) :
    lazyWordKilledAverage 0 x F = F x := by
  classical
  simp only [lazyWordKilledAverage, pow_zero, one_mul]
  rw [Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0)]
  simp only [lazyWordKilledPayoff, LazyWordSurvives, lazyWordValues,
    Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty, add_zero, hx, implies_true, ite_true]

/-- Actual finite uniform-word survival equals the numerical killed recursion. -/
theorem lazyWordKilledAverage_one (n z : ℕ) :
    lazyWordKilledAverage n z (fun _ => 1) = lazyKilledSurvival n z := by
  refine lazyKilledSurvival_unique (u := fun n z => lazyWordKilledAverage n z (fun _ => 1)) ?_ ?_ ?_ n z
  · intro z
    exact lazyWordKilledAverage_zero _ (by omega) _
  · intro n
    simp only [Nat.cast_zero, Nat.cast_one]
    rw [lazyWordKilledAverage_succ n 0 (by omega),
      lazyWordKilledAverage_of_neg n (show (0 : ℤ) - 1 < 0 by omega)]
    simp only [zero_add]
  · intro n z
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_sub_cancel_right,
      show (z : ℤ) + 1 + 1 = z + 2 by omega] using
      lazyWordKilledAverage_succ n ((z : ℤ) + 1) (by omega) _

/-- Actual killed shifted-height first moment is exactly the starting height plus one. -/
theorem lazyWordKilledAverage_shifted_height (n z : ℕ) :
    lazyWordKilledAverage n z (fun y => (y : ℝ) + 1) = (z : ℝ) + 1 := by
  refine lazy_killed_first_moment_eq (u := fun n z => lazyWordKilledAverage n z (fun y => (y : ℝ) + 1)) ?_ ?_ ?_ n z
  · intro z
    simpa only [Int.cast_natCast] using
      lazyWordKilledAverage_zero (z : ℤ) (by omega) (fun y => (y : ℝ) + 1)
  · intro n
    simp only [Nat.cast_zero, Nat.cast_one]
    rw [lazyWordKilledAverage_succ n 0 (by omega),
      lazyWordKilledAverage_of_neg n (show (0 : ℤ) - 1 < 0 by omega)]
    simp only [zero_add]
  · intro n z
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_sub_cancel_right,
      show (z : ℤ) + 1 + 1 = z + 2 by omega] using
      lazyWordKilledAverage_succ n ((z : ℤ) + 1) (by omega) _

/-- Genuine survival probability under the actual finite uniform word law. -/
theorem uniform_lazyWordSurvives_real (n z : ℕ) :
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).real
      {w | LazyWordSurvives z w} = lazyKilledSurvival n z := by
  classical
  rw [← lazyWordKilledAverage_one n z]
  rw [Measure.real, Measure.uniformOfFinset_apply, ENNReal.toReal_div]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_pow ]
  unfold lazyWordKilledAverage lazyWordKilledPayoff
  rw [Finset.sum_boole]
  rw [one_div, inv_pow, div_eq_mul_inv, mul_comm]
  simp only [Set.mem_ofPred_eq, Nat.cast_ofNat]

/-- The actual finite uniform-word survival probabilities vanish. -/
theorem tendsto_uniform_lazyWordSurvives_real (z : ℕ) :
    Filter.Tendsto (fun n =>
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).real
        {w | LazyWordSurvives z w}) Filter.atTop (𝓝 0) := by
  simp only [uniform_lazyWordSurvives_real]
  exact tendsto_lazyKilledSurvival z

/-- The normalized killed sum is the genuine Bochner expectation under the
actual finite uniform word measure. Integrability is proved on its finite carrier. -/
theorem integral_uniform_lazyWordKilledPayoff (n : ℕ) (x : ℤ) (F : ℤ → ℝ) :
    (∫ w, lazyWordKilledPayoff x F w ∂
      Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))) =
      lazyWordKilledAverage n x F := by
  classical
  have : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))) :=
    ⟨by
      rw [Measure.uniformOfFinset_apply]
      simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      exact ENNReal.div_self (by positivity) (by norm_num)⟩
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real, Measure.uniformOfFinset_apply_singleton,
    Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, ENNReal.toReal_inv, ENNReal.toReal_pow, Nat.cast_ofNat, ENNReal.toReal_ofNat,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [lazyWordKilledAverage, one_div, inv_pow]

/-- Actual killed shifted-height expectation, with all survival coordinates
and integrability supplied by the finite uniform word law. -/
theorem integral_uniform_lazyWordKilled_shifted_height (n z : ℕ) :
    (∫ w, lazyWordKilledPayoff z (fun y => (y : ℝ) + 1) w ∂
      Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))) =
      (z : ℝ) + 1 := by
  rw [integral_uniform_lazyWordKilledPayoff, lazyWordKilledAverage_shifted_height]

/-- Exact endpoint-weighted finite-word average needed by the conditioned
barrier law. The two actual killed averages are consumed inside the proof. -/
theorem lazyWordKilledAverage_endpoint_weight (n s x : ℕ) (a : ℝ) :
    lazyWordKilledAverage n s (fun y => ((y : ℝ) + 1 + a) / ((x : ℝ) + 1)) =
      (((s : ℝ) + 1) + a * lazyKilledSurvival n s) / ((x : ℝ) + 1) := by
  classical
  have hp (w : Fin n → Fin 3) :
      lazyWordKilledPayoff s (fun y => ((y : ℝ) + 1 + a) / ((x : ℝ) + 1)) w =
        (lazyWordKilledPayoff s (fun y => (y : ℝ) + 1) w +
          a * lazyWordKilledPayoff s (fun _ => 1) w) / ((x : ℝ) + 1) := by
    unfold lazyWordKilledPayoff
    split <;> simp only [mul_one, mul_zero, add_zero, zero_div]
  have hm := lazyWordKilledAverage_shifted_height n s
  have hu := lazyWordKilledAverage_one n s
  unfold lazyWordKilledAverage at hm hu ⊢
  simp_rw [hp]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    _ = (((1 / 3 : ℝ) ^ n *
        ∑ w : Fin n → Fin 3, lazyWordKilledPayoff s (fun y => (y : ℝ) + 1) w) +
        a * ((1 / 3 : ℝ) ^ n *
          ∑ w : Fin n → Fin 3, lazyWordKilledPayoff s (fun _ => 1) w)) /
        ((x : ℝ) + 1) := by ring
    _ = _ := by rw [hm, hu]

/-- The endpoint-weighted actual finite-word averages have the exact limiting
barrier value, using the proved vanishing survival probabilities. -/
theorem tendsto_lazyWordKilledAverage_endpoint_weight (s x : ℕ) (a : ℝ) :
    Filter.Tendsto (fun n => lazyWordKilledAverage n s
      (fun y => ((y : ℝ) + 1 + a) / ((x : ℝ) + 1))) Filter.atTop
      (𝓝 (((s : ℝ) + 1) / ((x : ℝ) + 1))) := by
  simp only [lazyWordKilledAverage_endpoint_weight]
  have h := (((tendsto_lazyKilledSurvival s).const_mul a).const_add
    ((s : ℝ) + 1)).div_const ((x : ℝ) + 1)
  simpa only [mul_zero, add_zero] using h

end DirectedDistances.RandomWalk
