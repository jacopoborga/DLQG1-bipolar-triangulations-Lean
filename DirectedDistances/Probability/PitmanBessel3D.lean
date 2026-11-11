/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3C
public import DirectedDistances.RandomWalk.LazyPathLaw
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk

/-- Helper toward Lemma 4.11: summing a joint test of the entire transformed
path and the original endpoint is exactly summing over its explicit fiber.
In particular the original endpoint ranges uniformly over `r, r-2, ..., -r`. -/
theorem lazyPitman_joint_endpoint_sum (n : ℕ)
    (F : NonnegativeLazyPath n → ℤ → ℝ) :
    (∑ p : LazyPath n, F (lazyPhi p) (p.val (Fin.last n))) =
      ∑ q : NonnegativeLazyPath n,
        ∑ k : Fin ((q.val.val (Fin.last n)).toNat + 1),
          F q (q.val.val (Fin.last n) - 2 * (k.val : ℤ)) := by
  classical
  rw [← Fintype.sum_fiberwise lazyPhi]
  apply Finset.sum_congr rfl
  intro q _
  symm
  apply Fintype.sum_equiv (lazyPhiFiberFinEquiv q)
  intro k
  have hq : lazyPhi ((lazyPhiFiberFinEquiv q k).val) = q :=
    (lazyPhiFiberFinEquiv q k).property
  rw [hq]
  change F q _ = F q ((lazyPsi q (lazyParameterFinEquiv q k)).val (Fin.last n))
  rw [lazyPsi_last]
  rfl

/-- Helper toward Lemma 4.11: the exact conditional uniform endpoint link,
expressed without conditional-expectation choices, for every joint test.
The weights on the right are the actual Pitman image probabilities. -/
theorem lazyPitman_joint_endpoint_uniform_link (n : ℕ)
    (F : NonnegativeLazyPath n → ℤ → ℝ) :
    (∑ p : LazyPath n, (uniformLazyPath n p).toReal *
      F (lazyPhi p) (p.val (Fin.last n))) =
      ∑ q : NonnegativeLazyPath n, (pitmanLazyPathLaw n q).toReal *
        ((∑ k : Fin ((q.val.val (Fin.last n)).toNat + 1),
          F q (q.val.val (Fin.last n) - 2 * (k.val : ℤ))) /
            ((q.val.val (Fin.last n)).toNat + 1 : ℝ)) := by
  classical
  simp only [uniformLazyPath_apply_pow, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, ← Finset.mul_sum]
  rw [lazyPitman_joint_endpoint_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [pitmanLazyPathLaw_apply, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have h : ((q.val.val (Fin.last n)).toNat + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

private theorem endpoint_link_difference (r : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    (∑ i : Fin (r + 1), if (r : ℤ) - 2 * (i.val : ℤ) = k then (1 : ℝ) else 0) =
      (if (r : ℤ) = k then (1 : ℝ) else 0) +
        ∑ i : Fin (r + 1), if (r : ℤ) - 2 * (i.val : ℤ) = k + 2 then (1 : ℝ) else 0 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc
    (fun i : Fin (r + 1) => if (r : ℤ) - 2 * (i.val : ℤ) = k + 2 then (1 : ℝ) else 0)]
  have hlast : ¬ (r : ℤ) - 2 * ((Fin.last r).val : ℤ) = k + 2 := by
    simp only [Fin.val_last]
    omega
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero, hlast, ↓reduceIte,
    add_zero, Fin.val_castSucc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (r : ℤ) - 2 * (i.succ.val : ℤ) = k ↔
      (r : ℤ) - 2 * (i.val : ℤ) = k + 2 := by
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    omega
  simp only [he]

/-- Helper toward Lemma 4.11: the discrete reflection difference follows
directly from the uniform Pitman fibers, for every nonnegative integer endpoint.
This is an exact finite identity, including the empty walk and boundary zero. -/
theorem lazyPitman_endpoint_count_difference (n : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    (∑ p : LazyPath n, if p.val (Fin.last n) = k then (1 : ℝ) else 0) =
      (∑ q : NonnegativeLazyPath n,
        if q.val.val (Fin.last n) = k then (1 : ℝ) else 0) +
      ∑ p : LazyPath n, if p.val (Fin.last n) = k + 2 then (1 : ℝ) else 0 := by
  classical
  rw [lazyPitman_joint_endpoint_sum n (fun _ z => if z = k then 1 else 0),
    lazyPitman_joint_endpoint_sum n (fun _ z => if z = k + 2 then 1 else 0),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have he : ((q.val.val (Fin.last n)).toNat : ℤ) = q.val.val (Fin.last n) :=
    Int.toNat_of_nonneg (q.property _)
  simpa only [he] using endpoint_link_difference (q.val.val (Fin.last n)).toNat k hk

private theorem pmf_map_real_finite {α β : Type*} [Fintype α] [DecidableEq β]
    (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal = ∑ a : α, if f a = b then (p a).toReal else 0 := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : f a = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro a
    split_ifs
    · exact p.apply_ne_top a
    · exact ENNReal.zero_ne_top

/-- Helper toward Lemma 4.11: the exact distribution of a discrete Pitman
endpoint is the height-plus-one weighted difference of two unconditioned
endpoint probabilities. This supplies a reflection formula without a new
reflection bijection and includes `n = 0` and `k = 0`. -/
theorem lazyPitman_endpoint_probability_difference (n : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    (((pitmanLazyPathLaw n).map (fun q => q.val.val (Fin.last n))) k).toReal =
      ((k : ℝ) + 1) *
        ((((uniformLazyPath n).map (fun p => p.val (Fin.last n))) k).toReal -
          (((uniformLazyPath n).map (fun p => p.val (Fin.last n))) (k + 2)).toReal) := by
  classical
  have hU (j : ℤ) :
      (((uniformLazyPath n).map (fun p => p.val (Fin.last n))) j).toReal =
        (1 / 3 : ℝ) ^ n *
          ∑ p : LazyPath n, if p.val (Fin.last n) = j then (1 : ℝ) else 0 := by
    rw [pmf_map_real_finite, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [uniformLazyPath_apply_pow]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, mul_ite, mul_one, mul_zero]
  have hP :
      (((pitmanLazyPathLaw n).map (fun q => q.val.val (Fin.last n))) k).toReal =
        ((k : ℝ) + 1) * (1 / 3 : ℝ) ^ n *
          ∑ q : NonnegativeLazyPath n,
            if q.val.val (Fin.last n) = k then (1 : ℝ) else 0 := by
    rw [pmf_map_real_finite, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.val.val (Fin.last n) = k
    · simp only [hq, ↓reduceIte, mul_one]
      rw [pitmanLazyPathLaw_apply]
      have hc : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hk
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      simp only [hq, Nat.cast_add,
        Nat.cast_one, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one,
        ENNReal.toReal_ofNat, hc]
    · simp only [hq, ↓reduceIte, mul_zero]
  rw [hP, hU, hU, lazyPitman_endpoint_count_difference n k hk]
  ring

private theorem sine_sum_telescopes (x r : ℝ) (m : ℕ) :
    Real.sin x * (∑ i ∈ Finset.range m, Real.cos (x * (r - 2 * i))) =
      (Real.sin (x * (r + 1)) - Real.sin (x * (r - 2 * m + 1))) / 2 := by
  induction m with
  | zero => simp only [Finset.sum_range_zero, mul_zero, Nat.cast_zero, sub_zero, sub_self, zero_div]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have htrig := Real.sin_add (x * (r - 2 * m)) x
    have htrig' := Real.sin_sub (x * (r - 2 * m)) x
    have h₁ : x * (r - 2 * m) + x = x * (r - 2 * m + 1) := by ring
    have h₂ : x * (r - 2 * m) - x = x * (r - 2 * (m + 1) + 1) := by ring
    rw [h₁] at htrig
    rw [h₂] at htrig'
    push_cast
    linarith only [htrig, htrig']

/-- Helper toward Lemma 4.11: the exact sinc transform of the discrete
uniform endpoint link, including zero frequency and zero height. -/
theorem finite_uniform_endpoint_sinc (r : ℕ) (x : ℝ) :
    Real.sinc x * ((∑ i : Fin (r + 1), Real.cos (x * ((r : ℝ) - 2 * i.val))) /
      (r + 1)) = Real.sinc (x * (r + 1)) := by
  by_cases hx : x = 0
  · subst x
    simp only [zero_mul, Real.cos_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Real.sinc_zero, one_mul]
    push_cast
    exact div_self (by positivity)
  have hr : (r : ℝ) + 1 ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hx, Real.sinc_of_ne_zero (mul_ne_zero hx hr)]
  have hs : (∑ i : Fin (r + 1), Real.cos (x * ((r : ℝ) - 2 * i.val))) =
      ∑ i ∈ Finset.range (r + 1), Real.cos (x * ((r : ℝ) - 2 * i)) :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => Real.cos (x * ((r : ℝ) - 2 * i))) (r + 1)
  rw [hs]
  have hh := sine_sum_telescopes x (r : ℝ) (r + 1)
  have he : x * ((r : ℝ) - 2 * (r + 1 : ℕ) + 1) = -(x * (r + 1)) := by
    push_cast
    ring
  rw [he, Real.sin_neg] at hh
  field_simp
  nlinarith only [hh]

/-- Helper toward Lemma 4.11: an exact bounded transform identity for the
actual original and Pitman endpoint laws. Its continuous limit determines the
sinc transform of the scalar Pitman marginal from the Gaussian characteristic
function, avoiding a local central limit theorem. -/
theorem lazyPitman_endpoint_sinc_link (n : ℕ) (x : ℝ) :
    Real.sinc x *
      (∫ p, Real.cos (x * (p.val (Fin.last n) : ℝ)) ∂(uniformLazyPath n).toMeasure) =
      ∫ p, Real.sinc (x * ((lazyPhi p).val.val (Fin.last n) + 1 : ℝ))
        ∂(uniformLazyPath n).toMeasure := by
  classical
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [lazyPitman_joint_endpoint_uniform_link n (fun _ z => Real.cos (x * z)),
    lazyPitman_joint_endpoint_uniform_link n
      (fun q _ => Real.sinc (x * (q.val.val (Fin.last n) + 1 : ℝ))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have he : (((q.val.val (Fin.last n)).toNat : ℕ) : ℝ) =
      (q.val.val (Fin.last n) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (q.property (Fin.last n))
  have hh := finite_uniform_endpoint_sinc (q.val.val (Fin.last n)).toNat x
  simp only [he] at hh
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  have hne : ((q.val.val (Fin.last n)).toNat + 1 : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hne, ← mul_assoc, mul_comm (Real.sinc x), mul_assoc]
  congr 1
  simpa only [he] using hh

end DirectedDistances.Probability
