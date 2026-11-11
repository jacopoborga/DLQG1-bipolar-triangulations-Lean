/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.PGFFirstMoment
import Mathlib.Topology.Algebra.InfiniteSum.Real







public section
namespace DirectedDistances.Tauberian

private theorem tsum_ite_lt_row (f : ℕ → ℝ) (n : ℕ) :
    (∑' k : ℕ, if k < n then f n else 0) = (n : ℝ) * f n := by
  rw [tsum_eq_sum (s := Finset.range n)]
  · calc
      _ = ∑ _k ∈ Finset.range n, f n := by
        apply Finset.sum_congr rfl
        intro k hk
        exact ite_eq_left (Finset.mem_range.mp hk)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro k hk
    simp only [Finset.mem_range] at hk
    exact ite_eq_right hk

private theorem summable_tail_triangle {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hm : Summable (fun n : ℕ => (n : ℝ) * f n)) :
    Summable (fun p : ℕ × ℕ => if p.2 < p.1 then f p.1 else 0) := by
  apply (summable_prod_of_nonneg (fun p => by split; exact hf _; exact le_refl 0)).2
  constructor
  · intro n
    apply summable_of_ne_finset_zero (s := Finset.range n)
    intro k hk
    exact ite_eq_right (by simpa only [Finset.mem_range] using hk)
  · simpa only [tsum_ite_lt_row] using hm

private theorem tsum_lt_column {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (k : ℕ)
    (h : Summable (fun n : ℕ => if k < n then f n else 0)) :
    (∑' n : ℕ, if k < n then f n else 0) = ∑' j, f (j + (k + 1)) := by
  rw [← h.sum_add_tsum_nat_add (k + 1)]
  have hzero : (∑ n ∈ Finset.range (k + 1), if k < n then f n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [ite_eq_right (by have := Finset.mem_range.mp hn; omega)]
  rw [hzero, zero_add]
  apply tsum_congr
  intro j
  rw [ite_eq_left (by omega)]

/-- The sum of the actual positive-index tails is the actual first moment.
This is a nonnegative double-series identity, including zero atoms. -/
theorem hasSum_tails_eq_first_moment {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hm : Summable (fun n : ℕ => (n : ℝ) * f n)) :
    HasSum (fun k : ℕ => ∑' j : ℕ, f (j + (k + 1)))
      (∑' n : ℕ, (n : ℝ) * f n) := by
  have h := summable_tail_triangle hf hm
  have hcol (k : ℕ) := h.prod_symm.prod_factor k
  have heq : (∑' k : ℕ, ∑' j : ℕ, f (j + (k + 1))) =
      ∑' n : ℕ, (n : ℝ) * f n := by
    calc
      _ = ∑' k : ℕ, ∑' n : ℕ, if k < n then f n else 0 := by
        apply tsum_congr; intro k; exact (tsum_lt_column f k (hcol k)).symm
      _ = ∑' n : ℕ, ∑' k : ℕ, if k < n then f n else 0 := h.tsum_comm
      _ = _ := tsum_congr (tsum_ite_lt_row f)
  have hs := h.prod_symm.prod
  change Summable (fun k : ℕ => ∑' n : ℕ, if k < n then f n else 0) at hs
  rw [show (fun k : ℕ => ∑' n : ℕ, if k < n then f n else 0) =
      (fun k : ℕ => ∑' j : ℕ, f (j + (k + 1))) from
    funext (fun k => tsum_lt_column f k (hcol k))] at hs
  exact heq ▸ hs.hasSum

/-- Dividing the actual tails by a positive actual mean produces a
nonnegative coefficient sequence of total mass one. -/
theorem normalized_tail_coefficients {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hm : Summable (fun n : ℕ => (n : ℝ) * f n))
    (hm0 : 0 < ∑' n : ℕ, (n : ℝ) * f n) :
    (∀ k : ℕ, 0 ≤ (∑' j : ℕ, f (j + (k + 1))) /
      (∑' n : ℕ, (n : ℝ) * f n)) ∧
    HasSum (fun k : ℕ => (∑' j : ℕ, f (j + (k + 1))) /
      (∑' n : ℕ, (n : ℝ) * f n)) 1 := by
  refine ⟨fun k => div_nonneg (tsum_nonneg (fun j => hf _)) hm0.le, ?_⟩
  simpa only [div_self hm0.ne'] using (hasSum_tails_eq_first_moment hf hm).div_const
    (∑' n : ℕ, (n : ℝ) * f n)

/-- The actual tail power series equals the geometric-polynomial series on
all of the closed unit disk. The double series is absolutely summable by
first-moment domination; no interchange hypothesis is assumed. -/
theorem tsum_tail_weighted_pow_eq_geom {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hm : Summable (fun n : ℕ => (n : ℝ) * f n))
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∑' k : ℕ, ((∑' j : ℕ, f (j + (k + 1)) : ℝ) : ℂ) * z ^ k) =
      ∑' n : ℕ, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k) := by
  have hreal := summable_tail_triangle hf hm
  have hc : Summable (fun p : ℕ × ℕ =>
      if p.2 < p.1 then (f p.1 : ℂ) * z ^ p.2 else 0) := by
    apply hreal.of_norm_bounded
    intro p
    split
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf p.1), norm_pow]
      exact mul_le_of_le_one_right (hf p.1) (pow_le_one₀ (norm_nonneg z) hz)
    · simp only [norm_zero, le_refl]
  have hcol (k : ℕ) := hc.prod_symm.prod_factor k
  have hrow (n : ℕ) :
      (∑' k : ℕ, if k < n then (f n : ℂ) * z ^ k else 0) =
        (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k) := by
    rw [tsum_eq_sum (s := Finset.range n)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Finset.mem_range.mp hk)]
    · intro k hk
      exact ite_eq_right (by simpa only [Finset.mem_range] using hk)
  calc
    _ = ∑' k : ℕ, ∑' n : ℕ,
        if k < n then (f n : ℂ) * z ^ k else 0 := by
      apply tsum_congr
      intro k
      rw [tsum_lt_column (fun n => (f n : ℂ) * z ^ k) k (hcol k)]
      rw [tsum_mul_right, ← Complex.ofReal_tsum]
    _ = ∑' n : ℕ, ∑' k : ℕ,
        if k < n then (f n : ℂ) * z ^ k else 0 := hc.tsum_comm
    _ = _ := tsum_congr hrow

/-- The probability generating function of the normalized tail coefficients
is the actual normalized geometric series used for `G` in Appendix A.3. -/
theorem tsum_normalized_tail_weighted_pow {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hm : Summable (fun n : ℕ => (n : ℝ) * f n))
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∑' k : ℕ, (((∑' j : ℕ, f (j + (k + 1))) /
      (∑' n : ℕ, (n : ℝ) * f n) : ℝ) : ℂ) * z ^ k) =
      (∑' n : ℕ, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)) /
        ((∑' n : ℕ, (n : ℝ) * f n : ℝ) : ℂ) := by
  simp_rw [Complex.ofReal_div, div_mul_eq_mul_div]
  rw [tsum_div_const, tsum_tail_weighted_pow_eq_geom hf hm hz]


/-- Away from one the normalized tail probability generating series is
exactly the manuscript quotient `G`, with the actual mean in its denominator. -/
theorem tsum_normalized_tail_weighted_pow_eq_quotient {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1)
    (hm : Summable (fun n : ℕ => (n : ℝ) * f n))
    (hm0 : 0 < ∑' n : ℕ, (n : ℝ) * f n)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    (∑' k : ℕ, (((∑' j : ℕ, f (j + (k + 1))) /
      (∑' n : ℕ, (n : ℝ) * f n) : ℝ) : ℂ) * z ^ k) =
      ((∑' n : ℕ, (f n : ℂ) * z ^ n) - 1) /
        (((∑' n : ℕ, (n : ℝ) * f n : ℝ) : ℂ) * (z - 1)) := by
  rw [tsum_normalized_tail_weighted_pow hf hm hz,
    tsum_weighted_pow_sub_one_eq hf hs hm hz]
  have hmean : ((∑' n : ℕ, (n : ℝ) * f n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hm0.ne'
  field_simp [hmean, sub_ne_zero.mpr hz1]

private theorem tsum_ite_lt_weighted_row (f : ℕ → ℝ) (r : ℝ) (n : ℕ) :
    (∑' k : ℕ, if k < n then f n * r ^ k else 0) =
      f n * ∑ k ∈ Finset.range n, r ^ k := by
  rw [tsum_eq_sum (s := Finset.range n)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact ite_eq_left (Finset.mem_range.mp hk)
  · intro k hk
    exact ite_eq_right (by simpa only [Finset.mem_range] using hk)

private theorem summable_tail_triangle_weighted {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : Summable f) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p : ℕ × ℕ => if p.2 < p.1 then f p.1 * r ^ p.2 else 0) := by
  apply (summable_prod_of_nonneg (fun p => by
    split; exact mul_nonneg (hf _) (pow_nonneg hr0 _); exact le_refl 0)).2
  constructor
  · intro n
    apply summable_of_ne_finset_zero (s := Finset.range n)
    intro k hk
    exact ite_eq_right (by simpa only [Finset.mem_range] using hk)
  · simp_rw [tsum_ite_lt_weighted_row]
    apply Summable.of_nonneg_of_le (fun n =>
      mul_nonneg (hf n) (Finset.sum_nonneg (fun k _ => pow_nonneg hr0 k))) _
      (hs.mul_right ((1 - r)⁻¹))
    intro n
    apply mul_le_mul_of_nonneg_left _ (hf n)
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _
      (fun k _ => pow_nonneg hr0 k)

/-- The tail power series converges at every real point of `[0,1)` without
any finite-mean assumption, as required for the Laplace step of Appendix A.2. -/
theorem summable_tail_weighted_pow {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hs : Summable f) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ => (∑' j : ℕ, f (j + (k + 1))) * r ^ k) := by
  have h := summable_tail_triangle_weighted hf hs hr0 hr1
  have ht := h.prod_symm.prod
  change Summable (fun k : ℕ => ∑' n : ℕ, if k < n then f n * r ^ k else 0) at ht
  apply ht.congr
  intro k
  rw [tsum_lt_column (fun n => f n * r ^ k) k (h.prod_symm.prod_factor k),
    tsum_mul_right]

/-- Exact tail/Laplace generating identity for a probability sequence,
valid with an infinite first moment as well as a finite one. -/
theorem one_sub_tsum_weighted_pow_eq_tail {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 - (∑' n : ℕ, f n * r ^ n) =
      (1 - r) * (∑' k : ℕ, (∑' j : ℕ, f (j + (k + 1))) * r ^ k) := by
  have h := summable_tail_triangle_weighted hf hs.summable hr0 hr1
  have heq : (∑' k : ℕ, (∑' j : ℕ, f (j + (k + 1))) * r ^ k) =
      ∑' n : ℕ, f n * (∑ k ∈ Finset.range n, r ^ k) := by
    calc
      _ = ∑' k : ℕ, ∑' n : ℕ, if k < n then f n * r ^ k else 0 := by
        apply tsum_congr
        intro k
        rw [tsum_lt_column (fun n => f n * r ^ k) k (h.prod_symm.prod_factor k),
          tsum_mul_right]
      _ = ∑' n : ℕ, ∑' k : ℕ, if k < n then f n * r ^ k else 0 := h.tsum_comm
      _ = _ := tsum_congr (tsum_ite_lt_weighted_row f r)
  have hgeom : Summable (fun n : ℕ => f n * ∑ k ∈ Finset.range n, r ^ k) := by
    simpa only [tsum_ite_lt_weighted_row] using h.prod
  have hp : Summable (fun n : ℕ => f n * r ^ n) := by
    apply hs.summable.of_nonneg_of_le (fun n => mul_nonneg (hf n) (pow_nonneg hr0 n))
    intro n
    exact mul_le_of_le_one_right (hf n) (pow_le_one₀ hr0 hr1.le)
  rw [heq]
  apply (hs.sub hp.hasSum).unique
  apply (hgeom.hasSum.mul_left (1 - r)).congr_fun
  intro n
  symm
  calc
    (1 - r) * (f n * ∑ k ∈ Finset.range n, r ^ k) =
        f n * -((r - 1) * ∑ k ∈ Finset.range n, r ^ k) := by ring
    _ = f n - f n * r ^ n := by rw [mul_geom_sum]; ring

end DirectedDistances.Tauberian
