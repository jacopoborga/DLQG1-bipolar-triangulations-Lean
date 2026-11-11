/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.RegularVariationStaircase
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.BigOperators.Intervals

/-! # Monotone density from power asymptotics of partial sums

The discrete monotone density step needed by revised Appendix A.2 is proved
from finite block sums and the derivative of the real power function. -/

public section
namespace DirectedDistances.Tauberian
open Filter Finset
open scoped Topology

/-- An antitone sequence bounds each forward block by its initial value. -/
theorem sum_range_sub_le_mul_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    {N M : ℕ} (hNM : N ≤ M) :
    (∑ k ∈ range M, a k) - (∑ k ∈ range N, a k) ≤ (M - N : ℕ) * a N := by
  rw [← sum_Ico_eq_sub _ hNM]
  calc
    _ ≤ ∑ _k ∈ Ico N M, a N := sum_le_sum fun k hk => ha (mem_Ico.mp hk).1
    _ = _ := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- An antitone sequence bounds each backward block by its final value. -/
theorem mul_le_sum_range_sub_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    {M N : ℕ} (hMN : M ≤ N) :
    (N - M : ℕ) * a N ≤ (∑ k ∈ range N, a k) - (∑ k ∈ range M, a k) := by
  rw [← sum_Ico_eq_sub _ hMN]
  calc
    _ = ∑ _k ∈ Ico M N, a N := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum fun k hk => ha (mem_Ico.mp hk).2.le

/-- The floor of a fixed positive multiple has the expected relative size. -/
theorem tendsto_floor_mul_div {u : ℝ} (hu : 0 < u) :
    Tendsto (fun N : ℕ => (⌊u * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)) atTop (𝓝 u) := by
  have ht : Tendsto (fun N : ℕ => u * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hu
  have h := (tendsto_nat_floor_div_atTop.comp ht).mul_const u
  have hs : Tendsto (fun N : ℕ => ((⌊u * (N : ℝ)⌋₊ : ℝ) /
      (u * (N : ℝ))) * u) atTop (𝓝 u) := by simpa only [one_mul, Function.comp_apply] using h
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Power-normalized partial sums have their actual scaled floor-index limit. -/
theorem tendsto_floor_scaled_of_power_limit (B : ℕ → ℝ) {C τ u : ℝ}
    (hu : 0 < u)
    (hB : Tendsto (fun N : ℕ => B N / (N : ℝ) ^ τ) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => B ⌊u * (N : ℝ)⌋₊ / (N : ℝ) ^ τ)
      atTop (𝓝 (C * u ^ τ)) := by
  have hidx : Tendsto (fun N : ℕ => ⌊u * (N : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hu)
  have hp := (Real.continuousAt_rpow_const u τ (Or.inl hu.ne')).tendsto.comp
    (tendsto_floor_mul_div hu)
  have hh := (hB.comp hidx).mul hp
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hidx.eventually (eventually_gt_atTop (0 : ℕ))] with N hN hM
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < (⌊u * (N : ℝ)⌋₊ : ℝ) := by exact_mod_cast hM
  dsimp only [Function.comp_apply]
  rw [Real.div_rpow hM0.le hN0.le]
  field_simp [(Real.rpow_pos_of_pos hM0 τ).ne', (Real.rpow_pos_of_pos hN0 τ).ne']

/-- A forward normalized block slope is below the normalized density. -/
theorem normalized_block_slope_le {a : ℕ → ℝ} (ha : Antitone a)
    {N M : ℕ} (hN : 0 < N) (hNM : N < M) (τ : ℝ) :
    (((∑ k ∈ range M, a k) / (N : ℝ) ^ τ) -
      ((∑ k ∈ range N, a k) / (N : ℝ) ^ τ)) /
        ((M : ℝ) / (N : ℝ) - 1) ≤ a N * (N : ℝ) / (N : ℝ) ^ τ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hmn : (N : ℝ) < M := by exact_mod_cast hNM
  have hp := Real.rpow_pos_of_pos hn τ
  have hd : 0 < (M : ℝ) / (N : ℝ) - 1 := by
    rw [sub_pos, one_lt_div hn]; exact hmn
  rw [div_le_iff₀ hd]
  have hb := sum_range_sub_le_mul_of_antitone ha hNM.le
  rw [Nat.cast_sub hNM.le] at hb
  have hr : (a N * (N : ℝ) / (N : ℝ) ^ τ) * ((M : ℝ) / (N : ℝ) - 1) =
      (((M : ℝ) - N) * a N) / (N : ℝ) ^ τ := by field_simp
  rw [hr, ← sub_div, div_le_div_iff_of_pos_right hp]
  exact hb

/-- A backward normalized block slope is above the normalized density. -/
theorem le_normalized_block_slope {a : ℕ → ℝ} (ha : Antitone a)
    {M N : ℕ} (hN : 0 < N) (hMN : M < N) (τ : ℝ) :
    a N * (N : ℝ) / (N : ℝ) ^ τ ≤
      (((∑ k ∈ range M, a k) / (N : ℝ) ^ τ) -
        ((∑ k ∈ range N, a k) / (N : ℝ) ^ τ)) /
          ((M : ℝ) / (N : ℝ) - 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hmn : (M : ℝ) < N := by exact_mod_cast hMN
  have hp := Real.rpow_pos_of_pos hn τ
  have hd : (M : ℝ) / (N : ℝ) - 1 < 0 := by
    rw [sub_neg, div_lt_one hn]; exact hmn
  rw [le_div_iff_of_neg hd]
  have hb := mul_le_sum_range_sub_of_antitone ha hMN.le
  rw [Nat.cast_sub hMN.le] at hb
  have hr : (a N * (N : ℝ) / (N : ℝ) ^ τ) * ((M : ℝ) / (N : ℝ) - 1) =
      (((M : ℝ) - N) * a N) / (N : ℝ) ^ τ := by field_simp
  rw [hr, ← sub_div, div_le_div_iff_of_pos_right hp]
  linarith only [hb]

/-- Fixed scaled block slopes converge using only the original power limit. -/
theorem tendsto_normalized_floor_block_slope (B : ℕ → ℝ) {C τ u : ℝ}
    (hu : 0 < u) (hu1 : u ≠ 1)
    (hB : Tendsto (fun N : ℕ => B N / (N : ℝ) ^ τ) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => (B ⌊u * (N : ℝ)⌋₊ / (N : ℝ) ^ τ -
      B N / (N : ℝ) ^ τ) / ((⌊u * (N : ℝ)⌋₊ : ℝ) / (N : ℝ) - 1))
      atTop (𝓝 ((C * u ^ τ - C) / (u - 1))) := by
  exact ((tendsto_floor_scaled_of_power_limit B hu hB).sub hB).div
    ((tendsto_floor_mul_div hu).sub_const 1) (sub_ne_zero.mpr hu1)

private theorem tendsto_density_of_antitone_primitive_power {a B : ℕ → ℝ}
    (ha : Antitone a) (hprimitive : ∀ N, B N - B 0 = ∑ k ∈ range N, a k)
    {C τ : ℝ}
    (hB : Tendsto (fun N : ℕ => B N / (N : ℝ) ^ τ)
      atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => a N / (N : ℝ) ^ (τ - 1)) atTop (𝓝 (τ * C)) := by
  have hd : HasDerivAt (fun u : ℝ => C * u ^ τ) (C * τ) 1 := by
    simpa only [Real.one_rpow, mul_one] using
      (Real.hasDerivAt_rpow_const (x := 1) (p := τ) (Or.inl one_ne_zero)).const_mul C
  have hslope : slope (fun u : ℝ => C * u ^ τ) 1 =
      (fun u : ℝ => (C * u ^ τ - C) / (u - 1)) := by
    funext u
    rw [slope_def_field]
    simp only [Real.one_rpow, mul_one]
  have hright : Tendsto (fun u : ℝ => (C * u ^ τ - C) / (u - 1))
      (𝓝[>] 1) (𝓝 (τ * C)) := by
    simpa only [hslope, mul_comm C τ] using
      hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 1)
  have hleft : Tendsto (fun u : ℝ => (C * u ^ τ - C) / (u - 1))
      (𝓝[<] 1) (𝓝 (τ * C)) := by
    simpa only [hslope, mul_comm C τ] using
      hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1)
  have heq (M N : ℕ) : B M / (N : ℝ) ^ τ - B N / (N : ℝ) ^ τ =
      (∑ k ∈ range M, a k) / (N : ℝ) ^ τ -
        (∑ k ∈ range N, a k) / (N : ℝ) ^ τ := by
    rw [← sub_div, ← sub_div]
    congr 1
    have hM := hprimitive M
    have hN := hprimitive N
    linarith only [hM, hN]
  have hmain : Tendsto (fun N : ℕ => a N * (N : ℝ) / (N : ℝ) ^ τ)
      atTop (𝓝 (τ * C)) := by
    apply tendsto_order.2
    constructor
    · intro b hb
      obtain ⟨u, hu1, hub⟩ := ((show ∀ᶠ u : ℝ in 𝓝[>] 1, 1 < u from self_mem_nhdsWithin).and
        (hright.eventually (Ioi_mem_nhds hb))).exists
      change 1 < u at hu1
      have hu : 0 < u := lt_trans zero_lt_one hu1
      have hq := tendsto_normalized_floor_block_slope
        B hu (ne_of_gt hu1) hB
      have hi := (tendsto_floor_mul_div hu).eventually (Ioi_mem_nhds hu1)
      filter_upwards [hq.eventually (Ioi_mem_nhds hub), hi,
        eventually_gt_atTop (0 : ℕ)] with N hqN hiN hN
      have hn : (0 : ℝ) < N := by exact_mod_cast hN
      have hNM : N < ⌊u * (N : ℝ)⌋₊ := by
        have hx := (one_lt_div hn).1 hiN
        exact_mod_cast hx
      rw [heq] at hqN
      exact hqN.trans_le (normalized_block_slope_le ha hN hNM τ)
    · intro b hb
      have hp : ∀ᶠ u : ℝ in 𝓝[<] 1, 0 < u :=
        nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)
      obtain ⟨u, hu1, hu, hub⟩ := ((show ∀ᶠ u : ℝ in 𝓝[<] 1, u < 1 from self_mem_nhdsWithin).and
        (hp.and (hleft.eventually (Iio_mem_nhds hb)))).exists
      change u < 1 at hu1
      have hq := tendsto_normalized_floor_block_slope
        B hu (ne_of_lt hu1) hB
      have hi := (tendsto_floor_mul_div hu).eventually (Iio_mem_nhds hu1)
      filter_upwards [hq.eventually (Iio_mem_nhds hub), hi,
        eventually_gt_atTop (0 : ℕ)] with N hqN hiN hN
      have hn : (0 : ℝ) < N := by exact_mod_cast hN
      have hMN : ⌊u * (N : ℝ)⌋₊ < N := by
        have hx := (div_lt_one hn).1 hiN
        exact_mod_cast hx
      rw [heq] at hqN
      exact (le_normalized_block_slope ha hN hMN τ).trans_lt hqN
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Real.rpow_sub_one hn, div_div_eq_mul_div]

/-- Discrete monotone density: power asymptotics of the actual partial sums
force the corresponding density asymptotic. No density limit is assumed.
The generic real-exponent form includes the A.2 regime `0<τ<1`, `C>0`. -/
theorem tendsto_density_of_antitone_partial_sum_power {a : ℕ → ℝ}
    (ha : Antitone a) {C τ : ℝ}
    (hB : Tendsto (fun N : ℕ => (∑ k ∈ range N, a k) / (N : ℝ) ^ τ)
      atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => a N / (N : ℝ) ^ (τ - 1)) atTop (𝓝 (τ * C)) := by
  apply tendsto_density_of_antitone_primitive_power ha _ hB
  intro N
  rw [sum_range_zero, sub_zero]

/-- Discrete monotone density for integrated tails, as needed for A.3:
the power limit of the actual tail sums forces the density limit. -/
theorem tendsto_density_of_antitone_tail_power {a : ℕ → ℝ}
    (ha : Antitone a) (hs : Summable a) {C ν : ℝ}
    (hT : Tendsto (fun N : ℕ => (∑' j : ℕ, a (j + N)) / (N : ℝ) ^ (-ν))
      atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => a N / (N : ℝ) ^ (-ν - 1)) atTop (𝓝 (ν * C)) := by
  have hprimitive (N : ℕ) :
      -(∑' j : ℕ, a (j + N)) - -(∑' j : ℕ, a (j + 0)) =
        ∑ k ∈ range N, a k := by
    simp only [Nat.add_zero]
    have h := hs.sum_add_tsum_nat_add N
    linarith only [h]
  have ht : Tendsto (fun N : ℕ => -(∑' j : ℕ, a (j + N)) / (N : ℝ) ^ (-ν))
      atTop (𝓝 (-C)) := by
    simpa only [neg_div] using hT.neg
  simpa only [neg_mul_neg] using
    (tendsto_density_of_antitone_primitive_power ha hprimitive ht)

end DirectedDistances.Tauberian
