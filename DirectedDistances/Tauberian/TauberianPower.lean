/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.LaplaceFromBoundary
public import DirectedDistances.Tauberian.KaramataTauberian
public import DirectedDistances.Tauberian.MonotoneDensity
public import DirectedDistances.Tauberian.TailAsymptotic

/-! Supporting lemmas for paper labels `lem-tauberian` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.Tauberian
open Filter
open scoped Topology

/-- Removing an index shift from a power-normalized sequence limit. -/
theorem tendsto_power_limit_of_succ {u : ℕ → ℝ} {ρ C : ℝ}
    (h : Tendsto (fun N : ℕ => u (N + 1) / (N : ℝ) ^ ρ) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => u N / (N : ℝ) ^ ρ) atTop (𝓝 C) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hh : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 1) := by
      have hdiv := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
      have hi := (tendsto_inv_atTop_zero.comp hdiv)
      have hr := (tendsto_const_nhds (x := (1 : ℝ))).div
        ((tendsto_const_nhds (x := (1 : ℝ))).add hi) (by norm_num : (1 : ℝ) + 0 ≠ 0)
      simp only [add_zero, div_one] at hr
      apply hr.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
      change 1 / (1 + (N : ℝ)⁻¹) = (N : ℝ) / ((N : ℝ) + 1)
      field_simp
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hp := hn.rpow_const (p := ρ) (Or.inl one_ne_zero)
  simp only [Real.one_rpow] at hp
  apply (tendsto_add_atTop_iff_nat 1).1
  have hh := h.mul hp
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [Real.div_rpow hN'.le (Nat.cast_nonneg (N + 1))]
  field_simp

/-- The actual source boundary expansion forces the actual natural-tail
power limit, with the same explicit Gamma/cosine coefficient as A.2. -/
theorem tendsto_tail_power_of_boundary_expansion {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1)
    {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) {c : ℂ} (hc : c.re ≠ 0)
    (hb : (fun t : ℝ =>
      (∑' k, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    Tendsto (fun N : ℕ => (∑' j : ℕ, f (j + N)) / (N : ℝ) ^ (-ν)) atTop
      (𝓝 (-(c.re / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2))) := by
  let a : ℕ → ℝ := fun N => ∑' j : ℕ, f (j + (N + 1))
  have ha₀ : ∀ N, 0 ≤ a N := fun N => real_tail_nonneg f hf (N + 1)
  have htail := real_tail_antitone f hs.summable hf
  have ha₁ : ∀ N, a N ≤ 1 := by
    intro N
    have hh := htail (Nat.zero_le (N + 1))
    simpa only [Nat.add_zero, hs.tsum_eq] using hh
  have ha : Antitone a := fun N M hNM => htail (Nat.add_le_add_right hNM 1)
  obtain ⟨hη, hlim⟩ := tail_laplace_of_boundary_expansion hf hs hν₀ hν₁ hc hb
  have hτ : 0 < 1 - ν := sub_pos.mpr hν₁
  have hpartial := tendsto_partial_sum_range_of_laplace_power_limit a ha₀ ha₁ hτ hη hlim
  have hdensity := tendsto_density_of_antitone_partial_sum_power ha hpartial
  have hexp : 1 - ν - 1 = -ν := by ring
  rw [hexp] at hdensity
  have hΓ : Real.Gamma (1 - ν) ≠ 0 := (Real.Gamma_pos_of_pos hτ).ne'
  have hconst : (1 - ν) * (-(c.re / Real.cos (Real.pi * ν / 2)) /
      Real.Gamma (1 - ν + 1)) =
      -(c.re / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2) := by
    rw [Real.Gamma_add_one hτ.ne']
    field_simp
  rw [hconst] at hdensity
  exact tendsto_power_limit_of_succ hdensity

end DirectedDistances.Tauberian
