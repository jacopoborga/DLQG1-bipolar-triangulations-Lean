/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.TailGeneratingFunction
public import DirectedDistances.Tauberian.MonotoneDensity
public import DirectedDistances.Tauberian.TauberianPower








public section
namespace DirectedDistances.Tauberian
open Filter
open scoped Topology

/-- A power limit for the actual tails of the normalized tail law forces the
original law's tail power limit, with its actual mean in the coefficient. -/
theorem tendsto_tail_power_of_normalized_integrated_tail {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1)
    (hm : Summable (fun n : ℕ => (n : ℝ) * f n))
    {c₁ ν C : ℝ} (hmean : (∑' n : ℕ, (n : ℝ) * f n) = c₁)
    (hc₁ : 0 < c₁) (_hν : 0 < ν)
    (hT : Tendsto (fun N : ℕ =>
      (∑' j : ℕ, (∑' k : ℕ, f (k + ((j + N) + 1))) / c₁) /
        (N : ℝ) ^ (-ν)) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => (∑' j : ℕ, f (j + N)) /
      (N : ℝ) ^ (-ν - 1)) atTop (𝓝 (ν * c₁ * C)) := by
  let g : ℕ → ℝ := fun N => (∑' j : ℕ, f (j + (N + 1))) / c₁
  have hm₀ : 0 < ∑' n : ℕ, (n : ℝ) * f n := by rw [hmean]; exact hc₁
  have hgprob := normalized_tail_coefficients hf hm hm₀
  rw [hmean] at hgprob
  have hgs : Summable g := hgprob.2.summable
  have htail := real_tail_antitone f hs.summable hf
  have hga : Antitone g := by
    intro N M hNM
    exact div_le_div_of_nonneg_right (htail (Nat.add_le_add_right hNM 1)) hc₁.le
  have hd := tendsto_density_of_antitone_tail_power hga hgs hT
  have hh := hd.mul_const c₁
  have hconst : (ν * C) * c₁ = ν * c₁ * C := by ring
  rw [hconst] at hh
  apply tendsto_power_limit_of_succ
  apply hh.congr'
  exact Eventually.of_forall (fun N => by
    change (((∑' j : ℕ, f (j + (N + 1))) / c₁) /
      (N : ℝ) ^ (-ν - 1)) * c₁ =
        (∑' j : ℕ, f (j + (N + 1))) / (N : ℝ) ^ (-ν - 1)
    field_simp [hc₁.ne'])

end DirectedDistances.Tauberian
