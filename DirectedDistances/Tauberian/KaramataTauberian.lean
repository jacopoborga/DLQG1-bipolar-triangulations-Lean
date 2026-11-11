/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.KaramataTilted
public import DirectedDistances.Tauberian.KaramataGamma
import DirectedDistances.Tauberian.WeakCutoff
import DirectedDistances.Tauberian.GammaExponentialLaw

/-! # Desmoothing the actual tilted laws

Producer dependencies for the Laplace-to-tail theorem used in revised A.2/A.3.
The reciprocal cutoff is identified with genuine finite coefficient sums;
its limiting value comes from the actual Gamma exponential law. -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology ENNReal

/-- Inverse integer scales are constructed only with a positive integer. -/
@[expose] noncomputable def karamataInvNatScale (N : ℕ) (hN : 0 < N) :
    {s : ℝ // 0 < s} := ⟨(N : ℝ)⁻¹, inv_pos.2 (Nat.cast_pos.2 hN)⟩

/-- At the inverse integer scale, the reciprocal cutoff selects exactly
indices `n ≤ N`, and cancels their exponential tilt. -/
theorem integral_tiltedLaplaceLaw_reciprocal_cutoff_nat (a : ℕ → ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) (hapos : ∃ n, 0 < a n)
    (N : ℕ) (hN : 0 < N) :
    (∫ y : Icc (0 : ℝ) 1,
      (if Real.exp (-1) ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0)
      ∂(tiltedLaplaceLaw a ha₀ ha₁ hapos (karamataInvNatScale N hN) :
        Measure (Icc (0 : ℝ) 1))) =
      (∑ n ∈ Finset.range (N + 1), a n) /
        (∑' n : ℕ, a n * Real.exp (-(N : ℝ)⁻¹ * (n : ℝ))) := by
  let s := karamataInvNatScale N hN
  let p := tiltedLaplacePMF a ha₀ ha₁ hapos s
  let h := fun y : Icc (0 : ℝ) 1 =>
    if Real.exp (-1) ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0
  have hpoint : Measurable (laplaceExpPoint s) := measurable_of_countable _
  have hm : StronglyMeasurable h := (measurable_reciprocal_cutoff _).stronglyMeasurable
  have htest := integrable_reciprocal_cutoff (Real.exp_pos (-1))
    (tiltedLaplaceLaw a ha₀ ha₁ hapos s)
  change Integrable h (p.toMeasure.map (laplaceExpPoint s)) at htest
  have hi : Integrable (fun n : ℕ => h (laplaceExpPoint s n)) p.toMeasure :=
    (integrable_map_measure hm.aestronglyMeasurable hpoint.aemeasurable).1 htest
  change (∫ y : Icc (0 : ℝ) 1, h y ∂(p.toMeasure.map (laplaceExpPoint s))) = _
  rw [integral_map_of_stronglyMeasurable hpoint hm, PMF.integral_eq_tsum p _ hi]
  have hpw (n : ℕ) : (p n).toReal = a n * Real.exp (-(N : ℝ)⁻¹ * (n : ℝ)) /
      (∑' m : ℕ, a m * Real.exp (-(N : ℝ)⁻¹ * (m : ℝ))) := by
    change (tiltedLaplacePMF a ha₀ ha₁ hapos s n).toReal = _
    rw [tiltedLaplacePMF_apply, ENNReal.toReal_ofReal
      (normalized_laplace_nonneg a ha₀ ha₁ hapos s.property n)]
    rfl
  have hcut (n : ℕ) : Real.exp (-1) ≤ (laplaceExpPoint s n : ℝ) ↔ n ≤ N := by
    rw [laplaceExpPoint_coe]
    change Real.exp (-1) ≤ Real.exp (-(N : ℝ)⁻¹ * (n : ℝ)) ↔ n ≤ N
    rw [Real.exp_le_exp, neg_mul, neg_le_neg_iff, ← div_eq_inv_mul,
      div_le_iff₀ (Nat.cast_pos.2 hN : (0 : ℝ) < N), one_mul, Nat.cast_le]
  have hterm (n : ℕ) : (p n).toReal • h (laplaceExpPoint s n) =
      if n ∈ Finset.range (N + 1) then
        a n / (∑' m : ℕ, a m * Real.exp (-(N : ℝ)⁻¹ * (m : ℝ))) else 0 := by
    rw [hpw, smul_eq_mul]
    dsimp only [h]
    by_cases hn : n ≤ N
    · rw [ite_eq_left ((hcut n).2 hn), ite_eq_left (Finset.mem_range.2 (Nat.lt_succ_iff.2 hn)),
        laplaceExpPoint_coe]
      change (a n * Real.exp (-(N : ℝ)⁻¹ * (n : ℝ)) /
        (∑' m : ℕ, a m * Real.exp (-(N : ℝ)⁻¹ * (m : ℝ)))) *
          (Real.exp (-(N : ℝ)⁻¹ * (n : ℝ)))⁻¹ = _
      calc
        _ = (a n / (∑' m : ℕ, a m * Real.exp (-(N : ℝ)⁻¹ * (m : ℝ)))) *
            (Real.exp (-(N : ℝ)⁻¹ * (n : ℝ)) *
              (Real.exp (-(N : ℝ)⁻¹ * (n : ℝ)))⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
    · rw [ite_eq_right (fun hh => hn ((hcut n).1 hh)),
        ite_eq_right (fun hh => hn (Nat.lt_succ_iff.1 (Finset.mem_range.1 hh))), mul_zero]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => ite_eq_right hn)]
  simp only [Finset.sum_ite_mem, Finset.inter_self]
  exact (Finset.sum_div _ _ _).symm

/-- A target probability law with the Gamma monomial moments and a proved
cutoff value desmooths the actual tilted family to coefficient partial sums.
This is an internal consumer; the final theorem supplies the actual law. -/
theorem tendsto_partial_sum_closed_of_limitLaw (a : ℕ → ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {τ η C : ℝ}
    (_hτ : 0 < τ) (hη : 0 < η)
    (hlim : Tendsto (fun s : ℝ => s ^ τ *
      (∑' n : ℕ, a n * Real.exp (-s * (n : ℝ)))) (𝓝[>] (0 : ℝ)) (𝓝 η))
    (ν : ProbabilityMeasure (Icc (0 : ℝ) 1))
    (hmom : ∀ k : ℕ,
      (∫ y : Icc (0 : ℝ) 1, (y : ℝ) ^ k ∂(ν : Measure (Icc (0 : ℝ) 1))) =
        ((k : ℝ) + 1) ^ (-τ))
    (hna : (ν : Measure (Icc (0 : ℝ) 1)) {y | (y : ℝ) = Real.exp (-1)} = 0)
    (hcut : (∫ y : Icc (0 : ℝ) 1,
      (if Real.exp (-1) ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0)
        ∂(ν : Measure (Icc (0 : ℝ) 1))) = C) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), a n) / (N : ℝ) ^ τ)
      atTop (𝓝 (η * C)) := by
  have hapos := exists_pos_of_laplace_power_limit a ha₀ hη hlim
  let μs := tiltedLaplaceLaw a ha₀ ha₁ hapos
  let l := Filter.comap (fun s : {s : ℝ // 0 < s} => (s : ℝ)) (𝓝[>] (0 : ℝ))
  have hc : Tendsto (fun s : {s : ℝ // 0 < s} => (s : ℝ)) l (𝓝[>] (0 : ℝ)) :=
    tendsto_comap
  have hweak : Tendsto μs l (𝓝 ν) := by
    apply probabilityMeasure_tendsto_of_unitInterval_moments
    intro k
    rw [hmom k]
    have hh := tendsto_laplace_scale_ratio hη.ne'
      (show 0 < (k : ℝ) + 1 by positivity) hlim
    simpa only [μs, Function.comp_def, integral_tiltedLaplaceLaw_monomial] using hh.comp hc
  have hcutlim := tendsto_integral_reciprocal_cutoff hweak (Real.exp_pos (-1))
    (Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0)) hna
  rw [hcut] at hcutlim
  let σ := fun N : ℕ => karamataInvNatScale (N + 1) (Nat.zero_lt_succ N)
  have hσreal : Tendsto (fun N : ℕ => (σ N : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa only [σ, karamataInvNatScale, Nat.cast_add, Nat.cast_one, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact Eventually.of_forall (fun N => (σ N).property)
  have hσ : Tendsto σ atTop l := tendsto_comap_iff.2 hσreal
  have hh := (hlim.comp hσreal).mul (hcutlim.comp hσ)
  apply (tendsto_add_atTop_iff_nat 1).1
  apply hh.congr'
  exact Eventually.of_forall (fun N => by
    change ((σ N : ℝ) ^ τ * (∑' n : ℕ, a n * Real.exp (-(σ N : ℝ) * (n : ℝ)))) *
      (∫ y : Icc (0 : ℝ) 1,
        (if Real.exp (-1) ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0)
          ∂(tiltedLaplaceLaw a ha₀ ha₁ hapos (σ N) : Measure (Icc (0 : ℝ) 1))) = _
    rw [integral_tiltedLaplaceLaw_reciprocal_cutoff_nat]
    change ((N + 1 : ℕ) : ℝ)⁻¹ ^ τ *
        (∑' n : ℕ, a n * Real.exp (-((N + 1 : ℕ) : ℝ)⁻¹ * (n : ℝ))) *
      ((∑ n ∈ Finset.range ((N + 1) + 1), a n) /
        (∑' n : ℕ, a n * Real.exp (-((N + 1 : ℕ) : ℝ)⁻¹ * (n : ℝ)))) = _
    have hz := (bounded_laplace_pos a ha₀ ha₁ hapos (σ N).property).ne'
    change (∑' n : ℕ, a n * Real.exp (-((N + 1 : ℕ) : ℝ)⁻¹ * (n : ℝ))) ≠ 0 at hz
    rw [Real.inv_rpow (Nat.cast_nonneg (N + 1))]
    let A := ∑ n ∈ Finset.range ((N + 1) + 1), a n
    let Z := ∑' n : ℕ, a n * Real.exp (-((N + 1 : ℕ) : ℝ)⁻¹ * (n : ℝ))
    change (((N + 1 : ℕ) : ℝ) ^ τ)⁻¹ * Z * (A / Z) = A / ((N + 1 : ℕ) : ℝ) ^ τ
    have hZ : Z ≠ 0 := hz
    calc
      _ = (((N + 1 : ℕ) : ℝ) ^ τ)⁻¹ * (A * (Z * Z⁻¹)) := by ring
      _ = (((N + 1 : ℕ) : ℝ) ^ τ)⁻¹ * A := by rw [mul_inv_cancel₀ hZ, mul_one]
      _ = _ := by rw [div_eq_mul_inv, mul_comm])

/-- Boundedness of a coefficient sequence removes the single endpoint term
from the normalized Karamata partial sum. -/
theorem tendsto_partial_sum_range_of_closed (a : ℕ → ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {τ C : ℝ} (hτ : 0 < τ)
    (hclosed : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range (N + 1), a n) / (N : ℝ) ^ τ) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / (N : ℝ) ^ τ)
      atTop (𝓝 C) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-τ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hτ).comp tendsto_natCast_atTop_atTop
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => ‖a N‖) := by
    apply isBoundedUnder_of
    refine ⟨1, ?_⟩
    intro N
    rw [Real.norm_eq_abs, abs_of_nonneg (ha₀ N)]
    exact ha₁ N
  have hend : Tendsto (fun N : ℕ => a N / (N : ℝ) ^ τ) atTop (𝓝 0) := by
    apply (hp.zero_mul_isBoundedUnder_le hb).congr'
    exact Eventually.of_forall (fun N => by
      change (N : ℝ) ^ (-τ) * a N = a N / (N : ℝ) ^ τ
      rw [Real.rpow_neg (Nat.cast_nonneg N), div_eq_mul_inv, mul_comm])
  have hh := hclosed.sub hend
  simp only [sub_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun N => by
    change (∑ n ∈ Finset.range (N + 1), a n) / (N : ℝ) ^ τ - a N / (N : ℝ) ^ τ =
      (∑ n ∈ Finset.range N, a n) / (N : ℝ) ^ τ
    rw [Finset.sum_range_succ, add_div]
    ring)

/-- The actual Gamma comparison law discharges every limit-law obligation and
gives the closed-endpoint Karamata partial-sum limit. -/
theorem tendsto_partial_sum_closed_of_laplace_power_limit (a : ℕ → ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {τ η : ℝ}
    (hτ : 0 < τ) (hη : 0 < η)
    (hlim : Tendsto (fun s : ℝ => s ^ τ *
      (∑' n : ℕ, a n * Real.exp (-s * (n : ℝ)))) (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), a n) / (N : ℝ) ^ τ)
      atTop (𝓝 (η / Real.Gamma (τ + 1))) := by
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    tendsto_partial_sum_closed_of_limitLaw a ha₀ ha₁ hτ hη hlim
      (gammaExponentialLaw τ hτ) (integral_gammaExponentialLaw_monomial hτ)
      (gammaExponentialLaw_no_atom_exp_neg_one hτ)
      (integral_gammaExponentialLaw_reciprocal_cutoff hτ)

/-- The actual Laplace power asymptotic implies the standard `range N`
Karamata partial-sum asymptotic, with no assumed target law or tail conclusion. -/
theorem tendsto_partial_sum_range_of_laplace_power_limit (a : ℕ → ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {τ η : ℝ}
    (hτ : 0 < τ) (hη : 0 < η)
    (hlim : Tendsto (fun s : ℝ => s ^ τ *
      (∑' n : ℕ, a n * Real.exp (-s * (n : ℝ)))) (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / (N : ℝ) ^ τ)
      atTop (𝓝 (η / Real.Gamma (τ + 1))) :=
  tendsto_partial_sum_range_of_closed a ha₀ ha₁ hτ
    (tendsto_partial_sum_closed_of_laplace_power_limit a ha₀ ha₁ hτ hη hlim)

end DirectedDistances.Tauberian
