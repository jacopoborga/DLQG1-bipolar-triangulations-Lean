module

public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

/-! # Scalar stable limits from characteristic function expansions

Consumed external input for the heavy-tailed CLT step excluding `κ > 0` in
These helpers do not assert the functional convergence of the paper theorem. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology



theorem existsUnique_probabilityMeasure_of_tendsto_charFun
    (μ : ℕ → ProbabilityMeasure ℝ) {f : ℝ → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    ∃! μ₀ : ProbabilityMeasure ℝ,
      charFun μ₀ = f ∧ Tendsto μ atTop (𝓝 μ₀) := by
  have ht := isTightMeasureSet_of_tendsto_charFun hf h
  have hc : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by
      convert ht using 1
      ext m
      simp)
  obtain ⟨μ₀, -, φ, hφ, hμ₀⟩ :=
    hc.tendsto_subseq (fun n ↦ subset_closure (Set.mem_range_self n))
  have hcf : charFun μ₀ = f := by
    funext t
    exact tendsto_nhds_unique
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hμ₀ t)
      ((h t).comp hφ.tendsto_atTop)
  refine ⟨μ₀, ⟨hcf, ProbabilityMeasure.tendsto_of_tendsto_charFun ?_⟩, ?_⟩
  · intro t
    simpa only [hcf] using h t
  · intro ν hν
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.ext_of_charFun (hν.1.trans hcf.symm)

/-- Characteristic function of an iid normalized sum, with arbitrary real scale. -/
theorem charFun_mul_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (a t : ℝ) (n : ℕ) :
    charFun (P.map (fun ω ↦ a * ∑ k ∈ Finset.range n, X k ω)) t =
      charFun (P.map (X 0)) (a * t) ^ n := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp,
    (hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ ↦ mX _)]
  · simp [fun i ↦ (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ mX _

private theorem stable_scale_power {ν : ℝ} (hν : 0 < ν) (n : ℕ) (t : ℝ) :
    |(n : ℝ) ^ (-1 / ν) * t| ^ ν = |t| ^ ν / n := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_nonneg t),
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  rw [div_mul_cancel₀ _ hν.ne', Real.rpow_neg_one]
  ring

/-- The characteristic function power limit from an expansion at zero.
also a scalar ingredient for `thm-busemann-conv`. -/
theorem tendsto_charFun_stable_pow {μ : Measure ℝ} {c ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun μ t - (1 - (c : ℂ) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun μ ((n : ℝ) ^ (-1 / ν) * t) ^ n)
      atTop (𝓝 (Complex.exp (-(c * |t| ^ ν : ℝ)))) := by
  have hs : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-1 / ν) * t) atTop (𝓝 0) := by
    simpa only [neg_div, one_div, zero_mul, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (inv_pos.mpr hν)).comp
        tendsto_natCast_atTop_atTop).mul_const t
  have he := hexp.comp_tendsto hs
  have he' : (fun n : ℕ ↦ charFun μ ((n : ℝ) ^ (-1 / ν) * t) -
      (1 + (-(c * |t| ^ ν : ℝ) : ℂ) / n)) =o[atTop]
      (fun n : ℕ ↦ |t| ^ ν * (1 / (n : ℝ))) := by
    convert he using 1
    · funext n
      dsimp only [Function.comp_apply]
      rw [stable_scale_power hν]
      push_cast
      ring
    · funext n
      dsimp only [Function.comp_apply]
      rw [stable_scale_power hν]
      ring
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
  have hn : (fun n : ℕ ↦ ‖(1 / (n : ℂ))‖) =
      (fun n : ℕ ↦ ‖(1 / (n : ℝ))‖) := by simp
  rw [← Asymptotics.isLittleO_norm_right, hn, Asymptotics.isLittleO_norm_right]
  exact he'.of_const_mul_right

/-- Stable characteristic function limit for iid sums. Consumed external input -/
theorem tendsto_charFun_stable_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {c ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t - (1 - (c : ℂ) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun
      (P.map (fun ω ↦ (n : ℝ) ^ (-1 / ν) * ∑ k ∈ Finset.range n, X k ω)) t)
      atTop (𝓝 (Complex.exp (-(c * |t| ^ ν : ℝ)))) := by
  simp_rw [charFun_mul_sum hindep hident]
  exact tendsto_charFun_stable_pow hν hexp t

/-- An even stable characteristic function gives a symmetric law. -/
theorem map_neg_eq_of_charFun_stable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {c ν : ℝ} (hcf : ∀ t, charFun μ t = Complex.exp (-(c * |t| ^ ν : ℝ))) :
    μ.map (fun x : ℝ ↦ -x) = μ := by
  apply Measure.ext_of_charFun
  funext t
  have hm : (fun x : ℝ ↦ -x) = (fun x : ℝ ↦ (-1 : ℝ) * x) := by
    funext x
    ring
  rw [hm, charFun_map_mul, hcf, hcf]
  simp only [neg_one_mul, abs_neg]

/-- A positive stable exponent excludes every Dirac mass, by testing frequency one. -/
theorem ne_dirac_of_charFun_stable {μ : Measure ℝ} {c ν : ℝ} (hc : 0 < c)
    (hcf : ∀ t, charFun μ t = Complex.exp (-(c * |t| ^ ν : ℝ))) (x : ℝ) :
    μ ≠ Measure.dirac x := by
  intro hx
  have hnorm : ‖charFun μ 1‖ < 1 := by
    rw [hcf]
    simpa only [abs_one, Real.one_rpow, mul_one, ← Complex.ofReal_neg,
      Complex.norm_exp_ofReal] using Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  rw [hx, charFun_dirac, Complex.norm_exp_ofReal_mul_I] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

/-- A symmetric probability measure which is not the Dirac mass at zero has
positive mass on the positive half-line. This is the scalar nondegeneracy input -/
theorem measure_Ioi_zero_pos_of_symmetric {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ ↦ -x) = μ) (hne : μ ≠ Measure.dirac 0) :
    0 < μ (Set.Ioi 0) := by
  by_contra hpos
  have hz : μ (Set.Ioi 0) = 0 := le_antisymm (not_lt.mp hpos) zero_le
  have hn : μ (Set.Iio 0) = 0 := by
    have he := congrArg (fun m : Measure ℝ ↦ m (Set.Ioi 0)) hsym
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at he
    have hp : (fun x : ℝ ↦ -x) ⁻¹' Set.Ioi 0 = Set.Iio 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
    rw [hp, hz] at he
    exact he
  have hae : (fun x : ℝ ↦ x) =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    apply ae_iff.mpr
    have hset : {x : ℝ | ¬x = 0} = Set.Iio 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      exact ne_iff_lt_or_gt
    rw [hset]
    exact measure_union_null hn hz
  apply hne
  calc
    μ = μ.map (fun x : ℝ ↦ x) := Measure.map_id.symm
    _ = μ.map (fun _ ↦ (0 : ℝ)) := Measure.map_congr hae
    _ = Measure.dirac 0 := by simp only [Measure.map_const, measure_univ, one_smul]

/-- Existence, weak convergence, symmetry and nondegeneracy of the scalar stable
limit of iid sums. Consumed external input for the heavy-tailed CLT step in
The limiting random variable is the identity on the real line with the limiting law. -/
theorem exists_stableLaw_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t - (1 - (c : ℂ) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) :
    ∃ stableLaw : ProbabilityMeasure ℝ,
      (∀ t, charFun stableLaw t = Complex.exp (-(c * |t| ^ ν : ℝ))) ∧
      TendstoInDistribution
        (fun n : ℕ ↦ fun ω ↦ (n : ℝ) ^ (-1 / ν) * ∑ k ∈ Finset.range n, X k ω)
        atTop (fun x : ℝ ↦ x) (fun _ ↦ P) (stableLaw : Measure ℝ) ∧
      (∀ x, (stableLaw : Measure ℝ) ≠ Measure.dirac x) ∧
      (stableLaw : Measure ℝ).map (fun x : ℝ ↦ -x) = stableLaw ∧
      0 < (stableLaw : Measure ℝ) (Set.Ioi 0) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun n ↦
    ⟨P.map (fun ω ↦ (n : ℝ) ^ (-1 / ν) * ∑ k ∈ Finset.range n, X k ω),
      inferInstance⟩
  have hf : ContinuousAt (fun t : ℝ ↦ Complex.exp (-(c * |t| ^ ν : ℝ))) 0 := by
    have hp : Continuous (fun t : ℝ ↦ |t| ^ ν) :=
      (Real.continuous_rpow_const hν.le).comp continuous_abs
    fun_prop
  obtain ⟨stableLaw, hLaw, -⟩ := existsUnique_probabilityMeasure_of_tendsto_charFun μ hf
    (tendsto_charFun_stable_sum hindep hident hν hexp)
  have hcf : ∀ t, charFun stableLaw t = Complex.exp (-(c * |t| ^ ν : ℝ)) :=
    congrFun hLaw.1
  have hsym := map_neg_eq_of_charFun_stable hcf
  have hne := ne_dirac_of_charFun_stable hc hcf
  refine ⟨stableLaw, hcf, ?_, hne, hsym,
    measure_Ioi_zero_pos_of_symmetric hsym (hne 0)⟩
  apply TendstoInDistribution.of_tendsto_charFun (fun n ↦ ?_) (by fun_prop)
  · intro t
    simpa only [Measure.map_id', hcf] using
      tendsto_charFun_stable_sum hindep hident hν hexp t
  · exact (Measurable.const_mul
      (Finset.measurable_fun_sum _ (fun k _ ↦ hX k)) _).aemeasurable

end DirectedDistances.Probability
