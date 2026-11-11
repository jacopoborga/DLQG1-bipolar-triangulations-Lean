module

public import DirectedDistances.Probability.SkewedStableJointLaw

import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

private theorem continuousAt_skewStable_limitCF {k : ℕ} {t : ℕ → ℝ}
    {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν) :
    ContinuousAt (fun θ : EuclideanSpace ℝ (Fin k) => ∏ i : Fin k,
      Complex.exp (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
        ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ))))) 0 := by
  let b : ℝ → ℂ := fun x ↦
    (if 0 ≤ x then κp else κm) * ((|x| ^ ν : ℝ) : ℂ)
  have hbpow : Tendsto (fun x : ℝ ↦ (|x| ^ ν : ℝ)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ |x| ^ ν) 0 := by
      fun_prop
    simpa [Real.zero_rpow hν.ne'] using hc.tendsto
  let C : ℝ := ‖κp‖ + ‖κm‖
  have hb : Tendsto b (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ => C * (|x| ^ ν))
    · filter_upwards [] with x
      have hcoeff : ‖(if 0 ≤ x then κp else κm)‖ ≤ C := by
        by_cases hx : 0 ≤ x <;> simp [C, hx]
      have hpownonneg : 0 ≤ |x| ^ ν := Real.rpow_nonneg (abs_nonneg x) ν
      change ‖(if 0 ≤ x then κp else κm) * ((|x| ^ ν : ℝ) : ℂ)‖ ≤ C * (|x| ^ ν)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hpownonneg]
      exact mul_le_mul_of_nonneg_right hcoeff hpownonneg
    · simpa [C] using hbpow.const_mul C
  have hfactor (i : Fin k) :
      Tendsto (fun θ : EuclideanSpace ℝ (Fin k) =>
        Complex.exp (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) * b (θ i))))
        (𝓝 0) (𝓝 1) := by
    have hscale : Tendsto (fun x : ℝ =>
        -(((t (i.val + 1) - t i.val : ℝ) : ℂ) * b x)) (𝓝 0) (𝓝 0) := by
      simpa using (hb.const_mul (((t (i.val + 1) - t i.val : ℝ) : ℂ))).neg
    have hexp := (Complex.continuous_exp.continuousAt.tendsto).comp hscale
    have hcoord : Tendsto (fun θ : EuclideanSpace ℝ (Fin k) => θ i)
        (𝓝 0) (𝓝 0) := by
      exact (EuclideanSpace.proj i).continuous.continuousAt.tendsto
    change Tendsto
      ((Complex.exp ∘ fun x : ℝ =>
        -(((t (i.val + 1) - t i.val : ℝ) : ℂ) * b x)) ∘
        fun θ : EuclideanSpace ℝ (Fin k) => θ i) (𝓝 0) (𝓝 1)
    simpa only [Complex.exp_zero] using hexp.comp hcoord
  have hprod : Tendsto
      (fun θ : EuclideanSpace ℝ (Fin k) => ∏ i ∈ (Finset.univ : Finset (Fin k)),
        Complex.exp (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) * b (θ i))))
      (𝓝 0) (𝓝 (∏ i ∈ (Finset.univ : Finset (Fin k)), (1 : ℂ))) := by
    apply tendsto_finsetProd Finset.univ
    intro i hi
    exact hfactor i
  rw [ContinuousAt]
  simpa [b, hν.ne'] using hprod

/-- Scalar finite-dimensional helper toward E-STABLE / thm-busemann-conv
and joint convergence in distribution of finitely many consecutive disjoint-block normalized
iid sums; no functional convergence, path tightness or Busemann law identification is claimed;
not the paper result. -/
theorem exists_skewStable_blockVector_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hX : ∀ i, Measurable (X i)) {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν))
    {k : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (hmono : Monotone t) :
    ∃ μlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)),
      ∀ θ : EuclideanSpace ℝ (Fin k),
        charFun (μlim : Measure _) θ = ∏ i : Fin k, Complex.exp
          (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ)))) := by
  let μn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) := fun n =>
    ⟨P.map (skewStableBlockVector (k := k) (t := t) (ν := ν) X n), inferInstance⟩
  let f : EuclideanSpace ℝ (Fin k) → ℂ := fun θ => ∏ i : Fin k, Complex.exp
    (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
      ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ))))
  have hf : ContinuousAt f 0 := by
    exact continuousAt_skewStable_limitCF hν
  have hchar : ∀ θ, Tendsto (fun n => charFun (μn n : Measure _) θ) atTop (𝓝 (f θ)) := by
    intro θ
    simpa only [f, μn, ProbabilityMeasure.coe_mk] using
      (tendsto_charFun_skewStable_blockVector hindep hident hX hν hexp ht0 hmono θ)
  have htight : IsTightMeasureSet (Set.range fun n => (μn n : Measure _)) :=
    isTightMeasureSet_of_tendsto_charFun hf hchar
  let S : Set (ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) := Set.range μn
  have hcompact : IsCompact (closure S) := by
    apply isCompact_closure_of_isTightMeasureSet
    simpa [S, Set.range] using htight
  obtain ⟨μlim, hμlim_mem, ψ, hψmono, hψlim⟩ :=
    hcompact.tendsto_subseq fun n => subset_closure ⟨n, rfl⟩
  have hchar_subseq (θ : EuclideanSpace ℝ (Fin k)) :
      Tendsto (fun n => charFun (μn (ψ n) : Measure _) θ) atTop
        (𝓝 (f θ)) := (hchar θ).comp hψmono.tendsto_atTop
  have hchar_lim (θ : EuclideanSpace ℝ (Fin k)) :
      Tendsto (fun n => charFun (μn (ψ n) : Measure _) θ) atTop
        (𝓝 (charFun (μlim : Measure _) θ)) := by
    exact (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hψlim) θ
  refine ⟨μlim, fun θ => ?_⟩
  exact (tendsto_nhds_unique (hchar_subseq θ) (hchar_lim θ)).symm

/-- Joint convergence of the finite vector to the limit law constructed above. -/
theorem tendsto_skewStable_blockVector_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hX : ∀ i, Measurable (X i)) {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν))
    {k : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (hmono : Monotone t) :
    ∃ μlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)),
      (∀ θ : EuclideanSpace ℝ (Fin k),
        charFun (μlim : Measure _) θ = ∏ i : Fin k, Complex.exp
          (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ))))) ∧
      Tendsto
        (fun n : ℕ ↦
          (⟨P.map (skewStableBlockVector (k := k) (t := t) (ν := ν) X n),
            inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))))
        atTop (@nhds (ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
          MeasureTheory.ProbabilityMeasure.instTopologicalSpace μlim) := by
  obtain ⟨μlim, hμlim⟩ :=
    exists_skewStable_blockVector_limit hindep hident hX hν hexp ht0 hmono
  refine ⟨μlim, hμlim, ?_⟩
  apply (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2
  intro θ
  rw [hμlim θ]
  simpa only [ProbabilityMeasure.coe_mk] using
    (tendsto_charFun_skewStable_blockVector hindep hident hX hν hexp ht0 hmono θ)

end DirectedDistances.Probability
