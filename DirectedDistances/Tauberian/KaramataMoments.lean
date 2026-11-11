/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction








public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology

/-- On the compact unit interval, convergence of all monomial moments implies
weak convergence of the actual probability measures, for any parameter filter. -/
theorem probabilityMeasure_tendsto_of_unitInterval_moments {ι : Type*} {l : Filter ι}
    (μs : ι → ProbabilityMeasure (Icc (0 : ℝ) 1))
    (μ : ProbabilityMeasure (Icc (0 : ℝ) 1))
    (hmom : ∀ n : ℕ, Tendsto
      (fun i : ι => ∫ x : Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂(μs i : Measure (Icc (0 : ℝ) 1)))
      l (𝓝 (∫ x : Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂(μ : Measure (Icc (0 : ℝ) 1))))) :
    Tendsto μs l (𝓝 μ) := by
  have hi (η : ProbabilityMeasure (Icc (0 : ℝ) 1)) (p : Polynomial ℝ) :
      Integrable (fun x : Icc (0 : ℝ) 1 => p.eval (x : ℝ))
        (η : Measure (Icc (0 : ℝ) 1)) := by
    exact (BoundedContinuousFunction.mkOfCompact
      (p.toContinuousMapOn (Icc (0 : ℝ) 1))).integrable _
  have hpoly (p : Polynomial ℝ) : Tendsto
      (fun i : ι => ∫ x : Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μs i : Measure (Icc (0 : ℝ) 1)))
      l (𝓝 (∫ x : Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μ : Measure (Icc (0 : ℝ) 1)))) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have he (η : ProbabilityMeasure (Icc (0 : ℝ) 1)) :
          (∫ x : Icc (0 : ℝ) 1, (p + q).eval (x : ℝ) ∂(η : Measure (Icc (0 : ℝ) 1))) =
            (∫ x : Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(η : Measure (Icc (0 : ℝ) 1))) +
              ∫ x : Icc (0 : ℝ) 1, q.eval (x : ℝ) ∂(η : Measure (Icc (0 : ℝ) 1)) := by
        simp only [Polynomial.eval_add]
        exact integral_add (hi η p) (hi η q)
      simpa only [he] using hp.add hq
    | monomial n a =>
      have he (η : ProbabilityMeasure (Icc (0 : ℝ) 1)) :
          (∫ x : Icc (0 : ℝ) 1, (Polynomial.monomial n a).eval (x : ℝ)
            ∂(η : Measure (Icc (0 : ℝ) 1))) =
              a * ∫ x : Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂(η : Measure (Icc (0 : ℝ) 1)) := by
        simp only [Polynomial.eval_monomial]
        exact integral_const_mul _ _
      simpa only [he] using (hmom n).const_mul a
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro f
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap (0 : ℝ) 1 f.toContinuousMap
    (ε / 3) hε3
  have hpoint (x : Icc (0 : ℝ) 1) : ‖p.eval (x : ℝ) - f x‖ ≤ ε / 3 := by
    have hh := (p.toContinuousMapOn (Icc (0 : ℝ) 1) - f.toContinuousMap).norm_coe_le_norm x
    exact hh.trans hp.le
  have herr (η : ProbabilityMeasure (Icc (0 : ℝ) 1)) :
      dist (∫ x : Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(η : Measure (Icc (0 : ℝ) 1)))
        (∫ x : Icc (0 : ℝ) 1, f x ∂(η : Measure (Icc (0 : ℝ) 1))) ≤ ε / 3 := by
    rw [dist_eq_norm, ← integral_sub (hi η p) (f.integrable _)]
    have hh := norm_integral_le_of_norm_le_const
      (μ := (η : Measure (Icc (0 : ℝ) 1))) (ae_of_all _ hpoint)
    simpa only [probReal_univ, mul_one] using hh
  have hevent := (Metric.tendsto_nhds.1 (hpoly p)) (ε / 3) hε3
  filter_upwards [hevent] with i hi'
  have herri := herr (μs i)
  rw [dist_comm] at herri
  let fi := ∫ x : Icc (0 : ℝ) 1, f x ∂(μs i : Measure (Icc (0 : ℝ) 1))
  let pi := ∫ x : Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μs i : Measure (Icc (0 : ℝ) 1))
  let p0 := ∫ x : Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μ : Measure (Icc (0 : ℝ) 1))
  let f0 := ∫ x : Icc (0 : ℝ) 1, f x ∂(μ : Measure (Icc (0 : ℝ) 1))
  change dist fi pi ≤ ε / 3 at herri
  change dist pi p0 < ε / 3 at hi'
  have herr0 := herr μ
  change dist p0 f0 ≤ ε / 3 at herr0
  change dist fi f0 < ε
  calc
    dist fi f0 ≤ dist fi pi + (dist pi p0 + dist p0 f0) :=
      (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
    _ < ε := by linarith only [herri, hi', herr0]

end DirectedDistances.Tauberian
