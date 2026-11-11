/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Poisson
import Mathlib.Tactic.Ring.Basic

/-! # Positive-kernel transport of a circle barrier

Necessary infrastructure for the A.1 Poisson/model proof. The kernel is a
continuous nonnegative function on the unit circle. Its integral identities
are not assumed here; the consumer supplies the actual Poisson reproduction
theorems for its two model weights. -/

public section
namespace DirectedDistances.Tauberian

open Set Metric

/-- Transport a pointwise complex norm bound through a nonnegative circle
kernel. All circle integrals are genuine integrable averages; the coefficient
signs do not need additional hypotheses. -/
theorem norm_circleAverage_kernel_smul_le (k : ℂ → ℝ) (e : ℂ → ℂ)
    (p q : ℂ → ℝ) (hk : ContinuousOn k (sphere (0 : ℂ) 1))
    (he : ContinuousOn e (sphere (0 : ℂ) 1))
    (hp : ContinuousOn p (sphere (0 : ℂ) 1))
    (hq : ContinuousOn q (sphere (0 : ℂ) 1))
    (hk_nonneg : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ k z) (ε C : ℝ)
    (hbound : ∀ z ∈ sphere (0 : ℂ) 1, ‖e z‖ ≤ ε * q z + C * p z) :
    ‖Real.circleAverage (fun z : ℂ => k z • e z) 0 1‖ ≤
      ε * Real.circleAverage (fun z : ℂ => k z * q z) 0 1 +
        C * Real.circleAverage (fun z : ℂ => k z * p z) 0 1 := by
  have hi := (hk.smul he).norm.circleIntegrable (zero_le_one : (0 : ℝ) ≤ 1)
  have hiq := ((hk.mul hq).const_mul ε).circleIntegrable (zero_le_one : (0 : ℝ) ≤ 1)
  have hip := ((hk.mul hp).const_mul C).circleIntegrable (zero_le_one : (0 : ℝ) ≤ 1)
  simp only [Pi.mul_apply] at hiq hip
  calc
    _ ≤ Real.circleAverage (fun z : ℂ => ‖k z • e z‖) 0 1 :=
      Real.norm_circleAverage_le_circleAverage_norm
    _ ≤ Real.circleAverage (fun z : ℂ => ε * (k z * q z) + C * (k z * p z)) 0 1 := by
      apply Real.circleAverage_mono hi (hiq.add hip)
      intro z hz
      rw [abs_one] at hz
      calc
        ‖k z • e z‖ = k z * ‖e z‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hk_nonneg z hz)]
        _ ≤ k z * (ε * q z + C * p z) :=
          mul_le_mul_of_nonneg_left (hbound z hz) (hk_nonneg z hz)
        _ = ε * (k z * q z) + C * (k z * p z) := by ring
    _ = _ := by
      rw [Real.circleAverage_fun_add hiq hip]
      simp only [← smul_eq_mul, Real.circleAverage_fun_smul]

end DirectedDistances.Tauberian
