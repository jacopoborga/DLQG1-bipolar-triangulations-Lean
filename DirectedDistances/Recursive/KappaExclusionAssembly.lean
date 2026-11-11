/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.KappaExclusionAnalytic
public import DirectedDistances.Recursive.SDPQuadraticFromMaster
public import Mathlib.Probability.Independence.InfinitePi

/-! # Assembly of the SDP linear-bound exclusion

The explicit hypothesis `hgeo` below gives the estimate on the canonical
infinite product probability space with iid coordinates of law `mu_f f`.
This is the fixed realization allowed for the geometric input
`eqn-sdp-identify-*`). The estimate remains to be proved from map geometry.
This file assembles that input with the analytic contradiction and does not
present the conclusion as a paper result. -/

public section

namespace DirectedDistances.Recursive.SDPExpansion

open Asymptotics Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-- Assuming the explicit geometric input `hgeo` on the canonical infinite
product probability space carrying iid coordinates with law `mu_f f`, this
helper excludes the positive-κ branch. The input asserts the paper's estimate
inventory rows 4.3–4.8, `eqn-sdp-identify-*`). This is the fixed iid realization
permitted for `hgeo`; the map-geometry proof of the estimate is not included. -/
theorem sdp_kappa_eq_zero_of_linear_bound {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (hgeo : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤ ((Measure.infinitePi (fun _ : ℕ => mu_f f)).real
        {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1})) :
    let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
    κ = 0 := by
  let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
  let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
  have hD := sdp_real_transform_dichotomy_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  rcases hD with ⟨_, hzero | ⟨hκpos, hExp⟩⟩
  · exact hzero.1
  · have ha : 0 < a := by
      dsimp [a]
      exact Real.rpow_pos_of_pos (by positivity) _
    have hExpReal :
        (fun t : ℝ => integerCF f t -
          ((1 : ℂ) - (a : ℂ) * (t ^ (2 / 3 : ℝ) : ℝ))) =o[𝓝[>] (0 : ℝ)]
          (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
      simpa only [Complex.isLittleO_ofReal_right] using hExp
    haveI : IsProbabilityMeasure (mu_f f) := mu_f_isProbabilityMeasure hf hfs
    let P : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => mu_f f)
    let X : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i
    haveI : IsProbabilityMeasure P := by
      dsimp [P]
      infer_instance
    have hX : ∀ i, Measurable (X i) := by
      intro i
      dsimp [X]
      fun_prop
    have hindep : iIndepFun X P := by
      simpa only [X, P] using
        (ProbabilityTheory.iIndepFun_infinitePi
          (P := fun _ : ℕ => mu_f f)
          (X := fun _ : ℕ => fun x : ℝ => x)
          (by fun_prop))
    have hident : ∀ i, IdentDistrib (X i) (X 0) P P := by
      intro i
      refine ⟨(hX i).aemeasurable, (hX 0).aemeasurable, ?_⟩
      dsimp [X, P]
      rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]
    have hLaw : P.map (X 0) = mu_f f := by
      dsimp [X, P]
      exact Measure.infinitePi_map_eval (fun _ : ℕ => mu_f f) 0
    have hlinear : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
        1 - δ ≤ (P.real {ω | ∑ i ∈ Finset.range k, X i ω ≤
          2 * A * (k : ℝ) + 1}) := by
      intro δ hδ
      obtain ⟨A, hA⟩ := hgeo δ hδ
      exact ⟨A, fun k => by simpa [P, X] using hA k⟩
    exact False.elim (not_uniform_high_probability_linear_bound
      hf hfs hsymm ha hExpReal hX hindep hident hLaw hlinear)

/-- Under the same seven master-recursion premises and explicit geometric
input, the zero-κ positive-side expansion follows from the corresponding branch
of the transform dichotomy (`prop:asympt-exp`, -/
theorem sdp_kappa_zero_expansion_of_linear_bound {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (hgeo : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤ ((Measure.infinitePi (fun _ : ℕ => mu_f f)).real
        {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1})) :
    let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
    let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
    κ = 0 ∧
      (fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (b : ℂ) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)]
          (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) := by
  let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  have hκ := sdp_kappa_eq_zero_of_linear_bound
    hf hfs hg hgs hsymm hgsupp hrec hgeo
  have hD := sdp_real_transform_dichotomy_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  rcases hD with ⟨_, hzero | hpos⟩
  · exact hzero
  · exact False.elim ((ne_of_gt hpos.1) hκ)

end DirectedDistances.Recursive.SDPExpansion
