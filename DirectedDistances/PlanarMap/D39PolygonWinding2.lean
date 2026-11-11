/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWinding
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Signed-angle winding helpers for closed polygons

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

/-- Helper toward Proposition 5.16: away from the polygonal image, the
principal argument of each defined edge quotient lies strictly between
`-pi` and `pi`. -/
theorem edgeArgument_mem_Ioo (p : Polyline) (z : ℂ) (i : ℕ)
    (hi : i + 1 < p.points.length) (hz : z ∉ p.image) :
    Complex.arg ((p.point (i + 1) - z) / (p.point i - z)) ∈
      Set.Ioo (-Real.pi) Real.pi := by
  have hpimg : p.point i ∈ p.image := by
    change p.point i ∈ {p.start} ∪ {w | ∃ j, j + 1 < p.points.length ∧ w ∈ p.segmentAt j}
    exact Or.inr ⟨i, hi, left_mem_segment ℝ _ _⟩
  have hznotseg : z ∉ p.segmentAt i := by
    intro hseg
    exact hz (Or.inr ⟨i, hi, hseg⟩)
  have hpa : p.point i - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hz (h ▸ hpimg)
  let q : ℂ := (p.point (i + 1) - z) / (p.point i - z)
  have hupper : Complex.arg q < Real.pi := by
    apply Complex.arg_lt_pi_iff.mpr
    by_contra h
    have hparts := not_or.mp h
    have hqre : q.re < 0 := lt_of_not_ge hparts.1
    have hqim : q.im = 0 := by simpa using hparts.2
    have hqreal : q = (q.re : ℂ) := Complex.ext (by simp) hqim
    have hmul : p.point (i + 1) - z = (q.re : ℂ) * (p.point i - z) := by
      have hdiv : (p.point (i + 1) - z) / (p.point i - z) = (q.re : ℂ) := by
        simpa [q] using hqreal
      calc
        p.point (i + 1) - z =
            ((p.point (i + 1) - z) / (p.point i - z)) * (p.point i - z) := by
          field_simp [hpa]
        _ = (q.re : ℂ) * (p.point i - z) := by rw [← hqreal]
    have hsame : SameRay ℝ (z - p.point i) (p.point (i + 1) - z) := by
      rw [show z - p.point i = -(p.point i - z) by ring]
      rw [show p.point (i + 1) - z = (q.re : ℝ) • (p.point i - z) by
        rw [RCLike.real_smul_eq_coe_mul]
        exact hmul]
      exact (sameRay_neg_smul_right_iff (R := ℝ)).2 (Or.inl hqre.le)
    have hzseg : z ∈ p.segmentAt i := by
      change z ∈ segment ℝ (p.point i) (p.point (i + 1))
      exact (mem_segment_iff_sameRay (𝕜 := ℝ)).2 hsame
    exact hznotseg hzseg
  have hlower : -Real.pi < Complex.arg q := Complex.neg_pi_lt_arg q
  change Complex.arg q ∈ Set.Ioo (-Real.pi) Real.pi
  exact ⟨hlower, hupper⟩

end Polyline
end DirectedDistances.PlanarMap









































end
