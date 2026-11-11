/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricClassSpace
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso5

/-! # The geometric rooted map class pseudometric -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open scoped ENNReal

/-- Helper toward Definition 3.8: class distance satisfies the ultrametric
inequality. -/
theorem d39ClassDistance_ultrametric (c d e : D39GeomRootedMapClass) :
    d39ClassDistance c e ≤ max (d39ClassDistance c d) (d39ClassDistance d e) := by
  refine Quotient.inductionOn₃ c d e ?_
  intro A B C
  rw [d39ClassDistance_mk, d39ClassDistance_mk, d39ClassDistance_mk]
  exact d39GeomDistanceV2_ultrametric

/-- Helper toward Definition 3.8: class distance satisfies the triangle
inequality. -/
theorem d39ClassDistance_triangle (c d e : D39GeomRootedMapClass) :
    d39ClassDistance c e ≤ d39ClassDistance c d + d39ClassDistance d e := by
  exact (d39ClassDistance_ultrametric c d e).trans
    (max_le_add_of_nonneg (by positivity) (by positivity))

/-- Helper toward Definition 3.8: the geometric class distance is a
pseudo-emetric. -/
noncomputable instance : PseudoEMetricSpace D39GeomRootedMapClass where
  edist := d39ClassDistance
  edist_self := d39ClassDistance_self
  edist_comm := d39ClassDistance_comm
  edist_triangle := d39ClassDistance_triangle

/-- Helper toward Definition 3.8: a class distance is at most the radius
scale exactly when the representatives' rooted balls are isomorphic. -/
theorem d39ClassDistance_le_pow_iff_nonempty {r : ℕ} (hr : 0 < r)
    (A B : D39DomainRootedMap) :
    edist (Quotient.mk d39DomainSetoid A) (Quotient.mk d39DomainSetoid B) ≤
        (1 / 2 : ℝ≥0∞) ^ r ↔
      Nonempty (D39GeomBallIsoV2 r A.map A.root B.map B.root) := by
  change d39ClassDistance (Quotient.mk d39DomainSetoid A)
      (Quotient.mk d39DomainSetoid B) ≤
    (1 / 2 : ℝ≥0∞) ^ r ↔ _
  rw [d39ClassDistance_mk]
  exact d39GeomDistanceV2_le_iff_nonempty (M := A.map) (rho := A.root)
    (M' := B.map) (rho' := B.root) hr

end DirectedDistances.PaperProofs.Section3

end
