/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLPolygonDiskChart2
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Arc normalization for polygon disk gluing

Helpers toward Proposition 5.16. The closed-cover gluing and whole-boundary
extension steps are imported from `D39PLPolygonDiskChart2`; this file records
the remaining proper-arc normalization dependency without assuming its result. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: the complement of a standard oriented
circle path is the open reverse path. This records the canonical arc-splitting
API used in the normalization attempt; it does not identify an arbitrary
embedded interval with a standard circle path. -/
theorem circlePath_compl_range_eq_reverse_open_path {x y : Circle} (hxy : x ≠ y) :
    (Set.range (Circle.path x y))ᶜ = Circle.path y x '' Set.Ioo (0 : unitInterval) 1 :=
  Circle.compl_range_path hxy

/-- Helper toward Proposition 5.16: the closure of the complement of a
standard circle path is the range of the reverse path, including both
endpoints. -/
theorem closure_circlePath_compl_range_eq_reverse_range {x y : Circle} (hxy : x ≠ y) :
    closure ((Set.range (Circle.path x y))ᶜ) = Set.range (Circle.path y x) := by
  rw [Circle.compl_range_path hxy]
  have hdense : closure (Set.Ioo (0 : unitInterval) 1) = Set.univ := by
    rw [closure_Ioo (zero_ne_one : (0 : unitInterval) ≠ 1)]
    ext t
    simp only [Set.mem_Icc, Set.mem_univ, iff_true]
    exact ⟨t.property.1, t.property.2⟩
  apply subset_antisymm
  · apply closure_minimal
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, rfl⟩
    · have hcompact : IsCompact (Set.range (Circle.path y x)) := by
        simpa only [Set.image_univ] using
          (isCompact_univ.image (Circle.path y x).continuous)
      exact hcompact.isClosed
  · rintro z ⟨t, rfl⟩
    have ht : t ∈ closure (Set.Ioo (0 : unitInterval) 1) := by
      rw [hdense]
      exact Set.mem_univ t
    have hc : ContinuousWithinAt (Circle.path y x) (Set.Ioo 0 1) t :=
      (Circle.path y x).continuous.continuousAt.continuousWithinAt
    exact hc.mem_closure_image ht

/-- Helper toward Proposition 5.16: the point of the upper half-disk diameter
with real coordinate `t`, retaining the endpoints `-1` and `1`. -/
@[expose] def polygonDiskUpperHalfDiameterPoint (t : Set.Icc (-1 : ℝ) 1) :
    polygonDiskUpperHalf :=
  ⟨⟨(t : ℝ), by
      have ht : |(t : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [t.property.1], t.property.2⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs] using ht⟩,
    by simp [polygonDiskUpperHalf]⟩



















































































end DirectedDistances.PlanarMap
