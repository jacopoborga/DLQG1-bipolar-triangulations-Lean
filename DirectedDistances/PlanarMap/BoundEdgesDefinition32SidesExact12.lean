/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact11
public import DirectedDistances.PlanarMap.D39PolygonalSeparation2
public import DirectedDistances.PlanarMap.D39PolygonalSeparation4
import DirectedDistances.PlanarMap.D39PolygonalConnected2
import DirectedDistances.PlanarMap.D39PLPolygonDiskChart5
import DirectedDistances.PlanarMap.D39PolygonWindingBridge2







public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

namespace Polyline

/-- Helper toward Definition 3.2: the winding of a closed endpoint-glued
pair of simple polygonal arcs is bounded by one in absolute value. The
polygonal separation and cyclic-simplicity results supply the Jordan-region
bound used here. -/
theorem closedConcat_hasWinding_bounds32 (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish)
    (hne : p.start ≠ p.finish)
    (hint : p.image ∩ q.image = {p.start, p.finish})
    (w : ℂ) (n : ℤ)
    (havoid : w ∉ p.image ∪ q.image)
    (hw : HasWinding
      ((closedConcat p q).toPath.cast rfl
        (closedConcat_closed p q hlenq hstart)) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  let c := closedConcat p q
  have hclosed : c.start = c.finish :=
    closedConcat_closed p q hlenq hstart
  have hc : c.IsCyclicSimple :=
    closedConcat_isCyclicSimple p q hp hq hlenp hlenq hstart hfinish hne hint
  have himage : c.image = p.image ∪ q.image :=
    image_closedConcat p q hfinish
  obtain ⟨B, U, _, _, _, _, _, hcover, _, _, _, _⟩ :=
    exists_polygonal_separation p q hp hq hlenp hlenq hstart hfinish hne hint
  have hBU : B ∪ U = c.imageᶜ := by
    rw [himage]
    exact hcover
  have hwBU : w ∈ B ∪ U := by
    rw [hcover]
    exact havoid
  have havoid' : w ∉ c.image := by
    have hwcomp : w ∈ c.imageᶜ := by
      rw [← hBU]
      exact hwBU
    exact hwcomp
  have hangle : c.angleSum w = (n : ℝ) := by
    exact (hasWinding_iff_angleSum_eq_int c hclosed w n havoid').mp
      (by simpa only [c] using hw)
  by_cases hz : c.angleSum w = 0
  · have hn0 : (n : ℝ) = 0 := by
      rw [← hangle]
      exact hz
    have hn : n = 0 := by exact_mod_cast hn0
    omega
  · have hwinside : w ∈ c.inside := ⟨havoid', hz⟩
    have habs := c.abs_angleSum_eq_one_of_mem_inside hc w hwinside
    have hnabs : |(n : ℝ)| = 1 := by
      rw [← hangle]
      exact habs
    have hn : n = 1 ∨ n = -1 := by
      rcases eq_or_eq_neg_of_abs_eq hnabs with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    rcases hn with hn | hn <;> omega

end Polyline




































































































































end DirectedDistances.PlanarMap

end
