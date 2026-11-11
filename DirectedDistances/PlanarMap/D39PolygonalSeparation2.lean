/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWinding5
public import DirectedDistances.PlanarMap.D39PolygonalSeparation

/-! # Polygonal winding sides

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Topology

/-- Helper toward Proposition 5.16: the off-image points with nonzero winding
angle sum. -/
@[expose] def inside (c : Polyline) : Set ℂ :=
  {z | z ∉ c.image ∧ c.angleSum z ≠ 0}

/-- Helper toward Proposition 5.16: the off-image points with zero winding
angle sum. -/
@[expose] def outside (c : Polyline) : Set ℂ :=
  {z | z ∉ c.image ∧ c.angleSum z = 0}

/-- Helper toward Proposition 5.16: the winding-defined inside set of a closed
polyline is open. -/
theorem isOpen_inside (c : Polyline) (hclosed : c.start = c.finish) :
    IsOpen c.inside := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  change z ∉ c.image ∧ c.angleSum z ≠ 0 at hz
  have havoid : c.imageᶜ ∈ 𝓝 z :=
    c.isCompact_image.isClosed.isOpen_compl.mem_nhds hz.1
  obtain ⟨ε, hε, hconst⟩ := angleSum_locallyConstant c hclosed z hz.1
  have hball : {w : ℂ | dist w z < ε} ∈ 𝓝 z :=
    Metric.ball_mem_nhds z hε
  filter_upwards [havoid, hball] with w hwavoid hwball
  refine ⟨hwavoid, ?_⟩
  rw [hconst w hwavoid hwball]
  exact hz.2

/-- Helper toward Proposition 5.16: the winding-defined outside set of a
closed polyline is open. -/
theorem isOpen_outside (c : Polyline) (hclosed : c.start = c.finish) :
    IsOpen c.outside := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  change z ∉ c.image ∧ c.angleSum z = 0 at hz
  have havoid : c.imageᶜ ∈ 𝓝 z :=
    c.isCompact_image.isClosed.isOpen_compl.mem_nhds hz.1
  obtain ⟨ε, hε, hconst⟩ := angleSum_locallyConstant c hclosed z hz.1
  have hball : {w : ℂ | dist w z < ε} ∈ 𝓝 z :=
    Metric.ball_mem_nhds z hε
  filter_upwards [havoid, hball] with w hwavoid hwball
  refine ⟨hwavoid, ?_⟩
  rw [hconst w hwavoid hwball]
  exact hz.2

/-- Helper toward Proposition 5.16: the inside and outside sets partition the
complement of a closed polyline image. -/
theorem inside_union_outside (c : Polyline) :
    c.inside ∪ c.outside = c.imageᶜ := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact hz.1
    · exact hz.1
  · intro hz
    by_cases hzero : c.angleSum z = 0
    · exact Or.inr ⟨hz, hzero⟩
    · exact Or.inl ⟨hz, hzero⟩

/-- Helper toward Proposition 5.16: the inside and outside sets are disjoint. -/
theorem disjoint_inside_outside (c : Polyline) : Disjoint c.inside c.outside := by
  apply Set.disjoint_left.mpr
  intro z hzinside hzoutside
  exact hzinside.2 hzoutside.2

/-- Helper toward Proposition 5.16: the inside set of a closed polyline is
bounded. -/
theorem isBounded_inside (c : Polyline) (hclosed : c.start = c.finish) :
    Bornology.IsBounded c.inside := by
  obtain ⟨R, hR⟩ := exists_radius_angleSum_eq_zero c hclosed
  have hsub : c.inside ⊆ Metric.closedBall (0 : ℂ) (max R 0) := by
    intro z hz
    change z ∉ c.image ∧ c.angleSum z ≠ 0 at hz
    have hnorm : ‖z‖ ≤ max R 0 := by
      apply le_of_not_gt
      intro hgt
      have hgtR : R < ‖z‖ := lt_of_le_of_lt (le_max_left R 0) hgt
      exact hz.2 (hR z hgtR)
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  exact Metric.isBounded_closedBall.subset hsub

/-- Helper toward Proposition 5.16: every point sufficiently far from a
closed polyline lies in its winding-defined outside set. -/
theorem exists_radius_exterior_subset_outside (c : Polyline)
    (hclosed : c.start = c.finish) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → z ∈ c.outside := by
  obtain ⟨Rangle, hangle⟩ := exists_radius_angleSum_eq_zero c hclosed
  obtain ⟨Rimage, himage⟩ := c.isCompact_image.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max Rangle (max Rimage 0), ?_⟩
  intro z hz
  have hzangle : Rangle < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hzimage : max Rimage 0 < ‖z‖ :=
    lt_of_le_of_lt (le_max_right _ _) hz
  have hznot : z ∉ c.image := by
    intro hmem
    have hball := himage hmem
    have hnorm : ‖z‖ ≤ Rimage := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_left _ _) hzimage)) hnorm
  exact ⟨hznot, hangle z hzangle⟩

/-- Helper toward Proposition 5.16: the outside set is unbounded, witnessed
by points of arbitrarily large norm. -/
theorem outside_unbounded (c : Polyline) (hclosed : c.start = c.finish) :
    ∀ R : ℝ, ∃ z ∈ c.outside, R < ‖z‖ := by
  obtain ⟨R0, hR0⟩ := exists_radius_exterior_subset_outside c hclosed
  intro R
  obtain ⟨z, hz, hznorm⟩ :=
    exists_point_outside_image_union_of_norm_gt c c (max R R0)
  have hR0z : R0 < ‖z‖ :=
    lt_of_le_of_lt (le_max_right R R0) hznorm
  have hznot : z ∉ c.image := fun h => hz (Or.inl h)
  have hzoutside := hR0 z hR0z
  change z ∉ c.image ∧ c.angleSum z = 0 at hzoutside
  exact ⟨z, ⟨hznot, hzoutside.2⟩, lt_of_le_of_lt (le_max_left R R0) hznorm⟩

private theorem image_ofHead_append_tail (a : ℂ) (l : List ℂ) (q : Polyline)
    (hfinish : (ofHead a l).finish = q.start) :
    (ofHead a (l ++ q.points.tail)).image = (ofHead a l).image ∪ q.image := by
  induction l generalizing a with
  | nil =>
      have hstart : a = q.start := by
        simpa [ofHead, finish] using hfinish
      have hq : ofHead a q.points.tail = q := by
        cases q with
        | mk points hne =>
          cases points with
          | nil => exact (hne rfl).elim
          | cons b rest =>
              have hab : a = b := by simpa [start] using hstart
              subst b
              rfl
      change (ofHead a q.points.tail).image = _
      rw [hq]
      ext z
      constructor
      · intro hz
        exact Or.inr hz
      · rintro (hz | hz)
        · have hza : z = a := by simpa [image, ofHead, start] using hz
          subst z
          rw [hstart]
          exact Or.inl rfl
        · exact hz
  | cons b l ih =>
      have htail : (ofHead b l).finish = q.start := by
        simpa [ofHead, finish] using hfinish
      change (ofHead a (b :: (l ++ q.points.tail))).image = _
      calc
        (ofHead a (b :: (l ++ q.points.tail))).image =
            segment ℝ a b ∪ (ofHead b (l ++ q.points.tail)).image :=
          image_ofHead_cons a b (l ++ q.points.tail)
        _ = segment ℝ a b ∪ ((ofHead b l).image ∪ q.image) := by
          rw [ih b htail]
        _ = (ofHead a (b :: l)).image ∪ q.image := by
          rw [image_ofHead_cons]
          ac_rfl

/-- Helper toward Proposition 5.16: concatenate two polylines by joining the
last vertex of the first to the first vertex of the second without duplicating
that shared vertex. -/
@[expose] def concat (p q : Polyline) : Polyline :=
  ⟨p.points ++ q.points.tail, by
    cases hp : p.points with
    | nil => exact (p.nonempty hp).elim
    | cons a l => simp⟩

/-- Helper toward Proposition 5.16: when the join points agree, concatenation
has exactly the union of the two polyline images. -/
theorem image_concat (p q : Polyline) (hjoin : p.finish = q.start) :
    (concat p q).image = p.image ∪ q.image := by
  cases p with
  | mk points hne =>
      cases points with
      | nil => exact (hne rfl).elim
      | cons a l =>
          change (ofHead a (l ++ q.points.tail)).image =
            (ofHead a l).image ∪ q.image
          apply image_ofHead_append_tail
          simpa [ofHead, finish] using hjoin

/-- Helper toward Proposition 5.16: concatenation starts where its first
polyline starts. -/
@[simp] theorem start_concat (p q : Polyline) : (concat p q).start = p.start := by
  cases p with
  | mk points hne =>
      cases points with
      | nil => exact (hne rfl).elim
      | cons a l => rfl

/-- Helper toward Proposition 5.16: if the second polyline has at least two
vertices, concatenation ends where it ends. -/
theorem finish_concat (p q : Polyline) (hq : 2 ≤ q.points.length) :
    (concat p q).finish = q.finish := by
  cases p with
  | mk ppoints hp =>
      cases ppoints with
      | nil => exact (hp rfl).elim
      | cons a pl =>
          cases q with
          | mk qpoints hqne =>
              cases qpoints with
              | nil => simp at hq
              | cons b qtail =>
                  cases qtail with
                  | nil => simp at hq
                  | cons d qrest =>
                      simp [concat, finish]

/-- Helper toward Proposition 5.16: the closed polyline following `p` by the
reverse of `q` is represented by their endpoint-glued vertex list. -/
@[expose] def closedConcat (p q : Polyline) : Polyline := concat p q.reverse

/-- Helper toward Proposition 5.16: the closed concatenation has the image
union of the two endpoint-glued arcs. -/
theorem image_closedConcat (p q : Polyline) (hjoin : p.finish = q.finish) :
    (closedConcat p q).image = p.image ∪ q.image := by
  rw [closedConcat, image_concat p q.reverse (by simpa using hjoin)]
  rw [image_reverse_transfer]

/-- Helper toward Proposition 5.16: two polylines with common endpoints give
a closed concatenation when the second has at least two vertices. -/
theorem closed_closedConcat (p q : Polyline)
    (hstart : p.start = q.start)
    (hq : 2 ≤ q.points.length) :
    (closedConcat p q).start = (closedConcat p q).finish := by
  rw [closedConcat, start_concat, finish_concat]
  · simpa using hstart
  · simpa [reverse] using hq

/-- Helper toward Proposition 5.16: the frontier of the winding-defined
inside set is contained in the polyline image. -/
theorem frontier_inside_subset_image (c : Polyline)
    (hclosed : c.start = c.finish) : frontier c.inside ⊆ c.image := by
  have hopen : IsOpen c.outside := isOpen_outside c hclosed
  have hclosed' : IsClosed (c.image ∪ c.inside) := by
    have heq : c.image ∪ c.inside = c.outsideᶜ := by
      ext z
      by_cases hmem : z ∈ c.image
      · simp [outside, hmem]
      · simp [inside, outside, hmem]
    rw [heq]
    exact hopen.isClosed_compl
  intro z hz
  rw [frontier] at hz
  have hzS : z ∈ c.image ∪ c.inside :=
    closure_minimal Set.subset_union_right hclosed' hz.1
  rcases hzS with hzimage | hzinside
  · exact hzimage
  · have hinterior : z ∈ _root_.interior c.inside := by
      rw [(isOpen_inside c hclosed).interior_eq]
      exact hzinside
    exact (hz.2 hinterior).elim

/-- Helper toward Proposition 5.16: the frontier of the winding-defined
outside set is contained in the polyline image. -/
theorem frontier_outside_subset_image (c : Polyline)
    (hclosed : c.start = c.finish) : frontier c.outside ⊆ c.image := by
  have hopen : IsOpen c.inside := isOpen_inside c hclosed
  have hclosed' : IsClosed (c.image ∪ c.outside) := by
    have heq : c.image ∪ c.outside = c.insideᶜ := by
      ext z
      by_cases hmem : z ∈ c.image
      · simp [inside, hmem]
      · simp [inside, outside, hmem]
    rw [heq]
    exact hopen.isClosed_compl
  intro z hz
  rw [frontier] at hz
  have hzS : z ∈ c.image ∪ c.outside :=
    closure_minimal Set.subset_union_right hclosed' hz.1
  rcases hzS with hzimage | hzoutside
  · exact hzimage
  · have hinterior : z ∈ _root_.interior c.outside := by
      rw [(isOpen_outside c hclosed).interior_eq]
      exact hzoutside
    exact (hz.2 hinterior).elim
























end Polyline
end DirectedDistances.PlanarMap

end
