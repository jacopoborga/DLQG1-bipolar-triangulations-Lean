/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalSeparation3
public import DirectedDistances.PlanarMap.D39PolygonEdgeJump2

/-! # Cyclic polygon simplicity

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Filter Topology

/-- Helper toward Proposition 5.16: a closed polygonal chain with at least
three edges is cyclically simple when every edge is nondegenerate, consecutive
edges meet only at their common vertex, nonconsecutive edges are disjoint
except for the first and last edge, which meet only at the root. -/
@[expose] def IsCyclicSimple (c : Polyline) : Prop :=
  4 ≤ c.points.length ∧
  c.point 0 = c.point (c.points.length - 1) ∧
  (∀ i, i + 1 < c.points.length → c.point i ≠ c.point (i + 1)) ∧
  (∀ i, i + 2 < c.points.length →
    c.segmentAt i ∩ c.segmentAt (i + 1) = {c.point (i + 1)}) ∧
  (∀ i j, i + 1 < c.points.length → j + 1 < c.points.length → i + 1 < j →
    ¬ (i = 0 ∧ j + 2 = c.points.length) →
      Disjoint (c.segmentAt i) (c.segmentAt j)) ∧
  c.segmentAt 0 ∩ c.segmentAt (c.points.length - 2) = {c.point 0}

/-- Helper toward Proposition 5.16: a genuinely closed polygon with at least
three edges cannot satisfy the linear-chain predicate `IsSimple`. -/
theorem not_isSimple_closed_of_length_ge_four (c : Polyline)
    (hlen : 4 ≤ c.points.length) (hclosed : c.start = c.finish) :
    ¬ c.IsSimple := by
  intro hsimple
  rcases hsimple with ⟨hne, hadj, hdisj⟩
  have hpoint0 := point_zero_eq_start c
  have hpointLast := point_last_eq_finish c
  have hstart : c.start ∈ c.segmentAt 0 := by
    change c.start ∈ segment ℝ (c.point 0) (c.point 1)
    rw [← hpoint0]
    exact left_mem_segment ℝ (c.point 0) (c.point 1)
  have hfinish : c.finish ∈ c.segmentAt (c.points.length - 2) := by
    change c.finish ∈ segment ℝ (c.point (c.points.length - 2))
      (c.point (c.points.length - 2 + 1))
    rw [show c.points.length - 2 + 1 = c.points.length - 1 by omega,
      ← hpointLast]
    exact right_mem_segment ℝ (c.point (c.points.length - 2))
      (c.point (c.points.length - 1))
  have hfirstlast := hdisj 0 (c.points.length - 2) (by omega) (by omega) (by omega)
  exact (Set.disjoint_left.mp hfirstlast) hstart (by simpa [hclosed] using hfinish)

/-- Helper toward Proposition 5.16: a closed two-edge walk with three listed
vertices cannot satisfy the linear-chain predicate `IsSimple`. -/
theorem not_isSimple_closed_of_length_three (c : Polyline)
    (hlen : c.points.length = 3) (hclosed : c.start = c.finish) :
    ¬ c.IsSimple := by
  intro hsimple
  rcases hsimple with ⟨hne, hadj, hdisj⟩
  have hpointLast : c.point 2 = c.finish := by
    have h := point_last_eq_finish c
    rw [hlen] at h
    norm_num at h
    exact h
  have hstart0 : c.start ∈ c.segmentAt 0 := by
    rw [← point_zero_eq_start c]
    exact left_mem_segment ℝ (c.point 0) (c.point 1)
  have hstart1 : c.start ∈ c.segmentAt 1 := by
    rw [hclosed, ← hpointLast]
    exact right_mem_segment ℝ (c.point 1) (c.point 2)
  have hshared : c.start ∈ ({c.point 1} : Set ℂ) := by
    rw [← hadj 0 (by omega)]
    exact ⟨hstart0, hstart1⟩
  have hvertex : c.start = c.point 1 := by simpa using hshared
  have hne01 := hne 0 (by omega)
  apply hne01
  calc
    c.point 0 = c.start := point_zero_eq_start c
    _ = c.point 1 := hvertex

/-- Helper toward Proposition 5.16: a closed one-edge polyline cannot satisfy
the nondegeneracy clause of `IsSimple`. -/
theorem not_isSimple_closed_of_length_two (c : Polyline)
    (hlen : c.points.length = 2) (hclosed : c.start = c.finish) :
    ¬ c.IsSimple := by
  intro hsimple
  have hpointLast : c.point 1 = c.finish := by
    have h := point_last_eq_finish c
    rw [hlen] at h
    norm_num at h
    exact h
  have hne01 := hsimple.1 0 (by omega)
  apply hne01
  calc
    c.point 0 = c.start := point_zero_eq_start c
    _ = c.finish := hclosed
    _ = c.point 1 := hpointLast.symm

/-- Helper toward Proposition 5.16: an interior point of an edge in a
cyclically simple polygon lies on no other edge, including across the root. -/
theorem not_mem_segmentAt_of_ne_cyclic (c : Polyline) (hsimple : c.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < c.points.length) (x : ℂ)
    (hx : x ∈ c.segmentAt i) (hxi : x ≠ c.point i)
    (hxi1 : x ≠ c.point (i + 1))
    (j : ℕ) (hj : j + 1 < c.points.length) (hji : j ≠ i) :
    x ∉ c.segmentAt j := by
  rcases hsimple with ⟨hlen, hroot, hne, hadj, hdisj, hwrap⟩
  intro hxj
  rcases lt_or_gt_of_ne hji with hji' | hij
  · by_cases hnext : j + 1 = i
    · have hlen' : j + 2 < c.points.length := by omega
      have hinter := hadj j hlen'
      have hmem : x ∈ ({c.point (j + 1)} : Set ℂ) := by
        rw [← hinter]
        exact ⟨hxj, by simpa [hnext] using hx⟩
      have heq : x = c.point i := by simpa [hnext] using hmem
      exact hxi heq
    · by_cases hwrap' : j = 0 ∧ i + 2 = c.points.length
      · rcases hwrap' with ⟨rfl, hlast⟩
        have hidx : i + 1 = c.points.length - 1 := by omega
        have hsegi : i = c.points.length - 2 := by omega
        have hmem : x ∈ ({c.point 0} : Set ℂ) := by
          rw [← hwrap]
          exact ⟨hxj, by simpa [hsegi] using hx⟩
        have heq : x = c.point (i + 1) := by
          calc
            x = c.point 0 := by simpa using hmem
            _ = c.point (c.points.length - 1) := hroot
            _ = c.point (i + 1) := by rw [hidx]
        exact hxi1 heq
      · have hfar : j + 1 < i := by omega
        have hnotwrap : ¬ (j = 0 ∧ i + 2 = c.points.length) := hwrap'
        exact (Set.disjoint_left.mp (hdisj j i hj hi hfar hnotwrap)) hxj hx
  · by_cases hnext : i + 1 = j
    · have hlen' : i + 2 < c.points.length := by omega
      have hinter := hadj i hlen'
      have hmem : x ∈ ({c.point (i + 1)} : Set ℂ) := by
        rw [← hinter]
        exact ⟨hx, by simpa [hnext] using hxj⟩
      have heq : x = c.point (i + 1) := by simpa using hmem
      exact hxi1 heq
    · by_cases hwrap' : i = 0 ∧ j + 2 = c.points.length
      · rcases hwrap' with ⟨rfl, hlast⟩
        have hidx : j = c.points.length - 2 := by omega
        have hmem : x ∈ ({c.point 0} : Set ℂ) := by
          rw [← hwrap]
          exact ⟨hx, by simpa [hidx] using hxj⟩
        have heq : x = c.point 0 := by simpa using hmem
        exact hxi heq
      · have hfar : i + 1 < j := by omega
        exact (Set.disjoint_left.mp (hdisj i j hi hj hfar hwrap')) hx hxj

/-- Helper toward Proposition 5.16: a neighborhood of an interior point of
an edge of a cyclically simple polygon misses every other edge. -/
theorem exists_pos_ball_avoiding_nonincident_segments_cyclic (c : Polyline)
    (hsimple : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxi : x ≠ c.point i)
    (hxi1 : x ≠ c.point (i + 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℂ, dist y x < ε →
      ∀ j, j + 1 < c.points.length → j ≠ i → y ∉ c.segmentAt j := by
  classical
  let s := (Finset.range (c.points.length - 1)).filter (fun j => j ≠ i)
  have hsegcompact (j : ℕ) : IsCompact (c.segmentAt j) := by
    have hcont : Continuous (fun t : ℝ =>
        c.point j + t • (c.point (j + 1) - c.point j)) := by fun_prop
    rw [Polyline.segmentAt, segment_eq_image']
    exact isCompact_Icc.image hcont
  have hclosed : IsClosed (⋃ j ∈ s, c.segmentAt j) :=
    isClosed_biUnion_finset (fun j _ => (hsegcompact j).isClosed)
  have hxout : x ∉ ⋃ j ∈ s, c.segmentAt j := by
    intro hxU
    rw [Set.mem_iUnion₂] at hxU
    obtain ⟨j, hjs, hxj⟩ := hxU
    have hjs' := Finset.mem_filter.mp hjs
    have hj : j + 1 < c.points.length := by
      simp only [Finset.mem_range] at hjs'
      omega
    exact not_mem_segmentAt_of_ne_cyclic c hsimple i hi x hx hxi hxi1
      j hj hjs'.2 hxj
  have hev : ∀ᶠ y : ℂ in 𝓝 x, y ∉ ⋃ j ∈ s, c.segmentAt j :=
    hclosed.isOpen_compl.mem_nhds hxout
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro y hy j hj hji hyj
  apply hball hy
  rw [Set.mem_iUnion₂]
  exact ⟨j, Finset.mem_filter.mpr ⟨by simp only [Finset.mem_range]; omega, hji⟩, hyj⟩

/-- Helper toward Proposition 5.16: a sufficiently small left half-disc at
an interior point of a cyclically simple edge misses every edge. -/
theorem exists_leftHalfDisc_avoiding_edges_cyclic (c : Polyline)
    (hsimple : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxi : x ≠ c.point i)
    (hxi1 : x ≠ c.point (i + 1)) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, y ∈ leftHalfDisc x
      (c.point (i + 1) - c.point i) r →
      ∀ j, j + 1 < c.points.length → y ∉ c.segmentAt j := by
  obtain ⟨r, hr, havoid⟩ := exists_pos_ball_avoiding_nonincident_segments_cyclic
    c hsimple i hi x hx hxi hxi1
  refine ⟨r, hr, ?_⟩
  intro y hy j hj hyj
  change y ∈ Metric.ball x r ∧
    0 < (star (c.point (i + 1) - c.point i) * (y - x)).im at hy
  by_cases hji : j = i
  · subst j
    have hline := segment_subset_edgeLine (c.point i) (c.point (i + 1)) x hx hyj
    have hzero : (star (c.point (i + 1) - c.point i) * (y - x)).im = 0 := by
      simpa [edgeLine] using hline
    rw [hzero] at hy
    exact (lt_irrefl 0) hy.2
  · exact havoid y (by simpa [Metric.mem_ball] using hy.1) j hj hji hyj

/-- Helper toward Proposition 5.16: a sufficiently small right half-disc at
an interior point of a cyclically simple edge misses every edge. -/
theorem exists_rightHalfDisc_avoiding_edges_cyclic (c : Polyline)
    (hsimple : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxi : x ≠ c.point i)
    (hxi1 : x ≠ c.point (i + 1)) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, y ∈ rightHalfDisc x
      (c.point (i + 1) - c.point i) r →
      ∀ j, j + 1 < c.points.length → y ∉ c.segmentAt j := by
  obtain ⟨r, hr, havoid⟩ := exists_pos_ball_avoiding_nonincident_segments_cyclic
    c hsimple i hi x hx hxi hxi1
  refine ⟨r, hr, ?_⟩
  intro y hy j hj hyj
  change y ∈ Metric.ball x r ∧
    (star (c.point (i + 1) - c.point i) * (y - x)).im < 0 at hy
  by_cases hji : j = i
  · subst j
    have hline := segment_subset_edgeLine (c.point i) (c.point (i + 1)) x hx hyj
    have hzero : (star (c.point (i + 1) - c.point i) * (y - x)).im = 0 := by
      simpa [edgeLine] using hline
    rw [hzero] at hy
    exact (lt_irrefl 0) hy.2
  · exact havoid y (by simpa [Metric.mem_ball] using hy.1) j hj hji hyj

/-- Helper toward Proposition 5.16: a sufficiently small left half-disc at
an interior point of a cyclically simple edge misses the polygon image. -/
theorem exists_leftHalfDisc_disjoint_image_cyclic (c : Polyline)
    (hsimple : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxi : x ≠ c.point i)
    (hxi1 : x ≠ c.point (i + 1)) :
    ∃ r : ℝ, 0 < r ∧ Disjoint (leftHalfDisc x
      (c.point (i + 1) - c.point i) r) c.image := by
  obtain ⟨r, hr, havoid⟩ := exists_leftHalfDisc_avoiding_edges_cyclic
    c hsimple i hi x hx hxi hxi1
  refine ⟨r, hr, Set.disjoint_left.mpr ?_⟩
  intro z hzside hzimage
  change z ∈ Metric.ball x r ∧
    0 < (star (c.point (i + 1) - c.point i) * (z - x)).im at hzside
  change z ∈ {c.start} ∪
    {z | ∃ j, j + 1 < c.points.length ∧ z ∈ c.segmentAt j} at hzimage
  rcases hzimage with hzstart | ⟨j, hj, hzseg⟩
  · subst z
    have hstartseg : c.start ∈ c.segmentAt 0 := by
      rw [← point_zero_eq_start c]
      exact left_mem_segment ℝ (c.point 0) (c.point 1)
    have hvalid : 0 + 1 < c.points.length := by rcases hsimple with ⟨hlen, _⟩; omega
    exact havoid c.start ⟨hzside.1, hzside.2⟩ 0 hvalid hstartseg
  · exact havoid z ⟨hzside.1, hzside.2⟩ j hj hzseg

/-- Helper toward Proposition 5.16: a sufficiently small right half-disc at
an interior point of a cyclically simple edge misses the polygon image. -/
theorem exists_rightHalfDisc_disjoint_image_cyclic (c : Polyline)
    (hsimple : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxi : x ≠ c.point i)
    (hxi1 : x ≠ c.point (i + 1)) :
    ∃ r : ℝ, 0 < r ∧ Disjoint (rightHalfDisc x
      (c.point (i + 1) - c.point i) r) c.image := by
  obtain ⟨r, hr, havoid⟩ := exists_rightHalfDisc_avoiding_edges_cyclic
    c hsimple i hi x hx hxi hxi1
  refine ⟨r, hr, Set.disjoint_left.mpr ?_⟩
  intro z hzside hzimage
  change z ∈ Metric.ball x r ∧
    (star (c.point (i + 1) - c.point i) * (z - x)).im < 0 at hzside
  change z ∈ {c.start} ∪
    {z | ∃ j, j + 1 < c.points.length ∧ z ∈ c.segmentAt j} at hzimage
  rcases hzimage with hzstart | ⟨j, hj, hzseg⟩
  · subst z
    have hstartseg : c.start ∈ c.segmentAt 0 := by
      rw [← point_zero_eq_start c]
      exact left_mem_segment ℝ (c.point 0) (c.point 1)
    have hvalid : 0 + 1 < c.points.length := by rcases hsimple with ⟨hlen, _⟩; omega
    exact havoid c.start ⟨hzside.1, hzside.2⟩ 0 hvalid hstartseg
  · exact havoid z ⟨hzside.1, hzside.2⟩ j hj hzseg

/-- Helper toward Proposition 5.16: both local sides of an interior edge of
a cyclically simple polygon are open, nonempty, connected, and avoid the image
in one common positive-radius ball. -/
theorem exists_connected_edge_sides_cyclic (c : Polyline)
    (hsimple : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxi : x ≠ c.point i)
    (hxi1 : x ≠ c.point (i + 1)) :
    ∃ r : ℝ, 0 < r ∧
      IsOpen (leftHalfDisc x (c.point (i + 1) - c.point i) r) ∧
      IsOpen (rightHalfDisc x (c.point (i + 1) - c.point i) r) ∧
      (leftHalfDisc x (c.point (i + 1) - c.point i) r).Nonempty ∧
      (rightHalfDisc x (c.point (i + 1) - c.point i) r).Nonempty ∧
      IsConnected (leftHalfDisc x (c.point (i + 1) - c.point i) r) ∧
      IsConnected (rightHalfDisc x (c.point (i + 1) - c.point i) r) ∧
      Disjoint (leftHalfDisc x (c.point (i + 1) - c.point i) r) c.image ∧
      Disjoint (rightHalfDisc x (c.point (i + 1) - c.point i) r) c.image := by
  obtain ⟨rl, hrl, hdisl⟩ := exists_leftHalfDisc_disjoint_image_cyclic
    c hsimple i hi x hx hxi hxi1
  obtain ⟨rr, hrr, hdisr⟩ := exists_rightHalfDisc_disjoint_image_cyclic
    c hsimple i hi x hx hxi hxi1
  let r := min rl rr
  have hr : 0 < r := lt_min hrl hrr
  have hrl' : r ≤ rl := min_le_left _ _
  have hrr' : r ≤ rr := min_le_right _ _
  let d := c.point (i + 1) - c.point i
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr (Ne.symm (hsimple.2.2.1 i hi))
  have hleftsub : leftHalfDisc x d r ⊆ leftHalfDisc x d rl := by
    intro y hy
    exact ⟨Metric.ball_subset_ball hrl' hy.1, hy.2⟩
  have hrightsub : rightHalfDisc x d r ⊆ rightHalfDisc x d rr := by
    intro y hy
    exact ⟨Metric.ball_subset_ball hrr' hy.1, hy.2⟩
  have hdisl' : Disjoint (leftHalfDisc x d r) c.image := by
    apply Set.disjoint_left.mpr
    intro y hy hyimage
    exact (Set.disjoint_left.mp hdisl) (hleftsub hy) hyimage
  have hdisr' : Disjoint (rightHalfDisc x d r) c.image := by
    apply Set.disjoint_left.mpr
    intro y hy hyimage
    exact (Set.disjoint_left.mp hdisr) (hrightsub hy) hyimage
  refine ⟨r, hr, isOpen_leftHalfDisc x d r, isOpen_rightHalfDisc x d r, ?_, ?_, ?_, ?_, hdisl', hdisr'⟩
  · exact leftHalfDisc_nonempty x d r hd hr
  · exact rightHalfDisc_nonempty x d r hd hr
  · exact isConnected_leftHalfDisc x d r (leftHalfDisc_nonempty x d r hd hr)
  · exact isConnected_rightHalfDisc x d r (rightHalfDisc_nonempty x d r hd hr)

/-- Helper toward Proposition 5.16: the endpoint-glued concatenation is
closed, as a polyline, when its two arcs have the same endpoints. -/
theorem closedConcat_closed (p q : Polyline)
    (hlenq : 2 ≤ q.points.length) (hstart : p.start = q.start) :
    (closedConcat p q).start = (closedConcat p q).finish :=
  closed_closedConcat p q hstart hlenq
































































































































end Polyline
end DirectedDistances.PlanarMap

end
