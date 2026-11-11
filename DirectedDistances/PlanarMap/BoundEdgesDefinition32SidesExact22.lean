/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact21
public import DirectedDistances.PlanarMap.D39PLFaceExtension3

/-! # Indexed cyclic edge transfer toward Definition 3.2

This file records the oriented edge index when a polygonal return is
attached to an extracted subarc. The source subarc extraction theorem in
SidesExact20 states image equality; it does not expose the list of vertices
of its existential witness. Identifying an original edge in that witness
therefore remains an open step. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

/- The extracted polyline stays the first chain in the replacement loop.
`point_boundaryConcat_left` therefore gives the exact index: an original
edge `i` remains edge `i`, with ordered endpoints and accumulation point
unchanged. -/

/-- Helper toward Definition 3.2: attaching a polygonal return preserves
the exact index, orientation, endpoints, and interior points of every edge
in the extracted subarc. -/
theorem Polyline.boundaryConcat_retains_oriented_edge32
    (p q : Polyline)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) :
    let c := p.boundaryConcat q
    c.point i = p.point i ∧ c.point (i + 1) = p.point (i + 1) ∧
      x ∈ c.segmentAt i := by
  let c := p.boundaryConcat q
  have hi0 : i < p.points.length := by omega
  have h0 : c.point i = p.point i :=
    Polyline.point_boundaryConcat_left p q i hi0
  have h1 : c.point (i + 1) = p.point (i + 1) :=
    Polyline.point_boundaryConcat_left p q (i + 1) hi
  have hseg : c.segmentAt i = p.segmentAt i := by
    exact Polyline.segmentAt_boundaryConcat_left p q i hi
  change c.point i = _ ∧ c.point (i + 1) = _ ∧ x ∈ c.segmentAt i
  exact ⟨h0, h1, hseg ▸ hx⟩

/-- Helper toward Definition 3.2: the signed winding obstruction of
SidesExact21 transfers to an original edge retained as the first chain of a
cyclic polygonal concatenation. -/
theorem Polyline.boundaryConcat_signed_edge_obstruction32
    (p q : Polyline)
    (hcyclic : (p.boundaryConcat q).IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    x ∉ closure {w : ℂ | w ∉ (p.boundaryConcat q).image ∧
        HasWinding ((p.boundaryConcat q).toPath.cast rfl (by
          rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
          exact hcyclic.2.1)) w 1 ∧
        (star ((p.boundaryConcat q).point (i + 1) -
          (p.boundaryConcat q).point i) * (w - x)).im < 0} ∧
    x ∉ closure {w : ℂ | w ∉ (p.boundaryConcat q).image ∧
        HasWinding ((p.boundaryConcat q).toPath.cast rfl (by
          rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
          exact hcyclic.2.1)) w (-1) ∧
        0 < (star ((p.boundaryConcat q).point (i + 1) -
          (p.boundaryConcat q).point i) * (w - x)).im} := by
  let c := p.boundaryConcat q
  have hi' : i + 1 < c.points.length := by
    rw [Polyline.length_boundaryConcat]
    have hp : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
    have hq : 0 < q.points.length := List.length_pos_iff.mpr q.nonempty
    omega
  have h0 : c.point i = p.point i :=
    Polyline.point_boundaryConcat_left p q i (by omega)
  have h1 : c.point (i + 1) = p.point (i + 1) :=
    Polyline.point_boundaryConcat_left p q (i + 1) hi
  have hx' : x ∈ c.segmentAt i := by
    have hseg : c.segmentAt i = p.segmentAt i := by
      simpa only [c] using Polyline.segmentAt_boundaryConcat_left p q i hi
    exact hseg ▸ hx
  have hxi' : x ≠ c.point i := by rw [h0]; exact hxi
  have hxi1' : x ≠ c.point (i + 1) := by rw [h1]; exact hxi1
  have hresult := c.not_mem_closure_wrong_side_winding_cyclic32
    hcyclic i hi' x hx' hxi' hxi1'
  simpa only [c] using hresult




































end DirectedDistances.PlanarMap

end
