/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesSurj2

/-! # Local image condition for Definition 3.2 winding sides

neighborhood decomposition below isolates the image fact used by the
surjectivity-based contact lemmas. It does not establish the localized
dart-border-to-winding-side theorem or the exact v7 equivalences. -/

public section

namespace DirectedDistances.PlanarMap

open Set

namespace PLDrawing

/-- Helper toward Definition 3.2: on a set where every vertex position is
already covered by an arc, the drawing image agrees with the union of arc
images. This is the local image decomposition needed near a boundary arc. -/
theorem image_inter_eq_union_arcs_inter_of_local_vertex_coverage
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (N : Set ℂ)
    (hvertex : ∀ z, z ∈ Set.range P.pos → z ∈ N →
      z ∈ ⋃ d, (P.arc d).image) :
    P.image ∩ N = (⋃ d, (P.arc d).image) ∩ N := by
  ext z
  constructor
  · rintro ⟨hz, hN⟩
    change z ∈ Set.range P.pos ∨ (∃ d, z ∈ (P.arc d).image) at hz
    rcases hz with ⟨v, hv⟩ | ⟨d, hd⟩
    · exact ⟨hvertex z ⟨v, hv⟩ hN, hN⟩
    · exact ⟨Set.mem_iUnion.mpr ⟨d, hd⟩, hN⟩
  · rintro ⟨hz, hN⟩
    exact ⟨Or.inr (Set.mem_iUnion.mp hz), hN⟩

/-- Helper toward Definition 3.2: a vertex-free neighborhood has the local
image decomposition above. -/
theorem image_inter_eq_union_arcs_inter_of_no_vertices
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (N : Set ℂ)
    (hN : Disjoint (Set.range P.pos) N) :
    P.image ∩ N = (⋃ d, (P.arc d).image) ∩ N := by
  apply P.image_inter_eq_union_arcs_inter_of_local_vertex_coverage N
  intro z hz hzn
  exact (Set.disjoint_left.mp hN) hz hzn |>.elim

end PLDrawing


































































end DirectedDistances.PlanarMap

end
