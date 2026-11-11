/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRootedIso
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation4

/-! # Stage drawing frontier incidence

This file makes no paper-completion claim. -/

public section

namespace DirectedDistances.PlanarMap.PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
  {vert : D → V} (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16. A named vertex lies on a closed dart arc
exactly when it is one of that dart's endpoints. The interior of every PL arc
avoids the drawing's named vertex positions. -/
theorem mem_pos_arc_image_iff_endpoint (d : D) (v : V) :
    P.pos v ∈ (P.arc d).image ↔ vert d = v ∨ vert (flip d) = v := by
  constructor
  · intro hv
    by_contra hnot
    have hne : ¬ (P.pos v = (P.arc d).start ∨ P.pos v = (P.arc d).finish) := by
      intro h
      rcases h with h | h
      · apply hnot
        left
        apply P.pos_injective
        exact (P.arc_start d).symm.trans h.symm
      · apply hnot
        right
        apply P.pos_injective
        exact (P.arc_finish d).symm.trans h.symm
    have hint : P.pos v ∈ (P.arc d).interior := by
      refine ⟨hv, ?_⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hne
    exact (P.interior_avoids_vertices d v hint).elim
  · rintro (h | h)
    · rw [← h]
      exact Or.inl (P.arc_start d).symm
    · have hs : P.pos (vert (flip d)) ∈ (P.arc (flip d)).image :=
        Or.inl (P.arc_start (flip d)).symm
      rw [P.arc_image_flip] at hs
      simpa [h] using hs

/-- Helper toward Proposition 5.16. For a finite PL drawing, a named vertex
lies on a face frontier exactly when it is an endpoint of some dart bordering
that face. This follows from the closed-arc frontier decomposition. -/
theorem mem_pos_frontier_iff_exists_dartBorders_endpoint [Finite D]
    (hvert : Function.Surjective vert) (F : P.Face) (v : V) :
    P.pos v ∈ frontier F.val ↔
      ∃ d, P.dartBorders d F ∧ (vert d = v ∨ vert (flip d) = v) := by
  rw [P.frontier_face_eq_iUnion_dartBorders_arcs hvert F]
  constructor
  · intro hv
    change P.pos v ∈ ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image at hv
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hborder, harc⟩ := Set.mem_iUnion.mp hd
    exact ⟨d, hborder, (P.mem_pos_arc_image_iff_endpoint d v).mp harc⟩
  · rintro ⟨d, hborder, hendpoint⟩
    change P.pos v ∈ ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image
    exact Set.mem_iUnion.mpr ⟨d,
      Set.mem_iUnion.mpr ⟨hborder,
        (P.mem_pos_arc_image_iff_endpoint d v).mpr hendpoint⟩⟩

end DirectedDistances.PlanarMap.PLDrawing

namespace DirectedDistances.PaperProofs.Section5






































end DirectedDistances.PaperProofs.Section5
