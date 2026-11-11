/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents6

/-! # Winding sides of a simple orbit boundary

Helpers toward Proposition 5.16. These results identify the side occupied by
an actual geometric face and the extra condition needed to identify that face
with the entire winding side. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Topology

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)





theorem plOrbitFace_windingSide_of_cyclicSimple_boundary
    (hvert : Function.Surjective vert) (O : D39BallFaceCycleOrbit B)
    (q : Polyline) (hclosed : q.start = q.finish) (_hc : q.IsCyclicSimple)
    (hqBoundary : q.image ⊆ B.plOrbitBoundary vert P O) :
    Disjoint (B.plOrbitFace vert P hvert O).val q.image ∧
      IsConnected (B.plOrbitFace vert P hvert O).val ∧
      ((B.plOrbitFace vert P hvert O).val ⊆ q.inside ∨
        (B.plOrbitFace vert P hvert O).val ⊆ q.outside) ∧
      q.image ⊆ frontier (B.plOrbitFace vert P hvert O).val ∧
      q.image ⊆ P.image := by
  let F := B.plOrbitFace vert P hvert O
  have hfront : B.plOrbitBoundary vert P O ⊆ frontier F.val := by
    simpa only [F] using B.plOrbitBoundary_subset_frontier vert P hvert O
  have hqfront : q.image ⊆ frontier F.val := hqBoundary.trans hfront
  have hqdraw : q.image ⊆ P.image :=
    hqfront.trans (P.face_open_frontier_subset_image hvert F).2
  have hdis : Disjoint F.val q.image := by
    apply Set.disjoint_left.mpr
    intro z hzF hzq
    exact (P.face_subset_compl F hzF) (hqdraw hzq)
  have hconn : IsConnected F.val := (P.face_isPathConnected hvert F).isConnected
  obtain ⟨x, hxF⟩ := hconn.nonempty
  have hxnot : x ∉ q.image := by
    intro hxq
    exact (P.face_subset_compl F hxF) (hqdraw hxq)
  have hxside : x ∈ q.inside ∨ x ∈ q.outside := by
    have hxcompl : x ∈ q.imageᶜ := hxnot
    rw [← Polyline.inside_union_outside q] at hxcompl
    exact hxcompl
  have hside : F.val ⊆ q.inside ∨ F.val ⊆ q.outside := by
    rcases hxside with hxin | hxout
    · exact Or.inl (B.plFace_subset_inside_of_mem vert P q hclosed hqdraw F hxF hxin)
    · exact Or.inr (B.plFace_subset_outside_of_mem vert P q hclosed hqdraw F hxF hxout)
  exact ⟨hdis, hconn, hside, hqfront, hqdraw⟩





theorem plOrbitFace_initialSectors_on_windingSide
    (hvert : Function.Surjective vert) (O : D39BallFaceCycleOrbit B)
    (q : Polyline) (hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hboundaryEq : q.image = B.plOrbitBoundary vert P O) :
    (∀ d ∈ O.val, ∃ r : ℝ, 0 < r ∧
      P.initialSector d r ⊆ q.inside ∧
      P.initialSector d r ⊆ Metric.ball (P.pos (vert d)) r ∧
      P.pos (vert d) ∈ q.image) ∨
    (∀ d ∈ O.val, ∃ r : ℝ, 0 < r ∧
      P.initialSector d r ⊆ q.outside ∧
      P.initialSector d r ⊆ Metric.ball (P.pos (vert d)) r ∧
      P.pos (vert d) ∈ q.image) := by
  have hqBoundary : q.image ⊆ B.plOrbitBoundary vert P O := hboundaryEq.subset
  have hstarts : ∀ d ∈ O.val, (P.arc d).start ∈ q.image := by
    intro d hd
    rw [hboundaryEq]
    apply mem_iUnion₂.mpr
    refine ⟨d, hd, ?_⟩
    rw [← Polyline.range_toPath]
    exact ⟨0, (P.arc d).toPath.source⟩
  obtain ⟨_, _, hside, _, _⟩ :=
    B.plOrbitFace_windingSide_of_cyclicSimple_boundary vert P hvert O q hclosed hc hqBoundary
  rcases hside with hin | hout
  · left
    intro d hd
    obtain ⟨r, hr, hsub⟩ := P.exists_initialSector_subset_of_dartBorders hvert d
      (B.plOrbitFace vert P hvert O)
      ((B.plOrbitFace_eq_iff vert P hvert O d hd
        (B.plOrbitFace vert P hvert O)).mp rfl)
    refine ⟨r, hr, hsub.trans hin, P.initialSector_subset_ball d r, ?_⟩
    exact P.arc_start d ▸ hstarts d hd
  · right
    intro d hd
    obtain ⟨r, hr, hsub⟩ := P.exists_initialSector_subset_of_dartBorders hvert d
      (B.plOrbitFace vert P hvert O)
      ((B.plOrbitFace_eq_iff vert P hvert O d hd
        (B.plOrbitFace vert P hvert O)).mp rfl)
    refine ⟨r, hr, hsub.trans hout, P.initialSector_subset_ball d r, ?_⟩
    exact P.arc_start d ▸ hstarts d hd





theorem plOrbitFace_eq_inside_of_no_drawing_points
    (hvert : Function.Surjective vert) (O : D39BallFaceCycleOrbit B)
    (q : Polyline) (_hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hqBoundary : q.image ⊆ B.plOrbitBoundary vert P O)
    (hnoDrawing : q.inside ∩ P.image = ∅)
    (hside : (B.plOrbitFace vert P hvert O).val ⊆ q.inside) :
    (B.plOrbitFace vert P hvert O).val = q.inside ∧
      q.image ⊆ frontier (B.plOrbitFace vert P hvert O).val := by
  let F := B.plOrbitFace vert P hvert O
  have hfront : B.plOrbitBoundary vert P O ⊆ frontier F.val := by
    simpa only [F] using B.plOrbitBoundary_subset_frontier vert P hvert O
  have hqfront : q.image ⊆ frontier F.val := hqBoundary.trans hfront
  obtain ⟨x, hxF⟩ := (P.face_isPathConnected hvert F).isConnected.nonempty
  have hxin : x ∈ q.inside := hside hxF
  have hF : F.val = connectedComponentIn P.imageᶜ x := by
    obtain ⟨z, hz, hF⟩ := F.property
    exact hF.trans (connectedComponentIn_eq (hF ▸ hxF))
  have hinsideCompl : q.inside ⊆ P.imageᶜ := by
    intro z hz
    have hzNot : z ∉ P.image := by
      intro hzDraw
      have hzInter : z ∈ q.inside ∩ P.image := ⟨hz, hzDraw⟩
      rw [hnoDrawing] at hzInter
      exact hzInter
    exact hzNot
  have hinsideConn := (Polyline.isConnected_inside_outside_cyclic q hc).1
  have hinsideComp : q.inside ⊆ connectedComponentIn P.imageᶜ x :=
    hinsideConn.isPreconnected.subset_connectedComponentIn hxin hinsideCompl
  have hinsideF : q.inside ⊆ F.val := hF.symm ▸ hinsideComp
  exact ⟨Set.Subset.antisymm hside hinsideF, hqfront⟩

/-- Helper toward Proposition 5.16: the outside analogue of
`plOrbitFace_eq_inside_of_no_drawing_points`. -/
theorem plOrbitFace_eq_outside_of_no_drawing_points
    (hvert : Function.Surjective vert) (O : D39BallFaceCycleOrbit B)
    (q : Polyline) (_hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hqBoundary : q.image ⊆ B.plOrbitBoundary vert P O)
    (hnoDrawing : q.outside ∩ P.image = ∅)
    (hside : (B.plOrbitFace vert P hvert O).val ⊆ q.outside) :
    (B.plOrbitFace vert P hvert O).val = q.outside ∧
      q.image ⊆ frontier (B.plOrbitFace vert P hvert O).val := by
  let F := B.plOrbitFace vert P hvert O
  have hfront : B.plOrbitBoundary vert P O ⊆ frontier F.val := by
    simpa only [F] using B.plOrbitBoundary_subset_frontier vert P hvert O
  have hqfront : q.image ⊆ frontier F.val := hqBoundary.trans hfront
  obtain ⟨x, hxF⟩ := (P.face_isPathConnected hvert F).isConnected.nonempty
  have hxout : x ∈ q.outside := hside hxF
  have hF : F.val = connectedComponentIn P.imageᶜ x := by
    obtain ⟨z, hz, hF⟩ := F.property
    exact hF.trans (connectedComponentIn_eq (hF ▸ hxF))
  have houtsideCompl : q.outside ⊆ P.imageᶜ := by
    intro z hz
    have hzNot : z ∉ P.image := by
      intro hzDraw
      have hzInter : z ∈ q.outside ∩ P.image := ⟨hz, hzDraw⟩
      rw [hnoDrawing] at hzInter
      exact hzInter
    exact hzNot
  have houtsideConn := (Polyline.isConnected_inside_outside_cyclic q hc).2
  have houtsideComp : q.outside ⊆ connectedComponentIn P.imageᶜ x :=
    houtsideConn.isPreconnected.subset_connectedComponentIn hxout houtsideCompl
  have houtsideF : q.outside ⊆ F.val := hF.symm ▸ houtsideComp
  exact ⟨Set.Subset.antisymm hside houtsideF, hqfront⟩

end D39FiniteBall





























end DirectedDistances.PlanarMap

end
