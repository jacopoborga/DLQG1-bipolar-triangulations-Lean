/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLeftmostNonCrossing

/-! # Leftmost non-crossing for adjacent geodesic slices -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}



theorem m0GeodesicSideEdges_of_path_avoiding_vertices {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {x : ℕ} (Q : InfinitePresentPath (shiftedStream W 0) ⟨x⟩)
    (s : ThinMapSide)
    (hstart : x ∈ m0GeodesicSideVertices hp P s)
    (havoid : ∀ n, (Q.initial n).1.id ∉ m0GeodesicVertices P) :
    ∀ n, Q.edge n ∈ m0GeodesicSideEdges hp P s := by
  cases s with
  | left =>
    have hv : ∀ n, (Q.initial n).1.id ∈ m0GeodesicSideVertices hp P .left := by
      intro n
      induction n with
      | zero =>
        have hzero : (Q.initial 0).1.id = x := by
          have hz := (Q.initial 0).2.eq_of_length_zero (Q.prefix_length 0)
          exact congrArg PresentVertex.id hz.symm
        simpa [hzero] using hstart
      | succ n ih =>
        rcases m0GeodesicSideEdges_cover hp P (Q.edge n) with he | he
        · have hend := (m0GeodesicSide_endpoints hp P .left (Q.edge n) he).2
          change edgeEast (shiftedStream W 0) (Q.edge n) ∈
            m0GeodesicSideVertices hp P .left at hend
          rw [(Q.edge_incoming_at_succ (shiftedStream W 0) n).2] at hend
          exact hend
        · have hwest := (m0GeodesicSide_endpoints hp P .right (Q.edge n) he).1
          change edgeWest (shiftedStream W 0) (Q.edge n) ∈
            m0GeodesicSideVertices hp P .right at hwest
          rw [(Q.edge_outgoing_at_initial (shiftedStream W 0) n).2] at hwest
          have hboth : (Q.initial n).1.id ∈
              m0GeodesicSideVertices hp P .left ∩
                m0GeodesicSideVertices hp P .right := ⟨ih, hwest⟩
          have hpv : (Q.initial n).1.id ∈ m0GeodesicVertices P := by
            rw [← m0GeodesicSideVertices_inter hp P]
            exact hboth
          exact False.elim (havoid n hpv)
    intro n
    rcases m0GeodesicSideEdges_cover hp P (Q.edge n) with he | he
    · exact he
    · have hwest := (m0GeodesicSide_endpoints hp P .right (Q.edge n) he).1
      change edgeWest (shiftedStream W 0) (Q.edge n) ∈
        m0GeodesicSideVertices hp P .right at hwest
      rw [(Q.edge_outgoing_at_initial (shiftedStream W 0) n).2] at hwest
      have hboth : (Q.initial n).1.id ∈
          m0GeodesicSideVertices hp P .left ∩ m0GeodesicSideVertices hp P .right :=
        ⟨hv n, hwest⟩
      have hpv : (Q.initial n).1.id ∈ m0GeodesicVertices P := by
        rw [← m0GeodesicSideVertices_inter hp P]
        exact hboth
      exact False.elim (havoid n hpv)
  | right =>
    have hv : ∀ n, (Q.initial n).1.id ∈ m0GeodesicSideVertices hp P .right := by
      intro n
      induction n with
      | zero =>
        have hzero : (Q.initial 0).1.id = x := by
          have hz := (Q.initial 0).2.eq_of_length_zero (Q.prefix_length 0)
          exact congrArg PresentVertex.id hz.symm
        simpa [hzero] using hstart
      | succ n ih =>
        rcases m0GeodesicSideEdges_cover hp P (Q.edge n) with he | he
        · have hwest := (m0GeodesicSide_endpoints hp P .left (Q.edge n) he).1
          change edgeWest (shiftedStream W 0) (Q.edge n) ∈
            m0GeodesicSideVertices hp P .left at hwest
          rw [(Q.edge_outgoing_at_initial (shiftedStream W 0) n).2] at hwest
          have hboth : (Q.initial n).1.id ∈
              m0GeodesicSideVertices hp P .left ∩
                m0GeodesicSideVertices hp P .right := ⟨hwest, ih⟩
          have hpv : (Q.initial n).1.id ∈ m0GeodesicVertices P := by
            rw [← m0GeodesicSideVertices_inter hp P]
            exact hboth
          exact False.elim (havoid n hpv)
        · have hend := (m0GeodesicSide_endpoints hp P .right (Q.edge n) he).2
          change edgeEast (shiftedStream W 0) (Q.edge n) ∈
            m0GeodesicSideVertices hp P .right at hend
          rw [(Q.edge_incoming_at_succ (shiftedStream W 0) n).2] at hend
          exact hend
    intro n
    rcases m0GeodesicSideEdges_cover hp P (Q.edge n) with he | he
    · have hwest := (m0GeodesicSide_endpoints hp P .left (Q.edge n) he).1
      change edgeWest (shiftedStream W 0) (Q.edge n) ∈
        m0GeodesicSideVertices hp P .left at hwest
      rw [(Q.edge_outgoing_at_initial (shiftedStream W 0) n).2] at hwest
      have hboth : (Q.initial n).1.id ∈
          m0GeodesicSideVertices hp P .left ∩ m0GeodesicSideVertices hp P .right :=
        ⟨hwest, hv n⟩
      have hpv : (Q.initial n).1.id ∈ m0GeodesicVertices P := by
        rw [← m0GeodesicSideVertices_inter hp P]
        exact hboth
      exact False.elim (havoid n hpv)
    · exact he



theorem m0Cut_previous_boundary_mem_left_side {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    boundaryVertex (shiftedStream W 0) h (k - 1) ∈
      m0GeodesicSideVertices hp P .left := by
  change (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
    (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h (k - 1))) ∈
      m0GeodesicSideRegion hp P .left
  rw [← (m0CutData W H h hLL).x_eq h hLL (k - 1)]
  change _ ∈ closure (m0GeodesicLeftOpen hp P) ∩ m0GeodesicAmbientRegion W H h
  exact ⟨subset_closure (m0Geodesic_previous_pos_mem_leftOpen hp P),
    (m0Geodesic_previous_pos_mem_complement hp P).1⟩






















end DirectedDistances.PaperProofs.Section5
