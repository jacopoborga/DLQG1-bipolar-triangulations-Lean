/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRepresentation
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingFrontierIncidence

/-! # Stage drawing frontier incidence transfer

This file makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

/-- Helper toward Proposition 5.16. The represented geometric face-side
condition transfers from a dart to every dart in its combinatorial face
orbit, using the `faceOrbit_iff` and `face_left_of_dart` fields. -/
theorem d39DrawingDartFace_side_of_sameCycle
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (hbase : D39DrawingRepresentationData M B) (d e : M.core.D)
    (hcycle : Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e) :
    (if (hbase.dartEquiv e).2 then
      B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
        (hbase.faceOfDart d) (hbase.dartEquiv e).1
    else
      B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
        (hbase.faceOfDart d) (hbase.dartEquiv e).1) := by
  rw [(hbase.faceOrbit_iff d e).2 hcycle]
  exact hbase.face_left_of_dart e

/-- Helper toward Proposition 5.16. The represented dart arc starts at the
position of its combinatorial tail vertex, by the endpoint fields of the
local topology drawing representation. -/
theorem d39DrawingDartArc_start_eq_vertex_pos
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (hbase : D39DrawingRepresentationData M B) (d : M.core.D) :
    d39DrawingDartArc B hbase d 0 =
      B.map.toPlaneMapWithMissing.pos
        (hbase.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d)) := by
  cases hb : (hbase.dartEquiv d).2 <;>
    simp [d39DrawingDartArc, hb, hbase.dart_tail_vertex]

/-- Helper toward Proposition 5.16. The represented dart arc finishes at the
position of the combinatorial head vertex, by the endpoint fields of the
local topology drawing representation. -/
theorem d39DrawingDartArc_finish_eq_vertex_pos
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (hbase : D39DrawingRepresentationData M B) (d : M.core.D) :
    d39DrawingDartArc B hbase d 1 =
      B.map.toPlaneMapWithMissing.pos
        (hbase.vertexEquiv
          (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d))) := by
  cases hb : (hbase.dartEquiv d).2 <;>
    simp [d39DrawingDartArc, hb, hbase.dart_head_vertex]





























































end DirectedDistances.PaperProofs.Section5

end
