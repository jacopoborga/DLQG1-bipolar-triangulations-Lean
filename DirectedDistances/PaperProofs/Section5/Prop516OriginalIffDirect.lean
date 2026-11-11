/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly4
public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly3
public import DirectedDistances.PaperProofs.Section5.Prop516HballForward








public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open scoped Topology

/-- Helper toward Proposition 5.16: a ball dart is original exactly when
every dart in its ambient face orbit belongs to the ball. -/
theorem d39FacedBall_original_iff_faceOrbit_subset_ballDarts
    (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D) :
    d ∈ (d39FacedBall M r hr).original ↔
      ∀ q, Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d.1 q →
        q ∈ d39BallDarts M r := by
  rfl

/-- Helper toward Proposition 5.16: the original-face predicate is exactly
retention of the represented geometric face. The imported retention theorem
uses the representation's vertex-frontier incidence in both directions. -/
theorem d39DrawingRepresentationData3_original_iff_face_retained
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D) :
    d ∈ (d39FacedBall M r hr).original ↔
      x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r := by
  change d39BallContainsOriginalFace M r d.1 ↔ _
  exact (d39BallContainsOriginalFace_iff M r d.1).trans
    (d39DrawingRepresentationData3_retainedFace_iff_ballOrbitVertices x r d.1).symm



theorem d39DrawingRepresentationData3_original_iff_face_darts_retained
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D) :
    d ∈ (d39FacedBall M r hr).original ↔
      ∀ q, x.faceOfDart d.1 = x.faceOfDart q → q ∈ d39BallDarts M r := by
  rw [d39FacedBall_original_iff_faceOrbit_subset_ballDarts]
  constructor
  · intro h q hq
    exact h q ((x.faceOrbit_iff d.1 q).mp hq)
  · intro h q hq
    exact h q ((x.faceOrbit_iff d.1 q).mpr hq)

/-- Helper toward Proposition 5.16: the geometric face equivalence carries
the entire frontier of each retained face to the frontier of its retained
image face. No uniqueness of winding-side incidence is used. -/
theorem d39GeomBallIsoV2_faceEquiv_frontier_image
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (F : {F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces B.map B.root r}) :
    e.h '' frontier F.1.val = frontier (e.faceEquiv F).1.val := by
  rw [e.h.image_frontier, e.face_image_map F]

/-- Helper toward Proposition 5.16: incidence of a retained vertex with a
retained face frontier is preserved directly by the geometric isomorphism. -/
theorem d39GeomBallIsoV2_faceEquiv_vertex_frontier_iff
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (F : {F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces B.map B.root r})
    (v : {v : B.V // v ∈ d39GeomBallVertices B.map B.root r}) :
    B.map.toPlaneMapWithMissing.pos v.1 ∈ frontier F.1.val ↔
      C.map.toPlaneMapWithMissing.pos (e.vertexEquiv v).1 ∈
        frontier (e.faceEquiv F).1.val := by
  rw [← e.pos_map v, ← d39GeomBallIsoV2_faceEquiv_frontier_image e F]
  constructor
  · intro hv
    exact ⟨_, hv, rfl⟩
  · rintro ⟨z, hz, hze⟩
    exact e.h.injective hze ▸ hz





theorem d39GeomBallIsoV2_faceEquiv_arc_frontier_iff
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (F : {F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces B.map B.root r})
    (a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r}) :
    Set.range (B.map.toPlaneMapWithMissing.arc a.1) ⊆ frontier F.1.val ↔
      Set.range (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) ⊆
        frontier (e.faceEquiv F).1.val := by
  rw [← e.arc_range_map a, ← d39GeomBallIsoV2_faceEquiv_frontier_image e F]
  constructor
  · intro h z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, h hw, rfl⟩
  · intro h z hz
    obtain ⟨w, hw, hwz⟩ := h ⟨z, hz, rfl⟩
    exact e.h.injective hwz ▸ hw

/-- Helper toward Proposition 5.16: the actual mapped dart, with its
increasing dart parameter, has a point on the image face frontier exactly
when the source point is on the source face frontier. This follows directly
from geometric face and dart compatibility, without a side-uniqueness step. -/
theorem d39DrawingRepresentationData3_geomBallIso_dart_frontier_iff
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (F : {F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces B.map B.root r})
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) (t : unitInterval) :
    let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
      ⟨(x.dartEquiv d.1).1,
        (d39DrawingRepresentationData3_ballDarts_iff x r d.1).mp d.2⟩
    d39DrawingDartArc B x.toD39DrawingRepresentationData d.1 t ∈
        frontier F.1.val ↔
      d39DrawingDartArc C y.toD39DrawingRepresentationData
          (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1
          (d39GeomBallIsoV2DartParam e a (x.dartEquiv d.1).2 t) ∈
        frontier (e.faceEquiv F).1.val := by
  dsimp only
  rw [← d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_arc_map x y e d t,
    ← d39GeomBallIsoV2_faceEquiv_frontier_image e F]
  constructor
  · intro ht
    exact ⟨_, ht, rfl⟩
  · rintro ⟨z, hz, hzt⟩
    exact e.h.injective hzt ▸ hz






















































































end DirectedDistances.PaperProofs.Section5

end
