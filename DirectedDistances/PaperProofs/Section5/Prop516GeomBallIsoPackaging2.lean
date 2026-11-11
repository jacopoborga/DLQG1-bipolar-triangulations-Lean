/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomBallIsoPackaging
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.PlanarMap.D39BallOrbitComponents10
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation

/-! # Packaging geometric ball isomorphisms without loops

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`,
these helpers do not assert the unrestricted targets in the preceding file. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

namespace D39GeomBallCorrespondenceV2

variable {r : ℕ} {B C : D39DomainRootedMapV2}

/-- Helper toward Proposition 5.16: with distinct target endpoints, the
stored flip bit is determined by whether the source endpoint maps to the
target endpoint. -/
theorem edgeFlip_eq_true_iff_src_map_eq_tgt
    (c : D39GeomBallCorrespondenceV2 r B C)
    (e : {e // e ∈ d39GeomBallEdges B.map B.root r})
    (hne : C.map.toPlaneMapWithMissing.src (c.edgeEquiv e).1 ≠
      C.map.toPlaneMapWithMissing.tgt (c.edgeEquiv e).1) :
    c.edgeFlip e = true ↔
      (c.vertexEquiv ⟨B.map.toPlaneMapWithMissing.src e.1, e.2.1⟩).1 =
        C.map.toPlaneMapWithMissing.tgt (c.edgeEquiv e).1 := by
  rw [c.src_map]
  cases c.edgeFlip e <;> simp only [Bool.false_eq_true, ite_false, ite_true, hne,
    eq_self]

/-- Helper toward Proposition 5.16: construct every geometric ball
isomorphism field from a discrete correspondence and the specified plane
homeomorphism, when neither ball contains a loop. -/
@[expose] def toGeomBallIsoOfNoLoops
    (c : D39GeomBallCorrespondenceV2 r B C)
    (hB : ∀ e : {e // e ∈ d39GeomBallEdges B.map B.root r},
      B.map.toPlaneMapWithMissing.src e.1 ≠ B.map.toPlaneMapWithMissing.tgt e.1)
    (hC : ∀ e : {e // e ∈ d39GeomBallEdges C.map C.root r},
      C.map.toPlaneMapWithMissing.src e.1 ≠ C.map.toPlaneMapWithMissing.tgt e.1)
    (H : ℂ ≃ₜ ℂ) (hH : OrientationPreserving H)
    (hpos : ∀ v, H (B.map.toPlaneMapWithMissing.pos v.1) =
      C.map.toPlaneMapWithMissing.pos (c.vertexEquiv v).1)
    (harc : ∀ e, H '' Set.range (B.map.toPlaneMapWithMissing.arc e.1) =
      Set.range (C.map.toPlaneMapWithMissing.arc (c.edgeEquiv e).1))
    (hface : ∀ F, H '' F.1 = (c.faceEquiv F).1) :
    D39GeomBallIsoV2 r B.map B.root C.map C.root := by
  have hp : ∀ e : {e // e ∈ d39GeomBallEdges B.map B.root r},
      ∃ φ : I ≃ₜ I,
        (c.edgeFlip e = false → StrictMono φ) ∧
        (c.edgeFlip e = true → StrictAnti φ) ∧
        ∀ t, H (B.map.toPlaneMapWithMissing.arc e.1 t) =
          C.map.toPlaneMapWithMissing.arc (c.edgeEquiv e).1 (φ t) := by
    intro e
    obtain ⟨h0, h1⟩ := c.arc_endpoints_map H hpos e
    exact exists_path_reparam_of_planeHomeomorph
      (B.map.toPlaneMapWithMissing.arc e.1)
      (C.map.toPlaneMapWithMissing.arc (c.edgeEquiv e).1)
      (planeGraphDrawing_arc_injective_of_src_ne_tgt _ _ (hB e))
      (planeGraphDrawing_arc_injective_of_src_ne_tgt _ _ (hC (c.edgeEquiv e)))
      H (c.edgeFlip e) h0 h1 (harc e)
  exact {
    radius_pos := c.radius_pos
    h := H
    orientationPreserving := hH
    vertexEquiv := c.vertexEquiv
    edgeEquiv := c.edgeEquiv
    faceEquiv := c.faceEquiv
    edgeFlip := c.edgeFlip
    pos_map := hpos
    edgeParam := fun e => Classical.choose (hp e)
    edgeParam_mono := fun e => (Classical.choose_spec (hp e)).1
    edgeParam_anti := fun e => (Classical.choose_spec (hp e)).2.1
    arc_map := fun e => (Classical.choose_spec (hp e)).2.2
    src_map := c.src_map
    tgt_map := c.tgt_map
    missing_map := c.missing_map
    orientation_map := c.orientation_map
    root_edge_map := c.root_edge_map
    root_bool_map := c.root_bool_map
    face_image_map := hface }

end D39GeomBallCorrespondenceV2

/-- Helper toward Proposition 5.16: the full plane-homeomorphism packaging
target with the additional explicit hypothesis that both balls have no loops. -/
theorem d39GeomBallIsoV2_of_planeHomeomorph_of_noLoops
    (r : ℕ) (B C : D39DomainRootedMapV2)
    (c : D39GeomBallCorrespondenceV2 r B C)
    (hB : ∀ e : {e // e ∈ d39GeomBallEdges B.map B.root r},
      B.map.toPlaneMapWithMissing.src e.1 ≠ B.map.toPlaneMapWithMissing.tgt e.1)
    (hC : ∀ e : {e // e ∈ d39GeomBallEdges C.map C.root r},
      C.map.toPlaneMapWithMissing.src e.1 ≠ C.map.toPlaneMapWithMissing.tgt e.1)
    (H : ℂ ≃ₜ ℂ) (hH : OrientationPreserving H)
    (hpos : ∀ v, H (B.map.toPlaneMapWithMissing.pos v.1) =
      C.map.toPlaneMapWithMissing.pos (c.vertexEquiv v).1)
    (harc : ∀ e, H '' Set.range (B.map.toPlaneMapWithMissing.arc e.1) =
      Set.range (C.map.toPlaneMapWithMissing.arc (c.edgeEquiv e).1))
    (hface : ∀ F, H '' F.1 = (c.faceEquiv F).1) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) :=
  ⟨c.toGeomBallIsoOfNoLoops hB hC H hH hpos harc hface⟩

end DirectedDistances.PaperProofs.Section5

namespace DirectedDistances.PlanarMap.PLDrawing

/-- Helper toward Proposition 5.16: passing a PL drawing to geometric edge
identities preserves its distinct endpoints, including on missing edges. -/
theorem toPlaneGraphDrawing_src_ne_tgt
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (e : P.GeometricEdge) :
    P.toPlaneGraphDrawing.src e ≠ P.toPlaneGraphDrawing.tgt e :=
  P.vert_ne_flip e.out

/-- Helper toward Proposition 5.16: every directed plane map whose
underlying drawing is the canonical PL drawing has no loop edges. Missing
tags and present-edge orientations impose no further conditions. -/
theorem directedPlaneMap_src_ne_tgt
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (M : DirectedPlaneMapWithMissing V P.GeometricEdge)
    (hM : M.toPlaneMapWithMissing.toPlaneGraphDrawing = P.toPlaneGraphDrawing)
    (e : P.GeometricEdge) :
    M.toPlaneMapWithMissing.src e ≠ M.toPlaneMapWithMissing.tgt e := by
  rw [hM]
  exact P.toPlaneGraphDrawing_src_ne_tgt e

end DirectedDistances.PlanarMap.PLDrawing

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open scoped Topology

universe u

/-- Helper toward Proposition 5.16: the canonical directed map built from
a PL drawing has no loop edges, regardless of missing tags or directions. -/
theorem finitePLDrawingDirectedMap_src_ne_tgt
    {D V : Type u} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (missing : P.GeometricEdge → Prop)
    (forward : {e : P.GeometricEdge // ¬ missing e} → Bool)
    (hmissingExternal : ∀ e, missing e →
      ∃ F : P.toPlaneGraphDrawing.Face,
        PlaneGraphDrawing.IsExternal P.toPlaneGraphDrawing F ∧
          Set.range (P.toPlaneGraphDrawing.arc e) ⊆ closure F.val)
    (e : P.GeometricEdge) :
    (finitePLDrawingDirectedMap P missing forward hmissingExternal).toPlaneMapWithMissing.src e ≠
      (finitePLDrawingDirectedMap P missing forward hmissingExternal).toPlaneMapWithMissing.tgt e :=
  P.toPlaneGraphDrawing_src_ne_tgt e

/-- Helper toward Proposition 5.16: packaging a finite PL drawing in the
canonical rooted local topology domain preserves distinct endpoints for every edge,
so in particular every radius ball satisfies the no-loop packaging hypothesis. -/
theorem finitePLDrawingD39DomainRootedMapV2_src_ne_tgt
    {D V : Type u} [Finite D]
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (missing : P.GeometricEdge → Prop)
    (forward : {e : P.GeometricEdge // ¬ missing e} → Bool)
    (hmissingExternal : ∀ e, missing e →
      ∃ F : P.toPlaneGraphDrawing.Face,
        PlaneGraphDrawing.IsExternal P.toPlaneGraphDrawing F ∧
          Set.range (P.toPlaneGraphDrawing.arc e) ⊆ closure F.val)
    (root : P.GeometricEdge × Bool)
    (hconn : ∀ v w : V,
      (d39GeomGraph (finitePLDrawingDirectedMap P missing forward
        hmissingExternal)).Reachable v w)
    (hroot : (finitePLDrawingDirectedMap P missing forward hmissingExternal).toPlaneMapWithMissing.missing root.1 ∨
      ∃ h : ¬ (finitePLDrawingDirectedMap P missing forward hmissingExternal).toPlaneMapWithMissing.missing root.1,
        (finitePLDrawingDirectedMap P missing forward hmissingExternal).forward
          ⟨root.1, h⟩ = root.2)
    (e : P.GeometricEdge) :
    (finitePLDrawingD39DomainRootedMapV2 P missing forward hmissingExternal
      root hconn hroot).map.toPlaneMapWithMissing.src e ≠
    (finitePLDrawingD39DomainRootedMapV2 P missing forward hmissingExternal
      root hconn hroot).map.toPlaneMapWithMissing.tgt e :=
  finitePLDrawingDirectedMap_src_ne_tgt P missing forward hmissingExternal e

end DirectedDistances.PaperProofs.Section5

end
