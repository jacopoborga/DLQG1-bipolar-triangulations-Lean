/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ReverseComparisonFromDU1
public import DirectedDistances.PaperProofs.Section5.Prop516PLFrameInsertion5

/-! # Discharging DU1 in the represented plane comparison

DU1 construction is now supplied by `exists_sum_fin_augmented_drawings`.
The plane comparison below retains the existing common-exterior condition.
Restricted orbit-face transport does not yet identify retained ambient faces;
the precise geometric comparison obligations are recorded at the end. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5.ReverseComparison2

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

universe u

/-- Helper toward Proposition 5.16: FrameInsertion5 supplies the complete
DU1 proposition, including every retained datum and both joint closed-face
decompositions. This is a proof of the existing proposition, not an input. -/
theorem drawing_uniqueness_du1 : D39PLDrawingUniquenessDU1.{u} := by
  exact @D39FiniteBall.exists_sum_fin_augmented_drawings

/-- Helper toward Proposition 5.16: discharge the exact displayed `hDU1`
of the predecessor's plane theorem using FrameInsertion5, preserving all
open and closed restricted orbit faces and every original dart image. -/
theorem exists_plane_homeomorph
    {V : Type} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : V, H (P.pos x) = P'.pos x) ∧
      (∀ d, H '' (P.arc d).image = (P'.arc d).image) ∧
      (H '' P.image = P'.image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val) := by
  exact ReverseComparisonFromDU1.exists_plane_homeomorph_of_du1
    drawing_uniqueness_du1 B vert P P' hvert hconn O_ext hext

/-- Helper toward Proposition 5.16: discharge DU1 also for the ordered
dart comparison, with strictly increasing interval homeomorphisms. -/
theorem exists_plDrawing_homeomorph
    {V : Type} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : V, H (P.pos x) = P'.pos x) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, H ((P.arc d).toPath t) = (P'.arc d).toPath (φ t)) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val) := by
  exact ReverseComparisonFromDU1.exists_plDrawing_homeomorph_of_du1
    drawing_uniqueness_du1 B vert P P' hvert hconn O_ext hext

/-- Helper toward Proposition 5.16: the represented plane comparison
with DU1 proved. The single remaining input to this plane comparison is
the explicitly named transport of the selected exterior.
The conclusion concerns restricted orbit faces, not retained ambient faces. -/
theorem exists_represented_plane_homeomorph_of_external_transport
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (hexterior_transport :
      plBallFaceOrbitMap I
          (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
        (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ d : (d39FacedBall M r hr).D,
        H (B.map.toPlaneMapWithMissing.pos (x.data.vertexEquiv (d39VertexClass M d.1))) =
          C.map.toPlaneMapWithMissing.pos
            (y.data.vertexEquiv (d39VertexClass N (I.toEquiv d).1))) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, H (d39DrawingDartArc B x.data.toD39DrawingRepresentationData d.1 t) =
            d39DrawingDartArc C y.data.toD39DrawingRepresentationData
              (I.toEquiv d).1 (φ t)) ∧
      (∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
        H '' ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val =
          ((d39FacedBall N r hr).plOrbitFace
            (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
            (d39FacedBallPLDrawing N y.drawing r hr)
            (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
            (plBallFaceOrbitMap I O)).val) := by
  exact ReverseComparisonFromDU1.exists_represented_plane_homeomorph_of_common_unbounded_incidence
    drawing_uniqueness_du1 x y r hr I
    ((d39PLRepresentation_external_transport_iff_exists_unbounded_dart x y r hr I).mp
      hexterior_transport)

























































































































end DirectedDistances.PaperProofs.Section5.ReverseComparison2

end
