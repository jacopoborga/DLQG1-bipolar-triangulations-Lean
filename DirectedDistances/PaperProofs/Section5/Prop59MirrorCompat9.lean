/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat7
public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat8
public import DirectedDistances.PaperProofs.Section5.Prop516ReverseComparison2







public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. Conditional on OPEN 2's exact exterior
orbit transport statement for these represented faced balls, the available
reverse comparison gives an orientation-preserving plane homeomorphism,
ordered dart-arc transport, vertex-position transport, and transport of the
restricted orbit faces. -/
theorem prop59_representedPlaneHomeomorph_of_open2
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B)
    (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (hOpen2 :
      plBallFaceOrbitMap I
          (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
        (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ d : (d39FacedBall M r hr).D,
        H (B.map.toPlaneMapWithMissing.pos
          (x.data.vertexEquiv (d39VertexClass M d.1))) =
          C.map.toPlaneMapWithMissing.pos
            (y.data.vertexEquiv (d39VertexClass N (I.toEquiv d).1))) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, H (d39DrawingDartArc B x.data.toD39DrawingRepresentationData
              d.1 t) =
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
  exact ReverseComparison2.exists_represented_plane_homeomorph_of_external_transport
    x y r hr I hOpen2




























end DirectedDistances.PaperProofs.Section5

end
