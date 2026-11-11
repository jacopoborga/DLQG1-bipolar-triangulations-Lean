module

public import DirectedDistances.PlanarMap.D39DrawingRepresentation3
public import DirectedDistances.PlanarMap.D39FacedBallClass
public import DirectedDistances.PaperProofs.SourceResults.D39GeometricSourceProviderV2

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16. A geometric ball isomorphism sends the
vertex represented by the first rooted dart to the vertex represented by the
second rooted dart. -/
theorem d39GeomBallIsoV2_representation_root_vertex
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (r : ℕ)
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    (e.vertexEquiv
      ⟨x.vertexEquiv (d39VertexClass M M.rootMark.dart), by
        have hxroot :
            x.vertexEquiv (d39VertexClass M M.rootMark.dart) =
              d39GeomRootVertex B.map B.root := by
          change x.vertexEquiv
              (rootedLocallyFiniteVertexClass M.core.rot M.rootMark.dart) = _
          rw [x.dart_tail_vertex, x.root_mark]
          rfl
        rw [hxroot]
        simp [d39GeomBallVertices, d39GeomGraphDistance]⟩).1 =
      y.vertexEquiv (d39VertexClass N N.rootMark.dart) := by
  have hxroot :
      x.vertexEquiv (d39VertexClass M M.rootMark.dart) =
        d39GeomRootVertex B.map B.root := by
    change x.vertexEquiv
        (rootedLocallyFiniteVertexClass M.core.rot M.rootMark.dart) = _
    rw [x.dart_tail_vertex, x.root_mark]
    rfl
  have hyroot :
      y.vertexEquiv (d39VertexClass N N.rootMark.dart) =
        d39GeomRootVertex C.map C.root := by
    change y.vertexEquiv
        (rootedLocallyFiniteVertexClass N.core.rot N.rootMark.dart) = _
    rw [y.dart_tail_vertex, y.root_mark]
    rfl
  have hrootB : d39GeomRootVertex B.map B.root ∈
      d39GeomBallVertices B.map B.root r := by
    simp [d39GeomBallVertices, d39GeomGraphDistance]
  have hrootC : d39GeomRootVertex C.map C.root ∈
      d39GeomBallVertices C.map C.root r := by
    simp [d39GeomBallVertices, d39GeomGraphDistance]
  have hmem :
      (⟨x.vertexEquiv (d39VertexClass M M.rootMark.dart), by
        rw [hxroot]
        exact hrootB⟩ :
          {v // v ∈ d39GeomBallVertices B.map B.root r}) =
      ⟨d39GeomRootVertex B.map B.root, hrootB⟩ := by
    exact Subtype.ext hxroot
  calc
    (e.vertexEquiv
      ⟨x.vertexEquiv (d39VertexClass M M.rootMark.dart), by
        rw [hxroot]
        exact hrootB⟩).1 =
        (e.vertexEquiv ⟨d39GeomRootVertex B.map B.root, hrootB⟩).1 :=
          congrArg (fun v => (e.vertexEquiv v).1) hmem
    _ = d39GeomRootVertex C.map C.root := e.root_initial_map
    _ = y.vertexEquiv (d39VertexClass N N.rootMark.dart) := hyroot.symm


































end DirectedDistances.PaperProofs.Section5

end
