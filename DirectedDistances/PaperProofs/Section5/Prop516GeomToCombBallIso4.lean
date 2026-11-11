module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso3

/-! # Retained faces and rotation for geometric-to-combinatorial balls

Helpers toward Proposition 5.16. This file records the face-orbit bridge
available from the drawing representation and the remaining rotation
compatibility obligation. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set

/-- Helper toward Proposition 5.16. A represented geometric face is
retained at radius `r` exactly when every dart in its combinatorial face orbit
has its incident vertex in the combinatorial vertex ball. Closure membership
of a represented vertex position is converted to frontier membership using
that vertex's inclusion in the drawing image and the face's disjointness from
the image. -/
theorem d39DrawingRepresentationData3_retainedFace_iff_ballOrbitVertices
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (r : ℕ) (d : M.core.D) :
    x.faceOfDart d ∈ d39GeomRetainedFaces B.map B.root r ↔
      ∀ e, Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e →
        d39VertexClass M e ∈ d39BallVertices M r := by
  apply (Iff.trans ?_ (d39BallContainsOriginalFace_iff M r d))
  rw [d39BallContainsOriginalFace_iff]
  constructor
  · intro h e he
    apply (d39DrawingRepresentationData3_ballVertices_iff x r
      (d39VertexClass M e)).mpr
    apply h
    exact frontier_subset_closure
      ((x.vertex_frontier_incidence d (d39VertexClass M e)).mpr
        ⟨e, he, rfl⟩)
  · intro h v hv
    obtain ⟨w, rfl⟩ := x.vertexEquiv.surjective v
    have hfront : B.map.toPlaneMapWithMissing.pos (x.vertexEquiv w) ∈
        frontier (x.faceOfDart d).val := by
      refine ⟨hv, ?_⟩
      intro hi
      exact B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.face_subset_compl_image
        (x.faceOfDart d) (interior_subset hi)
        (Or.inl ⟨x.vertexEquiv w, rfl⟩)
    obtain ⟨e, he, hew⟩ :=
      (x.vertex_frontier_incidence d w).mp hfront
    apply (d39DrawingRepresentationData3_ballVertices_iff x r w).mp
    rw [← hew]
    exact h e he















































































end DirectedDistances.PaperProofs.Section5

end
