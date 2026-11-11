/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry12

/-! The transported-drawing statements in this module are conditional on the
encoding condition that the marked combinatorial outer face of the finite
drawing is unbounded. This condition is not inferred from equality of drawing
images. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the specific transported drawing has the
same oriented dart polylines up to reversal, and each of its unbounded faces
determines an external face of the associated plane-map drawing. -/
theorem boundaryChanneled_transport_specific_arcs_and_external_faces
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
      DrawsMap (boundaryChanneledPlaneMap R G) H ∧
      (∀ q b, H.arc (q, b) = G.arc q.out ∨
        H.arc (q, b) = (G.arc q.out).reverse) ∧
      ∀ U : H.Face, H.IsUnbounded U →
        ∃ F : (Drawing (boundaryChanneledPlaneMap R G)).Face,
          F.val = U.val ∧ (Drawing (boundaryChanneledPlaneMap R G)).IsExternal F := by
  obtain ⟨rot, H, hDraws, hArcs⟩ :=
    boundaryChanneled_transport_oriented_arcs R G hOuterUnbounded
  refine ⟨rot, H, hDraws, hArcs, ?_⟩
  intro U hU
  obtain ⟨F, hF, hFext⟩ :=
    boundaryChanneled_drawsMap_externalFace R G rot H U hDraws hU
  exact ⟨F, hF, hFext⟩































































































































end DirectedDistances.PaperProofs.Section3

end
