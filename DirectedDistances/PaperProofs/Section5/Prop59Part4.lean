/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59Part3
public import DirectedDistances.PaperProofs.Section5.Prop59Reduction

/-! This closes OPEN 3 in the exact canonical mirrored-pair context recorded in
`Prop59Part2`. The preceding file closes its retained-face obstruction;
the existing reduction packages the two proved restricted root-side
incidences into the complete geometric ball isomorphism.
OPEN 1 is used only as the displayed canonical representation data.
This does not assert existence of that data, equality of source laws, or -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. Full OPEN 3 holds for two PL
representations of the canonical mirrored code in the recorded context.
The two restricted root-side incidences are proved from the canonical
assembly, and retained ambient faces are identified by the signed PL
comparison. No face identification or geometric isomorphism is assumed. -/
theorem prop59_canonicalPair_geomBallIso
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (hA : D39GeomDomain
      (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos)
      (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin))
    (hmirrorDomain : D39GeomDomain
      (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos).geomMirror
      (d39GeomMirrorRoot (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin)))
    (canonical : D39DrawingRepresentationData3
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap)
      ⟨_, _, (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos).geomMirror,
        d39GeomMirrorRoot (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin),
        hmirrorDomain⟩)
    {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) B)
    (y : PLCylinderBall.Representation
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso
      (d39FacedBall ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) r hr)
      (d39FacedBall ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) r hr)) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) := by
  exact prop59_representedGeomBallIso_of_rootSide_mem x y r hr I
    (prop59_mirroredRepresentation_rootSide_mem_external
      W H h0 hL hR hfin hRpos hA hmirrorDomain canonical x r hr)
    (prop59_mirroredRepresentation_rootSide_mem_external
      W H h0 hL hR hfin hRpos hA hmirrorDomain canonical y r hr)

end DirectedDistances.PaperProofs.Section5

end
