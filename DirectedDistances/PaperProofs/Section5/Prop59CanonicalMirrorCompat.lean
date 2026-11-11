/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalFaceCorrespondence








public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. The valid geometric drawing-representation
condition is the existing v3 predicate, retaining its represented dart and
vertex data, topological cyclic order, and face-frontier incidence clauses. -/
abbrev prop59ValidGeometricDrawingRepresentation
    (M : D39RootedMap) (B : D39DomainRootedMapV2) : Prop :=
  D39DrawingRepresents3 M B

/-- Helper toward Proposition 5.9. If a represented target drawing is exactly
the geometric mirror of a rooted drawing, then the reflected drawing agrees
with itself at every positive finite radius. This is the identity case only;
it does not identify the reflected canonical assembly with an arbitrary
drawing of the mirrored code. -/
theorem prop59_geomMirror_self_ballIso_of_representation
    (A : D39DomainRootedMap.{0})
    (Bmap : DirectedPlaneMapWithMissing A.V A.E)
    (Broot : A.E × Bool)
    (hBdomain : D39GeomDomain Bmap Broot)
    (M : D39RootedMap)
    (hrep : prop59ValidGeometricDrawingRepresentation M
      ⟨A.V, A.E, Bmap, Broot, hBdomain⟩)
    (hBmap : Bmap = A.map.geomMirror)
    (hBroot : Broot = d39GeomMirrorRoot A.root)
    (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 r A.map.geomMirror
      (d39GeomMirrorRoot A.root) Bmap Broot) := by
  cases hBmap
  cases hBroot
  exact ⟨DirectedDistances.PaperProofs.Section3.refl hr⟩

/- The exact remaining finite-radius statement is the following. For every
`W : ℤ → Fin 3`, `H : WholePlaneRotationHypothesis W`,
`h0 : BoundaryHitWitnesses (shiftedStream W 0)`,
`hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a`,
`hR : ∀ n, 0 ≤ R (kmswPastCode W) n`,
`hfin : KMSWFiniteIncidence (kmswPastCode W)`, and
`hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n`, let
`A := uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos` and
`rho := uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin`. Given
`hA : D39GeomDomain A rho`, `B : D39DomainRootedMap`, and
`hrep : prop59ValidGeometricDrawingRepresentation
  ((mirrorRootedLocallyFinitePlanarMap (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap)
  ⟨B.V, B.E, B.map, B.root, B.domain⟩`, prove for every `r : ℕ` with
`0 < r`:

`Nonempty (D39GeomBallIsoV2 r A.geomMirror (d39GeomMirrorRoot rho)
  B.map B.root)`.

Three routes were checked in the imported helper chain:

1. Direct geometric conjugation supplies the mirror and its ordered-root
   behavior, but it does not identify a drawing of the mirrored code with the
   reflected canonical assembly.
2. Code-level mirror invariance and finite-window comparison give
   combinatorial/class information, not a pathwise geometric ball
   isomorphism between these two drawings.
3. Enclosing-radius transport restricts an already supplied geometric ball
   isomorphism from radius `r + 1` to `r`; it cannot produce the missing
   initial comparison or the required retained-face correspondence.

The canonical assembly face correspondence is proved by the imported helper,
but no result here matches it to an arbitrary `hrep` for the mirrored code.
No isomorphism, face correspondence, or target-equivalent premise is assumed. -/

end DirectedDistances.PaperProofs.Section5

end
