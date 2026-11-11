/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat
public import DirectedDistances.PaperProofs.Section5.Prop516ReverseComparison2
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorTransportSettle2

/- Helpers toward Proposition 5.9 (prop-uihbot-sym). This file records the
same-code combinatorial ball comparison. The imported represented plane
comparison theorem is kernel-checked with standard axioms
2026-11-07T17:03:35Z). Its conclusion transports restricted orbit faces
only; the remaining obstruction is the exterior-transport input and the
retained ambient-face identification. This file does not assert the missing
canonical mirror representation or the resulting geometric ball comparison. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. Two v3 representations of the same
rooted map have isomorphic positive-radius combinatorial faced balls. The
representation witnesses are retained in the binders to make the common
represented map explicit; the faced-ball isomorphism follows from identity
of that map. -/
theorem prop59_same_represented_map_combinatorial_ballIso
    {M : D39RootedMap} {A' B : D39DomainRootedMapV2}
    (_hA' : D39DrawingRepresents3 M A')
    (_hB : D39DrawingRepresents3 M B)
    (r : ℕ) (hr : 0 < r) :
    Nonempty (D39BallIso (d39FacedBall M r hr) (d39FacedBall M r hr)) := by
  exact (d39BallClass_eq_iff M M r hr).mp rfl

/- OPEN canonical mirror-representation target, with the full binders used by
Prop59CanonicalMirrorCompat.lean:

For every W : ℤ → Fin 3, H : WholePlaneRotationHypothesis W,
h0 : BoundaryHitWitnesses (shiftedStream W 0),
hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a,
hR : ∀ n, 0 ≤ R (kmswPastCode W) n,
hfin : KMSWFiniteIncidence (kmswPastCode W), and
hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n, let
A := uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos and
rho := uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin. Given
hA : D39GeomDomain A rho, prove

∃ hmirrorDomain : D39GeomDomain A.geomMirror (d39GeomMirrorRoot rho),
  D39DrawingRepresents3
    ((mirrorRootedLocallyFinitePlanarMap
      (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap)
    ⟨A.V, A.E, A.geomMirror, d39GeomMirrorRoot rho, hmirrorDomain⟩.

This is the precise canonical-representation obligation: it includes the
mirrored domain, missing-root validity, edge/dart identity, reversed ordered
root, and the v3 topological rotation and frontier fields. Once a B and a
v3 representation of the same mirrored code are available, the preceding
combinatorial helper gives the faced-ball isomorphism. The existing
prop59_geomMirror_self_ballIso_of_representation is an identity case where
the second drawing is already the geometric mirror; it does not prove this
representation statement.

OPEN full geometric-ball target, with the original binders:

For the same W, H, h0, hL, hR, hfin, hRpos, A, and rho,
given hA : D39GeomDomain A rho, B : D39DomainRootedMap, and
hrep : D39DrawingRepresents3
  ((mirrorRootedLocallyFinitePlanarMap
    (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap)
  ⟨B.V, B.E, B.map, B.root, B.domain⟩, prove for each r : ℕ with 0 < r:

Nonempty (D39GeomBallIsoV2 r A.geomMirror (d39GeomMirrorRoot rho)
  B.map B.root).

The PL comparison also needs PLCylinderBall.Representation witnesses for
both drawings, which the stated v3 representation premise does not itself
contain. The exact represented plane-comparison statement used for the second
step is:

For M N : D39RootedMap, A' B : D39DomainRootedMapV2, representations
x : PLCylinderBall.Representation M A' and
y : PLCylinderBall.Representation N B, r : ℕ, hr : 0 < r,
I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr), and the single
input

hexterior_transport :
  plBallFaceOrbitMap I
      (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
    (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit,

the conclusion is the full homeomorphism, dart-arc, vertex-position, and
restricted orbit-face tuple of
ReverseComparison2.exists_represented_plane_homeomorph_of_external_transport
2026-11-07T17:03:35Z confirms that it is kernel-checked with standard axioms
[propext, Classical.choice, Quot.sound]. Its restricted orbit-face
conclusion still requires the exterior-transport input and does not provide
retained ambient-face identification. The full geometric target additionally
needs the edge identity and directions, missing root, reversed ordered root,
rotation reversal, and retained faces required by
Prop59D39GeomMirrorCompat.lean:47-54.

Three routes were checked:

1. Apply the identity case and D39DrawingRepresents3.transportCombinatorial.
   The identity case requires an already mirrored drawing, while
   transportCombinatorial changes only the combinatorial code and keeps the
   drawing fixed; the imported chain has no v3 representation action relating
   code mirroring to geometric conjugation.
2. Apply the imported reverse plane comparison, either with
   hexterior_transport or equality of representedExteriorMarkedBallClass.
   with standard axioms [propext, Classical.choice, Quot.sound]. Its
   conclusion transports restricted orbit faces only; use here still needs
   the exterior-transport input and retained ambient-face identification.
3. Use D39GeomMirror2 and its enclosing-radius restriction. It transports
   an existing D39GeomBallIsoV2 from radius r + 1 to the mirrored radius r;
   it cannot produce the initial isomorphism or its face correspondence.

Exterior transport is not proved automatic for the infinite canonical
half-plane maps. The finite fully represented digon counterexample in
Prop516ExteriorTransportSettle2.lean disproves automatic transport on the
whole representation carrier, but makes no claim about an infinite-only
subspace. The exact canonical infinite-map obligation, once the PL
representations and combinatorial isomorphism are constructed, is:

plBallFaceOrbitMap I
    (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
  (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit,

for the canonical mirrored-code map M, canonical mirrored assembly map N,
their PLCylinderBall.Representation witnesses x and y, every positive
radius r, and the resulting
I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr). This remains
geometric isomorphism is assumed here. -/

end DirectedDistances.PaperProofs.Section5

end

