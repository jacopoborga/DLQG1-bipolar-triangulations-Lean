/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat2





public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. For the canonical assembly and its ordered
root, the mirrored geometric domain exists exactly when the canonical root
edge has the missing tag. This isolates the root-validity obligation in the
mirrored-representation target. -/
theorem prop59_canonicalAssembly_geomMirrorDomain_iff_missing
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (hA : D39GeomDomain
      (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos)
      (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin)) :
    D39GeomDomain
        (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos).geomMirror
        (d39GeomMirrorRoot
          (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin)) ↔
      (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos).toPlaneMapWithMissing.missing
        (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin).1 := by
  exact D39GeomDomain.geomMirror_iff_missing hA

/- OPEN 1: canonical v3 representation of the mirrored code. For every
`W : ℤ → Fin 3`, `H : WholePlaneRotationHypothesis W`,
`h0 : BoundaryHitWitnesses (shiftedStream W 0)`,
`hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a`,
`hR : ∀ n, 0 ≤ R (kmswPastCode W) n`,
`hfin : KMSWFiniteIncidence (kmswPastCode W)`, and
`hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n`, define
`A := uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos` and
`rho := uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin`. Given
`hA : D39GeomDomain A rho`, prove

`∃ hmirrorDomain : D39GeomDomain A.geomMirror (d39GeomMirrorRoot rho),
  D39DrawingRepresents3
    ((mirrorRootedLocallyFinitePlanarMap
      (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap)
    ⟨A.V, A.E, A.geomMirror, d39GeomMirrorRoot rho, hmirrorDomain⟩`.

Three routes tried:

1. Apply `D39GeomDomain.geomMirror`. Its exact extra obligation is
   `A.toPlaneMapWithMissing.missing rho.1`, equivalently the result of the
   helper above. `hA.rootValid` is a disjunction allowing a present root with
   its matching orientation; the available `UIBHBOTCertifiedRootCapture.root_missing_wholePlane`
   requires a certified-capture witness not among these binders.
2. Transport the existing v3 representation of the unmirrored code with
   `D39DrawingRepresents3.transportCombinatorial`. This requires a
   `D39RootedMapIso` from the mirrored code to that code. The imported
   Proposition 5.9 class symmetry is a law-level statement and supplies no
   such pathwise rooted-map isomorphism for the fixed `W`.
3. Geometrically reflect the existing representation data. The available
   `D39GeomMirror` APIs transport geometric ball isomorphisms and face data
   after a correspondence exists; `D39DrawingRepresentationData3` has no
   proved reflection action identifying the reflected drawing's edge, root,
   rotation, and face data with the mirrored code.

OPEN 2: exterior input for represented canonical infinite maps. The full
general statement needed after OPEN 1 is: for `M N : D39RootedMap`,
`B C : D39DomainRootedMapV2`,
`x : PLCylinderBall.Representation M B`,
`y : PLCylinderBall.Representation N C`, `r : ℕ`, `hr : 0 < r`, and
`I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)`, prove

`plBallFaceOrbitMap I
    (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
  (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit`

when `M`, `N`, `x`, and `y` are the specific canonical mirrored-code and
canonical assembly representations in OPEN 1, with no exterior-transport
premise. Three routes tried:

1. Use `prop59D39CanonicalAssembly_planeFaceCorrespondence` and its
   unbounded marked outer face. This identifies the ambient complementary
   component, but no proved lemma here identifies that component with the
   selected orbit after restricting the PL drawing to the finite ball and
   locating its missing-root side in that restricted orbit.
2. Use that `I` preserves the root and missing tags. Those fields identify
   the marked boundary dart under `I`; they do not show that the dart belongs
   to either drawing's selected unbounded orbit. The external-orbit selector
   is defined by unboundedness of the restricted orbit face.
3. Apply uniqueness of the unbounded restricted orbit. To use uniqueness one
   must first prove the root-side orbit unbounded in both restricted drawings;
   this is the missing restriction/ambient-face comparison above. The finite
   digon result disproves this implication for arbitrary finite
   representations, and supplies no infinite-canonical proof.

OPEN 3: full geometric compatibility without an exterior input. For the same
`M`, `N`, `B`, `C`, `x`, `y`, `r`, `hr`, and faced-ball isomorphism `I` as in
OPEN 2, prove

`Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root)`

for the canonical infinite mirrored-code and assembly representations with
no exterior-transport premise. The exact currently available reverse
comparison requires that premise and only returns restricted orbit-face
transport; the finite digon counterexample does not resolve this
infinite-canonical statement. No isomorphism, face correspondence, or
target-equivalent premise is assumed here. -/

end DirectedDistances.PaperProofs.Section5

end
