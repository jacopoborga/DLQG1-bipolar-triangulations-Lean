/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59MirrorRepPart1
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation14

/-! The almost-sure statement below has exactly the OPEN 1 binders recorded in
`Prop59Reduction.lean:192-206`; the comment's `A.V` and `A.E` denote
the vertex and edge type parameters, inferred below from `A`. The geometric
mirror domain comes from the
proved almost-sure absence of the canonical root; no pathwise isomorphism or
sole coordinator. This helper does not assert the paper's law identification. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. Almost surely the canonical mirrored-code
map has a v3 representation by the reflected canonical assembly, with the
same witnesses as OPEN 1. Root absence supplies the reflected domain on the
conull event, and every representation field is reflected by the generic
construction. -/
theorem prop59_mirrorRep_canonicalRepresentation_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n),
        let A := uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos
        let rho := uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin
        ∃ (hA : D39GeomDomain A rho)
          (hmirrorDomain : D39GeomDomain A.geomMirror (d39GeomMirrorRoot rho)),
          D39DrawingRepresents3
            ((mirrorRootedLocallyFinitePlanarMap
              (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap)
            ⟨_, _, A.geomMirror, d39GeomMirrorRoot rho, hmirrorDomain⟩ := by
  filter_upwards [uibhbotRootedPlanarMapConullEvent_spec.2.1,
    prop59_canonicalAssembly_geomMirrorDomain_ae] with W hW hdomain
  obtain ⟨H, h0, hL, hR, hfin, hRpos, hA, hmirrorDomain⟩ := hdomain
  refine ⟨H, h0, hL, hR, hfin, hRpos, hA, hmirrorDomain, ?_⟩
  let D : UIBHBOTD39CanonicalDomainWitness W :=
    ⟨H, h0, hL, hR, hfin, hRpos, hA⟩
  obtain ⟨x⟩ := uibhbotD39CanonicalRepresentation14_data3 W hW D
  exact ⟨prop59_mirrorRep_data3
    (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap _ x hmirrorDomain⟩

end DirectedDistances.PaperProofs.Section5

end
