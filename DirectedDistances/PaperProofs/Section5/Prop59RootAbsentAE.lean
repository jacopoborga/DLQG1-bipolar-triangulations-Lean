/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirroredRoot
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBusemannIdentified
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalDomain3

/-! Helpers toward Proposition 5.9. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. The canonical root edge is absent exactly
when arbitrarily late stages of its defining whole-plane edge stream still
omit it. This is the direct tail characterization of `wholePlaneEdgePresent`. -/
theorem prop59_uibhbotRootEdge_absent_iff_arbitrarilyLateAbsent
    (W : ℤ → Fin 3) :
    ¬ wholePlaneEdgePresent W (uibhbotRootEdge W) ↔
      ∀ M, ∀ h1M : 1 ≤ M, ∃ L, ∃ hML : M ≤ L,
        ¬ EdgePresent (shiftedStream W L)
          (wholePlaneEdgeTrans W 1 L (h1M.trans hML)
            (kmswLLCreatedEdge (shiftedStream W 1) 1)) := by
  change ¬ wholePlaneEdgePresent W
    (wholePlaneEdgeι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1)) ↔ _
  rw [wholePlaneEdgePresent_ι]
  push Not
  rfl

/-- Helper toward Proposition 5.9. Under the UIBHBOT code law, the canonical
root edge is almost surely absent; this follows from the almost-sure source
chain of missing lower-left boundary edges and its zeroth edge identity. -/
theorem prop59_uibhbotRootEdge_absent_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ¬ wholePlaneEdgePresent W (uibhbotRootEdge W) := by
  filter_upwards [ae_uibhbotBusemannSource_missing_edges] with W hsource
  obtain ⟨e, hchain, hinjective, hroot⟩ := hsource
  rw [← hroot]
  exact (hchain 0).2.2.1

/-- Helper toward Proposition 5.9. Almost surely, on the OPEN 1 canonical
assembly domain, its geometric mirror and mirrored root satisfy the same
Definition 3.8 domain conditions. -/
theorem prop59_canonicalAssembly_geomMirrorDomain_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (_hA : D39GeomDomain
          (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos)
          (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin)),
        D39GeomDomain
          (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos).geomMirror
          (d39GeomMirrorRoot
            (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin)) := by
  filter_upwards [uibhbotCodeLawRel_ae_d39CanonicalGeomDomain,
    prop59_uibhbotRootEdge_absent_ae] with W hdomain hrootAbsent
  obtain ⟨H, h0, hL, hR, hfin, hRpos, e, he, hA⟩ := hdomain
  refine ⟨H, h0, hL, hR, hfin, hRpos, hA, ?_⟩
  exact (prop59_canonicalAssembly_geomMirrorDomain_iff_rootAbsent
    W H h0 hL hR hfin hRpos hA).mpr hrootAbsent

end DirectedDistances.PaperProofs.Section5

end
