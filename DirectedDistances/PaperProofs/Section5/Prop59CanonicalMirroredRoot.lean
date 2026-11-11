/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat3

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`). This file identifies the
canonical mirrored-domain obligation exactly; it makes no paper-completion
claim.

The remaining root question, with all OPEN 1 binders, is whether for every
`W : ℤ → Fin 3`, `H : WholePlaneRotationHypothesis W`,
`h0 : BoundaryHitWitnesses (shiftedStream W 0)`,
`hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a`,
`hR : ∀ n, 0 ≤ R (kmswPastCode W) n`,
`hfin : KMSWFiniteIncidence (kmswPastCode W)`,
`hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n`, and
`hA : D39GeomDomain A rho`, where `A` and `rho` are the canonical assembly
map and root, one can prove
`A.toPlaneMapWithMissing.missing rho.1`.

Three routes toward that implication were checked:

1. Derive a strict left-record description from `hL`, `hR`, and `hRpos` and
   apply the whole-plane record lemmas. The available lemmas transport an
   explicitly supplied strict record; these binders do not themselves provide
   the needed all-window strict-record witness.
2. Construct `UIBHBOTCertifiedRootCapture W 0`. Its capture event, seam
   certificates, and marked missing stage dart are additional data; no
   construction from the listed binders was found.
3. Use `hA.rootValid`. Its present-root branch is allowed when the root dart's
   direction agrees with the map orientation, so this field does not discharge
   the missing-tag obligation.

The proved characterization below shows that the precise additional fact
needed is `¬ wholePlaneEdgePresent W (uibhbotRootEdge W)`. It does not assert
that this fact follows from OPEN 1. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. The canonical assembly root is marked
missing exactly when its source UIBHBOT root edge is absent from the
whole-plane map. -/
theorem prop59_canonicalAssembly_rootMissing_iff_rootAbsent
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) :
    let A := uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos
    let rho := uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin
    A.toPlaneMapWithMissing.missing rho.1 ↔
      ¬ wholePlaneEdgePresent W (uibhbotRootEdge W) := by
  classical
  dsimp only [uibhbotD39CanonicalAssemblyMap, uibhbotD39CanonicalAssemblyRoot]
  let P := uibhbotD39PastCanonicalDrawing W hL hR hfin
  let hp := uibhbotD39PastCanonicalDrawing_pos W hL hR hfin
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin
  let F := uibhbotD39FutureCanonicalDrawing W H h0
  let hf := uibhbotD39FutureCanonicalDrawing_pos W H h0
  let hFim := uibhbotD39FutureCanonicalDrawing_image W H h0
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W H h0
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  change (uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin
      P hp ha F hf hFim hFa hRpos).missing
      (uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa).1 ↔
    ¬ wholePlaneEdgePresent W (uibhbotRootEdge W)
  have hmark := uibhbotAssemblyD39RootMark_eq W H h0 hL hR hfin
    P hp ha F hf hFim hFa
  have hroot : (uibhbotAssemblyD39RootMark W H h0 hL hR hfin
      P hp ha F hf hFim hFa).1 =
        Quotient.mk G.edgeSetoid (uibhbotRootEdge W, false) :=
    congrArg Prod.fst hmark
  rw [hroot]
  exact uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
    (uibhbotRootEdge W, false)

/-- Helper toward Proposition 5.9. For a canonical assembly satisfying the
Definition 3.8 domain, its mirrored geometric domain is equivalent to
whole-plane absence of the canonical root edge. -/
theorem prop59_canonicalAssembly_geomMirrorDomain_iff_rootAbsent
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
        (d39GeomMirrorRoot (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin)) ↔
      ¬ wholePlaneEdgePresent W (uibhbotRootEdge W) := by
  rw [prop59_canonicalAssembly_geomMirrorDomain_iff_missing
    W H h0 hL hR hfin hRpos hA]
  exact prop59_canonicalAssembly_rootMissing_iff_rootAbsent
    W H h0 hL hR hfin hRpos

end DirectedDistances.PaperProofs.Section5
