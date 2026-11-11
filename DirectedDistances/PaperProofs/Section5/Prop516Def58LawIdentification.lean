/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516RootedLawConvergence
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass
public import DirectedDistances.PaperProofs.Section5.Prop516FiniteOrderedMarkBridge2

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory
open scoped ENNReal Topology




























































































/-- Helper toward Proposition 5.16. The combinatorial UIBHBOT law is, by its
definition, the push-forward of the code law under the total measurable map
`uibhbotRootedPlanarMapOfCode`.
Source: `Prop516RootedLawConvergence.lean:165-176`. -/
theorem uibhbotRootedPlanarMapLaw_toMeasure_eq_code_map :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure =
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map uibhbotRootedPlanarMapOfCode := by
  rfl

/-- Helper toward Proposition 5.16. The finite uniform `Fin ell` mark selects
the same lower-left boundary dart as the source boundary enumeration: under a
combinatorial isomorphism of the representative channeled map with its KMSW
sample, index `k` in the source `leftPath.darts` maps to the KMSW root dart
selected by `k`. In the stage-list representation the same edge is at position
`LL.length - 1 - k`, as proved by the ordered-mark bridge. This matches the -/
theorem diskRootedSample_sourceBoundaryDart_eq_mark_ordered :
    ∀ (n ell : ℕ) (hell : 0 < ell)
      (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled})
      (I : DirectedMapWithMissingIso q.val.out.partialMap
        (kmswStageDirectedMap
          (finiteCodeExtend (n := n + 1)
            ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n))
      (k : Fin ell),
      I.toEquiv (q.val.out.B.leftPath.darts.get
        ⟨k.val, by rw [q.val.out.B.leftPath.darts_length]; omega⟩) =
        kmswDiskRootDart
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q)
          (Fin.cast (by omega : ell = (ell + 1) - 1) k) := by
  intro n ell hell q I k
  exact DirectedDistances.PaperProofs.Section5.diskRootedSample_sourceBoundaryDart_eq_mark
    n ell hell q I k

end DirectedDistances.PaperProofs.Section5
