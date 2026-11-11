module

public import DirectedDistances.PaperProofs.Section5.DiskRootedMirrorFacedCompat
public import DirectedDistances.PaperProofs.Section3.BSTopologyGenericMetrizable

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability TopologicalSpace
open scoped Topology

/- Helper toward Proposition 5.9. This code-law mirror invariance does not establish
`x̃_k = h(x_{1-k})`; reconciling them through the finite boundary-reversal/source-map -/
theorem uibhbotRootedPlanarMapLaw_mirror_invariant :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
      mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw.toMeasure := by
  exact uibhbotLaw_mirror_invariant
    DirectedDistances.PaperProofs.Section3.rootedPlanarMapLaw_hasOuterApproxClosed

end DirectedDistances.PaperProofs.Section5

