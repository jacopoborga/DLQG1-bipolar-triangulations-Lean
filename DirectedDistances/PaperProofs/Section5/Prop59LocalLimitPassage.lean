module

public import DirectedDistances.Probability.LawInvarianceLimit
public import DirectedDistances.PaperProofs.Section3.BSTopologyGenericMetrizable
public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarLaw
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorContinuity

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability
open Filter MeasureTheory TopologicalSpace
open scoped Topology

/-- Helper toward Proposition 5.9. If every admissible finite disk law is
invariant under the ordered-root mirror, then the UIBHBOT law is invariant
under that mirror. The sole open finite input is the displayed finite-law
invariance premise; its source-specific proof uses the finite right-side
sample bridge recorded at `Prop59FiniteReflectionGrade2.lean:128-144`.

The continuity premise needed by the local-limit argument is discharged by
`continuous_mirrorRootedLocallyFinitePlanarMap` at
`RootedLocallyFiniteMirrorContinuity.lean:863`; its `letI` topology is exactly
`bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem`, the local
topology in `LawInvarianceLimit.lean:26`. Closedness follows from
`rootedPlanarMapLaw_hasOuterApproxClosed` in
`BSTopologyGenericMetrizable.lean:143-145`. This is a helper, not a paper -/
theorem uibhbotRootedPlanarMapLaw_map_eq_of_finite_disk_mirror_invariant
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ))
    (hfinite :
      letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
        bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
      letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
        borel RootedLocallyFinitePlanarMap
      letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
      ∀ k,
        (diskRootedPlanarMapLaw (k + 1) (ell k)
          (hadm k).1 (hadm k).2.1 (hadm k).2.2).map
            mirrorRootedLocallyFinitePlanarMap =
          diskRootedPlanarMapLaw (k + 1) (ell k)
            (hadm k).1 (hadm k).2.1 (hadm k).2.2) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).map
      mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw := by
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  have hclosed : @HasOuterApproxClosed RootedLocallyFinitePlanarMap
      (bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem) :=
    DirectedDistances.PaperProofs.Section3.rootedPlanarMapLaw_hasOuterApproxClosed
  have hm : Continuous mirrorRootedLocallyFinitePlanarMap :=
    continuous_mirrorRootedLocallyFinitePlanarMap
  exact uibhbotRootedPlanarMapLaw_map_eq_of_disk_map_eq
    A hA ell hadm hlo hhi hclosed mirrorRootedLocallyFinitePlanarMap hm hfinite

end DirectedDistances.PaperProofs.Section5
end
