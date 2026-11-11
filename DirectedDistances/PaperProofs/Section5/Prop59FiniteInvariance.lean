module

public import DirectedDistances.PaperProofs.Section5.Prop59LocalLimitPassage
public import DirectedDistances.PaperProofs.Section5.Prop59RightSampleBridge
public import DirectedDistances.PaperProofs.Section5.DiskRootedMirrorFacedCompat

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability MeasureTheory TopologicalSpace
open Filter
open scoped Topology






theorem diskRootedPlanarMapLaw_map_mirror_of_admissible_sequence
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
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
          (hadm k).1 (hadm k).2.1 (hadm k).2.2 := by
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  intro k
  apply Subtype.ext
  change (diskRootedPlanarMapLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2).toMeasure.map
        mirrorRootedLocallyFinitePlanarMap =
    (diskRootedPlanarMapLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2).toMeasure
  exact diskRootedPlanarMapLaw_mirror_invariant
    (k + 1) (ell k) (hadm k).1 (hadm k).2.1 (hadm k).2.2

/-- Helper toward Proposition 5.9. The local-limit mirror invariance follows
unconditionally from the finite disk mirror invariance proved above. -/
theorem uibhbotRootedPlanarMapLaw_map_eq_unconditionally :
    ∀ (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
      (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
        ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
      (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
      (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)),
      letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
        bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
      letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
        borel RootedLocallyFinitePlanarMap
      letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
      (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).map
        mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw := by
  intro A hA ell hadm hlo hhi
  exact uibhbotRootedPlanarMapLaw_map_eq_of_finite_disk_mirror_invariant
    A hA ell hadm hlo hhi
    (diskRootedPlanarMapLaw_map_mirror_of_admissible_sequence
      A hA ell hadm hlo hhi)

end DirectedDistances.PaperProofs.Section5
end
