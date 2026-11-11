module

public import DirectedDistances.PaperProofs.Section5.D39UIBHBOTMeasurability

/-! Helpers for transporting the convergence in Proposition 5.16 to the topology of -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Helper toward Definition 3.8 and Proposition 5.16 (prop-disk-bs-conv).
The map from the faced-ball topology to the local topology rooted-map topology is
continuous. Its radius-`r` local topology ball is determined by the faced ball of radius
`r`, via the comparison in `D39UIBHBOTMeasurability`. -/
theorem continuous_toD39RootedMap :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    Continuous (fun M : RootedLocallyFinitePlanarMap =>
      M.toRootedLocallyFiniteMap.toD39RootedMap) := by
  let S := rootedLocallyFiniteFacedBallSystem
  let T := d39RootedBallSystem
  let f : S.Object → T.Object :=
    fun M => M.toRootedLocallyFiniteMap.toD39RootedMap
  letI : TopologicalSpace FacedFramedBallClass := ⊥
  letI : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  letI : TopologicalSpace D39BallClass := ⊥
  letI : DiscreteTopology D39BallClass := ⟨rfl⟩
  letI : TopologicalSpace S.Object := localClassTopology S.ballClass
  letI : TopologicalSpace T.Object := localClassTopology T.ballClass
  change Continuous[
    bsLocalDistanceTopologyGeneric S,
    bsLocalDistanceTopologyGeneric T] f
  rw [bsLocalDistanceTopology_eq_localClassTopologyGeneric S,
    bsLocalDistanceTopology_eq_localClassTopologyGeneric T]
  change Continuous[
    TopologicalSpace.generateFrom (localCylinders S.ballClass),
    TopologicalSpace.generateFrom (localCylinders T.ballClass)] f
  rw [continuous_generateFrom_iff]
  rintro U ⟨r, c, rfl⟩
  change IsOpen ((T.ballClass r ∘ f) ⁻¹' ({c} : Set D39BallClass))
  have hcoordinate : T.ballClass r ∘ f =
      facedFramedBallClassToD39BallClass ∘ S.ballClass r := by
    funext M
    change d39BallClass M.toRootedLocallyFiniteMap.toD39RootedMap
        (r + 1) (Nat.succ_pos r) =
      facedFramedBallClassToD39BallClass
        (rootedLocallyFiniteFacedBallClass r M)
    exact d39BallClass_eq_facedFramedBallClassToD39BallClass M r
  have hsource : Continuous (S.ballClass r) := by
    exact DirectedDistances.Probability.continuous_localClass S.ballClass r
  have hconvert : Continuous facedFramedBallClassToD39BallClass := by
    apply continuous_discrete_rng.mpr
    intro d
    exact isOpen_discrete _
  rw [hcoordinate]
  exact (hconvert.comp hsource).isOpen_preimage _ (isOpen_discrete _)

/-- Helper toward Definition 3.8 and Proposition 5.16 (prop-disk-bs-conv).
The continuous carrier map is measurable for the associated Borel structures. -/
theorem measurable_toD39RootedMap :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    letI : MeasurableSpace D39RootedMap := borel D39RootedMap
    letI : BorelSpace D39RootedMap := ⟨rfl⟩
    Measurable (fun M : RootedLocallyFinitePlanarMap =>
      M.toRootedLocallyFiniteMap.toD39RootedMap) := by
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  letI : TopologicalSpace D39RootedMap :=
    bsLocalDistanceTopologyGeneric d39RootedBallSystem
  letI : MeasurableSpace D39RootedMap := borel D39RootedMap
  letI : BorelSpace D39RootedMap := ⟨rfl⟩
  exact continuous_toD39RootedMap.measurable

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv). The push-forwards of
the finite disk-rooted laws converge in law to the push-forward of the UIBHBOT
law in the local topology rooted-map topology. The sequence premises are exactly those of
`diskRootedPlanarMapLaw_tendsto_uibhbot`. -/
theorem diskRootedPlanarMapLaw_d39_tendsto_uibhbot
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
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    letI : MeasurableSpace D39RootedMap := borel D39RootedMap
    letI : BorelSpace D39RootedMap := ⟨rfl⟩
    Tendsto (fun k =>
      (diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map
          (fun M : RootedLocallyFinitePlanarMap =>
            M.toRootedLocallyFiniteMap.toD39RootedMap))
      atTop
      (𝓝 ((uibhbotRootedPlanarMapLaw).map
        (fun M : RootedLocallyFinitePlanarMap =>
          M.toRootedLocallyFiniteMap.toD39RootedMap))) := by
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  letI : TopologicalSpace D39RootedMap :=
    bsLocalDistanceTopologyGeneric d39RootedBallSystem
  letI : MeasurableSpace D39RootedMap := borel D39RootedMap
  letI : BorelSpace D39RootedMap := ⟨rfl⟩
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k => diskRootedPlanarMapLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2)
    uibhbotRootedPlanarMapLaw
    (diskRootedPlanarMapLaw_tendsto_uibhbot A hA ell hadm hlo hhi)
    continuous_toD39RootedMap

end DirectedDistances.PaperProofs.Section5
