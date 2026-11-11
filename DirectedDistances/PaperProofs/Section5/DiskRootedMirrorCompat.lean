module

public import DirectedDistances.PaperProofs.Section5.DiskRootedMirrorLaw
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorClose

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-! Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.

Finite KMSW reflection identifies carriers through an equivalence, so equality of
the concrete `RootedLocallyFinitePlanarMap` values is too strong. The remaining
pointwise compatibility is equality of every faced-ball class. It is recorded
below as an open obligation and is not used as a premise. -/






@[expose] def diskRootedPlanarSampleMirrorFacedClassCompatibility
    (n ell : ℕ) (hell : 0 < ell) : Prop :=
  ∀ p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell,
    ∀ r : ℕ,
      rootedLocallyFiniteFacedBallClass r
          (mirrorRootedLocallyFinitePlanarMap
            (diskRootedPlanarMapOfSample n ell hell p)) =
        rootedLocallyFiniteFacedBallClass r
          (diskRootedPlanarMapOfMirroredSample n ell hell p)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
reindexed finite sample is the faced-ball marginal of the disk-rooted map law.
This is the finite parameter push-forward; it does not identify that sample
with the pointwise geometric mirror. -/
theorem diskRootedPlanarMapLaw_map_mirroredSample_facedClass
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) (r : ℕ) :
    let Q :=
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : TopologicalSpace FacedFramedBallClass := ⊥
    letI : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
    letI : MeasurableSpace FacedFramedBallClass := ⊤
    ((diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure).map
        (rootedLocallyFiniteFacedBallClass r) =
      ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
        (rootedLocallyFiniteFacedBallClass r ∘
          diskRootedPlanarMapOfMirroredSample n ell hell) := by
  classical
  let Q :=
    {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  let : MeasurableSpace FacedFramedBallClass := ⊤
  have h := diskRootedPlanarMapLaw_map_mirror n ell hell hle hmod
  have hc := congrArg
    (fun μ : Measure RootedLocallyFinitePlanarMap =>
      μ.map (rootedLocallyFiniteFacedBallClass r)) h
  have hclassmeas : Measurable (rootedLocallyFiniteFacedBallClass r) := by
    apply measurable_iff_comap_le.mpr
    let S := rootedLocallyFiniteFacedBallSystem
    change MeasurableSpace.comap (S.ballClass r) ⊤ ≤
      @borel S.Object (bsLocalDistanceTopologyGeneric S)
    rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic S]
    exact le_iSup_of_le r le_rfl
  rw [Measure.map_map hclassmeas (measurable_of_countable _)] at hc
  exact hc.symm

end DirectedDistances.PaperProofs.Section5
