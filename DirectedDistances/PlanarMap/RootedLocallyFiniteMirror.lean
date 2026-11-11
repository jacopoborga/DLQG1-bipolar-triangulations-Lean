module

public import DirectedDistances.PaperProofs.Section3.BSTopologyGeneric
















public section
namespace DirectedDistances.PlanarMap

open DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory TopologicalSpace

/- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The exact same-radius coordinate obligation for a proposed rooted reflection
neither argument is supplied by this file. Source: -/
@[expose] def RootedLocallyFiniteMirrorCoordinateEquation
    (mirrorMap : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap)
    (mirrorClass : FacedFramedBallClass → FacedFramedBallClass) : Prop :=
  ∀ (r : ℕ) (M : RootedLocallyFinitePlanarMap),
    rootedLocallyFiniteFacedBallClass r (mirrorMap M) =
      mirrorClass (rootedLocallyFiniteFacedBallClass r M)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The same-radius coordinate equation implies continuity in the helper topology.
This does not construct a reflection or discharge the coordinate obligation. -/
theorem continuous_mirrorRootedLocallyFinitePlanarMap_of_coordinateEquation
    (mirrorMap : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap)
    (mirrorClass : FacedFramedBallClass → FacedFramedBallClass)
    (h : RootedLocallyFiniteMirrorCoordinateEquation mirrorMap mirrorClass) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    Continuous mirrorMap := by
  rw [bsLocalDistanceTopology_eq_localClassTopologyGeneric]
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    localClassTopology rootedLocallyFiniteFacedBallClass
  change @Continuous _ _ _ (generateFrom
    (localCylinders rootedLocallyFiniteFacedBallClass)) mirrorMap
  apply continuous_generateFrom_iff.mpr
  rintro s ⟨r, c, rfl⟩
  have hc : Continuous
      (mirrorClass ∘ rootedLocallyFiniteFacedBallClass r) :=
    continuous_of_discreteTopology.comp
      (continuous_localClass rootedLocallyFiniteFacedBallClass r)
  have heq : rootedLocallyFiniteFacedBallClass r ∘ mirrorMap =
      mirrorClass ∘ rootedLocallyFiniteFacedBallClass r := funext (h r)
  change IsOpen ((rootedLocallyFiniteFacedBallClass r ∘ mirrorMap) ⁻¹' {c})
  rw [heq]
  exact hc.isOpen_preimage {c} (isOpen_discrete _)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The same-radius coordinate equation implies Borel measurability in the helper
topology. The coordinate obligation remains an explicit premise, not an axiom. -/
theorem measurable_mirrorRootedLocallyFinitePlanarMap_of_coordinateEquation
    (mirrorMap : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap)
    (mirrorClass : FacedFramedBallClass → FacedFramedBallClass)
    (h : RootedLocallyFiniteMirrorCoordinateEquation mirrorMap mirrorClass) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    Measurable mirrorMap := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  exact (continuous_mirrorRootedLocallyFinitePlanarMap_of_coordinateEquation
    mirrorMap mirrorClass h).measurable

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
For a non-loop frame edge, reversing its root incidence while retaining its
frame dart fails the reflected carrier's root-incidence condition. This only
rules out that particular attempted construction; it does not rule out a
reflection that also transports the ordered frame. Source: -/
theorem reversedRoot_not_at_retainedFrame (M : RootedLocallyFiniteMap)
    (hnonloop : ¬ M.rot.SameCycle M.frameEdgeDart (M.edgeInv M.frameEdgeDart)) :
    ¬ Equiv.Perm.SameCycle M.rot.symm (M.edgeInv M.frameEdgeDart) M.frameEdgeDart := by
  intro h
  exact hnonloop (Equiv.Perm.sameCycle_inv.mp h).symm

end DirectedDistances.PlanarMap
