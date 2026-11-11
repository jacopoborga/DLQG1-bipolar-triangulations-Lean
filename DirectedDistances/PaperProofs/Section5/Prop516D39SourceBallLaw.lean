module

public import DirectedDistances.PaperProofs.Section5.Prop516D39Transport

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv).
The local topology ball-coordinate law of the realized UIBHBOT rooted-map law is the
push-forward of the canonical faced UIBHBOT ball-class law. -/
theorem uibhbotRootedPlanarMapLaw_map_d39BallClass (r : ℕ) :
    letI : TopologicalSpace FacedFramedBallClass := ⊥
    letI : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
    letI : MeasurableSpace FacedFramedBallClass := ⊤
    letI : MeasurableSpace D39BallClass := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    uibhbotRootedPlanarMapLaw.map (fun M =>
      d39BallClass (M.toRootedLocallyFiniteMap.toD39RootedMap)
        (r + 1) (Nat.succ_pos r)) =
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map (fun W =>
        facedFramedBallClassToD39BallClass
          (facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r))) := by
  letI : TopologicalSpace FacedFramedBallClass := ⊥
  letI : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  letI : MeasurableSpace FacedFramedBallClass := ⊤
  letI : MeasurableSpace D39BallClass := ⊤
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  change ((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode).map
      (fun M => d39BallClass (M.toRootedLocallyFiniteMap.toD39RootedMap)
        (r + 1) (Nat.succ_pos r)) = _
  have hball : Measurable (fun M : RootedLocallyFinitePlanarMap =>
      d39BallClass (M.toRootedLocallyFiniteMap.toD39RootedMap)
        (r + 1) (Nat.succ_pos r)) := by
    let T := d39RootedBallSystem
    letI : TopologicalSpace T.Object := bsLocalDistanceTopologyGeneric T
    letI : MeasurableSpace T.Object := borel T.Object
    letI : BorelSpace T.Object := ⟨rfl⟩
    have hcoord : Measurable (T.ballClass r) := by
      apply measurable_iff_comap_le.mpr
      change MeasurableSpace.comap (T.ballClass r) ⊤ ≤
        @borel T.Object (bsLocalDistanceTopologyGeneric T)
      rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic T]
      exact le_iSup_of_le r le_rfl
    change Measurable (T.ballClass r ∘
      (fun M : RootedLocallyFinitePlanarMap =>
        M.toRootedLocallyFiniteMap.toD39RootedMap))
    exact hcoord.comp measurable_toD39RootedMap
  rw [Measure.map_map hball measurable_uibhbotRootedPlanarMapOfCode]
  apply Measure.map_congr
  filter_upwards [uibhbotRootedPlanarMapOfCode_ae_facedClass] with W hW
  change d39BallClass
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)
      (r + 1) (Nat.succ_pos r) = _
  rw [d39BallClass_eq_facedFramedBallClassToD39BallClass
    (uibhbotRootedPlanarMapOfCode W) r]
  rw [hW r]

end DirectedDistances.PaperProofs.Section5
