module

public import DirectedDistances.KMSW.UIBHBOTRootedPlanarMap
public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarLaw
public import DirectedDistances.PaperProofs.Section5.FacedDiskWindowCompare
public import DirectedDistances.PaperProofs.Section5.UIBHBOTFacedBallLaw
public import DirectedDistances.PaperProofs.Section3.BSTopologyGeneric
public import DirectedDistances.PaperProofs.Section3.RootedMapBallMeasurability

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
admits a measurable conull subevent carrying all ball identifications. -/
theorem exists_uibhbotRootedPlanarConullEvent :
    ∃ s : Set (ℤ → Fin 3), MeasurableSet s ∧
      (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), W ∈ s) ∧
      ∀ W ∈ s, ∃ M : RootedLocallyFinitePlanarMap,
        (∃ (H : WholePlaneRotationHypothesis W)
          (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
          (C₀ : UIBHBOTCertifiedRootCapture W 0)
          (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)),
          M = uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap) ∧
        ∀ r, rootedLocallyFiniteFacedBallClass r M =
          facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r) := by
  have h : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ M : RootedLocallyFinitePlanarMap,
        (∃ (H : WholePlaneRotationHypothesis W)
          (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
          (C₀ : UIBHBOTCertifiedRootCapture W 0)
          (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)),
          M = uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap) ∧
        ∀ r, rootedLocallyFiniteFacedBallClass r M =
          facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r) := by
    filter_upwards [uibhbotCodeLawRel_ae_rootedLocallyFinitePlanarMap] with W hW
    obtain ⟨H, hhit, C₀, hcap, _⟩ := hW
    exact ⟨uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap,
      ⟨H, hhit, C₀, hcap, rfl⟩,
      uibhbotRootedLocallyFinitePlanarMap_facedBallClass_index_eq W H hhit C₀ hcap⟩
  obtain ⟨s, hs, hsm, hsub⟩ := h.exists_measurable_mem
  exact ⟨s, hsm, hs, hsub⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
the code supplies the source planar map and all faced-ball identifications. -/
@[expose] noncomputable def uibhbotRootedPlanarMapConullEvent : Set (ℤ → Fin 3) :=
  exists_uibhbotRootedPlanarConullEvent.choose

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
every code in it supplies the source construction and all its ball classes. -/
theorem uibhbotRootedPlanarMapConullEvent_spec :
    MeasurableSet uibhbotRootedPlanarMapConullEvent ∧
      (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        W ∈ uibhbotRootedPlanarMapConullEvent) ∧
      ∀ W ∈ uibhbotRootedPlanarMapConullEvent, ∃ M : RootedLocallyFinitePlanarMap,
        (∃ (H : WholePlaneRotationHypothesis W)
          (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
          (C₀ : UIBHBOTCertifiedRootCapture W 0)
          (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)),
          M = uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap) ∧
        ∀ r, rootedLocallyFiniteFacedBallClass r M =
          facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r) :=
  exists_uibhbotRootedPlanarConullEvent.choose_spec

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
parameters n = ell = 1 and mark zero, is used only outside the conull event. -/
@[expose] noncomputable def uibhbotRootedPlanarMapNullDefault :
    RootedLocallyFinitePlanarMap :=
  diskRootedPlanarMapOfCodeMark
    (Classical.choice (kmswLeftWalkClass_nonempty_of_domain 1 1
      (by decide) (by decide) ⟨0, by norm_num⟩)) 0

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
conull event, extended to the full code space by the fixed finite disk map. -/
@[expose] noncomputable def uibhbotRootedPlanarMapOfCode (W : ℤ → Fin 3) :
    RootedLocallyFinitePlanarMap := by
  classical
  exact if h : W ∈ uibhbotRootedPlanarMapConullEvent then
    (uibhbotRootedPlanarMapConullEvent_spec.2.2 W h).choose
  else uibhbotRootedPlanarMapNullDefault

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
map is a source construction, with simultaneous identification of every ball. -/
theorem uibhbotRootedPlanarMapOfCode_on_event (W : ℤ → Fin 3)
    (hW : W ∈ uibhbotRootedPlanarMapConullEvent) :
    (∃ (H : WholePlaneRotationHypothesis W)
      (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0)
      (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)),
      uibhbotRootedPlanarMapOfCode W =
        uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap) ∧
    ∀ r, rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W) =
      facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r) := by
  classical
  simpa only [uibhbotRootedPlanarMapOfCode, dite_eq_left hW] using
    (uibhbotRootedPlanarMapConullEvent_spec.2.2 W hW).choose_spec

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
full-space map has the fixed finite disk value. -/
theorem uibhbotRootedPlanarMapOfCode_off_event (W : ℤ → Fin 3)
    (hW : W ∉ uibhbotRootedPlanarMapConullEvent) :
    uibhbotRootedPlanarMapOfCode W = uibhbotRootedPlanarMapNullDefault := by
  classical
  exact dite_eq_right hW

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
a measurable-event splice of the canonical coordinate and a fixed class. -/
theorem uibhbotRootedPlanarMapOfCode_facedClass (W : ℤ → Fin 3) (r : ℕ) :
    rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W) =
      if W ∈ uibhbotRootedPlanarMapConullEvent then
        facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r)
      else rootedLocallyFiniteFacedBallClass r uibhbotRootedPlanarMapNullDefault := by
  classical
  by_cases hW : W ∈ uibhbotRootedPlanarMapConullEvent
  · rw [ite_eq_left hW]
    exact (uibhbotRootedPlanarMapOfCode_on_event W hW).2 r
  · rw [ite_eq_right hW, uibhbotRootedPlanarMapOfCode_off_event W hW]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
measurability of the source map into the faced-ball topology's Borel space. -/
theorem measurable_uibhbotRootedPlanarMapOfCode :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    Measurable uibhbotRootedPlanarMapOfCode := by
  classical
  apply (measurable_into_iff_ballClass_generic rootedLocallyFiniteFacedBallSystem
    uibhbotRootedPlanarMapOfCode).2
  intro r
  change Measurable (fun W =>
    rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W))
  simp_rw [uibhbotRootedPlanarMapOfCode_facedClass]
  exact Measurable.ite uibhbotRootedPlanarMapConullEvent_spec.1
    (measurable_facedUIBHBOTBallClassRel (r + 1) (Nat.succ_pos r)) measurable_const

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
simultaneously almost surely with the source's canonical faced coordinates. -/
theorem uibhbotRootedPlanarMapOfCode_ae_facedClass :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ r, rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W) =
        facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r) := by
  filter_upwards [uibhbotRootedPlanarMapConullEvent_spec.2.1] with W hW
  exact (uibhbotRootedPlanarMapOfCode_on_event W hW).2

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
law is the push-forward of the code law under the full-space measurable map. -/
@[expose] noncomputable def uibhbotRootedPlanarMapLaw :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    ProbabilityMeasure RootedLocallyFinitePlanarMap := by
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  exact uibhbotCodeLawRel.map uibhbotRootedPlanarMapOfCode

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
faced-class push-forward is the canonical source ball law at radius r+1. -/
theorem uibhbotRootedPlanarMapLaw_map_facedClass (r : ℕ) :
    letI : TopologicalSpace FacedFramedBallClass := ⊥
    letI : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
    letI : MeasurableSpace FacedFramedBallClass := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    uibhbotRootedPlanarMapLaw.map (rootedLocallyFiniteFacedBallClass r) =
      facedUIBHBOTBSBallLaw (r + 1) (Nat.succ_pos r) := by
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  let : MeasurableSpace FacedFramedBallClass := ⊤
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  have hclass : Measurable (rootedLocallyFiniteFacedBallClass r) := by
    apply measurable_iff_comap_le.mpr
    let S := rootedLocallyFiniteFacedBallSystem
    change MeasurableSpace.comap (S.ballClass r) ⊤ ≤
      @borel S.Object (bsLocalDistanceTopologyGeneric S)
    rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic S]
    exact le_iSup_of_le r le_rfl
  apply Subtype.ext
  change ((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode).map (rootedLocallyFiniteFacedBallClass r) =
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun W => facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r))
  rw [Measure.map_map hclass measurable_uibhbotRootedPlanarMapOfCode]
  apply Measure.map_congr
  filter_upwards [uibhbotRootedPlanarMapOfCode_ae_facedClass] with W hW
  exact hW r

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
the finite rooted-map laws converge to the UIBHBOT law in the faced-ball topology. -/
theorem diskRootedPlanarMapLaw_tendsto_uibhbot
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
    Tendsto (fun k => diskRootedPlanarMapLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop (𝓝 uibhbotRootedPlanarMapLaw) := by
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  let : MeasurableSpace FacedFramedBallClass := ⊤
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  apply def_3_9_rootedLocallyFiniteFacedBall_criterion.2
  intro r
  simpa only [diskRootedPlanarMapLaw_map_facedClass,
    uibhbotRootedPlanarMapLaw_map_facedClass] using
    facedDiskWindowTransport_limit A hA ell hadm hlo hhi (r + 1) (Nat.succ_pos r)

end DirectedDistances.PaperProofs.Section5
