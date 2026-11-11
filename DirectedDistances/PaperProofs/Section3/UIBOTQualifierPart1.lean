/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart8







public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section5
open DirectedDistances.Paper.Section4 MeasureTheory Filter
open scoped Classical

local instance uibotQualifierPart1MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotQualifierPart1BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
local instance uibotQualifierPart1XDPFintype : Fintype XDP :=
  Fintype.ofList [.ldp, .sdp] (by intro x; cases x <;> simp)
local instance uibotQualifierPart1OptionMeasurableSpace :
    MeasurableSpace (Option (ℕ × ℕ)) := ⊤

/-- Helper toward Proposition 3.9: the joint least offsets selected with
exactly the actual slice witness, extended by zero off its existence event.
The extension is used only to define a total random variable. -/
@[expose] def uibotCodeCoalescenceOffsets (W : ℤ → Fin 3) (x : XDP) (k : ℤ) : ℕ × ℕ :=
  if hW : Nonempty (M0CutGeodesicSliceWitness W x) then
    let s := Classical.choice hW
    (s.thetaMinus k, s.theta k)
  else (0, 0)

private theorem offset_reader_source {W : ℤ → Fin 3} {x : XDP}
    (s : M0CutGeodesicSliceWitness W x) (k : ℤ) {N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso (m0GeodesicSide s.hp (s.P k) .left) N) :
    (geoSliceOneSideOffsetsOption (if x = XDP.ldp then true else false) N).getD (0, 0) =
      (s.thetaMinus k, s.theta k) := by
  obtain ⟨q, hq, _, _, _, hoff⟩ := s.oneSideReaders_eq_of_markedIso k I
  rw [hoff]
  rfl

private theorem aemeasurable_offsets_nonneg (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    AEMeasurable (fun W => uibotCodeCoalescenceOffsets W x k)
      wholePlaneIIDCodeMeasure := by
  let longest := if x = XDP.ldp then true else false
  let f (z : LPlusCodingPair x) : ℕ × ℕ :=
    if hz : z ∈ lPlusCertifiedCodingPairDomain x then
      (geoSliceOneSideOffsetsOption longest
        (lPlusCanonicalSideOnCertifiedPair x k ⟨z, hz⟩)).getD (0, 0)
    else (0, 0)
  have hf : Measurable f :=
    ((measurable_of_countable (fun p : Option (ℕ × ℕ) => p.getD (0, 0))).comp
      ((measurable_geoSliceOneSideOffsetsOption longest).comp
        (measurable_lPlusCanonicalSideOnCertifiedPair x k))).dite measurable_const
          (measurableSet_lPlusCertifiedCodingPairDomain x)
  apply (hf.comp_aemeasurable (aemeasurable_lPlusCodingPairObservation x k)).congr
  filter_upwards [ae_m0CutGeodesicSliceWitness x,
    lemma55LeftSideClassOption_ae_eq_lPlusRawPairCanonicalClassOption x k hk]
    with W hW hraw
  let s := Classical.choice hW
  have hsome := hraw.symm.trans (lemma55LeftSideClassOption_eq_of_sliceWitness s k)
  dsimp only [Function.comp_apply] at hsome
  by_cases hz : lPlusCodingPairObservation x k W ∈ lPlusCertifiedCodingPairDomain x
  · rw [lPlusRawPairCanonicalClassOption, dite_eq_left hz] at hsome
    obtain ⟨I⟩ := (geometricSideClass_eq_iff _ _).1 (Option.some.inj hsome).symm
    change f (lPlusCodingPairObservation x k W) = _
    dsimp only [f]
    rw [dite_eq_left hz, uibotCodeCoalescenceOffsets, dite_eq_left hW]
    exact offset_reader_source s k I
  · rw [lPlusRawPairCanonicalClassOption, dite_eq_right hz] at hsome
    cases hsome

private theorem aemeasurable_offsets_nonpos (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable (fun W => uibotCodeCoalescenceOffsets W x k)
      wholePlaneIIDCodeMeasure := by
  let longest := if x = XDP.ldp then true else false
  let D : Set (LMinusSidePresentation x × (ℕ → ℤ × ℤ)) :=
    {z | KMSWFiniteIncidence z.1.code.1 ∧
      z.2 ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime}
  have hD : MeasurableSet D :=
    (measurableSet_finiteIncidence.preimage
      ((measurable_lMinusSidePresentation_code x).fst.comp measurable_fst)).inter
    ((selectedCutCoherentDomain_measurable_conull x renewalTime
      renewalTime_positiveSuccessTime).1.preimage measurable_snd)
  let g (z : D) : LMinusCanonicalCodingDomain x :=
    ⟨(z.val.1, ⟨z.val.2, z.property.2⟩), z.property.1⟩
  have hg : Measurable g :=
    ((measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)).subtype_mk
  let f (z : LMinusSidePresentation x × (ℕ → ℤ × ℤ)) : ℕ × ℕ :=
    if hz : z ∈ D then
      (geoSliceOneSideOffsetsOption longest
        (lMinusCanonicalSideOnCoherent x (g ⟨z, hz⟩))).getD (0, 0)
    else (0, 0)
  have hf : Measurable f :=
    ((measurable_of_countable (fun p : Option (ℕ × ℕ) => p.getD (0, 0))).comp
      (((measurable_geoSliceOneSideOffsetsOption longest).comp
        (measurable_lMinusCanonicalSideOnCoherent x)).comp hg)).dite measurable_const hD
  have hobs := (aemeasurable_decodeLMinus_leftSideObsNonpos x k).prodMk
    (aemeasurable_boundaryFutureHattedPath k)
  apply (hf.comp_aemeasurable hobs).congr
  filter_upwards [ae_m0CutGeodesicSliceWitness x,
    geoSlice_lMinusRawCanonicalClassOption_ae_eq x k hk,
    lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4 x k hk]
    with W hW hraw hleft
  let s := Classical.choice hW
  have hsome := hraw.trans (hleft.symm.trans
    (lemma55LeftSideClassOption_eq_of_sliceWitness s k))
  let z := (decodeLMinus x k (leftSideObsNonpos x k W), boundaryFutureHattedPath k W)
  by_cases hz : z ∈ D
  · have hz' : KMSWFiniteIncidence z.1.code.1 ∧
        z.2 ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime := hz
    change lMinusRawCanonicalClassOption x z = _ at hsome
    rw [lMinusRawCanonicalClassOption, dite_eq_left hz'] at hsome
    obtain ⟨I⟩ := (geometricSideClass_eq_iff _ _).1 (Option.some.inj hsome).symm
    change f z = _
    dsimp only [f]
    rw [dite_eq_left hz, uibotCodeCoalescenceOffsets, dite_eq_left hW]
    exact offset_reader_source s k I
  · have hz' : ¬ (KMSWFiniteIncidence z.1.code.1 ∧
        z.2 ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) := hz
    change lMinusRawCanonicalClassOption x z = _ at hsome
    rw [lMinusRawCanonicalClassOption, dite_eq_right hz'] at hsome
    cases hsome

/-- Helper toward Proposition 3.9: the complete least-offset family is
a.e. measurable jointly in both metrics and every integer boundary index. -/
theorem aemeasurable_uibotCodeCoalescenceOffsets :
    AEMeasurable uibotCodeCoalescenceOffsets wholePlaneIIDCodeMeasure := by
  apply aemeasurable_pi_iff.mpr
  intro x
  apply aemeasurable_pi_iff.mpr
  intro k
  by_cases hk : 0 ≤ k
  · exact aemeasurable_offsets_nonneg x k hk
  · exact aemeasurable_offsets_nonpos x k (le_of_not_ge hk)

/-- Helper toward Proposition 3.9: a Borel geometric version of the
entire least-offset family, using the proved inverse of the class map. -/
@[expose] def uibotGeomCoalescenceOffsets : D39GeomRootedMapClass.{0} → XDP → ℤ → ℕ × ℕ :=
  uibotRecoveredObservable uibotCodeCoalescenceOffsets
    aemeasurable_uibotCodeCoalescenceOffsets

/-- Helper toward Proposition 3.9: the simultaneous geometric offset
observable is Borel measurable. -/
theorem measurable_uibotGeomCoalescenceOffsets :
    Measurable uibotGeomCoalescenceOffsets := measurable_uibotRecoveredObservable _ _

/-- Helper toward Proposition 3.9: on one conull event, all geometric
offsets agree with the offsets of the actual slice witness. -/
theorem uibotGeomCoalescenceOffsets_ae :
    uibotCodeCoalescenceOffsets =ᵐ[wholePlaneIIDCodeMeasure]
      uibotGeomCoalescenceOffsets ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
  uibotRecoveredObservable_ae _ _

/-- Helper toward Proposition 3.9: the exact offset-factor target, with
one witness per mode shared by all indices and by the existing slice factor. -/
theorem uibotGeomCoalescenceOffsets_ae_slice_characterization :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ x : XDP,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ k : ℤ,
        uibotGeomCoalescenceOffsets (uibotMeasurableWholePlaneClassMap
          uibotDeterministicComparison_proved W) x k =
            (s.thetaMinus k, s.theta k) ∧
        (uibotGeomSideSliceObservables (uibotMeasurableWholePlaneClassMap
          uibotDeterministicComparison_proved W) x k).2 =
          some (geometricSideClass (m0CutGeodesicSlice (hp := s.hp) s.P k
            (s.thetaMinus k) (s.theta k) (s.least k))) := by
  filter_upwards [uibotGeomCoalescenceOffsets_ae, uibotGeomSideSliceObservables_ae,
    ae_all_iff.mpr ae_m0CutGeodesicSliceWitness] with W hoff hside hw
  intro x
  let s := Classical.choice (hw x)
  refine ⟨s, fun k => ⟨?_, ?_⟩⟩
  · have he := congrArg (fun z => z x k) hoff.symm
    change uibotGeomCoalescenceOffsets _ x k = uibotCodeCoalescenceOffsets W x k at he
    exact he.trans (dite_eq_left (hw x))
  · have he := congrArg (fun z => (z x k).2) hside.symm
    change (uibotGeomSideSliceObservables _ x k).2 =
      m0CutGeodesicSliceClassOption x k W at he
    exact he.trans (dite_eq_left (hw x))

/-- Helper toward Proposition 3.9: one measurable factor gives the least
coalescence pair and the existing slice value with a shared source witness. -/
theorem exists_measurable_uibotCoalescenceOffsets :
    ∃ Theta : D39GeomRootedMapClass.{0} → XDP → ℤ → ℕ × ℕ,
      Measurable Theta ∧
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ x : XDP,
        ∃ s : M0CutGeodesicSliceWitness W x, ∀ k : ℤ,
          Theta (uibotMeasurableWholePlaneClassMap
            uibotDeterministicComparison_proved W) x k =
              (s.thetaMinus k, s.theta k) ∧
          (uibotGeomSideSliceObservables (uibotMeasurableWholePlaneClassMap
            uibotDeterministicComparison_proved W) x k).2 =
            some (geometricSideClass (m0CutGeodesicSlice (hp := s.hp) s.P k
              (s.thetaMinus k) (s.theta k) (s.least k))) :=
  ⟨uibotGeomCoalescenceOffsets, measurable_uibotGeomCoalescenceOffsets,
    uibotGeomCoalescenceOffsets_ae_slice_characterization⟩

end DirectedDistances.PaperProofs.Section3
end
