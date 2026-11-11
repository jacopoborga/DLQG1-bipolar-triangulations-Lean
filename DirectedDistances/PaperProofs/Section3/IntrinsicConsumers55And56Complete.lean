/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers55And56
public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion8
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers54And57Final
public import DirectedDistances.Paper.Section5.GeoInftyInd
public import DirectedDistances.Paper.Section5.GeoSlice

/-! # Simultaneous side and slice readers toward Lemmas 5.5 and 5.6

The Borel readers have the source independence and half-index laws. On one
iid conull event they identify the native geometric classes in every
representative, with common source witnesses and least offsets. Native-region
equality is supplied by `IntrinsicBetweenRegion8`. Intrinsic leftmostness and
uniqueness remain separate obligations; no intrinsic-object qualifier is removed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5 DirectedDistances.Paper.Section4
open MeasureTheory ProbabilityTheory Filter
open scoped Classical

local instance intrinsicConsumers55And56CompleteMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance intrinsicConsumers55And56CompleteBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

local notation "F₅₆" =>
  uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
local notation "O₅₆" => fun U : ℤ → Fin 3 => uibotGeomSideSliceObservables (F₅₆ U)

/-- Helper toward Proposition 3.9: one Borel family supplies both optional
side classes, the slice class and their common least-offset reader. -/
theorem intrinsicConsumers55And56_borel :
    Measurable (fun z : D39GeomRootedMapClass.{0} =>
      (uibotGeomSideSliceObservables z, uibotGeomCoalescenceOffsets z)) :=
  measurable_uibotGeomSideSliceObservables.prodMk measurable_uibotGeomCoalescenceOffsets

/-- Helper toward Proposition 3.9: every coordinate of the sampled
Borel family agrees with its code reader on the same iid conull event. -/
theorem intrinsicConsumers55And56_sample_eq_code :
    uibotCodeSideSliceObservables =ᵐ[wholePlaneIIDCodeMeasure] O₅₆ :=
  uibotGeomSideSliceObservables_ae

/-- Helper toward Proposition 3.9: on one iid event all representatives,
both metrics and all indices have the same native side and slice classes,
optional presence and least offsets, using a single source witness per mode.
This does not assert that the transported geodesics are intrinsically leftmost. -/
theorem intrinsicConsumers55And56_sample_classes_ae :
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := F₅₆ U
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))
      let D := m0CutData W H h hLL
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      ∃ s : ∀ x : XDP, M0CutGeodesicSliceWitness W x,
      z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root) ∧
        ∀ I : D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root,
        ∀ (x : XDP) (k : ℤ),
        let L := fun t => intrinsicGeodesicSide A
          (intrinsicBusemannImageCut W H G hp D A I)
          (I.h '' m0GeodesicAmbientRegion W H h) (I.vertexEquiv (D.x (k - 1)))
          (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (((s x).P k).codePath.edge n))) t
        let C := intrinsicGeodesicSliceOfCode W H h hpast hp A I (s x).P k
          ((s x).thetaMinus k) ((s x).theta k)
        uibotGeomSideSliceObservables z x k = uibotCodeSideSliceObservables W x k ∧
        ((uibotGeomSideSliceObservables z x k).1.1).isSome ∧
        ((uibotGeomSideSliceObservables z x k).1.2).isSome ∧
        ((uibotGeomSideSliceObservables z x k).2).isSome ∧
        Option.map forgetMarks (uibotGeomSideSliceObservables z x k).1.1 =
          some (intrinsicSideSubmapClass A (L .left) (I.vertexEquiv (D.x k))) ∧
        Option.map forgetMarks (uibotGeomSideSliceObservables z x k).1.2 =
          some (intrinsicSideSubmapClass A (L .right) (I.vertexEquiv (D.x k))) ∧
        Option.map forgetMarks (uibotGeomSideSliceObservables z x k).2 =
          some (intrinsicSideSubmapClass A C (I.vertexEquiv (D.x (k - 1)))) ∧
        IntrinsicLeastEdgeCoalescence
          (intrinsicGeodesicOfCode W H h hLL G hp A I ((s x).P (k - 1))).val
          (intrinsicGeodesicOfCode W H h hLL G hp A I ((s x).P k)).val
          ((s x).thetaMinus k) ((s x).theta k) ∧
        uibotGeomCoalescenceOffsets z x k = ((s x).thetaMinus k, (s x).theta k) ∧
        ∀ default : GeometricSideClass,
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1 =
            intrinsicSideSubmapClass A (L .left) (I.vertexEquiv (D.x k)) ∧
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2 =
            intrinsicSideSubmapClass A (L .right) (I.vertexEquiv (D.x k)) ∧
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).2 =
            intrinsicSideSubmapClass A C (I.vertexEquiv (D.x (k - 1))) := by
  filter_upwards [intrinsicGeodesic_sample_offsets_ae,
    uibotGeomSideSliceObservables_ae, uibotRecoveredCode_ae] with U hgeo hfactor hcode
  dsimp only at hgeo ⊢
  obtain ⟨H, h, hpast, hp, s, hclass, hall⟩ := hgeo
  refine ⟨H, h, hpast, hp, s, hclass, ?_⟩
  intro A hA
  refine ⟨(hall A hA).1, ?_⟩
  intro I x k
  have hf := (congrArg (fun f => f x k) hfactor.symm).trans
    (congrArg (fun V => uibotCodeSideSliceObservables V x k) hcode.symm)
  refine ⟨hf, ?_⟩
  have hread := intrinsicConsumers_readers_of_witness _ x (s x) hp A I k
  have hpresent := intrinsicConsumers_readers_present (s x) k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hread.2.2.2,
    (((hall A hA).2 I x).2.2 k).2.1, ?_⟩
  · exact (congrArg (fun q => q.1.1.isSome) hf).trans hpresent.1
  · exact (congrArg (fun q => q.1.2.isSome) hf).trans hpresent.2.1
  · exact (congrArg (fun q => q.2.isSome) hf).trans hpresent.2.2
  · exact (congrArg (fun q => Option.map forgetMarks q.1.1) hf).trans hread.1
  · exact (congrArg (fun q => Option.map forgetMarks q.1.2) hf).trans hread.2.1
  · exact (congrArg (fun q => Option.map forgetMarks q.2) hf).trans hread.2.2.1
  · intro default
    have hd := intrinsicConsumers_default_readers_of_witness _ x (s x) hp A I k default
    exact ⟨(congrArg (fun q => forgetMarksOptionClassValue default q.1.1) hf).trans hd.1,
      (congrArg (fun q => forgetMarksOptionClassValue default q.1.2) hf).trans hd.2.1,
      (congrArg (fun q => forgetMarksOptionClassValue default q.2) hf).trans hd.2.2⟩

private theorem intrinsicConsumers55And56_code_slice_laws
    (default : GeometricSideClass) (x : XDP) :
    iIndepFun (fun k => forgetMarksOptionClassValue default ∘
      m0CutGeodesicSliceClassOption x k) wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map
      (forgetMarksOptionClassValue default ∘ m0CutGeodesicSliceClassOption x k) =
      wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ m0CutGeodesicSliceClassOption x 1)) ∧
    (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map
      (forgetMarksOptionClassValue default ∘ m0CutGeodesicSliceClassOption x k) =
      wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ m0CutGeodesicSliceClassOption x 0)) := by
  exact lemma56_unmarked_of_sideReaders4 default x (m0CutGeodesicSliceClassOption x)
    (aemeasurable_m0CutGeodesicSliceClassOption x)
    (oneL (if x = XDP.ldp then true else false))
    (prevL (if x = XDP.ldp then true else false)) (m0Cut_ae_leftSideUpdates x)
    (oneR3 x) (nextR3 x) (m0Cut_ae_rightSideUpdates x)
    (readL4 default x) (hReadL4 default x) (readR4 default x) (hReadR4 default x)
    (readLminus4 default x) (hReadLminus4 default x)
    (readRplus4 default x) (hReadRplus4 default x)

/-- Helper toward Proposition 3.9: the sampled Borel side readers satisfy
all optional-presence, independence and same-sign law clauses of Lemma 5.5.
Their intrinsic leftmost-object interpretation remains qualified. -/
theorem intrinsicConsumers55And56_side_laws (default : GeometricSideClass)
    (x : XDP) (k : ℤ) :
    (∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      (O₅₆ U x k).1.1 = some (lemma55OptionClassValue default (O₅₆ U x k).1.1) ∧
      (O₅₆ U x k).1.2 = some (lemma55OptionClassValue default (O₅₆ U x k).1.2)) ∧
    IndepFun (fun U => forgetMarksOptionClassValue default (O₅₆ U x k).1.1)
      (fun U => forgetMarksOptionClassValue default (O₅₆ U x k).1.2)
      wholePlaneIIDCodeMeasure ∧
    (0 ≤ k → wholePlaneIIDCodeMeasure.map
      (fun U => forgetMarksOptionClassValue default (O₅₆ U x k).1.2) =
      wholePlaneIIDCodeMeasure.map
        (fun U => forgetMarksOptionClassValue default (O₅₆ U x 0).1.2)) ∧
    (k ≤ 0 → wholePlaneIIDCodeMeasure.map
      (fun U => forgetMarksOptionClassValue default (O₅₆ U x k).1.1) =
      wholePlaneIIDCodeMeasure.map
        (fun U => forgetMarksOptionClassValue default (O₅₆ U x 0).1.1)) := by
  have hL (j : ℤ) : (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x j)
      =ᵐ[wholePlaneIIDCodeMeasure]
      (fun U => forgetMarksOptionClassValue default (O₅₆ U x j).1.1) := by
    filter_upwards [intrinsicConsumers55And56_sample_eq_code] with U hU
    exact congrArg (fun f => forgetMarksOptionClassValue default (f x j).1.1) hU
  have hR (j : ℤ) : (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x j)
      =ᵐ[wholePlaneIIDCodeMeasure]
      (fun U => forgetMarksOptionClassValue default (O₅₆ U x j).1.2) := by
    filter_upwards [intrinsicConsumers55And56_sample_eq_code] with U hU
    exact congrArg (fun f => forgetMarksOptionClassValue default (f x j).1.2) hU
  have hlaw := DirectedDistances.Paper.Section5.lem_geo_infty_ind default x k
  refine ⟨?_, hlaw.2.2.1.congr (hL k) (hR k), ?_, ?_⟩
  · filter_upwards [intrinsicConsumers55And56_sample_eq_code,
      hlaw.1, hlaw.2.1] with U hU hleft hright
    rw [← hU]
    exact ⟨hleft, hright⟩
  · intro hk
    exact (Measure.map_congr (hR k)).symm.trans
      ((hlaw.2.2.2.1 hk).trans (Measure.map_congr (hR 0)))
  · intro hk
    exact (Measure.map_congr (hL k)).symm.trans
      ((hlaw.2.2.2.2 hk).trans (Measure.map_congr (hL 0)))

/-- Helper toward Proposition 3.9: the single Borel slice family is
almost surely present at every index, independent after forgetting marks,
and stationary on the two index ranges of Lemma 5.6. The class identification
with common witnesses is `intrinsicConsumers55And56_sample_classes_ae`. -/
theorem intrinsicConsumers55And56_slice_laws (default : GeometricSideClass) (x : XDP) :
    (∀ k : ℤ, Measurable (fun U => (O₅₆ U x k).2)) ∧
    (∀ᵐ U ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, ((O₅₆ U x k).2).isSome) ∧
    iIndepFun (fun k U => forgetMarksOptionClassValue default (O₅₆ U x k).2)
      wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map
      (fun U => forgetMarksOptionClassValue default (O₅₆ U x k).2) =
      wholePlaneIIDCodeMeasure.map
        (fun U => forgetMarksOptionClassValue default (O₅₆ U x 1).2)) ∧
    (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map
      (fun U => forgetMarksOptionClassValue default (O₅₆ U x k).2) =
      wholePlaneIIDCodeMeasure.map
        (fun U => forgetMarksOptionClassValue default (O₅₆ U x 0).2)) := by
  have he (j : ℤ) : (forgetMarksOptionClassValue default ∘ m0CutGeodesicSliceClassOption x j)
      =ᵐ[wholePlaneIIDCodeMeasure]
      (fun U => forgetMarksOptionClassValue default (O₅₆ U x j).2) := by
    filter_upwards [intrinsicConsumers55And56_sample_eq_code] with U hU
    exact congrArg (fun f => forgetMarksOptionClassValue default (f x j).2) hU
  have hlaw := intrinsicConsumers55And56_code_slice_laws default x
  refine ⟨?_, ?_, hlaw.1.congr he, ?_, ?_⟩
  · intro k
    exact (((measurable_pi_apply k).comp
      ((measurable_pi_apply x).comp measurable_uibotGeomSideSliceObservables)).snd).comp
        (measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)
  · filter_upwards [intrinsicConsumers55And56_sample_eq_code,
      ae_m0CutGeodesicSliceWitness x] with U hU hs
    intro k
    rw [← hU]
    exact (intrinsicConsumers_readers_present (Classical.choice hs) k).2.2
  · intro k hk
    exact (Measure.map_congr (he k)).symm.trans
      ((hlaw.2.1 k hk).trans (Measure.map_congr (he 1)))
  · intro k hk
    exact (Measure.map_congr (he k)).symm.trans
      ((hlaw.2.2 k hk).trans (Measure.map_congr (he 0)))

/- EXACT REMAINING STATEMENT WITH FULL BINDERS (comment only).

Native-region equality is now proved by
intrinsicBetween8_native_eq_closedBetween. The remaining step is simultaneous
intrinsic leftmostness and uniqueness, including identification of arbitrary
intrinsic cut-rightmost reference rays with the source reference. The code
witness uniqueness in IntrinsicConsumers55And56 is not this statement.
No theorem above assumes this obligation or a class-equality conclusion.

∀ᵐ U ∂wholePlaneIIDCodeMeasure,
  let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
  let W := uibotRecoveredCode z
  ∃ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∃ s : ∀ x : XDP, M0CutGeodesicSliceWitness W x,
  z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
  ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
    Nonempty (D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) ∧
    ∀ I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root,
    let C := intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)
    let S := intrinsicConsumersBusemannCut C
    ∀ (x : XDP) (k : ℤ),
    let longest := if x = XDP.ldp then true else false
    let P := intrinsicConsumersGeodesicOfCode W H h hpast hp A I ((s x).P k)
    IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest P ∧
    ∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
      IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P.

The completed consumer must combine this conclusion with all clauses of
intrinsicConsumers55And56_sample_classes_ae using the SAME H,h,hpast,hp,s,
and with intrinsicConsumers55And56_borel, intrinsicConsumers55And56_side_laws
and intrinsicConsumers55And56_slice_laws. This is the sole remaining
intrinsic-geodesic interpretation step for the present bounded assembly;
no removal of the intrinsic-object qualifier or numbered completion is claimed. -/

end DirectedDistances.PaperProofs.Section3
end
