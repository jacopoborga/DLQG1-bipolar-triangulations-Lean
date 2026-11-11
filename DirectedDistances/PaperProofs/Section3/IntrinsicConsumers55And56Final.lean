/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers55And56Complete
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers54And57Native

/-! # Intrinsic side and slice consumers of Lemmas 5.5 and 5.6

give unique intrinsic leftmost geodesics, native side and slice classes,
and least coalescence offsets in every representative and under every source
isomorphism. The Borel readers have the installed anchors' unmarked laws.
No intrinsic-object qualifier is removed and no numbered completion is claimed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5 DirectedDistances.Paper.Section4
open MeasureTheory ProbabilityTheory Filter
open scoped Classical

local instance intrinsicConsumers55And56FinalMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance intrinsicConsumers55And56FinalBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

local notation "F₅₆ᶠ" =>
  uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
local notation "O₅₆ᶠ" => fun U : ℤ → Fin 3 => uibotGeomSideSliceObservables (F₅₆ᶠ U)

/-- Helper toward Proposition 3.9: the exact remaining common-event
leftmostness and uniqueness statement from the side and slice assembly.
All representatives and all source isomorphisms share one witness family. -/
theorem intrinsicConsumers55And56Final_leftmost_ae :
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := F₅₆ᶠ U
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
          IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P := by
  filter_upwards [intrinsicConsumersNative54And57_sample_ae] with U hU
  dsimp only at hU ⊢
  obtain ⟨H, h, hpast, hp, s, hclass, hrep⟩ := hU
  refine ⟨H, h, hpast, hp, s, hclass, ?_⟩
  intro A hA
  refine ⟨(hrep A hA).1, ?_⟩
  intro I x k
  exact (((hrep A hA).2 I).2 x).2.2.2.2.2.2 k

/-- Helper toward Proposition 3.9: the complete Borel reader laws of
Lemmas 5.5 and 5.6, together with one iid conull event identifying all three
readers with native submaps determined by unique intrinsic leftmost geodesics.
Both modes, every index, every representative, every isomorphism, every default
and all least offsets use the same source witnesses. -/
theorem intrinsicConsumers55And56Final_complete :
    Measurable (fun z : D39GeomRootedMapClass.{0} =>
      (uibotGeomSideSliceObservables z, uibotGeomCoalescenceOffsets z)) ∧
    (∀ (default : GeometricSideClass) (x : XDP) (k : ℤ),
      (∀ᵐ U ∂wholePlaneIIDCodeMeasure,
        (O₅₆ᶠ U x k).1.1 = some (lemma55OptionClassValue default (O₅₆ᶠ U x k).1.1) ∧
        (O₅₆ᶠ U x k).1.2 = some (lemma55OptionClassValue default (O₅₆ᶠ U x k).1.2)) ∧
      IndepFun (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x k).1.1)
        (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x k).1.2)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map
        (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x k).1.2) =
        wholePlaneIIDCodeMeasure.map
          (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x 0).1.2)) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x k).1.1) =
        wholePlaneIIDCodeMeasure.map
          (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x 0).1.1))) ∧
    (∀ (default : GeometricSideClass) (x : XDP),
      (∀ k : ℤ, Measurable (fun U => (O₅₆ᶠ U x k).2)) ∧
      (∀ᵐ U ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, ((O₅₆ᶠ U x k).2).isSome) ∧
      iIndepFun (fun k U => forgetMarksOptionClassValue default (O₅₆ᶠ U x k).2)
        wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map
        (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x k).2) =
        wholePlaneIIDCodeMeasure.map
          (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x 1).2)) ∧
      (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x k).2) =
        wholePlaneIIDCodeMeasure.map
          (fun U => forgetMarksOptionClassValue default (O₅₆ᶠ U x 0).2))) ∧
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := F₅₆ᶠ U
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
        let C := intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)
        let S := intrinsicConsumersBusemannCut C
        (∀ k, C.x k = I.vertexEquiv (D.x k)) ∧
        ∀ (x : XDP) (k : ℤ),
        let longest := if x = XDP.ldp then true else false
        let P : ∀ j : ℤ, IntrinsicInfiniteXDPGeodesic A S (C.x j) longest :=
          fun j => intrinsicConsumersGeodesicOfCode W H h hpast hp A I ((s x).P j)
        let L := fun t => intrinsicGeodesicSide A S
          (I.h '' m0GeodesicAmbientRegion W H h) (C.x (k - 1))
          (fun n => ((P k).val.edge n).val) t
        let B := intrinsicGeodesicSlice A S
          (I.h '' m0GeodesicAmbientRegion W H h) C.x
          (fun j n => (P j).val.vertex n) (fun j n => ((P j).val.edge n).val)
          k ((s x).thetaMinus k) ((s x).theta k)
          (I.edgeEquiv (wholePlaneEdgeι W 0
            (boundaryOuterEdge (shiftedStream W 0) h (k - 1))))
        IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest (P k) ∧
        (∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
          IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P k) ∧
        uibotGeomSideSliceObservables z x k = uibotCodeSideSliceObservables W x k ∧
        ((uibotGeomSideSliceObservables z x k).1.1).isSome ∧
        ((uibotGeomSideSliceObservables z x k).1.2).isSome ∧
        ((uibotGeomSideSliceObservables z x k).2).isSome ∧
        (uibotGeomSideSliceObservables z x k).2 = some (geometricSideClass
          (m0CutGeodesicSlice (hp := hpast) (s x).P k
            ((s x).thetaMinus k) ((s x).theta k) ((s x).least k))) ∧
        Option.map forgetMarks (uibotGeomSideSliceObservables z x k).1.1 =
          some (intrinsicSideSubmapClass A (L .left) (I.vertexEquiv (D.x k))) ∧
        Option.map forgetMarks (uibotGeomSideSliceObservables z x k).1.2 =
          some (intrinsicSideSubmapClass A (L .right) (I.vertexEquiv (D.x k))) ∧
        Option.map forgetMarks (uibotGeomSideSliceObservables z x k).2 =
          some (intrinsicSideSubmapClass A B (I.vertexEquiv (D.x (k - 1)))) ∧
        IntrinsicLeastEdgeCoalescence (P (k - 1)).val (P k).val
          ((s x).thetaMinus k) ((s x).theta k) ∧
        uibotGeomCoalescenceOffsets z x k = ((s x).thetaMinus k, (s x).theta k) ∧
        ∀ default : GeometricSideClass,
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1 =
            intrinsicSideSubmapClass A (L .left) (I.vertexEquiv (D.x k)) ∧
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2 =
            intrinsicSideSubmapClass A (L .right) (I.vertexEquiv (D.x k)) ∧
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).2 =
            intrinsicSideSubmapClass A B (I.vertexEquiv (D.x (k - 1))) := by
  refine ⟨intrinsicConsumers55And56_borel, intrinsicConsumers55And56_side_laws,
    intrinsicConsumers55And56_slice_laws, ?_⟩
  filter_upwards [intrinsicConsumersNative54And57_sample_ae,
    uibotGeomSideSliceObservables_ae, uibotRecoveredCode_ae] with U hgeo hfactor hcode
  dsimp only at hgeo ⊢
  obtain ⟨H, h, hpast, hp, s, hclass, hrep⟩ := hgeo
  refine ⟨H, h, hpast, hp, s, hclass, ?_⟩
  intro A hA
  refine ⟨(hrep A hA).1, ?_⟩
  intro I
  refine ⟨((hrep A hA).2 I).1, ?_⟩
  intro x k
  obtain ⟨_, _, _, _, hoff, _, hleft⟩ := ((hrep A hA).2 I).2 x
  have hf := (congrArg (fun f => f x k) hfactor.symm).trans
    (congrArg (fun V => uibotCodeSideSliceObservables V x k) hcode.symm)
  have hread := intrinsicConsumers_readers_of_witness _ x (s x) hp A I k
  rw [intrinsicGeodesicSliceOfCode_eq_intrinsic] at hread
  have hpresent := intrinsicConsumers_readers_present (s x) k
  have hmarked := intrinsicConsumers_slice_reader_of_witness (s x) k
  refine ⟨(hleft k).1, (hleft k).2, hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hread.2.2.2, (hoff k).2.1, ?_⟩
  · exact (congrArg (fun q => q.1.1.isSome) hf).trans hpresent.1
  · exact (congrArg (fun q => q.1.2.isSome) hf).trans hpresent.2.1
  · exact (congrArg (fun q => q.2.isSome) hf).trans hpresent.2.2
  · exact (congrArg (fun q => q.2) hf).trans hmarked
  · exact (congrArg (fun q => Option.map forgetMarks q.1.1) hf).trans hread.1
  · exact (congrArg (fun q => Option.map forgetMarks q.1.2) hf).trans hread.2.1
  · exact (congrArg (fun q => Option.map forgetMarks q.2) hf).trans hread.2.2.1
  · intro default
    have hd := intrinsicConsumers_default_readers_of_witness _ x (s x) hp A I k default
    rw [intrinsicGeodesicSliceOfCode_eq_intrinsic] at hd
    exact ⟨(congrArg (fun q => forgetMarksOptionClassValue default q.1.1) hf).trans hd.1,
      (congrArg (fun q => forgetMarksOptionClassValue default q.1.2) hf).trans hd.2.1,
      (congrArg (fun q => forgetMarksOptionClassValue default q.2) hf).trans hd.2.2⟩

end DirectedDistances.PaperProofs.Section3
end
