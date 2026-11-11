/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumersMuAE
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers54And57Native
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers55And56Final

/-! # Intrinsic leftmost geodesics and Busemann increments under the UIBOT law

Helpers toward Proposition 3.9, transferring Lemmas 5.4–5.7 from
reconstruction transfers the representative-wide predicates without a
measurability assumption on those predicates. Cut uniqueness identifies
every intrinsic cut with the constructed one. The Lemma 5.4/5.7 conclusions
use intrinsic paths, least offsets, and the class-defined Busemann sequence.
The side/slice identification uses the class's recovered code for its
geometric realization; it has no independently sampled input.
the intrinsic-object qualifier is retained. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section7 DirectedDistances.Paper.Section4
open MeasureTheory ProbabilityTheory Filter
open scoped Classical

local instance intrinsicConsumersMuAE4MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance intrinsicConsumersMuAE4BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

local notation "μᵢ" =>
  (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
    Measure D39GeomRootedMapClass)

/-- Helper toward Proposition 3.9: Lemmas 5.4 and 5.7 hold on one UIBOT
conull event, on every intrinsic cut of every representative, in both modes.
The unique leftmost rays share all coalescence, least-offset and increment
clauses. Every normalized intrinsic Busemann sequence equals the class
selector, which itself satisfies the increment identity at every least pair. -/
theorem intrinsicConsumersMuAE4_lem54_and_lem57 :
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0},
      Quotient.mk d39DomainSetoid A = z →
      (∃! _C : IntrinsicFutureCut2 A, True) ∧
      ∀ (C : IntrinsicFutureCut2 A) (x : XDP),
        let S := intrinsicConsumerCut C
        let longest := if x = XDP.ldp then true else false
        ∃ P : ∀ k : ℤ, IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
          (∀ k : ℤ,
            IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest (P k) ∧
            ∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
              IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P k) ∧
          (∀ k k' : ℤ, ∃ a b : ℕ,
            IntrinsicEdgeTailsCoalesce (P k).val (P k').val a b) ∧
          (∃! X : ℤ → ℤ,
            if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X
            else IsIntrinsicBusemannSDP A S C.x X) ∧
          (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x
              (intrinsicConsumerSequence longest z)
            else IsIntrinsicBusemannSDP A S C.x
              (intrinsicConsumerSequence longest z)) ∧
          (∀ X : ℤ → ℤ,
            (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X
              else IsIntrinsicBusemannSDP A S C.x X) →
            X = intrinsicConsumerSequence longest z) ∧
          (∀ k : ℤ, ∃! q : ℕ × ℕ,
            IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val q.1 q.2) ∧
          (∀ X : ℤ → ℤ,
            (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X
              else IsIntrinsicBusemannSDP A S C.x X) →
            ∀ (k : ℤ) (theta thetaMinus : ℕ),
              IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val theta thetaMinus →
              X k - X (k - 1) = (theta : ℤ) - (thetaMinus : ℤ)) ∧
          ∀ (k : ℤ) (theta thetaMinus : ℕ),
            IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val theta thetaMinus →
            intrinsicConsumerSequence longest z k -
                intrinsicConsumerSequence longest z (k - 1) =
              (theta : ℤ) - (thetaMinus : ℤ) := by
  have h := intrinsicConsumersNative54And57_sample_ae
  rw [← uibotLaw135_recoveredCode_law] at h
  have hmap := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable h
  filter_upwards [hmap, uibotClassSeparation6_ae_reconstruction,
    intrinsicConsumersMuAE_cut_sequences] with z hz hrec hseq
  dsimp only at hz
  rw [hrec] at hz
  obtain ⟨H, h, hpast, hp, s, _hclass, hrep⟩ := hz
  intro A hA
  refine ⟨(hseq A hA).1, ?_⟩
  intro C x
  obtain ⟨⟨I⟩, hI⟩ := hrep A hA
  let C₀ := intrinsicFutureCut2Pushforward I
    (uibotCut2Source (uibotRecoveredCode z) H h hpast hp)
  have hC : C = C₀ := (hseq A hA).1.unique trivial trivial
  rw [hC]
  obtain ⟨hchar, huniq, hcoal, hleast, _hoff, hinc, hleft⟩ := (hI I).2 x
  let longest := if x = XDP.ldp then true else false
  let P : ∀ k : ℤ, IntrinsicInfiniteXDPGeodesic A (intrinsicConsumerCut C₀)
      (C₀.x k) longest := fun k =>
    intrinsicConsumersGeodesicOfCode (uibotRecoveredCode z) H h hpast hp A I ((s x).P k)
  have hs : (if x = XDP.ldp then
      IsIntrinsicBusemannLDP A (intrinsicConsumerCut C₀) C₀.x
        (intrinsicConsumerSequence longest z)
    else IsIntrinsicBusemannSDP A (intrinsicConsumerCut C₀) C₀.x
      (intrinsicConsumerSequence longest z)) := by
    by_cases hx : x = XDP.ldp
    · simpa only [longest, hx, ite_true] using ((hseq A hA).2 C₀).2.2.2
    · simpa only [longest, hx, ite_false] using ((hseq A hA).2 C₀).2.2.1
  refine ⟨P, hleft, hcoal, ⟨_, hchar, huniq⟩, hs, ?_, hleast, hinc, ?_⟩
  · intro X hX
    exact (huniq X hX).trans (huniq _ hs).symm
  · exact hinc _ hs

/-- Helper toward Proposition 3.9: Lemma 5.4 for every Boolean XDP mode
and every intrinsic boundary label, with uniqueness against all intrinsic
leftmost competitors and equality of geometric edge tails for every pair. -/
theorem intrinsicConsumersMuAE4_lem54 :
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0},
      Quotient.mk d39DomainSetoid A = z →
      (∃! _C : IntrinsicFutureCut2 A, True) ∧
      ∀ (C : IntrinsicFutureCut2 A) (longest : Bool),
        let S := intrinsicConsumerCut C
        ∃ P : ∀ k : ℤ, IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
          (∀ k : ℤ,
            IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest (P k) ∧
            ∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
              IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P k) ∧
          ∀ k k' : ℤ, ∃ a b : ℕ,
            IntrinsicEdgeTailsCoalesce (P k).val (P k').val a b := by
  filter_upwards [intrinsicConsumersMuAE4_lem54_and_lem57] with z hz
  intro A hA
  refine ⟨(hz A hA).1, ?_⟩
  intro C longest
  cases longest
  · obtain ⟨P, hleft, hcoal, _⟩ := (hz A hA).2 C XDP.sdp
    exact ⟨P, hleft, hcoal⟩
  · obtain ⟨P, hleft, hcoal, _⟩ := (hz A hA).2 C XDP.ldp
    exact ⟨P, hleft, hcoal⟩

/-- Helper toward Proposition 3.9: Lemma 5.7 uses the class-defined
intrinsic sequence and the uniquely least intrinsic edge offsets. It retains
all normalized sequences and all least pairs, in both modes and on every
cut of every representative, on one UIBOT conull event. -/
theorem intrinsicConsumersMuAE4_lem57 :
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0},
      Quotient.mk d39DomainSetoid A = z →
      (∃! _C : IntrinsicFutureCut2 A, True) ∧
      ∀ (C : IntrinsicFutureCut2 A) (longest : Bool),
        let S := intrinsicConsumerCut C
        ∃ P : ∀ k : ℤ, IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
          (∀ k : ℤ,
            IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest (P k) ∧
            ∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
              IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P k) ∧
          (∃! X : ℤ → ℤ, if longest then IsIntrinsicBusemannLDP A S C.x X
            else IsIntrinsicBusemannSDP A S C.x X) ∧
          (if longest then IsIntrinsicBusemannLDP A S C.x
              (intrinsicConsumerSequence longest z)
            else IsIntrinsicBusemannSDP A S C.x
              (intrinsicConsumerSequence longest z)) ∧
          (∀ X : ℤ → ℤ,
            (if longest then IsIntrinsicBusemannLDP A S C.x X
              else IsIntrinsicBusemannSDP A S C.x X) →
            X = intrinsicConsumerSequence longest z) ∧
          (∀ k : ℤ, ∃! q : ℕ × ℕ,
            IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val q.1 q.2) ∧
          (∀ X : ℤ → ℤ,
            (if longest then IsIntrinsicBusemannLDP A S C.x X
              else IsIntrinsicBusemannSDP A S C.x X) →
            ∀ (k : ℤ) (theta thetaMinus : ℕ),
              IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val theta thetaMinus →
              X k - X (k - 1) = (theta : ℤ) - (thetaMinus : ℤ)) ∧
          ∀ (k : ℤ) (theta thetaMinus : ℕ),
            IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val theta thetaMinus →
            intrinsicConsumerSequence longest z k -
                intrinsicConsumerSequence longest z (k - 1) =
              (theta : ℤ) - (thetaMinus : ℤ) := by
  filter_upwards [intrinsicConsumersMuAE4_lem54_and_lem57] with z hz
  intro A hA
  refine ⟨(hz A hA).1, ?_⟩
  intro C longest
  cases longest
  · obtain ⟨P, hleft, _hcoal, hex, hs, huniq, hleast, hinc, hseq⟩ :=
      (hz A hA).2 C XDP.sdp
    exact ⟨P, hleft, hex, hs, huniq, hleast, hinc, hseq⟩
  · obtain ⟨P, hleft, _hcoal, hex, hs, huniq, hleast, hinc, hseq⟩ :=
      (hz A hA).2 C XDP.ldp
    exact ⟨P, hleft, hex, hs, huniq, hleast, hinc, hseq⟩

/-- Helper toward Proposition 3.9: the fixed side and slice readers
under the UIBOT law identify native submaps of the unique intrinsic cut.
All representatives, all source isomorphisms of the class's recovered code,
both modes and all labels share the same witnesses. Leftmost uniqueness,
least offsets, presence and every default-independent unmarked class are
included. The code here is recovered from the class, never sampled separately. -/
theorem intrinsicConsumersMuAE4_lem55_lem56_geometry :
    ∀ᵐ z ∂μᵢ,
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
        (∃! _C : IntrinsicFutureCut2 A, True) ∧
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root) ∧
        ∀ I : D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root,
        let C := intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)
        let S := intrinsicConsumersBusemannCut C
        (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
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
  have h := intrinsicConsumers55And56Final_complete.2.2.2
  rw [← uibotLaw135_recoveredCode_law] at h
  have hmap := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable h
  filter_upwards [hmap, uibotClassSeparation6_ae_reconstruction,
    intrinsicConsumersMuAE_unique_cut] with z hz hrec hcut
  dsimp only at hz ⊢
  rw [hrec] at hz
  obtain ⟨H, h, hpast, hp, s, hclass, hrep⟩ := hz
  refine ⟨H, h, hpast, hp, s, hclass, ?_⟩
  intro A hA
  refine ⟨hcut A hA, (hrep A hA).1, ?_⟩
  intro I
  exact ⟨fun _ => (hcut A hA).unique trivial trivial, (hrep A hA).2 I⟩

/-- Helper toward Proposition 3.9: Lemma 5.5's unmarked side laws under
the UIBOT law. Both readers are present, independent, and stationary on
their respective closed half-index ranges, for every mode and default.
Their intrinsic interpretation is given by the common geometry theorem. -/
theorem intrinsicConsumersMuAE4_lem55 (default : GeometricSideClass)
    (x : XDP) (k : ℤ) :
    ((fun z => (uibotGeomSideSliceObservables z x k).1.1) =ᵐ[μᵢ]
      fun z => some (lemma55OptionClassValue default
        (uibotGeomSideSliceObservables z x k).1.1)) ∧
    ((fun z => (uibotGeomSideSliceObservables z x k).1.2) =ᵐ[μᵢ]
      fun z => some (lemma55OptionClassValue default
        (uibotGeomSideSliceObservables z x k).1.2)) ∧
    IndepFun
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1)
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2)
      μᵢ ∧
    (0 ≤ k → (μᵢ).map
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2) =
      (μᵢ).map
        (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x 0).1.2)) ∧
    (k ≤ 0 → (μᵢ).map
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1) =
      (μᵢ).map
        (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x 0).1.1)) :=
  uibotLaw135_geo_infty_ind default x k

private theorem intrinsicConsumersMuAE4_side_slice_readers :
    ∀ᵐ z ∂μᵢ, uibotGeomSideSliceObservables z =
      uibotCodeSideSliceObservables (uibotRecoveredCode z) := by
  have h := uibotGeomSideSliceObservables_ae
  rw [← uibotLaw135_recoveredCode_law] at h
  have hmap := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable h
  filter_upwards [hmap, uibotClassSeparation6_ae_reconstruction] with z hz hrec
  change uibotCodeSideSliceObservables (uibotRecoveredCode z) =
    uibotGeomSideSliceObservables
      (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
        (uibotRecoveredCode z)) at hz
  rw [hrec] at hz
  exact hz.symm

/-- Helper toward Proposition 3.9: Lemma 5.6 for the fixed intrinsic
slice reader under the UIBOT law. The slices are measurable, simultaneously
present, jointly independent after forgetting marks, and stationary
separately on indices at least one and at most zero. Their native geometric
identification uses the unique leftmost paths and least offsets above. -/
theorem intrinsicConsumersMuAE4_lem56 (default : GeometricSideClass) (x : XDP) :
    (∀ k : ℤ, Measurable (fun z : D39GeomRootedMapClass.{0} =>
      (uibotGeomSideSliceObservables z x k).2)) ∧
    (∀ᵐ z ∂μᵢ, ∀ k : ℤ, (uibotGeomSideSliceObservables z x k).2.isSome) ∧
    iIndepFun (fun k z =>
      forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).2) μᵢ ∧
    (∀ k : ℤ, 1 ≤ k → (μᵢ).map
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).2) =
      (μᵢ).map
        (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x 1).2)) ∧
    (∀ k : ℤ, k ≤ 0 → (μᵢ).map
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).2) =
      (μᵢ).map
        (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x 0).2)) := by
  obtain ⟨Phi, _, hpres, hw, hind, hpos, hneg⟩ := uibotLaw135_geo_slice default x
  have heq : ∀ k : ℤ, Phi k =ᵐ[μᵢ]
      (fun z => (uibotGeomSideSliceObservables z x k).2) := by
    intro k
    filter_upwards [hw, intrinsicConsumersMuAE4_side_slice_readers] with z hz hr
    obtain ⟨H, h, hLL, hpast, T, P, hleft, huniq, hvals⟩ := hz
    choose a b hab hPhi using hvals
    let s : M0CutGeodesicSliceWitness (uibotRecoveredCode z) x :=
      ⟨H, h, hLL, hpast, T, P, hleft, huniq, a, b, hab⟩
    rw [hr]
    exact (hPhi k).trans (intrinsicConsumers_slice_reader_of_witness s k).symm
  have heq' : ∀ k : ℤ, (forgetMarksOptionClassValue default ∘ Phi k) =ᵐ[μᵢ]
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).2) :=
    fun k => (heq k).fun_comp (forgetMarksOptionClassValue default)
  refine ⟨?_, ?_, hind.congr heq', ?_, ?_⟩
  · intro k
    exact ((measurable_pi_apply k).comp
      ((measurable_pi_apply x).comp measurable_uibotGeomSideSliceObservables)).snd
  · filter_upwards [ae_all_iff.mpr hpres, ae_all_iff.mpr heq] with z hz he
    intro k
    rw [← he k]
    exact hz k
  · intro k hk
    exact (Measure.map_congr (heq' k)).symm.trans
      ((hpos k hk).trans (Measure.map_congr (heq' 1)))
  · intro k hk
    exact (Measure.map_congr (heq' k)).symm.trans
      ((hneg k hk).trans (Measure.map_congr (heq' 0)))

end DirectedDistances.PaperProofs.Section3
end
