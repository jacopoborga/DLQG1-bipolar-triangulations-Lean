/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart7
public import DirectedDistances.PaperProofs.Section1.ScalingPathMarginalsIdentified
public import DirectedDistances.KMSW.FutureMapHatLawShift
public import DirectedDistances.PaperProofs.Section5.DirectedContainIdentified
public import DirectedDistances.PaperProofs.Section5.FutureMapLawIdentified
public import DirectedDistances.KMSW.KMSWMeasurability
public import DirectedDistances.PaperProofs.Section5.GeoSliceOneSliceReaderFixed2
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55SourceClosure










public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section7 DirectedDistances.Paper.Section4
open MeasureTheory Filter

local instance uibotCodeRecoveryPart8MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotCodeRecoveryPart8BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
local instance uibotCodeRecoveryPart8XDPFintype : Fintype XDP :=
  Fintype.ofList [.ldp, .sdp] (by intro x; cases x <;> simp)

/-- Helper toward Proposition 3.9: the full pair of identified Busemann
sequences together with every positive-scale whole-line path. -/
@[expose] def uibotCodeBusemannObservables (W : ℤ → Fin 3) :
    ((ℤ → ℤ) × (ℤ → ℤ)) × (ℕ → WholeLineCadlag × WholeLineCadlag) :=
  ((identifiedLDPBusemann W, identifiedSDPBusemann W),
    fun n => (identifiedLDPScalingPath n W, identifiedSDPScalingPath n W))

/-- Helper toward Proposition 3.9: the complete Busemann/path tuple is
a.e. measurable in the existing whole-line local-J1 output space. -/
theorem aemeasurable_uibotCodeBusemannObservables :
    AEMeasurable uibotCodeBusemannObservables wholePlaneIIDCodeMeasure :=
  (aemeasurable_identifiedLDPBusemann.prodMk aemeasurable_identifiedSDPBusemann).prodMk
    (aemeasurable_pi_iff.mpr fun n =>
      (aemeasurable_identifiedLDPScalingPath n).prodMk
        (aemeasurable_identifiedSDPScalingPath n))

/-- Helper toward Proposition 3.9: one Borel geometric observable for
both Busemann sequences and all their full-path rescalings. -/
@[expose] def uibotGeomBusemannObservables : D39GeomRootedMapClass.{0} →
    ((ℤ → ℤ) × (ℤ → ℤ)) × (ℕ → WholeLineCadlag × WholeLineCadlag) :=
  uibotRecoveredObservable uibotCodeBusemannObservables
    aemeasurable_uibotCodeBusemannObservables

/-- Helper toward Proposition 3.9: the joint Busemann and whole-path
factor is Borel measurable. -/
theorem measurable_uibotGeomBusemannObservables :
    Measurable uibotGeomBusemannObservables :=
  measurable_uibotRecoveredObservable _ _

/-- Helper toward Proposition 3.9: simultaneous factorization of both
entire Busemann functions and all whole-line local-J1 paths. -/
theorem uibotGeomBusemannObservables_ae :
    uibotCodeBusemannObservables =ᵐ[wholePlaneIIDCodeMeasure]
      uibotGeomBusemannObservables ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
  uibotRecoveredObservable_ae _ _

/-- Helper toward Proposition 3.9: the Borel Busemann pair has the full
eventual-distance characterization on one common cut, with shared witnesses.
This supports Theorems 1.4 and 1.6–1.8 and Lemmas 7.1, 7.3, 7.5, 7.7. -/
theorem uibotGeomBusemannObservables_ae_characterization :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))),
        let B := uibotGeomBusemannObservables (uibotMeasurableWholePlaneClassMap
          uibotDeterministicComparison_proved W)
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) B.1.1 ∧
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) B.1.2 ∧
        ∀ n : ℕ, B.2 n = (identifiedLDPScalingPath n W, identifiedSDPScalingPath n W) := by
  filter_upwards [m0Cut_busemann_identified_ae,
    identifiedLDPBusemann_characterization_ae, identifiedSDPBusemann_characterization_ae,
    uibotGeomBusemannObservables_ae] with W hex hL hS heq
  obtain ⟨H, h, hLL, _⟩ := hex
  refine ⟨H, h, hLL, ?_⟩
  change uibotCodeBusemannObservables W = uibotGeomBusemannObservables _ at heq
  rw [← heq]
  exact ⟨hL H h hLL, hS H h hLL, fun _ => rfl⟩

/-- Helper toward Proposition 3.9: at every integer shift retain both
literal hatted/primed generating codes and the boundary-stopped future code. -/
@[expose] def uibotCodeFutureObservables (W : ℤ → Fin 3) (n : ℤ) :
    ((ℕ → Fin 3) × (ℕ → Fin 3)) × (ℕ → Fin 3) :=
  ((hatLawCodes (futureMapShiftedCodePath n W),
    hatLawPrimedCodes (futureMapShiftedCodePath n W)), boundaryFutureCode n W)

/-- Helper toward Proposition 3.9: joint measurability of all future
generating words uses their proved code laws, including stopped codes. -/
theorem aemeasurable_uibotCodeFutureObservables :
    AEMeasurable uibotCodeFutureObservables wholePlaneIIDCodeMeasure := by
  apply aemeasurable_pi_iff.mpr
  intro n
  exact ((aemeasurable_futureMapShiftedHatCodes n).1.prodMk
    (aemeasurable_futureMapShiftedHatCodes n).2).prodMk
      (measurable_boundaryFutureCode n).aemeasurable

/-- Helper toward Proposition 3.9: the simultaneous geometric Borel
factor for the literal code observations of Proposition 5.1 and Lemma 5.2. -/
@[expose] def uibotGeomFutureObservables : D39GeomRootedMapClass.{0} → ℤ →
    ((ℕ → Fin 3) × (ℕ → Fin 3)) × (ℕ → Fin 3) :=
  uibotRecoveredObservable uibotCodeFutureObservables
    aemeasurable_uibotCodeFutureObservables

/-- Helper toward Proposition 3.9: all geometric future-code coordinates
form a single Borel observable. -/
theorem measurable_uibotGeomFutureObservables :
    Measurable uibotGeomFutureObservables := measurable_uibotRecoveredObservable _ _

/-- Helper toward Proposition 3.9: both shifted generating codes and
every boundary-stopped code are recovered on one common event. -/
theorem uibotGeomFutureObservables_ae :
    uibotCodeFutureObservables =ᵐ[wholePlaneIIDCodeMeasure]
      uibotGeomFutureObservables ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
  uibotRecoveredObservable_ae _ _

/-- Helper toward Proposition 3.9: the recovered hatted and primed words
identify their actual rooted maps at every shift, with the same witnesses.
The primed clause retains its missing, unoriented root convention. -/
theorem uibotGeomFutureObservables_ae_rootedMaps :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      let Y := uibotGeomFutureObservables (uibotMeasurableWholePlaneClassMap
        uibotDeterministicComparison_proved W) n
      u = shiftedStream (fun k => W (k + n)) 0 ∧
        ∃ (h : HasFlowLineHits u) (hfin_hat : hatLimitFiniteIncidence u)
          (hfin_primed : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
          Y.1.1 = hatCodes u h ∧
          Y.1.2 = primedCode (primedSimInput u) h ∧
          hatRootedMapClause u h hfin_hat ∧ primedRootedMapClause u h hfin_primed hb := by
  filter_upwards [uibotGeomFutureObservables_ae, prop51_holds.2.2] with W heq hW
  intro n
  have heqn := congrFun heq n
  change uibotCodeFutureObservables W n = uibotGeomFutureObservables _ n at heqn
  dsimp only
  rw [← heqn]
  exact hW n

private theorem measurable_boundaryCodeTime_recovery (k : ℤ) :
    Measurable (boundaryCodeTime k) := by
  unfold boundaryCodeTime
  by_cases hk0 : k = 0
  · simp only [hk0, ite_true]
    exact measurable_const
  · simp only [hk0, ite_false]
    by_cases hk : 0 < k
    · simp only [hk, ite_true]
      exact (measurable_of_countable ENat.toNat).comp (measurable_codeSndFirstHit (-k))
    · simp only [hk, ite_false]
      exact (measurable_of_countable ENat.toNat).comp (measurable_codeFstFirstHit k)

/-- Helper toward Proposition 3.9: the common source boundary hitting
times, read from the recovered code using the established total representative. -/
@[expose] def uibotGeomBoundaryTimes (z : D39GeomRootedMapClass.{0}) (k : ℤ) : ℕ :=
  boundaryCodeTime k (shiftedCodePath (uibotRecoveredCode z) 0)

/-- Helper toward Proposition 3.9: all boundary hitting times constitute
one Borel geometric observable. -/
theorem measurable_uibotGeomBoundaryTimes : Measurable uibotGeomBoundaryTimes := by
  apply measurable_pi_iff.mpr
  intro k
  exact (measurable_boundaryCodeTime_recovery k).comp
    ((measurable_shiftedCodePath 0).comp measurable_uibotRecoveredCode)

/-- Helper toward Proposition 3.9: on one event all recovered stopping
times and stopped words have their literal source values, for every common
boundary witness. This retains the stopped-run information in Lemmas 5.2 and 7.1. -/
theorem uibotGeomBoundaryTimes_ae_stoppedWords :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ h : BoundaryHitWitnesses (shiftedStream W 0), ∀ k : ℤ,
        let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
        uibotGeomBoundaryTimes z k = boundaryHitTime (shiftedStream W 0) h k ∧
        (fun i => (uibotGeomFutureObservables z k).2 (i + 1)) =
          (fun i => shiftedStream W 0 (uibotGeomBoundaryTimes z k + i)) := by
  filter_upwards [uibotRecoveredCode_ae, uibotGeomFutureObservables_ae] with W hcode hfuture
  intro h k
  have hω : BoundaryHitWitnesses (fun i => shiftedCodePath W 0 (i + 1)) := by
    rw [shiftedCodePath_tail_eq]
    exact h
  have ht : boundaryCodeTime k (shiftedCodePath W 0) =
      boundaryHitTime (shiftedStream W 0) h k := by
    simpa only [shiftedCodePath_tail_eq] using
      boundaryCodeTime_eq_boundaryHitTime (shiftedCodePath W 0) hω k
  have ht' : uibotGeomBoundaryTimes (uibotMeasurableWholePlaneClassMap
      uibotDeterministicComparison_proved W) k = boundaryHitTime (shiftedStream W 0) h k := by
    unfold uibotGeomBoundaryTimes
    rw [hcode]
    exact ht
  refine ⟨ht', ?_⟩
  have hf := congrArg (fun y => (y k).2) hfuture.symm
  change (uibotGeomFutureObservables (uibotMeasurableWholePlaneClassMap
    uibotDeterministicComparison_proved W) k).2 = boundaryFutureCode k W at hf
  rw [hf, ht']
  exact boundaryFutureCode_tail W h k

private theorem aemeasurable_rightSide_all (x : XDP) (k : ℤ) :
    AEMeasurable (lemma55RightSideClassOption2 x k) wholePlaneIIDCodeMeasure := by
  by_cases hk : 0 ≤ k
  · exact aemeasurable_lemma55RightSideClassOption2_nonnegative x k hk
  · have hk' : k ≤ 0 := le_of_not_ge hk
    exact (aemeasurable_decodeRMinus_rightSideObsNonpos_classOption x k hk').congr
      (lemma55RightSideClassOption2_ae_eq_RMinusSidePresentation_classOption x k hk').symm

/-- Helper toward Proposition 3.9: both optional marked side classes and
the actual optional slice class, simultaneously for both metrics and all labels. -/
@[expose] def uibotCodeSideSliceObservables (W : ℤ → Fin 3) (x : XDP) (k : ℤ) :
    (Option GeometricSideClass × Option GeometricSideClass) × Option GeometricSideClass :=
  ((lemma55LeftSideClassOption x k W, lemma55RightSideClassOption2 x k W),
    m0CutGeodesicSliceClassOption x k W)

/-- Helper toward Proposition 3.9: both modes of the complete side/slice
family are a.e. measurable, using the proved actual-slice measurability. -/
theorem aemeasurable_uibotCodeSideSliceObservables :
    AEMeasurable uibotCodeSideSliceObservables wholePlaneIIDCodeMeasure := by
  apply aemeasurable_pi_iff.mpr
  intro x
  apply aemeasurable_pi_iff.mpr
  intro k
  exact ((aemeasurable_lemma55LeftSideClassOption_all x k).prodMk
    (aemeasurable_rightSide_all x k)).prodMk
      (aemeasurable_m0CutGeodesicSliceClassOption x k)

/-- Helper toward Proposition 3.9: the Borel joint side/slice observable
retains optional values and the complete existing geometric class marks. -/
@[expose] def uibotGeomSideSliceObservables : D39GeomRootedMapClass.{0} → XDP → ℤ →
    (Option GeometricSideClass × Option GeometricSideClass) × Option GeometricSideClass :=
  uibotRecoveredObservable uibotCodeSideSliceObservables
    aemeasurable_uibotCodeSideSliceObservables

/-- Helper toward Proposition 3.9: Borel measurability of the complete
side/slice factor, before either metric or boundary label is selected. -/
theorem measurable_uibotGeomSideSliceObservables :
    Measurable uibotGeomSideSliceObservables := measurable_uibotRecoveredObservable _ _

/-- Helper toward Proposition 3.9: Lemmas 5.5 and 5.6 side/slice
observables descend simultaneously, including every optional value. -/
theorem uibotGeomSideSliceObservables_ae :
    uibotCodeSideSliceObservables =ᵐ[wholePlaneIIDCodeMeasure]
      uibotGeomSideSliceObservables ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
  uibotRecoveredObservable_ae _ _

/-- Helper toward Proposition 3.9: the slice factor has a single source
geodesic witness per mode, before all boundary indices. The witness retains
the shared cut, leftmost characterization and least edge-coalescence offsets. -/
theorem uibotGeomSideSliceObservables_ae_slice_characterization :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ x : XDP,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ k : ℤ,
        (uibotGeomSideSliceObservables (uibotMeasurableWholePlaneClassMap
          uibotDeterministicComparison_proved W) x k).2 =
          some (geometricSideClass (m0CutGeodesicSlice (hp := s.hp) s.P k
            (s.thetaMinus k) (s.theta k) (s.least k))) := by
  filter_upwards [uibotGeomSideSliceObservables_ae,
    ae_all_iff.mpr ae_m0CutGeodesicSliceWitness] with W heq hw
  intro x
  let s := Classical.choice (hw x)
  refine ⟨s, ?_⟩
  intro k
  have h := congrArg (fun z => (z x k).2) heq
  change m0CutGeodesicSliceClassOption x k W = _ at h
  exact h.symm.trans (dite_eq_left (hw x))

/-- Helper toward Proposition 3.9: one event carries code recovery and
every concrete factor above. Any dependent predicate keeps all its shared
witnesses on this event, and all full-path and integer-family equalities hold. -/
theorem uibotRecovery_joint_observables_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
      uibotRecoveredCode z = W ∧
      uibotGeomBusemannObservables z = uibotCodeBusemannObservables W ∧
      uibotGeomFutureObservables z = uibotCodeFutureObservables W ∧
      uibotGeomSideSliceObservables z = uibotCodeSideSliceObservables W ∧
      uibotGeomBoundaryTimes z = (fun k => boundaryCodeTime k (shiftedCodePath W 0)) := by
  filter_upwards [uibotRecoveredCode_ae, uibotGeomBusemannObservables_ae,
    uibotGeomFutureObservables_ae, uibotGeomSideSliceObservables_ae] with W hC hB hF hS
  refine ⟨hC, hB.symm, hF.symm, hS.symm, ?_⟩
  funext k
  unfold uibotGeomBoundaryTimes
  rw [hC]

section LocalLimit

variable (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
  (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
  (hsize : ∀ k, 1 ≤ ns k)
  (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))

/-- Helper toward Proposition 3.9: the entire joint law of all concrete
consumer factors is the code law, preserving all cross-observable dependence. -/
theorem uibotGeomConsumerObservables_localLimit_law :
    (uibotGeometricLocalLimitProbabilityLaw uibotDeterministicComparison_proved
      ℓ ρ hℓ hρ ns hns hsize hne : Measure D39GeomRootedMapClass.{0}).map
      (fun z => (uibotGeomBusemannObservables z,
        uibotGeomFutureObservables z, uibotGeomSideSliceObservables z, uibotGeomBoundaryTimes z)) =
      wholePlaneIIDCodeMeasure.map (fun W => (uibotCodeBusemannObservables W,
        uibotCodeFutureObservables W, uibotCodeSideSliceObservables W,
        fun k => boundaryCodeTime k (shiftedCodePath W 0))) := by
  rw [uibotGeometricLocalLimitProbabilityLaw_map _ _ _ _ _ _ _ _ _ _
    (measurable_uibotGeomBusemannObservables.prodMk
      (measurable_uibotGeomFutureObservables.prodMk
        (measurable_uibotGeomSideSliceObservables.prodMk measurable_uibotGeomBoundaryTimes)))]
  apply Measure.map_congr
  filter_upwards [uibotRecovery_joint_observables_ae] with W hW
  exact Prod.ext hW.2.1 (Prod.ext hW.2.2.1 (Prod.ext hW.2.2.2.1 hW.2.2.2.2))

/-- Helper toward Proposition 3.9: every integer-window event of either
full Borel Busemann sequence has exactly its original code probability. -/
theorem uibotGeomBusemannObservables_window_probability
    (longest : Bool) (k : ℕ) (A p : ℝ) :
    (uibotGeometricLocalLimitProbabilityLaw uibotDeterministicComparison_proved
      ℓ ρ hℓ hρ ns hns hsize hne : Measure D39GeomRootedMapClass.{0}).real
      {z | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |((if longest then (uibotGeomBusemannObservables z).1.1
          else (uibotGeomBusemannObservables z).1.2) l : ℝ)| ≤ A * (k : ℝ) ^ p} =
      wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |((if longest then identifiedLDPBusemann W
          else identifiedSDPBusemann W) l : ℝ)| ≤ A * (k : ℝ) ^ p} := by
  have hm : Measurable (fun z => if longest then (uibotGeomBusemannObservables z).1.1
      else (uibotGeomBusemannObservables z).1.2) := by
    cases longest
    · exact measurable_uibotGeomBusemannObservables.fst.snd
    · exact measurable_uibotGeomBusemannObservables.fst.fst
  have hs : MeasurableSet {z | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then (uibotGeomBusemannObservables z).1.1
        else (uibotGeomBusemannObservables z).1.2) l : ℝ)| ≤ A * (k : ℝ) ^ p} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro l
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((measurable_of_countable (fun j : ℤ => |(j : ℝ)|)).comp
      ((measurable_pi_apply l).comp hm)) measurable_const
  rw [uibotGeometricLocalLimitProbabilityLaw_toMeasure_eq,
    map_measureReal_apply (measurable_uibotMeasurableWholePlaneClassMap _) hs]
  apply measureReal_congr
  filter_upwards [uibotGeomBusemannObservables_ae] with W hW
  have heq := congrArg Prod.fst hW.symm
  change (uibotGeomBusemannObservables (uibotMeasurableWholePlaneClassMap
    uibotDeterministicComparison_proved W)).1 =
      (identifiedLDPBusemann W, identifiedSDPBusemann W) at heq
  change (∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then (uibotGeomBusemannObservables
        (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W)).1.1
        else (uibotGeomBusemannObservables
          (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W)).1.2) l : ℝ)|
        ≤ A * (k : ℝ) ^ p) = _
  rw [heq]

/-- Helper toward Proposition 3.9: the geometric Borel LDP process obeys
Lemma 7.3's window bound with one constant chosen before every size and level. -/
theorem uibotGeomBusemannObservables_ldp_fluctuation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        (uibotGeometricLocalLimitProbabilityLaw uibotDeterministicComparison_proved
          ℓ ρ hℓ hρ ns hns hsize hne : Measure D39GeomRootedMapClass.{0}).real
          {z | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
            |((uibotGeomBusemannObservables z).1.1 l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  obtain ⟨C, hC, hbound⟩ := lem_ldp_fluctuation_identified
  refine ⟨C, hC, ?_⟩
  intro k A hA
  have heq := uibotGeomBusemannObservables_window_probability
    ℓ ρ hℓ hρ ns hns hsize hne true k A (3 / 2)
  simp only [ite_true] at heq
  rw [heq]
  exact hbound k A hA

/-- Helper toward Proposition 3.9: the geometric Borel SDP process obeys
Lemma 7.7's window bound with one threshold for every size, for each delta. -/
theorem uibotGeomBusemannObservables_sdp_fluctuation :
    ∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
        1 - delta ≤
          (uibotGeometricLocalLimitProbabilityLaw uibotDeterministicComparison_proved
            ℓ ρ hℓ hρ ns hns hsize hne : Measure D39GeomRootedMapClass.{0}).real
            {z | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
              |((uibotGeomBusemannObservables z).1.2 l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  intro delta hdelta
  obtain ⟨A0, hA0, hbound⟩ := lem_sdp_fluctuation_paper delta hdelta
  refine ⟨A0, hA0, ?_⟩
  intro k hk A hA
  have heq := uibotGeomBusemannObservables_window_probability
    ℓ ρ hℓ hρ ns hns hsize hne false k A (3 / 4)
  simp only [Bool.false_eq_true, ite_false] at heq
  rw [heq]
  exact hbound k hk A hA

end LocalLimit

/- Exact remaining offset-factor target (not a declaration or premise):

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
            (s.thetaMinus k) (s.theta k) (s.least k)))

The slice factors above do not alone establish this separate offset
measurability target or Borel selection of entire geodesics. Those are
remaining observable obligations for Lemmas 5.4/5.7. Source-level common
cut, stopped-submap inclusion, finite-distance and path predicates still
need consumer-specific integration for Definition 1.3, Lemmas 3.8, 5.2–5.4,
5.7, 7.1, 7.5. Full predicate equivalence through recovered codes is proved
an intrinsic geometric face collection. The exact geometric face-transport
target and the cut-side/boundary factors are recorded in the separately
owned UIBOTCutDescent2.lean; they are neither imported nor edited here.
No consumer qualification or numbered-result status is changed. -/

end DirectedDistances.PaperProofs.Section3
end
