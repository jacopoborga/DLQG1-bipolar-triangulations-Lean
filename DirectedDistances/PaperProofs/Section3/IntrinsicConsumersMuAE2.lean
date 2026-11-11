/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumersMuAE
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumersSection7Direct

/-! # Further intrinsic consumers under the UIBOT class law

104–111,233–238,287–292`. The stopped-stage conclusion is transferred by the recovered
code and almost-sure reconstruction of the class. Reconstruction uses the
measurable conull set of `UIBOTClassReconstruction`; no measurability of
representative-wide predicates is assumed. The uniquely characterized
intrinsic sequences are functions of the class, and their laws transfer the
two uniform fluctuation bounds. The intrinsic geometric qualifier is retained. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

local instance intrinsicConsumersMuAE2MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance intrinsicConsumersMuAE2BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

local notation "μᵢ" =>
  (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
    Measure D39GeomRootedMapClass)

/-- Helper toward Proposition 3.9: Lemma 7.1 holds on every representative
of almost every UIBOT class, using its unique intrinsic cut and its intrinsic
LDP sequence. The recovered code is a function of the class and supplies the
stopped stages and their first-hit characterization. -/
theorem intrinsicConsumersMuAE2_lem71 :
    ∀ᵐ z ∂μᵢ,
      let W := uibotRecoveredCode z
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        ∃ H : WholePlaneRotationHypothesis W,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hpast : BoundaryHitWitnesses (kmswPastCode W),
        ∃ hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e,
        let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
        let hLL := fun (k : ℤ) (_hk : k ≤ 0) => hp
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))
        let D := m0CutData W H h hLL
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root) ∧
        ∃ C : IntrinsicFutureCut2 A,
          (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
          ∀ I : D39GeomRootedMapIsoV2
            (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
            A.map A.root,
            (∀ k : ℤ, C.x k = I.vertexEquiv (D.x k)) ∧
            IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
              (intrinsicConsumerSequence true z) ∧
            let V := fun j => I.vertexEquiv (wholePlaneVertexι W 0 j)
            let E := fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)
            let S := I.edgeEquiv '' D.edges
            let missing := fun e => D.missing (I.edgeEquiv.symm e)
            let t := intrinsicStageBoundaryTime W H h hLL G hp A I
            (∀ k : ℤ,
              IsLeast {n : ℕ | I.vertexEquiv (D.x k) =
                intrinsicStageActiveInitial A
                  (intrinsicStageActiveEdges W H G hp A I) n} (t k) ∧
              t k = boundaryHitTime (shiftedStream W 0) h k ∧
              IntrinsicStageShiftContainment W A V E S missing
                (I.vertexEquiv (D.x k)) (t k)) ∧
            (∀ n : ℕ,
              intrinsicStageAllocatedVertices W A V n = I.vertexEquiv ''
                intrinsicStageAllocatedVertices W
                  (uibotWholePlaneSourceDomain W H G hp) (wholePlaneVertexι W 0) n ∧
              intrinsicStageAllocatedEdges W A E n = I.edgeEquiv ''
                intrinsicStageAllocatedEdges W
                  (uibotWholePlaneSourceDomain W H G hp) (wholePlaneEdgeι W 0) n ∧
              intrinsicStagePresentEdges W A E n = I.edgeEquiv ''
                intrinsicStagePresentEdges W
                  (uibotWholePlaneSourceDomain W H G hp) (wholePlaneEdgeι W 0) n) ∧
            (∀ (n N : ℕ) (p : Fin (N + 1) → WholePlaneVertex W),
              IntrinsicIdentifiedStagePath W A V E n N
                (fun i => I.vertexEquiv (p i)) ↔
              IdentifiedStagePath W (wholePlaneVertexι W 0) n N p) ∧
            ∀ ell k : ℕ, 1 ≤ ell → ell < k →
              ∃ N : ℕ, ∃ p : Fin (N + 1) → A.V,
                (∀ i : Fin N, ∃ e : A.E,
                  IntrinsicStageEdgeStep A S missing e (p i.castSucc) (p i.succ)) ∧
                IntrinsicIdentifiedStagePath W A V E (t (-(k : ℤ))) N p ∧
                (max (intrinsicConsumerSequence true z (-(ell : ℤ)) -
                  intrinsicConsumerSequence true z (-(k : ℤ))) 0).toNat ≤ N := by
  have h := intrinsicConsumersSection7_lem71_direct
  rw [← uibotLaw135_recoveredCode_law] at h
  have hp := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable h
  filter_upwards [hp, uibotClassSeparation6_ae_reconstruction] with z hz hrec
  simpa only [sampledIntrinsicSequence, hrec] using hz

/-- Helper toward Proposition 3.9: Lemma 7.5 holds for every intrinsic cut
of every representative of almost every UIBOT class, retaining reachability,
finite SDP, the endpoint case `l = 0`, and the intrinsic sequence inequality. -/
theorem intrinsicConsumersMuAE2_lem75 :
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0},
      Quotient.mk d39DomainSetoid A = z →
      (∃! _C : IntrinsicFutureCut2 A, True) ∧
      ∀ C : IntrinsicFutureCut2 A,
        IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
          (intrinsicConsumerSequence false z) ∧
        ∀ l k : ℤ, 0 ≤ l → l < k →
        intrinsicBusemannReachable A (intrinsicConsumerCut C) (C.x l) (C.x k) ∧
        intrinsicDirectedSDP A (intrinsicConsumerCut C).edges
          (intrinsicConsumerCut C).missing (C.x l) (C.x k) ≠ ⊤ ∧
        intrinsicConsumerSequence false z l - intrinsicConsumerSequence false z k ≤
          ((intrinsicDirectedSDP A (intrinsicConsumerCut C).edges
            (intrinsicConsumerCut C).missing (C.x l) (C.x k)).toNat : ℤ) := by
  have h := intrinsicConsumersSection7_lem75_direct
  rw [← uibotLaw135_recoveredCode_law] at h
  have hp := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable h
  filter_upwards [hp, uibotClassSeparation6_ae_reconstruction,
    intrinsicConsumersMuAE_unique_cut] with z hz hrec huniq
  simp only [sampledIntrinsicSequence, hrec] at hz
  intro A hA
  refine ⟨huniq A hA, ?_⟩
  intro C
  obtain ⟨H, h, hpast, hp, hI, C₀, hC₀, hall⟩ := hz A hA
  obtain ⟨I⟩ := hI
  rw [hC₀ C]
  exact (hall I).2

private theorem intrinsicConsumersMuAE2_sequence_probability (longest : Bool)
    (s : Set (ℤ → ℤ)) (hs : MeasurableSet s) :
    (μᵢ).real {z | intrinsicConsumerSequence longest z ∈ s} =
      wholePlaneIIDCodeMeasure.real {W | sampledIntrinsicSequence longest W ∈ s} := by
  have hm : AEMeasurable (sampledIntrinsicSequence longest) wholePlaneIIDCodeMeasure :=
    (aemeasurable_intrinsicConsumerSequence longest).comp_measurable
      (measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)
  apply congrArg ENNReal.toReal
  calc
    (μᵢ) {z | intrinsicConsumerSequence longest z ∈ s} =
        ((μᵢ).map (intrinsicConsumerSequence longest)) s :=
      (Measure.map_apply_of_aemeasurable
        (aemeasurable_intrinsicConsumerSequence longest) hs).symm
    _ = (wholePlaneIIDCodeMeasure.map (sampledIntrinsicSequence longest)) s :=
      congrArg (fun ν : Measure (ℤ → ℤ) => ν s)
        (intrinsicConsumersMuAE_sequence_law longest)
    _ = wholePlaneIIDCodeMeasure {W | sampledIntrinsicSequence longest W ∈ s} :=
      Measure.map_apply_of_aemeasurable hm hs

private theorem intrinsicConsumersMuAE2_measurable_fluctuation (k : ℕ) (b : ℝ) :
    MeasurableSet {X : ℤ → ℤ | ∀ l : ℤ,
      -(k : ℤ) ≤ l → l ≤ k → |(X l : ℝ)| ≤ b} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro _hl
  apply MeasurableSet.iInter
  intro _hk
  have hi : Measurable (fun n : ℤ => |(n : ℝ)|) := measurable_of_countable _
  have he : Measurable (fun X : ℤ → ℤ => X l) := measurable_pi_apply l
  exact measurableSet_le (hi.comp he) measurable_const

/-- Helper toward Proposition 3.9: Lemma 7.3 holds for the intrinsic LDP
sequence under the UIBOT law, with one constant uniform in every positive
size and with both full intrinsic sequence characterizations on every cut
of every representative on one conull event. -/
theorem intrinsicConsumersMuAE2_lem73 :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        (μᵢ).real {z | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(intrinsicConsumerSequence true z l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)}) ∧
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0},
      Quotient.mk d39DomainSetoid A = z →
      (∃! _C : IntrinsicFutureCut2 A, True) ∧
      ∀ C : IntrinsicFutureCut2 A,
        (∃! X : ℤ → ℤ, IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X) ∧
        (∃! X : ℤ → ℤ, IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X) ∧
        IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
          (intrinsicConsumerSequence false z) ∧
        IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
          (intrinsicConsumerSequence true z) := by
  refine ⟨?_, intrinsicConsumersMuAE_cut_sequences⟩
  obtain ⟨C, hC, hbound⟩ := intrinsicConsumersSection7_lem73_direct.1
  refine ⟨C, hC, ?_⟩
  intro k hk A hA
  exact (hbound k hk A hA).trans_eq (intrinsicConsumersMuAE2_sequence_probability true
    {X | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k → |(X l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)}
    (intrinsicConsumersMuAE2_measurable_fluctuation k _)).symm

/-- Helper toward Proposition 3.9: Lemma 7.7 holds for the intrinsic SDP
sequence under the UIBOT law, preserving one threshold per positive delta
uniform in every positive size, together with the full representative-wide
intrinsic sequence characterizations on one conull event. -/
theorem intrinsicConsumersMuAE2_lem77 :
    (∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
        1 - delta ≤ (μᵢ).real {z | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |(intrinsicConsumerSequence false z l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)}) ∧
    ∀ᵐ z ∂μᵢ, ∀ A : D39DomainRootedMap.{0},
      Quotient.mk d39DomainSetoid A = z →
      (∃! _C : IntrinsicFutureCut2 A, True) ∧
      ∀ C : IntrinsicFutureCut2 A,
        (∃! X : ℤ → ℤ, IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X) ∧
        (∃! X : ℤ → ℤ, IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X) ∧
        IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
          (intrinsicConsumerSequence false z) ∧
        IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
          (intrinsicConsumerSequence true z) := by
  refine ⟨?_, intrinsicConsumersMuAE_cut_sequences⟩
  intro delta hdelta
  obtain ⟨A0, hA0, hbound⟩ := intrinsicConsumersSection7_lem77_direct.1 delta hdelta
  refine ⟨A0, hA0, ?_⟩
  intro k hk A hA
  exact (hbound k hk A hA).trans_eq (intrinsicConsumersMuAE2_sequence_probability false
    {X | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k → |(X l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)}
    (intrinsicConsumersMuAE2_measurable_fluctuation k _)).symm

end DirectedDistances.PaperProofs.Section3
end
