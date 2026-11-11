/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumersSection7

/-! # Direct intrinsic restatements of Section 7 consumers

104–111,233–238,287–292`. Each a.e. conclusion uses the same shared-cut iid
event; the geometric qualifier is retained. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

local instance intrinsicConsumersSection7DirectMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance intrinsicConsumersSection7DirectBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: Lemma 7.1's stopped path conclusion holds
on the shared iid event for every representative and produced isomorphism.
The same intrinsic cut supplies the boundary labels, stopped stages, and
path lower bound using `sampledIntrinsicSequence true`. -/
theorem intrinsicConsumersSection7_lem71_direct :
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap
        uibotDeterministicComparison_proved U
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        ∃ H : WholePlaneRotationHypothesis U,
        ∃ h : BoundaryHitWitnesses (shiftedStream U 0),
        ∃ hpast : BoundaryHitWitnesses (kmswPastCode U),
        ∃ hp : ∀ e : WholePlaneEdge U, wholePlaneEdgePresent U e,
        let G := WholePlanePastGlueDrawing.glueDrawing U h hpast H
        let hLL := fun (k : ℤ) (_hk : k ≤ 0) => hp
          (wholePlaneEdgeι U 0 (kmswLLCreatedEdge (shiftedStream U 0)
            (boundaryHitTime (shiftedStream U 0) h (k - 1))))
        let D := m0CutData U H h hLL
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap U H G hp) (uibotWholePlaneSourceRoot U H G)
          A.map A.root) ∧
        ∃ C : IntrinsicFutureCut2 A,
          (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
          ∀ I : D39GeomRootedMapIsoV2
            (uibotWholePlaneSourceMap U H G hp) (uibotWholePlaneSourceRoot U H G)
            A.map A.root,
            (∀ k : ℤ, C.x k = I.vertexEquiv (D.x k)) ∧
            IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
              (sampledIntrinsicSequence true U) ∧
            let V := fun j => I.vertexEquiv (wholePlaneVertexι U 0 j)
            let E := fun j => I.edgeEquiv (wholePlaneEdgeι U 0 j)
            let S := I.edgeEquiv '' D.edges
            let missing := fun e => D.missing (I.edgeEquiv.symm e)
            let t := intrinsicStageBoundaryTime U H h hLL G hp A I
            (∀ k : ℤ,
              IsLeast {n : ℕ | I.vertexEquiv (D.x k) =
                intrinsicStageActiveInitial A
                  (intrinsicStageActiveEdges U H G hp A I) n} (t k) ∧
              t k = boundaryHitTime (shiftedStream U 0) h k ∧
              IntrinsicStageShiftContainment U A V E S missing
                (I.vertexEquiv (D.x k)) (t k)) ∧
            (∀ n : ℕ,
              intrinsicStageAllocatedVertices U A V n = I.vertexEquiv ''
                intrinsicStageAllocatedVertices U
                  (uibotWholePlaneSourceDomain U H G hp) (wholePlaneVertexι U 0) n ∧
              intrinsicStageAllocatedEdges U A E n = I.edgeEquiv ''
                intrinsicStageAllocatedEdges U
                  (uibotWholePlaneSourceDomain U H G hp) (wholePlaneEdgeι U 0) n ∧
              intrinsicStagePresentEdges U A E n = I.edgeEquiv ''
                intrinsicStagePresentEdges U
                  (uibotWholePlaneSourceDomain U H G hp) (wholePlaneEdgeι U 0) n) ∧
            (∀ (n N : ℕ) (p : Fin (N + 1) → WholePlaneVertex U),
              IntrinsicIdentifiedStagePath U A V E n N
                (fun i => I.vertexEquiv (p i)) ↔
              IdentifiedStagePath U (wholePlaneVertexι U 0) n N p) ∧
            ∀ ell k : ℕ, 1 ≤ ell → ell < k →
              ∃ N : ℕ, ∃ p : Fin (N + 1) → A.V,
                (∀ i : Fin N, ∃ e : A.E,
                  IntrinsicStageEdgeStep A S missing e (p i.castSucc) (p i.succ)) ∧
                IntrinsicIdentifiedStagePath U A V E (t (-(k : ℤ))) N p ∧
                (max (sampledIntrinsicSequence true U (-(ell : ℤ)) -
                  sampledIntrinsicSequence true U (-(k : ℤ))) 0).toNat ≤ N := by
  filter_upwards [intrinsicConsumersSection7_jointIidEvent] with U hJoint
  have hcode : uibotRecoveredCode
      (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U) = U :=
    hJoint.2.1.1.1
  have hseq : sampledIntrinsicSequence true U = identifiedLDPBusemann U :=
    hJoint.2.1.2.2.2
  have hlabels := hJoint.2.2.1
  have hstages := hJoint.2.2.2
  dsimp only at hlabels hstages ⊢
  rw [hcode] at hstages
  obtain ⟨HL, hL, hpastL, hpL, hrepL⟩ := hlabels
  obtain ⟨HS, hS, hpastS, hpS, ⟨_, hrepS⟩⟩ := hstages
  have hH : HS = HL := Subsingleton.elim _ _
  subst HS
  have hh : hS = hL := Subsingleton.elim _ _
  subst hS
  have hpast : hpastS = hpastL := Subsingleton.elim _ _
  subst hpastS
  have hp : hpS = hpL := Subsingleton.elim _ _
  subst hpS
  intro A hA
  refine ⟨HL, hL, hpastL, hpL, ?_⟩
  obtain ⟨hIso, ⟨C, hC, _⟩⟩ := hrepL A hA
  have hStageA := hrepS A hA
  refine ⟨hIso, C, hC.1, ?_⟩
  intro I
  obtain ⟨_, _, _, _, _, _, _, hlabel, _⟩ := hC.2 I
  have hldpChar : IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
      (sampledIntrinsicSequence true U) :=
    ((hJoint.1.2 A hA).2 C).2.2.2.2
  obtain ⟨hboundary, hsets, hiff, hpath⟩ := hStageA.2 I
  refine ⟨hlabel, hldpChar, hboundary, hsets, hiff, ?_⟩
  intro ell k hell hk
  obtain ⟨N, p, hsteps, hstage, hbound⟩ := hpath ell k hell hk
  refine ⟨N, p, hsteps, hstage, ?_⟩
  simpa only [hseq] using hbound

/-- Helper toward Proposition 3.9: Lemma 7.5's boundary inequality holds on
the shared iid event for every representative and produced isomorphism, with
intrinsic reachability and finite intrinsic SDP retained explicitly. -/
theorem intrinsicConsumersSection7_lem75_direct :
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap
        uibotDeterministicComparison_proved U
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        ∃ H : WholePlaneRotationHypothesis U,
        ∃ h : BoundaryHitWitnesses (shiftedStream U 0),
        ∃ hpast : BoundaryHitWitnesses (kmswPastCode U),
        ∃ hp : ∀ e : WholePlaneEdge U, wholePlaneEdgePresent U e,
        let G := WholePlanePastGlueDrawing.glueDrawing U h hpast H
        let hLL := fun (j : ℤ) (_hj : j ≤ 0) => hp
          (wholePlaneEdgeι U 0 (kmswLLCreatedEdge (shiftedStream U 0)
            (boundaryHitTime (shiftedStream U 0) h (j - 1))))
        let D := m0CutData U H h hLL
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap U H G hp) (uibotWholePlaneSourceRoot U H G)
          A.map A.root) ∧
        ∃ C : IntrinsicFutureCut2 A,
          (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
          ∀ I : D39GeomRootedMapIsoV2
            (uibotWholePlaneSourceMap U H G hp) (uibotWholePlaneSourceRoot U H G)
            A.map A.root,
            (∀ j : ℤ, C.x j = I.vertexEquiv (D.x j)) ∧
            IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
              (sampledIntrinsicSequence false U) ∧
            ∀ l k : ℤ, 0 ≤ l → l < k →
              intrinsicBusemannReachable A (intrinsicConsumerCut C) (C.x l) (C.x k) ∧
              intrinsicDirectedSDP A (intrinsicConsumerCut C).edges
                (intrinsicConsumerCut C).missing (C.x l) (C.x k) ≠ ⊤ ∧
              sampledIntrinsicSequence false U l - sampledIntrinsicSequence false U k ≤
                ((intrinsicDirectedSDP A (intrinsicConsumerCut C).edges
                  (intrinsicConsumerCut C).missing (C.x l) (C.x k)).toNat : ℤ) := by
  filter_upwards [intrinsicConsumersSection7_jointIidEvent] with U hJoint
  have hcode : uibotRecoveredCode
      (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U) = U :=
    hJoint.2.1.1.1
  have hobs := hJoint.2.1.1.2.1
  have hseq : sampledIntrinsicSequence false U = identifiedSDPBusemann U :=
    hJoint.2.1.2.2.1
  have hlabels := hJoint.2.2.1
  have hshared := hJoint.1.1
  dsimp only at hlabels hshared ⊢
  rw [hcode, hobs] at hshared
  obtain ⟨HL, hL, hpastL, hpL, hrepL⟩ := hlabels
  obtain ⟨HT, hT, hLLT, hsharedData⟩ := hshared
  have hH : HT = HL := Subsingleton.elim _ _
  subst HT
  have hh : hT = hL := Subsingleton.elim _ _
  subst hT
  let hLL := fun (j : ℤ) (_hj : j ≤ 0) => hpL
    (wholePlaneEdgeι U 0 (kmswLLCreatedEdge (shiftedStream U 0)
      (boundaryHitTime (shiftedStream U 0) hL (j - 1))))
  have hLL_eq : hLLT = hLL := Subsingleton.elim _ _
  subst hLLT
  let D := m0CutData U HL hL hLL
  obtain ⟨_, hldp, hsdp, _, _, htri⟩ := hsharedData
  have hX : IsIdentifiedM0BusemannSDP D
      (sampledIntrinsicSequence false U) := by
    rw [hseq]
    exact hsdp
  intro A hA
  refine ⟨HL, hL, hpastL, hpL, ?_⟩
  obtain ⟨hIso, ⟨C, hC, _⟩⟩ := hrepL A hA
  refine ⟨hIso, C, hC.1, ?_⟩
  intro I
  obtain ⟨_, he, _, _, hm, _⟩ := hC.2 I
  obtain ⟨_, _, _, _, _, _, _, hlabel, _⟩ := hC.2 I
  have hchar : IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
      (sampledIntrinsicSequence false U) :=
    ((hJoint.1.2 A hA).2 C).2.2.1.2
  refine ⟨hlabel, hchar, ?_⟩
  intro l k hl hlt
  obtain ⟨hsourceReach, hsourceFinite, hsourceBound⟩ :=
    htri (sampledIntrinsicSequence false U) hX l k hl hlt
  have hcut : intrinsicConsumerCut C =
      intrinsicBusemannImageCut U HL
        (WholePlanePastGlueDrawing.glueDrawing U hL hpastL HL) hpL
        (m0CutData U HL hL hLL) A I := by
    cases C
    simp only [intrinsicConsumerCut, intrinsicBusemannImageCut,
      IntrinsicBusemannCut.mk.injEq]
    refine ⟨hC.2 I |> fun q => q.1, he, ?_⟩
    funext e
    apply propext
    obtain ⟨e0, rfl⟩ := I.edgeEquiv.surjective e
    simpa only [Equiv.symm_apply_apply] using hm e0
  have hreach : intrinsicBusemannReachable A (intrinsicConsumerCut C)
      (C.x l) (C.x k) := by
    rw [hcut, hlabel l, hlabel k]
    exact (intrinsicBusemannImageCut_reachable_iff U HL
      (WholePlanePastGlueDrawing.glueDrawing U hL hpastL HL) hpL
      D A I (D.x l) (D.x k)).mpr hsourceReach
  have hdist := intrinsicDirected_image_source_distances U HL
    (WholePlanePastGlueDrawing.glueDrawing U hL hpastL HL) hpL
    D A I (D.x l) (D.x k)
  have hdist' : intrinsicDirectedSDP A (intrinsicConsumerCut C).edges
      (intrinsicConsumerCut C).missing (C.x l) (C.x k) =
        D.sdp (D.x l) (D.x k) := by
    rw [hcut, hlabel l, hlabel k]
    simpa only [intrinsicBusemannImageCut, M0CutData.sdp] using hdist.1
  refine ⟨hreach, ?_, ?_⟩
  · rw [hdist']
    exact hsourceFinite
  · rw [hdist']
    exact hsourceBound

/-- Helper toward Proposition 3.9: one iid conclusion packages the intrinsic
representative-wide LDP characterization with Lemma 7.3's sampled-sequence
probability bound. All a.e. facts use the shared Section 7 cut event. -/
theorem intrinsicConsumersSection7_lem73_direct :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |(sampledIntrinsicSequence true W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)}) ∧
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ A : D39DomainRootedMap.{0},
        Quotient.mk d39DomainSetoid A =
          uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W →
        (∃! _C : IntrinsicFutureCut2 A, True) ∧
        ∀ C : IntrinsicFutureCut2 A,
          (∃! X : ℤ → ℤ,
            IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X) ∧
          (∃! X : ℤ → ℤ,
            IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X) ∧
          (sampledIntrinsicSequence false W = identifiedSDPBusemann W ∧
            IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
              (sampledIntrinsicSequence false W)) ∧
          (sampledIntrinsicSequence true W = identifiedLDPBusemann W ∧
            IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
              (sampledIntrinsicSequence true W)) := by
  refine ⟨intrinsicConsumersSection7_ldpFluctuation, ?_⟩
  filter_upwards [intrinsicConsumersSection7_jointIidEvent] with W hW
  exact hW.1.2

/-- Helper toward Proposition 3.9: one iid conclusion packages the intrinsic
representative-wide SDP characterization with Lemma 7.7's sampled-sequence
probability bound, preserving `∀ δ > 0, ∃ A₀ > 1, ∀ k ≥ 1, ∀ A ≥ A₀`.
All a.e. facts use the shared Section 7 cut event. -/
theorem intrinsicConsumersSection7_lem77_direct :
    ((∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
        1 - delta ≤ wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |(sampledIntrinsicSequence false W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)})) ∧
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ A : D39DomainRootedMap.{0},
        Quotient.mk d39DomainSetoid A =
          uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W →
        (∃! _C : IntrinsicFutureCut2 A, True) ∧
        ∀ C : IntrinsicFutureCut2 A,
          (∃! X : ℤ → ℤ,
            IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x X) ∧
          (∃! X : ℤ → ℤ,
            IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x X) ∧
          (sampledIntrinsicSequence false W = identifiedSDPBusemann W ∧
            IsIntrinsicBusemannSDP A (intrinsicConsumerCut C) C.x
              (sampledIntrinsicSequence false W)) ∧
          (sampledIntrinsicSequence true W = identifiedLDPBusemann W ∧
            IsIntrinsicBusemannLDP A (intrinsicConsumerCut C) C.x
              (sampledIntrinsicSequence true W)) := by
  refine ⟨intrinsicConsumersSection7_sdpFluctuation, ?_⟩
  filter_upwards [intrinsicConsumersSection7_jointIidEvent] with W hW
  exact hW.1.2

end DirectedDistances.PaperProofs.Section3
end
