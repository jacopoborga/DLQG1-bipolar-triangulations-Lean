module
public import Palomar.Principal.Busemann.Solution
public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified
public import DirectedDistances.PaperProofs.Section7.SDPFluctuationIdentified

public section

namespace DLQG1.Palomar.Model.PaperProofs.Section7

abbrev identifiedLDPWitness (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W,
    ∃ h : DirectedDistances.KMSW.BoundaryHitWitnesses
      (DLQG1.Palomar.Model.KMSW.shiftedStream W 0),
    ∃ hLL : ∀ k : ℤ, k ≤ 0 →
      DLQG1.Palomar.Model.KMSW.wholePlaneEdgePresent W
        (DLQG1.Palomar.Model.KMSW.wholePlaneEdgeι W 0
          (DirectedDistances.KMSW.kmswLLCreatedEdge
            (DLQG1.Palomar.Model.KMSW.shiftedStream W 0)
            (DirectedDistances.KMSW.boundaryHitTime
              (DLQG1.Palomar.Model.KMSW.shiftedStream W 0) h (k - 1)))),
    DLQG1.Palomar.Model.PaperProofs.Section1.IsIdentifiedM0BusemannLDP
      (DLQG1.Palomar.Model.KMSW.m0CutData W H h hLL) X

abbrev sourceIdentifiedLDPWitness (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : DirectedDistances.KMSW.WholePlaneRotationHypothesis W,
    ∃ h : DirectedDistances.KMSW.BoundaryHitWitnesses
      (DirectedDistances.KMSW.shiftedStream W 0),
    ∃ hLL : ∀ k : ℤ, k ≤ 0 →
      DirectedDistances.KMSW.wholePlaneEdgePresent W
        (DirectedDistances.KMSW.wholePlaneEdgeι W 0
          (DirectedDistances.KMSW.kmswLLCreatedEdge
            (DirectedDistances.KMSW.shiftedStream W 0)
            (DirectedDistances.KMSW.boundaryHitTime
              (DirectedDistances.KMSW.shiftedStream W 0) h (k - 1)))),
    DirectedDistances.PaperProofs.Section1.IsIdentifiedM0BusemannLDP
      (DirectedDistances.KMSW.m0CutData W H h hLL) X

abbrev identifiedSDPWitness (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W,
    ∃ h : DirectedDistances.KMSW.BoundaryHitWitnesses
      (DLQG1.Palomar.Model.KMSW.shiftedStream W 0),
    ∃ hLL : ∀ k : ℤ, k ≤ 0 →
      DLQG1.Palomar.Model.KMSW.wholePlaneEdgePresent W
        (DLQG1.Palomar.Model.KMSW.wholePlaneEdgeι W 0
          (DirectedDistances.KMSW.kmswLLCreatedEdge
            (DLQG1.Palomar.Model.KMSW.shiftedStream W 0)
            (DirectedDistances.KMSW.boundaryHitTime
              (DLQG1.Palomar.Model.KMSW.shiftedStream W 0) h (k - 1)))),
    DLQG1.Palomar.Model.PaperProofs.Section1.IsIdentifiedM0BusemannSDP
      (DLQG1.Palomar.Model.KMSW.m0CutData W H h hLL) X

abbrev sourceIdentifiedSDPWitness (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : DirectedDistances.KMSW.WholePlaneRotationHypothesis W,
    ∃ h : DirectedDistances.KMSW.BoundaryHitWitnesses
      (DirectedDistances.KMSW.shiftedStream W 0),
    ∃ hLL : ∀ k : ℤ, k ≤ 0 →
      DirectedDistances.KMSW.wholePlaneEdgePresent W
        (DirectedDistances.KMSW.wholePlaneEdgeι W 0
          (DirectedDistances.KMSW.kmswLLCreatedEdge
            (DirectedDistances.KMSW.shiftedStream W 0)
            (DirectedDistances.KMSW.boundaryHitTime
              (DirectedDistances.KMSW.shiftedStream W 0) h (k - 1)))),
    DirectedDistances.PaperProofs.Section1.IsIdentifiedM0BusemannSDP
      (DirectedDistances.KMSW.m0CutData W H h hLL) X

@[expose] noncomputable def identifiedLDPBusemann (W : ℤ → Fin 3) : ℤ → ℤ := by
  classical
  exact if hW : ∃ X : ℤ → ℤ, identifiedLDPWitness W X then hW.choose else fun _ => 0

@[expose] noncomputable def identifiedSDPBusemann (W : ℤ → Fin 3) : ℤ → ℤ := by
  classical
  exact if hW : ∃ X : ℤ → ℤ, identifiedSDPWitness W X then hW.choose else fun _ => 0

theorem identifiedLDPWitness_iff_source (W : ℤ → Fin 3) (X : ℤ → ℤ) :
    identifiedLDPWitness W X ↔ sourceIdentifiedLDPWitness W X := by
  constructor
  · rintro ⟨H, h, hLL, hX⟩
    let H₀ := DLQG1.Palomar.Model.KMSW.sourceHyp H
    let h₀ := DLQG1.Palomar.Model.KMSW.sourceBoundaryHits h
    let hLL₀ := (DLQG1.Palomar.Model.KMSW.llPresence_iff_source W h).mp hLL
    refine ⟨H₀, h₀, hLL₀, ?_⟩
    let D := DLQG1.Palomar.Model.KMSW.m0CutData W H h hLL
    let E := DLQG1.Palomar.Model.KMSW.sourceChosenCut W H h hLL
    have hx : ∀ k,
        DLQG1.Palomar.Model.KMSW.sourceVertexEquiv W (D.x k) = E.x k :=
      DLQG1.Palomar.Model.KMSW.chosen_x_eq_source W H h hLL
    exact (DLQG1.Palomar.Model.PaperProofs.Section1.identifiedLDP_iff_source
      D E hx X).mp hX
  · rintro ⟨H₀, h₀, hLL₀, hX⟩
    let H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W :=
      (DLQG1.Palomar.Model.KMSW.rotationHyp_iff_source W).mpr H₀
    let h : DirectedDistances.KMSW.BoundaryHitWitnesses
        (DLQG1.Palomar.Model.KMSW.shiftedStream W 0) := by
      simpa only [DLQG1.Palomar.Model.KMSW.shiftedStream_eq_source] using h₀
    let hLL :=
      (DLQG1.Palomar.Model.KMSW.llPresence_iff_source W h).mpr hLL₀
    refine ⟨H, h, hLL, ?_⟩
    let D := DLQG1.Palomar.Model.KMSW.m0CutData W H h hLL
    let E := DLQG1.Palomar.Model.KMSW.sourceChosenCut W H h hLL
    have hx : ∀ k,
        DLQG1.Palomar.Model.KMSW.sourceVertexEquiv W (D.x k) = E.x k :=
      DLQG1.Palomar.Model.KMSW.chosen_x_eq_source W H h hLL
    have hE : E = DirectedDistances.KMSW.m0CutData W H₀ h₀ hLL₀ := by
      dsimp [E, DLQG1.Palomar.Model.KMSW.sourceChosenCut]
    rw [← hE] at hX
    exact (DLQG1.Palomar.Model.PaperProofs.Section1.identifiedLDP_iff_source
      D E hx X).mpr hX

theorem identifiedSDPWitness_iff_source (W : ℤ → Fin 3) (X : ℤ → ℤ) :
    identifiedSDPWitness W X ↔ sourceIdentifiedSDPWitness W X := by
  constructor
  · rintro ⟨H, h, hLL, hX⟩
    let H₀ := DLQG1.Palomar.Model.KMSW.sourceHyp H
    let h₀ := DLQG1.Palomar.Model.KMSW.sourceBoundaryHits h
    let hLL₀ := (DLQG1.Palomar.Model.KMSW.llPresence_iff_source W h).mp hLL
    refine ⟨H₀, h₀, hLL₀, ?_⟩
    let D := DLQG1.Palomar.Model.KMSW.m0CutData W H h hLL
    let E := DLQG1.Palomar.Model.KMSW.sourceChosenCut W H h hLL
    have hx : ∀ k,
        DLQG1.Palomar.Model.KMSW.sourceVertexEquiv W (D.x k) = E.x k :=
      DLQG1.Palomar.Model.KMSW.chosen_x_eq_source W H h hLL
    exact (DLQG1.Palomar.Model.PaperProofs.Section1.identifiedSDP_iff_source
      D E hx X).mp hX
  · rintro ⟨H₀, h₀, hLL₀, hX⟩
    let H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W :=
      (DLQG1.Palomar.Model.KMSW.rotationHyp_iff_source W).mpr H₀
    let h : DirectedDistances.KMSW.BoundaryHitWitnesses
        (DLQG1.Palomar.Model.KMSW.shiftedStream W 0) := by
      simpa only [DLQG1.Palomar.Model.KMSW.shiftedStream_eq_source] using h₀
    let hLL :=
      (DLQG1.Palomar.Model.KMSW.llPresence_iff_source W h).mpr hLL₀
    refine ⟨H, h, hLL, ?_⟩
    let D := DLQG1.Palomar.Model.KMSW.m0CutData W H h hLL
    let E := DLQG1.Palomar.Model.KMSW.sourceChosenCut W H h hLL
    have hx : ∀ k,
        DLQG1.Palomar.Model.KMSW.sourceVertexEquiv W (D.x k) = E.x k :=
      DLQG1.Palomar.Model.KMSW.chosen_x_eq_source W H h hLL
    have hE : E = DirectedDistances.KMSW.m0CutData W H₀ h₀ hLL₀ := by
      dsimp [E, DLQG1.Palomar.Model.KMSW.sourceChosenCut]
    rw [← hE] at hX
    exact (DLQG1.Palomar.Model.PaperProofs.Section1.identifiedSDP_iff_source
      D E hx X).mpr hX

theorem identifiedLDPWitnessFun_eq_source (W : ℤ → Fin 3) :
    (fun X : ℤ → ℤ => identifiedLDPWitness W X) =
      (fun X => sourceIdentifiedLDPWitness W X) := by
  funext X
  exact propext (identifiedLDPWitness_iff_source W X)

theorem identifiedSDPWitnessFun_eq_source (W : ℤ → Fin 3) :
    (fun X : ℤ → ℤ => identifiedSDPWitness W X) =
      (fun X => sourceIdentifiedSDPWitness W X) := by
  funext X
  exact propext (identifiedSDPWitness_iff_source W X)

private theorem exists_choose_eq_of_pred_eq {α : Type} {P Q : α → Prop}
    (hPQ : P = Q) (hP : ∃ x, P x) (hQ : ∃ x, Q x) :
    hP.choose = hQ.choose := by
  cases hPQ
  have hh : hP = hQ := Subsingleton.elim _ _
  cases hh
  rfl

theorem identifiedLDPBusemann_eq_source (W : ℤ → Fin 3) :
    identifiedLDPBusemann W =
      DirectedDistances.PaperProofs.Section7.identifiedLDPBusemann W := by
  classical
  change
    (if hW : ∃ X : ℤ → ℤ, identifiedLDPWitness W X
      then hW.choose else fun _ => 0) =
    (if hW : ∃ X : ℤ → ℤ, sourceIdentifiedLDPWitness W X
      then hW.choose else fun _ => 0)
  have hPred := identifiedLDPWitnessFun_eq_source W
  by_cases hM : ∃ X : ℤ → ℤ, identifiedLDPWitness W X
  · have hS : ∃ X : ℤ → ℤ, sourceIdentifiedLDPWitness W X := by
      rw [← hPred]
      exact hM
    have hc := exists_choose_eq_of_pred_eq hPred hM hS
    rw [dite_eq_left hM, dite_eq_left hS]
    funext k
    exact congrFun hc k
  · have hS : ¬ ∃ X : ℤ → ℤ, sourceIdentifiedLDPWitness W X := by
      intro hs
      apply hM
      rw [hPred]
      exact hs
    rw [dite_eq_right hM, dite_eq_right hS]

theorem identifiedSDPBusemann_eq_source (W : ℤ → Fin 3) :
    identifiedSDPBusemann W =
      DirectedDistances.PaperProofs.Section7.identifiedSDPBusemann W := by
  classical
  change
    (if hW : ∃ X : ℤ → ℤ, identifiedSDPWitness W X
      then hW.choose else fun _ => 0) =
    (if hW : ∃ X : ℤ → ℤ, sourceIdentifiedSDPWitness W X
      then hW.choose else fun _ => 0)
  have hPred := identifiedSDPWitnessFun_eq_source W
  by_cases hM : ∃ X : ℤ → ℤ, identifiedSDPWitness W X
  · have hS : ∃ X : ℤ → ℤ, sourceIdentifiedSDPWitness W X := by
      rw [← hPred]
      exact hM
    have hc := exists_choose_eq_of_pred_eq hPred hM hS
    rw [dite_eq_left hM, dite_eq_left hS]
    funext k
    exact congrFun hc k
  · have hS : ¬ ∃ X : ℤ → ℤ, sourceIdentifiedSDPWitness W X := by
      intro hs
      apply hM
      rw [hPred]
      exact hs
    rw [dite_eq_right hM, dite_eq_right hS]

end DLQG1.Palomar.Model.PaperProofs.Section7

