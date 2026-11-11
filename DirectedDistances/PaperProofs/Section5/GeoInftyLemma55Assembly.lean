module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Reduction
public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusMeasurableClass

/-! Helper toward Lemma 5.5: reduction helper assembling the three
conclusions from the side identifications and measurable `Psi`. Lemma 5.5 is
not proved here. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4

/-- Helper toward Lemma 5.5: transfer independence through measurable maps
when the target observables are almost everywhere equal to the corresponding
composites. The measurable codomains of the two maps may be arbitrary. -/
theorem indepFun_of_ae_eq_comp
    {Ω α β γ δ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure Ω) {X : Ω → α} {Y : Ω → β}
    (F : α → γ) (G : β → δ)
    (hF : Measurable F) (hG : Measurable G)
    (hXY : IndepFun X Y μ)
    {A : Ω → γ} {B : Ω → δ}
    (hA : A =ᵐ[μ] F ∘ X) (hB : B =ᵐ[μ] G ∘ Y) :
    IndepFun A B μ := by
  exact (hXY.comp hF hG).congr hA.symm hB.symm

/-- Helper toward Lemma 5.5: the exact three-clause conclusion follows from
the side identifications and the named open obligation that each `Psi x` is
measurable. This is a reduction helper; Lemma 5.5 is not proved. -/
theorem lemma55_of_sideIdentification_of_measurable_Psi
    (A_L : Lemma55LeftSideObservable)
    (h : Lemma55SideIdentification A_L)
    (hPsi : ∀ x : XDP, Measurable (Psi x)) :
    ∀ (x : XDP) (k : ℤ),
      IndepFun (A_L x k) (lemma55RightSideClassOption x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x 0)) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map (A_L x k) =
        wholePlaneIIDCodeMeasure.map (A_L x 0)) := by
  intro x k
  refine ⟨?_, ?_, ?_⟩
  · by_cases hk : 0 ≤ k
    · have hleft := h.actual_left_ae_eq_Lplus x k hk
      have hright : lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
          (fun W => Psi x (rightSideObsNonneg x k W)) := by
        cases x with
        | ldp =>
            change m0RightSideClassOption true k =ᵐ[wholePlaneIIDCodeMeasure]
              (fun W => Psi XDP.ldp (rightSideObsNonneg XDP.ldp k W))
            simpa [Psi, decodeRPlus] using
              (m0RightSideClassOption_ae_eq_RPlusPresentationClass true k hk)
        | sdp =>
            change m0RightSideClassOption false k =ᵐ[wholePlaneIIDCodeMeasure]
              (fun W => Psi XDP.sdp (rightSideObsNonneg XDP.sdp k W))
            simpa [Psi, decodeRPlus] using
              (m0RightSideClassOption_ae_eq_RPlusPresentationClass false k hk)
      have hF : Measurable (fun c => h.F_Lplus x (decodeLPlus x k c)) :=
        (h.measurable_F_Lplus x).comp (measurable_decodeLPlus x k)
      exact indepFun_of_ae_eq_comp wholePlaneIIDCodeMeasure
        (fun c => h.F_Lplus x (decodeLPlus x k c)) (Psi x)
        hF (hPsi x) (leftSideObsNonneg_indep_rightSideObsNonneg x k)
        hleft hright
    · have hk' : k ≤ 0 := by omega
      have hleft := h.actual_left_ae_eq_Lminus x k hk'
      have hright := h.actual_right_ae_eq_Rminus x k hk'
      exact indepFun_of_ae_eq_comp wholePlaneIIDCodeMeasure
        (h.F_Lminus x) (h.F_Rminus x)
        (h.measurable_F_Lminus x) (h.measurable_F_Rminus x)
        (lemma55_nonpos_presentation_indepFun x k) hleft hright
  · intro hk
    exact lemma55_rightLaw_of_sideIdentification x k hk
  · intro hk
    exact lemma55_leftLaw_of_sideIdentification A_L h x k hk

end DirectedDistances.PaperProofs.Section5

