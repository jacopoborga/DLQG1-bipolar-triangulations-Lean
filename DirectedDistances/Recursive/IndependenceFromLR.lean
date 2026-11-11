module

public import DirectedDistances.Probability.FrontierIndependence
public import DirectedDistances.Probability.ShiftIndependenceInduction
public import DirectedDistances.Probability.IndependenceTwoSided
public import DirectedDistances.Recursive.RightIncrementShift
public import DirectedDistances.Recursive.LeftStationaryBusemann

/-! # CONDITIONAL independence from the left and right Busemann processes

frontier decompositions and independence of the two processes at zero
These conditional helpers are not counted as paper results. F1/F4 remain. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Probability

local notation "μ" => iidCodeMeasure

private theorem iIndepFun_of_frontier_shift
    (τ : (ℕ → Fin 3) → ℕ∞)
    (hτ : ∀ k : ℕ, MeasurableSet[codePast k] {ω | τ ω = k})
    (hfin : ∀ᵐ ω ∂μ, τ ω < ⊤)
    {E : ℕ → (ℕ → Fin 3) → ℤ} (hE : ∀ n, Measurable (E n))
    {G : (ℕ → Fin 3) → (ℕ → ℤ)} (hG : Measurable G)
    (hGE : IndepFun G (fun ω n => E n ω) μ)
    (hshift : ∀ n, E (n + 1) =ᵐ[μ]
      E n ∘ (fun ω => codeShift (τ ω).toNat ω))
    (hfront : ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂μ, E 0 ω = F (τ ω).toNat (codePastVector τ ω)
        (G (codeShift (τ ω).toNat ω))) :
    iIndepFun E μ := by
  have hT : MeasurePreserving (fun ω => codeShift (τ ω).toNat ω) μ μ :=
    ⟨measurable_codeShift_toNat τ hτ, map_codeShift_toNat τ hτ hfin⟩
  apply iIndepFun_of_head_indep_tail_of_shift hT hE hshift
  obtain ⟨F, hF, hfront⟩ := hfront
  have h := indepFun_frontier_of_strongMarkov τ hτ hfin hG
    (measurable_pi_iff.mpr hE) hGE F hF
  have htail : (fun ω n => E n (codeShift (τ ω).toNat ω)) =ᵐ[μ]
      (fun ω n => E (n + 1) ω) := by
    have hall := ae_all_iff.mpr hshift
    filter_upwards [hall] with ω hω
    funext n
    exact (hω n).symm
  apply h.congr _ htail
  filter_upwards [hfront] with ω hω
  exact hω.symm

/-- CONDITIONAL reduction of `item-busemann-ind`
The frontier decompositions and left/right independence (`lem-geo-infty-ind`
hypotheses. This helper is not counted as a paper result; F1/F4 remain. -/
theorem iIndepFun_increment_of_LR
    (V : (ℕ → Fin 3) → ℤ → ℤ)
    (hV : ∀ k, Measurable (fun ω => V ω k))
    (_h0 : ∀ ω, V ω 0 = 0)
    (hRshift : ∀ j : ℕ, 1 ≤ j →
      (fun ω => V ω ((j : ℤ) + 1) - V ω (((j : ℤ) + 1) - 1)) =ᵐ[μ]
      (fun ω => V ω (j : ℤ) - V ω ((j : ℤ) - 1)) ∘
        (fun ω => codeShift (codeSndFirstHit (-1) ω).toNat ω))
    (hLshift : ∀ n : ℕ,
      (fun ω => V ω (-(n : ℤ) - 1) - V ω ((-(n : ℤ) - 1) - 1)) =ᵐ[μ]
      (fun ω => V ω (-(n : ℤ)) - V ω (-(n : ℤ) - 1)) ∘
        (fun ω => codeShift (codeFstFirstHit (-1) ω).toNat ω))
    (hfrontR : ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂μ, V ω 1 - V ω (1 - 1) =
        F (codeSndFirstHit (-1) ω).toNat (codePastVector (codeSndFirstHit (-1)) ω)
          (fun j => V (codeShift (codeSndFirstHit (-1) ω).toNat ω) (-(j : ℤ))))
    (hfrontL : ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂μ, V ω 0 - V ω (0 - 1) =
        F (codeFstFirstHit (-1) ω).toNat (codePastVector (codeFstFirstHit (-1)) ω)
          (fun j => V (codeShift (codeFstFirstHit (-1) ω).toNat ω) (j : ℤ)))
    (hLR : IndepFun (fun ω (j : ℕ) => V ω (-(j : ℤ)))
      (fun ω (j : ℕ) => V ω (j : ℤ)) μ) :
    iIndepFun (fun k ω => V ω k - V ω (k - 1)) μ := by
  let D : ℤ → (ℕ → Fin 3) → ℤ := fun k ω => V ω k - V ω (k - 1)
  let L : (ℕ → Fin 3) → ℕ → ℤ := fun ω n => V ω (-(n : ℤ))
  let R : (ℕ → Fin 3) → ℕ → ℤ := fun ω n => V ω (n : ℤ)
  let pL : (ℕ → ℤ) → ℕ → ℤ := fun x n => x n - x (n + 1)
  let pR : (ℕ → ℤ) → ℕ → ℤ := fun x n => x (n + 1) - x n
  have hpL : Measurable pL := measurable_pi_iff.mpr fun n =>
    (measurable_pi_apply n).sub (measurable_pi_apply (n + 1))
  have hpR : Measurable pR := measurable_pi_iff.mpr fun n =>
    (measurable_pi_apply (n + 1)).sub (measurable_pi_apply n)
  have hDm : ∀ k, Measurable (D k) := fun k => (hV k).sub (hV (k - 1))
  have hLm : Measurable L := measurable_pi_iff.mpr fun n => hV (-(n : ℤ))
  have hRm : Measurable R := measurable_pi_iff.mpr fun n => hV (n : ℤ)
  have hpLD : pL ∘ L = (fun ω (n : ℕ) => D (-(n : ℤ)) ω) := by
    funext ω n
    dsimp [pL, L, D]
    congr 1
    congr 1
    omega
  have hpRD : pR ∘ R = (fun ω (n : ℕ) => D ((n : ℤ) + 1) ω) := by
    funext ω n
    simp [pR, R, D]
  have hGLR : IndepFun L (fun ω (n : ℕ) => D ((n : ℤ) + 1) ω) μ := by
    have h := hLR.comp measurable_id hpR
    change IndepFun L (pR ∘ R) μ at h
    rw [hpRD] at h
    exact h
  have hGRL : IndepFun R (fun ω (n : ℕ) => D (-(n : ℤ)) ω) μ := by
    have h := hLR.symm.comp measurable_id hpL
    change IndepFun R (pL ∘ L) μ at h
    rw [hpLD] at h
    exact h
  have hR : iIndepFun (fun n : ℕ => D ((n : ℤ) + 1)) μ := by
    apply iIndepFun_of_frontier_shift (codeSndFirstHit (-1))
      (measurableSet_codePast_codeSndFirstHit_eq (-1))
      (ae_codeSndFirstHit_lt_top_int (-1)) (fun n => hDm _) hLm hGLR
    · intro n
      simpa [D, Nat.cast_add, Nat.cast_one, add_assoc] using hRshift (n + 1) (by omega)
    · simpa [D, L] using hfrontR
  have hL : iIndepFun (fun n : ℕ => D (-(n : ℤ))) μ := by
    apply iIndepFun_of_frontier_shift (codeFstFirstHit (-1))
      (measurableSet_codePast_codeFstFirstHit_eq (-1))
      (ae_codeFstFirstHit_lt_top_int (-1)) (fun n => hDm _) hRm hGRL
    · intro n
      have heq : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 := by omega
      simpa only [heq] using hLshift n
    · simpa [D, R] using hfrontL
  apply iIndepFun_int_of_two_sides hDm hR hL
  have h := hLR.comp hpL hpR
  change IndepFun (pL ∘ L) (pR ∘ R) μ at h
  rw [hpLD, hpRD] at h
  exact h

private theorem left_increment_shift_of_value_shift
    (V : (ℕ → Fin 3) → ℤ → ℤ)
    (hshift : ∀ᵐ ω ∂μ, ∀ j : ℕ,
      V (codeShift (codeFstFirstHit (-1) ω).toNat ω) (-(j : ℤ)) =
        V ω (-1 - j) - V ω (-1)) :
    ∀ n : ℕ,
      (fun ω => V ω (-(n : ℤ) - 1) - V ω ((-(n : ℤ) - 1) - 1)) =ᵐ[μ]
      (fun ω => V ω (-(n : ℤ)) - V ω (-(n : ℤ) - 1)) ∘
        (fun ω => codeShift (codeFstFirstHit (-1) ω).toNat ω) := by
  intro n
  filter_upwards [hshift] with ω hω
  have hn : -1 - (n : ℤ) = -(n : ℤ) - 1 := by omega
  have hns : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 := by omega
  have hnss : -1 - ((n + 1 : ℕ) : ℤ) = (-(n : ℤ) - 1) - 1 := by omega
  have h₁ := hω n
  have h₂ := hω (n + 1)
  rw [hn] at h₁
  rw [hns, hnss] at h₂
  change V ω (-(n : ℤ) - 1) - V ω ((-(n : ℤ) - 1) - 1) = _
  dsimp only [Function.comp_apply]
  rw [h₁, h₂]
  omega

section LDP

local notation "V" => busemannLDPMeasurableVersion

/-- CONDITIONAL LDP reduction of `item-busemann-ind`
left/right Busemann-process independence (`lem-geo-infty-ind` at zero,
shifts are discharged. This helper is not counted; F1/F4 remain. -/
theorem busemannLDPMeasurableVersion_ind_of_LR
    (hfrontR : ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂μ, ldpIncrement V 1 ω =
        F (codeSndFirstHit (-1) ω).toNat (codePastVector (codeSndFirstHit (-1)) ω)
          (fun j => V (codeShift (codeSndFirstHit (-1) ω).toNat ω) (-(j : ℤ))))
    (hfrontL : ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂μ, ldpIncrement V 0 ω =
        F (codeFstFirstHit (-1) ω).toNat (codePastVector (codeFstFirstHit (-1)) ω)
          (fun j => V (codeShift (codeFstFirstHit (-1) ω).toNat ω) (j : ℤ)))
    (hLR : IndepFun (fun ω (j : ℕ) => V ω (-(j : ℤ)))
      (fun ω (j : ℕ) => V ω (j : ℤ)) μ) :
    iIndepFun (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω)
      iidCodeMeasure := by
  exact iIndepFun_increment_of_LR V measurable_busemannLDPMeasurableVersion
    busemannLDPMeasurableVersion_zero
    busemannLDPMeasurableVersion_right_increment_shift
    (left_increment_shift_of_value_shift V
      (busemannLDPMeasurableVersion_left_shift_identity (-1) (by omega)))
    hfrontR hfrontL hLR

end LDP

section SDP

local notation "V" => busemannSDPMeasurableVersion

/-- CONDITIONAL SDP reduction of `item-busemann-ind`
left/right Busemann-process independence (`lem-geo-infty-ind` at zero,
shifts are discharged. This helper is not counted; F1/F4 remain. -/
theorem busemannSDPMeasurableVersion_ind_of_LR
    (hfrontR : ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂μ, SDPMasterFromLaw.increment V 1 ω =
        F (codeSndFirstHit (-1) ω).toNat (codePastVector (codeSndFirstHit (-1)) ω)
          (fun j => V (codeShift (codeSndFirstHit (-1) ω).toNat ω) (-(j : ℤ))))
    (hfrontL : ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂μ, SDPMasterFromLaw.increment V 0 ω =
        F (codeFstFirstHit (-1) ω).toNat (codePastVector (codeFstFirstHit (-1)) ω)
          (fun j => V (codeShift (codeFstFirstHit (-1) ω).toNat ω) (j : ℤ)))
    (hLR : IndepFun (fun ω (j : ℕ) => V ω (-(j : ℤ)))
      (fun ω (j : ℕ) => V ω (j : ℤ)) μ) :
    iIndepFun (fun k ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω)
      iidCodeMeasure := by
  exact iIndepFun_increment_of_LR V measurable_busemannSDPMeasurableVersion
    busemannSDPMeasurableVersion_zero
    busemannSDPMeasurableVersion_right_increment_shift
    (left_increment_shift_of_value_shift V
      (busemannSDPMeasurableVersion_left_shift_identity (-1) (by omega)))
    hfrontR hfrontL hLR

end SDP

end DirectedDistances.Recursive
