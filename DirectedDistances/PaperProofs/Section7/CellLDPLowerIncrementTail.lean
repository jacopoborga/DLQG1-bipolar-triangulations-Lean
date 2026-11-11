/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.LDPMasterFromLaw
public import DirectedDistances.Probability.LowerTailProduct

/-! Supporting lemmas for paper labels `lem-cell-ldp-lower` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory DirectedDistances.Recursive

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (Y : Ω → ℤ → ℤ)





theorem ldp_nonpos_index_positive_tail
    (hmeas : ∀ k, Measurable (fun ω => ldpIncrement Y k ω))
    (hstat : ∀ k : ℤ, k ≤ 0 →
      μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 0))
    (hsym : μ.map (ldpIncrement Y 0) =
      μ.map (fun ω => -ldpIncrement Y 0 ω))
    {c x₀ : ℝ} (_hc : 0 < c) (hx₀ : 0 < x₀)
    (habs : ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤
        μ.real {ω | x ≤ |(ldpIncrement Y 0 ω : ℝ)|}) :
    ∀ k : ℤ, k ≤ 0 → ∀ x ≥ x₀,
      c * x ^ (-(2 / 3 : ℝ)) ≤
        μ.real {ω | x ≤ (ldpIncrement Y k ω : ℝ)} := by
  intro k hk x hx
  let S : Set ℤ := {z | x ≤ (z : ℝ)}
  have hS : MeasurableSet S := by
    simp [S]
  have hstat' := congrArg (fun ν : Measure ℤ => ν.real S) (hstat k hk)
  rw [MeasureTheory.map_measureReal_apply (hmeas k) hS,
    MeasureTheory.map_measureReal_apply (hmeas 0) hS] at hstat'
  have hpos : μ.real {ω | x ≤ (ldpIncrement Y k ω : ℝ)} =
      μ.real {ω | x ≤ (ldpIncrement Y 0 ω : ℝ)} := by
    simpa [S, Set.preimage] using hstat'
  have hsym' := congrArg (fun ν : Measure ℤ => ν.real S) hsym
  rw [MeasureTheory.map_measureReal_apply (hmeas 0) hS,
    MeasureTheory.map_measureReal_apply (f := fun ω => -ldpIncrement Y 0 ω)
      (measurable_neg.comp (hmeas 0)) hS] at hsym'
  have hreflection :
      μ.real {ω | x ≤ (ldpIncrement Y 0 ω : ℝ)} =
        μ.real {ω | x ≤ -(ldpIncrement Y 0 ω : ℝ)} := by
    simpa [S, Set.preimage] using hsym'
  let P : Set Ω := {ω | x ≤ (ldpIncrement Y 0 ω : ℝ)}
  let N : Set Ω := {ω | x ≤ -(ldpIncrement Y 0 ω : ℝ)}
  let B : Set Ω := {ω | x ≤ |(ldpIncrement Y 0 ω : ℝ)|}
  have hB : B = P ∪ N := by
    ext ω
    simp only [B, P, N, Set.mem_ofPred_eq, Set.mem_union]
    by_cases hd : 0 ≤ (ldpIncrement Y 0 ω : ℝ)
    · rw [abs_of_nonneg hd]
      constructor
      · exact Or.inl
      · rintro (hp | hn)
        · exact hp
        · have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
          linarith
    · rw [abs_of_neg (lt_of_not_ge hd)]
      constructor
      · exact Or.inr
      · rintro (hp | hn)
        · have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
          linarith
        · exact hn
  have hdisj : Disjoint P N := by
    apply Set.disjoint_left.mpr
    intro ω hp hn
    have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
    dsimp [P, N] at hp hn
    linarith
  have hPmeas : MeasurableSet P := by
    simpa [P, S, Set.preimage] using hS.preimage (hmeas 0)
  have hNmeas : MeasurableSet N := by
    simpa [N, S, Set.preimage] using
      hS.preimage (measurable_neg.comp (hmeas 0))
  have hBmass : μ.real B = 2 * μ.real P := by
    calc
      μ.real B = μ.real (P ∪ N) := congrArg (fun s : Set Ω => μ.real s) hB
      _ = μ.real P + μ.real N := MeasureTheory.measureReal_union hdisj hNmeas
      _ = 2 * μ.real P := by rw [← hreflection]; ring
  have habs' := habs x hx
  change 2 * c * x ^ (-(2 / 3 : ℝ)) ≤ μ.real B at habs'
  have hP0 : c * x ^ (-(2 / 3 : ℝ)) ≤ μ.real P := by
    rw [hBmass] at habs'
    linarith
  change c * x ^ (-(2 / 3 : ℝ)) ≤
    μ.real {ω | x ≤ (ldpIncrement Y k ω : ℝ)}
  rw [hpos]
  exact hP0





theorem ldp_lower_product_step
    (hmeasInc : ∀ k, Measurable (fun ω => ldpIncrement Y k ω))
    (hmeas : ∀ j : ℕ,
      Measurable (fun ω => (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ)))
    (hind : iIndepFun
      (fun (j : ℕ) ω => (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ)) μ)
    (hstat : ∀ k : ℤ, k ≤ 0 →
      μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 0))
    (hsym : μ.map (ldpIncrement Y 0) =
      μ.map (fun ω => -ldpIncrement Y 0 ω))
    {c x₀ : ℝ} (hc : 0 < c) (hx₀ : 0 < x₀)
    (habs : ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤
        μ.real {ω | x ≤ |(ldpIncrement Y 0 ω : ℝ)|})
    (ε : ℝ) :
    ∃ c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
      x₀ ≤ A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) →
      1 - c₂ * Real.exp (-(c₃ * A ^ ε)) ≤
        μ.real {ω | ∃ j ∈ Finset.range
          ⌊A ^ (-2 / 3 + ε : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)⌋₊,
          A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤
            (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ)} := by
  obtain ⟨c₂, c₃, hc₂, hc₃, hprod⟩ :=
    DirectedDistances.Probability.lowerTail_exists_ge_prob_param
      (P := μ)
      (ξ := fun j ω => (ldpIncrement Y (-((j : ℤ) + 1)) ω : ℝ)) hmeas hind hc ε
  refine ⟨c₂, c₃, hc₂, hc₃, ?_⟩
  intro n hn A hA hcut
  apply hprod n hn A hA
  intro j
  have hk : -((j : ℤ) + 1) ≤ 0 := by omega
  have htail := ldp_nonpos_index_positive_tail
    (μ := μ) (Y := Y) hmeasInc hstat hsym hc hx₀ habs
    (-((j : ℤ) + 1)) hk (A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ)) hcut
  have hApos : 0 < A := by linarith
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      (A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ)) ^ (-(2 / 3 : ℝ)) =
        A ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [Real.mul_rpow (inv_nonneg.mpr (le_of_lt hApos))
      (Real.rpow_nonneg (le_of_lt hnpos) _)]
    have hA : A⁻¹ ^ (-(2 / 3 : ℝ)) = A ^ (2 / 3 : ℝ) := by
      rw [Real.inv_rpow (le_of_lt hApos), Real.rpow_neg (le_of_lt hApos)]
      norm_num
    have hn : ((n : ℝ) ^ (3 / 4 : ℝ)) ^ (-(2 / 3 : ℝ)) =
        (n : ℝ) ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hnpos)]
      congr 1; ring
    rw [hA, hn]
  rw [hpow] at htail
  simpa [mul_assoc] using htail

end DirectedDistances.PaperProofs.Section7
