/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section7.BoltzmannLDPUpper
public import DirectedDistances.PaperProofs.SourceResults.BoltzmannLDPLower
public import DirectedDistances.Paper.Section7.BoltzmannSDPLower
public import DirectedDistances.Paper.Section7.BoltzmannSDPUpper

/-! # Joint directed-distance bounds for the marked Boltzmann map

the same law identified in Lemma 7.9. One constant works for every positive right
boundary length, and all three source clauses hold on one event. The SDP lower
bound is to some right-boundary vertex; SDP retains `+∞` for unreachable vertices. -/

public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section7

/-- one joint event for the LDP bounds, source-to-sink SDP upper bound, and SDP lower -/
theorem thm_boltzmann_ldp (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q : RightVertexMarkedBoltzmannSpace r |
          (A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (ldpLengthBase q.1.2.2.out.B : ℝ) ∧
            (ldpLengthBase q.1.2.2.out.B : ℝ) ≤ A * (r : ℝ) ^ (3 / 2 : ℝ)) ∧
          ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
              ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ)) ∧
          ∃ i : Fin (r + 1),
            ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)) ≤
              ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
                q.1.2.2.out.B.source (rightBoundaryVertex q i))} := by
  have hε : 0 < δ / 4 := by linarith only [hδ]
  have hεlt : δ / 4 < 1 := by linarith only [hδlt]
  obtain ⟨A₁, hA₁, h₁⟩ :=
    DirectedDistances.PaperProofs.SourceResults.boltzmann_ldp_lower (δ / 4) hε hεlt
  obtain ⟨A₂, hA₂, h₂⟩ :=
    DirectedDistances.Paper.Section7.boltzmann_ldp_upper (δ / 4) hε hεlt
  obtain ⟨A₃, hA₃, h₃⟩ :=
    DirectedDistances.Paper.Section7.boltzmann_sdp_upper (δ / 4) hε
  obtain ⟨A₄, hA₄, h₄⟩ :=
    DirectedDistances.Paper.Section7.boltzmann_sdp_lower (δ / 4) hε
  let A := max (max A₁ A₂) (max A₃ A₄)
  have h₁A : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have h₂A : A₂ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  have h₃A : A₃ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have h₄A : A₄ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA : 1 < A := hA₁.trans_le h₁A
  have hApos : 0 < A := zero_lt_one.trans hA
  refine ⟨A, hA, fun r hr => ?_⟩
  let μ := rightVertexMarkedBoltzmannLaw r
  let : IsProbabilityMeasure μ :=
    (DirectedDistances.Paper.Section3.boltzmann_finite r hr).2.2.2
  let E₁ : Set (RightVertexMarkedBoltzmannSpace r) :=
    {q | A₁⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (ldpLengthBase q.1.2.2.out.B : ℝ)}
  let E₂ : Set (RightVertexMarkedBoltzmannSpace r) :=
    {q | (ldpLengthBase q.1.2.2.out.B : ℝ) ≤ A₂ * (r : ℝ) ^ (3 / 2 : ℝ)}
  let E₃ : Set (RightVertexMarkedBoltzmannSpace r) :=
    {q | ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
        q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
      ENNReal.ofReal (A₃ * (r : ℝ) ^ (3 / 4 : ℝ))}
  let E₄ := rightBoundarySDPEvent r
    (ENNReal.ofReal (A₄⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)))
  have hinter (s t : Set (RightVertexMarkedBoltzmannSpace r)) :
      μ.real s + μ.real t - 1 ≤ μ.real (s ∩ t) := by
    have ht : MeasurableSet t := by trivial
    have hu : μ.real (s ∪ t) ≤ 1 := by
      calc
        μ.real (s ∪ t) ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = 1 := probReal_univ
    have hi := measureReal_union_add_inter (μ := μ) (s := s) ht
    linarith only [hi, hu]
  have hp₁ : 1 - δ / 4 ≤ μ.real E₁ := h₁ r hr
  have hp₂ : 1 - δ / 4 ≤ μ.real E₂ := h₂ r hr
  have hp₃ : 1 - δ / 4 ≤ μ.real E₃ := h₃ r hr
  have hp₄ : 1 - δ / 4 ≤ μ.real E₄ := h₄ r hr
  have hp : 1 - δ ≤ μ.real ((E₁ ∩ E₂) ∩ (E₃ ∩ E₄)) := by
    have h12 := hinter E₁ E₂
    have h34 := hinter E₃ E₄
    have h1234 := hinter (E₁ ∩ E₂) (E₃ ∩ E₄)
    linarith only [hp₁, hp₂, hp₃, hp₄, h12, h34, h1234]
  apply hp.trans
  refine measureReal_mono ?_
  rintro q ⟨⟨hq₁, hq₂⟩, hq₃, hq₄⟩
  have hp32 : 0 ≤ (r : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hp34 : 0 ≤ (r : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have hinv₁ : A⁻¹ ≤ A₁⁻¹ :=
    (inv_le_inv₀ hApos (zero_lt_one.trans hA₁)).2 h₁A
  have hinv₄ : A⁻¹ ≤ A₄⁻¹ :=
    (inv_le_inv₀ hApos (zero_lt_one.trans hA₄)).2 h₄A
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hinv₁ hp32).trans hq₁
  · exact hq₂.trans (mul_le_mul_of_nonneg_right h₂A hp32)
  · exact hq₃.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right h₃A hp34))
  · exact rightBoundarySDPEvent_antitone r
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hinv₄ hp34)) hq₄

end DirectedDistances.PaperProofs.Section1
