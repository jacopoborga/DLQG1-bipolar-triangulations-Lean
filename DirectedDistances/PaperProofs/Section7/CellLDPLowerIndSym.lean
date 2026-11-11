module

public import DirectedDistances.PaperProofs.Section7.CellLDPLowerGeodesic
import DirectedDistances.Recursive.BusemannItemsIndSym

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Filter Asymptotics
open Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open scoped ENNReal Topology

/-- Only Theorem 1.7(i) (`hind`) and 1.7(iv) at index 0 (`hsym`) remain; the
absolute-tail asymptotic is converted using a strictly smaller constant.
The source-identification gates F1/F4 apply to the measurable Busemann
representative. This is not the paper result. -/
theorem ldp_habs_of_ind_sym
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
        iidCodeMeasure.map
          (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∃ c x₀ : ℝ, 0 < c ∧ 0 < x₀ ∧ ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤ iidCodeMeasure.real
        {ω | x ≤ |(ldpIncrement busemannLDPMeasurableVersion 0 ω : ℝ)|} := by
  obtain ⟨c₁, hc₁, _, htail⟩ :=
    busemann_tail_ldp_of_ind_sym hind hsym
  let ρ : ℝ := -(2 / 3 : ℝ)
  let F : ℝ → ℝ := fun x => iidCodeMeasure.real
    {ω | x ≤ |(ldpIncrement busemannLDPMeasurableVersion 0 ω : ℝ)|}
  have htail' : (fun x : ℝ => F x - 2 * c₁ * x ^ ρ) =o[atTop]
      (fun x : ℝ => x ^ ρ) := by
    simpa only [F, ρ, ldpIncrement, zero_sub] using htail
  have hratio : Tendsto (fun x : ℝ => F x / x ^ ρ) atTop
      (𝓝 (2 * c₁)) := by
    have ht := htail'.tendsto_div_nhds_zero.add_const (2 * c₁)
    simp only [zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [sub_div, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hx ρ).ne']
    exact sub_add_cancel _ _
  have hEventually : ∀ᶠ x : ℝ in atTop, c₁ < F x / x ^ ρ :=
    (tendsto_order.1 hratio).1 c₁ (by linarith only [hc₁])
  obtain ⟨b, hb⟩ := (eventually_atTop.1 hEventually)
  refine ⟨c₁ / 4, max b 1, by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  have hxpos : 0 < x :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right b 1) hx)
  have hden : 0 < x ^ ρ := Real.rpow_pos_of_pos hxpos ρ
  have hlarge : c₁ < F x / x ^ ρ :=
    hb x (le_trans (le_max_left b 1) hx)
  have hmul : c₁ * x ^ ρ < F x := (lt_div_iff₀ hden).1 hlarge
  have hcoeff : 2 * (c₁ / 4) ≤ c₁ := by linarith only [hc₁]
  calc
    2 * (c₁ / 4) * x ^ ρ ≤ c₁ * x ^ ρ :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (le_of_lt hxpos) ρ)
    _ ≤ F x := hmul.le




theorem cell_ldp_lower_of_ind_sym
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
        iidCodeMeasure.map
          (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
        1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
          c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
          iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
            (fun i => ω (i + 1)) n, ∃ q : Path a b,
              A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  obtain ⟨c, x₀, hc, hx₀, habs⟩ := ldp_habs_of_ind_sym hind hsym
  exact cell_ldp_lower_of_items_geodesic hind hsym hc hx₀ habs ε hε

end DirectedDistances.PaperProofs.Section7
