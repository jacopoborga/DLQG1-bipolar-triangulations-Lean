module

public import DirectedDistances.Recursive.BusemannItemsIndSym
public import DirectedDistances.Recursive.BusemannTailSDPConditional
public import DirectedDistances.Probability.PowerTailBounds







public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk
open scoped ENNReal Topology

private theorem tendsto_normalized_of_remainder {F : ℝ → ℝ} {C ρ : ℝ}
    (h : (fun x => F x - C * x ^ ρ) =o[atTop] (fun x => x ^ ρ)) :
    Tendsto (fun x => F x / x ^ ρ) atTop (𝓝 C) := by
  have ht := h.tendsto_div_nhds_zero.add_const C
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [sub_div, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hx ρ).ne']
  exact sub_add_cancel _ _

private theorem shifted_squeeze_remainder {F H : ℝ → ℝ} {C ρ : ℝ}
    (h : (fun x => F x - C * x ^ ρ) =o[atTop] (fun x => x ^ ρ))
    (hbound : ∀ x, F (x + 1) ≤ H x ∧ H x ≤ F x) :
    (fun x => H x - C * x ^ ρ) =o[atTop] (fun x => x ^ ρ) := by
  have hn := tendsto_normalized_of_remainder h
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop := by
    apply tendsto_atTop_atTop.2
    intro b
    exact ⟨b, fun x hx => by linarith only [hx]⟩
  have hbase : Tendsto (fun x : ℝ => (x + 1) / x) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hratio : Tendsto (fun x : ℝ => (x + 1) ^ ρ / x ^ ρ) atTop (𝓝 1) := by
    have ht := hbase.rpow_const (p := ρ) (Or.inl one_ne_zero)
    simp only [Real.one_rpow] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact Real.div_rpow (by linarith only [hx]) (by linarith only [hx]) ρ
  have hu : Tendsto (fun x : ℝ => F (x + 1) / x ^ ρ) atTop (𝓝 C) := by
    have ht := (hn.comp hshift).mul hratio
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_mul_div_cancel₀ (Real.rpow_pos_of_pos (by linarith only [hx]) ρ).ne'
  apply DirectedDistances.Tauberian.isLittleO_sub_mul_rpow_of_tendsto
  apply hu.squeeze' hn
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (hbound x).1 (Real.rpow_pos_of_pos hx ρ).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (hbound x).2 (Real.rpow_pos_of_pos hx ρ).le

private theorem strict_abs_remainder_of_weak {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) {C ρ : ℝ}
    (h : (fun x => μ.real {ω | x ≤ |Y ω|} - C * x ^ ρ) =o[atTop]
      (fun x => x ^ ρ)) :
    (fun x => μ.real {ω | x < |Y ω|} - C * x ^ ρ) =o[atTop]
      (fun x => x ^ ρ) := by
  apply shifted_squeeze_remainder h
  intro x
  constructor
  · refine measureReal_mono ?_ (measure_ne_top μ _)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith only [hω]
  · refine measureReal_mono ?_ (measure_ne_top μ _)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact le_of_lt hω

private theorem tendsto_power_mul_of_remainder {F : ℝ → ℝ} {C ν : ℝ}
    (h : (fun x => F x - C * x ^ (-ν)) =o[atTop] (fun x => x ^ (-ν))) :
    Tendsto (fun x => x ^ ν * F x) atTop (𝓝 C) := by
  have hn := tendsto_normalized_of_remainder h
  have hp : Tendsto (fun x : ℝ => x ^ ν * x ^ (-ν)) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
  have ht := hn.mul hp
  have heq : (fun x : ℝ => F x / x ^ (-ν) * (x ^ ν * x ^ (-ν))) =ᶠ[atTop]
      (fun x => x ^ ν * F x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxρ : x ^ (-ν) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    field_simp [hxρ]
  have ht' := ht.congr' heq
  simpa only [mul_one] using ht'

private theorem symmetric_strict_abs_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Ω → ℤ) (hD : Measurable D)
    (hsym : μ.map D = μ.map (fun ω => -D ω)) {x : ℝ} (hx : 0 < x) :
    μ.real {ω | x < |(D ω : ℝ)|} = 2 * μ.real {ω | x < (D ω : ℝ)} := by
  let A : Set Ω := {ω | x < (D ω : ℝ)}
  let B : Set Ω := {ω | x < -((D ω : ℤ) : ℝ)}
  have hsymTail : μ.real A = μ.real B := by
    have hm := congrArg (fun ν : Measure ℤ => ν.real {z | x < (z : ℝ)}) hsym
    rw [map_measureReal_apply (f := D) hD MeasurableSet.of_discrete,
      map_measureReal_apply (f := fun ω => -D ω) (measurable_neg.comp hD)
        MeasurableSet.of_discrete] at hm
    simpa only [A, B, Set.preimage, Set.mem_ofPred_eq, Int.cast_neg] using hm
  have hset : {ω | x < |(D ω : ℝ)|} = A ∪ B := by
    ext ω
    simp only [Set.mem_ofPred_eq, A, B, Set.mem_union]
    by_cases hy : (D ω : ℝ) < 0
    · rw [abs_of_neg hy]
      constructor
      · intro h
        exact Or.inr h
      · intro h
        rcases h with h | h
        · linarith only [hx, hy, h]
        · exact h
    · have hy' : 0 ≤ (D ω : ℝ) := le_of_not_gt hy
      rw [abs_of_nonneg hy']
      constructor
      · intro h
        exact Or.inl h
      · intro h
        rcases h with h | h
        · exact h
        · linarith only [hx, hy', h]
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.2
    intro ω hA hB
    simp only [A, B, Set.mem_ofPred_eq] at hA hB
    linarith only [hx, hA, hB]
  have hAmeas : MeasurableSet A := by
    change MeasurableSet (D ⁻¹' {z : ℤ | x < (z : ℝ)})
    exact hD (MeasurableSet.of_discrete : MeasurableSet {z : ℤ | x < (z : ℝ)})
  have hBmeas : MeasurableSet B := by
    change MeasurableSet (D ⁻¹' {z : ℤ | x < -((z : ℝ))})
    exact hD (MeasurableSet.of_discrete :
      MeasurableSet {z : ℤ | x < -((z : ℝ))})
  calc
    μ.real {ω | x < |(D ω : ℝ)|} = μ.real (A ∪ B) := congrArg (fun s => μ.real s) hset
    _ = μ.real A + μ.real B := measureReal_union hdisj hBmeas
    _ = 2 * μ.real A := by rw [hsymTail]; ring

private theorem symmetric_strict_tail_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Ω → ℤ) (hD : Measurable D)
    (hsym : μ.map D = μ.map (fun ω => -D ω)) (x : ℝ) :
    μ.real {ω | x < (D ω : ℝ)} = μ.real {ω | x < -((D ω : ℝ))} := by
  have hm := congrArg (fun ν : Measure ℤ => ν.real {z | x < (z : ℝ)}) hsym
  rw [map_measureReal_apply (f := D) hD MeasurableSet.of_discrete,
    map_measureReal_apply (f := fun ω => -D ω) (measurable_neg.comp hD)
      MeasurableSet.of_discrete] at hm
  simpa only [Set.preimage, Set.mem_ofPred_eq, Int.cast_neg] using hm

section LDP

local notation "Y" => busemannLDPMeasurableVersion
local notation "D" => fun ω => (Y ω 0 - Y ω (-1) : ℤ)

variable
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement Y 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement Y 0 ω))

include hind hsym





theorem ldp_increment_powerTail_of_ind_sym :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      iidCodeMeasure.real {ω | x < |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} ≤
        C * x ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨c, hc, _, habs⟩ := busemann_tail_ldp_of_ind_sym hind hsym
  have hstrict := strict_abs_remainder_of_weak iidCodeMeasure
    (fun ω => (D ω : ℝ)) habs
  have hlim := tendsto_power_mul_of_remainder hstrict
  have hD : Measurable D := by
    exact (measurable_busemannLDPMeasurableVersion 0).sub
      (measurable_busemannLDPMeasurableVersion (-1))
  have hsymD : iidCodeMeasure.map D = iidCodeMeasure.map (fun ω => -D ω) := by
    have heq : ldpIncrement Y 0 = D := by
      funext ω
      change Y ω 0 - Y ω (0 - 1) = Y ω 0 - Y ω (-1)
      congr 1
    rw [heq] at hsym
    exact hsym
  have hplus : Tendsto (fun x : ℝ => x ^ (2 / 3 : ℝ) *
      iidCodeMeasure.real {ω | x < (D ω : ℝ)}) atTop (𝓝 c) := by
    have ht := hlim.mul_const (1 / 2 : ℝ)
    have hconst : (2 * c) * (1 / 2 : ℝ) = c := by ring
    rw [hconst] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [symmetric_strict_abs_eq iidCodeMeasure D hD hsymD hx]
    ring
  have hminus : Tendsto (fun x : ℝ => x ^ (2 / 3 : ℝ) *
      iidCodeMeasure.real {ω | x < -((D ω : ℝ))}) atTop (𝓝 c) := by
    apply hplus.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [symmetric_strict_tail_eq iidCodeMeasure D hD hsymD]
  have hY : Measurable (fun ω => (D ω : ℝ)) := by fun_prop
  exact DirectedDistances.Probability.exists_powerTailBound hY
    (by norm_num : (0 : ℝ) < 2 / 3) hplus hminus

end LDP

section SDP

local notation "Y" => busemannSDPMeasurableVersion
local notation "D" => fun ω => (Y ω 0 - Y ω (-1) : ℤ)

variable
    (hind : iIndepFun (fun k ω => SDPMasterFromLaw.increment Y k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment Y 0) =
      iidCodeMeasure.map (fun ω => -SDPMasterFromLaw.increment Y 0 ω))

include hind hsym





theorem sdp_increment_powerTail_of_ind_sym :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      iidCodeMeasure.real {ω | x < |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} ≤
        C * x ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨c, hc, _, habs⟩ := busemann_tail_sdp_of_ind_sym hind hsym
  have hstrict := strict_abs_remainder_of_weak iidCodeMeasure
    (fun ω => (D ω : ℝ)) habs
  have hlim := tendsto_power_mul_of_remainder hstrict
  have hD : Measurable D := by
    exact (measurable_busemannSDPMeasurableVersion 0).sub
      (measurable_busemannSDPMeasurableVersion (-1))
  have hsymD : iidCodeMeasure.map D = iidCodeMeasure.map (fun ω => -D ω) := by
    have heq : SDPMasterFromLaw.increment Y 0 = D := by
      funext ω
      change Y ω 0 - Y ω (0 - 1) = Y ω 0 - Y ω (-1)
      congr 1
    rw [heq] at hsym
    exact hsym
  have hplus : Tendsto (fun x : ℝ => x ^ (4 / 3 : ℝ) *
      iidCodeMeasure.real {ω | x < (D ω : ℝ)}) atTop (𝓝 c) := by
    have ht := hlim.mul_const (1 / 2 : ℝ)
    have hconst : (2 * c) * (1 / 2 : ℝ) = c := by ring
    rw [hconst] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [symmetric_strict_abs_eq iidCodeMeasure D hD hsymD hx]
    ring
  have hminus : Tendsto (fun x : ℝ => x ^ (4 / 3 : ℝ) *
      iidCodeMeasure.real {ω | x < -((D ω : ℝ))}) atTop (𝓝 c) := by
    apply hplus.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [symmetric_strict_tail_eq iidCodeMeasure D hD hsymD]
  have hY : Measurable (fun ω => (D ω : ℝ)) := by fun_prop
  exact DirectedDistances.Probability.exists_powerTailBound hY
    (by norm_num : (0 : ℝ) < 4 / 3) hplus hminus

end SDP
end DirectedDistances.Recursive
