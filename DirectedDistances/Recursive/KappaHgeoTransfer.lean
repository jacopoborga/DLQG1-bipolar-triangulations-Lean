module

public import DirectedDistances.Recursive.KappaExclusionAnalytic
public import Mathlib.Probability.Independence.InfinitePi

/-! # Generic transfer of the SDP linear bound to the iid realization

These GENERIC probability helpers implement the law transfer used in
items `ind`, `stationary`, and `sym` of `thm-busemann-property`; they are NOT
proved here for the Busemann function. The hypothesis `hbound` is the
Busemann-side estimate being proved separately as `SDPIdentifyBusemann`.
None of these helpers is a paper statement, and no KMSW input is used. -/

public section

namespace DirectedDistances.Recursive.KappaHgeoTransfer

open MeasureTheory ProbabilityTheory
open DirectedDistances.Recursive.SDPExpansion
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℤ → ℤ)

/-- GENERIC integer increment, with the convention used at -/
@[expose] def increment (k : ℤ) (ω : Ω) : ℤ := Y ω k - Y ω (k - 1)

/-- GENERIC time-zero increment mass, as in `eq:den-dist-f-g`; -/
@[expose] noncomputable def incrementMass (x : ℤ) : ℝ :=
  μ.real {ω | increment Y 0 ω = x}

private theorem measurable_increment
    (hY : ∀ k, Measurable (fun ω => Y ω k)) (k : ℤ) :
    Measurable (increment Y k) :=
  (hY k).sub (hY (k - 1))

private theorem measurable_cast : Measurable (fun z : ℤ => (z : ℝ)) :=
  measurable_of_countable _

private theorem measurable_real_sequence
    (hY : ∀ k, Measurable (fun ω => Y ω k)) :
    Measurable (fun ω (i : ℕ) => (increment Y (-(i : ℤ)) ω : ℝ)) :=
  measurable_pi_iff.mpr (fun i : ℕ =>
    measurable_cast.comp (measurable_increment Y hY (-(i : ℤ))))

/-- GENERIC identification of the real increment law with `mu_f` of its -/
theorem real_increment_law
    (hY : ∀ k, Measurable (fun ω => Y ω k)) :
    μ.map (fun ω => (increment Y 0 ω : ℝ)) = mu_f (incrementMass μ Y) := by
  change μ.map ((fun z : ℤ => (z : ℝ)) ∘ increment Y 0) = _
  rw [← Measure.map_map measurable_cast (measurable_increment Y hY 0),
    Measure.map_eq_sum μ (increment Y 0) (measurable_increment Y hY 0),
    Measure.map_sum measurable_cast.aemeasurable]
  simp_rw [Measure.map_smul _ measurable_cast.aemeasurable,
    Measure.map_dirac' measurable_cast]
  unfold mu_f
  congr 1
  funext z
  congr 1
  exact (ENNReal.ofReal_toReal (measure_ne_top μ (increment Y 0 ⁻¹' {z}))).symm

omit [IsProbabilityMeasure μ] in
private theorem sequence_law
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hind : iIndepFun (increment Y) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (C : ℤ → ℝ) (hC : Measurable C) :
    μ.map (fun ω (i : ℕ) => C (increment Y (-(i : ℤ)) ω)) =
      Measure.infinitePi (fun _ : ℕ => μ.map (fun ω => C (increment Y 0 ω))) := by
  have hi : Function.Injective (fun i : ℕ => -(i : ℤ)) := by
    intro i j hij
    have hij' : (i : ℤ) = (j : ℤ) := neg_injective hij
    exact_mod_cast hij'
  have hn := iIndepFun.precomp (g := fun i : ℕ => -(i : ℤ)) hi hind
  have hr := hn.comp (fun _ => C) (fun _ => hC)
  have hprod : μ.map (fun ω (i : ℕ) => C (increment Y (-(i : ℤ)) ω)) =
      Measure.infinitePi (fun i : ℕ => μ.map (fun ω => C (increment Y (-(i : ℤ)) ω))) := by
    simpa only [Function.comp_def] using hr.map_fun_eq_infinitePi_map
      (fun i : ℕ => hC.comp (measurable_increment Y hY (-(i : ℤ))))
  rw [hprod]
  congr 1
  funext i
  change μ.map (C ∘ increment Y (-(i : ℤ))) = μ.map (C ∘ increment Y 0)
  rw [← Measure.map_map hC (measurable_increment Y hY (-(i : ℤ))),
    ← Measure.map_map hC (measurable_increment Y hY 0), hstatL _ (by omega)]

private theorem real_sequence_law
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hind : iIndepFun (increment Y) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0)) :
    μ.map (fun ω (i : ℕ) => (increment Y (-(i : ℤ)) ω : ℝ)) =
      Measure.infinitePi (fun _ : ℕ => mu_f (incrementMass μ Y)) := by
  rw [sequence_law μ Y hY hind hstatL _ measurable_cast, real_increment_law μ Y hY]

/-- GENERIC finite-vector law transfer from independence and left stationarity,
the law forms of items `ind` and `stationary` of `thm-busemann-property`.
These properties are not proved for the Busemann function here -/
theorem negative_increment_vector_law
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hind : iIndepFun (increment Y) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (k : ℕ) :
    μ.map (fun ω (i : Fin k) => (increment Y (-(i : ℤ)) ω : ℝ)) =
      (Measure.infinitePi (fun _ : ℕ => mu_f (incrementMass μ Y))).map
        (fun ω (i : Fin k) => ω i) := by
  rw [← real_sequence_law μ Y hY hind hstatL,
    Measure.map_map (by fun_prop) (measurable_real_sequence Y hY)]
  rfl

omit [MeasurableSpace Ω] in
/-- GENERIC telescoping identity, with the sign and endpoints required by -/
theorem sum_negative_increments
    (h0 : ∀ ω, Y ω 0 = 0) (k : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range k, (increment Y (-(i : ℤ)) ω : ℝ)) =
      ((-Y ω (-(k : ℤ))) : ℝ) := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [increment, Int.cast_sub]
    rw [show -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 by omega]
    ring

/-- GENERIC equality of the iid upper-bound event and the event for `-Y(-k)`; -/
theorem iid_sum_probability_eq_neg
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (increment Y) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (c : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => mu_f (incrementMass μ Y))).real
        {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ c} =
      μ.real {ω | ((-Y ω (-(k : ℤ))) : ℝ) ≤ c} := by
  rw [← real_sequence_law μ Y hY hind hstatL,
    map_measureReal_apply
      (measurable_real_sequence Y hY)
      (measurableSet_le (Finset.measurable_fun_sum _ (fun i _ => measurable_pi_apply i))
        measurable_const)]
  congr 1
  ext ω
  change (∑ i ∈ Finset.range k, (increment Y (-(i : ℤ)) ω : ℝ)) ≤ c ↔
    ((-Y ω (-(k : ℤ))) : ℝ) ≤ c
  rw [sum_negative_increments Y h0]

/-- GENERIC symmetry of the sum of the negative-time increments. Independence
and the law forms of items `stationary` and `sym` of `thm-busemann-property`
are assumptions, not Busemann results proved here -/
theorem sum_negative_increments_symmetric
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hind : iIndepFun (increment Y) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (hsym : μ.map (increment Y 0) = μ.map (fun ω => -increment Y 0 ω))
    (k : ℕ) :
    μ.map (fun ω => ∑ i ∈ Finset.range k, (increment Y (-(i : ℤ)) ω : ℝ)) =
      μ.map (fun ω => -(∑ i ∈ Finset.range k, (increment Y (-(i : ℤ)) ω : ℝ))) := by
  have hneg : μ.map (fun ω => -(increment Y 0 ω : ℝ)) =
      μ.map (fun ω => (increment Y 0 ω : ℝ)) := by
    calc
      _ = (μ.map (fun ω => -increment Y 0 ω)).map (fun z : ℤ => (z : ℝ)) := by
        rw [Measure.map_map (f := fun ω => -increment Y 0 ω)
          measurable_cast (measurable_increment Y hY 0).neg]
        simp only [Function.comp_def, Int.cast_neg]
      _ = (μ.map (increment Y 0)).map (fun z : ℤ => (z : ℝ)) := by rw [← hsym]
      _ = _ := Measure.map_map measurable_cast (measurable_increment Y hY 0)
  have hreflected : μ.map (fun ω (i : ℕ) => -(increment Y (-(i : ℤ)) ω : ℝ)) =
      μ.map (fun ω (i : ℕ) => (increment Y (-(i : ℤ)) ω : ℝ)) := by
    rw [sequence_law μ Y hY hind hstatL (fun z : ℤ => -(z : ℝ)) measurable_cast.neg,
      sequence_law μ Y hY hind hstatL (fun z : ℤ => (z : ℝ)) measurable_cast, hneg]
  have hs := congrArg
    (fun ν : Measure (ℕ → ℝ) => ν.map (fun ω => ∑ i ∈ Finset.range k, ω i))
    hreflected
  have hmneg : Measurable (fun ω (i : ℕ) => -(increment Y (-(i : ℤ)) ω : ℝ)) :=
    measurable_pi_iff.mpr (fun i : ℕ =>
      (measurable_cast.comp (measurable_increment Y hY (-(i : ℤ)))).neg)
  rw [Measure.map_map
      (Finset.measurable_fun_sum _ (fun i _ => measurable_pi_apply i))
      hmneg,
    Measure.map_map
      (Finset.measurable_fun_sum _ (fun i _ => measurable_pi_apply i))
      (measurable_real_sequence Y hY)] at hs
  simpa only [Function.comp_def, Finset.sum_neg_distrib] using hs.symm

/-- GENERIC event transfer including reflection symmetry, used at
proved for the Busemann function in this helper. -/
theorem iid_sum_probability_eq
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (increment Y) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (hsym : μ.map (increment Y 0) = μ.map (fun ω => -increment Y 0 ω))
    (c : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => mu_f (incrementMass μ Y))).real
        {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ c} =
      μ.real {ω | (Y ω (-(k : ℤ)) : ℝ) ≤ c} := by
  rw [iid_sum_probability_eq_neg μ Y hY h0 hind hstatL c k]
  have hs := congrArg (fun ν : Measure ℝ => ν.real (Set.Iic c))
    (sum_negative_increments_symmetric μ Y hY hind hstatL hsym k)
  have hm : Measurable (fun ω =>
      ∑ i ∈ Finset.range k, (increment Y (-(i : ℤ)) ω : ℝ)) :=
    Finset.measurable_fun_sum _ (fun i _ =>
      measurable_cast.comp (measurable_increment Y hY (-(i : ℤ))))
  rw [map_measureReal_apply hm measurableSet_Iic,
    map_measureReal_apply (f := fun ω =>
      -(∑ i ∈ Finset.range k, (increment Y (-(i : ℤ)) ω : ℝ)))
      hm.neg measurableSet_Iic] at hs
  simpa only [Set.preimage, Set.mem_Iic, sum_negative_increments Y h0,
    Int.cast_neg, neg_neg] using hs

/-- GENERIC transfer to the exact canonical iid bound consumed by
`sdp_kappa_eq_zero_of_linear_bound`. The input `hbound` is the Busemann-side
estimate being proved separately as `SDPIdentifyBusemann`
`stationary`, and `sym` of `thm-busemann-property` are assumed here and are NOT
proved for the Busemann function. This helper is not a paper statement. -/
theorem hgeo_of_linear_bound
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (increment Y) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (hsym : μ.map (increment Y 0) = μ.map (fun ω => -increment Y 0 ω))
    (hbound : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ, 1 ≤ k →
      1 - δ ≤ μ.real {ω | (Y ω (-(k : ℤ)) : ℝ) ≤ 2 * A * (k : ℝ) + 1}) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤ (Measure.infinitePi (fun _ : ℕ => mu_f (incrementMass μ Y))).real
        {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1} := by
  intro δ hδ
  obtain ⟨A, hA⟩ := hbound δ hδ
  refine ⟨max A 0, fun k => ?_⟩
  rw [iid_sum_probability_eq μ Y hY h0 hind hstatL hsym]
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, neg_zero, h0, Int.cast_zero, mul_zero, zero_add,
      zero_le_one, Set.ofPred_true, probReal_univ]
    linarith only [hδ]
  · have hk1 : 1 ≤ k := by omega
    have hthreshold : 2 * A * (k : ℝ) + 1 ≤ 2 * max A 0 * (k : ℝ) + 1 := by
      have ht := mul_le_mul_of_nonneg_right (le_max_left A 0)
        (show 0 ≤ 2 * (k : ℝ) by positivity)
      linarith only [ht]
    exact (hA k hk1).trans (measureReal_mono (μ := μ)
      (fun ω hω => hω.trans hthreshold))

end DirectedDistances.Recursive.KappaHgeoTransfer
