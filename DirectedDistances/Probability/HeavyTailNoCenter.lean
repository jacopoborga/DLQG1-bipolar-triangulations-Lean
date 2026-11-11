module

public import DirectedDistances.Probability.TwoSidedFluctuation

/-! # Fluctuation bound for heavy-tailed walks with index `alpha < 1`, no centering

For `alpha ∈ (0, 1)` no centering is needed: on the event that no increment among the first `k`
exceeds `t = A k ^ (1 / alpha)` in absolute value, the walk is bounded by the sum of truncated
absolute values, whose mean is controlled by the dyadic-shell first-moment bound.  The Busemann
laws and tails must come from `busemann-property` / `busemann-tail`. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section Maximal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Absolute value truncated at level `t`: keep `|x|` when `|x| ≤ t`, else `0`. -/
private noncomputable def absTrunc (t x : ℝ) : ℝ := if |x| ≤ t then |x| else 0

private lemma measurable_absTrunc (t : ℝ) : Measurable (absTrunc t) := by
  show Measurable (fun x : ℝ => if |x| ≤ t then |x| else 0)
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    continuous_abs.measurable measurable_const

private lemma absTrunc_nonneg (t x : ℝ) : 0 ≤ absTrunc t x := by
  unfold absTrunc
  split_ifs <;> simp

private lemma absTrunc_le_self (t x : ℝ) : absTrunc t x ≤ |x| := by
  unfold absTrunc
  split_ifs with h
  · exact le_rfl
  · exact abs_nonneg _

private lemma absTrunc_le_level {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : absTrunc t x ≤ t := by
  unfold absTrunc
  split_ifs with h
  · exact h
  · exact ht

private lemma integrable_of_abs_le' {f : Ω → ℝ} (hf : Measurable f) (B : ℝ)
    (h : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact h ω)

private lemma exists_shell' (t x : ℝ) (ht : 0 < t) (hx : t < x) :
    ∃ n : ℕ, t * 2 ^ n < x ∧ x ≤ t * 2 ^ (n + 1) := by
  classical
  have h : ∃ n : ℕ, x ≤ t * 2 ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / t) (one_lt_two : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ht] at hn
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    nlinarith [mul_le_mul_of_nonneg_left h2 ht.le]
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  by_cases h0 : Nat.find h = 0
  · rw [h0]
    simpa using hx
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hmin := Nat.find_min h (show m < Nat.find h by omega)
    push_neg at hmin
    rw [hm]
    exact hmin

private lemma exists_two_pow' (t : ℝ) (ht : 1 ≤ t) :
    ∃ N : ℕ, t ≤ 2 ^ N ∧ (2 : ℝ) ^ N ≤ 2 * t := by
  classical
  have h : ∃ N : ℕ, t ≤ 2 ^ N :=
    (pow_unbounded_of_one_lt t (one_lt_two : (1 : ℝ) < 2)).imp fun N hN => hN.le
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  by_cases h0 : Nat.find h = 0
  · rw [h0]
    norm_num
    linarith
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hmin := Nat.find_min h (show m < Nat.find h by omega)
    push_neg at hmin
    rw [hm, pow_succ]
    linarith

private lemma two_pow_rpow' (n : ℕ) (β : ℝ) :
    ((2 : ℝ) ^ n) ^ β = ((2 : ℝ) ^ β) ^ n := by
  rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_natCast]

private lemma absTrunc_le_shells (t : ℝ) (N : ℕ) (hN : t ≤ 2 ^ N) (x : ℝ) :
    absTrunc t x ≤ 1 + ∑ n ∈ Finset.range N,
      (2 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |x| then 1 else 0) := by
  have hterm : ∀ n ∈ Finset.range N,
      0 ≤ (2 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |x| then 1 else 0) := fun n _ =>
    mul_nonneg (by positivity) (by split_ifs <;> norm_num)
  have hnn := Finset.sum_nonneg hterm
  by_cases h1 : |x| ≤ t
  · have hz : absTrunc t x = |x| := by simp [absTrunc, h1]
    rw [hz]
    by_cases h2 : |x| ≤ 1
    · linarith
    · obtain ⟨n, hn1, hn2⟩ := exists_shell' 1 |x| one_pos (lt_of_not_ge h2)
      rw [one_mul] at hn1 hn2
      have hnN : n < N := by
        have : (2 : ℝ) ^ n < 2 ^ N := lt_of_lt_of_le hn1 (h1.trans hN)
        exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
      have hsingle := Finset.single_le_sum
        (f := fun n => (2 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |x| then 1 else 0)) hterm
        (Finset.mem_range.mpr hnN)
      simp only [if_pos hn1, mul_one] at hsingle
      linarith
  · have hz : absTrunc t x = 0 := by simp [absTrunc, h1]
    rw [hz]
    linarith

private lemma first_moment_trunc {X : Ω → ℝ} (hX : Measurable X) (α C : ℝ) (hα0 : 0 < α)
    (hα1 : α < 1) (hC : 0 < C)
    (htail : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |X ω|} ≤ C * x ^ (-α)) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t →
      ∫ ω, absTrunc t (X ω) ∂P ≤ D * t ^ (1 - α) := by
  classical
  have hβ : 0 < 1 - α := by linarith
  have hr : 1 < (2 : ℝ) ^ (1 - α) := Real.one_lt_rpow (by norm_num) hβ
  have hr1 : 0 < (2 : ℝ) ^ (1 - α) - 1 := by linarith
  have hpos : 0 ≤ 2 * C * (2 : ℝ) ^ (1 - α) / ((2 : ℝ) ^ (1 - α) - 1) :=
    div_nonneg (by positivity) hr1.le
  refine ⟨1 + 2 * C * (2 : ℝ) ^ (1 - α) / ((2 : ℝ) ^ (1 - α) - 1),
    add_pos_of_pos_of_nonneg one_pos hpos, ?_⟩
  intro t ht
  obtain ⟨N, hN1, hN2⟩ := exists_two_pow' t ht
  have hXabs : Measurable fun ω => |X ω| := continuous_abs.measurable.comp hX
  have hind_meas (n : ℕ) : MeasurableSet {ω | (2 : ℝ) ^ n < |X ω|} :=
    measurableSet_lt measurable_const hXabs
  have hind_int (n : ℕ) : ∫ ω, (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0) ∂P =
      P.real {ω | (2 : ℝ) ^ n < |X ω|} := by
    have hfun : (fun ω => if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0) =
        Set.indicator {ω | (2 : ℝ) ^ n < |X ω|} (fun _ => (1 : ℝ)) := by
      funext ω
      simp [Set.indicator_apply]
    rw [hfun, integral_indicator_const _ (hind_meas n)]
    simp
  have hind_integrable (n : ℕ) :
      Integrable (fun ω => if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0) P :=
    integrable_of_abs_le' (Measurable.ite (hind_meas n) measurable_const measurable_const) 1
      fun ω => by split_ifs <;> simp
  have hi : ∀ n ∈ Finset.range N, Integrable
      (fun ω => (2 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0)) P :=
    fun n _ => (hind_integrable n).const_mul _
  have hRint : Integrable (fun ω => 1 + ∑ n ∈ Finset.range N,
      (2 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0)) P :=
    (integrable_const _).add (integrable_finsetSum _ hi)
  have hR : ∫ ω, (1 + ∑ n ∈ Finset.range N,
      (2 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0)) ∂P =
      1 + ∑ n ∈ Finset.range N, (2 : ℝ) ^ (n + 1) * P.real {ω | (2 : ℝ) ^ n < |X ω|} := by
    rw [integral_add (integrable_const _) (integrable_finsetSum _ hi),
      integral_finsetSum _ hi]
    simp only [integral_const_mul, hind_int]
    simp
  have hZ : Integrable (fun ω => absTrunc t (X ω)) P :=
    integrable_of_abs_le' ((measurable_absTrunc t).comp hX) t fun ω => by
      rw [abs_of_nonneg (absTrunc_nonneg _ _)]
      exact absTrunc_le_level (by linarith) _
  have hmono : ∫ ω, absTrunc t (X ω) ∂P ≤ ∫ ω, (1 + ∑ n ∈ Finset.range N,
      (2 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0)) ∂P :=
    integral_mono hZ hRint fun ω => absTrunc_le_shells t N hN1 (X ω)
  rw [hR] at hmono
  have hterm : ∀ n ∈ Finset.range N, (2 : ℝ) ^ (n + 1) * P.real {ω | (2 : ℝ) ^ n < |X ω|} ≤
      2 * C * ((2 : ℝ) ^ (1 - α)) ^ n := by
    intro n _
    have h1 : P.real {ω | (2 : ℝ) ^ n < |X ω|} ≤ C * ((2 : ℝ) ^ n) ^ (-α) :=
      htail _ (one_le_pow₀ (by norm_num))
    have h2 : (2 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ (-α) = ((2 : ℝ) ^ (1 - α)) ^ n := by
      have h3 : (2 : ℝ) ^ (1 - α) = 2 * (2 : ℝ) ^ (-α) := by
        rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
      rw [two_pow_rpow', h3, mul_pow]
    calc (2 : ℝ) ^ (n + 1) * P.real {ω | (2 : ℝ) ^ n < |X ω|}
        ≤ (2 : ℝ) ^ (n + 1) * (C * ((2 : ℝ) ^ n) ^ (-α)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * C * ((2 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ (-α)) := by ring
      _ = 2 * C * ((2 : ℝ) ^ (1 - α)) ^ n := by rw [h2]
  have hsum : ∑ n ∈ Finset.range N, (2 : ℝ) ^ (n + 1) * P.real {ω | (2 : ℝ) ^ n < |X ω|} ≤
      2 * C * ∑ n ∈ Finset.range N, ((2 : ℝ) ^ (1 - α)) ^ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hgeom : ∑ n ∈ Finset.range N, ((2 : ℝ) ^ (1 - α)) ^ n ≤
      (2 : ℝ) ^ (1 - α) * t ^ (1 - α) / ((2 : ℝ) ^ (1 - α) - 1) := by
    have hid := geom_sum_mul ((2 : ℝ) ^ (1 - α)) N
    have hrN : ((2 : ℝ) ^ (1 - α)) ^ N ≤ (2 : ℝ) ^ (1 - α) * t ^ (1 - α) := by
      rw [← two_pow_rpow', ← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by positivity) hN2 hβ.le
    rw [le_div_iff₀ hr1]
    have : 0 ≤ ((2 : ℝ) ^ (1 - α)) ^ N := by positivity
    linarith
  have ht1 : 1 ≤ t ^ (1 - α) := Real.one_le_rpow ht hβ.le
  have hfinal : 2 * C * ∑ n ∈ Finset.range N, ((2 : ℝ) ^ (1 - α)) ^ n ≤
      2 * C * ((2 : ℝ) ^ (1 - α) * t ^ (1 - α) / ((2 : ℝ) ^ (1 - α) - 1)) :=
    mul_le_mul_of_nonneg_left hgeom (by positivity)
  have he : 2 * C * ((2 : ℝ) ^ (1 - α) * t ^ (1 - α) / ((2 : ℝ) ^ (1 - α) - 1)) =
      (2 * C * (2 : ℝ) ^ (1 - α) / ((2 : ℝ) ^ (1 - α) - 1)) * t ^ (1 - α) := by ring
  nlinarith

/-- Maximal inequality for partial sums of identically distributed variables with power-law
tails of index `alpha ∈ (0, 1)`, with no centering: with probability `1 - O(A ^ (-alpha))`, the
walk stays within `A * k ^ (1 / alpha)` up to time `k`.

laws/tails must come from `busemann-property` / `busemann-tail`; not a paper result. -/
theorem heavyTail_maximal_lt_one {xi : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (xi i))
    (hind : iIndepFun xi P) (hid : ∀ i, IdentDistrib (xi i) (xi 0) P P)
    (alpha C : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hC : 0 < C)
    (htail : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 0 ω|} ≤ C * x ^ (-alpha)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 ≤ A →
      P.real {ω | ∃ j ≤ k,
        A * (k : ℝ) ^ (1 / alpha) < |∑ i ∈ Finset.range j, xi i ω|} ≤ C' * A ^ (-alpha) := by
  obtain ⟨D, hD, hmom⟩ := first_moment_trunc (P := P) (hmeas 0) alpha C ha0 ha1 hC htail
  refine ⟨C + D, by positivity, ?_⟩
  intro k hk A hA
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = A * (k : ℝ) ^ (1 / alpha) := ⟨_, rfl⟩
  rw [← ht_def]
  have hkα : ((k : ℝ) ^ (1 / alpha)) ^ alpha = k := by
    rw [← Real.rpow_mul hkpos.le, one_div, inv_mul_cancel₀ ha0.ne', Real.rpow_one]
  have ht1 : 1 ≤ t := by
    rw [ht_def]
    exact one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hk' (by positivity))
  have ht0 : 0 < t := by linarith
  have htα : t ^ alpha = A ^ alpha * k := by
    rw [ht_def, Real.mul_rpow hA0.le (by positivity), hkα]
  have hAα : 0 < A ^ alpha := Real.rpow_pos_of_pos hA0 _
  have hAneg : A ^ (-alpha) = (A ^ alpha)⁻¹ := Real.rpow_neg hA0.le alpha
  have hZmeas (i : ℕ) : Measurable fun ω => absTrunc t (xi i ω) :=
    (measurable_absTrunc t).comp (hmeas i)
  have hZint (i : ℕ) : Integrable (fun ω => absTrunc t (xi i ω)) P :=
    integrable_of_abs_le' (hZmeas i) t fun ω => by
      rw [abs_of_nonneg (absTrunc_nonneg _ _)]
      exact absTrunc_le_level ht0.le _
  have hsub : {ω | ∃ j ≤ k, t < |∑ i ∈ Finset.range j, xi i ω|} ⊆
      (⋃ i ∈ Finset.range k, {ω | t < |xi i ω|}) ∪
        {ω | t ≤ ∑ i ∈ Finset.range k, absTrunc t (xi i ω)} := by
    rintro ω ⟨j, hj, hs⟩
    by_cases hU : ∃ i ∈ Finset.range k, t < |xi i ω|
    · left
      simpa using hU
    · right
      push_neg at hU
      have hrange : Finset.range j ⊆ Finset.range k := Finset.range_subset_range.mpr hj
      have h1 : |∑ i ∈ Finset.range j, xi i ω| ≤ ∑ i ∈ Finset.range j, |xi i ω| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ i ∈ Finset.range j, |xi i ω| = ∑ i ∈ Finset.range j, absTrunc t (xi i ω) :=
        Finset.sum_congr rfl fun i hi => by
          have := hU i (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hj))
          simp [absTrunc, this]
      have h3 : ∑ i ∈ Finset.range j, absTrunc t (xi i ω) ≤
          ∑ i ∈ Finset.range k, absTrunc t (xi i ω) :=
        Finset.sum_le_sum_of_subset_of_nonneg hrange fun i _ _ => absTrunc_nonneg _ _
      show t ≤ _
      linarith
  have hU : P.real (⋃ i ∈ Finset.range k, {ω | t < |xi i ω|}) ≤ C / A ^ alpha := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range k, P.real {ω | t < |xi i ω|} ≤ C * (A ^ alpha * k)⁻¹ := by
      intro i _
      have h := (hid i).measure_mem_eq (s := {x : ℝ | t < |x|})
        (measurableSet_lt measurable_const continuous_abs.measurable)
      have heq : P.real {ω | t < |xi i ω|} = P.real {ω | t < |xi 0 ω|} := by
        simp only [Measure.real]
        exact congrArg ENNReal.toReal h
      rw [heq]
      have := htail t ht1
      rwa [Real.rpow_neg ht0.le, htα] at this
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    apply le_of_eq
    field_simp
  have hV : P.real {ω | t ≤ ∑ i ∈ Finset.range k, absTrunc t (xi i ω)} ≤ D / A ^ alpha := by
    have hSint : Integrable (fun ω => ∑ i ∈ Finset.range k, absTrunc t (xi i ω)) P :=
      integrable_finsetSum _ fun i _ => hZint i
    have hmk := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all P fun ω => Finset.sum_nonneg fun i _ => absTrunc_nonneg t (xi i ω))
      hSint t
    have hEi : ∀ i : ℕ, ∫ ω, absTrunc t (xi i ω) ∂P = ∫ ω, absTrunc t (xi 0 ω) ∂P :=
      fun i => ((hid i).comp (measurable_absTrunc t)).integral_eq
    rw [integral_finsetSum _ fun i _ => hZint i,
      Finset.sum_congr rfl fun i _ => hEi i, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hmk
    have hm := hmom t ht1
    have key : t * P.real {ω | t ≤ ∑ i ∈ Finset.range k, absTrunc t (xi i ω)} ≤
        t * (D / A ^ alpha) := by
      calc t * P.real {ω | t ≤ ∑ i ∈ Finset.range k, absTrunc t (xi i ω)}
          ≤ k * ∫ ω, absTrunc t (xi 0 ω) ∂P := hmk
        _ ≤ k * (D * t ^ (1 - alpha)) := mul_le_mul_of_nonneg_left hm hkpos.le
        _ = t * (D / A ^ alpha) := by
            rw [Real.rpow_sub ht0, Real.rpow_one, htα]
            field_simp
    exact le_of_mul_le_mul_left key ht0
  calc P.real {ω | ∃ j ≤ k, t < |∑ i ∈ Finset.range j, xi i ω|}
      ≤ P.real ((⋃ i ∈ Finset.range k, {ω | t < |xi i ω|}) ∪
        {ω | t ≤ ∑ i ∈ Finset.range k, absTrunc t (xi i ω)}) := measureReal_mono hsub
    _ ≤ P.real (⋃ i ∈ Finset.range k, {ω | t < |xi i ω|}) +
        P.real {ω | t ≤ ∑ i ∈ Finset.range k, absTrunc t (xi i ω)} := measureReal_union_le _ _
    _ ≤ C / A ^ alpha + D / A ^ alpha := add_le_add hU hV
    _ = (C + D) * A ^ (-alpha) := by
        rw [hAneg, ← add_div, ← div_eq_mul_inv]

end Maximal

section TwoSided

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
private lemma sum_Ioc_pos' (xi : ℤ → Ω → ℝ) (ω : Ω) (j : ℕ) :
    ∑ i ∈ Finset.range j, xi ((i : ℤ) + 1) ω = ∑ x ∈ Finset.Ioc (0 : ℤ) j, xi x ω := by
  have hinj : Function.Injective (fun i : ℕ => (i : ℤ) + 1) := fun a b h => by
    simpa using h
  have : Finset.Ioc (0 : ℤ) j = (Finset.range j).map ⟨fun i : ℕ => (i : ℤ) + 1, hinj⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(x - 1).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [this, Finset.sum_map]
  rfl

omit mΩ in
private lemma sum_Ioc_neg' (xi : ℤ → Ω → ℝ) (ω : Ω) (m : ℕ) :
    ∑ i ∈ Finset.range m, xi (-(i : ℤ)) ω = ∑ x ∈ Finset.Ioc (-(m : ℤ)) 0, xi x ω := by
  have hinj : Function.Injective (fun i : ℕ => -(i : ℤ)) := fun a b h => by
    simpa using h
  have : Finset.Ioc (-(m : ℤ)) 0 = (Finset.range m).map ⟨fun i : ℕ => -(i : ℤ), hinj⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(-x).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [this, Finset.sum_map]
  rfl

omit mΩ in
private lemma sum_Ioc_consecutive_int (xi : ℤ → Ω → ℝ) (ω : Ω) {a b c : ℤ} (h1 : a ≤ b)
    (h2 : b ≤ c) :
    ∑ x ∈ Finset.Ioc a b, xi x ω + ∑ x ∈ Finset.Ioc b c, xi x ω =
      ∑ x ∈ Finset.Ioc a c, xi x ω := by
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Ioc] at hx hx'
    omega
  have hun : Finset.Ioc a b ∪ Finset.Ioc b c = Finset.Ioc a c := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [← hun, Finset.sum_union hdisj]

omit mΩ in
/-- The two-sided walk starts at `0`.

result. -/
theorem twoSidedWalk_zero (xi : ℤ → Ω → ℝ) (ω : Ω) : twoSidedWalk xi 0 ω = 0 := by
  simp [twoSidedWalk]

/-- The increments of the two-sided walk are `xi`: `X k - X (k - 1) = xi k` for all `k ∈ ℤ`.

result. -/
theorem twoSidedWalk_sub (xi : ℤ → Ω → ℝ) (ω : Ω) (k : ℤ) :
    twoSidedWalk xi k ω - twoSidedWalk xi (k - 1) ω = xi k ω := by
  have hone : ∑ x ∈ Finset.Ioc (k - 1) k, xi x ω = xi k ω := by
    have : Finset.Ioc (k - 1) k = {k} := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rw [this, Finset.sum_singleton]
  by_cases hk : 1 ≤ k
  · have h1 : 0 ≤ k := by omega
    have h2 : 0 ≤ k - 1 := by omega
    have hc := sum_Ioc_consecutive_int xi ω h2 (by omega : k - 1 ≤ k)
    simp only [twoSidedWalk, if_pos h1, if_pos h2]
    linarith
  · have h1 : ¬ (0 ≤ k - 1) := by omega
    have hc := sum_Ioc_consecutive_int xi ω (by omega : k - 1 ≤ k) (by omega : k ≤ 0)
    by_cases h0 : 0 ≤ k
    · have hk0 : k = 0 := by omega
      subst hk0
      simp only [twoSidedWalk, if_pos h0, if_neg h1]
      have hempty : Finset.Ioc (0 : ℤ) 0 = ∅ := by simp
      rw [hempty, Finset.sum_empty, hone]
      ring
    · simp only [twoSidedWalk, if_neg h0, if_neg h1]
      linarith

/-- Two-sided fluctuation bound for `alpha ∈ (0, 1)` without centering: with independent
increments identically distributed for `k ≥ 1` and for `k ≤ 0`, with power-law tails of index
`alpha`, `P[∃ l ∈ [-k, k], A k ^ (1 / alpha) < |X l|] ≤ C' A ^ (-alpha)`.

laws/tails must come from `busemann-property` / `busemann-tail`; not a paper result. -/
theorem twoSidedWalk_fluctuation_lt_one {P : Measure Ω} [IsProbabilityMeasure P]
    {xi : ℤ → Ω → ℝ} (hmeas : ∀ k, Measurable (xi k)) (hind : iIndepFun xi P)
    (hidPos : ∀ k : ℤ, 1 ≤ k → IdentDistrib (xi k) (xi 1) P P)
    (hidNeg : ∀ k : ℤ, k ≤ 0 → IdentDistrib (xi k) (xi 0) P P)
    (alpha Cp Cn : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hCp : 0 < Cp) (hCn : 0 < Cn)
    (htailPos : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 1 ω|} ≤ Cp * x ^ (-alpha))
    (htailNeg : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 0 ω|} ≤ Cn * x ^ (-alpha)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 ≤ A →
      P.real {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} ≤ C' * A ^ (-alpha) := by
  have hinjP : Function.Injective (fun i : ℕ => (i : ℤ) + 1) := fun a b h => by
    simpa using h
  have hinjN : Function.Injective (fun i : ℕ => -(i : ℤ)) := fun a b h => by
    simpa using h
  obtain ⟨Cp', hCp', hP⟩ := heavyTail_maximal_lt_one (P := P)
    (xi := fun (i : ℕ) => xi ((i : ℤ) + 1)) (fun i => hmeas _) (hind.precomp hinjP)
    (fun i => by
      simpa using hidPos ((i : ℤ) + 1) (by omega))
    alpha Cp ha0 ha1 hCp (by simpa using htailPos)
  obtain ⟨Cn', hCn', hN⟩ := heavyTail_maximal_lt_one (P := P)
    (xi := fun (i : ℕ) => xi (-(i : ℤ))) (fun i => hmeas _) (hind.precomp hinjN)
    (fun i => by
      simpa using hidNeg (-(i : ℤ)) (by omega))
    alpha Cn ha0 ha1 hCn (by simpa using htailNeg)
  refine ⟨Cp' + Cn', by positivity, ?_⟩
  intro k hk A hA
  have hsub : {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} ⊆
      {ω | ∃ j ≤ k, A * (k : ℝ) ^ (1 / alpha) <
          |∑ i ∈ Finset.range j, xi ((i : ℤ) + 1) ω|} ∪
        {ω | ∃ j ≤ k, A * (k : ℝ) ^ (1 / alpha) <
          |∑ i ∈ Finset.range j, xi (-(i : ℤ)) ω|} := by
    rintro ω ⟨l, hl1, hl2, hl⟩
    by_cases h0 : 0 ≤ l
    · left
      refine ⟨l.toNat, by omega, ?_⟩
      rw [sum_Ioc_pos', Int.toNat_of_nonneg h0]
      simpa [twoSidedWalk, h0] using hl
    · right
      refine ⟨(-l).toNat, by omega, ?_⟩
      rw [sum_Ioc_neg', Int.toNat_of_nonneg (by omega), neg_neg]
      simpa [twoSidedWalk, h0] using hl
  calc P.real {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|}
      ≤ P.real ({ω | ∃ j ≤ k, A * (k : ℝ) ^ (1 / alpha) <
          |∑ i ∈ Finset.range j, xi ((i : ℤ) + 1) ω|} ∪
        {ω | ∃ j ≤ k, A * (k : ℝ) ^ (1 / alpha) <
          |∑ i ∈ Finset.range j, xi (-(i : ℤ)) ω|}) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ Cp' * A ^ (-alpha) + Cn' * A ^ (-alpha) := add_le_add (hP k hk A hA) (hN k hk A hA)
    _ = (Cp' + Cn') * A ^ (-alpha) := by ring

/-- Corollary in the source's form for `alpha ∈ (0, 1)`: with probability at least
`1 - C' A ^ (-alpha)`, `max_{|l| ≤ k} |X l| ≤ A k ^ (1 / alpha)`, with no centering.

laws/tails must come from `busemann-property` / `busemann-tail`; not a paper result. -/
theorem twoSidedWalk_max_le_lt_one {P : Measure Ω} [IsProbabilityMeasure P]
    {xi : ℤ → Ω → ℝ} (hmeas : ∀ k, Measurable (xi k)) (hind : iIndepFun xi P)
    (hidPos : ∀ k : ℤ, 1 ≤ k → IdentDistrib (xi k) (xi 1) P P)
    (hidNeg : ∀ k : ℤ, k ≤ 0 → IdentDistrib (xi k) (xi 0) P P)
    (alpha Cp Cn : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hCp : 0 < Cp) (hCn : 0 < Cn)
    (htailPos : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 1 ω|} ≤ Cp * x ^ (-alpha))
    (htailNeg : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 0 ω|} ≤ Cn * x ^ (-alpha)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 ≤ A →
      1 - C' * A ^ (-alpha) ≤ P.real {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |twoSidedWalk xi l ω| ≤ A * (k : ℝ) ^ (1 / alpha)} := by
  obtain ⟨C', hC', h⟩ := twoSidedWalk_fluctuation_lt_one hmeas hind hidPos hidNeg alpha Cp Cn
    ha0 ha1 hCp hCn htailPos htailNeg
  refine ⟨C', hC', fun k hk A hA => ?_⟩
  have hcompl : {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |twoSidedWalk xi l ω| ≤ A * (k : ℝ) ^ (1 / alpha)} =
      {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  have hmeasE : MeasurableSet {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} := by
    have hX : ∀ l : ℤ, Measurable fun ω => twoSidedWalk xi l ω := by
      intro l
      unfold twoSidedWalk
      split_ifs
      · exact Finset.measurable_sum _ fun j _ => hmeas j
      · exact (Finset.measurable_sum _ fun j _ => hmeas j).neg
    have : {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} =
        ⋃ l ∈ Finset.Icc (-(k : ℤ)) k,
          {ω | A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} := by
      ext ω
      simp [Finset.mem_Icc, and_assoc]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun l _ =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX l))
  rw [hcompl, measureReal_compl hmeasE]
  have := h k hk A hA
  have hu : P.real Set.univ = 1 := by simp
  linarith

end TwoSided

end DirectedDistances.Probability
