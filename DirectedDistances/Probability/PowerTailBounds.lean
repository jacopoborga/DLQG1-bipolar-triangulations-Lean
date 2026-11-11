module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Topology.Algebra.Ring.Real









public section
namespace DirectedDistances.Probability
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]



theorem exists_powerTailBound {Y : Ω → ℝ} (_hY : Measurable Y) {ν cPlus cMinus : ℝ}
    (hν : 0 < ν)
    (hplus : Tendsto
      (fun x : ℝ => x ^ ν * P.real {ω | x < Y ω}) atTop (𝓝 cPlus))
    (hminus : Tendsto
      (fun x : ℝ => x ^ ν * P.real {ω | x < -Y ω}) atTop (𝓝 cMinus)) :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |Y ω|} ≤ C * x ^ (-ν) := by
  have hplusEvent : ∀ᶠ x : ℝ in atTop,
      dist (x ^ ν * P.real {ω | x < Y ω}) cPlus < 1 :=
    hplus (Metric.ball_mem_nhds cPlus one_pos)
  have hminusEvent : ∀ᶠ x : ℝ in atTop,
      dist (x ^ ν * P.real {ω | x < -Y ω}) cMinus < 1 :=
    hminus (Metric.ball_mem_nhds cMinus one_pos)
  obtain ⟨xp, hxp⟩ := Filter.eventually_atTop.mp hplusEvent
  obtain ⟨xm, hxm⟩ := Filter.eventually_atTop.mp hminusEvent
  let T := max 1 (max xp xm)
  let K := (|cPlus| + 1) + (|cMinus| + 1)
  let C := T ^ ν + K
  have hT : 1 ≤ T := le_max_left _ _
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hC : 0 < C := by
    dsimp [C, K]
    positivity
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxpow : 0 < x ^ ν := Real.rpow_pos_of_pos hxpos _
  have htail (z : ℝ) (hz : T ≤ z) :
      P.real {ω | z < |Y ω|} ≤ K * z ^ (-ν) := by
    have hplusClose := hxp z (le_trans (le_max_of_le_right (le_max_left _ _)) hz)
    have hminusClose := hxm z (le_trans (le_max_of_le_right (le_max_right _ _)) hz)
    have hplusBound : z ^ ν * P.real {ω | z < Y ω} ≤ |cPlus| + 1 := by
      have hdist : |z ^ ν * P.real {ω | z < Y ω} - cPlus| < 1 := by
        simpa [Real.dist_eq] using hplusClose
      have habs := abs_lt.mp hdist
      have hc : cPlus ≤ |cPlus| := le_abs_self cPlus
      linarith
    have hminusBound : z ^ ν * P.real {ω | z < -Y ω} ≤ |cMinus| + 1 := by
      have hdist : |z ^ ν * P.real {ω | z < -Y ω} - cMinus| < 1 := by
        simpa [Real.dist_eq] using hminusClose
      have habs := abs_lt.mp hdist
      have hc : cMinus ≤ |cMinus| := le_abs_self cMinus
      linarith
    have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one (le_trans hT hz)
    have hpow : 0 < z ^ ν := Real.rpow_pos_of_pos hzpos _
    have hplusProb : P.real {ω | z < Y ω} ≤ (|cPlus| + 1) * z ^ (-ν) := by
      have hdiv : P.real {ω | z < Y ω} ≤ (|cPlus| + 1) / z ^ ν :=
        (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hplusBound)
      simpa [div_eq_mul_inv, Real.rpow_neg hzpos.le] using hdiv
    have hminusProb : P.real {ω | z < -Y ω} ≤ (|cMinus| + 1) * z ^ (-ν) := by
      have hdiv : P.real {ω | z < -Y ω} ≤ (|cMinus| + 1) / z ^ ν :=
        (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hminusBound)
      simpa [div_eq_mul_inv, Real.rpow_neg hzpos.le] using hdiv
    have hsubset : {ω | z < |Y ω|} ⊆
        {ω | z < Y ω} ∪ {ω | z < -Y ω} := by
      intro ω hω
      by_cases hy : Y ω < 0
      · right
        simpa [abs_of_neg hy] using hω
      · left
        have hy' : 0 ≤ Y ω := le_of_not_gt hy
        simpa [abs_of_nonneg hy'] using hω
    calc P.real {ω | z < |Y ω|}
        ≤ P.real ({ω | z < Y ω} ∪ {ω | z < -Y ω}) := measureReal_mono hsubset
      _ ≤ P.real {ω | z < Y ω} + P.real {ω | z < -Y ω} :=
        measureReal_union_le _ _
      _ ≤ K * z ^ (-ν) := by
        have hzneg : 0 ≤ z ^ (-ν) := Real.rpow_nonneg hzpos.le _
        calc P.real {ω | z < Y ω} + P.real {ω | z < -Y ω}
            ≤ (|cPlus| + 1) * z ^ (-ν) +
              (|cMinus| + 1) * z ^ (-ν) := add_le_add hplusProb hminusProb
          _ = K * z ^ (-ν) := by dsimp [K]; ring
  by_cases hxt : T ≤ x
  · have hxneg : 0 ≤ x ^ (-ν) := Real.rpow_nonneg hxpos.le _
    calc P.real {ω | x < |Y ω|}
        ≤ K * x ^ (-ν) := htail x hxt
      _ ≤ C * x ^ (-ν) := by
        apply mul_le_mul_of_nonneg_right _ hxneg
        dsimp [C]
        have htnonneg : 0 ≤ T ^ ν := Real.rpow_nonneg hTpos.le _
        linarith
  · have hsmall : x ≤ T := le_of_not_ge hxt
    have hprob : P.real {ω | x < |Y ω|} ≤ 1 := measureReal_le_one
    have hxpowle : x ^ ν ≤ T ^ ν := Real.rpow_le_rpow hxpos.le hsmall hν.le
    have hxinverse : x ^ (-ν) = (x ^ ν)⁻¹ := Real.rpow_neg hxpos.le ν
    have hprod : 1 ≤ T ^ ν * x ^ (-ν) := by
      rw [hxinverse]
      exact (one_le_div hxpow).2 hxpowle
    have hCprod : 1 ≤ C * x ^ (-ν) := by
      dsimp [C]
      have hxneg : 0 ≤ x ^ (-ν) := Real.rpow_nonneg hxpos.le _
      have hK : 0 ≤ K := by dsimp [K]; positivity
      calc 1 ≤ T ^ ν * x ^ (-ν) := hprod
        _ ≤ (T ^ ν + K) * x ^ (-ν) := by
          exact mul_le_mul_of_nonneg_right (by linarith) hxneg
    exact hprob.trans hCprod


private lemma integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) (B : ℝ)
    (h : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact h ω)


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
    push Not at hmin
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
    push Not at hmin
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
      simp only [hn1, ite_true, mul_one] at hsingle
      linarith
  · have hz : absTrunc t x = 0 := by simp [absTrunc, h1]
    rw [hz]
    linarith

private lemma first_moment_trunc {X : Ω → ℝ} (hX : Measurable X) (α C : ℝ) (_hα0 : 0 < α)
    (hα1 : α < 1) (hC : 0 < C)
    (htail : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |X ω|} ≤ C * x ^ (-α)) :
    ∀ t : ℝ, 1 ≤ t →
      ∫ ω, absTrunc t (X ω) ∂P ≤
        (1 + 2 * C * (2 : ℝ) ^ (1 - α) /
          ((2 : ℝ) ^ (1 - α) - 1)) * t ^ (1 - α) := by
  classical
  have hβ : 0 < 1 - α := by linarith
  have hr : 1 < (2 : ℝ) ^ (1 - α) := Real.one_lt_rpow (by norm_num) hβ
  have hr1 : 0 < (2 : ℝ) ^ (1 - α) - 1 := by linarith
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


private noncomputable def truncFn (t x : ℝ) : ℝ := if |x| ≤ t then x else 0

private lemma measurable_truncFn (t : ℝ) : Measurable (truncFn t) := by
  show Measurable (fun x : ℝ => if |x| ≤ t then x else 0)
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    measurable_id measurable_const

private lemma abs_truncFn_le {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : |truncFn t x| ≤ t := by
  unfold truncFn
  split_ifs with h
  · exact h
  · simpa using ht

private lemma exists_shell (t x : ℝ) (ht : 0 < t) (hx : t < x) :
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
    push Not at hmin
    rw [hm]
    exact hmin

private lemma exists_two_pow (t : ℝ) (ht : 1 ≤ t) :
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
    push Not at hmin
    rw [hm, pow_succ]
    linarith

private lemma two_pow_rpow (n : ℕ) (β : ℝ) :
    ((2 : ℝ) ^ n) ^ β = ((2 : ℝ) ^ β) ^ n := by
  rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_natCast]

private lemma truncFn_sq_le (t : ℝ) (N : ℕ) (hN : t ≤ 2 ^ N) (x : ℝ) :
    (truncFn t x) ^ 2 ≤ 1 + ∑ n ∈ Finset.range N,
      (4 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |x| then 1 else 0) := by
  have hterm : ∀ n ∈ Finset.range N,
      0 ≤ (4 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |x| then 1 else 0) := fun n _ =>
    mul_nonneg (by positivity) (by split_ifs <;> norm_num)
  have hnn := Finset.sum_nonneg hterm
  by_cases h1 : |x| ≤ t
  · have hz : truncFn t x = x := by simp [truncFn, h1]
    rw [hz]
    by_cases h2 : |x| ≤ 1
    · have : x ^ 2 ≤ 1 := by
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg _) h2
      linarith
    · obtain ⟨n, hn1, hn2⟩ := exists_shell 1 |x| one_pos (lt_of_not_ge h2)
      rw [one_mul] at hn1 hn2
      have hnN : n < N := by
        have : (2 : ℝ) ^ n < 2 ^ N := lt_of_lt_of_le hn1 (h1.trans hN)
        exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
      have hx2 : x ^ 2 ≤ (4 : ℝ) ^ (n + 1) := by
        rw [← sq_abs]
        have h4 : (4 : ℝ) ^ (n + 1) = ((2 : ℝ) ^ (n + 1)) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [h4]
        exact pow_le_pow_left₀ (abs_nonneg _) hn2 2
      have hsingle := Finset.single_le_sum
        (f := fun n => (4 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |x| then 1 else 0)) hterm
        (Finset.mem_range.mpr hnN)
      simp only [hn1, ite_true, mul_one] at hsingle
      linarith
  · have hz : truncFn t x = 0 := by simp [truncFn, h1]
    rw [hz]
    linarith

private lemma second_moment_bound {X : Ω → ℝ} (hX : Measurable X) (α C : ℝ) (_hα0 : 0 < α)
    (hα2 : α < 2) (hC : 0 < C)
    (htail : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |X ω|} ≤ C * x ^ (-α)) :
    ∀ t : ℝ, 1 ≤ t →
      ∫ ω, (truncFn t (X ω)) ^ 2 ∂P ≤
        (1 + 4 * C * (2 : ℝ) ^ (2 - α) /
          ((2 : ℝ) ^ (2 - α) - 1)) * t ^ (2 - α) := by
  classical
  have hβ : 0 < 2 - α := by linarith
  have hr : 1 < (2 : ℝ) ^ (2 - α) := Real.one_lt_rpow (by norm_num) hβ
  have hr1 : 0 < (2 : ℝ) ^ (2 - α) - 1 := by linarith
  intro t ht
  obtain ⟨N, hN1, hN2⟩ := exists_two_pow t ht
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
    integrable_of_abs_le (Measurable.ite (hind_meas n) measurable_const measurable_const) 1
      fun ω => by split_ifs <;> simp
  have hi : ∀ n ∈ Finset.range N, Integrable
      (fun ω => (4 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0)) P :=
    fun n _ => (hind_integrable n).const_mul _
  have hRint : Integrable (fun ω => 1 + ∑ n ∈ Finset.range N,
      (4 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0)) P :=
    (integrable_const _).add (integrable_finsetSum _ hi)
  have hR : ∫ ω, (1 + ∑ n ∈ Finset.range N,
      (4 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0)) ∂P =
      1 + ∑ n ∈ Finset.range N, (4 : ℝ) ^ (n + 1) * P.real {ω | (2 : ℝ) ^ n < |X ω|} := by
    rw [integral_add (integrable_const _) (integrable_finsetSum _ hi),
      integral_finsetSum _ hi]
    simp only [integral_const_mul, hind_int]
    simp
  have hZ2 : Integrable (fun ω => (truncFn t (X ω)) ^ 2) P :=
    integrable_of_abs_le (((measurable_truncFn t).comp hX).pow_const 2) (t ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncFn_le (by linarith) _) 2
  have hmono : ∫ ω, (truncFn t (X ω)) ^ 2 ∂P ≤ ∫ ω, (1 + ∑ n ∈ Finset.range N,
      (4 : ℝ) ^ (n + 1) * (if (2 : ℝ) ^ n < |X ω| then (1 : ℝ) else 0)) ∂P :=
    integral_mono hZ2 hRint fun ω => truncFn_sq_le t N hN1 (X ω)
  rw [hR] at hmono
  have hterm : ∀ n ∈ Finset.range N, (4 : ℝ) ^ (n + 1) * P.real {ω | (2 : ℝ) ^ n < |X ω|} ≤
      4 * C * ((2 : ℝ) ^ (2 - α)) ^ n := by
    intro n _
    have h1 : P.real {ω | (2 : ℝ) ^ n < |X ω|} ≤ C * ((2 : ℝ) ^ n) ^ (-α) :=
      htail _ (one_le_pow₀ (by norm_num))
    have h2 : (4 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ n) ^ (-α) =
        4 * ((2 : ℝ) ^ (2 - α)) ^ n := by
      rw [← two_pow_rpow, sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_two]
      have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [pow_succ, h4]
      ring
    calc (4 : ℝ) ^ (n + 1) * P.real {ω | (2 : ℝ) ^ n < |X ω|}
        ≤ (4 : ℝ) ^ (n + 1) * (C * ((2 : ℝ) ^ n) ^ (-α)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C * ((4 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ n) ^ (-α)) := by ring
      _ = 4 * C * ((2 : ℝ) ^ (2 - α)) ^ n := by rw [h2]; ring
  have hsum : ∑ n ∈ Finset.range N, (4 : ℝ) ^ (n + 1) * P.real {ω | (2 : ℝ) ^ n < |X ω|} ≤
      4 * C * ∑ n ∈ Finset.range N, ((2 : ℝ) ^ (2 - α)) ^ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hgeom : ∑ n ∈ Finset.range N, ((2 : ℝ) ^ (2 - α)) ^ n ≤
      (2 : ℝ) ^ (2 - α) * t ^ (2 - α) / ((2 : ℝ) ^ (2 - α) - 1) := by
    have hid := geom_sum_mul ((2 : ℝ) ^ (2 - α)) N
    have hrN : ((2 : ℝ) ^ (2 - α)) ^ N ≤ (2 : ℝ) ^ (2 - α) * t ^ (2 - α) := by
      rw [← two_pow_rpow, ← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by positivity) hN2 hβ.le
    rw [le_div_iff₀ hr1]
    have : 0 ≤ ((2 : ℝ) ^ (2 - α)) ^ N := by positivity
    linarith
  have ht1 : 1 ≤ t ^ (2 - α) := Real.one_le_rpow ht hβ.le
  have hfinal : 4 * C * ∑ n ∈ Finset.range N, ((2 : ℝ) ^ (2 - α)) ^ n ≤
      4 * C * ((2 : ℝ) ^ (2 - α) * t ^ (2 - α) / ((2 : ℝ) ^ (2 - α) - 1)) :=
    mul_le_mul_of_nonneg_left hgeom (by positivity)
  have he : 4 * C * ((2 : ℝ) ^ (2 - α) * t ^ (2 - α) / ((2 : ℝ) ^ (2 - α) - 1)) =
      (4 * C * (2 : ℝ) ^ (2 - α) / ((2 : ℝ) ^ (2 - α) - 1)) * t ^ (2 - α) := by ring
  nlinarith


private lemma tail_first_moment {X : Ω → ℝ} (hX : Measurable X) (α C : ℝ) (hα1 : 1 < α)
    (hC : 0 < C)
    (htail : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |X ω|} ≤ C * x ^ (-α)) :
    ∀ t : ℝ, 1 ≤ t →
      (∫ ω, (if t < |X ω| then |X ω| else 0) ∂P ≤
        (2 * C / (1 - (2 : ℝ) ^ (1 - α))) * t ^ (1 - α)) ∧
        Integrable (fun ω => if t < |X ω| then |X ω| else 0) P := by
  classical
  have hq0 : 0 < (2 : ℝ) ^ (1 - α) := by positivity
  have hq1 : (2 : ℝ) ^ (1 - α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq2 : 0 < 1 - (2 : ℝ) ^ (1 - α) := by linarith
  intro t ht
  have ht0 : 0 < t := by linarith
  have hXabs : Measurable fun ω => |X ω| := continuous_abs.measurable.comp hX
  have hE (n : ℕ) : MeasurableSet {ω | t * 2 ^ n < |X ω|} :=
    measurableSet_lt measurable_const hXabs
  have hg : Measurable fun ω => if t < |X ω| then |X ω| else 0 :=
    Measurable.ite (measurableSet_lt measurable_const hXabs) hXabs measurable_const
  -- pointwise domination by a series of shell indicators
  have hpt : ∀ ω, ENNReal.ofReal (if t < |X ω| then |X ω| else 0) ≤
      ∑' n : ℕ, Set.indicator {ω | t * 2 ^ n < |X ω|}
        (fun _ => ENNReal.ofReal (2 * t * 2 ^ n)) ω := by
    intro ω
    by_cases h : t < |X ω|
    · obtain ⟨n, hn1, hn2⟩ := exists_shell t |X ω| ht0 h
      simp [h]
      refine le_trans ?_ (le_tsum _ n)
      rw [Set.indicator_of_mem (show ω ∈ {ω | t * 2 ^ n < |X ω|} from hn1)]
      exact ENNReal.ofReal_le_ofReal (by rw [pow_succ] at hn2; linarith)
    · simp [h]
  have hterm : ∀ n : ℕ, ∫⁻ ω, Set.indicator {ω | t * 2 ^ n < |X ω|}
      (fun _ => ENNReal.ofReal (2 * t * 2 ^ n)) ω ∂P ≤
      ENNReal.ofReal (2 * C * t ^ (1 - α) * ((2 : ℝ) ^ (1 - α)) ^ n) := by
    intro n
    rw [lintegral_indicator_const (hE n)]
    have hx : 0 < t * 2 ^ n := by positivity
    have h1 : P.real {ω | t * 2 ^ n < |X ω|} ≤ C * (t * 2 ^ n) ^ (-α) :=
      htail _ (one_le_mul_of_one_le_of_one_le ht (one_le_pow₀ (by norm_num)))
    have h2 : (t * 2 ^ n) * (t * 2 ^ n) ^ (-α) = (t * 2 ^ n) ^ (1 - α) := by
      rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
    have h3 : (t * 2 ^ n) ^ (1 - α) = t ^ (1 - α) * ((2 : ℝ) ^ (1 - α)) ^ n := by
      rw [Real.mul_rpow ht0.le (by positivity), two_pow_rpow]
    rw [← MeasureTheory.ofReal_measureReal (measure_ne_top P _),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc 2 * t * 2 ^ n * P.real {ω | t * 2 ^ n < |X ω|}
        ≤ 2 * t * 2 ^ n * (C * (t * 2 ^ n) ^ (-α)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * C * ((t * 2 ^ n) * (t * 2 ^ n) ^ (-α)) := by ring
      _ = 2 * C * t ^ (1 - α) * ((2 : ℝ) ^ (1 - α)) ^ n := by rw [h2, h3]; ring
  have hsumq : ∀ M : ℕ, ∑ n ∈ Finset.range M, ((2 : ℝ) ^ (1 - α)) ^ n ≤
      1 / (1 - (2 : ℝ) ^ (1 - α)) := by
    intro M
    have hid := mul_neg_geom_sum ((2 : ℝ) ^ (1 - α)) M
    rw [le_div_iff₀ hq2]
    have : 0 ≤ ((2 : ℝ) ^ (1 - α)) ^ M := by positivity
    nlinarith
  have hlint : ∫⁻ ω, ENNReal.ofReal (if t < |X ω| then |X ω| else 0) ∂P ≤
      ENNReal.ofReal (2 * C / (1 - (2 : ℝ) ^ (1 - α)) * t ^ (1 - α)) := by
    calc ∫⁻ ω, ENNReal.ofReal (if t < |X ω| then |X ω| else 0) ∂P
        ≤ ∫⁻ ω, ∑' n : ℕ, Set.indicator {ω | t * 2 ^ n < |X ω|}
            (fun _ => ENNReal.ofReal (2 * t * 2 ^ n)) ω ∂P := lintegral_mono hpt
      _ = ∑' n : ℕ, ∫⁻ ω, Set.indicator {ω | t * 2 ^ n < |X ω|}
            (fun _ => ENNReal.ofReal (2 * t * 2 ^ n)) ω ∂P :=
          lintegral_tsum fun n => (measurable_const.indicator (hE n)).aemeasurable
      _ ≤ ENNReal.ofReal (2 * C / (1 - (2 : ℝ) ^ (1 - α)) * t ^ (1 - α)) := by
          apply ENNReal.tsum_le_of_sum_range_le
          intro M
          calc ∑ n ∈ Finset.range M, ∫⁻ ω, Set.indicator {ω | t * 2 ^ n < |X ω|}
                (fun _ => ENNReal.ofReal (2 * t * 2 ^ n)) ω ∂P
              ≤ ∑ n ∈ Finset.range M, ENNReal.ofReal
                  (2 * C * t ^ (1 - α) * ((2 : ℝ) ^ (1 - α)) ^ n) :=
                Finset.sum_le_sum fun n _ => hterm n
            _ = ENNReal.ofReal (∑ n ∈ Finset.range M,
                  2 * C * t ^ (1 - α) * ((2 : ℝ) ^ (1 - α)) ^ n) :=
                (ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity).symm
            _ ≤ ENNReal.ofReal (2 * C / (1 - (2 : ℝ) ^ (1 - α)) * t ^ (1 - α)) := by
                apply ENNReal.ofReal_le_ofReal
                rw [← Finset.mul_sum]
                have hp : 0 ≤ 2 * C * t ^ (1 - α) := by positivity
                calc 2 * C * t ^ (1 - α) * ∑ n ∈ Finset.range M,
                      ((2 : ℝ) ^ (1 - α)) ^ n
                    ≤ 2 * C * t ^ (1 - α) * (1 / (1 - (2 : ℝ) ^ (1 - α))) :=
                      mul_le_mul_of_nonneg_left (hsumq M) hp
                  _ = 2 * C / (1 - (2 : ℝ) ^ (1 - α)) * t ^ (1 - α) := by ring
  constructor
  · rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ω => by simp only [Pi.zero_apply]; split_ifs <;> simp)
      hg.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (div_nonneg (by positivity) hq2.le) (by positivity)) hlint
  · have hfinite :
        (∫⁻ ω, ENNReal.ofReal (if t < |X ω| then |X ω| else 0) ∂P) < ∞ :=
      lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
    exact (lintegral_ofReal_ne_top_iff_integrable hg.aestronglyMeasurable
      (ae_of_all _ fun ω => by positivity)).mp hfinite.ne





theorem truncated_first_moment_power_tail_bound {Y : Ω → ℝ} (_hY : Measurable Y)
    {ν C : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |Y ω|} ≤ C * x ^ (-ν)) :
    ∀ a : ℝ, 1 ≤ a →
      ∫ ω, |Y ω| * Set.indicator {ω | |Y ω| ≤ a} (fun _ => (1 : ℝ)) ω ∂P ≤
        (1 + 2 * C * (2 : ℝ) ^ (1 - ν) /
          ((2 : ℝ) ^ (1 - ν) - 1)) * a ^ (1 - ν) := by
  have h := first_moment_trunc (P := P) _hY ν C hν0 hν1 hC hTail
  intro a ha
  have heq : (fun ω => |Y ω| *
      Set.indicator {ω | |Y ω| ≤ a} (fun _ => (1 : ℝ)) ω) =
      fun ω => absTrunc a (Y ω) := by
    funext ω
    simp [absTrunc, Set.indicator_apply]
  rw [heq]
  exact h a ha




theorem truncated_second_moment_power_tail_bound {Y : Ω → ℝ} (_hY : Measurable Y)
    {ν C : ℝ} (hν1 : 1 < ν) (hν2 : ν < 2) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |Y ω|} ≤ C * x ^ (-ν)) :
    ∀ a : ℝ, 1 ≤ a →
      ∫ ω, Y ω ^ 2 * Set.indicator {ω | |Y ω| ≤ a}
        (fun _ => (1 : ℝ)) ω ∂P ≤
        (1 + 4 * C * (2 : ℝ) ^ (2 - ν) /
          ((2 : ℝ) ^ (2 - ν) - 1)) * a ^ (2 - ν) := by
  have hν0 : 0 < ν := lt_trans zero_lt_one hν1
  have h := second_moment_bound (P := P) _hY ν C hν0 hν2 hC hTail
  intro a ha
  have heq : (fun ω => Y ω ^ 2 *
      Set.indicator {ω | |Y ω| ≤ a} (fun _ => (1 : ℝ)) ω) =
      fun ω => (truncFn a (Y ω)) ^ 2 := by
    funext ω
    simp [truncFn, Set.indicator_apply]
  rw [heq]
  exact h a ha




theorem tail_first_moment_power_tail_bound {Y : Ω → ℝ} (hY : Measurable Y)
    {ν C : ℝ} (hν : 1 < ν) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |Y ω|} ≤ C * x ^ (-ν)) :
    Integrable Y P ∧ ∀ a : ℝ, 1 ≤ a →
      ∫ ω, (if a < |Y ω| then |Y ω| else 0) ∂P ≤
        (2 * C / (1 - (2 : ℝ) ^ (1 - ν))) * a ^ (1 - ν) := by
  have ht := tail_first_moment (P := P) hY ν C hν hC hTail
  have htailInt := (ht 1 (by norm_num)).2
  have hlow : Integrable (fun ω => absTrunc 1 (Y ω)) P :=
    integrable_of_abs_le' ((measurable_absTrunc 1).comp hY) 1 fun ω => by
      rw [abs_of_nonneg (absTrunc_nonneg _ _)]
      exact absTrunc_le_level (by norm_num) _
  have hsplit : (fun ω => |Y ω|) = fun ω =>
      absTrunc 1 (Y ω) + (if 1 < |Y ω| then |Y ω| else 0) := by
    funext ω
    by_cases h : |Y ω| ≤ 1
    · simp [absTrunc, h, not_lt.mpr h]
    · simp [absTrunc, h, lt_of_not_ge h]
  have hnorm : Integrable (fun ω => |Y ω|) P := by
    rw [hsplit]
    exact hlow.add htailInt
  have hYint : Integrable Y P := by
    apply (integrable_norm_iff hY.aestronglyMeasurable).mp
    simpa [Real.norm_eq_abs] using hnorm
  refine ⟨hYint, ?_⟩
  intro a ha
  exact (ht a ha).1

end DirectedDistances.Probability
