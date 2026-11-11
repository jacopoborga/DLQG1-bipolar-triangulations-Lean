module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.OptionalStopping

/-! # Maximal inequality for sums with power-law tails

Helper for `lem-ldp-fluctuation` and `lem-sdp-fluctuation`
not a paper result. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section Kolmogorov

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Partial sums `∑ i < k, Y i`. -/
private noncomputable def psum (Y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, Y i ω

private noncomputable def psumSq (Y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (psum Y k ω) ^ 2

private lemma psum_succ (Y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    psum Y (k + 1) ω = psum Y k ω + Y k ω := by
  simp [psum, Finset.sum_range_succ]

private def walkFiltration (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) :
    Filtration ℕ mΩ where
  seq k := ⨆ i ∈ Set.Iio k, MeasurableSpace.comap (Y i) inferInstance
  mono' := by
    intro k l hkl
    refine iSup₂_le fun i hi => ?_
    exact le_iSup_of_le i <| le_iSup_of_le (lt_of_lt_of_le hi hkl) le_rfl
  le' := by
    intro k
    refine iSup₂_le fun i hi => ?_
    exact measurable_iff_comap_le.mp (hY i)

private lemma integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) (B : ℝ)
    (h : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact h ω)

variable (Y : ℕ → Ω → ℝ)

private lemma psum_measurable (hY : ∀ i, Measurable (Y i)) (k : ℕ) :
    Measurable (psum Y k) := by
  unfold psum
  exact Finset.measurable_sum _ fun i _ => hY i

private lemma psum_abs_le (B : ℝ) (hbd : ∀ i ω, |Y i ω| ≤ B) (k : ℕ) (ω : Ω) :
    |psum Y k ω| ≤ k * B := by
  calc |psum Y k ω| ≤ ∑ i ∈ Finset.range k, |Y i ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range k, B := Finset.sum_le_sum fun i _ => hbd i ω
    _ = k * B := by simp

private lemma psum_measurable_filtration (hY : ∀ i, Measurable (Y i)) (k : ℕ) :
    Measurable[walkFiltration Y hY k] (psum Y k) := by
  change Measurable[walkFiltration Y hY k] (fun ω => ∑ i ∈ Finset.range k, Y i ω)
  apply Finset.measurable_sum
  intro i hi
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le i <| le_iSup_of_le (Finset.mem_range.mp hi) le_rfl

private lemma indep_filtration_next (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (k : ℕ) :
    Indep (walkFiltration Y hY k) (MeasurableSpace.comap (Y k) inferInstance) P := by
  have hspaces : iIndep (fun i : ℕ => MeasurableSpace.comap (Y i) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).mp hind
  have hle : ∀ i, MeasurableSpace.comap (Y i) inferInstance ≤ mΩ := fun i =>
    measurable_iff_comap_le.mp (hY i)
  have hst : Disjoint (Set.Iio k) ({k} : Set ℕ) := by simp
  change Indep (⨆ i ∈ Set.Iio k, MeasurableSpace.comap (Y i) inferInstance)
    (MeasurableSpace.comap (Y k) inferInstance) P
  have h := indep_iSup_of_disjoint hle hspaces hst
  simpa only [iSup_singleton] using h

private lemma cross_zero (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0) (k : ℕ) (A : Set Ω)
    (hA : MeasurableSet[walkFiltration Y hY k] A) :
    ∫ ω in A, psum Y k ω * Y k ω ∂P = 0 := by
  have hA' : MeasurableSet A := (walkFiltration Y hY).le k A hA
  let H : Ω → ℝ := A.indicator (psum Y k)
  have hmeasH : Measurable[walkFiltration Y hY k] H :=
    (psum_measurable_filtration Y hY k).indicator hA
  have hHm : Measurable H := (psum_measurable Y hY k).indicator hA'
  have hindHG : H ⟂ᵢ[P] (Y k) := by
    change Indep (MeasurableSpace.comap H inferInstance)
      (MeasurableSpace.comap (Y k) inferInstance) P
    exact indep_of_indep_of_le (indep_filtration_next Y hY hind k)
      (measurable_iff_comap_le.mp hmeasH) le_rfl
  have hfact := hindHG.integral_mul_eq_mul_integral hHm.aestronglyMeasurable
    (hY k).aestronglyMeasurable
  calc ∫ ω in A, psum Y k ω * Y k ω ∂P
      = ∫ ω, A.indicator (fun ω => psum Y k ω * Y k ω) ω ∂P :=
        (integral_indicator hA').symm
    _ = ∫ ω, H ω * Y k ω ∂P := by
        congr 1
        funext ω
        by_cases hω : ω ∈ A <;> simp [H, hω]
    _ = (∫ ω, H ω ∂P) * ∫ ω, Y k ω ∂P := hfact
    _ = 0 := by rw [hmean k, mul_zero]

private lemma integrable_psum_sq (hY : ∀ i, Measurable (Y i)) (B : ℝ)
    (hbd : ∀ i ω, |Y i ω| ≤ B) (k : ℕ) :
    Integrable (fun ω => (psum Y k ω) ^ 2) P :=
  integrable_of_abs_le ((psum_measurable Y hY k).pow_const 2) ((k * B) ^ 2) fun ω => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (psum_abs_le Y B hbd k ω) 2

private lemma integrable_psum_mul (hY : ∀ i, Measurable (Y i)) (B : ℝ)
    (hbd : ∀ i ω, |Y i ω| ≤ B) (k : ℕ) :
    Integrable (fun ω => psum Y k ω * Y k ω) P :=
  integrable_of_abs_le ((psum_measurable Y hY k).mul (hY k)) ((k * B) * B) fun ω => by
    rw [abs_mul]
    exact mul_le_mul (psum_abs_le Y B hbd k ω) (hbd k ω) (abs_nonneg _)
      ((abs_nonneg _).trans (psum_abs_le Y B hbd k ω))

private lemma integrable_sq_bdd (hY : ∀ i, Measurable (Y i)) (B : ℝ)
    (hbd : ∀ i ω, |Y i ω| ≤ B) (k : ℕ) :
    Integrable (fun ω => (Y k ω) ^ 2) P :=
  integrable_of_abs_le ((hY k).pow_const 2) (B ^ 2) fun ω => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbd k ω) 2

private lemma psumSq_submartingale (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (B : ℝ) (hbd : ∀ i ω, |Y i ω| ≤ B) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0) :
    Submartingale (psumSq Y) (walkFiltration Y hY) P := by
  apply submartingale_of_setIntegral_le_succ
  · intro k
    exact ((psum_measurable_filtration Y hY k).pow_const 2).stronglyMeasurable
  · intro k
    exact integrable_psum_sq Y hY B hbd k
  · intro k A hA
    have h1 := integrable_psum_sq (P := P) Y hY B hbd k
    have h2 := integrable_psum_mul (P := P) Y hY B hbd k
    have hcross := cross_zero Y hY hind hmean k A hA
    have hmono : ∫ ω in A, ((psum Y k ω) ^ 2 + 2 * (psum Y k ω * Y k ω)) ∂P ≤
        ∫ ω in A, (psum Y (k + 1) ω) ^ 2 ∂P :=
      setIntegral_mono (h1.add (h2.const_mul 2)).integrableOn
        (integrable_psum_sq Y hY B hbd (k + 1)).integrableOn fun ω => by
          have := sq_nonneg (Y k ω)
          simp only [psum_succ]
          nlinarith
    rw [integral_add h1.integrableOn (h2.const_mul 2).integrableOn, integral_const_mul,
      hcross] at hmono
    change ∫ ω in A, (psum Y k ω) ^ 2 ∂P ≤ ∫ ω in A, (psum Y (k + 1) ω) ^ 2 ∂P
    linarith

private lemma integral_psum_sq_le (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (B : ℝ) (hbd : ∀ i ω, |Y i ω| ≤ B) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0) (v : ℝ)
    (hv : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂P ≤ v) (k : ℕ) :
    ∫ ω, (psum Y k ω) ^ 2 ∂P ≤ k * v := by
  induction k with
  | zero => simp [psum]
  | succ k ih =>
    have h1 := integrable_psum_sq (P := P) Y hY B hbd k
    have h2 := integrable_psum_mul (P := P) Y hY B hbd k
    have h3 := integrable_sq_bdd (P := P) Y hY B hbd k
    have hc : ∫ ω, psum Y k ω * Y k ω ∂P = 0 := by
      simpa using cross_zero Y hY hind hmean k Set.univ MeasurableSet.univ
    have heq : ∫ ω, (psum Y (k + 1) ω) ^ 2 ∂P =
        ∫ ω, (psum Y k ω) ^ 2 ∂P + ∫ ω, (Y k ω) ^ 2 ∂P := by
      have hfun : (fun ω => (psum Y (k + 1) ω) ^ 2) =
          fun ω => ((psum Y k ω) ^ 2 + 2 * (psum Y k ω * Y k ω)) + (Y k ω) ^ 2 := by
        funext ω
        rw [psum_succ]
        ring
      have h12 : Integrable
          (fun ω => (psum Y k ω) ^ 2 + 2 * (psum Y k ω * Y k ω)) P :=
        h1.add (h2.const_mul 2)
      rw [hfun, integral_add h12 h3, integral_add h1 (h2.const_mul 2),
        integral_const_mul, hc]
      ring
    rw [heq]
    have := hv k
    push_cast
    linarith

/-- Kolmogorov's maximal inequality for bounded independent centered summands, via Doob's
maximal inequality for the submartingale of squared partial sums. -/
private theorem kolmogorov_max (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (B : ℝ) (hbd : ∀ i ω, |Y i ω| ≤ B) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0) (v : ℝ)
    (hv : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂P ≤ v) (k : ℕ) (s : ℝ) (hs : 0 < s) :
    P.real {ω | ∃ j ≤ k, s ≤ |psum Y j ω|} ≤ k * v / s ^ 2 := by
  let ε : ℝ≥0 := ⟨s ^ 2, by positivity⟩
  let E : Set Ω := {ω | ∃ j ≤ k, s ≤ |psum Y j ω|}
  have hε : (ε : ℝ) = s ^ 2 := rfl
  have hrange : (Finset.range (k + 1)).Nonempty := ⟨0, by simp⟩
  have hevent : {ω | (ε : ℝ) ≤ (Finset.range (k + 1)).sup' hrange
      (fun j => psumSq Y j ω)} = E := by
    ext ω
    constructor
    · intro h
      obtain ⟨j, hj, hjs⟩ := (Finset.le_sup'_iff (s := Finset.range (k + 1)) (H := hrange)
        (f := fun j => psumSq Y j ω) (a := (ε : ℝ))).mp h
      refine ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), ?_⟩
      have hjs' : s ^ 2 ≤ (psum Y j ω) ^ 2 := hjs
      have hjs'' : s ^ 2 ≤ |psum Y j ω| ^ 2 := by rw [sq_abs]; exact hjs'
      exact (sq_le_sq₀ hs.le (abs_nonneg _)).mp hjs''
    · rintro ⟨j, hj, hjs⟩
      apply (Finset.le_sup'_iff (s := Finset.range (k + 1)) (H := hrange)
        (f := fun j => psumSq Y j ω) (a := (ε : ℝ))).mpr
      refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj), ?_⟩
      show s ^ 2 ≤ (psum Y j ω) ^ 2
      rw [← sq_abs (psum Y j ω)]
      exact pow_le_pow_left₀ hs.le hjs 2
  have hsub := psumSq_submartingale Y hY hind B hbd hmean
  have hmax := MeasureTheory.maximal_ineq (ε := ε) hsub (fun j ω => sq_nonneg _) k
  rw [hevent] at hmax
  have hint := integral_psum_sq_le Y hY hind B hbd hmean v hv k
  have hv0 : 0 ≤ v := (integral_nonneg fun ω => sq_nonneg _).trans (hv 0)
  have hset : ∫ ω in E, psumSq Y k ω ∂P ≤ ∫ ω, psumSq Y k ω ∂P :=
    setIntegral_le_integral (integrable_psum_sq Y hY B hbd k)
      (ae_of_all _ fun ω => sq_nonneg _)
  have hwrap : ENNReal.ofReal ((ε : ℝ) * P.real E) ≤ ENNReal.ofReal (k * v) := by
    calc ENNReal.ofReal ((ε : ℝ) * P.real E) = (ε : ℝ≥0∞) * P E := by
          rw [ENNReal.ofReal_mul (show 0 ≤ (ε : ℝ) by positivity),
            ENNReal.ofReal_coe_nnreal,
            MeasureTheory.ofReal_measureReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (∫ ω in E, psumSq Y k ω ∂P) := hmax
      _ ≤ ENNReal.ofReal (k * v) :=
          ENNReal.ofReal_le_ofReal (hset.trans hint)
  have hprob : (ε : ℝ) * P.real E ≤ k * v :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hwrap
  rw [le_div_iff₀ (by positivity)]
  rw [hε] at hprob
  linarith

end Kolmogorov

section Moments

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Truncation at level `t`: keep `x` when `|x| ≤ t`, else `0`. -/
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
    push_neg at hmin
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
    push_neg at hmin
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
      simp only [if_pos hn1, mul_one] at hsingle
      linarith
  · have hz : truncFn t x = 0 := by simp [truncFn, h1]
    rw [hz]
    linarith

private lemma second_moment_bound {X : Ω → ℝ} (hX : Measurable X) (α C : ℝ) (hα0 : 0 < α)
    (hα2 : α < 2) (hC : 0 < C)
    (htail : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |X ω|} ≤ C * x ^ (-α)) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ t : ℝ, 1 ≤ t →
      ∫ ω, (truncFn t (X ω)) ^ 2 ∂P ≤ C2 * t ^ (2 - α) := by
  classical
  have hβ : 0 < 2 - α := by linarith
  have hr : 1 < (2 : ℝ) ^ (2 - α) := Real.one_lt_rpow (by norm_num) hβ
  have hr1 : 0 < (2 : ℝ) ^ (2 - α) - 1 := by linarith
  have hpos : 0 ≤ 4 * C * (2 : ℝ) ^ (2 - α) / ((2 : ℝ) ^ (2 - α) - 1) :=
    div_nonneg (by positivity) hr1.le
  refine ⟨1 + 4 * C * (2 : ℝ) ^ (2 - α) / ((2 : ℝ) ^ (2 - α) - 1),
    add_pos_of_pos_of_nonneg one_pos hpos, ?_⟩
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
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 1 ≤ t →
      ∫ ω, (if t < |X ω| then |X ω| else 0) ∂P ≤ D * t ^ (1 - α) := by
  classical
  have hq0 : 0 < (2 : ℝ) ^ (1 - α) := by positivity
  have hq1 : (2 : ℝ) ^ (1 - α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq2 : 0 < 1 - (2 : ℝ) ^ (1 - α) := by linarith
  refine ⟨2 * C / (1 - (2 : ℝ) ^ (1 - α)), div_nonneg (by positivity) hq2.le, ?_⟩
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
      rw [if_pos h]
      refine le_trans ?_ (le_tsum _ n)
      rw [Set.indicator_of_mem (show ω ∈ {ω | t * 2 ^ n < |X ω|} from hn1)]
      exact ENNReal.ofReal_le_ofReal (by rw [pow_succ] at hn2; linarith)
    · rw [if_neg h]
      simp
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
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun ω => by simp only [Pi.zero_apply]; split_ifs <;> simp)
    hg.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (div_nonneg (by positivity) hq2.le) (by positivity)) hlint

end Moments

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma variance_le_second_moment {Z : Ω → ℝ} (hZ : Measurable Z) (B : ℝ)
    (hB : ∀ ω, |Z ω| ≤ B) :
    ∫ ω, (Z ω - ∫ ω', Z ω' ∂P) ^ 2 ∂P ≤ ∫ ω, (Z ω) ^ 2 ∂P := by
  have hZi : Integrable Z P := integrable_of_abs_le hZ B hB
  have hZ2i : Integrable (fun ω => (Z ω) ^ 2) P :=
    integrable_of_abs_le (hZ.pow_const 2) (B ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB ω) 2
  generalize hm : ∫ ω', Z ω' ∂P = m
  have hfun : (fun ω => (Z ω - m) ^ 2) = fun ω => (Z ω) ^ 2 - (2 * m) * Z ω + m ^ 2 := by
    funext ω
    ring
  have hu : P.real Set.univ = 1 := by simp
  have hZc : Integrable (fun ω => (2 * m) * Z ω) P := hZi.const_mul _
  have hZs : Integrable (fun ω => (Z ω) ^ 2 - (2 * m) * Z ω) P := hZ2i.sub hZc
  rw [hfun, integral_add hZs (integrable_const _), integral_sub hZ2i hZc,
    integral_const_mul, hm, integral_const, smul_eq_mul, hu]
  nlinarith [sq_nonneg m]

private lemma drift_of_mean_zero {X : Ω → ℝ} (hX : Measurable X) (hint : Integrable X P)
    (hmean : ∫ ω, X ω ∂P = 0) (α D : ℝ)
    (hD : ∀ t : ℝ, 1 ≤ t → ∫ ω, (if t < |X ω| then |X ω| else 0) ∂P ≤ D * t ^ (1 - α))
    (t : ℝ) (ht : 1 ≤ t) :
    |∫ ω, truncFn t (X ω) ∂P| ≤ D * t ^ (1 - α) := by
  have hXabs : Measurable fun ω => |X ω| := continuous_abs.measurable.comp hX
  have hTl : Integrable (fun ω => if t < |X ω| then X ω else 0) P :=
    hint.norm.mono'
      (Measurable.ite (measurableSet_lt measurable_const hXabs) hX
        measurable_const).aestronglyMeasurable
      (ae_of_all _ fun ω => by split_ifs <;> simp)
  have hsplit : (fun ω => truncFn t (X ω)) =
      fun ω => X ω - (if t < |X ω| then X ω else 0) := by
    funext ω
    unfold truncFn
    by_cases h : |X ω| ≤ t
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  have hint_eq : ∫ ω, truncFn t (X ω) ∂P = -∫ ω, (if t < |X ω| then X ω else 0) ∂P := by
    rw [hsplit, integral_sub hint hTl, hmean, zero_sub]
  rw [hint_eq, abs_neg]
  calc |∫ ω, (if t < |X ω| then X ω else 0) ∂P|
      = ‖∫ ω, (if t < |X ω| then X ω else 0) ∂P‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ ω, ‖if t < |X ω| then X ω else 0‖ ∂P := norm_integral_le_integral_norm _
    _ = ∫ ω, (if t < |X ω| then |X ω| else 0) ∂P := by
        congr 1
        funext ω
        split_ifs <;> simp
    _ ≤ D * t ^ (1 - α) := hD t ht

/-- Maximal inequality for partial sums of iid variables with power-law tails of index
`alpha ∈ (0, 2)`: with probability `1 - O(A ^ (-alpha))`, the walk stays within
`A * k ^ (1 / alpha)` up to time `k`.  The summands are centered either in the sense that every
truncated mean `E[ξ 1{|ξ| ≤ t}]` vanishes, or, when `alpha > 1`, by `E ξ = 0`.

Helper for `lem-ldp-fluctuation` and `lem-sdp-fluctuation`
not a paper result. -/
theorem heavyTail_maximal {xi : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (xi i))
    (hind : iIndepFun xi P) (hid : ∀ i, IdentDistrib (xi i) (xi 0) P P)
    (alpha C : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 2) (hC : 0 < C)
    (htail : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 0 ω|} ≤ C * x ^ (-alpha))
    (hcenter : (∀ t : ℝ, 0 ≤ t →
        ∫ ω, Set.indicator {ω | |xi 0 ω| ≤ t} (xi 0) ω ∂P = 0) ∨
      (1 < alpha ∧ Integrable (xi 0) P ∧ ∫ ω, xi 0 ω ∂P = 0)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 ≤ A →
      P.real {ω | ∃ j ≤ k,
        A * (k : ℝ) ^ (1 / alpha) < |∑ i ∈ Finset.range j, xi i ω|} ≤ C' * A ^ (-alpha) := by
  obtain ⟨C2, hC2, hmom⟩ := second_moment_bound (hmeas 0) alpha C ha0 ha2 hC htail
  obtain ⟨D, hD0, hdrift⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 1 ≤ t →
      |∫ ω, truncFn t (xi 0 ω) ∂P| ≤ D * t ^ (1 - alpha) := by
    rcases hcenter with h1 | ⟨hα1, hint, hm0⟩
    · refine ⟨0, le_rfl, fun t ht => ?_⟩
      have hrel : ∫ ω, truncFn t (xi 0 ω) ∂P =
          ∫ ω, Set.indicator {ω | |xi 0 ω| ≤ t} (xi 0) ω ∂P := by
        congr 1
      rw [hrel, h1 t (by linarith)]
      simp
    · obtain ⟨D, hD0, hD⟩ := tail_first_moment (hmeas 0) alpha C hα1 hC htail
      exact ⟨D, hD0, fun t ht => drift_of_mean_zero (hmeas 0) hint hm0 alpha D hD t ht⟩
  refine ⟨C + 4 * C2 + 2 * D + 1, by positivity, ?_⟩
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
  have htneg : t ^ (-alpha) = (A ^ alpha * k)⁻¹ := by
    rw [Real.rpow_neg ht0.le, htα]
  by_cases hbig : 2 * D ≤ A ^ alpha
  swap
  · -- small `A`: the bound exceeds one
    have hlt : A ^ alpha < 2 * D := lt_of_not_ge hbig
    calc P.real {ω | ∃ j ≤ k, t < |∑ i ∈ Finset.range j, xi i ω|} ≤ 1 := measureReal_le_one
      _ ≤ (C + 4 * C2 + 2 * D + 1) * A ^ (-alpha) := by
          rw [hAneg, ← div_eq_mul_inv, le_div_iff₀ hAα]
          linarith
  -- large `A`: truncate at level `t`
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ ω, truncFn t (xi 0 ω) ∂P := ⟨_, rfl⟩
  have hZmeas (i : ℕ) : Measurable fun ω => truncFn t (xi i ω) :=
    (measurable_truncFn t).comp (hmeas i)
  have hZint (i : ℕ) : Integrable (fun ω => truncFn t (xi i ω)) P :=
    integrable_of_abs_le (hZmeas i) t fun ω => abs_truncFn_le ht0.le _
  have hYmeas (i : ℕ) : Measurable fun ω => truncFn t (xi i ω) - m :=
    (hZmeas i).sub_const m
  have hYind : iIndepFun (fun (i : ℕ) (ω : Ω) => truncFn t (xi i ω) - m) P :=
    hind.comp (fun _ x => truncFn t x - m) fun _ => (measurable_truncFn t).sub_const m
  have hYbd : ∀ (i : ℕ) (ω : Ω), |truncFn t (xi i ω) - m| ≤ t + |m| := by
    intro i ω
    have h1 := abs_le.mp (abs_truncFn_le ht0.le (xi i ω))
    have h2 := le_abs_self m
    have h3 := neg_abs_le m
    exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hZmean (i : ℕ) : ∫ ω, truncFn t (xi i ω) ∂P = m := by
    rw [hm]
    exact ((hid i).comp (measurable_truncFn t)).integral_eq
  have hYmean : ∀ i : ℕ, ∫ ω, (truncFn t (xi i ω) - m) ∂P = 0 := by
    intro i
    have hu : P.real Set.univ = 1 := by simp
    rw [integral_sub (hZint i) (integrable_const m), hZmean i, integral_const, smul_eq_mul,
      hu]
    ring
  have hYsq : ∀ i : ℕ, ∫ ω, (truncFn t (xi i ω) - m) ^ 2 ∂P ≤ C2 * t ^ (2 - alpha) := by
    intro i
    have hident : ∫ ω, (truncFn t (xi i ω) - m) ^ 2 ∂P =
        ∫ ω, (truncFn t (xi 0 ω) - m) ^ 2 ∂P :=
      ((hid i).comp (((measurable_truncFn t).sub_const m).pow_const 2)).integral_eq
    rw [hident]
    have hvar := variance_le_second_moment (P := P) (hZmeas 0) t
      fun ω => abs_truncFn_le ht0.le _
    rw [← hm] at hvar
    exact hvar.trans (hmom t ht1)
  have hkol := kolmogorov_max (P := P) (fun (i : ℕ) (ω : Ω) => truncFn t (xi i ω) - m)
    hYmeas hYind (t + |m|) hYbd hYmean (C2 * t ^ (2 - alpha)) hYsq k (t / 2) (by linarith)
  -- drift of the truncation is at most `t / 2` over `k` steps
  have hkm : (k : ℝ) * |m| ≤ t / 2 := by
    have h1 : |m| ≤ D * (t / (A ^ alpha * k)) := by
      have := hdrift t ht1
      rwa [← hm, Real.rpow_sub ht0, Real.rpow_one, htα] at this
    calc (k : ℝ) * |m| ≤ k * (D * (t / (A ^ alpha * k))) :=
          mul_le_mul_of_nonneg_left h1 hkpos.le
      _ = D * t / A ^ alpha := by field_simp
      _ ≤ t / 2 := by
          rw [div_le_iff₀ hAα]
          nlinarith [mul_le_mul_of_nonneg_right hbig ht0.le]
  -- decomposition of the bad event
  have hsub : {ω | ∃ j ≤ k, t < |∑ i ∈ Finset.range j, xi i ω|} ⊆
      (⋃ i ∈ Finset.range k, {ω | t < |xi i ω|}) ∪
        {ω | ∃ j ≤ k, t / 2 ≤ |psum (fun (i : ℕ) (ω : Ω) => truncFn t (xi i ω) - m) j ω|} := by
    rintro ω ⟨j, hj, hs⟩
    by_cases hU : ∃ i ∈ Finset.range k, t < |xi i ω|
    · left
      simpa using hU
    · right
      refine ⟨j, hj, ?_⟩
      push_neg at hU
      have hU' : ∀ i, i < k → |xi i ω| ≤ t := fun i hi => hU i (Finset.mem_range.mpr hi)
      have hS : ∑ i ∈ Finset.range j, xi i ω =
          psum (fun (i : ℕ) (ω : Ω) => truncFn t (xi i ω) - m) j ω + j * m := by
        have h1 : ∑ i ∈ Finset.range j, xi i ω = ∑ i ∈ Finset.range j, truncFn t (xi i ω) :=
          Finset.sum_congr rfl fun i hi => by
            simp [truncFn, hU' i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)]
        rw [h1]
        simp only [psum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring
      have hjm : |(j : ℝ) * m| ≤ t / 2 := by
        rw [abs_mul, Nat.abs_cast]
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (abs_nonneg m)).trans hkm
      by_contra hcon
      have hlt := abs_lt.mp (not_le.mp hcon)
      have hjm' := abs_le.mp hjm
      rw [hS] at hs
      have : |psum (fun (i : ℕ) (ω : Ω) => truncFn t (xi i ω) - m) j ω + j * m| ≤ t :=
        abs_le.mpr ⟨by linarith [hlt.1, hjm'.1], by linarith [hlt.2, hjm'.2]⟩
      linarith
  -- probability of a large single step
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
      rwa [htneg] at this
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    apply le_of_eq
    field_simp
  -- probability of a large centered truncated walk
  have hV : P.real {ω | ∃ j ≤ k,
      t / 2 ≤ |psum (fun (i : ℕ) (ω : Ω) => truncFn t (xi i ω) - m) j ω|} ≤
      4 * C2 / A ^ alpha := by
    refine hkol.trans (le_of_eq ?_)
    rw [Real.rpow_sub ht0, Real.rpow_two, htα]
    field_simp
    ring
  calc P.real {ω | ∃ j ≤ k, t < |∑ i ∈ Finset.range j, xi i ω|}
      ≤ P.real ((⋃ i ∈ Finset.range k, {ω | t < |xi i ω|}) ∪
        {ω | ∃ j ≤ k, t / 2 ≤ |psum (fun (i : ℕ) (ω : Ω) => truncFn t (xi i ω) - m) j ω|}) :=
        measureReal_mono hsub
    _ ≤ P.real (⋃ i ∈ Finset.range k, {ω | t < |xi i ω|}) + P.real {ω | ∃ j ≤ k,
        t / 2 ≤ |psum (fun (i : ℕ) (ω : Ω) => truncFn t (xi i ω) - m) j ω|} :=
        measureReal_union_le _ _
    _ ≤ C / A ^ alpha + 4 * C2 / A ^ alpha := add_le_add hU hV
    _ ≤ (C + 4 * C2 + 2 * D + 1) * A ^ (-alpha) := by
        rw [hAneg, ← add_div, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_right (by linarith) hAα.le

end Assembly

end DirectedDistances.Probability
