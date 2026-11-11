module

public import DirectedDistances.Probability.PowerTailBounds
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.OptionalStopping






public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory



@[expose] noncomputable def scaledSmallJumpLevel (ν ρ : ℝ) (n : ℕ) : ℝ :=
  ρ * (n + 1 : ℝ) ^ (1 / ν)



@[expose] noncomputable def scaledTruncatedIncrement {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (ν ρ : ℝ) (n j : ℕ) (ω : Ω) : ℝ :=
  let level := scaledSmallJumpLevel ν ρ n
  let trunc := fun ω' => X j ω' *
    Set.indicator {ω' | |X j ω'| ≤ level} (fun _ => (1 : ℝ)) ω'
  trunc ω - (if 1 < ν then ∫ ω', trunc ω' ∂P else 0)



@[expose] noncomputable def scaledSmallJumpRemainder {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (ν ρ T : ℝ) (n : ℕ) (ω : Ω) : ℝ := by
  let N : ℝ := (n + 1 : ℝ)
  let K : ℕ := ⌊N * T⌋₊
  let times := Finset.range (K + 1)
  have htimes : times.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩
  exact N ^ (-(1 / ν)) * times.sup' htimes (fun m =>
    |∑ j ∈ Finset.range m, scaledTruncatedIncrement P X ν ρ n j ω|)

private noncomputable def truncatedAbs {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ) (Z : Ω → ℝ) (ω : Ω) : ℝ :=
  |Z ω| * Set.indicator {ω | |Z ω| ≤ a} (fun _ => (1 : ℝ)) ω

private lemma truncatedAbs_measurable {Ω : Type*} [MeasurableSpace Ω]
    {a : ℝ} {Z : Ω → ℝ} (hZ : Measurable Z) :
    Measurable (truncatedAbs a Z) := by
  apply Measurable.mul
  · exact continuous_abs.measurable.comp hZ
  · exact measurable_const.indicator
      (measurableSet_le (continuous_abs.measurable.comp hZ) measurable_const)

private lemma truncatedAbs_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ) (Z : Ω → ℝ) (ω : Ω) : 0 ≤ truncatedAbs a Z ω := by
  unfold truncatedAbs
  by_cases h : |Z ω| ≤ a <;> simp [h]

private lemma truncatedAbs_le {Ω : Type*} [MeasurableSpace Ω]
    {a : ℝ} (ha : 0 ≤ a) (Z : Ω → ℝ) (ω : Ω) :
    truncatedAbs a Z ω ≤ a := by
  unfold truncatedAbs
  by_cases h : |Z ω| ≤ a
  · simp [h]
  · simp [h]
    exact ha

private lemma integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) (B : ℝ)
    (hB : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB ω)

private lemma scaledTruncatedIncrement_eq_truncated {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    {ν ρ : ℝ} (hν : ν < 1) (n j : ℕ) (ω : Ω) :
    scaledTruncatedIncrement P X ν ρ n j ω =
      X j ω * Set.indicator
        {ω | |X j ω| ≤ scaledSmallJumpLevel ν ρ n}
        (fun _ => (1 : ℝ)) ω := by
  have hnot : ¬1 < ν := by linarith
  simp [scaledTruncatedIncrement, hnot]




theorem scaledSmallJumpRemainder_prob_lt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    (_hindep : iIndepFun X P)
    {ν C T : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν)) (hT : 0 < T) :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℕ,
        P.real {ω | η < scaledSmallJumpRemainder P X ν ρ T n ω} ≤ ε := by
  intro η hη ε hε
  let p : ℝ := 1 - ν
  have hp : 0 < p := by dsimp [p]; linarith
  let q : ℝ := (2 : ℝ) ^ p
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hp
  let D : ℝ := 1 + 2 * C * q / (q - 1)
  have hD : 1 ≤ D := by
    have hden : 0 < q - 1 := by linarith
    dsimp [D]
    have hn : 0 ≤ 2 * C * q / (q - 1) :=
      div_nonneg (by positivity) hden.le
    linarith
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let b : ℝ := ε * η / (T * D)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  let ρ : ℝ := b ^ (1 / p)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact Real.rpow_pos_of_pos hb _
  have hρpow : ρ ^ p = b := by
    dsimp [ρ]
    rw [← Real.rpow_mul hb.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have hρbound : T * D / η * ρ ^ p = ε := by
    rw [hρpow]
    dsimp [b]
    field_simp
  refine ⟨ρ, hρ, ?_⟩
  intro n
  let N : ℝ := (n + 1 : ℝ)
  let s : ℝ := N ^ (1 / ν)
  let a : ℝ := ρ * s
  let K : ℕ := ⌊N * T⌋₊
  let total : Ω → ℝ := fun ω =>
    ∑ j ∈ Finset.range K, truncatedAbs a (X j) ω
  have hN : 0 < N := by dsimp [N]; positivity
  have hs : 0 < s := by
    dsimp [s]
    exact Real.rpow_pos_of_pos hN _
  have ha : 0 < a := by dsimp [a]; positivity
  have hsPow : s ^ ν = N := by
    dsimp [s]
    rw [← Real.rpow_mul hN.le, one_div,
      inv_mul_cancel₀ hν0.ne', Real.rpow_one]
  have hK : (K : ℝ) ≤ N * T := by
    dsimp [K]
    exact Nat.floor_le (mul_nonneg hN.le hT.le)
  have htotalMeas : Measurable total := by
    apply Finset.measurable_sum
    intro j hj
    exact truncatedAbs_measurable (hX j)
  have htotalInt : Integrable total P := by
    apply integrable_finsetSum
    intro j hj
    exact integrable_of_abs_le (truncatedAbs_measurable (hX j)) a
      (fun ω => by
        rw [abs_of_nonneg (truncatedAbs_nonneg a (X j) ω)]
        exact truncatedAbs_le ha.le (X j) ω)
  have htruncMeas : Measurable (fun x : ℝ =>
      |x| * Set.indicator {x : ℝ | |x| ≤ a} (fun _ => (1 : ℝ)) x) := by
    apply Measurable.mul
    · exact continuous_abs.measurable
    · exact measurable_const.indicator
        (measurableSet_le continuous_abs.measurable measurable_const)
  have hbase :
      ∫ ω, truncatedAbs a (X 0) ω ∂P ≤
        (if 1 ≤ a then D * a ^ p else a) := by
    by_cases hbig : 1 ≤ a
    · simp [hbig]
      have hMoment := truncated_first_moment_power_tail_bound (P := P) (hX 0)
        hν0 hν1 hC hTail a hbig
      simpa [truncatedAbs] using hMoment
    · simp [hbig]
      have hI : Integrable (truncatedAbs a (X 0)) P :=
        integrable_of_abs_le (truncatedAbs_measurable (hX 0)) a
          (fun ω => by
            rw [abs_of_nonneg (truncatedAbs_nonneg a (X 0) ω)]
            exact truncatedAbs_le ha.le (X 0) ω)
      have hmono : ∫ ω, truncatedAbs a (X 0) ω ∂P ≤ ∫ _ω, a ∂P :=
        integral_mono hI (integrable_const a) fun ω => truncatedAbs_le ha.le (X 0) ω
      simpa using hmono
  have htermInt : ∀ j : ℕ,
      ∫ ω, truncatedAbs a (X j) ω ∂P ≤ (if 1 ≤ a then D * a ^ p else a) := by
    intro j
    have hEq :
        ∫ ω, truncatedAbs a (X j) ω ∂P =
          ∫ ω, truncatedAbs a (X 0) ω ∂P := by
      have hdist := (hident j).comp htruncMeas
      exact hdist.integral_eq
    rw [hEq]
    exact hbase
  have htotalIntBound : ∫ ω, total ω ∂P ≤
      (K : ℝ) * (if 1 ≤ a then D * a ^ p else a) := by
    dsimp [total]
    rw [integral_finsetSum _ (fun j hj =>
      integrable_of_abs_le (truncatedAbs_measurable (hX j)) a
        (fun ω => by
          rw [abs_of_nonneg (truncatedAbs_nonneg a (X j) ω)]
          exact truncatedAbs_le ha.le (X j) ω))]
    calc ∑ j ∈ Finset.range K, ∫ ω, truncatedAbs a (X j) ω ∂P
        ≤ ∑ _j ∈ Finset.range K, (if 1 ≤ a then D * a ^ p else a) := by
            exact Finset.sum_le_sum fun j hj => htermInt j
      _ = (K : ℝ) * (if 1 ≤ a then D * a ^ p else a) := by simp
  have hscaleRemainder : ∀ ω,
      scaledSmallJumpRemainder P X ν ρ T n ω ≤ s⁻¹ * total ω := by
    intro ω
    have hlevel : scaledSmallJumpLevel ν ρ n = a := by
      simp [scaledSmallJumpLevel, a, s, N]
    have hterm : ∀ m ∈ Finset.range (K + 1),
        |∑ j ∈ Finset.range m, scaledTruncatedIncrement P X ν ρ n j ω| ≤
          total ω := by
      intro m hm
      have hmK : m ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      calc |∑ j ∈ Finset.range m, scaledTruncatedIncrement P X ν ρ n j ω|
          ≤ ∑ j ∈ Finset.range m,
              |scaledTruncatedIncrement P X ν ρ n j ω| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j ∈ Finset.range m, truncatedAbs a (X j) ω := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [scaledTruncatedIncrement_eq_truncated P X hν1 n j ω, hlevel]
          by_cases h : |X j ω| ≤ a <;> simp [truncatedAbs, h]
        _ ≤ total ω := by
          dsimp [total]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr hmK)
            (fun j hj hjK => truncatedAbs_nonneg a (X j) ω)
    unfold scaledSmallJumpRemainder
    dsimp only [N, K, s, total]
    rw [Real.rpow_neg hN.le]
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sup'_le
      intro m hm
      exact hterm m hm
    · positivity
  have hthreshold : 0 < η * s := mul_pos hη hs
  have hlargeEvent : {ω | η < scaledSmallJumpRemainder P X ν ρ T n ω} ⊆
      {ω | η * s ≤ total ω} := by
    intro ω hω
    have hlt := lt_of_lt_of_le hω (hscaleRemainder ω)
    have hmul := mul_lt_mul_of_pos_right hlt hs
    have heq : (s⁻¹ * total ω) * s = total ω := by
      field_simp
    rw [heq] at hmul
    exact hmul.le
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all P fun ω => Finset.sum_nonneg fun j hj =>
      truncatedAbs_nonneg a (X j) ω) htotalInt (η * s)
  have hprobMarkov :
      P.real {ω | η < scaledSmallJumpRemainder P X ν ρ T n ω} ≤
        (∫ ω, total ω ∂P) / (η * s) := by
    apply (le_div_iff₀ hthreshold).2
    have hmono := measureReal_mono hlargeEvent (measure_ne_top P _)
    have hmul := mul_le_mul_of_nonneg_left hmono hthreshold.le
    simpa [mul_comm] using hmul.trans hmark
  by_cases hbig : 1 ≤ a
  · simp [hbig] at htotalIntBound
    have hscale : N * a ^ p / s = ρ ^ p := by
      have haEq : a = ρ * s := rfl
      calc N * a ^ p / s
          = s ^ ν * (ρ ^ p * s ^ p) / s := by
              rw [haEq, Real.mul_rpow hρ.le hs.le, ← hsPow]
      _ = ρ ^ p := by
        have he : s ^ ν * s ^ p = s := by
          rw [← Real.rpow_add hs, show ν + p = 1 by dsimp [p]; ring,
            Real.rpow_one]
        calc s ^ ν * (ρ ^ p * s ^ p) / s
            = ρ ^ p * (s ^ ν * s ^ p) / s := by ring
          _ = ρ ^ p * s / s := by rw [he]
          _ = ρ ^ p := by field_simp
    have hbound : (K : ℝ) * (D * a ^ p) / (η * s) ≤ ε := by
      calc (K : ℝ) * (D * a ^ p) / (η * s)
          ≤ (N * T) * (D * a ^ p) / (η * s) := by
            apply div_le_div_of_nonneg_right _ hthreshold.le
            exact mul_le_mul_of_nonneg_right hK (by positivity)
        _ = T * D / η * (N * a ^ p / s) := by field_simp
        _ = T * D / η * ρ ^ p := by rw [hscale]
        _ = ε := hρbound
    calc P.real {ω | η < scaledSmallJumpRemainder P X ν ρ T n ω}
        ≤ (∫ ω, total ω ∂P) / (η * s) := hprobMarkov
      _ ≤ (K : ℝ) * (D * a ^ p) / (η * s) :=
        div_le_div_of_nonneg_right htotalIntBound hthreshold.le
      _ ≤ ε := hbound
  · simp [hbig] at htotalIntBound
    have haLt : a < 1 := lt_of_not_ge hbig
    have haPow : a ^ ν < 1 := by
      rw [← Real.one_rpow ν]
      exact Real.rpow_lt_rpow ha.le haLt hν0
    have haPowEq : a ^ ν = ρ ^ ν * N := by
      rw [show a = ρ * s by rfl, Real.mul_rpow hρ.le hs.le, hsPow]
    have hρN : ρ * N ≤ ρ ^ p := by
      have hsmall : ρ ^ ν * N < 1 := by rwa [haPowEq] at haPow
      have hpower : ρ = ρ ^ p * ρ ^ ν := by
        rw [← Real.rpow_add hρ, show p + ν = 1 by dsimp [p]; ring,
          Real.rpow_one]
      have hfact : ρ * N = ρ ^ p * (ρ ^ ν * N) := by
        calc ρ * N = (ρ ^ p * ρ ^ ν) * N := congrArg (fun x : ℝ => x * N) hpower
          _ = ρ ^ p * (ρ ^ ν * N) := by ring
      rw [hfact]
      calc ρ ^ p * (ρ ^ ν * N) ≤ ρ ^ p * 1 :=
          mul_le_mul_of_nonneg_left hsmall.le (Real.rpow_nonneg hρ.le _)
        _ = ρ ^ p := mul_one _
    have hscale : N * a / s = ρ * N := by
      rw [show a = ρ * s by rfl]
      field_simp
    have hbound : (K : ℝ) * a / (η * s) ≤ ε := by
      calc (K : ℝ) * a / (η * s)
          ≤ (N * T) * a / (η * s) := by
            apply div_le_div_of_nonneg_right _ hthreshold.le
            exact mul_le_mul_of_nonneg_right hK (le_of_lt ha)
        _ = T / η * (N * a / s) := by field_simp
        _ = T / η * (ρ * N) := by rw [hscale]
        _ ≤ T / η * ρ ^ p :=
          mul_le_mul_of_nonneg_left hρN (div_nonneg hT.le hη.le)
        _ ≤ T * D / η * ρ ^ p := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hρ.le _)
          apply div_le_div_of_nonneg_right _ hη.le
          calc T = T * 1 := by ring
            _ ≤ T * D := mul_le_mul_of_nonneg_left hD hT.le
        _ = ε := hρbound
    calc P.real {ω | η < scaledSmallJumpRemainder P X ν ρ T n ω}
        ≤ (∫ ω, total ω ∂P) / (η * s) := hprobMarkov
      _ ≤ (K : ℝ) * a / (η * s) :=
        div_le_div_of_nonneg_right htotalIntBound hthreshold.le
      _ ≤ ε := hbound

end DirectedDistances.Probability

namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
section Kolmogorov

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]



private noncomputable def psum (Y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, Y i ω

private noncomputable def psumSq (Y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (psum Y k ω) ^ 2

omit mΩ in
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

variable (Y : ℕ → Ω → ℝ)

private lemma psum_measurable (hY : ∀ i, Measurable (Y i)) (k : ℕ) :
    Measurable (psum Y k) := by
  unfold psum
  exact Finset.measurable_sum _ fun i _ => hY i

omit mΩ in
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

omit [IsProbabilityMeasure P] in
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

omit [IsProbabilityMeasure P] in
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
end DirectedDistances.Probability

namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

private lemma sjrVarianceLeSecond {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) (B : ℝ) (hB : ∀ ω, |f ω| ≤ B) :
    ∫ ω, (f ω - ∫ ω', f ω' ∂P) ^ 2 ∂P ≤ ∫ ω, (f ω) ^ 2 ∂P := by
  have hfi : Integrable f P := integrable_of_abs_le hf B hB
  have hf2i : Integrable (fun ω => (f ω) ^ 2) P :=
    integrable_of_abs_le (hf.pow_const 2) (B ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB ω) 2
  generalize hm : ∫ ω', f ω' ∂P = m
  have hfun : (fun ω => (f ω - m) ^ 2) =
      fun ω => (f ω) ^ 2 - (2 * m) * f ω + m ^ 2 := by
    funext ω
    ring
  have hu : P.real Set.univ = 1 := by simp
  have hfc : Integrable (fun ω => (2 * m) * f ω) P := hfi.const_mul _
  have hfsub : Integrable (fun ω => (f ω) ^ 2 - (2 * m) * f ω) P := hf2i.sub hfc
  rw [hfun, integral_add hfsub (integrable_const _), integral_sub hf2i hfc,
    integral_const_mul, hm, integral_const, smul_eq_mul, hu]
  nlinarith [sq_nonneg m]




theorem scaledSmallJumpRemainder_prob_gt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    (hindep : iIndepFun X P)
    {ν C T : ℝ} (hν1 : 1 < ν) (hν2 : ν < 2) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν))
    (_hint : Integrable (X 0) P) (_hmean0 : ∫ ω, X 0 ω ∂P = 0)
    (hT : 0 < T) :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℕ,
        P.real {ω | η < scaledSmallJumpRemainder P X ν ρ T n ω} ≤ ε := by
  intro η hη ε hε
  let β : ℝ := 2 - ν
  have hβ : 0 < β := by dsimp [β]; linarith
  have hν0 : 0 < ν := lt_trans zero_lt_one hν1
  let q : ℝ := (2 : ℝ) ^ β
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hβ
  let D : ℝ := 1 + 4 * C * q / (q - 1)
  have hD : 1 ≤ D := by
    have hden : 0 < q - 1 := by linarith
    dsimp [D]
    have hn : 0 ≤ 4 * C * q / (q - 1) := div_nonneg (by positivity) hden.le
    linarith
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let b : ℝ := ε * η ^ 2 / (T * D)
  have hb : 0 < b := by dsimp [b]; positivity
  let ρ : ℝ := b ^ (1 / β)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact Real.rpow_pos_of_pos hb _
  have hρpow : ρ ^ β = b := by
    dsimp [ρ]
    rw [← Real.rpow_mul hb.le, one_div, inv_mul_cancel₀ hβ.ne', Real.rpow_one]
  have hρbound : T * D / η ^ 2 * ρ ^ β = ε := by
    rw [hρpow]
    dsimp [b]
    field_simp
  refine ⟨ρ, hρ, ?_⟩
  intro n
  let N : ℝ := (n + 1 : ℝ)
  let s : ℝ := N ^ (1 / ν)
  let a : ℝ := ρ * s
  let K : ℕ := ⌊N * T⌋₊
  let v : ℝ := D * a ^ β
  have hN : 0 < N := by dsimp [N]; positivity
  have hs : 0 < s := by dsimp [s]; exact Real.rpow_pos_of_pos hN _
  have ha : 0 < a := by dsimp [a]; positivity
  have hsPow : s ^ ν = N := by
    dsimp [s]
    rw [← Real.rpow_mul hN.le, one_div, inv_mul_cancel₀ hν0.ne', Real.rpow_one]
  have hK : (K : ℝ) ≤ N * T := by
    dsimp [K]
    exact Nat.floor_le (mul_nonneg hN.le hT.le)
  let truncFn : ℝ → ℝ := fun x =>
    x * Set.indicator {y : ℝ | |y| ≤ a} (fun _ => (1 : ℝ)) x
  have htruncFn : Measurable truncFn := by
    dsimp [truncFn]
    apply Measurable.mul measurable_id
    exact measurable_const.indicator
      (measurableSet_le continuous_abs.measurable measurable_const)
  let trunc : ℕ → Ω → ℝ := fun j ω => truncFn (X j ω)
  have htruncMeas (j : ℕ) : Measurable (trunc j) := (htruncFn.comp (hX j))
  have htruncAbs (j : ℕ) (ω : Ω) : |trunc j ω| ≤ a := by
    dsimp [trunc, truncFn]
    by_cases h : |X j ω| ≤ a
    · simp [h]
    · simp [h]
      exact ha.le
  have htruncInt (j : ℕ) : Integrable (trunc j) P :=
    integrable_of_abs_le (htruncMeas j) a (htruncAbs j)
  let m : ℝ := ∫ ω, trunc 0 ω ∂P
  let Z : ℕ → Ω → ℝ := fun j ω => trunc j ω - m
  have htruncMeanEq (j : ℕ) : ∫ ω, trunc j ω ∂P = m := by
    dsimp [m, trunc]
    exact ((hident j).comp htruncFn).integral_eq
  have htruncMeanAbs (j : ℕ) : |∫ ω, trunc j ω ∂P| ≤ a := by
    calc |∫ ω, trunc j ω ∂P| = ‖∫ ω, trunc j ω ∂P‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ ω, ‖trunc j ω‖ ∂P := norm_integral_le_integral_norm _
      _ = ∫ ω, |trunc j ω| ∂P := by simp only [Real.norm_eq_abs]
      _ ≤ ∫ _ω, a ∂P := integral_mono (htruncInt j).norm (integrable_const a)
        (fun ω => htruncAbs j ω)
      _ = a := by simp
  have hZmeas (j : ℕ) : Measurable (Z j) := (htruncMeas j).sub_const m
  have hZbound (j : ℕ) (ω : Ω) : |Z j ω| ≤ 2 * a := by
    have ht := abs_le.mp (htruncAbs j ω)
    have hm : |m| ≤ a := by
      rw [← htruncMeanEq j]
      exact htruncMeanAbs j
    have hm' := abs_le.mp hm
    apply abs_le.mpr
    constructor <;> dsimp [Z] <;> linarith
  have hZint (j : ℕ) : Integrable (Z j) P :=
    integrable_of_abs_le (hZmeas j) (2 * a) (hZbound j)
  have hZmean (j : ℕ) : ∫ ω, Z j ω ∂P = 0 := by
    have hu : P.real Set.univ = 1 := by simp
    dsimp [Z]
    rw [integral_sub (htruncInt j) (integrable_const m), htruncMeanEq j,
      integral_const, smul_eq_mul, hu]
    ring
  have hZind : iIndepFun Z P :=
    hindep.comp (fun _ x => truncFn x - m) fun _ => htruncFn.sub_const m
  have hZbd (j : ℕ) (ω : Ω) : |Z j ω| ≤ 2 * a := hZbound j ω
  have hZsqMeas (j : ℕ) : Measurable (fun ω => (Z j ω) ^ 2) :=
    (hZmeas j).pow_const 2
  have htruncSqInt (j : ℕ) : Integrable (fun ω => (trunc j ω) ^ 2) P :=
    integrable_of_abs_le ((htruncMeas j).pow_const 2) (a ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (htruncAbs j ω) 2
  have hbigMoment (hbig : 1 ≤ a) :
      ∫ ω, (trunc 0 ω) ^ 2 ∂P ≤ D * a ^ β := by
    have h := truncated_second_moment_power_tail_bound (P := P) (hX 0)
      hν1 hν2 hC hTail a hbig
    simpa [trunc, truncFn, Set.indicator_apply] using h
  have hsmallMoment (hsmall : a < 1) :
      ∫ ω, (trunc 0 ω) ^ 2 ∂P ≤ D * a ^ β := by
    have ha1 : a ≤ 1 := hsmall.le
    have haPow : a ^ (2 : ℕ) ≤ a ^ β := by
      have h := Real.rpow_le_rpow_of_exponent_ge ha ha1
        (show β ≤ (2 : ℝ) by dsimp [β]; linarith)
      rw [← Real.rpow_natCast a (2 : ℕ)]
      exact h
    have hmono : ∫ ω, (trunc 0 ω) ^ 2 ∂P ≤ ∫ _ω, a ^ 2 ∂P :=
      integral_mono (htruncSqInt 0) (integrable_const (a ^ 2)) fun ω => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (htruncAbs 0 ω) 2
    calc ∫ ω, (trunc 0 ω) ^ 2 ∂P ≤ a ^ 2 := by simpa using hmono
      _ ≤ D * a ^ β := by
        apply le_trans haPow
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg ha.le β))
  have hbase : ∫ ω, (trunc 0 ω) ^ 2 ∂P ≤ v := by
    by_cases hbig : 1 ≤ a
    · simpa [v] using hbigMoment hbig
    · simpa [v] using hsmallMoment (lt_of_not_ge hbig)
  have hsecond : ∀ j : ℕ, ∫ ω, (Z j ω) ^ 2 ∂P ≤ v := by
    intro j
    have hdist : ∫ ω, (Z j ω) ^ 2 ∂P = ∫ ω, (Z 0 ω) ^ 2 ∂P := by
      dsimp [Z, trunc]
      exact ((hident j).comp ((htruncFn.sub_const m).pow_const 2)).integral_eq
    have hvar := sjrVarianceLeSecond (P := P) (htruncMeas 0) a (htruncAbs 0)
    calc ∫ ω, (Z j ω) ^ 2 ∂P = ∫ ω, (Z 0 ω) ^ 2 ∂P := hdist
      _ ≤ ∫ ω, (trunc 0 ω) ^ 2 ∂P := by simpa [Z, m] using hvar
      _ ≤ v := hbase
  have hlevel : scaledSmallJumpLevel ν ρ n = a := by simp [scaledSmallJumpLevel, a, s, N]
  have hinc (j : ℕ) (ω : Ω) :
      scaledTruncatedIncrement P X ν ρ n j ω = Z j ω := by
    rw [scaledTruncatedIncrement, hlevel]
    simp only [hν1]
    change trunc j ω - (∫ ω', trunc j ω' ∂P) = trunc j ω - m
    rw [htruncMeanEq j]
  have hsumEq (m' : ℕ) (ω : Ω) :
      (∑ j ∈ Finset.range m', scaledTruncatedIncrement P X ν ρ n j ω) =
        psum Z m' ω := by
    rw [psum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hinc j ω
  let times : Finset ℕ := Finset.range (K + 1)
  have htimes : times.Nonempty := ⟨0, by simp [times]⟩
  have hremEq (ω : Ω) : scaledSmallJumpRemainder P X ν ρ T n ω =
      s⁻¹ * times.sup' htimes (fun m' => |psum Z m' ω|) := by
    simp only [scaledSmallJumpRemainder, N, K, times]
    rw [Real.rpow_neg hN.le]
    have hsup := Finset.sup'_congr (s := Finset.range (K + 1)) (H := by simp)
      rfl (fun m' hm' => congrArg abs (hsumEq m' ω))
    rw [hsup]
  have hlargeSub : {ω | η < scaledSmallJumpRemainder P X ν ρ T n ω} ⊆
      {ω | ∃ j ≤ K, η * s ≤ |psum Z j ω|} := by
    intro ω hω
    change η < scaledSmallJumpRemainder P X ν ρ T n ω at hω
    rw [hremEq ω] at hω
    have hmul := mul_lt_mul_of_pos_right hω hs
    have hcancel : (s⁻¹ * times.sup' htimes (fun m' => |psum Z m' ω|)) * s =
        times.sup' htimes (fun m' => |psum Z m' ω|) := by field_simp
    rw [hcancel] at hmul
    have hsSup : η * s ≤ times.sup' htimes (fun m' => |psum Z m' ω|) := hmul.le
    obtain ⟨j, hj, hjbound⟩ := (Finset.le_sup'_iff (s := times) (H := htimes)
      (f := fun m' => |psum Z m' ω|) (a := η * s)).mp hsSup
    have hj' : j < K + 1 := Finset.mem_range.mp (by simpa [times] using hj)
    exact ⟨j, Nat.lt_succ_iff.mp hj', hjbound⟩
  have hKol := kolmogorov_max (P := P) Z hZmeas hZind (2 * a) hZbd
    hZmean v hsecond K (η * s) (mul_pos hη hs)
  have hprob :
      P.real {ω | η < scaledSmallJumpRemainder P X ν ρ T n ω} ≤ K * v / (η * s) ^ 2 := by
    exact (measureReal_mono hlargeSub).trans hKol
  have hscale : N * a ^ β / s ^ 2 = ρ ^ β := by
    have hsexp : s ^ ν * s ^ β = s ^ (2 : ℝ) := by
      rw [← Real.rpow_add hs, show ν + β = 2 by dsimp [β]; ring]
    calc N * a ^ β / s ^ 2
        = s ^ ν * (ρ ^ β * s ^ β) / s ^ 2 := by
            rw [← hsPow, show a = ρ * s by rfl, Real.mul_rpow hρ.le hs.le]
      _ = ρ ^ β * (s ^ ν * s ^ β) / s ^ 2 := by ring
      _ = ρ ^ β := by
        rw [hsexp, ← Real.rpow_natCast s (2 : ℕ)]
        norm_num
        field_simp
  have hbound : K * v / (η * s) ^ 2 ≤ ε := by
    calc K * v / (η * s) ^ 2
        ≤ (N * T) * v / (η * s) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg (η * s))
          exact mul_le_mul_of_nonneg_right hK (mul_nonneg
            (le_trans (by norm_num) hD) (Real.rpow_nonneg ha.le β))
      _ = (T * D / η ^ 2) * (N * a ^ β / s ^ 2) := by
          dsimp [v]
          field_simp
      _ = T * D / η ^ 2 * ρ ^ β := by rw [hscale]
      _ = ε := hρbound
  exact hprob.trans hbound

end DirectedDistances.Probability
