module

public import DirectedDistances.RandomWalk.IIDWalkTube
import DirectedDistances.RandomWalk.IIDWalkMaximal
import Mathlib.Probability.Independence.InfinitePi

/-! # Quantitative endpoint estimates for tube assembly -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

/-- Portmanteau with any specified threshold below the limiting mass, uniformly
over block starting times (`lem-walk-bdy-sum`, -/
theorem iidCodeWalk_endpoint_open_lower_bound_of_lt
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (η : ℝ)
    (hη : η < iidEndpointLimitLaw.real
      ((fun z : ℝ × ℝ => (z.1, (z.2 - z.1) / 2)) ⁻¹' U)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s : ℕ,
      η ≤ iidCodeMeasure.real {ω | (Real.sqrt (m : ℝ))⁻¹ •
        (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
         ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ U} := by
  by_cases hηneg : η < 0
  · exact ⟨0, fun _ _ _ => hηneg.le.trans (measureReal_nonneg)⟩
  have hηnonneg : 0 ≤ η := le_of_not_gt hηneg
  let Y : ℝ × ℝ → ℝ × ℝ := fun z => (z.1, (z.2 - z.1) / 2)
  have hY : Measurable Y := by fun_prop
  have hsmall : ENNReal.ofReal η < (iidEndpointLimitLaw.map Y) U := by
    rw [Measure.map_apply hY hU.measurableSet]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hηnonneg (measure_ne_top _ _)).mpr hη
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    codeWalk_endpoint_clt.tendsto hU
  have hevent : ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal η <
        (iidCodeMeasure.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ •
          (((codeWalk ω m).1 : ℝ), ((codeWalk ω m).2 : ℝ)))) U :=
    eventually_lt_of_lt_liminf (hsmall.trans_le hport)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hevent
  refine ⟨m₀, fun m hm s => ?_⟩
  have h := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
    (hm₀ m hm).le
  have hmmeas : Measurable (fun ω => (Real.sqrt (m : ℝ))⁻¹ •
      (((codeWalk ω m).1 : ℝ), ((codeWalk ω m).2 : ℝ))) :=
    (measurable_of_countable (fun z : ℤ × ℤ =>
      (Real.sqrt (m : ℝ))⁻¹ • ((z.1 : ℝ), (z.2 : ℝ)))).comp
      (measurable_pi_apply m |>.comp measurable_codeWalk)
  rw [Measure.map_apply hmmeas hU.measurableSet] at h
  have hstat := (identDistrib_codeWalk_normalized_block s m).measure_mem_eq hU.measurableSet
  change iidCodeMeasure {ω | (Real.sqrt (m : ℝ))⁻¹ •
      (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
       ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ U} =
    iidCodeMeasure {ω | (Real.sqrt (m : ℝ))⁻¹ •
      (((codeWalk ω m).1 : ℝ), ((codeWalk ω m).2 : ℝ)) ∈ U} at hstat
  simpa only [measureReal_def, hstat, Set.preimage] using h

/-- Explicit density bound on the box used for endpoint windows -/
theorem gaussianPDFReal_lower_bound_on_box (v : ℝ≥0)
    (hvlo : (2 / 3 : ℝ) ≤ v) (hvhi : (v : ℝ) ≤ 2)
    (x : ℝ) (hx : |x| ≤ 4) :
    Real.exp (-12) / 4 ≤ gaussianPDFReal 0 v x := by
  have hvpos : (0 : ℝ) < v := by linarith
  have hdenpos : 0 < Real.sqrt (2 * Real.pi * v) := by positivity
  have hden : Real.sqrt (2 * Real.pi * v) ≤ 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · calc
        2 * Real.pi * (v : ℝ) ≤ 2 * 4 * 2 := by
          gcongr
          exact Real.pi_le_four
        _ = (4 : ℝ) ^ 2 := by norm_num
  have hsq : x ^ 2 ≤ 16 := by
    have h := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 4)).mpr hx
    norm_num only [sq_abs, show (4 : ℝ) ^ 2 = 16 by norm_num] at h
    exact h
  have hexponent : (-12 : ℝ) ≤ -(x ^ 2) / (2 * v) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (v : ℝ))).mpr
    nlinarith
  rw [gaussianPDFReal, sub_zero]
  calc
    Real.exp (-12) / 4 = (4 : ℝ)⁻¹ * Real.exp (-12) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x ^ 2) / (2 * v)) := by
      apply mul_le_mul
      · exact (inv_le_inv₀ (by norm_num) hdenpos).mpr hden
      · exact Real.exp_le_exp.mpr hexponent
      · positivity
      · positivity

/-- A scalar interval in the bounded box has an explicit Gaussian mass -/
theorem gaussianReal_interval_lower_bound (v : ℝ≥0)
    (hvlo : (2 / 3 : ℝ) ≤ v) (hvhi : (v : ℝ) ≤ 2)
    (a r : ℝ) (ha : |a| ≤ 3) (hr : 0 < r) (hrhi : r ≤ 1) :
    Real.exp (-12) / 4 * r ≤
      (gaussianReal 0 v).real (Set.Ioo (a - r / 2) (a + r / 2)) := by
  have hv : v ≠ 0 := by intro h; simp only [h, NNReal.coe_zero] at hvlo; linarith
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 hv,
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _))]
  have hvol : volume.real (Set.Ioo (a - r / 2) (a + r / 2)) = r := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  have hbound := setIntegral_ge_of_const_le_real
    (μ := volume) (f := gaussianPDFReal 0 v) measurableSet_Ioo
    (show volume (Set.Ioo (a - r / 2) (a + r / 2)) ≠ ⊤ by
      simp only [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    (fun x hx => gaussianPDFReal_lower_bound_on_box v hvlo hvhi x (by
      rcases abs_le.mp ha with ⟨hal, hau⟩
      exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
    (integrable_gaussianPDFReal 0 v).integrableOn
  rwa [hvol] at hbound

/-- Explicit lower bound for the limiting mass of a raw-coordinate endpoint
ball. Only radii at most one are needed for the shrinking windows in -/
theorem iidEndpointLimitLaw_ball_lower_bound (z : ℝ × ℝ) (hz : ‖z‖ ≤ 1)
    (r : ℝ) (hr : 0 < r) (hrhi : r ≤ 1) :
    Real.exp (-24) / 16 * r ^ 2 ≤ iidEndpointLimitLaw.real
      ((fun w : ℝ × ℝ => (w.1, (w.2 - w.1) / 2)) ⁻¹' Metric.ball z r) := by
  have hz1 : |z.1| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le z).trans hz
  have hz2 : |z.2| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le z).trans hz
  have hzc : |z.1 + 2 * z.2| ≤ 3 := by
    calc
      |z.1 + 2 * z.2| ≤ |z.1| + |2 * z.2| := abs_add_le _ _
      _ ≤ 3 := by rw [abs_mul]; norm_num; linarith
  let A := Set.Ioo (z.1 - r / 2) (z.1 + r / 2)
  let B := Set.Ioo (z.1 + 2 * z.2 - r / 2) (z.1 + 2 * z.2 + r / 2)
  have hsub : A ×ˢ B ⊆
      (fun w : ℝ × ℝ => (w.1, (w.2 - w.1) / 2)) ⁻¹' Metric.ball z r := by
    intro w hw
    rcases hw with ⟨⟨h1l, h1u⟩, ⟨h2l, h2u⟩⟩
    simp only [Set.mem_preimage, Metric.mem_ball, Prod.dist_eq,
      Real.dist_eq, max_lt_iff]
    constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
  have h1 := gaussianReal_interval_lower_bound ((2 : ℝ≥0) / 3)
    (by norm_num) (by norm_num) z.1 r (hz1.trans (by norm_num)) hr hrhi
  have h2 := gaussianReal_interval_lower_bound (2 : ℝ≥0)
    (by norm_num) (by norm_num) (z.1 + 2 * z.2) r hzc hr hrhi
  calc
    Real.exp (-24) / 16 * r ^ 2 = (Real.exp (-12) / 4 * r) ^ 2 := by
      rw [show (-24 : ℝ) = -12 + -12 by norm_num, Real.exp_add]
      ring
    _ ≤ (gaussianReal 0 ((2 : ℝ≥0) / 3)).real A *
        (gaussianReal 0 (2 : ℝ≥0)).real B := by
      rw [pow_two]
      exact mul_le_mul h1 h2 (by positivity) measureReal_nonneg
    _ = iidEndpointLimitLaw.real (A ×ˢ B) := by
      rw [iidEndpointLimitLaw, measureReal_prod_prod]
    _ ≤ _ := measureReal_mono hsub

/-- A concrete even block count for the endpoint-minus-tail estimate in -/
theorem iidTube_explicit_constants :
    Even (3276800 : ℕ) ∧ 0 < Real.exp (-24) / 16 ∧
    8 * Real.exp (-(3276800 : ℝ) / 3200) ≤
      (Real.exp (-24) / 16) * ((1 / 20 : ℝ) ^ 2 / 3276800) / 2 ∧
    0 < (Real.exp (-24) / 16) * (1 / 20 : ℝ) ^ 2 / (2 * 3276800) -
      4 * Real.exp (-(3276800 : ℝ) / 3200) := by
  have hlarge : (335544320000 : ℝ) < Real.exp 1000 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 126)
      (show (126 : ℝ) ≤ Real.exp 125 by linarith [Real.add_one_le_exp (125 : ℝ)]) 8
    have heq : Real.exp (1000 : ℝ) = Real.exp 125 ^ 8 := by
      convert Real.exp_nat_mul (125 : ℝ) 8 using 1; norm_num
    rw [← heq] at hpow
    norm_num at hpow ⊢
    linarith only [hpow]
  have heq : Real.exp (-1024 : ℝ) = Real.exp (-24) / Real.exp 1000 := by
    rw [← Real.exp_sub]
    norm_num
  have hsmall : 8 * Real.exp (-1024 : ℝ) ≤ Real.exp (-24) / 41943040000 := by
    rw [heq]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 41943040000)).mpr
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (div_le_iff₀ (Real.exp_pos 1000)).mpr
    nlinarith only [hlarge, Real.exp_pos (-24)]
  refine ⟨⟨1638400, by norm_num⟩, by positivity, ?_, ?_⟩
  · convert hsmall using 1 <;> norm_num; ring
  · norm_num at hsmall ⊢
    have hpos : 0 < Real.exp (-24 : ℝ) / 41943040000 := by positivity
    linarith only [hsmall, hpos]

/-- The explicit half-Gaussian-mass endpoint bound used for each fixed block -/
theorem iidCodeWalk_endpoint_ball_explicit_lower_bound
    (z : ℝ × ℝ) (hz : ‖z‖ ≤ 1) (r : ℝ) (hr : 0 < r) (hrhi : r ≤ 1) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s : ℕ,
      (Real.exp (-24) / 16) * r ^ 2 / 2 ≤ iidCodeMeasure.real {ω |
        (Real.sqrt (m : ℝ))⁻¹ •
          (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
           ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ Metric.ball z r} := by
  apply iidCodeWalk_endpoint_open_lower_bound_of_lt _ Metric.isOpen_ball
  exact (half_lt_self (by positivity : 0 < (Real.exp (-24) / 16) * r ^ 2)).trans_le
    (iidEndpointLimitLaw_ball_lower_bound z hz r hr hrhi)

/-- Explicit endpoint mass uniform over the unit ball of centers. The cover
uses windows of radius `3r/4`, retaining more than half of the explicit
Gaussian lower bound (`lem-walk-bdy-sum`, -/
theorem iidCodeWalk_endpoint_unitBall_explicit_lower_bound
    (r : ℝ) (hr : 0 < r) (hrhi : r ≤ 1) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s : ℕ, ∀ z : ℝ × ℝ, ‖z‖ ≤ 1 →
      (Real.exp (-24) / 16) * r ^ 2 / 2 ≤ iidCodeMeasure.real {ω |
        (Real.sqrt (m : ℝ))⁻¹ •
          (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
           ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ Metric.ball z r} := by
  classical
  let C : Set (ℝ × ℝ) := Metric.closedBall 0 1
  have hC : IsCompact C := isCompact_closedBall 0 1
  have hpoint (x : C) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s : ℕ,
      (Real.exp (-24) / 16) * r ^ 2 / 2 ≤ iidCodeMeasure.real {ω |
        (Real.sqrt (m : ℝ))⁻¹ •
          (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
           ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈
              Metric.ball x.val (3 * r / 4)} := by
    apply iidCodeWalk_endpoint_open_lower_bound_of_lt _ Metric.isOpen_ball
    have hx : ‖x.val‖ ≤ 1 := by
      simpa only [C, Metric.mem_closedBall, dist_zero_right] using x.property
    have hmass := iidEndpointLimitLaw_ball_lower_bound x.val hx (3 * r / 4)
      (by positivity) (by linarith only [hrhi])
    have hpos : 0 < (Real.exp (-24) / 16) * r ^ 2 := by positivity
    exact (show (Real.exp (-24) / 16) * r ^ 2 / 2 <
      (Real.exp (-24) / 16) * (3 * r / 4) ^ 2 by nlinarith only [hpos]).trans_le hmass
  choose m₀ hmass using hpoint
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => Metric.ball x.val (r / 4))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by positivity)⟩)
  let x₀ : C := ⟨0, by simp only [C, Metric.mem_closedBall, dist_self]; norm_num⟩
  let t' : Finset C := insert x₀ t
  refine ⟨t'.sup m₀, fun m hm s z hz => ?_⟩
  have hzC : z ∈ C := by simpa only [C, Metric.mem_closedBall, dist_zero_right] using hz
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht hzC)
  obtain ⟨hxt, hzx⟩ := Set.mem_iUnion.mp hx
  have hxt' : x ∈ t' := Finset.mem_insert_of_mem hxt
  have hballs : Metric.ball x.val (3 * r / 4) ⊆ Metric.ball z r := by
    apply Metric.ball_subset_ball'
    have hd : dist x.val z < r / 4 := by
      simpa only [Metric.mem_ball, dist_comm] using hzx
    linarith only [hd]
  exact (hmass x m ((Finset.le_sup (f := m₀) hxt').trans hm) s).trans
    (measureReal_mono (fun _ hω => hballs hω))

/-- Positive single-block mass with explicit constants. The maximal-tail
statement is the sole additional input of this intermediate lemma for -/
theorem iidCodeWalk_explicit_block_mass_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))))
    : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s : ℕ, ∀ z : ℝ × ℝ, ‖z‖ ≤ 1 →
      (Real.exp (-24) / 16) * (1 / 20 : ℝ) ^ 2 / (2 * 3276800) -
        4 * Real.exp (-(3276800 : ℝ) / 3200) ≤
      iidCodeMeasure.real {ω |
        (Real.sqrt (m : ℝ))⁻¹ •
          (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
           ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈
            Metric.ball z ((1 / 20 : ℝ) / Real.sqrt 3276800) ∧
        ∀ k ≤ m,
          |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| <
            Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40 ∧
          |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)| <
            Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40} := by
  let r : ℝ := (1 / 20) / Real.sqrt 3276800
  have hspos : 0 < Real.sqrt (3276800 : ℝ) := by positivity
  have hssq : Real.sqrt (3276800 : ℝ) ^ 2 = 3276800 := Real.sq_sqrt (by norm_num)
  have hr : 0 < r := by positivity
  have hrhi : r ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ hspos).mpr
    have hsone : 1 ≤ Real.sqrt (3276800 : ℝ) :=
      Real.one_le_sqrt.mpr (by norm_num)
    linarith only [hsone]
  obtain ⟨m₀, hmass⟩ := iidCodeWalk_endpoint_unitBall_explicit_lower_bound r hr hrhi
  refine ⟨max 1 m₀, fun m hm s z hz => ?_⟩
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 m₀).trans hm)
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hmsq : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt hmreal.le
  let a : ℝ := Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40
  have ha : 0 < a := by positivity
  have hexponent : -(a ^ 2) / (2 * (m : ℝ)) = -(3276800 : ℝ) / 3200 := by
    dsimp [a]
    rw [div_pow, mul_pow, hssq, hmsq]
    field_simp; ring
  have hconstant : (Real.exp (-24) / 16) * r ^ 2 / 2 =
      (Real.exp (-24) / 16) * (1 / 20 : ℝ) ^ 2 / (2 * 3276800) := by
    dsimp [r]
    rw [div_pow, hssq]
    ring
  let A : Set (ℕ → Fin 3) := {ω | (Real.sqrt (m : ℝ))⁻¹ •
    (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
     ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ Metric.ball z r}
  let B : Set (ℕ → Fin 3) := {ω | ∃ k, k ≤ m ∧
    (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
     a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)}
  have hendpoint := hmass m ((le_max_right 1 m₀).trans hm) s z hz
  rw [hconstant] at hendpoint
  have htail' := htail s m hmpos a ha
  rw [hexponent] at htail'
  have hgood : A \ B ⊆ {ω |
      (Real.sqrt (m : ℝ))⁻¹ •
        (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
         ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ Metric.ball z r ∧
      ∀ k ≤ m,
        |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| < a ∧
        |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)| < a} := by
    intro ω hω
    refine ⟨hω.1, fun k hk => ⟨?_, ?_⟩⟩
    · exact lt_of_not_ge (fun h => hω.2 ⟨k, hk, Or.inl h⟩)
    · exact lt_of_not_ge (fun h => hω.2 ⟨k, hk, Or.inr h⟩)
  exact (sub_le_sub hendpoint htail').trans
    ((le_measureReal_sdiff (μ := iidCodeMeasure) (s₁ := A) (s₂ := B)).trans
      (measureReal_mono hgood))

/-- The finite increment vectors in disjoint consecutive code blocks are -/
theorem iIndepFun_codeWalk_blocks (K m : ℕ) (hm : 0 < m) :
    iIndepFun (fun (k : Fin K) ω => fun i : Fin m =>
      codeWalk ω (k.val * m + i.val + 1) - codeWalk ω (k.val * m + i.val))
      iidCodeMeasure := by
  let X (k : Fin K) (i : Fin m) (ω : ℕ → Fin 3) :=
    codeWalk ω (k.val * m + i.val + 1) - codeWalk ω (k.val * m + i.val)
  have hmeas (k : Fin K) (i : Fin m) : Measurable (X k i) :=
    measurable_codeWalk_increment _
  have hinj : Function.Injective (fun p : Fin K × Fin m => p.1.val * m + p.2.val) := by
    intro p q hpq
    change p.1.val * m + p.2.val = q.1.val * m + q.2.val at hpq
    have hk := congrArg (fun n : ℕ => n / m) hpq
    simp only [Nat.mul_comm _ m, Nat.mul_add_div hm, Nat.div_eq_of_lt p.2.isLt,
      Nat.div_eq_of_lt q.2.isLt, Nat.add_zero] at hk
    have hi : p.2.val = q.2.val := by rw [hk] at hpq; exact Nat.add_left_cancel hpq
    exact Prod.ext (Fin.ext hk) (Fin.ext hi)
  have hflat : iIndepFun (fun (p : Fin K × Fin m) ω => X p.1 p.2 ω) iidCodeMeasure :=
    iIndepFun_codeWalk_increments.precomp hinj
  have hrow (k : Fin K) : iIndepFun (X k) iidCodeMeasure :=
    iIndepFun_codeWalk_increments.precomp (g := fun i : Fin m => k.val * m + i.val)
      (fun i j h => Fin.ext (Nat.add_left_cancel h))
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun k => Measurable.of_eval (hmeas k))]
  change iidCodeMeasure.map (fun ω k i => X k i ω) = _
  calc
    iidCodeMeasure.map (fun ω k i => X k i ω) =
        (iidCodeMeasure.map (fun ω (p : Fin K × Fin m) => X p.1 p.2 ω)).map
          (MeasurableEquiv.curry (Fin K) (Fin m) (ℤ × ℤ)) :=
      (Measure.map_map (MeasurableEquiv.curry _ _ _).measurable
        (Measurable.of_eval (fun p => hmeas p.1 p.2))).symm
    _ = (Measure.infinitePi (fun p : Fin K × Fin m =>
        iidCodeMeasure.map (X p.1 p.2))).map
          (MeasurableEquiv.curry (Fin K) (Fin m) (ℤ × ℤ)) :=
      congrArg (fun μ : Measure ((Fin K × Fin m) → ℤ × ℤ) =>
        μ.map (MeasurableEquiv.curry (Fin K) (Fin m) (ℤ × ℤ)))
          (hflat.map_fun_eq_infinitePi_map (fun p => hmeas p.1 p.2))
    _ = Measure.infinitePi (fun k : Fin K => Measure.infinitePi
        (fun i : Fin m => iidCodeMeasure.map (X k i))) :=
      Measure.infinitePi_map_curry (fun k i => iidCodeMeasure.map (X k i))
    _ = _ := by
      congr 1
      funext k
      exact (hrow k).map_fun_eq_infinitePi_map (hmeas k) |>.symm

/-- Exact product formula for arbitrary events depending on the separate
finite increment vectors (`lem-walk-bdy-sum`, -/
theorem iidCodeWalk_blocks_real_product (K m : ℕ) (hm : 0 < m)
    (S : Fin K → Set (Fin m → ℤ × ℤ)) :
    iidCodeMeasure.real {ω | ∀ k : Fin K,
      (fun i : Fin m => codeWalk ω (k.val * m + i.val + 1) -
        codeWalk ω (k.val * m + i.val)) ∈ S k} =
      ∏ k : Fin K, iidCodeMeasure.real {ω |
        (fun i : Fin m => codeWalk ω (k.val * m + i.val + 1) -
          codeWalk ω (k.val * m + i.val)) ∈ S k} := by
  have h := (iIndepFun_codeWalk_blocks K m hm).measure_inter_preimage_eq_mul
    Finset.univ (sets := S) (fun _ _ => (Set.to_countable _).measurableSet)
  simpa [measureReal_def, Set.preimage, Set.iInter_ofPred, ENNReal.toReal_prod]
    using congrArg ENNReal.toReal h

/-- Independence includes the complete within-block paths, so it applies
jointly to endpoint and maximum events (`lem-walk-bdy-sum`, -/
theorem iIndepFun_codeWalk_block_paths (K m : ℕ) (hm : 0 < m) :
    iIndepFun (fun (k : Fin K) ω => fun j : Fin (m + 1) =>
      codeWalk ω (k.val * m + j.val) - codeWalk ω (k.val * m)) iidCodeMeasure := by
  let Y (v : Fin m → ℤ × ℤ) (j : Fin (m + 1)) : ℤ × ℤ :=
    ∑ i : Fin j.val, v ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩
  have h := (iIndepFun_codeWalk_blocks K m hm).comp (fun _ => Y)
    (fun _ => measurable_of_countable _)
  convert h using 1
  funext k ω j
  dsimp only [Y, Function.comp_def]
  rw [codeWalk_block_eq_sum, ← Fin.sum_univ_eq_sum_range]

/-- Exact product formula for separate events on the full finite block -/
theorem iidCodeWalk_block_paths_real_product (K m : ℕ) (hm : 0 < m)
    (S : Fin K → Set (Fin (m + 1) → ℤ × ℤ)) :
    iidCodeMeasure.real {ω | ∀ k : Fin K,
      (fun j : Fin (m + 1) => codeWalk ω (k.val * m + j.val) -
        codeWalk ω (k.val * m)) ∈ S k} =
      ∏ k : Fin K, iidCodeMeasure.real {ω |
        (fun j : Fin (m + 1) => codeWalk ω (k.val * m + j.val) -
          codeWalk ω (k.val * m)) ∈ S k} := by
  have h := (iIndepFun_codeWalk_block_paths K m hm).measure_inter_preimage_eq_mul
    Finset.univ (sets := S) (fun _ _ => (Set.to_countable _).measurableSet)
  simpa [measureReal_def, Set.preimage, Set.iInter_ofPred, ENNReal.toReal_prod]
    using congrArg ENNReal.toReal h

/-- Uniform positive product mass for endpoint and maximum constraints on
finitely many disjoint blocks. This is an intermediate tube-assembly estimate -/
theorem iidCodeWalk_explicit_blocks_mass_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))))
    (K : ℕ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ z : Fin K → ℝ × ℝ, (∀ k, ‖z k‖ ≤ 1) →
      ((Real.exp (-24) / 16) * (1 / 20 : ℝ) ^ 2 / (2 * 3276800) -
        4 * Real.exp (-(3276800 : ℝ) / 3200)) ^ K ≤
      iidCodeMeasure.real {ω | ∀ k : Fin K,
        (Real.sqrt (m : ℝ))⁻¹ •
          (((codeWalk ω (k.val * m + m) - codeWalk ω (k.val * m)).1 : ℝ),
           ((codeWalk ω (k.val * m + m) - codeWalk ω (k.val * m)).2 : ℝ)) ∈
            Metric.ball (z k) ((1 / 20 : ℝ) / Real.sqrt 3276800) ∧
        ∀ j ≤ m,
          |((codeWalk ω (k.val * m + j) - codeWalk ω (k.val * m)).1 : ℝ)| <
            Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40 ∧
          |((codeWalk ω (k.val * m + j) - codeWalk ω (k.val * m)).2 : ℝ)| <
            Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40} := by
  classical
  obtain ⟨m₀, hmass⟩ := iidCodeWalk_explicit_block_mass_of_tail htail
  refine ⟨max 1 m₀, fun m hm z hz => ?_⟩
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm)
  let c : ℝ := (Real.exp (-24) / 16) * (1 / 20 : ℝ) ^ 2 / (2 * 3276800) -
    4 * Real.exp (-(3276800 : ℝ) / 3200)
  have hc : 0 ≤ c := iidTube_explicit_constants.2.2.2.le
  let S (k : Fin K) : Set (Fin (m + 1) → ℤ × ℤ) := {p |
    (Real.sqrt (m : ℝ))⁻¹ •
      (((p ⟨m, by omega⟩).1 : ℝ), ((p ⟨m, by omega⟩).2 : ℝ)) ∈
        Metric.ball (z k) ((1 / 20 : ℝ) / Real.sqrt 3276800) ∧
    ∀ j : Fin (m + 1),
      |((p j).1 : ℝ)| < Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40 ∧
      |((p j).2 : ℝ)| < Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40}
  have hS (k : Fin K) (ω : ℕ → Fin 3) :
      (fun j : Fin (m + 1) => codeWalk ω (k.val * m + j.val) -
        codeWalk ω (k.val * m)) ∈ S k ↔
      (Real.sqrt (m : ℝ))⁻¹ •
        (((codeWalk ω (k.val * m + m) - codeWalk ω (k.val * m)).1 : ℝ),
         ((codeWalk ω (k.val * m + m) - codeWalk ω (k.val * m)).2 : ℝ)) ∈
          Metric.ball (z k) ((1 / 20 : ℝ) / Real.sqrt 3276800) ∧
      ∀ j ≤ m,
        |((codeWalk ω (k.val * m + j) - codeWalk ω (k.val * m)).1 : ℝ)| <
          Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40 ∧
        |((codeWalk ω (k.val * m + j) - codeWalk ω (k.val * m)).2 : ℝ)| <
          Real.sqrt 3276800 * Real.sqrt (m : ℝ) / 40 := by
    constructor
    · intro h
      exact ⟨h.1, fun j hj => h.2 ⟨j, by omega⟩⟩
    · intro h
      exact ⟨h.1, fun j => h.2 j.val (by omega)⟩
  have hprod := iidCodeWalk_block_paths_real_product K m hmpos S
  have hlow (k : Fin K) :
      c ≤ iidCodeMeasure.real {ω | (fun j : Fin (m + 1) =>
        codeWalk ω (k.val * m + j.val) - codeWalk ω (k.val * m)) ∈ S k} := by
    simp_rw [hS]
    exact hmass m ((le_max_right _ _).trans hm) (k.val * m) (z k) (hz k)
  have hbound : c ^ K ≤ iidCodeMeasure.real {ω | ∀ k : Fin K,
      (fun j : Fin (m + 1) => codeWalk ω (k.val * m + j.val) -
        codeWalk ω (k.val * m)) ∈ S k} := by
    rw [hprod]
    calc
      c ^ K = ∏ _k : Fin K, c := by simp only [Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc) (fun k _ => hlow k)
  simpa only [hS] using hbound

/-- Endpoint errors accumulate linearly, and the two within-block errors
fit in the remaining tube budget. This deterministic coordinate estimate is -/
theorem tube_coord_of_block_bounds (K m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (R : ℝ) (hR : 0 ≤ R) (x f : ℕ → ℝ) (hzero : x 0 = f 0)
    (hend : ∀ k < K,
      |(x ((k + 1) * m) - x (k * m)) -
        (f ((k + 1) * m) - f (k * m))| ≤ R / (20 * K))
    (hmax : ∀ k < K, ∀ j ≤ m, |x (k * m + j) - x (k * m)| ≤ R / 40)
    (hprofile : ∀ k < K, ∀ j ≤ m, |f (k * m + j) - f (k * m)| ≤ R / 120) :
    ∀ n ≤ K * m, |x n - f n| ≤ R / 12 := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have he (k : ℕ) (hk : k ≤ K) :
      |x (k * m) - f (k * m)| ≤ (k : ℝ) * (R / (20 * K)) := by
    induction k with
    | zero => simp only [hzero, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
    | succ k ih =>
      have hk' : k < K := by omega
      calc
        |x ((k + 1) * m) - f ((k + 1) * m)| =
            |(x (k * m) - f (k * m)) +
              ((x ((k + 1) * m) - x (k * m)) -
                (f ((k + 1) * m) - f (k * m)))| := by congr 1; ring
        _ ≤ |x (k * m) - f (k * m)| +
              |(x ((k + 1) * m) - x (k * m)) -
                (f ((k + 1) * m) - f (k * m))| := abs_add_le _ _
        _ ≤ (k : ℝ) * (R / (20 * K)) + R / (20 * K) :=
          add_le_add (ih hk'.le) (hend k hk')
        _ = ((k + 1 : ℕ) : ℝ) * (R / (20 * K)) := by push_cast; ring
  have he' (k : ℕ) (hk : k ≤ K) : |x (k * m) - f (k * m)| ≤ R / 20 := by
    calc
      _ ≤ (k : ℝ) * (R / (20 * K)) := he k hk
      _ ≤ (K : ℝ) * (R / (20 * K)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
      _ = R / 20 := by field_simp
  intro n hn
  by_cases hlast : n = K * m
  · rw [hlast]
    exact (he' K le_rfl).trans (by linarith only [hR])
  have hk : n / m < K := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm m K] using
    (lt_of_le_of_ne hn hlast))
  have hj : n % m ≤ m := (Nat.mod_lt n hm).le
  have hn' : n / m * m + n % m = n := by
    simpa only [Nat.mul_comm m (n / m)] using Nat.div_add_mod n m
  calc
    |x n - f n| =
        |(x (n / m * m) - f (n / m * m)) +
          ((x n - x (n / m * m)) - (f n - f (n / m * m)))| := by congr 1; ring
    _ ≤ |x (n / m * m) - f (n / m * m)| +
        |(x n - x (n / m * m)) - (f n - f (n / m * m))| := abs_add_le _ _
    _ ≤ |x (n / m * m) - f (n / m * m)| +
        (|x n - x (n / m * m)| + |f n - f (n / m * m)|) :=
      add_le_add_right (abs_sub _ _) _
    _ ≤ R / 20 + (R / 40 + R / 120) :=
      add_le_add (he' (n / m) hk.le)
        (add_le_add (by simpa only [hn'] using hmax (n / m) hk (n % m) hj)
          (by simpa only [hn'] using hprofile (n / m) hk (n % m) hj))
    _ = R / 12 := by ring

/-- Deterministic assembly including fewer than `K` leftover steps. The
Lipschitz estimate also handles a block straddling the profile corner when
`N / K` leaves a remainder (`lem-walk-bdy-sum`, -/
theorem tube_coord_of_block_bounds_with_remainder
    (K m N : ℕ) (hK : 720 ≤ K) (hm : 0 < m) (hNm : K * m ≤ N)
    (hrem : N - K * m < K) (R : ℝ) (hR : 0 < R) (hRsq : R ^ 2 = N)
    (hlarge : 120 * (K : ℝ) ≤ R) (x f : ℕ → ℝ) (hzero : x 0 = f 0)
    (hend : ∀ k < K,
      |(x ((k + 1) * m) - x (k * m)) -
        (f ((k + 1) * m) - f (k * m))| ≤ R / (20 * K))
    (hmax : ∀ k < K, ∀ j ≤ m, |x (k * m + j) - x (k * m)| ≤ R / 40)
    (hstep : ∀ s j, |x (s + j) - x s| ≤ j)
    (hprofile : ∀ u ≤ N, ∀ v ≤ N,
      |f u - f v| ≤ 6 * |(u : ℝ) - (v : ℝ)| / R) :
    ∀ n ≤ N, |x n - f n| ≤ R / 10 := by
  have hKpos : 0 < K := by omega
  have hNreal : (K : ℝ) * m ≤ R ^ 2 := by
    rw [hRsq]
    exact_mod_cast hNm
  have hKreal : (720 : ℝ) ≤ K := by exact_mod_cast hK
  have hcore : ∀ n ≤ K * m, |x n - f n| ≤ R / 12 := by
    apply tube_coord_of_block_bounds K m hKpos hm R hR.le x f hzero hend hmax
    intro k hk j hj
    have hkm : k * m ≤ K * m := Nat.mul_le_mul_right m hk.le
    have hkj : k * m + j ≤ K * m := by
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hk)
      rw [Nat.succ_mul] at h
      omega
    have hdiff : |((k * m + j : ℕ) : ℝ) - ((k * m : ℕ) : ℝ)| = j := by
      rw [Nat.cast_add, add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg j)]
    calc
      _ ≤ 6 * |((k * m + j : ℕ) : ℝ) - ((k * m : ℕ) : ℝ)| / R :=
        hprofile _ (hkj.trans hNm) _ (hkm.trans hNm)
      _ = 6 * (j : ℝ) / R := by rw [hdiff]
      _ ≤ 6 * (m : ℝ) / R := by gcongr
      _ ≤ R / 120 := by
        apply (div_le_iff₀ hR).mpr
        have hmult : (720 : ℝ) * m ≤ (K : ℝ) * m :=
          mul_le_mul_of_nonneg_right hKreal (Nat.cast_nonneg m)
        nlinarith only [hmult, hNreal]
  have hR6 : (6 : ℝ) ≤ R := by linarith only [hlarge, hKreal]
  have hbudget : (K : ℝ) + 6 * K / R ≤ R / 60 := by
    have hfirst : (K : ℝ) ≤ R / 120 := by linarith only [hlarge]
    have hsecond : 6 * (K : ℝ) / R ≤ R / 120 := by
      apply (div_le_iff₀ hR).mpr
      have hsq6 : 6 * R ≤ R ^ 2 := by
        nlinarith only [mul_nonneg hR.le (sub_nonneg.mpr hR6)]
      nlinarith only [hlarge, hsq6]
    linarith only [hfirst, hsecond]
  intro n hn
  by_cases hnm : n ≤ K * m
  · exact (hcore n hnm).trans (by linarith only [hR])
  have hmn : K * m ≤ n := (lt_of_not_ge hnm).le
  have hj : n - K * m ≤ K := (Nat.sub_le_sub_right hn _).trans hrem.le
  have hstep' : |x n - x (K * m)| ≤ K := by
    have h := hstep (K * m) (n - K * m)
    rw [Nat.add_sub_of_le hmn] at h
    exact h.trans (by exact_mod_cast hj)
  have hdiff : |(n : ℝ) - ((K * m : ℕ) : ℝ)| ≤ K := by
    rw [← Nat.cast_sub hmn, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hj
  have hprofile' : |f n - f (K * m)| ≤ 6 * K / R :=
    (hprofile n hn (K * m) hNm).trans (by gcongr)
  calc
    |x n - f n| = |(x (K * m) - f (K * m)) +
        ((x n - x (K * m)) - (f n - f (K * m)))| := by congr 1; ring
    _ ≤ |x (K * m) - f (K * m)| +
        |(x n - x (K * m)) - (f n - f (K * m))| := abs_add_le _ _
    _ ≤ |x (K * m) - f (K * m)| +
        (|x n - x (K * m)| + |f n - f (K * m)|) :=
      add_le_add_right (abs_sub _ _) _
    _ ≤ R / 12 + ((K : ℝ) + 6 * K / R) :=
      add_le_add (hcore (K * m) le_rfl) (add_le_add hstep' hprofile')
    _ ≤ R / 12 + R / 60 := add_le_add_right hbudget _
    _ = R / 10 := by ring

/-- Full assembly for any deterministic profile with coordinate Lipschitz
constant at most `6 / sqrt N`. The maximal tail is the sole analytic input of
this intermediate estimate for `lem-walk-bdy-sum` -/
theorem iidCodeWalk_lipschitz_tube_mass_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ)))) :
    ∃ m₀ : ℕ, ∀ N : ℕ, m₀ ≤ N / 3276800 →
      120 * (3276800 : ℝ) ≤ Real.sqrt N →
      ∀ f : ℕ → ℝ × ℝ, f 0 = 0 →
      (∀ u ≤ N, ∀ v ≤ N,
        ‖f u - f v‖ ≤ 6 * |(u : ℝ) - (v : ℝ)| / Real.sqrt N) →
      ((Real.exp (-24) / 16) * (1 / 20 : ℝ) ^ 2 / (2 * 3276800) -
        4 * Real.exp (-(3276800 : ℝ) / 3200)) ^ 3276800 ≤
      iidCodeMeasure.real {ω | ∀ n ≤ N,
        |((codeWalk ω n).1 : ℝ) - (f n).1| ≤ Real.sqrt N / 10 ∧
        |((codeWalk ω n).2 : ℝ) - (f n).2| ≤ Real.sqrt N / 10} := by
  let K : ℕ := 3276800
  obtain ⟨m₀, hmass⟩ := iidCodeWalk_explicit_blocks_mass_of_tail htail K
  refine ⟨max 1 m₀, fun N hm₀ hlarge f hfzero hf => ?_⟩
  let m := N / K
  let R := Real.sqrt (N : ℝ)
  let b := Real.sqrt (m : ℝ)
  let a := Real.sqrt (K : ℝ)
  have hKpos : 0 < K := by norm_num [K]
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm₀)
  have hNpos : 0 < N := hmpos.trans_le (Nat.div_le_self N K)
  have hR : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hb : 0 < b := Real.sqrt_pos.mpr (by exact_mod_cast hmpos)
  have ha : 0 < a := by dsimp [a]; positivity
  have hasq : a ^ 2 = K := Real.sq_sqrt (Nat.cast_nonneg K)
  have hbsq : b ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  have hRsq : R ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hNm : K * m ≤ N := by
    simpa only [Nat.mul_comm K m] using Nat.div_mul_le_self N K
  have hrem : N - K * m < K := by
    have hd : K * m + N % K = N := Nat.div_add_mod N K
    have hr := Nat.mod_lt N hKpos
    omega
  have hab : a * b ≤ R := by
    dsimp [a, b, R]
    rw [← Real.sqrt_mul (Nat.cast_nonneg K)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNm)
  have ha6 : 6 ≤ a := by
    dsimp [a, K]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hsmall : 6 * (m : ℝ) / R ≤ b := by
    apply (div_le_iff₀ hR).mpr
    have h6 : 6 * b ≤ R := (mul_le_mul_of_nonneg_right ha6 hb.le).trans hab
    have hmul := mul_le_mul_of_nonneg_left h6 hb.le
    nlinarith only [hmul, hbsq]
  have hwindow : b * ((1 / 20 : ℝ) / a) ≤ R / (20 * K) := by
    have heq : b * ((1 / 20 : ℝ) / a) = (a * b) / (20 * K) := by
      rw [← hasq]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hab (by positivity)
  have hboundaries (k : Fin K) : k.val * m ≤ N ∧ (k.val + 1) * m ≤ N :=
    ⟨(Nat.mul_le_mul_right m k.isLt.le).trans hNm,
      (Nat.mul_le_mul_right m (Nat.succ_le_of_lt k.isLt)).trans hNm⟩
  let z (k : Fin K) : ℝ × ℝ := b⁻¹ • (f ((k.val + 1) * m) - f (k.val * m))
  have hz (k : Fin K) : ‖z k‖ ≤ 1 := by
    have hd : |(((k.val + 1) * m : ℕ) : ℝ) - ((k.val * m : ℕ) : ℝ)| = m := by
      push_cast
      rw [show ((k.val : ℝ) + 1) * m - (k.val : ℝ) * m = m by ring,
        abs_of_nonneg (Nat.cast_nonneg m)]
    have h := hf _ (hboundaries k).2 _ (hboundaries k).1
    rw [hd] at h
    dsimp only [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
    calc
      _ ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left (h.trans hsmall) (inv_nonneg.mpr hb.le)
      _ = 1 := inv_mul_cancel₀ hb.ne'
  have hprob := hmass m ((le_max_right _ _).trans hm₀) z hz
  apply hprob.trans
  refine measureReal_mono ?_
  intro ω hω n hn
  have hend (k : ℕ) (hk : k < K) :
      |(((codeWalk ω ((k + 1) * m)).1 : ℝ) - ((codeWalk ω (k * m)).1 : ℝ)) -
        ((f ((k + 1) * m)).1 - (f (k * m)).1)| ≤ R / (20 * K) ∧
      |(((codeWalk ω ((k + 1) * m)).2 : ℝ) - ((codeWalk ω (k * m)).2 : ℝ)) -
        ((f ((k + 1) * m)).2 - (f (k * m)).2)| ≤ R / (20 * K) := by
    let w : ℝ × ℝ :=
      (((codeWalk ω ((k + 1) * m) - codeWalk ω (k * m)).1 : ℝ),
       ((codeWalk ω ((k + 1) * m) - codeWalk ω (k * m)).2 : ℝ))
    let d := f ((k + 1) * m) - f (k * m)
    have hball : dist (b⁻¹ • w) (b⁻¹ • d) < (1 / 20 : ℝ) / a := by
      simpa [Metric.mem_ball, z, w, d, a, b, K, Nat.add_mul] using (hω ⟨k, hk⟩).1
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hb)] at hball
    have hnorm : ‖w - d‖ ≤ R / (20 * K) := by
      have hh := mul_le_mul_of_nonneg_left hball.le hb.le
      rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at hh
      exact hh.trans hwindow
    have hfst := (norm_fst_le (w - d)).trans hnorm
    have hsnd := (norm_snd_le (w - d)).trans hnorm
    simpa only [w, d, Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Real.norm_eq_abs] using
      And.intro hfst hsnd
  have hmax (k : ℕ) (hk : k < K) (j : ℕ) (hj : j ≤ m) :
      |((codeWalk ω (k * m + j)).1 : ℝ) - ((codeWalk ω (k * m)).1 : ℝ)| ≤ R / 40 ∧
      |((codeWalk ω (k * m + j)).2 : ℝ) - ((codeWalk ω (k * m)).2 : ℝ)| ≤ R / 40 := by
    have h := (hω ⟨k, hk⟩).2 j hj
    have hh : a * b / 40 ≤ R / 40 := div_le_div_of_nonneg_right hab (by norm_num)
    exact ⟨by simpa only [Prod.fst_sub, Int.cast_sub] using h.1.le.trans hh,
      by simpa only [Prod.snd_sub, Int.cast_sub] using h.2.le.trans hh⟩
  have hf1 (u : ℕ) (hu : u ≤ N) (v : ℕ) (hv : v ≤ N) :
      |(f u).1 - (f v).1| ≤ 6 * |(u : ℝ) - v| / R := by
    exact (norm_fst_le (f u - f v)).trans (hf u hu v hv)
  have hf2 (u : ℕ) (hu : u ≤ N) (v : ℕ) (hv : v ≤ N) :
      |(f u).2 - (f v).2| ≤ 6 * |(u : ℝ) - v| / R := by
    exact (norm_snd_le (f u - f v)).trans (hf u hu v hv)
  have hs1 (s j : ℕ) :
      |((codeWalk ω (s + j)).1 : ℝ) - ((codeWalk ω s).1 : ℝ)| ≤ j := by
    have h := (codeWalk_block_sub_coord_abs_le_length ω s j).1
    simp only [Prod.fst_sub] at h
    exact_mod_cast h
  have hs2 (s j : ℕ) :
      |((codeWalk ω (s + j)).2 : ℝ) - ((codeWalk ω s).2 : ℝ)| ≤ j := by
    have h := (codeWalk_block_sub_coord_abs_le_length ω s j).2
    simp only [Prod.snd_sub] at h
    exact_mod_cast h
  exact ⟨tube_coord_of_block_bounds_with_remainder K m N (by norm_num [K]) hmpos hNm hrem
    R hR hRsq hlarge (fun n => ((codeWalk ω n).1 : ℝ)) (fun n => (f n).1)
    (by simp only [codeWalk_zero, hfzero, Prod.fst_zero, Int.cast_zero])
    (fun k hk => (hend k hk).1) (fun k hk j hj => (hmax k hk j hj).1) hs1 hf1 n hn,
    tube_coord_of_block_bounds_with_remainder K m N (by norm_num [K]) hmpos hNm hrem
    R hR hRsq hlarge (fun n => ((codeWalk ω n).2 : ℝ)) (fun n => (f n).2)
    (by simp only [codeWalk_zero, hfzero, Prod.snd_zero, Int.cast_zero])
    (fun k hk => (hend k hk).2) (fun k hk j hj => (hmax k hk j hj).2) hs2 hf2 n hn⟩

/-- The specified two-coordinate profile satisfies the uniform Lipschitz
bound used by the block assembly (`lem-walk-bdy-sum`, -/
theorem tube_profile_norm_sub_le (N : ℕ) (hN : 0 < N) (u v : ℕ) :
    ‖((u : ℝ) / N * Real.sqrt N,
        (-6 * max 0 ((u : ℝ) / N - 1 / 2)) * Real.sqrt N) -
      ((v : ℝ) / N * Real.sqrt N,
        (-6 * max 0 ((v : ℝ) / N - 1 / 2)) * Real.sqrt N)‖ ≤
      6 * |(u : ℝ) - (v : ℝ)| / Real.sqrt N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNreal.le
  have hscale (x : ℝ) : x / N * Real.sqrt N = x / Real.sqrt N := by
    rw [div_mul_eq_mul_div, div_eq_div_iff hNreal.ne' hR.ne', mul_assoc, ← sq, hsq]
  rw [Prod.norm_def, max_le_iff]
  change |(u : ℝ) / N * Real.sqrt N - (v : ℝ) / N * Real.sqrt N| ≤ _ ∧
    |(-6 * max 0 ((u : ℝ) / N - 1 / 2)) * Real.sqrt N -
      (-6 * max 0 ((v : ℝ) / N - 1 / 2)) * Real.sqrt N| ≤ _
  constructor
  · rw [hscale, hscale, ← sub_div, abs_div, abs_of_pos hR]
    have hnonneg : 0 ≤ |(u : ℝ) - v| / Real.sqrt N := by positivity
    rw [mul_div_assoc]
    linarith only [hnonneg]
  · calc
      _ = |(-6 * max 0 ((u : ℝ) / N - 1 / 2)) -
          (-6 * max 0 ((v : ℝ) / N - 1 / 2))| * Real.sqrt N := by
        rw [← sub_mul, abs_mul, abs_of_pos hR]
      _ ≤ (6 * |(u : ℝ) / N - (v : ℝ) / N|) * Real.sqrt N :=
        mul_le_mul_of_nonneg_right (tube_right_profile_abs_sub_le _ _) hR.le
      _ = (6 * |(u : ℝ) - v|) / N * Real.sqrt N := by
        rw [← sub_div, abs_div, abs_of_pos hNreal]
        ring
      _ = _ := hscale _




theorem iidCodeWalk_eventually_tube_mass_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ)))) :
    ∃ q : ℝ, 0 < q ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      q ≤ iidCodeMeasure.real {ω | ∀ n ≤ N,
        |((codeWalk ω n).1 : ℝ) - (n : ℝ) / N * Real.sqrt N| ≤ Real.sqrt N / 10 ∧
        |((codeWalk ω n).2 : ℝ) - (-6 * max 0 ((n : ℝ) / N - 1 / 2)) * Real.sqrt N| ≤
          Real.sqrt N / 10} := by
  obtain ⟨m₀, hmass⟩ := iidCodeWalk_lipschitz_tube_mass_of_tail htail
  refine ⟨((Real.exp (-24) / 16) * (1 / 20 : ℝ) ^ 2 / (2 * 3276800) -
    4 * Real.exp (-(3276800 : ℝ) / 3200)) ^ 3276800,
    pow_pos iidTube_explicit_constants.2.2.2 _,
    max (m₀ * 3276800) ((120 * 3276800) ^ 2), fun N hN => ?_⟩
  have hm : m₀ ≤ N / 3276800 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr ((le_max_left _ _).trans hN)
  have hsquare : (120 * 3276800 : ℕ) ^ 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hsquare
  have hlarge : 120 * (3276800 : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hsquare
  exact hmass N hm hlarge
    (fun n => ((n : ℝ) / N * Real.sqrt N,
      (-6 * max 0 ((n : ℝ) / N - 1 / 2)) * Real.sqrt N))
    (by norm_num)
    (fun u _ v _ => tube_profile_norm_sub_le N hNpos u v)

end DirectedDistances.RandomWalk
