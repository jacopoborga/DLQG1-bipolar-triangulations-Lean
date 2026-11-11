module

public import DirectedDistances.Recursive.SDPExpansionDichotomy

/-! # SDP quadratic derived from the master recursion

Transform identities from `eq:master-eq`, `eq:big-rel2`, `eq:quadratic`, and -/

public section
namespace DirectedDistances.Recursive.SDPExpansion
open Filter Asymptotics
open scoped Topology

/-- The unimodular phase `e^{itk}` used in `integerCF` and `negativeCF` -/
private noncomputable def cfPhase (t : ℝ) (k : ℤ) : ℂ :=
  Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)

private theorem cfPhase_add (t : ℝ) (a b : ℤ) :
    cfPhase t (a + b) = cfPhase t a * cfPhase t b := by
  unfold cfPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem cfPhase_norm (t : ℝ) (k : ℤ) : ‖cfPhase t k‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem cfPhase_zero_left (k : ℤ) : cfPhase 0 k = 1 := by
  simp [cfPhase]

private theorem cfPhase_zero_right (t : ℝ) : cfPhase t 0 = 1 := by
  simp [cfPhase]

private theorem cfPhase_neg (t : ℝ) (k : ℤ) : cfPhase t (-k) = cfPhase (-t) k := by
  unfold cfPhase
  congr 1
  push_cast
  ring

private theorem cfPhase_neg_neg (t : ℝ) (k : ℤ) : cfPhase (-t) (-k) = cfPhase t k := by
  rw [cfPhase_neg, neg_neg]

/-- `HasSum` form of the characteristic series `integerCF` -/
private theorem hasSum_cf {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    HasSum (fun k : ℤ => (p k : ℂ) * cfPhase t k) (integerCF p t) := by
  have h : Summable (fun k : ℤ => (p k : ℂ) * cfPhase t k) := by
    refine Summable.of_norm_bounded hs fun k => ?_
    rw [norm_mul, cfPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hp k)]
  exact h.hasSum

/-- `HasSum` form of the negative-index series `negativeCF`, indexed by `n ↦ -(n+1)` -/
private theorem hasSum_negativeCF {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    HasSum (fun n : ℕ => (p (-((n : ℤ) + 1)) : ℂ) * cfPhase t (-((n : ℤ) + 1)))
      (negativeCF p t) := by
  have hsum := hasSum_cf hp hs t
  set h : ℤ → ℂ := fun k => (p k : ℂ) * cfPhase t k with hh
  have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  have hzero : ∀ k, k ∉ Set.range (fun n : ℕ => -((n : ℤ) + 1)) →
      ({k : ℤ | k ≤ -1}.indicator h) k = 0 := by
    intro k hk
    rw [Set.indicator_apply]
    split_ifs with hk'
    · exfalso
      apply hk
      refine ⟨(-k - 1).toNat, ?_⟩
      have hk'' : k ≤ -1 := hk'
      dsimp only
      omega
    · rfl
  have hind : HasSum ({k : ℤ | k ≤ -1}.indicator h) (negativeCF p t) := by
    have hsub : negativeCF p t = ∑' k : ℤ, {k : ℤ | k ≤ -1}.indicator h k :=
      tsum_subtype ({k : ℤ | k ≤ -1}) h
    rw [hsub]
    exact (hsum.summable.indicator _).hasSum
  have key := (hinj.hasSum_iff hzero).2 hind
  convert key using 1
  funext n
  have hm : (-((n : ℤ) + 1)) ∈ {k : ℤ | k ≤ -1} := by
    show -((n : ℤ) + 1) ≤ -1
    omega
  simp only [Function.comp_apply, Set.indicator_apply, hh]
  simp only [hm, ↓reduceIte]

/-- Symmetric splitting `F = f(0) + F⁻(t) + F⁻(-t)` used for -/
private theorem integerCF_eq_split {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
    (hsymm : ∀ k, p (-k) = p k) (t : ℝ) :
    integerCF p t = (p 0 : ℂ) + negativeCF p t + negativeCF p (-t) := by
  have hc := hasSum_cf hp hs t
  have h1 : Summable (fun n : ℕ => (p n : ℂ) * cfPhase t n) :=
    hc.summable.comp_injective Nat.cast_injective
  have hneg := hasSum_negativeCF hp hs t
  have h2 := hneg.summable
  have e1 : integerCF p t =
      (∑' n : ℕ, (p n : ℂ) * cfPhase t n) +
        ∑' n : ℕ, (p (-((n : ℤ) + 1)) : ℂ) * cfPhase t (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one (f := fun k : ℤ => (p k : ℂ) * cfPhase t k) h1 h2
  have e2 := h1.tsum_eq_zero_add
  have e3 := (hasSum_negativeCF hp hs (-t)).tsum_eq
  have e4 : ∀ n : ℕ, (p (-((n : ℤ) + 1)) : ℂ) * cfPhase (-t) (-((n : ℤ) + 1)) =
      (p ((n + 1 : ℕ) : ℤ) : ℂ) * cfPhase t ((n + 1 : ℕ) : ℤ) := by
    intro n
    rw [cfPhase_neg_neg]
    have : (-((n : ℤ) + 1)) = -(((n + 1 : ℕ)) : ℤ) := by push_cast; ring
    rw [this, hsymm]
    push_cast
    ring_nf
  simp only [e4] at e3
  rw [e1, e2, e3, hneg.tsum_eq]
  simp [cfPhase_zero_right]
  ring

/-- `F(0) = 1`. -/
private theorem integerCF_zero {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hps : HasSum p 1) :
    integerCF p 0 = 1 := by
  have h1 := hasSum_cf hp hps.summable 0
  have h2 : HasSum (fun k : ℤ => (p k : ℂ)) 1 := by
    have := Complex.hasSum_ofReal.2 hps
    simpa using this
  simp only [cfPhase_zero_left, mul_one] at h1
  exact h1.unique h2

/-- `F⁻(0) = (1 - f(0))/2`, used in `eq:first-sub`, -/
private theorem negativeCF_zero {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hps : HasSum p 1)
    (hsymm : ∀ k, p (-k) = p k) :
    negativeCF p 0 = (((1 - p 0) / 2 : ℝ) : ℂ) := by
  have h := integerCF_eq_split hp hps.summable hsymm 0
  rw [integerCF_zero hp hps, neg_zero] at h
  push_cast
  linear_combination (-1 / 2 : ℂ) * h

private theorem cfPhase_re (t : ℝ) (k : ℤ) : (cfPhase t k).re = Real.cos (t * (k : ℝ)) := by
  unfold cfPhase
  exact Complex.exp_ofReal_mul_I_re _


private theorem cfPhase_one (t : ℝ) : cfPhase t 1 = Complex.exp ((t : ℂ) * Complex.I) := by
  simp [cfPhase]

private theorem sdpOffset_phase (f g : ℤ → ℝ) (t : ℝ) :
    sdpOffset f g t = (g (-1) : ℂ) ^ 2 * cfPhase t (-2) +
      (((-3 - 2 * (g (-1)) ^ 2 + f 0) / 2 : ℝ) : ℂ) * cfPhase t (-1) := by
  have h2 : Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) = cfPhase t 2 := by
    unfold cfPhase
    congr 1
    push_cast
    ring
  have hm2 : cfPhase t (-2) * cfPhase t 2 = 1 := by
    rw [← cfPhase_add]; norm_num [cfPhase_zero_right]
  have hm1 : cfPhase t (-1) * cfPhase t 2 = cfPhase t 1 := by
    rw [← cfPhase_add]; norm_num
  unfold sdpOffset
  rw [h2, ← cfPhase_one]
  have hne : cfPhase t 2 ≠ 0 := Complex.exp_ne_zero _
  apply (div_eq_iff (mul_ne_zero (by norm_num) hne)).2
  symm
  rw [add_mul]
  push_cast
  calc
    _ = 2 * (g (-1) : ℂ) ^ 2 * (cfPhase t (-2) * cfPhase t 2) +
      ((-3 - 2 * (g (-1) : ℂ) ^ 2 + (f 0 : ℂ))) *
        (cfPhase t (-1) * cfPhase t 2) := by ring
    _ = _ := by rw [hm2, hm1]; ring

/-- Symmetry gives `eq:real-part-fhat2`, -/
theorem sdp_real_part_of_symm {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x) (t : ℝ) :
    (sdpHat f g t).re = ((integerCF f t).re - sdpK f g t) / 2 := by
  have hsplit := integerCF_eq_split hf hfs.summable hsymm t
  have hre : (negativeCF f (-t)).re = (negativeCF f t).re := by
    have h1 := Complex.hasSum_re (hasSum_negativeCF hf hfs.summable t)
    have h2 := Complex.hasSum_re (hasSum_negativeCF hf hfs.summable (-t))
    refine h2.unique ?_
    convert h1 using 1
    funext n
    simp only [Complex.re_ofReal_mul, cfPhase_re]
    congr 1
    push_cast
    rw [show -t * -((n : ℝ) + 1) = t * ((n : ℝ) + 1) by ring,
      show t * -((n : ℝ) + 1) = -(t * ((n : ℝ) + 1)) by ring, Real.cos_neg]
  have hF : (integerCF f t).re = f 0 + (negativeCF f t).re + (negativeCF f (-t)).re := by
    rw [hsplit]
    simp
  unfold sdpHat
  rw [Complex.add_re, sdpOffset_phase, Complex.add_re]
  simp only [← Complex.ofReal_pow, Complex.re_ofReal_mul, cfPhase_re, Int.cast_neg, Int.cast_ofNat,
    mul_neg, Real.cos_neg]
  rw [hF, hre]
  unfold sdpK
  rw [mul_comm t (2 : ℝ)]
  ring

private theorem hasSum_negative_indicator {p : ℤ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    HasSum (fun k : ℤ => if k ≤ -1 then (p k : ℂ) * cfPhase t k else 0)
      (negativeCF p t) := by
  have hc := hasSum_cf hp hs t
  have ht : negativeCF p t = ∑' k : ℤ,
      {k : ℤ | k ≤ -1}.indicator (fun k => (p k : ℂ) * cfPhase t k) k :=
    by
      change (∑' k : {k : ℤ // k ≤ -1}, (p k : ℂ) * cfPhase t k) = _
      exact tsum_subtype {k : ℤ | k ≤ -1} (fun k : ℤ => (p k : ℂ) * cfPhase t k)
  rw [ht]
  convert (hc.summable.indicator {k : ℤ | k ≤ -1}).hasSum using 1
  funext k
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

private theorem norm_summable_cf {p : ℤ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    Summable (fun k : ℤ => ‖(p k : ℂ) * cfPhase t k‖) := by
  convert hs using 1
  funext k
  rw [norm_mul, cfPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hp k)]

private theorem hasSum_phase_conv {a b : ℤ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (has : Summable a) (hbs : Summable b) (t : ℝ) (d : ℤ) :
    HasSum (fun y : ℤ => cfPhase t y *
      ((∑' j : ℤ, a j * b (y - j - d) : ℝ) : ℂ))
      (cfPhase t d * integerCF a t * integerCF b t) := by
  let u : ℤ → ℂ := fun k => (a k : ℂ) * cfPhase t k
  let v : ℤ → ℂ := fun k => (b k : ℂ) * cfPhase t k
  have hu := norm_summable_cf ha has t
  have hv := norm_summable_cf hb hbs t
  have hp : HasSum (fun q : ℤ × ℤ => u q.1 * v q.2)
      (integerCF a t * integerCF b t) := by
    have hsm := summable_mul_of_summable_norm hu hv
    have heq := tsum_mul_tsum_of_summable_norm hu hv
    exact heq ▸ hsm.hasSum
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    ⟨fun q => (q.2, q.1 - q.2 - d), fun q => (q.1 + q.2 + d, q.1),
      fun q => by dsimp; ext <;> ring,
      fun q => by dsimp; ext <;> ring⟩
  have hp' := (e.hasSum_iff.2 hp).mul_left (cfPhase t d)
  have hsum := hp'.prod_fiberwise (fun y => (hp'.summable.prod_factor y).hasSum)
  have hvv : cfPhase t d * (integerCF a t * integerCF b t) =
      cfPhase t d * integerCF a t * integerCF b t := (mul_assoc _ _ _).symm
  rw [hvv] at hsum
  convert hsum using 1
  funext y
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro j
  change cfPhase t y * ((a j * b (y - j - d) : ℝ) : ℂ) =
    cfPhase t d * (u j * v (y - j - d))
  have he : cfPhase t y = cfPhase t d * cfPhase t j * cfPhase t (y - j - d) := by
    rw [← cfPhase_add, ← cfPhase_add]
    congr 1
    ring
  rw [he]
  dsimp [u, v]
  push_cast
  ring

private theorem hasSum_phase_shift {p : ℤ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) (d : ℤ) :
    HasSum (fun x : ℤ => cfPhase t x * (p (x - d) : ℂ))
      (cfPhase t d * integerCF p t) := by
  have h := (Equiv.addRight (-d)).hasSum_iff.2 (hasSum_cf hp hs t)
  convert h.mul_left (cfPhase t d) using 1
  funext x
  simp only [Function.comp_apply, Equiv.coe_addRight]
  have he : cfPhase t x = cfPhase t d * cfPhase t (x - d) := by
    rw [← cfPhase_add]
    congr 1
    ring
  rw [he]
  simp only [sub_eq_add_neg]
  ring

private theorem hasSum_tail_pairs {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hfs : HasSum f 1) (t : ℝ) :
    HasSum (fun x : ℤ => cfPhase t x *
      ((∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1) : ℝ) : ℂ))
      (integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ))) := by
  let a : ℤ → ℝ := {j : ℤ | j ≤ -2}.indicator f
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    dsimp [a, Set.indicator]
    split_ifs
    · exact hf j
    · exact le_rfl
  have has : Summable a := hfs.summable.indicator _
  have hA : integerCF a t = negativeCF f t - (f (-1) : ℂ) * cfPhase t (-1) := by
    have hn := hasSum_negative_indicator hf hfs.summable t
    have hi := hasSum_ite_eq (-1 : ℤ) ((f (-1) : ℂ) * cfPhase t (-1))
    have hh := hn.sub hi
    have he : (fun j : ℤ =>
        (if j ≤ -1 then (f j : ℂ) * cfPhase t j else 0) -
        (if j = -1 then (f (-1) : ℂ) * cfPhase t (-1) else 0)) =
        (fun j => (a j : ℂ) * cfPhase t j) := by
      funext j
      by_cases hj : j ≤ -2
      · have hj' : j ≤ -1 := by omega
        have hjn : j ≠ -1 := by omega
        simp [a, hj, hj', hjn]
      · by_cases hj1 : j = -1
        · subst j; simp [a]
        · have hj' : ¬ j ≤ -1 := by omega
          simp [a, hj, hj', hj1]
    rw [he] at hh
    exact (hasSum_cf ha has t).unique hh
  have hc := hasSum_phase_conv ha hf has hfs.summable t 1
  have hphase : cfPhase t 1 * cfPhase t (-1) = 1 := by
    rw [← cfPhase_add]; norm_num [cfPhase_zero_right]
  have hval : cfPhase t 1 * integerCF a t * integerCF f t =
      integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ)) := by
    rw [hA]
    linear_combination -(integerCF f t) * (f (-1) : ℂ) * hphase
  rw [hval] at hc
  convert hc using 1
  funext x
  congr 2
  refine (tsum_subtype {j : ℤ | j ≤ -2} (fun j : ℤ => f j * f (x - j - 1))).trans ?_
  apply tsum_congr
  intro j
  by_cases hj : j ≤ -2 <;> simp [a, Set.indicator, hj]

private theorem hasSum_upper_f {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hfs : HasSum f 1) (t : ℝ) :
    HasSum (fun y : ℤ => if -1 ≤ y then (f y : ℂ) * cfPhase t y else 0)
      (integerCF f t - negativeCF f t + (f (-1) : ℂ) * cfPhase t (-1)) := by
  have hh := ((hasSum_cf hf hfs.summable t).sub
    (hasSum_negative_indicator hf hfs.summable t)).add
    (hasSum_ite_eq (-1 : ℤ) ((f (-1) : ℂ) * cfPhase t (-1)))
  convert hh using 1
  funext y
  by_cases hy : y = -1
  · subst y; simp
  · by_cases hy' : -1 ≤ y
    · have hy'' : ¬ y ≤ -1 := by omega
      simp [hy, hy', hy'']
    · have hy'' : y ≤ -1 := by omega
      simp [hy, hy', hy'']

private theorem hasSum_upper_g {g : ℤ → ℝ}
    (hg : ∀ k, 0 ≤ g k) (hgs : HasSum g 1)
    (hgsupp : ∀ y, y < -1 → g y = 0) (t : ℝ) :
    HasSum (fun y : ℤ => if -1 ≤ y then (g y : ℂ) * cfPhase t y else 0)
      (integerCF g t) := by
  convert hasSum_cf hg hgs.summable t using 1
  funext y
  by_cases hy : -1 ≤ y
  · simp [hy]
  · simp [hy, hgsupp y (by omega)]

private theorem hasSum_upper_conv {g : ℤ → ℝ}
    (hg : ∀ k, 0 ≤ g k) (hgs : HasSum g 1)
    (hgsupp : ∀ y, y < -1 → g y = 0) (t : ℝ) :
    HasSum (fun y : ℤ => if -1 ≤ y then cfPhase t y *
      ((∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ) else 0)
      ((integerCF g t) ^ 2 - (g (-1) : ℂ) ^ 2 * cfPhase t (-2)) := by
  have hc := hasSum_phase_conv hg hg hgs.summable hgs.summable t 0
  simp only [cfPhase_zero_right, one_mul, sub_zero] at hc
  have hc' : HasSum (fun y : ℤ => cfPhase t y *
      ((∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ))
      ((integerCF g t) ^ 2) := by
    convert hc using 1
    · funext y
      congr 2
      symm
      apply tsum_eq_sum
      intro j hj
      simp only [Finset.mem_Icc, not_and_or, not_le] at hj
      rcases hj with hj | hj
      · rw [hgsupp j hj, zero_mul]
      · rw [hgsupp (y - j) (by omega), mul_zero]
    · ring
  have hh := hc'.sub
    (hasSum_ite_eq (-2 : ℤ) ((g (-1) : ℂ) ^ 2 * cfPhase t (-2)))
  convert hh using 1
  funext y
  by_cases hy : -1 ≤ y
  · have hyn : y ≠ -2 := by omega
    simp [hy, hyn]
  · by_cases hy2 : y = -2
    · subst y
      norm_num
      ring
    · have hempty : Finset.Icc (-1 : ℤ) (y + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      simp [hy, hy2, hempty]

private theorem sdp_fiber_identity {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f 1)
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g 1)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (t : ℝ) (y : ℤ) (hy : -1 ≤ y) :
    3 * integerCF f t * (g y : ℂ) =
      integerCF f t * ((f y : ℂ) +
        ((∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ)) +
      (if y = -1 then
        integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ)) +
        (g (-1) : ℂ) ^ 2 * cfPhase t (-1) * integerCF f t +
        cfPhase t 1 * integerCF g t else 0) := by
  let V : ℂ := integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ)) +
        (g (-1) : ℂ) ^ 2 * cfPhase t (-1) * integerCF f t +
        cfPhase t 1 * integerCF g t
  have htail := hasSum_tail_pairs hf hfs t
  have hshift := (hasSum_phase_shift hf hfs.summable t (-1)).mul_left ((g (-1) : ℂ) ^ 2)
  have hgshift := hasSum_phase_shift hg hgs.summable t 1
  have hV : HasSum (fun x : ℤ => cfPhase t x *
      (((∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
        (g (-1)) ^ 2 * f (x + 1) + g (x - 1) : ℝ) : ℂ)) V := by
    convert (htail.add hshift).add hgshift using 1
    · funext x
      simp only [sub_neg_eq_add]
      push_cast
      ring
    · dsimp [V]; ring
  have hExtra : HasSum (fun x : ℤ => cfPhase t x *
      ((if y = -1 then
        (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
        (g (-1)) ^ 2 * f (x + 1) + g (x - 1) else 0 : ℝ) : ℂ))
      (if y = -1 then V else 0) := by
    by_cases hy1 : y = -1
    · simpa only [hy1, ↓reduceIte] using hV
    · simp [hy1]
  have hF := hasSum_cf hf hfs.summable t
  have hL := hF.mul_left (3 * (g y : ℂ))
  have hR := (hF.mul_right
    (((f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ))).add hExtra
  have he : (fun x : ℤ => 3 * (g y : ℂ) * ((f x : ℂ) * cfPhase t x)) =
      (fun x : ℤ => (f x : ℂ) * cfPhase t x *
        ((f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ) +
      cfPhase t x * ((if y = -1 then
        (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
        (g (-1)) ^ 2 * f (x + 1) + g (x - 1) else 0 : ℝ) : ℂ)) := by
    funext x
    have hr := congrArg (fun r : ℝ => (r : ℂ)) (hrec x y hy)
    push_cast at hr ⊢
    linear_combination cfPhase t x * hr
  rw [he] at hL
  have hh := hL.unique hR
  dsimp [V] at hh
  push_cast at hh ⊢
  linear_combination hh

private theorem sdp_big_rel_of_master {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f 1)
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g 1)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (s t : ℝ) :
    3 * integerCF f t * integerCF g s =
      integerCF f t * (integerCF f s - negativeCF f s +
        (f (-1) : ℂ) * cfPhase s (-1) + integerCF g s ^ 2 -
          (g (-1) : ℂ) ^ 2 * cfPhase s (-2)) +
      cfPhase s (-1) *
        (integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ)) +
          (g (-1) : ℂ) ^ 2 * cfPhase t (-1) * integerCF f t +
          cfPhase t 1 * integerCF g t) := by
  let V : ℂ := integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ)) +
          (g (-1) : ℂ) ^ 2 * cfPhase t (-1) * integerCF f t +
          cfPhase t 1 * integerCF g t
  have hL := (hasSum_upper_g hg hgs hgsupp s).mul_left (3 * integerCF f t)
  have hR := (((hasSum_upper_f hf hfs s).add
    (hasSum_upper_conv hg hgs hgsupp s)).mul_left (integerCF f t)).add
      (hasSum_ite_eq (-1 : ℤ) (cfPhase s (-1) * V))
  have he : (fun y : ℤ => 3 * integerCF f t *
      (if -1 ≤ y then (g y : ℂ) * cfPhase s y else 0)) =
      (fun y : ℤ => integerCF f t *
        ((if -1 ≤ y then (f y : ℂ) * cfPhase s y else 0) +
          (if -1 ≤ y then cfPhase s y *
            ((∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ) else 0)) +
        if y = -1 then cfPhase s (-1) * V else 0) := by
    funext y
    by_cases hy : -1 ≤ y
    · have hh := sdp_fiber_identity hf hfs hg hgs hrec t y hy
      by_cases hy1 : y = -1
      · subst y
        simp only [le_refl, ↓reduceIte] at hh ⊢
        dsimp [V]
        norm_num only at hh
        linear_combination cfPhase s (-1) * hh
      · simp only [hy, hy1, ↓reduceIte, add_zero] at hh ⊢
        linear_combination cfPhase s y * hh
    · have hy1 : y ≠ -1 := by omega
      simp [hy, hy1]
  rw [he] at hL
  have hh := hL.unique hR
  dsimp [V] at hh
  linear_combination hh

/-- from the master recursion `eq:master-eq` at lines 631–638 alone. -/
theorem sdp_quadratic_of_master {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (t : ℝ) :
    (integerCF f t) ^ 2 * (sdpHat f g t) ^ 2 +
      (3 * integerCF f t - 1) * sdpHat f g t + integerCF f t = 0 := by
  have hi := sdp_big_rel_of_master hf hfs hg hgs hgsupp hrec 0 t
  have hj := sdp_big_rel_of_master hf hfs hg hgs hgsupp hrec t 0
  rw [integerCF_zero hg hgs, integerCF_zero hf hfs,
    negativeCF_zero hf hfs hsymm] at hi
  rw [integerCF_zero hf hfs, integerCF_zero hg hgs,
    negativeCF_zero hf hfs hsymm] at hj
  simp only [cfPhase_zero_left, one_mul, mul_one, one_pow] at hi hj
  push_cast at hi hj
  have hp1 : cfPhase t (-1) * cfPhase t 1 = 1 := by
    rw [← cfPhase_add]; norm_num [cfPhase_zero_right]
  have hp2 : cfPhase t (-1) * cfPhase t (-1) = cfPhase t (-2) := by
    rw [← cfPhase_add]; norm_num
  have hG : integerCF g t = -integerCF f t * sdpHat f g t := by
    unfold sdpHat
    rw [sdpOffset_phase]
    push_cast
    linear_combination -cfPhase t (-1) * hi -
      (integerCF f t * negativeCF f t + integerCF g t) * hp1 -
      (g (-1) : ℂ) ^ 2 * integerCF f t * hp2
  have hhat : -negativeCF f t - (g (-1) : ℂ) ^ 2 * cfPhase t (-2) +
      cfPhase t (-1) * (((3 - f 0) / 2 + (g (-1)) ^ 2 : ℝ) : ℂ) =
      -sdpHat f g t := by
    unfold sdpHat
    rw [sdpOffset_phase]
    push_cast
    ring
  push_cast at hhat
  have hj' : 3 * integerCF g t = integerCF f t + integerCF g t ^ 2 - sdpHat f g t := by
    linear_combination hj + hhat
  rw [hG] at hj'
  linear_combination -hj'

/-- The real SDP transform dichotomy from the seven master-recursion
premises, with no intermediate transform identities assumed; -/
theorem sdp_real_transform_dichotomy_of_master {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0)) :
    let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
    0 < g (-1) ∧
      ((κ = 0 ∧
        (fun t : ℝ => integerCF f t -
          ((1 : ℂ) - (b : ℂ) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
          =o[𝓝[>] (0 : ℝ)]
            (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) ∨
       (0 < κ ∧
        (fun t : ℝ => integerCF f t -
          ((1 : ℂ) - (a : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
          =o[𝓝[>] (0 : ℝ)]
            (fun t : ℝ => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))) := by
  exact sdp_real_transform_dichotomy hf hfs hg hgs hsymm hgsupp hrec
    (sdp_quadratic_of_master hf hfs hg hgs hsymm hgsupp hrec)
    (sdp_real_part_of_symm hf hfs hsymm)

end DirectedDistances.Recursive.SDPExpansion
