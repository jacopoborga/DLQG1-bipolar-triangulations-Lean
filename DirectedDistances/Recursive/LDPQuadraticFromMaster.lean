/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.LDPExpansionF







public section
namespace DirectedDistances.Recursive

open Filter Asymptotics
open scoped Topology

/-- The unimodular phase `e^{itk}` used in `integerCF` and `negativeCF` -/
@[expose] noncomputable def cfPhase (t : ℝ) (k : ℤ) : ℂ :=
  Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)

theorem cfPhase_add (t : ℝ) (a b : ℤ) :
    cfPhase t (a + b) = cfPhase t a * cfPhase t b := by
  unfold cfPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem cfPhase_norm (t : ℝ) (k : ℤ) : ‖cfPhase t k‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem cfPhase_zero_left (k : ℤ) : cfPhase 0 k = 1 := by
  simp [cfPhase]

theorem cfPhase_zero_right (t : ℝ) : cfPhase t 0 = 1 := by
  simp [cfPhase]

theorem cfPhase_neg (t : ℝ) (k : ℤ) : cfPhase t (-k) = cfPhase (-t) k := by
  unfold cfPhase
  congr 1
  push_cast
  ring

theorem cfPhase_neg_neg (t : ℝ) (k : ℤ) : cfPhase (-t) (-k) = cfPhase t k := by
  rw [cfPhase_neg, neg_neg]

theorem cfPhase_neg_one_mul (t : ℝ) :
    cfPhase t (-1) * Complex.exp ((t : ℂ) * Complex.I) = 1 := by
  unfold cfPhase
  rw [← Complex.exp_add]
  have : ((((t * (((-1 : ℤ)) : ℝ) : ℝ) : ℂ) * Complex.I) + (t : ℂ) * Complex.I) = 0 := by
    push_cast
    ring
  rw [this, Complex.exp_zero]

/-- `HasSum` form of the characteristic series `integerCF` -/
theorem hasSum_cf {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    HasSum (fun k : ℤ => (p k : ℂ) * cfPhase t k) (integerCF p t) := by
  have h : Summable (fun k : ℤ => (p k : ℂ) * cfPhase t k) := by
    refine Summable.of_norm_bounded hs fun k => ?_
    rw [norm_mul, cfPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hp k)]
  exact h.hasSum

/-- `HasSum` form of the negative-index series `negativeCF`, indexed by `n ↦ -(n+1)` -/
theorem hasSum_negativeCF {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
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

/-- Symmetric splitting `F = f(0) + F⁻(t) + F⁻(-t)`; used for `eq:real-part-fhat` -/
theorem integerCF_eq_split {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
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
theorem integerCF_zero {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hps : HasSum p 1) :
    integerCF p 0 = 1 := by
  have h1 := hasSum_cf hp hps.summable 0
  have h2 : HasSum (fun k : ℤ => (p k : ℂ)) 1 := by
    have := Complex.hasSum_ofReal.2 hps
    simpa using this
  simp only [cfPhase_zero_left, mul_one] at h1
  exact h1.unique h2

 
theorem negativeCF_zero {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hps : HasSum p 1)
    (hsymm : ∀ k, p (-k) = p k) :
    negativeCF p 0 = (((1 - p 0) / 2 : ℝ) : ℂ) := by
  have h := integerCF_eq_split hp hps.summable hsymm 0
  rw [integerCF_zero hp hps, neg_zero] at h
  push_cast
  linear_combination (-1 / 2 : ℂ) * h

theorem cfPhase_re (t : ℝ) (k : ℤ) : (cfPhase t k).re = Real.cos (t * (k : ℝ)) := by
  unfold cfPhase
  exact Complex.exp_ofReal_mul_I_re _

/-- Part (A): the real-part identity `eq:real-part-fhat` -/
theorem ldp_real_part_of_symm {f : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x) (t : ℝ) :
    (ldpHat f t).re = ((integerCF f t).re - ldpK f t) / 2 := by
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
  have hH : (ldpHat f t).re =
      (negativeCF f t).re + (f 0 - (3 + f 0) / 2 * Real.cos t) := by
    unfold ldpHat ldpOffset
    rw [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
      Complex.ofReal_re]
  rw [hH, hF, hre]
  unfold ldpK
  ring

theorem hasSum_neg_half {a : ℂ} {w : ℤ → ℂ} (hw : HasSum w a)
    (hz : ∀ k : ℤ, 0 ≤ k → w k = 0) :
    HasSum (fun n : ℕ => w (-((n : ℤ) + 1))) a := by
  have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro m n hmn
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hmn
    exact hmn
  refine (hinj.hasSum_iff ?_).2 hw
  intro k hk
  apply hz
  by_contra hneg
  apply hk
  refine ⟨(-k - 1).toNat, ?_⟩
  dsimp only
  omega

theorem hasSum_shift_term {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) (j : ℕ) :
    HasSum (fun x : ℤ => cfPhase t x * (((p ((j : ℤ) + x + 1) * p (-(j : ℤ))) : ℝ) : ℂ))
      (integerCF p t * (cfPhase t (-((j : ℤ) + 1)) * (p (-(j : ℤ)) : ℂ))) := by
  have hc := hasSum_cf hp hs t
  have h := (Equiv.addRight ((j : ℤ) + 1)).hasSum_iff.2 hc
  have h' := h.mul_right (cfPhase t (-((j : ℤ) + 1)) * (p (-(j : ℤ)) : ℂ))
  convert h' using 1
  funext x
  simp only [Function.comp_apply, Equiv.coe_addRight]
  have e1 : cfPhase t x = cfPhase t (x + ((j : ℤ) + 1)) * cfPhase t (-((j : ℤ) + 1)) := by
    rw [← cfPhase_add]
    congr 1
    ring
  have e2 : (j : ℤ) + x + 1 = x + ((j : ℤ) + 1) := by ring
  rw [e2, e1]
  push_cast
  ring

theorem summable_shift_family {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hps : HasSum p 1) :
    Summable (fun q : ℕ × ℤ => p ((q.1 : ℤ) + q.2 + 1) * p (-(q.1 : ℤ))) := by
  have hshift : ∀ j : ℕ, HasSum (fun x : ℤ => p ((j : ℤ) + x + 1)) 1 := by
    intro j
    have := (Equiv.addRight ((j : ℤ) + 1)).hasSum_iff.2 hps
    convert this using 1
    funext x
    simp only [Function.comp_apply, Equiv.coe_addRight]
    congr 1
    ring
  have hinj : Function.Injective (fun j : ℕ => -(j : ℤ)) := by
    intro a b hab
    simpa using hab
  have hneg : Summable (fun j : ℕ => p (-(j : ℤ))) :=
    hps.summable.comp_injective (i := fun j : ℕ => -(j : ℤ)) hinj
  have h0 : (0 : ℕ × ℤ → ℝ) ≤ fun q : ℕ × ℤ => p ((q.1 : ℤ) + q.2 + 1) * p (-(q.1 : ℤ)) :=
    fun q => mul_nonneg (hp _) (hp _)
  refine (summable_prod_of_nonneg h0).2 ⟨fun j => ?_, ?_⟩
  · exact ((hshift j).summable).mul_right (p (-(j : ℤ)))
  · have htsum : ∀ j : ℕ, ∑' x : ℤ, p ((j : ℤ) + x + 1) * p (-(j : ℤ)) = p (-(j : ℤ)) := by
      intro j
      rw [((hshift j).mul_right (p (-(j : ℤ)))).tsum_eq, one_mul]
    exact hneg.congr (fun j => (htsum j).symm)

/-- The sum over `x` of `e^{itx} ∑_{j ≥ 0} f(j+x+1) f(-j)`, with the substitution -/
theorem hasSum_forward_pairs {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hps : HasSum p 1) (t : ℝ) :
    HasSum (fun x : ℤ => cfPhase t x *
        ((∑' j : ℕ, p ((j : ℤ) + x + 1) * p (-(j : ℤ)) : ℝ) : ℂ))
      (integerCF p t * cfPhase t (-1) * ((p 0 : ℂ) + negativeCF p t)) := by
  have hs := hps.summable
  let G : ℕ → ℤ → ℂ := fun j x =>
    cfPhase t x * (((p ((j : ℤ) + x + 1) * p (-(j : ℤ))) : ℝ) : ℂ)
  have hG : Summable (Function.uncurry G) := by
    refine Summable.of_norm_bounded (summable_shift_family hp hps) fun q => ?_
    show ‖cfPhase t q.2 * (((p ((q.1 : ℤ) + q.2 + 1) * p (-(q.1 : ℤ))) : ℝ) : ℂ)‖ ≤ _
    rw [norm_mul, cfPhase_norm, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (hp _) (hp _))]
  have hx : Summable (fun x : ℤ => ∑' j : ℕ, G j x) := (hG.prod_symm).prod
  have hterm : ∀ x : ℤ, cfPhase t x *
      ((∑' j : ℕ, p ((j : ℤ) + x + 1) * p (-(j : ℤ)) : ℝ) : ℂ) = ∑' j : ℕ, G j x := by
    intro x
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
  have hφ : HasSum (fun j : ℕ => (p (-(j : ℤ)) : ℂ) * cfPhase t (-(j : ℤ)))
      ((p 0 : ℂ) + negativeCF p t) := by
    have h := hasSum_negativeCF hp hs t
    have h2 : HasSum (fun n : ℕ => (p (-(((n + 1 : ℕ) : ℤ))) : ℂ) *
        cfPhase t (-(((n + 1 : ℕ) : ℤ)))) (negativeCF p t) := by
      convert h using 1
      funext n
      push_cast
      rfl
    have := HasSum.zero_add
      (f := fun j : ℕ => (p (-(j : ℤ)) : ℂ) * cfPhase t (-(j : ℤ))) h2
    simpa [cfPhase_zero_right] using this
  have hJ : HasSum (fun j : ℕ => integerCF p t *
      (cfPhase t (-((j : ℤ) + 1)) * (p (-(j : ℤ)) : ℂ)))
      (integerCF p t * cfPhase t (-1) * ((p 0 : ℂ) + negativeCF p t)) := by
    have := hφ.mul_left (integerCF p t * cfPhase t (-1))
    convert this using 1
    funext j
    have : cfPhase t (-((j : ℤ) + 1)) = cfPhase t (-1) * cfPhase t (-(j : ℤ)) := by
      rw [← cfPhase_add]
      congr 1
      ring
    rw [this]
    ring
  have hcomm : ∑' x : ℤ, ∑' j : ℕ, G j x = ∑' j : ℕ, ∑' x : ℤ, G j x := hG.tsum_comm
  have hval : ∑' j : ℕ, ∑' x : ℤ, G j x =
      integerCF p t * cfPhase t (-1) * ((p 0 : ℂ) + negativeCF p t) := by
    rw [← hJ.tsum_eq]
    exact tsum_congr fun j => (hasSum_shift_term hp hs t j).tsum_eq
  have := hx.hasSum
  rw [hcomm, hval] at this
  convert this using 1
  funext x
  exact hterm x

theorem hasSum_backward_term {g : ℤ → ℝ} (hg : ∀ k, 0 ≤ g k) (hgs : Summable g) (t : ℝ) :
    HasSum (fun x : ℤ => cfPhase t x * (g (-x - 1) : ℂ))
      (cfPhase t (-1) * integerCF g (-t)) := by
  have hc := hasSum_cf hg hgs (-t)
  let e : ℤ ≃ ℤ := ⟨fun x => -x - 1, fun y => -y - 1, fun x => by simp, fun y => by simp⟩
  have h := e.hasSum_iff.2 hc
  have h' := h.mul_left (cfPhase t (-1))
  convert h' using 1
  funext x
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk]
  have e1 : cfPhase (-t) (-x - 1) = cfPhase t (x + 1) := by
    rw [show -x - 1 = -(x + 1) by ring, cfPhase_neg_neg]
  have e2 : cfPhase t x = cfPhase t (-1) * cfPhase t (x + 1) := by
    rw [← cfPhase_add]
    congr 1
    ring
  rw [e1, e2]
  ring

theorem cfPhase_neg_t_neg_one (t : ℝ) :
    cfPhase (-t) (-1) = Complex.exp ((t : ℂ) * Complex.I) := by
  unfold cfPhase
  congr 1
  push_cast
  ring

theorem convSum_eq {g : ℤ → ℝ} (y : ℤ) :
    ∑ b ∈ Finset.Icc (y + 1) (-1), g (y - b) * g b =
      ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) := by
  refine Finset.sum_nbij' (fun b => -b) (fun j => -j) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_Icc] at hb ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro b _
    simp
  · intro j _
    simp
  · intro b _
    simp [sub_eq_add_neg]



theorem hasSum_conv {g : ℤ → ℝ} (hg : ∀ k, 0 ≤ g k) (hgs : HasSum g 1)
    (hgsupp : ∀ y, 0 ≤ y → g y = 0) (s : ℝ) :
    HasSum (fun n : ℕ => cfPhase (-s) (-((n : ℤ) + 1)) *
        ((∑ j ∈ Finset.Icc (1 : ℤ) (-(-((n : ℤ) + 1)) - 1),
          g (-((n : ℤ) + 1) + j) * g (-j) : ℝ) : ℂ))
      (integerCF g (-s) ^ 2) := by
  let u : ℤ → ℂ := fun k => (g k : ℂ) * cfPhase (-s) k
  have hn : ∀ k, ‖u k‖ = g k := by
    intro k
    simp only [u]
    rw [norm_mul, cfPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hg k)]
  have hnorm : Summable (fun k => ‖u k‖) := hgs.summable.congr (fun k => (hn k).symm)
  have hI : (∑' k, u k) = integerCF g (-s) := rfl
  have hprod : HasSum (fun q : ℤ × ℤ => u q.1 * u q.2) (integerCF g (-s) ^ 2) := by
    have hsm := summable_mul_of_summable_norm hnorm hnorm
    have h := tsum_mul_tsum_of_summable_norm hnorm hnorm
    rw [hI] at h
    have := hsm.hasSum
    rw [← h, ← sq] at this
    exact this
  let ψ : ℤ × ℤ ≃ ℤ × ℤ :=
    ⟨fun q => (q.1 - q.2, q.2), fun q => (q.1 + q.2, q.2), fun q => by simp, fun q => by simp⟩
  have hprod' := ψ.hasSum_iff.2 hprod
  have hfib : HasSum (fun y : ℤ => ∑' b : ℤ, u (y - b) * u b) (integerCF g (-s) ^ 2) :=
    hprod'.prod_fiberwise (fun y => (hprod'.summable.prod_factor y).hasSum)
  have hc : ∀ y : ℤ, ∑' b : ℤ, u (y - b) * u b =
      cfPhase (-s) y * ((∑ b ∈ Finset.Icc (y + 1) (-1), g (y - b) * g b : ℝ) : ℂ) := by
    intro y
    rw [tsum_eq_sum (s := Finset.Icc (y + 1) (-1))]
    · rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : cfPhase (-s) y = cfPhase (-s) (y - b) * cfPhase (-s) b := by
        rw [← cfPhase_add]
        congr 1
        ring
      simp only [u]
      rw [this]
      push_cast
      ring
    · intro b hb
      simp only [Finset.mem_Icc, not_and_or, not_le] at hb
      simp only [u]
      rcases hb with hb | hb
      · rw [hgsupp (y - b) (by omega)]
        simp
      · rw [hgsupp b (by omega)]
        simp
  have hfib' : HasSum (fun y : ℤ => cfPhase (-s) y *
      ((∑ b ∈ Finset.Icc (y + 1) (-1), g (y - b) * g b : ℝ) : ℂ)) (integerCF g (-s) ^ 2) := by
    convert hfib using 1
    funext y
    exact (hc y).symm
  have hz : ∀ y : ℤ, 0 ≤ y → cfPhase (-s) y *
      ((∑ b ∈ Finset.Icc (y + 1) (-1), g (y - b) * g b : ℝ) : ℂ) = 0 := by
    intro y hy
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  have hh := hasSum_neg_half hfib' hz
  convert hh using 1
  funext n
  rw [convSum_eq]



theorem fiber_identity {f g : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
         else 0))
    (t : ℝ) (y : ℤ) (hy : y ≤ -1) :
    3 * integerCF f t * (g y : ℂ) = integerCF f t * (f y : ℂ) +
      integerCF f t *
        ((∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) : ℝ) : ℂ) +
      (if y = -1 then cfPhase t (-1) *
        (integerCF f t * ((f 0 : ℂ) + negativeCF f t) + integerCF g (-t)) else 0) := by
  have hF := hasSum_cf hf hfs.summable t
  set S : ℝ := ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) with hS
  have core : ∀ (extra : ℤ → ℝ) (V : ℂ),
      HasSum (fun x : ℤ => cfPhase t x * (extra x : ℂ)) V →
      (∀ x, 3 * f x * g y = f x * f y + f x * S + extra x) →
      3 * integerCF f t * (g y : ℂ) =
        integerCF f t * (f y : ℂ) + integerCF f t * (S : ℂ) + V := by
    intro extra V hV hr
    have h1 : HasSum (fun x : ℤ => cfPhase t x * ((3 * f x * g y : ℝ) : ℂ))
        ((3 * (g y : ℂ)) * integerCF f t) := by
      convert hF.mul_left (3 * (g y : ℂ)) using 1
      funext x
      push_cast
      ring
    have h2 : HasSum (fun x : ℤ => cfPhase t x * ((f x * f y : ℝ) : ℂ))
        (integerCF f t * (f y : ℂ)) := by
      convert hF.mul_right (f y : ℂ) using 1
      funext x
      push_cast
      ring
    have h3 : HasSum (fun x : ℤ => cfPhase t x * ((f x * S : ℝ) : ℂ))
        (integerCF f t * (S : ℂ)) := by
      convert hF.mul_right (S : ℂ) using 1
      funext x
      push_cast
      ring
    have h5 := (h2.add h3).add hV
    have hfun : (fun x : ℤ => cfPhase t x * ((3 * f x * g y : ℝ) : ℂ)) =
        fun x : ℤ => cfPhase t x * ((f x * f y : ℝ) : ℂ) +
          cfPhase t x * ((f x * S : ℝ) : ℂ) + cfPhase t x * (extra x : ℂ) := by
      funext x
      rw [hr x]
      push_cast
      ring
    rw [hfun] at h1
    have := h1.unique h5
    linear_combination this
  by_cases hy1 : y = -1
  · subst hy1
    have hA := hasSum_forward_pairs hf hfs t
    have hB := hasSum_backward_term hg hgs.summable t
    have hAB := hA.add hB
    have key := core
      (fun x => (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1))
      (integerCF f t * cfPhase t (-1) * ((f 0 : ℂ) + negativeCF f t) +
        cfPhase t (-1) * integerCF g (-t))
      (by
        convert hAB using 1
        funext x
        rw [Complex.ofReal_add, mul_add])
      (fun x => by
        have h := hrec x (-1) hy
        simp only [↓reduceIte] at h
        exact h)
    simp only [↓reduceIte]
    rw [key]
    ring
  · have key := core (fun _ => 0) 0 (by simp)
      (fun x => by
        have h := hrec x y hy
        simp [hy1] at h
        simpa using h)
    simp [hy1]
    simpa using key



theorem ldp_big_rel_of_master {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
         else 0))
    (s t : ℝ) :
    3 * integerCF g (-s) * integerCF f t =
      integerCF f t * (negativeCF f (-s) + integerCF g (-s) ^ 2) +
        cfPhase (-s) (-1) * cfPhase t (-1) *
          (integerCF f t * ((f 0 : ℂ) + negativeCF f t) + integerCF g (-t)) := by
  have hGs : HasSum (fun n : ℕ => (g (-((n : ℤ) + 1)) : ℂ) * cfPhase (-s) (-((n : ℤ) + 1)))
      (integerCF g (-s)) :=
    hasSum_neg_half (w := fun k => (g k : ℂ) * cfPhase (-s) k)
      (hasSum_cf hg hgs.summable (-s)) (fun k hk => by simp [hgsupp k hk])
  have hNs := hasSum_negativeCF hf hfs.summable (-s)
  have hC := hasSum_conv hg hgs hgsupp s
  have hI : HasSum (fun n : ℕ => if n = 0 then cfPhase (-s) (-1) * (cfPhase t (-1) *
      (integerCF f t * ((f 0 : ℂ) + negativeCF f t) + integerCF g (-t))) else 0)
      (cfPhase (-s) (-1) * (cfPhase t (-1) *
      (integerCF f t * ((f 0 : ℂ) + negativeCF f t) + integerCF g (-t)))) :=
    hasSum_ite_eq 0 _
  have hL := hGs.mul_left (3 * integerCF f t)
  have hR := ((hNs.mul_left (integerCF f t)).add (hC.mul_left (integerCF f t))).add hI
  have hterm : ∀ n : ℕ, 3 * integerCF f t *
      ((g (-((n : ℤ) + 1)) : ℂ) * cfPhase (-s) (-((n : ℤ) + 1))) =
      (integerCF f t * ((f (-((n : ℤ) + 1)) : ℂ) * cfPhase (-s) (-((n : ℤ) + 1))) +
        integerCF f t * (cfPhase (-s) (-((n : ℤ) + 1)) *
          ((∑ j ∈ Finset.Icc (1 : ℤ) (-(-((n : ℤ) + 1)) - 1),
            g (-((n : ℤ) + 1) + j) * g (-j) : ℝ) : ℂ))) +
      (if n = 0 then cfPhase (-s) (-1) * (cfPhase t (-1) *
        (integerCF f t * ((f 0 : ℂ) + negativeCF f t) + integerCF g (-t))) else 0) := by
    intro n
    have h := fiber_identity hf hfs hg hgs hrec t (-((n : ℤ) + 1)) (by omega)
    by_cases hn : n = 0
    · subst hn
      simp only [Nat.cast_zero, zero_add, ↓reduceIte] at h ⊢
      linear_combination cfPhase (-s) (-1) * h
    · have hn' : ¬ (-((n : ℤ) + 1) = -1) := by omega
      simp only [hn, hn', ↓reduceIte] at h ⊢
      linear_combination cfPhase (-s) (-((n : ℤ) + 1)) * h
  have hR' : HasSum (fun n : ℕ => 3 * integerCF f t *
      ((g (-((n : ℤ) + 1)) : ℂ) * cfPhase (-s) (-((n : ℤ) + 1))))
      (integerCF f t * negativeCF f (-s) + integerCF f t * integerCF g (-s) ^ 2 +
        cfPhase (-s) (-1) * (cfPhase t (-1) *
          (integerCF f t * ((f 0 : ℂ) + negativeCF f t) + integerCF g (-t)))) := by
    convert hR using 1
    funext n
    exact hterm n
  have := hL.unique hR'
  linear_combination this




theorem ldp_quadratic_of_master {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
         else 0))
    (t : ℝ) :
    (integerCF f t) ^ 2 * (ldpHat f t) ^ 2 +
      (3 * integerCF f t - 1) * ldpHat f t + integerCF f t = 0 := by
  have hb0 := ldp_big_rel_of_master hf hfs hg hgs hgsupp hrec 0 t
  have hb1 := ldp_big_rel_of_master hf hfs hg hgs hgsupp hrec t 0
  have hN0 := negativeCF_zero hf hfs hsymm
  have hF0 := integerCF_zero hf hfs
  have hG0 := integerCF_zero hg hgs
  have hsplit := integerCF_eq_split hf hfs.summable hsymm t
  have hpE := cfPhase_neg_one_mul t
  simp only [neg_zero, hN0, hG0, hF0, cfPhase_zero_left, cfPhase_neg_t_neg_one] at hb0 hb1
  push_cast at hb0 hb1
  have hG : integerCF g (-t) = -(integerCF f t * ldpHat f t) := by
    unfold ldpHat ldpOffset
    push_cast
    linear_combination (-Complex.exp ((t : ℂ) * Complex.I)) * hb0 +
      (-(integerCF f t * ((f 0 : ℂ) + negativeCF f t) + integerCF g (-t))) * hpE
  have hM : negativeCF f (-t) = integerCF f t - (f 0 : ℂ) - negativeCF f t := by
    linear_combination (-1 : ℂ) * hsplit
  rw [hG, hM] at hb1
  unfold ldpHat ldpOffset at hb1 ⊢
  push_cast at hb1 ⊢
  linear_combination (-1 : ℂ) * hb1




theorem ldp_real_transform_expansion_of_master {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
         else 0)) :
    let κ : ℝ := 3 + f 0
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    0 < κ ∧
      (fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (a : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)]
          (fun t : ℝ => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) :=
  ldp_real_transform_expansion hf hfs hg hgs hsymm hgsupp hrec
    (ldp_quadratic_of_master hf hfs hg hgs hsymm hgsupp hrec)
    (ldp_real_part_of_symm hf hfs hsymm)

end DirectedDistances.Recursive
