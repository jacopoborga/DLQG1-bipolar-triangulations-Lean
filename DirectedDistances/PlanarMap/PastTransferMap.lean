/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PiecewiseLinearInterp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace DirectedDistances.PlanarMap

noncomputable section

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. The transfer between seam graphs. -/
@[expose] def pastTransfer (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) (z : ℂ) : ℂ :=
  ⟨-(phi z.re), -z.im + f0 (-(phi z.re)) + fp z.re⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Its explicit inverse. -/
@[expose] def pastTransferInv (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) (z : ℂ) : ℂ :=
  ⟨phi.symm (-z.re), -z.im + f0 z.re + fp (phi.symm (-z.re))⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Left inverse identity. -/
theorem pastTransferInv_pastTransfer (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) (z : ℂ) :
    pastTransferInv phi f0 fp (pastTransfer phi f0 fp z) = z := by
  apply Complex.ext <;> simp only [pastTransferInv, pastTransfer, neg_neg,
    OrderIso.symm_apply_apply]; ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Right inverse identity. -/
theorem pastTransfer_pastTransferInv (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) (z : ℂ) :
    pastTransfer phi f0 fp (pastTransferInv phi f0 fp z) = z := by
  apply Complex.ext <;> simp only [pastTransferInv, pastTransfer,
    OrderIso.apply_symm_apply, neg_neg]; ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Continuity of the transfer. -/
theorem pastTransfer_continuous (phi : ℝ ≃o ℝ) {f0 fp : ℝ → ℝ}
    (h0 : Continuous f0) (hp : Continuous fp) : Continuous (pastTransfer phi f0 fp) := by
  have hphi : Continuous (fun z : ℂ => phi z.re) := phi.continuous.comp Complex.continuous_re
  unfold pastTransfer
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Continuity of the inverse. -/
theorem pastTransferInv_continuous (phi : ℝ ≃o ℝ) {f0 fp : ℝ → ℝ}
    (h0 : Continuous f0) (hp : Continuous fp) : Continuous (pastTransferInv phi f0 fp) := by
  have hphi : Continuous (fun z : ℂ => phi.symm (-z.re)) :=
    phi.symm.continuous.comp Complex.continuous_re.neg
  unfold pastTransferInv
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. The transfer as a homeomorphism. -/
@[expose] def pastTransferHomeomorph (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ)
    (h0 : Continuous f0) (hp : Continuous fp) : ℂ ≃ₜ ℂ where
  toFun := pastTransfer phi f0 fp
  invFun := pastTransferInv phi f0 fp
  left_inv := pastTransferInv_pastTransfer phi f0 fp
  right_inv := pastTransfer_pastTransferInv phi f0 fp
  continuous_toFun := pastTransfer_continuous phi h0 hp
  continuous_invFun := pastTransferInv_continuous phi h0 hp

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Signed height reverses. -/
theorem pastTransfer_height (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) (z : ℂ) :
    (pastTransfer phi f0 fp z).im - f0 (pastTransfer phi f0 fp z).re =
      -(z.im - fp z.re) := by
  dsimp [pastTransfer]
  ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Images of signed-height predicates. -/
theorem pastTransfer_image_height (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) (P : ℝ → Prop) :
    pastTransfer phi f0 fp '' {z | P (z.im - fp z.re)} =
      {z | P (-(z.im - f0 z.re))} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Set.mem_ofPred_eq, pastTransfer_height, neg_neg] using hw
  · intro hz
    refine ⟨pastTransferInv phi f0 fp z, ?_, pastTransfer_pastTransferInv phi f0 fp z⟩
    have hh := pastTransfer_height phi f0 fp (pastTransferInv phi f0 fp z)
    rw [pastTransfer_pastTransferInv] at hh
    have he : (pastTransferInv phi f0 fp z).im -
        fp (pastTransferInv phi f0 fp z).re = -(z.im - f0 z.re) := by
      linarith only [hh]
    change P ((pastTransferInv phi f0 fp z).im -
      fp (pastTransferInv phi f0 fp z).re)
    rw [he]
    exact hz

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Exact seam-graph image. -/
theorem pastTransfer_image_graph (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) :
    pastTransfer phi f0 fp '' {z | z.im = fp z.re} = {z | z.im = f0 z.re} := by
  simpa only [sub_eq_zero, neg_eq_zero] using
    pastTransfer_image_height phi f0 fp (fun t => t = 0)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. The open upper side maps below. -/
theorem pastTransfer_image_above (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) :
    pastTransfer phi f0 fp '' {z | fp z.re < z.im} = {z | z.im < f0 z.re} := by
  simpa only [sub_pos, neg_pos, sub_neg] using
    pastTransfer_image_height phi f0 fp (fun t => 0 < t)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. The open lower side maps above. -/
theorem pastTransfer_image_below (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) :
    pastTransfer phi f0 fp '' {z | z.im < fp z.re} = {z | f0 z.re < z.im} := by
  simpa only [sub_neg, neg_lt_zero, sub_pos] using
    pastTransfer_image_height phi f0 fp (fun t => t < 0)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. The closed upper side maps below. -/
theorem pastTransfer_image_onOrAbove (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) :
    pastTransfer phi f0 fp '' {z | fp z.re ≤ z.im} = {z | z.im ≤ f0 z.re} := by
  simpa only [sub_nonneg, neg_nonneg, sub_nonpos] using
    pastTransfer_image_height phi f0 fp (fun t => 0 ≤ t)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. The closed lower side maps above. -/
theorem pastTransfer_image_onOrBelow (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) :
    pastTransfer phi f0 fp '' {z | z.im ≤ fp z.re} = {z | f0 z.re ≤ z.im} := by
  simpa only [sub_nonpos, neg_nonpos, sub_nonneg] using
    pastTransfer_image_height phi f0 fp (fun t => t ≤ 0)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. The linear part on an affine strip. -/
@[expose] def pastTransferLinear (m0 m1 m2 : ℝ) : ℂ →L[ℝ] ℂ where
  toFun z := ⟨-m0 * z.re, -z.im + (m1 + m2) * z.re⟩
  map_add' u v := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im] <;> ring
  map_smul' t z := by
    apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im,
      RingHom.id_apply, smul_eq_mul] <;> ring
  cont := by
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. The affine extension on a strip. -/
@[expose] def pastTransferAffine (m0 c0 m1 c1 m2 c2 : ℝ) : ℂ →ᵃ[ℝ] ℂ where
  toFun z := ⟨-(m0 * z.re + c0), -z.im + (m2 * z.re + c2) + (m1 * z.re + c1)⟩
  linear := (pastTransferLinear m0 m1 m2).toLinearMap
  map_vadd' p v := by
    apply Complex.ext <;>
      simp only [vadd_eq_add, Complex.add_re, Complex.add_im, pastTransferLinear,
        LinearMap.coe_mk, AddHom.coe_mk] <;> ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Agreement on the closed strip. -/
theorem pastTransfer_eqOn_affine (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ)
    (c d m0 c0 m1 c1 m2 c2 : ℝ)
    (hphi : ∀ x ∈ Set.Icc c d, phi x = m0 * x + c0)
    (hp : ∀ x ∈ Set.Icc c d, fp x = m1 * x + c1)
    (h0 : ∀ x ∈ Set.Icc c d, f0 (-(phi x)) = m2 * x + c2) :
    Set.EqOn (pastTransfer phi f0 fp) (pastTransferAffine m0 c0 m1 c1 m2 c2)
      {z | c ≤ z.re ∧ z.re ≤ d} := by
  intro z hz
  apply Complex.ext
  · exact congrArg Neg.neg (hphi z.re hz)
  · change -z.im + f0 (-(phi z.re)) + fp z.re = _
    rw [h0 z.re hz, hp z.re hz]
    rfl

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Strip-affinity existence interface. -/
theorem pastTransfer_exists_affine (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ) (c d : ℝ)
    (h : ∃ m0 c0 m1 c1 m2 c2 : ℝ,
      (∀ x ∈ Set.Icc c d, phi x = m0 * x + c0) ∧
      (∀ x ∈ Set.Icc c d, fp x = m1 * x + c1) ∧
      (∀ x ∈ Set.Icc c d, f0 (-(phi x)) = m2 * x + c2)) :
    ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn (pastTransfer phi f0 fp) A
      {z | c ≤ z.re ∧ z.re ≤ d} := by
  obtain ⟨m0, c0, m1, c1, m2, c2, hphi, hp, h0⟩ := h
  exact ⟨pastTransferAffine m0 c0 m1 c1 m2 c2,
    pastTransfer_eqOn_affine phi f0 fp c d m0 c0 m1 c1 m2 c2 hphi hp h0⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Concrete linear-part formula. -/
theorem pastTransferAffine_sub_zero (m0 c0 m1 c1 m2 c2 : ℝ) (z : ℂ) :
    pastTransferAffine m0 c0 m1 c1 m2 c2 z - pastTransferAffine m0 c0 m1 c1 m2 c2 0 =
      (⟨-m0 * z.re, -z.im + (m1 + m2) * z.re⟩ : ℂ) := by
  apply Complex.ext <;>
    simp only [pastTransferAffine, AffineMap.coe_mk, Complex.sub_re, Complex.sub_im,
      Complex.zero_re, Complex.zero_im] <;> ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Cross products scale by m0. -/
theorem pastTransferLinear_cross (m0 m1 m2 : ℝ) (u v : ℂ) :
    (pastTransferLinear m0 m1 m2 u).re * (pastTransferLinear m0 m1 m2 v).im -
      (pastTransferLinear m0 m1 m2 u).im * (pastTransferLinear m0 m1 m2 v).re =
      m0 * (u.re * v.im - u.im * v.re) := by
  dsimp [pastTransferLinear]
  ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Positive determinant when m0 is positive. -/
theorem pastTransferAffine_det_pos {m0 : ℝ} (hm0 : 0 < m0) :
    0 < (-m0) * (-1 : ℝ) := by
  simpa only [neg_mul_neg, mul_one] using hm0

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Exact direction on a strip segment. -/
theorem pastTransfer_segment_direction (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ)
    (c d m0 c0 m1 c1 m2 c2 : ℝ)
    (hphi : ∀ x ∈ Set.Icc c d, phi x = m0 * x + c0)
    (hp : ∀ x ∈ Set.Icc c d, fp x = m1 * x + c1)
    (h0 : ∀ x ∈ Set.Icc c d, f0 (-(phi x)) = m2 * x + c2)
    (z v : ℂ) (t : ℝ) (hz : c ≤ z.re ∧ z.re ≤ d)
    (ht : c ≤ (z + t • v).re ∧ (z + t • v).re ≤ d) :
    pastTransfer phi f0 fp (z + t • v) - pastTransfer phi f0 fp z =
      t • pastTransferLinear m0 m1 m2 v := by
  rw [pastTransfer_eqOn_affine phi f0 fp c d m0 c0 m1 c1 m2 c2 hphi hp h0 ht,
    pastTransfer_eqOn_affine phi f0 fp c d m0 c0 m1 c1 m2 c2 hphi hp h0 hz]
  apply Complex.ext <;> simp only [pastTransferAffine, AffineMap.coe_mk, pastTransferLinear,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: the orientation-preserving past transfer
F(x,y) = (-phi x, -y + g x)); not a paper result. Derivative direction at a strip interior. -/
theorem pastTransfer_hasDerivAt_segment (phi : ℝ ≃o ℝ) (f0 fp : ℝ → ℝ)
    (c d m0 c0 m1 c1 m2 c2 : ℝ)
    (hphi : ∀ x ∈ Set.Icc c d, phi x = m0 * x + c0)
    (hp : ∀ x ∈ Set.Icc c d, fp x = m1 * x + c1)
    (h0 : ∀ x ∈ Set.Icc c d, f0 (-(phi x)) = m2 * x + c2)
    (z v : ℂ) (hz : c < z.re ∧ z.re < d) :
    HasDerivAt (fun t : ℝ => pastTransfer phi f0 fp (z + t • v))
      (pastTransferLinear m0 m1 m2 v) 0 := by
  let A := pastTransferAffine m0 c0 m1 c1 m2 c2
  have hA : Continuous A := by
    change Continuous (fun w : ℂ =>
      Complex.mk (-(m0 * w.re + c0))
        (-w.im + (m2 * w.re + c2) + (m1 * w.re + c1)))
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  let B : ℂ →ᴬ[ℝ] ℂ := ⟨A, hA⟩
  have hcurve : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hder := B.hasFDerivAt.comp_hasDerivAt 0 hcurve
  apply hder.congr_of_eventuallyEq
  have hcont : Continuous (fun t : ℝ => (z + t • v).re) := by fun_prop
  have hn : Set.Ioo c d ∈ nhds ((z + (0 : ℝ) • v).re) := by
    simpa only [zero_smul, add_zero] using isOpen_Ioo.mem_nhds hz
  have hev := hcont.continuousAt.eventually_mem hn
  filter_upwards [hev] with t ht
  exact pastTransfer_eqOn_affine phi f0 fp c d m0 c0 m1 c1 m2 c2
    hphi hp h0 ⟨ht.1.le, ht.2.le⟩

end

end DirectedDistances.PlanarMap
