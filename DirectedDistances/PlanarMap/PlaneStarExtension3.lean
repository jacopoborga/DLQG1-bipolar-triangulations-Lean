/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlaneStarExtension2
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Logarithmic lifts for radial extensions

Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
a degree-one real lift commutes with every integer angular period. -/
theorem starLift_add_int_mul (f : ℝ → ℝ)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi)
    (t : ℝ) (k : ℤ) :
    f (t + k * (2 * Real.pi)) = f t + k * (2 * Real.pi) := by
  have hp : Function.Periodic (fun t => f t - t) (2 * Real.pi) := by
    intro t
    change f (t + 2 * Real.pi) - (t + 2 * Real.pi) = f t - t
    rw [hper]
    ring
  have hk := hp.int_mul k t
  change f (t + ↑k * (2 * Real.pi)) - (t + ↑k * (2 * Real.pi)) = f t - t at hk
  linarith only [hk]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the inverse real lift also has degree one. -/
theorem starLift_symm_period (f : ℝ ≃ₜ ℝ)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi)
    (t : ℝ) :
    f.symm (t + 2 * Real.pi) = f.symm t + 2 * Real.pi := by
  apply f.injective
  rw [f.apply_symm_apply, hper, f.apply_symm_apply]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone extension acts on a complex exponential by changing its imaginary part. -/
theorem starConeHomeomorph_complex_exp (f : ℝ ≃ₜ ℝ) (h : Circle ≃ₜ Circle)
    (hh : ∀ t : ℝ, h (Circle.exp t) = Circle.exp (f t)) (z : ℂ) :
    starConeHomeomorph h (Complex.exp z) =
      Complex.exp ((z.re : ℂ) + (f z.im : ℂ) * Complex.I) := by
  have hz : Complex.exp z =
      (Real.exp z.re : ℂ) * (Circle.exp z.im : ℂ) := by
    rw [Circle.coe_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    exact (Complex.re_add_im z).symm
  rw [hz, starConeHomeomorph_exp f h hh _ _ (Real.exp_pos _).le,
    Circle.coe_exp, Complex.ofReal_exp, ← Complex.exp_add]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
a continuous logarithmic correction with equal endpoint values preserves the
increment of a logarithmic lift. -/
theorem star_log_increment_correction (γ δ : C(I, ℂ)) (a : C(I, ℂ))
    (ha : ∀ t, Complex.exp (a t) * γ t = δ t)
    (haend : a 1 = a 0) (n : ℤ) :
    (∃ φ : C(I, ℂ), (∀ t, Complex.exp (φ t) = γ t) ∧
      φ 1 - φ 0 = 2 * Real.pi * Complex.I * n) ↔
    (∃ φ : C(I, ℂ), (∀ t, Complex.exp (φ t) = δ t) ∧
      φ 1 - φ 0 = 2 * Real.pi * Complex.I * n) := by
  constructor
  · rintro ⟨φ, hφ, hend⟩
    refine ⟨⟨fun t => a t + φ t, a.continuous.add φ.continuous⟩, ?_, ?_⟩
    · intro t
      change Complex.exp (a t + φ t) = _
      rw [Complex.exp_add, hφ, ha]
    · change (a 1 + φ 1) - (a 0 + φ 0) = _
      rw [haend]
      linear_combination hend
  · rintro ⟨φ, hφ, hend⟩
    refine ⟨⟨fun t => φ t - a t, φ.continuous.sub a.continuous⟩, ?_, ?_⟩
    · intro t
      change Complex.exp (φ t - a t) = _
      rw [Complex.exp_sub, hφ, ← ha, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
    · change (φ 1 - a 1) - (φ 0 - a 0) = _
      rw [haend]
      linear_combination hend

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
nearby nonzero loops have the same logarithmic increments whenever their
pointwise ratio stays in the principal logarithm's slit plane. -/
theorem star_log_increment_ratio (γ δ : C(I, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hγend : γ 1 = γ 0) (hδend : δ 1 = δ 0)
    (hratio : ∀ t, δ t / γ t ∈ Complex.slitPlane) (n : ℤ) :
    (∃ φ : C(I, ℂ), (∀ t, Complex.exp (φ t) = γ t) ∧
      φ 1 - φ 0 = 2 * Real.pi * Complex.I * n) ↔
    (∃ φ : C(I, ℂ), (∀ t, Complex.exp (φ t) = δ t) ∧
      φ 1 - φ 0 = 2 * Real.pi * Complex.I * n) := by
  let a : C(I, ℂ) := ⟨fun t => Complex.log (δ t / γ t),
    (δ.continuous.div γ.continuous hγ).clog hratio⟩
  apply star_log_increment_correction γ δ a
  · intro t
    change Complex.exp (Complex.log (δ t / γ t)) * γ t = δ t
    rw [Complex.exp_log (Complex.slitPlane_ne_zero (hratio t)),
      div_mul_cancel₀ _ (hγ t)]
  · change Complex.log (δ 1 / γ 1) = Complex.log (δ 0 / γ 0)
    rw [hγend, hδend]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
logarithmic increments are invariant through a jointly continuous family of
closed nonzero loops. Both the loop and its omitted point may move. -/
theorem star_log_increment_homotopy (F : C(I × I, ℂ))
    (hnz : ∀ s t, F (s, t) ≠ 0) (hloop : ∀ s, F (s, 1) = F (s, 0)) (n : ℤ) :
    (∃ φ : C(I, ℂ), (∀ t, Complex.exp (φ t) = F (0, t)) ∧
      φ 1 - φ 0 = 2 * Real.pi * Complex.I * n) ↔
    (∃ φ : C(I, ℂ), (∀ t, Complex.exp (φ t) = F (1, t)) ∧
      φ 1 - φ 0 = 2 * Real.pi * Complex.I * n) := by
  let P : I → Prop := fun s => ∃ φ : C(I, ℂ),
    (∀ t, Complex.exp (φ t) = F (s, t)) ∧
      φ 1 - φ 0 = 2 * Real.pi * Complex.I * n
  have hlocal (s : I) : ∀ᶠ r in 𝓝 s, P s ↔ P r := by
    have he : ∀ᶠ r in 𝓝 s, ∀ t : I, F (r, t) / F (s, t) ∈ Complex.slitPlane := by
      have hc := isCompact_univ.eventually_forall_of_forall_eventually
        (X := I) (Y := I) (x₀ := s) (P := fun r t => F (r, t) / F (s, t) ∈ Complex.slitPlane)
        (fun t _ => ?_)
      · simpa only [Set.mem_univ, forall_const] using hc
      · have hcont : Continuous (fun p : I × I => F p / F (s, p.2)) :=
          F.continuous.div (F.continuous.comp (continuous_const.prodMk continuous_snd))
            (fun p => hnz s p.2)
        apply hcont.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds ?_)
        simp only [div_self (hnz s t)]
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    filter_upwards [he] with r hr
    exact star_log_increment_ratio
      ⟨fun t => F (s, t), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
      ⟨fun t => F (r, t), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
      (hnz s) (hloop s) (hloop r) hr n
  have ho : IsOpen {s | P s} := isOpen_iff_mem_nhds.mpr fun s hs =>
    (hlocal s).mono fun r hr => hr.mp hs
  have hc : IsOpen {s | ¬ P s} := isOpen_iff_mem_nhds.mpr fun s hs =>
    (hlocal s).mono fun r hr => fun hp => hs (hr.mpr hp)
  have hcl : IsClopen {s | P s} := ⟨by simpa only [Set.compl_ofPred, not_not] using hc.isClosed_compl, ho⟩
  change P 0 ↔ P 1
  constructor
  · intro h0
    have hu := hcl.eq_univ ⟨0, h0⟩
    exact (Set.ext_iff.mp hu (1 : I)).mpr (Set.mem_univ _)
  · intro h1
    have hu := hcl.eq_univ ⟨1, h1⟩
    exact (Set.ext_iff.mp hu (0 : I)).mpr (Set.mem_univ _)

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
linear interpolation of the identity and an increasing angular lift. -/
@[expose] def starAngularInterpolate (f : ℝ → ℝ) (s : I) (t : ℝ) : ℝ :=
  (1 - (s : ℝ)) * t + (s : ℝ) * f t

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
every interpolated angular lift remains strictly increasing. -/
theorem strictMono_starAngularInterpolate (f : ℝ → ℝ) (hf : StrictMono f) (s : I) :
    StrictMono (starAngularInterpolate f s) := by
  intro x y hxy
  dsimp only [starAngularInterpolate]
  have h₁ := mul_nonneg (sub_nonneg.mpr s.property.2) (sub_pos.mpr hxy).le
  have h₂ := mul_nonneg s.property.1 (sub_pos.mpr (hf hxy)).le
  by_cases hs : (s : ℝ) = 0
  · simp only [hs, sub_zero, one_mul, zero_mul, add_zero]
    exact hxy
  · have hp := mul_pos (lt_of_le_of_ne s.property.1 (Ne.symm hs)) (sub_pos.mpr (hf hxy))
    nlinarith only [h₁, hp]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
every interpolated angular lift has degree one. -/
theorem starAngularInterpolate_add_int_mul (f : ℝ → ℝ)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi)
    (s : I) (t : ℝ) (k : ℤ) :
    starAngularInterpolate f s (t + k * (2 * Real.pi)) =
      starAngularInterpolate f s t + k * (2 * Real.pi) := by
  dsimp only [starAngularInterpolate]
  rw [starLift_add_int_mul f hper]
  ring

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
interpolating angular lifts respects equality on the circle. -/
theorem starAngularInterpolate_exp_congr (f : ℝ → ℝ)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi)
    (s : I) {a b : ℝ} (hab : Circle.exp a = Circle.exp b) :
    Circle.exp (starAngularInterpolate f s a) =
      Circle.exp (starAngularInterpolate f s b) := by
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hab
  rw [hk, starAngularInterpolate_add_int_mul f hper]
  exact Circle.exp_eq_exp.mpr ⟨k, rfl⟩

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the circle interpolation induced by the angular lifts. -/
@[expose] def starCircleInterpolate (f : ℝ → ℝ) (s : I) (c : Circle) : Circle :=
  Circle.exp (starAngularInterpolate f s (Complex.arg c))

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the induced circle interpolation realizes every lifted angle. -/
theorem starCircleInterpolate_exp (f : ℝ → ℝ)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi)
    (s : I) (t : ℝ) :
    starCircleInterpolate f s (Circle.exp t) = Circle.exp (starAngularInterpolate f s t) :=
  starAngularInterpolate_exp_congr f hper s (Circle.exp_arg _)

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the interpolation is jointly continuous, including at the angular cut. -/
theorem continuous_starCircleInterpolate (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi) :
    Continuous (fun p : I × Circle => starCircleInterpolate f p.1 p.2) := by
  have hq : Topology.IsQuotientMap (Prod.map (id : I → I) Circle.exp) :=
    ((Homeomorph.refl I).isOpenMap.prodMap isLocalHomeomorph_circleExp.isOpenMap).isQuotientMap
      (continuous_id.prodMap Circle.exp.continuous)
      (Function.surjective_id.prodMap Circle.exp_surjective)
  apply hq.continuous_iff.mpr
  have he : (fun p : I × Circle => starCircleInterpolate f p.1 p.2) ∘
      Prod.map (id : I → I) Circle.exp =
      fun p : I × ℝ => Circle.exp (starAngularInterpolate f p.1 p.2) := by
    funext p
    exact starCircleInterpolate_exp f hper p.1 p.2
  rw [he]
  apply Circle.exp.continuous.comp
  dsimp only [starAngularInterpolate]
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul continuous_snd |>.add
    ((continuous_subtype_val.comp continuous_fst).mul (hf.comp continuous_snd))

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
each member of the circle interpolation is injective. -/
theorem starCircleInterpolate_injective (f : ℝ → ℝ) (hf : StrictMono f)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi) (s : I) :
    Function.Injective (starCircleInterpolate f s) := by
  intro c d hcd
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hcd
  have he : Complex.arg c = Complex.arg d + k * (2 * Real.pi) := by
    apply (strictMono_starAngularInterpolate f hf s).injective
    rw [starAngularInterpolate_add_int_mul f hper]
    exact hk
  have hc := Circle.exp_eq_exp.mpr ⟨k, he⟩
  simpa only [Circle.exp_arg] using hc

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
an injective circle map induces an injective cone map. -/
theorem starConeMap_injective (h : Circle → Circle) (hh : Function.Injective h) :
    Function.Injective (starConeMap h) := by
  intro z w he
  have hn : ‖z‖ = ‖w‖ := by simpa only [norm_starConeMap] using congrArg norm he
  by_cases hz : z = 0
  · subst z
    have hw : w = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hn.symm)
    exact hw.symm
  have hw : w ≠ 0 := by
    intro hw
    exact hz (norm_eq_zero.mp (by simpa only [hw, norm_zero] using hn))
  have hd := congrArg starDirection he
  change starDirection ((‖z‖ : ℂ) * (h (starDirection z) : ℂ)) =
    starDirection ((‖w‖ : ℂ) * (h (starDirection w) : ℂ)) at hd
  rw [starDirection_polar _ (norm_pos_iff.mpr hz),
    starDirection_polar _ (norm_pos_iff.mpr hw)] at hd
  have hdir := hh hd
  calc
    z = (‖z‖ : ℂ) * (starDirection z : ℂ) := (norm_mul_starDirection z).symm
    _ = (‖w‖ : ℂ) * (starDirection w : ℂ) := by rw [hn, hdir]
    _ = w := norm_mul_starDirection w

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone interpolation is jointly continuous even at its vertex. -/
theorem continuous_starConeInterpolate (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi) :
    Continuous (fun p : I × ℂ => starConeMap (starCircleInterpolate f p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.2 = 0
  · change Filter.Tendsto _ (𝓝 p) (𝓝 (starConeMap (starCircleInterpolate f p.1) p.2))
    rw [hp, starConeMap_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [norm_starConeMap]
    have hc := (continuous_norm.comp (continuous_snd : Continuous (Prod.snd : I × ℂ → ℂ))).continuousAt
      (x := p)
    change Filter.Tendsto (fun x : I × ℂ => ‖x.2‖) (𝓝 p) (𝓝 ‖p.2‖) at hc
    simpa only [hp, norm_zero] using hc
  · exact (Complex.continuous_ofReal.continuousAt.comp
        (continuous_norm.continuousAt.comp continuous_snd.continuousAt)).mul
      (continuous_subtype_val.continuousAt.comp
        ((continuous_starCircleInterpolate f hf hper).continuousAt.comp
          (continuous_fst.continuousAt.prodMk
            ((continuousAt_starDirection hp).comp continuous_snd.continuousAt))))

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone interpolation starts at the identity. -/
theorem starConeInterpolate_zero (f : ℝ → ℝ) (z : ℂ) :
    starConeMap (starCircleInterpolate f 0) z = z := by
  have he : starCircleInterpolate f 0 = id := by
    funext c
    simp only [starCircleInterpolate, starAngularInterpolate, Set.Icc.coe_zero,
      sub_zero, one_mul, zero_mul, add_zero, Circle.exp_arg, id_eq]
  rw [he]
  exact norm_mul_starDirection z

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone interpolation ends at the cone map specified by the angular lift. -/
theorem starConeInterpolate_one (f : ℝ → ℝ) (h : Circle ≃ₜ Circle)
    (hh : ∀ t : ℝ, h (Circle.exp t) = Circle.exp (f t)) (z : ℂ) :
    starConeMap (starCircleInterpolate f 1) z = starConeHomeomorph h z := by
  have he : starCircleInterpolate f 1 = h := by
    funext c
    change Circle.exp ((1 - (1 : ℝ)) * Complex.arg c + (1 : ℝ) * f (Complex.arg c)) = h c
    simp only [sub_self, zero_mul, one_mul, zero_add]
    rw [← hh, Circle.exp_arg]
  rw [he]
  rfl

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone map of an increasing degree-one angular lift preserves winding
numbers about every omitted point. -/
theorem orientationPreserving_starConeHomeomorph
    (f : ℝ ≃ₜ ℝ) (hf : StrictMono f)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi)
    (h : Circle ≃ₜ Circle)
    (hh : ∀ t : ℝ, h (Circle.exp t) = Circle.exp (f t)) :
    OrientationPreserving (starConeHomeomorph h) := by
  intro z L w hw n
  let F : C(I × I, ℂ) := ⟨fun p =>
      starConeMap (starCircleInterpolate f p.1) (L p.2) -
        starConeMap (starCircleInterpolate f p.1) w,
    ((continuous_starConeInterpolate f f.continuous hper).comp
      (continuous_fst.prodMk (L.continuous.comp continuous_snd))).sub
    ((continuous_starConeInterpolate f f.continuous hper).comp
      (continuous_fst.prodMk continuous_const))⟩
  have hnz (s t : I) : F (s, t) ≠ 0 := by
    change starConeMap (starCircleInterpolate f s) (L t) -
      starConeMap (starCircleInterpolate f s) w ≠ 0
    apply sub_ne_zero.mpr
    intro he
    apply hw
    exact ⟨t, starConeMap_injective _ (starCircleInterpolate_injective f hf hper s) he⟩
  have hloop (s : I) : F (s, 1) = F (s, 0) := by
    change starConeMap (starCircleInterpolate f s) (L 1) - _ =
      starConeMap (starCircleInterpolate f s) (L 0) - _
    rw [L.target, L.source]
  have hi := star_log_increment_homotopy F hnz hloop n
  have h0 (t : I) : F (0, t) = L t - w := by
    change starConeMap (starCircleInterpolate f 0) (L t) -
      starConeMap (starCircleInterpolate f 0) w = _
    rw [starConeInterpolate_zero, starConeInterpolate_zero]
  have h1 (t : I) : F (1, t) =
      (L.map (starConeHomeomorph h).continuous) t - starConeHomeomorph h w := by
    change starConeMap (starCircleInterpolate f 1) (L t) -
      starConeMap (starCircleInterpolate f 1) w = _
    rw [starConeInterpolate_one f h hh, starConeInterpolate_one f h hh]
    rfl
  simpa only [HasWinding, h0, h1] using hi

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
cone extension commutes with composition of circle maps. -/
theorem starConeMap_comp (h g : Circle → Circle) (z : ℂ) :
    starConeMap g (starConeMap h z) = starConeMap (g ∘ h) z := by
  change starConeMap g ((‖z‖ : ℂ) * (h (starDirection z) : ℂ)) = _
  rw [starConeMap_polar g _ (norm_nonneg _) _]
  rfl

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
cone extension commutes with composition of circle homeomorphisms. -/
theorem starConeHomeomorph_trans (h g : Circle ≃ₜ Circle) :
    starConeHomeomorph (h.trans g) = (starConeHomeomorph h).trans (starConeHomeomorph g) := by
  apply Homeomorph.ext
  intro z
  exact (starConeMap_comp h g z).symm

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
cone extension commutes with inversion of circle homeomorphisms. -/
theorem starConeHomeomorph_symm (h : Circle ≃ₜ Circle) :
    starConeHomeomorph h.symm = (starConeHomeomorph h).symm := by
  apply Homeomorph.ext
  intro z
  rfl

/- Composition and inverse closure of orientation preservation are already proved
as `OrientationPreserving.trans` and `OrientationPreserving.symm` in
`GeneralPlaneMapOrientedEquiv`. Applied to
`orientationPreserving_starConeHomeomorph`, these require no new geometric
premises. The identities above identify those operations with cone extension
of the corresponding circle operations.

of completion of Definition 3.8, Propositions 5.9 or 5.16, or the geometric
bridge. -/

end DirectedDistances.PlanarMap

