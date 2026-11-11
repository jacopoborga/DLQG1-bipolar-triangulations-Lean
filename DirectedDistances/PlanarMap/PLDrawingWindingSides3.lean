/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides2
public import Mathlib.Analysis.SpecialFunctions.Complex.Log












public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Definition 1.1 / Definition 3.2: the counterclockwise
semicircle returning from `x + u` to `x - u`. -/
@[expose] def leftSemicircle (x u : ℂ) : Path (x + u) (x - u) where
  toFun t := x + u * Complex.exp ((Real.pi * (t : ℝ) : ℝ) * Complex.I)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [Complex.exp_pi_mul_I, sub_eq_add_neg]

/-- Helper toward Definition 1.1 / Definition 3.2: the semicircular return
path is injective whenever its radius vector is nonzero. -/
theorem leftSemicircle_injective (x u : ℂ) (hu : u ≠ 0) :
    Function.Injective (leftSemicircle x u) := by
  intro t v h
  have hexp : Complex.exp ((Real.pi * (t : ℝ) : ℝ) * Complex.I) =
      Complex.exp ((Real.pi * (v : ℝ) : ℝ) * Complex.I) :=
    mul_left_cancel₀ hu (add_left_cancel h)
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := ((Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)
    (y := ((Real.pi * (v : ℝ) : ℝ) : ℂ) * Complex.I)
    (by simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
        ; nlinarith only [Real.pi_pos, t.property.1])
    (by simp; exact mul_le_of_le_one_right Real.pi_pos.le t.property.2)
    (by simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
        ; nlinarith only [Real.pi_pos, v.property.1])
    (by simp; exact mul_le_of_le_one_right Real.pi_pos.le v.property.2) hexp
  have him := congrArg Complex.im he
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] at him
  exact Subtype.ext (mul_left_cancel₀ Real.pi_ne_zero him)

/-- Helper toward Definition 1.1 / Definition 3.2: the return path remains
at precisely the prescribed radius from its center. -/
theorem leftSemicircle_dist (x u : ℂ) (t : I) :
    dist (leftSemicircle x u t) x = ‖u‖ := by
  rw [dist_eq_norm]
  change ‖x + u * Complex.exp ((Real.pi * (t : ℝ) : ℝ) * Complex.I) - x‖ = _
  rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Helper toward Definition 1.1 / Definition 3.2: every interior point of
the return path lies strictly on the left of its oriented diameter. -/
theorem leftSemicircle_side_pos (x u : ℂ) (hu : u ≠ 0)
    (t : I) (ht : t ∈ openParams) :
    0 < (star u * (leftSemicircle x u t - x)).im := by
  have hs : 0 < Real.sin (Real.pi * (t : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi
      (mul_pos Real.pi_pos ht.1)
      (mul_lt_of_lt_one_right Real.pi_pos ht.2)
  change 0 < (star u * (x + u * Complex.exp
    ((Real.pi * (t : ℝ) : ℝ) * Complex.I) - x)).im
  rw [add_sub_cancel_left, ← mul_assoc, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self]
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im, zero_mul, add_zero] using
    mul_pos (Complex.normSq_pos.mpr hu) hs

/-- Helper toward Definition 1.1 / Definition 3.2: traverse the unit
diameter from left to right and return along the upper semicircle. -/
@[expose] def diameterSemicircleLoop : Path (-1 : ℂ) (-1) :=
  (Path.segment (-1 : ℂ) 1).trans
    ((leftSemicircle 0 1).cast (by simp) (by simp))

/-- Helper toward Definition 1.1 / Definition 3.2: the diameter portion
of the model loop has an affine parameterization. -/
private theorem diameterSemicircleLoop_apply_first (t : I)
    (ht : (t : ℝ) ≤ 1 / 2) :
    diameterSemicircleLoop t = ((4 * (t : ℝ) - 1 : ℝ) : ℂ) := by
  rw [diameterSemicircleLoop, Path.trans_apply, dite_eq_left ht]
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, Complex.real_smul]
  push_cast
  ring

/-- Helper toward Definition 1.1 / Definition 3.2: the return portion
of the model loop has its exponential parameterization. -/
private theorem diameterSemicircleLoop_apply_second (t : I)
    (ht : ¬ (t : ℝ) ≤ 1 / 2) :
    diameterSemicircleLoop t =
      Complex.exp ((Real.pi * (2 * (t : ℝ) - 1) : ℝ) * Complex.I) := by
  rw [diameterSemicircleLoop, Path.trans_apply, dite_eq_right ht]
  change 0 + 1 * Complex.exp _ = _
  simp

/-- Helper toward Definition 1.1 / Definition 3.2: the two logarithm
branches will meet at the top of the semicircle. -/
private theorem diameterSemicircleLoop_three_quarters
    (t : I) (ht : (t : ℝ) = 3 / 4) : diameterSemicircleLoop t = Complex.I := by
  rw [diameterSemicircleLoop_apply_second t (by linarith only [ht]), ht]
  have he : Real.pi * (2 * (3 / 4 : ℝ) - 1) = Real.pi / 2 := by ring
  rw [he]
  push_cast
  exact Complex.exp_pi_div_two_mul_I

/-- Helper toward Definition 1.1 / Definition 3.2: the first portion of
the translated model loop avoids the principal logarithm's cut. -/
private theorem diameterSemicircleLoop_slit_first (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (t : I) (ht : (t : ℝ) ≤ 3 / 4) :
    diameterSemicircleLoop t - ε * Complex.I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hhalf : (t : ℝ) ≤ 1 / 2
  · right
    rw [diameterSemicircleLoop_apply_first t hhalf]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_sub]
    exact neg_ne_zero.mpr hε.ne'
  · by_cases hthree : (t : ℝ) = 3 / 4
    · right
      rw [diameterSemicircleLoop_three_quarters t hthree]
      simp only [Complex.sub_im, Complex.I_im, Complex.mul_I_im, Complex.ofReal_re]
      exact sub_ne_zero.mpr hε1.ne'
    · left
      rw [diameterSemicircleLoop_apply_second t hhalf]
      simp only [Complex.sub_re, Complex.exp_ofReal_mul_I_re,
        Complex.mul_I_re, Complex.ofReal_im, neg_zero, sub_zero]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith only [Real.pi_pos, not_le.mp hhalf,
        lt_of_le_of_ne ht hthree]

/-- Helper toward Definition 1.1 / Definition 3.2: negating the remaining
portion avoids the principal logarithm's cut. -/
private theorem diameterSemicircleLoop_slit_second (ε : ℝ) (hε1 : ε < 1)
    (t : I) (ht : 3 / 4 ≤ (t : ℝ)) :
    -(diameterSemicircleLoop t - ε * Complex.I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hthree : (t : ℝ) = 3 / 4
  · right
    rw [diameterSemicircleLoop_three_quarters t hthree]
    simp only [Complex.neg_im, Complex.sub_im, Complex.I_im,
      Complex.mul_I_im, Complex.ofReal_re, neg_ne_zero]
    exact sub_ne_zero.mpr hε1.ne'
  · left
    rw [diameterSemicircleLoop_apply_second t (by linarith only [ht])]
    simp only [Complex.neg_re, Complex.sub_re, Complex.exp_ofReal_mul_I_re,
      Complex.mul_I_re, Complex.ofReal_im, neg_zero, sub_zero, neg_pos]
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith only [Real.pi_pos, lt_of_le_of_ne ht (Ne.symm hthree)]
    · nlinarith only [Real.pi_pos, t.property.2]

/-- Helper toward Definition 1.1 / Definition 3.2: the logarithm branches
agree above the real axis. -/
private theorem log_neg_add_pi_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    Complex.log (-z) + Real.pi * Complex.I = Complex.log z := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.log_re, norm_neg, Complex.mul_I_re,
      Complex.ofReal_im, neg_zero, add_zero]
  · simp only [Complex.add_im, Complex.log_im, Complex.mul_I_im,
      Complex.ofReal_re, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
    ring

/-- Helper toward Definition 1.1 / Definition 3.2: below the real axis
the two logarithm branches differ by one positive full turn. -/
private theorem log_neg_add_pi_of_im_neg (z : ℂ) (hz : z.im < 0) :
    Complex.log (-z) + Real.pi * Complex.I =
      Complex.log z + 2 * Real.pi * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, Complex.mul_re, Complex.mul_im]
  · simp only [Complex.add_im, Complex.log_im, Complex.mul_I_im,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]
    norm_num
    ring

/-- Helper toward Definition 1.1 / Definition 3.2: the positively oriented
unit diameter/semicircle loop winds once about every point `ε * I` with
`0 < ε < 1`. The proof supplies a continuous logarithm explicitly. -/
theorem hasWinding_diameterSemicircleLoop (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    HasWinding diameterSemicircleLoop (ε * Complex.I) 1 := by
  let f : I → ℂ := fun t => diameterSemicircleLoop t - ε * Complex.I
  have hf : Continuous f := diameterSemicircleLoop.continuous.sub continuous_const
  let ψ : I → ℂ := fun t => if (t : ℝ) ≤ 3 / 4 then Complex.log (f t)
    else Complex.log (-f t) + Real.pi * Complex.I
  have hψ : Continuous ψ := by
    apply continuous_if_le continuous_subtype_val continuous_const
    · exact hf.continuousOn.clog
        (fun t ht => diameterSemicircleLoop_slit_first ε hε hε1 t ht)
    · exact (hf.neg.continuousOn.clog
        (fun t ht => diameterSemicircleLoop_slit_second ε hε1 t ht)).add
          continuousOn_const
    · intro t ht
      have him : 0 < (f t).im := by
        dsimp [f]
        rw [diameterSemicircleLoop_three_quarters t ht]
        simpa only [Complex.sub_im, Complex.I_im, Complex.mul_I_im,
          Complex.ofReal_re] using sub_pos.mpr hε1
      exact (log_neg_add_pi_of_im_pos (f t) him).symm
  refine ⟨⟨ψ, hψ⟩, ?_, ?_⟩
  · intro t
    change Complex.exp (ψ t) = f t
    dsimp only [ψ]
    split_ifs with ht
    · exact Complex.exp_log
        (Complex.slitPlane_ne_zero (diameterSemicircleLoop_slit_first ε hε hε1 t ht))
    · rw [Complex.exp_add, Complex.exp_log
        (Complex.slitPlane_ne_zero
          (diameterSemicircleLoop_slit_second ε hε1 t (le_of_not_ge ht))),
        Complex.exp_pi_mul_I]
      ring
  · change ψ 1 - ψ 0 = _
    have hzero : f 0 = -1 - ε * Complex.I := by simp [f]
    have hone : f 1 = -1 - ε * Complex.I := by simp [f]
    have him : (-1 - ε * Complex.I).im < 0 := by
      simpa using hε
    have hend := log_neg_add_pi_of_im_neg (-1 - ε * Complex.I) him
    dsimp only [ψ]
    rw [ite_eq_right (by norm_num), ite_eq_left (by norm_num), hzero, hone, hend]
    push_cast
    ring

/-- Helper toward Definition 1.1 / Definition 3.2: a local diameter,
traversed forward, closed by its left semicircular return path. -/
@[expose] def semicircleLoop (x u : ℂ) : Path (x - u) (x - u) :=
  (Path.segment (x - u) (x + u)).trans (leftSemicircle x u)

/-- Helper toward Definition 1.1 / Definition 3.2: the local loop is the
complex affine image of the unit model. -/
private theorem semicircleLoop_apply (x u : ℂ) (t : I) :
    semicircleLoop x u t = x + u * diameterSemicircleLoop t := by
  rw [semicircleLoop, diameterSemicircleLoop, Path.trans_apply, Path.trans_apply]
  split_ifs
  · simp only [Path.segment_apply, AffineMap.lineMap_apply_module, Complex.real_smul]
    push_cast
    ring
  · change x + u * Complex.exp _ = x + u * (0 + 1 * Complex.exp _)
    ring

/-- Helper toward Definition 1.1 / Definition 3.2: the local semicircle
loop winds positively about all points between its center and the midpoint
of its return arc. -/
theorem hasWinding_semicircleLoop (x u : ℂ) (hu : u ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    HasWinding (semicircleLoop x u) (x + u * (ε * Complex.I)) 1 := by
  obtain ⟨φ, hφ, hinc⟩ := hasWinding_diameterSemicircleLoop ε hε hε1
  refine ⟨⟨fun t => Complex.log u + φ t,
    continuous_const.add φ.continuous⟩, ?_, ?_⟩
  · intro t
    change Complex.exp (Complex.log u + φ t) = _
    rw [Complex.exp_add, Complex.exp_log hu, hφ, semicircleLoop_apply]
    ring
  · change (Complex.log u + φ 1) - (Complex.log u + φ 0) = _
    rw [show (Complex.log u + φ 1) - (Complex.log u + φ 0) = φ 1 - φ 0 by ring]
    exact hinc

/-- Helper toward Definition 1.1 / Definition 3.2: a point of an open
segment admits symmetric smaller diameters within that same segment. -/
theorem openSegment_small_symmetric_endpoints (a b x : ℂ)
    (hx : x ∈ openSegment ℝ a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      x - ε • (b - a) ∈ openSegment ℝ a b ∧
      x + ε • (b - a) ∈ openSegment ℝ a b := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨min t (1 - t), lt_min ht.1 (sub_pos.mpr ht.2), ?_⟩
  intro ε hε hεδ
  have hεt : ε < t := hεδ.trans_le (min_le_left _ _)
  have hεt' : ε < 1 - t := hεδ.trans_le (min_le_right _ _)
  constructor
  · have hmem := lineMap_mem_openSegment ℝ a b
      (show t - ε ∈ Set.Ioo (0 : ℝ) 1 from
        ⟨sub_pos.mpr hεt, by linarith only [ht.2, hε]⟩)
    convert hmem using 1
    simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
    push_cast
    ring
  · have hmem := lineMap_mem_openSegment ℝ a b
      (show t + ε ∈ Set.Ioo (0 : ℝ) 1 from
        ⟨add_pos ht.1 hε, by linarith only [hεt']⟩)
    convert hmem using 1
    simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
    push_cast
    ring

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)

/-- Helper toward Definition 1.1 / Definition 3.2: at every open-segment
contact of a bordering face, arbitrarily small semicircular return paths
have endpoints on the same segment, are injective, and have their entire
open image in that face. -/
theorem dartBorders_openSegment_leftSemicircle (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) (x : ℂ)
    (hx : x ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (x - ε • ((P.arc d).point (i + 1) - (P.arc d).point i) ∈
        openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) ∧
      (x + ε • ((P.arc d).point (i + 1) - (P.arc d).point i) ∈
        openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) ∧
      Function.Injective
        (leftSemicircle x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i))) ∧
      ∀ t : I, t ∈ openParams →
        leftSemicircle x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i)) t ∈
          F.val := by
  let u := (P.arc d).point (i + 1) - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_openSegment_left_halfDisk hvert d F hborder hi x hx
  obtain ⟨δseg, hδseg, hend⟩ := openSegment_small_symmetric_endpoints
    ((P.arc d).point i) ((P.arc d).point (i + 1)) x hx
  let δ := min δseg (r / (‖u‖ + 1))
  have hδ : 0 < δ := lt_min hδseg (div_pos hr (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hεu : ε • u ≠ 0 := smul_ne_zero hε.ne' hu
  obtain ⟨hleft, hright⟩ := hend ε hε (hεδ.trans_le (min_le_left _ _))
  refine ⟨hleft, hright, leftSemicircle_injective x (ε • u) hεu, ?_⟩
  intro t ht
  apply hhalf _
  · rw [Metric.mem_ball, leftSemicircle_dist, norm_smul, Real.norm_eq_abs,
      abs_of_pos hε]
    have he : ε * (‖u‖ + 1) < r :=
      (lt_div_iff₀ (by positivity)).mp (hεδ.trans_le (min_le_right _ _))
    nlinarith only [he, hε]
  · have hp := leftSemicircle_side_pos x (ε • u) hεu t ht
    have he : (star (ε • u) *
        (leftSemicircle x (ε • u) t - x)).im =
        ε * (star u * (leftSemicircle x (ε • u) t - x)).im := by
      rw [star_smul, star_trivial, smul_mul_assoc, Complex.smul_im, smul_eq_mul]
    rw [he] at hp
    exact ((mul_pos_iff.mp hp).resolve_right
      (fun h => (not_lt_of_gt hε) h.1)).2

/-- Helper toward Definition 1.1 / Definition 3.2: at an open-segment
contact, a semicircular return path lies in the bordering face, and points
of that face with winding number one accumulate at the contact. This is
the geometric local loop, before identifying it with `edgeSubarc`. -/
theorem dartBorders_openSegment_semicircleLoop (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) (x : ℂ)
    (hx : x ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ ε : ℝ, 0 < ε ∧
      (x - ε • ((P.arc d).point (i + 1) - (P.arc d).point i) ∈
        openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) ∧
      (x + ε • ((P.arc d).point (i + 1) - (P.arc d).point i) ∈
        openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) ∧
      Function.Injective
        (leftSemicircle x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i))) ∧
      (∀ t : I, t ∈ openParams →
        leftSemicircle x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i)) t ∈
          F.val) ∧
      x ∈ closure {w : ℂ | w ∈ F.val ∧
        HasWinding
          (semicircleLoop x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i)))
          w 1} := by
  let u := (P.arc d).point (i + 1) - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  obtain ⟨δ, hδ, hreturn⟩ :=
    P.dartBorders_openSegment_leftSemicircle hvert d F hborder hi x hx
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_openSegment_left_halfDisk hvert d F hborder hi x hx
  let ε := min (δ / 2) (r / (2 * (‖u‖ + 1)))
  have hε : 0 < ε := lt_min (by positivity) (div_pos hr (by positivity))
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith only [hδ])
  have hεr : ε * (2 * (‖u‖ + 1)) ≤ r :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let v := ε • u
  have hv : v ≠ 0 := smul_ne_zero hε.ne' hu
  have hvnorm : ‖v‖ = ε * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hvr : ‖v‖ < r := by
    rw [hvnorm]
    exact (mul_lt_mul_of_pos_left (by linarith only [norm_nonneg u]) hε).trans_le hεr
  obtain ⟨hleft, hright, hinj, hopen⟩ := hreturn ε hε hεδ
  refine ⟨ε, hε, hleft, hright, hinj, hopen, Metric.mem_closure_iff.mpr ?_⟩
  intro η hη
  let τ := min (1 / 2) (η / (2 * (‖v‖ + 1)))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hτ1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hτη : τ * (2 * (‖v‖ + 1)) ≤ η :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let w := x + v * (τ * Complex.I)
  have hwx : dist w x = τ * ‖v‖ := by
    rw [dist_eq_norm]
    change ‖x + v * (τ * Complex.I) - x‖ = _
    rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hτ, Complex.norm_I, mul_one, mul_comm]
  have hwF : w ∈ F.val := by
    apply hhalf _
    · rw [Metric.mem_ball, hwx]
      exact (mul_lt_of_lt_one_left (norm_pos_iff.mpr hv) hτ1).trans hvr
    · have he : star u * (w - x) =
          ((ε * τ : ℝ) : ℂ) * Complex.I * (star u * u) := by
        dsimp [w, v]
        push_cast
        ring
      rw [he, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        sub_zero, add_zero, mul_one, zero_add]
      exact mul_pos (mul_pos hε hτ) (Complex.normSq_pos.mpr hu)
  refine ⟨w, ⟨hwF, hasWinding_semicircleLoop x v hv τ hτ hτ1⟩, ?_⟩
  rw [dist_comm, hwx]
  exact (mul_lt_mul_of_pos_left (by linarith only [norm_nonneg v]) hτ).trans_le hτη

end PLDrawing























end DirectedDistances.PlanarMap

end
