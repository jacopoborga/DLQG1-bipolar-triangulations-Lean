/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.HasWindingTransfer
public import Mathlib.Analysis.Convex.PathConnected

/-! # Logarithmic lifts along triangle edges

Helper toward Definition 3.2. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology ComplexConjugate

/-- Helper toward Definition 3.2: positive oriented area gives a positive
imaginary part for the quotient of the two vectors. -/
theorem im_div_pos_of_conj_mul_im_pos {u v : ℂ}
    (h : 0 < (conj u * v).im) : 0 < (v / u).im := by
  have hu : u ≠ 0 := by
    intro hu
    simp [hu] at h
  rw [Complex.div_im, ← sub_div]
  apply div_pos _ (Complex.normSq_pos.mpr hu)
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h
  nlinarith only [h]

/-- Helper toward Definition 3.2: the quotient along an oriented segment
lies in the principal logarithm's slit plane, including both endpoints. -/
theorem segment_ratio_mem_slitPlane {p q w : ℂ}
    (h : 0 < (conj (p - w) * (q - w)).im) (u : I) :
    ((Path.segment p q) u - w) / (p - w) ∈ Complex.slitPlane := by
  have hp : p - w ≠ 0 := by
    intro hp
    simp [hp] at h
  have hi := im_div_pos_of_conj_mul_im_pos h
  have heq : ((Path.segment p q) u - w) / (p - w) =
      (1 - (u : ℂ)) + (u : ℂ) * ((q - w) / (p - w)) := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, Complex.real_smul,
      Complex.ofReal_sub, Complex.ofReal_one]
    field_simp [hp]
    ring
  rw [heq, Complex.mem_slitPlane_iff]
  by_cases hu : (u : ℝ) = 0
  · left
    simp [hu]
  · right
    have hu' : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hu)
    have : 0 < ((1 - (u : ℂ)) + (u : ℂ) * ((q - w) / (p - w))).im := by
      simpa using mul_pos hu' hi
    exact ne_of_gt this

/-- Helper toward Definition 3.2: the relative principal logarithm along
an oriented segment is continuous on the entire closed parameter interval. -/
theorem continuous_log_segment_ratio {p q w : ℂ}
    (h : 0 < (conj (p - w) * (q - w)).im) :
    Continuous (fun u : I => Complex.log (((Path.segment p q) u - w) / (p - w))) := by
  exact ((Path.segment p q).continuous.sub continuous_const |>.div_const (p - w)).clog
    (segment_ratio_mem_slitPlane h)

/-- Helper toward Definition 3.2: an oriented segment admits a logarithmic
lift starting at any prescribed logarithm of its initial translated point. -/
theorem exists_segment_log_lift {p q w A : ℂ}
    (h : 0 < (conj (p - w) * (q - w)).im)
    (hA : Complex.exp A = p - w) :
    ∃ α : Path A (A + Complex.log ((q - w) / (p - w))),
      ∀ u : I, Complex.exp (α u) = (Path.segment p q) u - w := by
  have hp : p - w ≠ 0 := by
    intro hp
    simp [hp] at h
  let f : C(I, ℂ) := ⟨fun u => A + Complex.log (((Path.segment p q) u - w) / (p - w)),
    continuous_const.add (continuous_log_segment_ratio h)⟩
  have hf0 : f 0 = A := by simp [f, hp]
  have hf1 : f 1 = A + Complex.log ((q - w) / (p - w)) := by simp [f]
  refine ⟨⟨f, hf0, hf1⟩, ?_⟩
  intro u
  change Complex.exp (A + Complex.log (((Path.segment p q) u - w) / (p - w))) = _
  rw [Complex.exp_add, hA,
    Complex.exp_log (Complex.slitPlane_ne_zero (segment_ratio_mem_slitPlane h u))]
  exact mul_div_cancel₀ _ hp

/-- Helper toward Definition 3.2: exponential lifts glue with the same
parameterization as concatenation of their underlying paths. -/
theorem exp_trans_of_exp_eq {x y z a b c w : ℂ}
    {α : Path x y} {β : Path y z} {P : Path a b} {Q : Path b c}
    (hα : ∀ u : I, Complex.exp (α u) = P u - w)
    (hβ : ∀ u : I, Complex.exp (β u) = Q u - w) :
    ∀ u : I, Complex.exp ((α.trans β) u) = (P.trans Q) u - w := by
  intro u
  rw [Path.trans_apply α β u, Path.trans_apply P Q u]
  by_cases hu : (u : ℝ) ≤ 1 / 2
  · simp only [dite_eq_left hu]
    exact hα _
  · simp only [dite_eq_right hu]
    exact hβ _

/-- Helper toward Definition 3.2: each vertex pair of a counterclockwise
triangle subtends a positive oriented angle at a strictly interior point. -/
theorem ccw_triangle_interior_cross_pos {a b c w : ℂ} {s t : ℝ}
    (hw : w = a + (s : ℂ) * (b - a) + (t : ℂ) * (c - a))
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (horient : 0 < (conj (b - a) * (c - a)).im) :
    0 < (conj (a - w) * (b - w)).im ∧
      0 < (conj (b - w) * (c - w)).im ∧
      0 < (conj (c - w) * (a - w)).im := by
  have hab : (conj (a - w) * (b - w)).im =
      t * (conj (b - a) * (c - a)).im := by
    rw [hw]
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hbc : (conj (b - w) * (c - w)).im =
      (1 - s - t) * (conj (b - a) * (c - a)).im := by
    rw [hw]
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hca : (conj (c - w) * (a - w)).im =
      s * (conj (b - a) * (c - a)).im := by
    rw [hw]
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hab, hbc, hca]
  exact ⟨mul_pos ht horient, mul_pos (by linarith only [hst]) horient,
    mul_pos hs horient⟩

/-- Helper toward Definition 3.2: a vector in the upper half plane has a
principal logarithm with imaginary part strictly between zero and π. -/
theorem log_im_mem_Ioo_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    (Complex.log z).im ∈ Set.Ioo 0 Real.pi := by
  rw [Complex.log_im]
  constructor
  · have hn : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hz.le
    have hne : z.arg ≠ 0 := by
      intro hzero
      exact (ne_of_gt hz) (Complex.arg_eq_zero_iff.mp hzero).2
    exact lt_of_le_of_ne hn (Ne.symm hne)
  · exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hz))

/-- Helper toward Definition 3.2: the three positive principal-log angle
increments around a triangle sum to exactly `2 * π * I`. -/
theorem triangle_log_ratio_sum {u v r : ℂ}
    (huv : 0 < (conj u * v).im)
    (hvr : 0 < (conj v * r).im)
    (hru : 0 < (conj r * u).im) :
    Complex.log (v / u) + Complex.log (r / v) + Complex.log (u / r) =
      2 * Real.pi * Complex.I := by
  have hu : u ≠ 0 := by intro h; simp [h] at huv
  have hv : v ≠ 0 := by intro h; simp [h] at hvr
  have hr : r ≠ 0 := by intro h; simp [h] at hru
  have h₁ := log_im_mem_Ioo_of_im_pos (im_div_pos_of_conj_mul_im_pos huv)
  have h₂ := log_im_mem_Ioo_of_im_pos (im_div_pos_of_conj_mul_im_pos hvr)
  have h₃ := log_im_mem_Ioo_of_im_pos (im_div_pos_of_conj_mul_im_pos hru)
  have he : Complex.exp (Complex.log (v / u) + Complex.log (r / v) +
      Complex.log (u / r)) = 1 := by
    rw [Complex.exp_add, Complex.exp_add,
      Complex.exp_log (div_ne_zero hv hu), Complex.exp_log (div_ne_zero hr hv),
      Complex.exp_log (div_ne_zero hu hr)]
    field_simp
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp he
  have him := congrArg Complex.im hk
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, mul_one, add_zero,
    Complex.re_ofNat, Complex.im_ofNat, sub_zero] at him
  have hkpos : (0 : ℝ) < k := by
    nlinarith only [him, h₁.1, h₂.1, h₃.1, Real.pi_pos]
  have hklt : (k : ℝ) < 2 := by
    nlinarith only [him, h₁.2, h₂.2, h₃.2, Real.pi_pos]
  have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hklt' : k < (2 : ℤ) := by exact_mod_cast hklt
  have hkone : k = 1 := by omega
  simpa only [hkone, Int.cast_one, one_mul] using hk

/-- Helper toward Definition 3.2: the counterclockwise boundary of a
nondegenerate triangle has winding one about every strictly interior point. -/
theorem hasWinding_ccw_triangle_loop {a b c w : ℂ} {s t : ℝ}
    (hw : w = a + (s : ℂ) * (b - a) + (t : ℂ) * (c - a))
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (horient : 0 < (conj (b - a) * (c - a)).im) :
    HasWinding ((Path.segment a b).trans
      ((Path.segment b c).trans (Path.segment c a))) w 1 := by
  obtain ⟨hab, hbc, hca⟩ := ccw_triangle_interior_cross_pos hw hs ht hst horient
  have ha : a - w ≠ 0 := by intro h; simp [h] at hab
  let A := Complex.log (a - w)
  let B := A + Complex.log ((b - w) / (a - w))
  let C := B + Complex.log ((c - w) / (b - w))
  have hA : Complex.exp A = a - w := Complex.exp_log ha
  obtain ⟨α, hα⟩ := exists_segment_log_lift hab hA
  have hB : Complex.exp B = b - w := by
    simpa only [Path.target] using hα 1
  obtain ⟨β, hβ⟩ := exists_segment_log_lift hbc hB
  have hC : Complex.exp C = c - w := by
    simpa only [Path.target] using hβ 1
  obtain ⟨γ, hγ⟩ := exists_segment_log_lift hca hC
  let Ψ : C(I, ℂ) := (α.trans (β.trans γ)).toContinuousMap
  refine ⟨Ψ, exp_trans_of_exp_eq hα (exp_trans_of_exp_eq hβ hγ), ?_⟩
  change (α.trans (β.trans γ)) 1 - (α.trans (β.trans γ)) 0 = _
  simp only [Path.target, Path.source, Int.cast_one, mul_one]
  calc
    C + Complex.log ((a - w) / (c - w)) - A =
        Complex.log ((b - w) / (a - w)) + Complex.log ((c - w) / (b - w)) +
          Complex.log ((a - w) / (c - w)) := by dsimp [C, B]; ring
    _ = 2 * Real.pi * Complex.I := triangle_log_ratio_sum hab hbc hca

end DirectedDistances.PlanarMap

end
