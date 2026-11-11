/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass7
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedEquiv
import Mathlib.Tactic.FunProp

/-! Helper toward Definition 3.8 (consumer).

# Vertical seam reparameterizations -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8 (consumer): the vertical shear carrying the
seam graph of `f` to that of `g`, with the horizontal coordinate fixed. -/
@[expose] def uibhbotVerticalSeamTransfer (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) : ℂ ≃ₜ ℂ where
  toFun z := ⟨z.re, z.im - f z.re + g z.re⟩
  invFun z := ⟨z.re, z.im - g z.re + f z.re⟩
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv z := by
    apply Complex.ext <;> simp
  continuous_toFun := by
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  continuous_invFun := by
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop

/-- Helper toward Definition 3.8 (consumer): constant vertical translation
leaves pairwise complex differences unchanged. -/
theorem uibhbotVerticalShift_sub (c : ℝ) (z w : ℂ) :
    uibhbotVerticalSeamTransfer (fun _ => 0) (fun _ => c)
        continuous_const continuous_const z -
      uibhbotVerticalSeamTransfer (fun _ => 0) (fun _ => c)
        continuous_const continuous_const w = z - w := by
  apply Complex.ext <;> simp [uibhbotVerticalSeamTransfer]

/-- Helper toward Definition 3.8 (consumer): the shear carries every closed
strip of fixed vertical width above `f` to the corresponding strip above `g`. -/
theorem uibhbotVerticalSeamTransfer_maps_closedStrip
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (h : ℝ) :
    uibhbotVerticalSeamTransfer f g hf hg ''
        {z : ℂ | f z.re ≤ z.im ∧ z.im ≤ f z.re + h} =
      {z : ℂ | g z.re ≤ z.im ∧ z.im ≤ g z.re + h} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hlo, hhi⟩, rfl⟩
    change g w.re ≤ w.im - f w.re + g w.re ∧
      w.im - f w.re + g w.re ≤ g w.re + h
    constructor <;> linarith
  · intro hz
    rcases hz with ⟨hlo, hhi⟩
    refine ⟨(uibhbotVerticalSeamTransfer f g hf hg).symm z, ?_, ?_⟩
    · change f z.re ≤ z.im - g z.re + f z.re ∧
        z.im - g z.re + f z.re ≤ f z.re + h
      constructor <;> linarith
    · exact (uibhbotVerticalSeamTransfer f g hf hg).apply_symm_apply z

/-- Helper toward Definition 3.8 (consumer): vertical translation preserves
winding numbers, hence is orientation-preserving in the project's sense. -/
theorem uibhbotVerticalShift_orientationPreserving (c : ℝ) :
    OrientationPreserving (uibhbotVerticalSeamTransfer (fun _ => 0)
      (fun _ => c) continuous_const continuous_const) := by
  intro z L w hw n
  constructor
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ, ?_, hinc⟩
    intro t
    change Complex.exp (φ t) =
      uibhbotVerticalSeamTransfer (fun _ => 0) (fun _ => c)
        continuous_const continuous_const (L t) -
      uibhbotVerticalSeamTransfer (fun _ => 0) (fun _ => c)
        continuous_const continuous_const w
    simpa only [uibhbotVerticalShift_sub] using hφ t
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ, ?_, hinc⟩
    intro t
    have ht := hφ t
    change Complex.exp (φ t) =
      uibhbotVerticalSeamTransfer (fun _ => 0) (fun _ => c)
        continuous_const continuous_const (L t) -
      uibhbotVerticalSeamTransfer (fun _ => 0) (fun _ => c)
        continuous_const continuous_const w at ht
    simpa only [uibhbotVerticalShift_sub] using ht

/-- Helper toward Definition 3.8 (consumer): translation is strictly
increasing in the vertical coordinate on each vertical fiber. -/
theorem uibhbotVerticalSeamTransfer_strictMono_fiber
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (x : ℝ) :
    StrictMono (fun y : ℝ =>
      (uibhbotVerticalSeamTransfer f g hf hg ⟨x, y⟩).im) := by
  intro y₁ y₂ hy
  change y₁ - f x + g x < y₂ - f x + g x
  linarith






































end DirectedDistances.PaperProofs.Section5

end

