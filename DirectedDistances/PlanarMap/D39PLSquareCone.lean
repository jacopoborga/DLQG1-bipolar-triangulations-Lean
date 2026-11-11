/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLFaceExtension4

/-! Helpers toward Proposition 5.16: radial coordinates for the enclosing square. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology

/-- Helper toward Proposition 5.16: the coordinate supremum norm on the plane. -/
def supNormC (z : ℂ) : ℝ := max |z.re| |z.im|

/-- Helper toward Proposition 5.16: nonnegative real scaling is homogeneous for the coordinate supremum norm. -/
theorem supNormC_smul_of_nonneg (t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    supNormC (t • z) = t * supNormC z := by
  simp only [supNormC, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    abs_mul, abs_of_nonneg ht]
  have hm (a b : ℝ) : max (t * a) (t * b) = t * max a b := by
    by_cases h : a ≤ b
    · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h ht)]
    · have h' : b ≤ a := le_of_not_gt (fun hlt => h hlt.le)
      rw [max_eq_left h', max_eq_left (mul_le_mul_of_nonneg_left h' ht)]
  exact hm _ _

/-- Helper toward Proposition 5.16: the coordinate supremum norm vanishes exactly at zero. -/
theorem supNormC_eq_zero_iff (z : ℂ) : supNormC z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hre : |z.re| = 0 := by
      apply le_antisymm
      · calc
          |z.re| ≤ max |z.re| |z.im| := le_max_left _ _
          _ = 0 := hz
      · exact abs_nonneg _
    have him : |z.im| = 0 := by
      apply le_antisymm
      · calc
          |z.im| ≤ max |z.re| |z.im| := le_max_right _ _
          _ = 0 := hz
      · exact abs_nonneg _
    exact Complex.ext (abs_eq_zero.mp hre) (abs_eq_zero.mp him)
  · rintro rfl
    simp [supNormC]

/-- Helper toward Proposition 5.16: the coordinate supremum norm is continuous. -/
theorem continuous_supNormC : Continuous (fun z : ℂ => supNormC z) := by
  exact (continuous_abs.comp Complex.continuous_re).max
    (continuous_abs.comp Complex.continuous_im)

namespace Polyline

/-- Helper toward Proposition 5.16: the enclosing square is the level set of the coordinate supremum norm. -/
theorem enclosingSquare_image_eq_supNormC (R : ℝ) (hR : 0 < R) :
    (enclosingSquare R).image = {z : ℂ | supNormC z = R} := by
  ext z
  rw [mem_enclosingSquare_image_iff R hR z]
  constructor
  · rintro ⟨⟨hre₁, hre₂⟩, ⟨him₁, him₂⟩, hside⟩
    have hreb : |z.re| ≤ R := abs_le.mpr ⟨hre₁, hre₂⟩
    have himb : |z.im| ≤ R := abs_le.mpr ⟨him₁, him₂⟩
    rcases hside with h | h | h | h
    · have habs : |z.re| = R := by
        rw [h, abs_of_nonpos (by linarith only [hR] : -R ≤ 0)]
        simp only [neg_neg]
      change max |z.re| |z.im| = R
      rw [habs, max_eq_left himb]
    · have habs : |z.re| = R := by
        rw [h, abs_of_nonneg (by linarith only [hR] : 0 ≤ R)]
      change max |z.re| |z.im| = R
      rw [habs, max_eq_left himb]
    · have habs : |z.im| = R := by
        rw [h, abs_of_nonpos (by linarith only [hR] : -R ≤ 0)]
        simp only [neg_neg]
      change max |z.re| |z.im| = R
      rw [habs, max_eq_right hreb]
    · have habs : |z.im| = R := by
        rw [h, abs_of_nonneg (by linarith only [hR] : 0 ≤ R)]
      change max |z.re| |z.im| = R
      rw [habs, max_eq_right hreb]
  · intro hz
    change max |z.re| |z.im| = R at hz
    have hre : |z.re| ≤ R := by rw [← hz]; exact le_max_left _ _
    have him : |z.im| ≤ R := by rw [← hz]; exact le_max_right _ _
    have hc := abs_le.mp hre
    have hd := abs_le.mp him
    have hside : |z.re| = R ∨ |z.im| = R := by
      rcases max_eq_iff.mp hz with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    refine ⟨⟨hc.1, hc.2⟩, ⟨hd.1, hd.2⟩, ?_⟩
    rcases hside with h | h
    · rcases (abs_eq hR.le).mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · rcases (abs_eq hR.le).mp h with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))

/-- Helper toward Proposition 5.16: the closed outside of the enclosing square is the closed coordinate exterior. -/
theorem enclosingSquare_closure_outside_eq_supNormC_ge (R : ℝ) (hR : 0 < R) :
    closure (enclosingSquare R).outside = {z : ℂ | R ≤ supNormC z} := by
  have hc := enclosingSquare_isCyclicSimple R hR
  rw [(enclosingSquare R).closure_outside_eq_union_image_cyclic hc]
  ext z
  constructor
  · rintro (hz | hz)
    · change z ∉ (enclosingSquare R).image ∧ (enclosingSquare R).angleSum z = 0 at hz
      have hnoinside : z ∉ (enclosingSquare R).inside := by
        intro hi
        exact (Set.disjoint_left.mp (disjoint_inside_outside (enclosingSquare R))) hi hz
      by_contra hn
      have hsmall : supNormC z < R := lt_of_not_ge hn
      have hi : z ∈ (enclosingSquare R).inside := by
        rw [enclosingSquare_inside R hR]
        simpa [supNormC, max_lt_iff, abs_lt] using hsmall
      exact hnoinside hi
    · have hz' := hz
      rw [enclosingSquare_image_eq_supNormC R hR] at hz'
      change supNormC z = R at hz'
      exact hz'.symm.le
  · intro hz
    by_cases heq : supNormC z = R
    · right
      rw [enclosingSquare_image_eq_supNormC R hR]
      exact heq
    · have hgt : R < supNormC z := lt_of_le_of_ne hz (Ne.symm heq)
      have hout : z ∈ (enclosingSquare R).outside := by
        have hnot : z ∉ (enclosingSquare R).image := by
          intro h
          rw [enclosingSquare_image_eq_supNormC R hR] at h
          change supNormC z = R at h
          exact (ne_of_gt hgt) h
        have hzpart := (inside_union_outside (enclosingSquare R)).ge hnot
        rcases hzpart with hi | ho
        · have hinside := hi
          rw [enclosingSquare_inside R hR] at hinside
          have hsmall : supNormC z < R := by
            simpa [supNormC, max_lt_iff, abs_lt] using hinside
          exact False.elim ((not_lt_of_ge (le_of_lt hgt)) hsmall)
        · exact ho
      exact Or.inl hout

/-- Helper toward Proposition 5.16: the open outside is the strict coordinate exterior. -/
theorem enclosingSquare_outside_eq_supNormC_gt (R : ℝ) (hR : 0 < R) :
    (enclosingSquare R).outside = {z : ℂ | R < supNormC z} := by
  ext z
  have hclosed := enclosingSquare_closure_outside_eq_supNormC_ge R hR
  have himage := enclosingSquare_image_eq_supNormC R hR
  constructor
  · intro hz
    have hzcl : z ∈ closure (enclosingSquare R).outside := subset_closure hz
    rw [hclosed] at hzcl
    change R ≤ supNormC z at hzcl
    have hnot : z ∉ (enclosingSquare R).image := hz.1
    have hneq : supNormC z ≠ R := by
      intro heq
      apply hnot
      rw [himage]
      exact heq
    exact lt_of_le_of_ne hzcl (Ne.symm hneq)
  · intro hz
    change R < supNormC z at hz
    have hzcl : z ∈ closure (enclosingSquare R).outside := by
      rw [hclosed]
      exact hz.le
    have hnotimage : z ∉ (enclosingSquare R).image := by
      intro heq
      rw [himage] at heq
      change supNormC z = R at heq
      exact (ne_of_gt hz) heq
    rw [closure_outside_eq_union_image_cyclic (enclosingSquare R)
      (enclosingSquare_isCyclicSimple R hR)] at hzcl
    rcases hzcl with hout | him
    · exact hout
    · exact False.elim (hnotimage him)









































end Polyline
end DirectedDistances.PlanarMap
