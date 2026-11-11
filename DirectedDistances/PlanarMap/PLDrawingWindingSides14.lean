/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides13

/-! # Left offsets at PL drawing bends

Helpers toward Definition 3.2. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Metric
open scoped Topology

namespace PLDrawing

/-- Helper toward Definition 3.2: uniformly small left offsets on both
segments incident to a bend belong to the face bordering the dart. -/
theorem dartBorders_bend_left_offsets_mem_face
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ,
      0 < t → t < δ → 0 < ε → ε < δ →
      b + t • (-u + ε • (Complex.I * u)) ∈ F.val ∧
      b + t • (v + ε • (Complex.I * v)) ∈ F.val := by
  obtain ⟨S, hSpre, hSface, δ, hδ, hcorners⟩ :=
    P.dartBorders_bend_left_sector_subset_face hvert d F hborder hi
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htδ hε hεδ
  exact ⟨hSface (hcorners t ε ht htδ hε hεδ).1,
    hSface (hcorners t ε ht htδ hε hεδ).2⟩

/-- Helper toward Definition 3.2: the left-offset points from the preceding
lemma accumulate at the bend while remaining in its bordering face. -/
theorem dartBorders_bend_left_offsets_accumulate
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    b ∈ closure {y : ℂ | y ∈ F.val ∧ ∃ t ε : ℝ,
      0 < t ∧ 0 < ε ∧ y = b + t • (-u + ε • (Complex.I * u))} ∧
    b ∈ closure {y : ℂ | y ∈ F.val ∧ ∃ t ε : ℝ,
      0 < t ∧ 0 < ε ∧ y = b + t • (v + ε • (Complex.I * v))} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨δ, hδ, hface⟩ :=
    P.dartBorders_bend_left_offsets_mem_face hvert d F hborder hi
  have hu : u ≠ 0 := by
    dsimp [u, b]
    exact sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  have hv : v ≠ 0 := by
    dsimp [v, b]
    exact sub_ne_zero.mpr ((P.arc_simple d).1 (i + 1) (by omega)).symm
  constructor
  · rw [Metric.mem_closure_iff]
    intro η hη
    let c := min (δ / 2) (min (1 / 2) (η / (4 * (‖u‖ + 1))))
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hcδ : c < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hc1 : c < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hcη : c ≤ η / (4 * (‖u‖ + 1)) := by
      dsimp [c]
      exact (min_le_right _ _).trans (min_le_right _ _)
    let y := b + c • (-u + c • (Complex.I * u))
    have hyF : y ∈ F.val := (hface c c hc hcδ hc hcδ).1
    have hySet : y ∈ {y : ℂ | y ∈ F.val ∧ ∃ t ε : ℝ,
        0 < t ∧ 0 < ε ∧ y = b + t • (-u + ε • (Complex.I * u))} := by
      exact ⟨hyF, c, c, hc, hc, rfl⟩
    refine ⟨y, hySet, ?_⟩
    rw [dist_comm, dist_eq_norm]
    change ‖b + c • (-u + c • (Complex.I * u)) - b‖ < η
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have hc1' : c ≤ 1 := le_of_lt hc1
    have hnorm : ‖-u + c • (Complex.I * u)‖ ≤ ‖u‖ + c * ‖u‖ := by
      calc
        ‖-u + c • (Complex.I * u)‖ ≤ ‖-u‖ + ‖c • (Complex.I * u)‖ := norm_add_le _ _
        _ = ‖u‖ + c * ‖u‖ := by
          rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
            norm_mul, Complex.norm_I, one_mul]
    have hsmall : c * ‖-u + c • (Complex.I * u)‖ ≤
        c * (‖u‖ + c * ‖u‖) := mul_le_mul_of_nonneg_left hnorm hc.le
    have hestimate : c * (‖u‖ + c * ‖u‖) ≤ 2 * c * ‖u‖ := by
      have hcNorm : c * ‖u‖ ≤ ‖u‖ :=
        by simpa using mul_le_mul_of_nonneg_right hc1' (norm_nonneg u)
      have hccNorm : c * (c * ‖u‖) ≤ c * ‖u‖ :=
        mul_le_mul_of_nonneg_left hcNorm hc.le
      nlinarith [hccNorm]
    have hηbound : 2 * c * ‖u‖ < η := by
      have hprod : c * (4 * (‖u‖ + 1)) ≤ η :=
        (le_div_iff₀ (by positivity : 0 < 4 * (‖u‖ + 1))).mp hcη
      nlinarith [norm_nonneg u, hc]
    exact lt_of_le_of_lt (hsmall.trans hestimate) hηbound
  · rw [Metric.mem_closure_iff]
    intro η hη
    let c := min (δ / 2) (min (1 / 2) (η / (4 * (‖v‖ + 1))))
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hcδ : c < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hc1 : c < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hcη : c ≤ η / (4 * (‖v‖ + 1)) := by
      dsimp [c]
      exact (min_le_right _ _).trans (min_le_right _ _)
    let y := b + c • (v + c • (Complex.I * v))
    have hyF : y ∈ F.val := (hface c c hc hcδ hc hcδ).2
    have hySet : y ∈ {y : ℂ | y ∈ F.val ∧ ∃ t ε : ℝ,
        0 < t ∧ 0 < ε ∧ y = b + t • (v + ε • (Complex.I * v))} := by
      exact ⟨hyF, c, c, hc, hc, rfl⟩
    refine ⟨y, hySet, ?_⟩
    rw [dist_comm, dist_eq_norm]
    change ‖b + c • (v + c • (Complex.I * v)) - b‖ < η
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have hc1' : c ≤ 1 := le_of_lt hc1
    have hnorm : ‖v + c • (Complex.I * v)‖ ≤ ‖v‖ + c * ‖v‖ := by
      calc
        ‖v + c • (Complex.I * v)‖ ≤ ‖v‖ + ‖c • (Complex.I * v)‖ := norm_add_le _ _
        _ = ‖v‖ + c * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc,
            norm_mul, Complex.norm_I, one_mul]
    have hsmall : c * ‖v + c • (Complex.I * v)‖ ≤
        c * (‖v‖ + c * ‖v‖) := mul_le_mul_of_nonneg_left hnorm hc.le
    have hestimate : c * (‖v‖ + c * ‖v‖) ≤ 2 * c * ‖v‖ := by
      have hcNorm : c * ‖v‖ ≤ ‖v‖ :=
        by simpa using mul_le_mul_of_nonneg_right hc1' (norm_nonneg v)
      have hccNorm : c * (c * ‖v‖) ≤ c * ‖v‖ :=
        mul_le_mul_of_nonneg_left hcNorm hc.le
      nlinarith [hccNorm]
    have hηbound : 2 * c * ‖v‖ < η := by
      have hprod : c * (4 * (‖v‖ + 1)) ≤ η :=
        (le_div_iff₀ (by positivity : 0 < 4 * (‖v‖ + 1))).mp hcη
      nlinarith [norm_nonneg v, hc]
    exact lt_of_le_of_lt (hsmall.trans hestimate) hηbound















end PLDrawing

end DirectedDistances.PlanarMap

end
