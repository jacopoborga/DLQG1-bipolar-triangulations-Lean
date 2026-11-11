/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides14
public import DirectedDistances.PlanarMap.HasWindingTransfer

/-! # Paired left offsets at PL drawing bends -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace PLDrawing

/-- Helper toward Definition 3.2: arbitrarily close to an internal bend,
the bordering face contains a left offset on each incident segment at once. -/
theorem dartBorders_bend_left_offsets_pair_close
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η →
      ∃ t ε : ℝ, 0 < t ∧ t < δ ∧ 0 < ε ∧ ε < δ ∧
        b + t • (-u + ε • (Complex.I * u)) ∈ F.val ∧
        b + t • (v + ε • (Complex.I * v)) ∈ F.val ∧
        dist (b + t • (-u + ε • (Complex.I * u))) b < η ∧
        dist (b + t • (v + ε • (Complex.I * v))) b < η := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨δ, hδ, hface⟩ :=
    P.dartBorders_bend_left_offsets_mem_face hvert d F hborder hi
  refine ⟨δ, hδ, ?_⟩
  intro η hη
  let c := min (δ / 2) (min (1 / 2) (η / (4 * (‖u‖ + ‖v‖ + 1))))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hcδ : c < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hcη : c ≤ η / (4 * (‖u‖ + ‖v‖ + 1)) := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hnormu : ‖-u + c • (Complex.I * u)‖ ≤ ‖u‖ + c * ‖u‖ := by
    calc
      ‖-u + c • (Complex.I * u)‖ ≤ ‖-u‖ + ‖c • (Complex.I * u)‖ := norm_add_le _ _
      _ = ‖u‖ + c * ‖u‖ := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
          norm_mul, Complex.norm_I, one_mul]
  have hnormv : ‖v + c • (Complex.I * v)‖ ≤ ‖v‖ + c * ‖v‖ := by
    calc
      ‖v + c • (Complex.I * v)‖ ≤ ‖v‖ + ‖c • (Complex.I * v)‖ := norm_add_le _ _
      _ = ‖v‖ + c * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc,
          norm_mul, Complex.norm_I, one_mul]
  have hprod : c * (4 * (‖u‖ + ‖v‖ + 1)) ≤ η :=
    (le_div_iff₀ (by positivity : 0 < 4 * (‖u‖ + ‖v‖ + 1))).mp hcη
  have hboundu : c * (‖u‖ + c * ‖u‖) ≤ 2 * c * ‖u‖ := by
    have hcNorm : c * ‖u‖ ≤ ‖u‖ := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hc1) (norm_nonneg u)
    have hccNorm : c * (c * ‖u‖) ≤ c * ‖u‖ :=
      mul_le_mul_of_nonneg_left hcNorm hc.le
    nlinarith [hccNorm]
  have hboundv : c * (‖v‖ + c * ‖v‖) ≤ 2 * c * ‖v‖ := by
    have hcNorm : c * ‖v‖ ≤ ‖v‖ := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hc1) (norm_nonneg v)
    have hccNorm : c * (c * ‖v‖) ≤ c * ‖v‖ :=
      mul_le_mul_of_nonneg_left hcNorm hc.le
    nlinarith [hccNorm]
  have hηu : 2 * c * ‖u‖ < η := by
    have hlt : 2 * c * ‖u‖ < c * (4 * (‖u‖ + ‖v‖ + 1)) := by
      nlinarith [norm_nonneg u, norm_nonneg v, hc]
    exact hlt.trans_le hprod
  have hηv : 2 * c * ‖v‖ < η := by
    have hlt : 2 * c * ‖v‖ < c * (4 * (‖u‖ + ‖v‖ + 1)) := by
      nlinarith [norm_nonneg u, norm_nonneg v, hc]
    exact hlt.trans_le hprod
  have hdistu : dist (b + c • (-u + c • (Complex.I * u))) b < η := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have hsmall : c * ‖-u + c • (Complex.I * u)‖ ≤
        c * (‖u‖ + c * ‖u‖) := mul_le_mul_of_nonneg_left hnormu hc.le
    exact (hsmall.trans hboundu).trans_lt hηu
  have hdistv : dist (b + c • (v + c • (Complex.I * v))) b < η := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have hsmall : c * ‖v + c • (Complex.I * v)‖ ≤
        c * (‖v‖ + c * ‖v‖) := mul_le_mul_of_nonneg_left hnormv hc.le
    exact (hsmall.trans hboundv).trans_lt hηv
  have hpoints := hface c c hc hcδ hc hcδ
  exact ⟨c, c, hc, hcδ, hc, hcδ, hpoints.1, hpoints.2, hdistu, hdistv⟩



















end PLDrawing

end DirectedDistances.PlanarMap

end
