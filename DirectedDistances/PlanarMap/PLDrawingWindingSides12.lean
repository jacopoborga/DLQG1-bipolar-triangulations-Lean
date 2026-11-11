/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides11

/-! # Winding sides at PL drawing bends

Helpers toward Definition 3.2. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace PLDrawing

/-- Helper toward Definition 3.2: the left local sector at an internal
bend belongs to the face bordering the dart. -/
theorem dartBorders_bend_left_sector_subset_face
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ S : Set ℂ, IsPreconnected S ∧ S ⊆ F.val ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ,
        0 < t → t < δ → 0 < ε → ε < δ →
        b + t • (-u + ε • (Complex.I * u)) ∈ S ∧
        b + t • (v + ε • (Complex.I * v)) ∈ S := by
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨S, hSpre, hSsafe, δ, hδ, hcorners⟩ :=
    P.bend_contact_side_sector hvert d hi 1 one_ne_zero
  let t := min (δ / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let a := (P.arc d).point i
  let x := b - t • u
  have hx : x ∈ openSegment ℝ a b := by
    rw [openSegment_eq_image']
    refine ⟨1 - t, ⟨by linarith, by linarith⟩, ?_⟩
    dsimp [x, u, b, a]
    push_cast
    ring
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_openSegment_left_halfDisk hvert d F hborder (by omega) x hx
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  let ε := min (δ / 2) (r / (2 * (t * ‖u‖ + 1)))
  have hε : 0 < ε := lt_min (half_pos hδ) (div_pos hr (by positivity))
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let y := b + t • (-u + ε • (Complex.I * u))
  have hyx : y - x = (t * ε) • (Complex.I * u) := by
    dsimp [y, x]
    push_cast
    ring
  have hyr : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm, hyx, norm_smul, Real.norm_eq_abs,
      abs_of_pos (mul_pos ht hε)]
    have hprod : ε * (2 * (t * ‖u‖ + 1)) ≤ r :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hnorm : ‖Complex.I * u‖ = ‖u‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [hnorm]
    nlinarith [norm_nonneg u]
  have hyside : 0 < (star u * (y - x)).im := by
    rw [hyx, mul_smul_comm, Complex.smul_im]
    have hn : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
    have hnormal : (star u * (Complex.I * u)).im = Complex.normSq u := by
      rw [show star u * (Complex.I * u) = Complex.I * (star u * u) by ring,
        Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      simp
    rw [hnormal]
    positivity
  have hyF : y ∈ F.val := hhalf y hyr hyside
  have hyS : y ∈ S := by
    simpa only [one_smul, y, u, b] using (hcorners t ε ht htδ hε hεδ).1
  have hSface : S ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hyF ⊢
    rw [connectedComponentIn_eq hyF]
    exact hSpre.subset_connectedComponentIn hyS hSsafe
  refine ⟨S, hSpre, hSface, δ, hδ, ?_⟩
  intro t' ε' ht' ht'δ hε' hε'δ
  simpa only [one_smul] using hcorners t' ε' ht' ht'δ hε' hε'δ

















end PLDrawing

end DirectedDistances.PlanarMap

end
