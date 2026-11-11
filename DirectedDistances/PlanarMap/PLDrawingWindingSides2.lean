/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides
public import DirectedDistances.PlanarMap.GeneralPlaneMapSideReversal

/- # Winding sides on PL drawings with no isolated vertices

Helpers toward Definition 1.1 / Definition 3.2

Reversal and endpoint-cast transfer are proved below. Dart-vertex
surjectivity also gives closure incidence at every path parameter and a
left half-disk at each open segment point. The chord-and-winding conclusion
These helpers do not establish winding-side multiplicity or degree. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Definition 1.1 / Definition 3.2: reversal interchanges
the winding-side tests, with complementary interior parameters. -/
theorem leftAtOn_path_symm_iff_rightAtOn {x y : ℂ} (F : Set ℂ)
    (γ : Path x y) (s s' : {t : I // t ∈ openParams})
    (hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1) :
    LeftAtOn F γ.symm s' ↔ RightAtOn F γ s := by
  constructor
  · exact leftAtOn_symm_to_rightAtOn F γ s s' hcomp
  · exact rightAtOn_to_leftAtOn_symm F γ s s' hcomp

/-- Helper toward Definition 1.1 / Definition 3.2: endpoint casts do
not change the left winding-side test. -/
theorem leftAtOn_cast_iff {x y x' y' : ℂ} (F : Set ℂ) (γ : Path x y)
    (hx : x' = x) (hy : y' = y) (s : {t : I // t ∈ openParams}) :
    LeftAtOn F (γ.cast hx hy) s ↔ LeftAtOn F γ s := by
  subst x'
  subst y'
  rfl

/-- Helper toward Definition 1.1 / Definition 3.2: endpoint casts do
not change the right winding-side test. -/
theorem rightAtOn_cast_iff {x y x' y' : ℂ} (F : Set ℂ) (γ : Path x y)
    (hx : x' = x) (hy : y' = y) (s : {t : I // t ∈ openParams}) :
    RightAtOn F (γ.cast hx hy) s ↔ RightAtOn F γ s := by
  subst x'
  subst y'
  rfl

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)

/-- Helper toward Definition 1.1 / Definition 3.2: without isolated
vertices, a bordering face accumulates at every interior path parameter. -/
theorem dartBorders_toPath_mem_closure (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) :
    (P.arc d).toPath s.val ∈ closure F.val := by
  apply P.dartBorders_arc_subset_closure hvert d F hborder
  rw [← Polyline.range_toPath]
  exact Set.mem_range_self s.val

/-- Helper toward Definition 1.1 / Definition 3.2: at an open segment
point, a bordering face contains a full sufficiently small left half-disk.
The radius and the side identification are proved from the drawing. -/
theorem dartBorders_openSegment_left_halfDisk (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) (q : ℂ)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball q r,
      0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - q)).im →
        y ∈ F.val := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨r, hr, hlocal⟩ := P.openSegment_contact_local_image hvert d hi hq
  let t := r / (4 * (‖u‖ + 1))
  have ht : 0 < t := div_pos hr (by positivity)
  have htprod : t * (4 * (‖u‖ + 1)) = r := div_mul_cancel₀ r (by positivity)
  have hsmall : t * ‖u‖ < r / 2 := by nlinarith only [htprod, ht, hnu]
  let z := q + t • (Complex.I * u)
  have hzq : dist z q = t * ‖u‖ := by
    rw [dist_eq_norm]
    change ‖q + t • (Complex.I * u) - q‖ = _
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      norm_mul, Complex.norm_I, one_mul]
  have hzqpos : 0 < dist z q := hzq ▸ mul_pos ht hnu
  have hnormal : (star u * (Complex.I * u)).im = Complex.normSq u := by
    rw [show star u * (Complex.I * u) = Complex.I * (star u * u) by ring,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp
  have hmin : ∀ y ∈ P.image, dist z q ≤ dist z y := by
    intro y hy
    by_cases hyr : y ∈ Metric.ball q r
    · have hyseg := hlocal y hyr hy
      have hside := segment_contact_side_eq_zero a b q y
        (openSegment_subset_segment ℝ a b hq) hyseg
      have him : (star u * (z - y)).im = t * Complex.normSq u := by
        have he : z - y = t • (Complex.I * u) - (y - q) := by dsimp [z]; module
        rw [he, mul_sub, Complex.sub_im, mul_smul_comm, Complex.smul_im]
        change t * (star u * (Complex.I * u)).im - (star u * (y - q)).im = _
        rw [hnormal, hside, sub_zero]
      have hb := Complex.im_le_norm (star u * (z - y))
      rw [him, norm_mul, norm_star, Complex.normSq_eq_norm_sq] at hb
      rw [hzq, dist_eq_norm]
      nlinarith only [hb, hnu]
    · have hry : r ≤ dist q y := by
        simpa only [Metric.mem_ball, dist_comm, not_lt] using hyr
      have htri := dist_triangle q z y
      rw [dist_comm q z, hzq] at htri
      rw [hzq]
      linarith only [hry, htri, hsmall]
  have hznot : z ∉ P.image := by
    intro hz
    have hm := hmin z hz
    rw [dist_self] at hm
    exact (not_le_of_gt hzqpos) hm
  obtain ⟨K, hzK⟩ := (P.faces_cover_compl z).mpr hznot
  have hball : Metric.ball z (dist z q) ⊆ K.val := by
    have hsafe : Metric.ball z (dist z q) ⊆ P.imageᶜ := by
      intro y hy hym
      exact (not_lt_of_ge (hmin y hym)) (by
        simpa only [Metric.mem_ball, dist_comm] using hy)
    obtain ⟨x, _, hK⟩ := K.property
    rw [hK] at hzK ⊢
    rw [connectedComponentIn_eq hzK]
    exact (convex_ball z (dist z q)).isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self hzqpos) hsafe
  have hpos : 0 < (star u * (z - q)).im := by
    have he : z - q = t • (Complex.I * u) := by dsimp [z]; abel
    rw [he, mul_smul_comm, Complex.smul_im, hnormal]
    exact mul_pos ht (Complex.normSq_pos.mpr hu)
  have hdK := P.face_nearest_openSegment_dartBorders_of_pos hvert K z q d hi hq
    (dist_pos.mp hzqpos) hball hmin hpos
  have hKF : K = F := P.dartBorders_face_unique d K F hdK hborder
  obtain ⟨r', hr', hhalf⟩ := P.face_nearest_openSegment_halfDisk hvert K z q d hi hq
    (dist_pos.mp hzqpos) hball hmin
  refine ⟨r', hr', ?_⟩
  intro y hy hyside
  rw [← hKF]
  exact hhalf y hy (mul_pos hpos hyside)

/-- Helper toward Definition 1.1 / Definition 3.2: the left winding-side
test on a stored geometric edge is exactly the test on its selected dart. -/
theorem toPlaneGraphDrawing_leftAtOn_iff (e : P.GeometricEdge)
    (F : P.toPlaneGraphDrawing.Face) (s : {t : I // t ∈ openParams}) :
    LeftAtOn F.val (P.toPlaneGraphDrawing.arc e) s ↔
      LeftAtOn (P.toPlaneGraphDrawingFaceEquiv F).val (P.arc e.out).toPath s := by
  exact leftAtOn_cast_iff F.val (P.arc e.out).toPath
    (P.arc_start e.out).symm (P.arc_finish e.out).symm s

/-- Helper toward Definition 1.1 / Definition 3.2: the right winding-side
test on a stored geometric edge is exactly the test on its selected dart. -/
theorem toPlaneGraphDrawing_rightAtOn_iff (e : P.GeometricEdge)
    (F : P.toPlaneGraphDrawing.Face) (s : {t : I // t ∈ openParams}) :
    RightAtOn F.val (P.toPlaneGraphDrawing.arc e) s ↔
      RightAtOn (P.toPlaneGraphDrawingFaceEquiv F).val (P.arc e.out).toPath s := by
  exact rightAtOn_cast_iff F.val (P.arc e.out).toPath
    (P.arc_start e.out).symm (P.arc_finish e.out).symm s


























end PLDrawing

end DirectedDistances.PlanarMap

end
