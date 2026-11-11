/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalConnected2
public import DirectedDistances.PlanarMap.PlaneStarExtension2
public import Mathlib.Analysis.Convex.Gauge
public import DirectedDistances.PlanarMap.TriangleGeometry

/-! # Radial disk charts

Helpers toward Proposition 5.16. Radial scaling is used only under an explicit
positive radial hypothesis; arbitrary cyclically simple polygons still require
ear removal and gluing. No general Schoenflies theorem is assumed. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Topology

/-- Helper toward Proposition 5.16: scaling each ray by its prescribed radius. -/
@[expose] def polygonRadialMap (ρ : Circle → ℝ) (z : ℂ) : ℂ :=
  (ρ (starDirection z) : ℂ) * z

/-- Helper toward Proposition 5.16: radial scaling fixes the origin. -/
@[simp] theorem polygonRadialMap_zero (ρ : Circle → ℝ) : polygonRadialMap ρ 0 = 0 := by
  simp only [polygonRadialMap, mul_zero]

/-- Helper toward Proposition 5.16: the norm under nonnegative radial scaling. -/
theorem norm_polygonRadialMap (ρ : Circle → ℝ) (hρ : ∀ c, 0 ≤ ρ c) (z : ℂ) :
    ‖polygonRadialMap ρ z‖ = ρ (starDirection z) * ‖z‖ := by
  rw [polygonRadialMap, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hρ _)]

/-- Helper toward Proposition 5.16: a positive scalar does not change direction. -/
theorem starDirection_pos_mul (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    starDirection ((r : ℂ) * z) = starDirection z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have heq : (r : ℂ) * z = ((r * ‖z‖ : ℝ) : ℂ) * (starDirection z : ℂ) := by
    rw [Complex.ofReal_mul, mul_assoc, norm_mul_starDirection]
  rw [heq]
  exact starDirection_polar _ (mul_pos hr hn) _

/-- Helper toward Proposition 5.16: a continuous radial scaling is continuous,
including at the cone vertex. -/
theorem continuous_polygonRadialMap (ρ : Circle → ℝ) (hρ : Continuous ρ)
    (hpos : ∀ c, 0 < ρ c) : Continuous (polygonRadialMap ρ) := by
  obtain ⟨M, hM⟩ := (isCompact_univ.image hρ).bddAbove
  have hbound (c : Circle) : ρ c ≤ M := hM ⟨c, Set.mem_univ c, rfl⟩
  have hMpos : 0 < M + 1 := by linarith only [hpos 1, hbound 1]
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    refine ⟨ε / (M + 1), div_pos hε hMpos, fun {z} hz => ?_⟩
    rw [polygonRadialMap_zero, dist_zero_right,
      norm_polygonRadialMap ρ (fun c => (hpos c).le)]
    have hz' : ‖z‖ < ε / (M + 1) := by simpa only [dist_zero_right] using hz
    calc
      ρ (starDirection z) * ‖z‖ ≤ (M + 1) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (le_trans (hbound _) (le_add_of_nonneg_right zero_le_one))
          (norm_nonneg _)
      _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hMpos).mp hz'
  · exact (Complex.continuous_ofReal.continuousAt.comp
      (hρ.continuousAt.comp (continuousAt_starDirection hz))).mul continuous_id.continuousAt

/-- Helper toward Proposition 5.16: reciprocal radial scaling is an inverse. -/
theorem polygonRadialMap_inverse (ρ : Circle → ℝ) (hpos : ∀ c, 0 < ρ c) (z : ℂ) :
    polygonRadialMap (fun c => (ρ c)⁻¹) (polygonRadialMap ρ z) = z := by
  by_cases hz : z = 0
  · subst z
    rw [polygonRadialMap_zero, polygonRadialMap_zero]
  · have hd := starDirection_pos_mul (ρ (starDirection z)) (hpos _) z hz
    simp only [polygonRadialMap, hd, Complex.ofReal_inv, ← mul_assoc,
      inv_mul_cancel₀ (show (ρ (starDirection z) : ℂ) ≠ 0 by exact_mod_cast (hpos _).ne'),
      one_mul]

/-- Helper toward Proposition 5.16: every continuous positive radial function
induces a plane homeomorphism. -/
@[expose] def polygonRadialHomeomorph (ρ : Circle → ℝ) (hρ : Continuous ρ)
    (hpos : ∀ c, 0 < ρ c) : ℂ ≃ₜ ℂ where
  toFun := polygonRadialMap ρ
  invFun := polygonRadialMap (fun c => (ρ c)⁻¹)
  left_inv := polygonRadialMap_inverse ρ hpos
  right_inv := by
    intro z
    have h := polygonRadialMap_inverse (fun c => (ρ c)⁻¹)
      (fun c => inv_pos.mpr (hpos c)) z
    simpa only [inv_inv] using h
  continuous_toFun := continuous_polygonRadialMap ρ hρ hpos
  continuous_invFun := continuous_polygonRadialMap _
    (hρ.inv₀ (fun c => (hpos c).ne')) (fun c => inv_pos.mpr (hpos c))


namespace Polyline

/-- Helper toward Proposition 5.16: the direction from an interior point is
continuous on the polygon boundary. -/
theorem continuous_boundaryDirection (c : Polyline) (p : ℂ) (hp : p ∉ c.image) :
    Continuous (fun x : c.image => starDirection ((x : ℂ) - p)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx : (x : ℂ) - p ≠ 0 := sub_ne_zero.mpr (fun h => hp (h ▸ x.property))
  have hg : Continuous (fun y : c.image => (y : ℂ) - p) :=
    continuous_subtype_val.sub continuous_const
  exact (continuousAt_starDirection hx).comp (f := fun y : c.image => (y : ℂ) - p) hg.continuousAt

/-- Helper toward Proposition 5.16: unique positive intersections of all rays
make the boundary direction map bijective. -/
theorem bijective_boundaryDirection (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image) :
    Function.Bijective (fun x : c.image => starDirection ((x : ℂ) - p)) := by
  have hpos (x : c.image) : 0 < ‖(x : ℂ) - p‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h : (x : ℂ) = p => hp (h ▸ x.property)))
  have hrec (x : c.image) : p + (‖(x : ℂ) - p‖ : ℂ) *
      (starDirection ((x : ℂ) - p) : ℂ) = x := by
    rw [norm_mul_starDirection, add_sub_cancel]
  constructor
  · intro x y hxy
    change starDirection ((x : ℂ) - p) = starDirection ((y : ℂ) - p) at hxy
    obtain ⟨r, _, huniq⟩ := hray (starDirection ((x : ℂ) - p))
    have hx := huniq ‖(x : ℂ) - p‖ ⟨hpos x, by rw [hrec]; exact x.property⟩
    have hy := huniq ‖(y : ℂ) - p‖ ⟨hpos y, by rw [hxy, hrec]; exact y.property⟩
    apply Subtype.ext
    calc
      (x : ℂ) = p + (‖(x : ℂ) - p‖ : ℂ) *
          (starDirection ((x : ℂ) - p) : ℂ) := (hrec x).symm
      _ = p + (‖(y : ℂ) - p‖ : ℂ) *
          (starDirection ((y : ℂ) - p) : ℂ) := by rw [hx, hy, hxy]
      _ = y := hrec y
  · intro d
    obtain ⟨r, ⟨hr, hm⟩, _⟩ := hray d
    refine ⟨⟨p + (r : ℂ) * (d : ℂ), hm⟩, ?_⟩
    dsimp
    rw [add_sub_cancel_left, starDirection_polar r hr]

/-- Helper toward Proposition 5.16: radial projection of a compact polygon
boundary with exactly one positive point on each ray is a homeomorphism. -/
@[expose] def boundaryDirectionHomeomorph (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image) :
    c.image ≃ₜ Circle := by
  letI : CompactSpace c.image := isCompact_iff_compactSpace.mp c.isCompact_image
  exact (continuous_boundaryDirection c p hp).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (bijective_boundaryDirection c p hp hray))

/-- Helper toward Proposition 5.16: the radial distance to the uniquely
intersected polygon boundary. Its existence comes from the boundary homeomorphism. -/
@[expose] def boundaryRadius (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (d : Circle) : ℝ :=
  ‖((boundaryDirectionHomeomorph c p hp hray).symm d : ℂ) - p‖

/-- Helper toward Proposition 5.16: the radial boundary function is continuous;
continuity is derived from compactness and unique rays, not assumed. -/
theorem continuous_boundaryRadius (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image) :
    Continuous (boundaryRadius c p hp hray) := by
  exact (continuous_subtype_val.comp
    (boundaryDirectionHomeomorph c p hp hray).symm.continuous |>.sub continuous_const).norm

/-- Helper toward Proposition 5.16: the radial boundary function is positive. -/
theorem boundaryRadius_pos (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (d : Circle) : 0 < boundaryRadius c p hp hray d := by
  apply norm_pos_iff.mpr
  apply sub_ne_zero.mpr
  intro h
  exact hp (h ▸ ((boundaryDirectionHomeomorph c p hp hray).symm d).property)

/-- Helper toward Proposition 5.16: polar reconstruction of the boundary
point selected by a direction. -/
theorem boundaryRadius_reconstruct (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (d : Circle) :
    p + (boundaryRadius c p hp hray d : ℂ) * (d : ℂ) =
      ((boundaryDirectionHomeomorph c p hp hray).symm d : ℂ) := by
  have hd := (boundaryDirectionHomeomorph c p hp hray).apply_symm_apply d
  change starDirection (((boundaryDirectionHomeomorph c p hp hray).symm d : ℂ) - p) = d at hd
  change p + (‖((boundaryDirectionHomeomorph c p hp hray).symm d : ℂ) - p‖ : ℂ) * (d : ℂ) = _
  conv_lhs => arg 2; arg 2; rw [← hd]
  rw [norm_mul_starDirection, add_sub_cancel]


/-- Helper toward Proposition 5.16: the ambient radial chart centered at an
interior point of a polygon with unique positive ray intersections. -/
@[expose] def radialPlaneChart (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image) :
    ℂ ≃ₜ ℂ :=
  (polygonRadialHomeomorph (boundaryRadius c p hp hray)
    (continuous_boundaryRadius c p hp hray) (boundaryRadius_pos c p hp hray)).trans
      (Homeomorph.addLeft p)

/-- Helper toward Proposition 5.16: the radial chart sends the center to the
chosen polygon interior point. -/
theorem radialPlaneChart_zero (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image) :
    radialPlaneChart c p hp hray 0 = p := by
  change p + polygonRadialMap _ 0 = p
  rw [polygonRadialMap_zero, add_zero]

/-- Helper toward Proposition 5.16: on the unit circle, the radial chart
realizes the inverse boundary projection. -/
theorem radialPlaneChart_circle (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (d : Circle) :
    radialPlaneChart c p hp hray (d : ℂ) =
      ((boundaryDirectionHomeomorph c p hp hray).symm d : ℂ) := by
  have hd : starDirection (d : ℂ) = d := by
    simpa only [Complex.ofReal_one, one_mul] using starDirection_polar 1 zero_lt_one d
  change p + (boundaryRadius c p hp hray (starDirection (d : ℂ)) : ℂ) * (d : ℂ) = _
  rw [hd]
  exact boundaryRadius_reconstruct c p hp hray d

/-- Helper toward Proposition 5.16: the ambient radial chart maps the unit
sphere onto exactly the polygon boundary. -/
theorem radialPlaneChart_image_sphere (c : Polyline) (p : ℂ) (hp : p ∉ c.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image) :
    radialPlaneChart c p hp hray '' Metric.sphere (0 : ℂ) 1 = c.image := by
  apply Set.Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    let d : Circle := ⟨w, hw⟩
    rw [show w = (d : ℂ) from rfl, radialPlaneChart_circle]
    exact ((boundaryDirectionHomeomorph c p hp hray).symm d).property
  · intro z hz
    let d := boundaryDirectionHomeomorph c p hp hray ⟨z, hz⟩
    refine ⟨(d : ℂ), d.property, ?_⟩
    rw [radialPlaneChart_circle]
    exact congrArg Subtype.val ((boundaryDirectionHomeomorph c p hp hray).symm_apply_apply ⟨z, hz⟩)

/-- Helper toward Proposition 5.16: an ambient chart carrying the unit circle
to a cyclic polygon and its center inside carries the open disk onto the inside.
This is a consequence of the proved polygonal separation theorem. -/
theorem image_ball_eq_inside_of_image_sphere (c : Polyline) (hc : c.IsCyclicSimple)
    (H : ℂ ≃ₜ ℂ) (hcenter : H 0 ∈ c.inside)
    (hsphere : H '' Metric.sphere (0 : ℂ) 1 = c.image) :
    H '' Metric.ball (0 : ℂ) 1 = c.inside := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, dist_self, zero_lt_one]
  have havoid (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : H z ∉ c.image := by
    intro him
    rw [← hsphere] at him
    obtain ⟨w, hw, heq⟩ := him
    have hwz := H.injective heq
    subst w
    have hzlt : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzeq : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    exact (ne_of_lt hzlt) hzeq
  apply Set.Subset.antisymm
  · have hpre : IsPreconnected (H '' Metric.ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).isPreconnected.image H H.continuous.continuousOn
    have hsub : H '' Metric.ball (0 : ℂ) 1 ⊆ connectedComponentIn c.imageᶜ (H 0) :=
      hpre.subset_connectedComponentIn
      (Set.mem_image_of_mem H hzero) (by rintro _ ⟨z, hz, rfl⟩; exact havoid z hz)
    exact hsub.trans (component_subset_inside c hclosed (H 0) hcenter)
  · intro z hz
    have hpre := (isConnected_inside_outside_cyclic c hc).1.isPreconnected
    have hnorm : Continuous (fun z : ℂ => ‖H.symm z‖) := H.symm.continuous.norm
    have hne : ∀ z ∈ c.inside, ‖H.symm z‖ ≠ 1 := by
      intro z hz heq
      apply hz.1
      rw [← hsphere]
      refine ⟨H.symm z, ?_, H.apply_symm_apply z⟩
      simpa only [Metric.mem_sphere, dist_zero_right] using heq
    have hlt : ‖H.symm z‖ < 1 := hpre.gt_of_ne hnorm.continuousOn hne
      ⟨H 0, hcenter, by rw [H.symm_apply_apply, norm_zero]; exact zero_lt_one⟩ hz
    refine ⟨H.symm z, ?_, H.apply_symm_apply z⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hlt

/-- Helper toward Proposition 5.16: the radial chart carries the closed unit
disk onto the closure of the inside, without assuming a disk chart. -/
theorem radialPlaneChart_image_closedBall (c : Polyline) (hc : c.IsCyclicSimple)
    (p : ℂ) (hp : p ∈ c.inside)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image) :
    radialPlaneChart c p hp.1 hray '' Metric.closedBall (0 : ℂ) 1 = closure c.inside := by
  have hi := image_ball_eq_inside_of_image_sphere c hc (radialPlaneChart c p hp.1 hray)
    (by rw [radialPlaneChart_zero]; exact hp) (radialPlaneChart_image_sphere c p hp.1 hray)
  rw [← closure_ball (0 : ℂ) one_ne_zero, Homeomorph.image_closure, hi]

/-- Helper toward Proposition 5.16: a cyclically simple polygon with an
interior point meeting each ray exactly once has a closed unit disk chart. -/
@[expose] def radialDiskChart (c : Polyline) (hc : c.IsCyclicSimple)
    (p : ℂ) (hp : p ∈ c.inside)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image) :
    Metric.closedBall (0 : ℂ) 1 ≃ₜ closure c.inside :=
  ((radialPlaneChart c p hp.1 hray).image (Metric.closedBall (0 : ℂ) 1)).trans
    (Homeomorph.setCongr (radialPlaneChart_image_closedBall c hc p hp hray))


/-- Helper toward Proposition 5.16: the disk chart has the explicit ambient
radial formula. -/
theorem radialDiskChart_apply (c : Polyline) (hc : c.IsCyclicSimple)
    (p : ℂ) (hp : p ∈ c.inside)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (z : Metric.closedBall (0 : ℂ) 1) :
    (radialDiskChart c hc p hp hray z : ℂ) =
      p + (boundaryRadius c p hp.1 hray (starDirection (z : ℂ)) : ℂ) * (z : ℂ) := rfl

/-- Helper toward Proposition 5.16: the disk chart identifies exactly its
unit-circle boundary with the polygon image. -/
theorem radialDiskChart_mem_image_iff (c : Polyline) (hc : c.IsCyclicSimple)
    (p : ℂ) (hp : p ∈ c.inside)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (z : Metric.closedBall (0 : ℂ) 1) :
    (radialDiskChart c hc p hp hray z : ℂ) ∈ c.image ↔ ‖(z : ℂ)‖ = 1 := by
  change radialPlaneChart c p hp.1 hray (z : ℂ) ∈ c.image ↔ _
  have hs := radialPlaneChart_image_sphere c p hp.1 hray
  constructor
  · intro hz
    have hm : radialPlaneChart c p hp.1 hray (z : ℂ) ∈
        radialPlaneChart c p hp.1 hray '' Metric.sphere (0 : ℂ) 1 := hs.symm ▸ hz
    obtain ⟨w, hw, heq⟩ := hm
    have hwz := (radialPlaneChart c p hp.1 hray).injective heq
    subst w
    simpa only [Metric.mem_sphere, dist_zero_right] using hw
  · intro hz
    apply hs ▸ (show radialPlaneChart c p hp.1 hray (z : ℂ) ∈
      radialPlaneChart c p hp.1 hray '' Metric.sphere (0 : ℂ) 1 from ?_)
    exact ⟨z, by simpa only [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩

/-- Helper toward Proposition 5.16: the boundary correspondence of the disk
chart is the inverse of radial projection, with no unspecified reparameterization. -/
theorem radialDiskChart_circle (c : Polyline) (hc : c.IsCyclicSimple)
    (p : ℂ) (hp : p ∈ c.inside)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (d : Circle) :
    (radialDiskChart c hc p hp hray
      ⟨(d : ℂ), by simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]⟩ : ℂ) =
      ((boundaryDirectionHomeomorph c p hp.1 hray).symm d : ℂ) :=
  radialPlaneChart_circle c p hp.1 hray d

end Polyline

/-- Helper toward Proposition 5.16: a convex region is star-convex with
respect to each of its points. -/
theorem polygon_starConvex_of_convex (s : Set ℂ) (hs : Convex ℝ s)
    (p : ℂ) (hp : p ∈ s) : StarConvex ℝ p s := hs.starConvex hp

/-- Helper toward Proposition 5.16: a filled triangle is star-convex at its
barycenter, including degenerate triangles. -/
theorem triangle_starConvex_barycenter (a b c : ℂ) :
    StarConvex ℝ ((a + b + c) / 3) (convexHull ℝ ({a, b, c} : Set ℂ)) := by
  have ha : a ∈ convexHull ℝ ({a, b, c} : Set ℂ) := subset_convexHull ℝ _ (by simp only [Set.mem_insert_iff, true_or])
  have hb : b ∈ convexHull ℝ ({a, b, c} : Set ℂ) := subset_convexHull ℝ _ (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
  have hc : c ∈ convexHull ℝ ({a, b, c} : Set ℂ) := subset_convexHull ℝ _ (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true])
  apply (convex_convexHull ℝ _).starConvex
  have hbc := (convex_convexHull ℝ _) hb hc
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
  have habc := (convex_convexHull ℝ _) ha hbc
    (show (0 : ℝ) ≤ 1 / 3 by norm_num) (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    (show (1 : ℝ) / 3 + 2 / 3 = 1 by norm_num)
  convert habc using 1; simp only [RCLike.real_smul_eq_coe_mul]; push_cast; ring


namespace Polyline

/-- Helper toward Proposition 5.16: every ray from an inside point of a
closed polygon meets its boundary at a positive distance. Uniqueness is not
asserted for non-star-shaped polygons. -/
theorem exists_pos_ray_mem_image (c : Polyline) (hclosed : c.start = c.finish)
    (p : ℂ) (hp : p ∈ c.inside) (d : Circle) :
    ∃ r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image := by
  by_contra hnone
  have hoff : ∀ r : ℝ, 0 ≤ r → p + (r : ℂ) * (d : ℂ) ∉ c.image := by
    intro r hr hm
    rcases hr.eq_or_lt with hr | hr
    · subst r
      exact hp.1 (by simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hm)
    · exact hnone ⟨r, hr, hm⟩
  let f : ℝ → ℂ := fun r => p + (r : ℂ) * (d : ℂ)
  have hf : Continuous f := by fun_prop
  have hpre : IsPreconnected (f '' Set.Ici (0 : ℝ)) :=
    isPreconnected_Ici.image f hf.continuousOn
  have hpim : p ∈ f '' Set.Ici (0 : ℝ) :=
    ⟨0, le_refl 0, by simp only [f, Complex.ofReal_zero, zero_mul, add_zero]⟩
  have hsub : f '' Set.Ici (0 : ℝ) ⊆ connectedComponentIn c.imageᶜ p :=
    hpre.subset_connectedComponentIn hpim (by rintro _ ⟨r, hr, rfl⟩; exact hoff r hr)
  have hin : f '' Set.Ici (0 : ℝ) ⊆ c.inside :=
    hsub.trans (component_subset_inside c hclosed p hp)
  obtain ⟨R, hR⟩ := (isBounded_inside c hclosed).subset_closedBall p
  let r : ℝ := max R 0 + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrR : R < r := by dsimp [r]; linarith only [le_max_left R 0]
  have hball := hR (hin ⟨r, hr, rfl⟩)
  have hnorm : ‖(r : ℂ) * (d : ℂ)‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, f, add_sub_cancel_left] using hball
  rw [norm_star_polar r hr d] at hnorm
  exact (not_le_of_gt hrR) hnorm

/-- Helper toward Proposition 5.16: along a ray of a convex polygon inside,
every positive point before a boundary point remains inside. -/
theorem ray_mem_inside_of_lt_boundary (c : Polyline) (hc : c.IsCyclicSimple)
    (hconv : Convex ℝ c.inside) (p : ℂ) (hp : p ∈ c.inside)
    (d : Circle) (r s : ℝ) (hr : 0 < r) (hrs : r < s)
    (hs : p + (s : ℂ) * (d : ℂ) ∈ c.image) :
    p + (r : ℂ) * (d : ℂ) ∈ c.inside := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  have hfront := (frontier_inside_outside_eq_image_cyclic c hc).1
  have hscl : p + (s : ℂ) * (d : ℂ) ∈ closure c.inside :=
    frontier_subset_closure (hfront.symm ▸ hs)
  have hpint : p ∈ _root_.interior c.inside := by
    rwa [(isOpen_inside c hclosed).interior_eq]
  have hseg := hconv.openSegment_interior_closure_subset_interior hpint hscl
  apply interior_subset (hseg ?_)
  rw [openSegment_eq_image']
  have hspos : 0 < s := hr.trans hrs
  refine ⟨r / s, ⟨div_pos hr hspos, (div_lt_one₀ hspos).mpr hrs⟩, ?_⟩
  simp only [add_sub_cancel_left, RCLike.real_smul_eq_coe_mul]
  have hcast := congrArg Complex.ofReal (div_mul_cancel₀ r hspos.ne')
  rw [Complex.ofReal_mul] at hcast
  calc
    p + ((r / s : ℝ) : ℂ) * ((s : ℂ) * (d : ℂ)) =
        p + (((r / s : ℝ) : ℂ) * (s : ℂ)) * (d : ℂ) := by ring
    _ = p + (r : ℂ) * (d : ℂ) := congrArg (fun q : ℂ => p + q * (d : ℂ)) hcast

/-- Helper toward Proposition 5.16: a cyclically simple polygon with convex
inside has exactly one boundary point at positive distance on every ray. -/
theorem existsUnique_pos_ray_mem_image_of_convex (c : Polyline) (hc : c.IsCyclicSimple)
    (hconv : Convex ℝ c.inside) (p : ℂ) (hp : p ∈ c.inside) (d : Circle) :
    ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  obtain ⟨r, hr, hrim⟩ := exists_pos_ray_mem_image c hclosed p hp d
  refine ⟨r, ⟨hr, hrim⟩, ?_⟩
  rintro s ⟨hs, hsim⟩
  rcases lt_trichotomy s r with hlt | heq | hgt
  · exact False.elim ((ray_mem_inside_of_lt_boundary c hc hconv p hp d s r hs hlt hrim).1 hsim)
  · exact heq
  · exact False.elim ((ray_mem_inside_of_lt_boundary c hc hconv p hp d r s hr hgt hsim).1 hrim)

/-- Helper toward Proposition 5.16: every cyclically simple polygon whose
inside is convex has a closed unit disk chart, constructed at any inside point. -/
@[expose] def convexDiskChart (c : Polyline) (hc : c.IsCyclicSimple)
    (hconv : Convex ℝ c.inside) (p : ℂ) (hp : p ∈ c.inside) :
    Metric.closedBall (0 : ℂ) 1 ≃ₜ closure c.inside :=
  radialDiskChart c hc p hp (existsUnique_pos_ray_mem_image_of_convex c hc hconv p hp)

end Polyline

/-- Helper toward Proposition 5.16: inverse gauge gives a positive continuous
radial function for a bounded convex neighborhood of the origin. -/
theorem continuous_pos_inverse_gauge (s : Set ℂ) (hconv : Convex ℝ s)
    (hzero : s ∈ 𝓝 (0 : ℂ)) (hb : Bornology.IsBounded s) :
    Continuous (fun d : Circle => (gauge s (d : ℂ))⁻¹) ∧
      ∀ d : Circle, 0 < (gauge s (d : ℂ))⁻¹ := by
  have hg (d : Circle) : 0 < gauge s (d : ℂ) :=
    (gauge_pos (absorbent_nhds_zero hzero)
      (NormedSpace.isVonNBounded_of_isBounded ℝ hb)).mpr d.coe_ne_zero
  exact ⟨((continuous_gauge hconv hzero).comp continuous_subtype_val).inv₀
    (fun d => (hg d).ne'), fun d => inv_pos.mpr (hg d)⟩

/-- Helper toward Proposition 5.16: scaling by the inverse boundary gauge
normalizes the gauge to the original Euclidean radius. -/
theorem gauge_polygonRadialMap_inverse_gauge (s : Set ℂ) (hzero : s ∈ 𝓝 (0 : ℂ))
    (hb : Bornology.IsBounded s) (z : ℂ) :
    gauge s (polygonRadialMap (fun d => (gauge s (d : ℂ))⁻¹) z) = ‖z‖ := by
  have hg (d : Circle) : 0 < gauge s (d : ℂ) :=
    (gauge_pos (absorbent_nhds_zero hzero)
      (NormedSpace.isVonNBounded_of_isBounded ℝ hb)).mpr d.coe_ne_zero
  have hpolar : (‖z‖ : ℝ) • (starDirection z : ℂ) = z := by
    exact Complex.real_smul.trans (norm_mul_starDirection z)
  have hscale := gauge_smul_of_nonneg (s := s) (norm_nonneg z) (starDirection z : ℂ)
  rw [hpolar] at hscale
  change gauge s ((gauge s (starDirection z : ℂ))⁻¹ • z) = ‖z‖
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr (hg _).le), hscale, smul_eq_mul, smul_eq_mul]
  field_simp [(hg (starDirection z)).ne']

/-- Helper toward Proposition 5.16: an explicit ambient disk chart for a
bounded convex neighborhood of zero, built from its gauge. -/
@[expose] def convexZeroPlaneChart (s : Set ℂ) (hconv : Convex ℝ s)
    (hzero : s ∈ 𝓝 (0 : ℂ)) (hb : Bornology.IsBounded s) : ℂ ≃ₜ ℂ :=
  polygonRadialHomeomorph _ (continuous_pos_inverse_gauge s hconv hzero hb).1
    (continuous_pos_inverse_gauge s hconv hzero hb).2

/-- Helper toward Proposition 5.16: the gauge chart carries the closed unit
disk onto the closure of the convex neighborhood. -/
theorem convexZeroPlaneChart_image_closedBall (s : Set ℂ) (hconv : Convex ℝ s)
    (hzero : s ∈ 𝓝 (0 : ℂ)) (hb : Bornology.IsBounded s) :
    convexZeroPlaneChart s hconv hzero hb '' Metric.closedBall (0 : ℂ) 1 = closure s := by
  have hmem (z : ℂ) : convexZeroPlaneChart s hconv hzero hb z ∈ closure s ↔ ‖z‖ ≤ 1 := by
    rw [← gauge_le_one_iff_mem_closure hconv hzero]
    rw [show gauge s (convexZeroPlaneChart s hconv hzero hb z) = ‖z‖ from
      gauge_polygonRadialMap_inverse_gauge s hzero hb z]
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    apply (hmem z).mpr
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  · intro z hz
    let H := convexZeroPlaneChart s hconv hzero hb
    refine ⟨H.symm z, ?_, H.apply_symm_apply z⟩
    have hle := (hmem (H.symm z)).mp (by simpa only [H, Homeomorph.apply_symm_apply] using hz)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hle

/-- Helper toward Proposition 5.16: the gauge chart also identifies the exact
boundary, rather than merely producing a homeomorphism of the closed sets. -/
theorem convexZeroPlaneChart_image_sphere (s : Set ℂ) (hconv : Convex ℝ s)
    (hzero : s ∈ 𝓝 (0 : ℂ)) (hb : Bornology.IsBounded s) :
    convexZeroPlaneChart s hconv hzero hb '' Metric.sphere (0 : ℂ) 1 = frontier s := by
  have hmem (z : ℂ) : convexZeroPlaneChart s hconv hzero hb z ∈ frontier s ↔ ‖z‖ = 1 := by
    rw [← gauge_eq_one_iff_mem_frontier hconv hzero,
      show gauge s (convexZeroPlaneChart s hconv hzero hb z) = ‖z‖ from
        gauge_polygonRadialMap_inverse_gauge s hzero hb z]
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (hmem z).mpr (by simpa only [Metric.mem_sphere, dist_zero_right] using hz)
  · intro z hz
    let H := convexZeroPlaneChart s hconv hzero hb
    refine ⟨H.symm z, ?_, H.apply_symm_apply z⟩
    have heq := (hmem (H.symm z)).mp (by simpa only [H, Homeomorph.apply_symm_apply] using hz)
    simpa only [Metric.mem_sphere, dist_zero_right] using heq


/-- Helper toward Proposition 5.16: any bounded convex planar region with
nonempty interior admits an ambient chart matching both its closure and frontier. -/
theorem exists_convex_plane_chart (s : Set ℂ) (hconv : Convex ℝ s)
    (hne : (_root_.interior s).Nonempty) (hb : Bornology.IsBounded s) :
    ∃ H : ℂ ≃ₜ ℂ, H '' Metric.closedBall (0 : ℂ) 1 = closure s ∧
      H '' Metric.sphere (0 : ℂ) 1 = frontier s := by
  obtain ⟨p, hp⟩ := hne
  let T : ℂ ≃ₜ ℂ := Homeomorph.addLeft p
  let t : Set ℂ := T ⁻¹' s
  have htc : Convex ℝ t := hconv.translate_preimage_right p
  have ht0 : t ∈ 𝓝 (0 : ℂ) := by
    have hpnhds : s ∈ 𝓝 (T 0) := by
      change s ∈ 𝓝 (p + 0)
      rw [add_zero]
      exact
        (mem_interior_iff_mem_nhds.mp hp)
    exact T.continuous.continuousAt.preimage_mem_nhds hpnhds
  obtain ⟨R, hR⟩ := hb.subset_closedBall p
  have htb : Bornology.IsBounded t := by
    have hbounded : Bornology.IsBounded (Metric.closedBall (0 : ℂ) R) := Metric.isBounded_closedBall
    apply hbounded.subset
    intro z hz
    have hzball := hR hz
    change dist (p + z) p ≤ R at hzball
    simpa only [Metric.mem_closedBall, dist_eq_norm,
      add_sub_cancel_left, sub_zero] using hzball
  have hT : T '' t = s := Set.image_preimage_eq _ T.surjective
  let G := convexZeroPlaneChart t htc ht0 htb
  refine ⟨G.trans T, ?_, ?_⟩
  · change (fun z => T (G z)) '' Metric.closedBall (0 : ℂ) 1 = closure s
    rw [← Set.image_image, convexZeroPlaneChart_image_closedBall,
      T.image_closure, hT]
  · change (fun z => T (G z)) '' Metric.sphere (0 : ℂ) 1 = frontier s
    rw [← Set.image_image, convexZeroPlaneChart_image_sphere,
      T.image_frontier, hT]

/-- Helper toward Proposition 5.16: a noncollinear filled triangle has an
ambient disk chart with its three geometric sides as the induced boundary. -/
theorem exists_triangle_plane_chart (a b c : ℂ)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    ∃ H : ℂ ≃ₜ ℂ,
      H '' Metric.closedBall (0 : ℂ) 1 = convexHull ℝ ({a, b, c} : Set ℂ) ∧
      H '' Metric.sphere (0 : ℂ) 1 =
        segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
  obtain ⟨H, hdisk, hfront⟩ := exists_convex_plane_chart
    (convexHull ℝ ({a, b, c} : Set ℂ)) (convex_convexHull ℝ _)
    (triangle_interior_nonempty a b c hnc) (isBounded_triangle a b c)
  refine ⟨H, ?_, ?_⟩
  · simpa only [(isCompact_triangle a b c).isClosed.closure_eq] using hdisk
  · have hreg : frontier (convexHull ℝ ({a, b, c} : Set ℂ)) =
        frontier (_root_.interior (convexHull ℝ ({a, b, c} : Set ℂ))) := by
      rw [frontier, frontier, (isCompact_triangle a b c).isClosed.closure_eq,
        closure_triangle_interior a b c hnc, interior_interior]
    exact hfront.trans (hreg.trans (frontier_triangle_interior a b c hnc))


namespace Polyline

/-- Helper toward Proposition 5.16: a boundary homeomorphism between two
polygons with unique positive ray intersections extends to the whole plane
by conjugating the circle cone through their radial charts. -/
@[expose] def radialBoundaryExtension (c c' : Polyline) (p q : ℂ)
    (hp : p ∉ c.image) (hq : q ∉ c'.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (hray' : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ q + (r : ℂ) * (d : ℂ) ∈ c'.image)
    (f : c.image ≃ₜ c'.image) : ℂ ≃ₜ ℂ :=
  (radialPlaneChart c p hp hray).symm.trans
    ((starConeHomeomorph
      (((boundaryDirectionHomeomorph c p hp hray).symm.trans f).trans
        (boundaryDirectionHomeomorph c' q hq hray'))).trans
      (radialPlaneChart c' q hq hray'))

/-- Helper toward Proposition 5.16: the extended plane map realizes the
specified boundary homeomorphism pointwise. -/
theorem radialBoundaryExtension_apply_boundary (c c' : Polyline) (p q : ℂ)
    (hp : p ∉ c.image) (hq : q ∉ c'.image)
    (hray : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ p + (r : ℂ) * (d : ℂ) ∈ c.image)
    (hray' : ∀ d : Circle, ∃! r : ℝ, 0 < r ∧ q + (r : ℂ) * (d : ℂ) ∈ c'.image)
    (f : c.image ≃ₜ c'.image) (x : c.image) :
    radialBoundaryExtension c c' p q hp hq hray hray' f (x : ℂ) = (f x : ℂ) := by
  let b := boundaryDirectionHomeomorph c p hp hray
  let b' := boundaryDirectionHomeomorph c' q hq hray'
  let e : Circle ≃ₜ Circle := (b.symm.trans f).trans b'
  have hrec : radialPlaneChart c p hp hray (b x : ℂ) = (x : ℂ) :=
    (radialPlaneChart_circle c p hp hray (b x)).trans
      (congrArg Subtype.val (b.symm_apply_apply x))
  have hinv : (radialPlaneChart c p hp hray).symm (x : ℂ) = (b x : ℂ) := by
    apply (radialPlaneChart c p hp hray).injective
    rw [Homeomorph.apply_symm_apply]
    exact hrec.symm
  have hcone : starConeHomeomorph e (b x : ℂ) = (e (b x) : ℂ) := by
    simpa only [Complex.ofReal_one, one_mul] using
      starConeHomeomorph_polar e 1 zero_le_one (b x)
  change radialPlaneChart c' q hq hray'
    (starConeHomeomorph e ((radialPlaneChart c p hp hray).symm (x : ℂ))) = _
  rw [hinv, hcone, radialPlaneChart_circle]
  change ((b'.symm (b' (f (b.symm (b x))))) : ℂ) = (f x : ℂ)
  rw [b.symm_apply_apply, b'.symm_apply_apply]

end Polyline

/-- Helper toward Proposition 5.16: the noncollinear triangle chart restricts
to an actual closed-disk homeomorphism with the exact three-side correspondence. -/
theorem exists_triangle_disk_chart (a b c : ℂ)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ convexHull ℝ ({a, b, c} : Set ℂ),
      ∀ z : Metric.closedBall (0 : ℂ) 1,
        (h z : ℂ) ∈ segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a ↔ ‖(z : ℂ)‖ = 1 := by
  obtain ⟨H, hdisk, hboundary⟩ := exists_triangle_plane_chart a b c hnc
  let h := (H.image (Metric.closedBall (0 : ℂ) 1)).trans (Homeomorph.setCongr hdisk)
  refine ⟨h, ?_⟩
  intro z
  change H (z : ℂ) ∈ segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a ↔ _
  constructor
  · intro hz
    have hm : H (z : ℂ) ∈ H '' Metric.sphere (0 : ℂ) 1 := hboundary.symm ▸ hz
    obtain ⟨w, hw, heq⟩ := hm
    have hwz := H.injective heq
    subst w
    simpa only [Metric.mem_sphere, dist_zero_right] using hw
  · intro hz
    have hm : H (z : ℂ) ∈ H '' Metric.sphere (0 : ℂ) 1 :=
      ⟨z, by simpa only [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩
    exact hboundary ▸ hm




































end DirectedDistances.PlanarMap

