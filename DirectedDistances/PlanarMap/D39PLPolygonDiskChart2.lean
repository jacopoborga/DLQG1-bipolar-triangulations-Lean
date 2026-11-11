/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLPolygonDiskChart
public import DirectedDistances.PlanarMap.D39PLUnitDiskBoundary
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Complex.Convex

/-! # Closed-cover gluing for polygon disk charts

Helpers toward Proposition 5.16. The gluing theorem below proves the topological
pasting step for compatible charts; polygon diagonals and their geometric
decompositions are separate obligations. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Topology

/-- Helper toward Proposition 5.16: injective continuous charts on a closed
cover of a compact space glue to a homeomorphism onto the union of their images
when their cross-chart coincidences are exactly the shared domain points. -/
theorem exists_homeomorph_union_of_closed_cover
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (s t : Set X) (hs : IsClosed s) (ht : IsClosed t)
    (hcover : s ∪ t = Set.univ)
    (f : s → Y) (g : t → Y) (hf : Continuous f) (hg : Continuous g)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hcross : ∀ x : s, ∀ y : t, f x = g y ↔ (x : X) = (y : X)) :
    ∃ H : X ≃ₜ ↥(Set.range f ∪ Set.range g),
      (∀ x : s, (H x : Y) = f x) ∧ (∀ y : t, (H y : Y) = g y) := by
  classical
  have hmem (x : X) : x ∈ s ∨ x ∈ t := by
    have hx : x ∈ s ∪ t := hcover.symm ▸ Set.mem_univ x
    exact hx
  let F : X → Y := fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, (hmem x).resolve_left hx⟩
  have hFs (x : s) : F x = f x := by simp only [F, dite_eq_left x.property]
  have hFt (y : t) : F y = g y := by
    by_cases hy : (y : X) ∈ s
    · rw [show F y = f ⟨y, hy⟩ from hFs ⟨y, hy⟩]
      exact (hcross ⟨y, hy⟩ y).mpr rfl
    · simp only [F, dite_eq_right hy]
  have hcont : Continuous F := by
    rw [← continuousOn_univ, ← hcover]
    apply ContinuousOn.union_of_isClosed _ _ hs ht
    · rw [continuousOn_iff_continuous_domRestrict]
      exact hf.congr (fun x => (hFs x).symm)
    · rw [continuousOn_iff_continuous_domRestrict]
      exact hg.congr (fun y => (hFt y).symm)
  have hinj : Function.Injective F := by
    intro x y hxy
    rcases hmem x with hx | hx <;> rcases hmem y with hy | hy
    · have heq : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by rw [← hFs, ← hFs]; exact hxy
      exact congrArg Subtype.val (hfi heq)
    · apply (hcross ⟨x, hx⟩ ⟨y, hy⟩).mp
      rw [← hFs, ← hFt]
      exact hxy
    · apply Eq.symm
      apply (hcross ⟨y, hy⟩ ⟨x, hx⟩).mp
      rw [← hFs, ← hFt]
      exact hxy.symm
    · have heq : g ⟨x, hx⟩ = g ⟨y, hy⟩ := by rw [← hFt, ← hFt]; exact hxy
      exact congrArg Subtype.val (hgi heq)
  have hFmem (x : X) : F x ∈ Set.range f ∪ Set.range g := by
    rcases hmem x with hx | hx
    · exact Or.inl ⟨⟨x, hx⟩, (hFs ⟨x, hx⟩).symm⟩
    · exact Or.inr ⟨⟨x, hx⟩, (hFt ⟨x, hx⟩).symm⟩
  let G : X → ↥(Set.range f ∪ Set.range g) := fun x => ⟨F x, hFmem x⟩
  have hGbij : Function.Bijective G := by
    constructor
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · rintro ⟨y, hy⟩
      rcases hy with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact ⟨x, Subtype.ext (hFs x)⟩
      · exact ⟨x, Subtype.ext (hFt x)⟩
  let H : X ≃ₜ ↥(Set.range f ∪ Set.range g) :=
    (hcont.subtype_mk hFmem).homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hGbij)
  exact ⟨H, hFs, hFt⟩

/-- Helper toward Proposition 5.16: the upper closed half of the unit disk,
viewed as a closed subset of the disk. -/
@[expose] def polygonDiskUpperHalf : Set (Metric.closedBall (0 : ℂ) 1) :=
  {z | 0 ≤ (z : ℂ).im}

/-- Helper toward Proposition 5.16: the lower closed half of the unit disk,
viewed as a closed subset of the disk. -/
@[expose] def polygonDiskLowerHalf : Set (Metric.closedBall (0 : ℂ) 1) :=
  {z | (z : ℂ).im ≤ 0}

/-- Helper toward Proposition 5.16: the two closed half-disks cover the disk. -/
theorem polygonDiskUpperHalf_union_lowerHalf :
    polygonDiskUpperHalf ∪ polygonDiskLowerHalf = Set.univ := by
  ext z
  exact iff_true_intro (le_total 0 (z : ℂ).im)

/-- Helper toward Proposition 5.16: the shared half-disk seam is exactly
the real diameter, including both endpoints. -/
theorem polygonDiskUpperHalf_inter_lowerHalf :
    polygonDiskUpperHalf ∩ polygonDiskLowerHalf =
      {z : Metric.closedBall (0 : ℂ) 1 | (z : ℂ).im = 0} := by
  ext z
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.symm.le, h.le⟩⟩

/-- Helper toward Proposition 5.16: compatible charts on the upper and lower
half-disks glue to a chart of their union. Cross-chart coincidences must be
exactly the points of the common diameter, with the same parameter. The chart
also identifies the union of the two outer semicircle images with its boundary.
This theorem does not assert that arbitrary polygon disk charts have already
been reparameterized to meet this compatibility condition. -/
theorem exists_disk_chart_of_compatible_half_disk_charts
    (A B : Set ℂ) (f : polygonDiskUpperHalf ≃ₜ A) (g : polygonDiskLowerHalf ≃ₜ B)
    (hcross : ∀ x : polygonDiskUpperHalf, ∀ y : polygonDiskLowerHalf,
      (f x : ℂ) = (g y : ℂ) ↔
        (x : Metric.closedBall (0 : ℂ) 1) = (y : Metric.closedBall (0 : ℂ) 1)) :
    ∃ H : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥(A ∪ B),
      (∀ x : polygonDiskUpperHalf, (H x : ℂ) = (f x : ℂ)) ∧
      (∀ y : polygonDiskLowerHalf, (H y : ℂ) = (g y : ℂ)) ∧
      ∀ z : Metric.closedBall (0 : ℂ) 1,
        ((∃ x : polygonDiskUpperHalf, ‖((x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 ∧
            (f x : ℂ) = (H z : ℂ)) ∨
         (∃ y : polygonDiskLowerHalf, ‖((y : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 ∧
            (g y : ℂ) = (H z : ℂ))) ↔ ‖(z : ℂ)‖ = 1 := by
  have hs : IsClosed polygonDiskUpperHalf :=
    isClosed_le continuous_const (Complex.continuous_im.comp continuous_subtype_val)
  have ht : IsClosed polygonDiskLowerHalf :=
    isClosed_le (Complex.continuous_im.comp continuous_subtype_val) continuous_const
  let F : polygonDiskUpperHalf → ℂ := fun x => f x
  let G : polygonDiskLowerHalf → ℂ := fun y => g y
  have hFrange : Set.range F = A := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact (f x).property
    · intro hz
      exact ⟨f.symm ⟨z, hz⟩, congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)⟩
  have hGrange : Set.range G = B := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (g y).property
    · intro hz
      exact ⟨g.symm ⟨z, hz⟩, congrArg Subtype.val (g.apply_symm_apply ⟨z, hz⟩)⟩
  obtain ⟨H, hHf, hHg⟩ := exists_homeomorph_union_of_closed_cover
    polygonDiskUpperHalf polygonDiskLowerHalf hs ht polygonDiskUpperHalf_union_lowerHalf
    F G (continuous_subtype_val.comp f.continuous) (continuous_subtype_val.comp g.continuous)
    (Subtype.val_injective.comp f.injective) (Subtype.val_injective.comp g.injective) hcross
  have hunion : Set.range F ∪ Set.range G = A ∪ B := by rw [hFrange, hGrange]
  let K := H.trans (Homeomorph.setCongr hunion)
  have hKf (x : polygonDiskUpperHalf) : (K x : ℂ) = (f x : ℂ) := hHf x
  have hKg (y : polygonDiskLowerHalf) : (K y : ℂ) = (g y : ℂ) := hHg y
  refine ⟨K, hKf, hKg, ?_⟩
  intro z
  constructor
  · rintro (⟨x, hx, heq⟩ | ⟨y, hy, heq⟩)
    · have hval : (K x : ℂ) = (K z : ℂ) := (hKf x).trans heq
      have hparam := K.injective (Subtype.ext hval)
      simpa only [hparam] using hx
    · have hval : (K y : ℂ) = (K z : ℂ) := (hKg y).trans heq
      have hparam := K.injective (Subtype.ext hval)
      simpa only [hparam] using hy
  · intro hz
    rcases le_total 0 (z : ℂ).im with hpos | hneg
    · exact Or.inl ⟨⟨z, hpos⟩, hz, (hKf ⟨z, hpos⟩).symm⟩
    · exact Or.inr ⟨⟨z, hneg⟩, hz, (hKg ⟨z, hneg⟩).symm⟩

/-- Helper toward Proposition 5.16: a common diameter parameterization and
the assertion that the first chart meets the second piece exactly on its
diameter imply the cross-chart coincidence criterion used for gluing. -/
theorem half_disk_charts_cross_iff_of_seam
    (A B : Set ℂ) (f : polygonDiskUpperHalf ≃ₜ A) (g : polygonDiskLowerHalf ≃ₜ B)
    (hseam : ∀ x : polygonDiskUpperHalf,
      (f x : ℂ) ∈ B ↔ (((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0)
    (hagree : ∀ (z : Metric.closedBall (0 : ℂ) 1) (hz : (z : ℂ).im = 0),
      (f ⟨z, hz.symm.le⟩ : ℂ) = (g ⟨z, hz.le⟩ : ℂ)) :
    ∀ x : polygonDiskUpperHalf, ∀ y : polygonDiskLowerHalf,
      (f x : ℂ) = (g y : ℂ) ↔
        (x : Metric.closedBall (0 : ℂ) 1) = (y : Metric.closedBall (0 : ℂ) 1) := by
  intro x y
  constructor
  · intro heq
    have hxB : (f x : ℂ) ∈ B := heq.symm ▸ (g y).property
    have hxzero := (hseam x).mp hxB
    have hsame : (g ⟨x, hxzero.le⟩ : ℂ) = (g y : ℂ) :=
      (hagree x hxzero).symm.trans heq
    exact congrArg Subtype.val (g.injective (Subtype.ext hsame))
  · intro hxy
    have hy : (((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im ≤ 0 := hxy.symm ▸ y.property
    have hxzero := le_antisymm hy x.property
    have hyx : y = ⟨x, hxzero.le⟩ := Subtype.ext hxy.symm
    rw [hyx]
    exact hagree x hxzero

/-- Helper toward Proposition 5.16: two half-disk charts whose common arc
is exactly their compatibly parameterized diameter give a closed-disk chart
of the union, agreeing with both charts on their whole respective pieces. -/
theorem exists_disk_chart_of_half_disk_seam
    (A B : Set ℂ) (f : polygonDiskUpperHalf ≃ₜ A) (g : polygonDiskLowerHalf ≃ₜ B)
    (hseam : ∀ x : polygonDiskUpperHalf,
      (f x : ℂ) ∈ B ↔ (((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0)
    (hagree : ∀ (z : Metric.closedBall (0 : ℂ) 1) (hz : (z : ℂ).im = 0),
      (f ⟨z, hz.symm.le⟩ : ℂ) = (g ⟨z, hz.le⟩ : ℂ)) :
    ∃ H : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥(A ∪ B),
      (∀ x : polygonDiskUpperHalf, (H x : ℂ) = (f x : ℂ)) ∧
      (∀ y : polygonDiskLowerHalf, (H y : ℂ) = (g y : ℂ)) := by
  obtain ⟨H, hf, hg, _⟩ := exists_disk_chart_of_compatible_half_disk_charts A B f g
    (half_disk_charts_cross_iff_of_seam A B f g hseam hagree)
  exact ⟨H, hf, hg⟩

/-- Helper toward Proposition 5.16: a closed-disk chart with exact boundary
correspondence induces a circle homeomorphism onto that boundary. -/
theorem exists_boundary_homeomorph_of_disk_chart
    (S T : Set ℂ) (hT : T ⊆ S) (h : Metric.closedBall (0 : ℂ) 1 ≃ₜ S)
    (hb : ∀ z : Metric.closedBall (0 : ℂ) 1, (h z : ℂ) ∈ T ↔ ‖(z : ℂ)‖ = 1) :
    ∃ b : Circle ≃ₜ T, ∀ c : Circle,
      (b c : ℂ) = (h ⟨(c : ℂ), by
        simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]⟩ : ℂ) := by
  let j : Circle → Metric.closedBall (0 : ℂ) 1 := fun c =>
    ⟨c, by simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hmem (c : Circle) : (h (j c) : ℂ) ∈ T :=
    (hb (j c)).mpr (Circle.norm_coe c)
  let f : Circle → T := fun c => ⟨h (j c), hmem c⟩
  have hf : Continuous f := (continuous_subtype_val.comp (h.continuous.comp hj)).subtype_mk _
  have hfi : Function.Injective f := by
    intro c d hcd
    have heq : (h (j c) : ℂ) = (h (j d) : ℂ) :=
      congrArg (fun z : T => (z : ℂ)) hcd
    have hh : h (j c) = h (j d) := Subtype.ext heq
    exact Subtype.ext (congrArg (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ))
      (h.injective hh))
  have hfs : Function.Surjective f := by
    intro z
    let w := h.symm ⟨z, hT z.property⟩
    have hw : h w = ⟨z, hT z.property⟩ := h.apply_symm_apply _
    have hw1 : ‖(w : ℂ)‖ = 1 := (hb w).mp (by rw [hw]; exact z.property)
    let c : Circle := ⟨w, mem_sphere_zero_iff_norm.mpr hw1⟩
    have hjw : j c = w := Subtype.ext rfl
    refine ⟨c, Subtype.ext ?_⟩
    change (h (j c) : ℂ) = z
    rw [hjw, hw]
  let b : Circle ≃ₜ T := hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩)
  exact ⟨b, fun _ => rfl⟩

/-- Helper toward Proposition 5.16: any prescribed homeomorphism of the
boundaries of two already charted disks extends to their filled disks. The
extension uses the proved circle cone and does not require radial polygon
charts. Existence of the two input disk charts remains an explicit input to
this relative extension theorem. -/
theorem exists_disk_homeomorph_extending_boundary
    (S T U V : Set ℂ) (hT : T ⊆ S) (hV : V ⊆ U)
    (h : Metric.closedBall (0 : ℂ) 1 ≃ₜ S) (k : Metric.closedBall (0 : ℂ) 1 ≃ₜ U)
    (hb : ∀ z : Metric.closedBall (0 : ℂ) 1, (h z : ℂ) ∈ T ↔ ‖(z : ℂ)‖ = 1)
    (kb : ∀ z : Metric.closedBall (0 : ℂ) 1, (k z : ℂ) ∈ V ↔ ‖(z : ℂ)‖ = 1)
    (f : T ≃ₜ V) :
    ∃ H : S ≃ₜ U, ∀ x : T, (H ⟨x, hT x.property⟩ : ℂ) = (f x : ℂ) := by
  obtain ⟨b, hbapply⟩ := exists_boundary_homeomorph_of_disk_chart S T hT h hb
  obtain ⟨b', hb'apply⟩ := exists_boundary_homeomorph_of_disk_chart U V hV k kb
  let e : Circle ≃ₜ Circle := (b.trans f).trans b'.symm
  let E := starConeClosedBallHomeomorph e
  let H : S ≃ₜ U := h.symm.trans (E.trans k)
  refine ⟨H, ?_⟩
  intro x
  let c := b.symm x
  have hcx : b c = x := b.apply_symm_apply x
  let z : Metric.closedBall (0 : ℂ) 1 :=
    ⟨c, by simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]⟩
  have hhz : h z = ⟨x, hT x.property⟩ :=
    Subtype.ext ((hbapply c).symm.trans (congrArg Subtype.val hcx))
  have hinv : h.symm ⟨x, hT x.property⟩ = z := by rw [← hhz, h.symm_apply_apply]
  change (k (E (h.symm ⟨x, hT x.property⟩)) : ℂ) = _
  rw [hinv]
  have hEz : E z = ⟨(e c : ℂ), by
      simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]⟩ :=
    starConeClosedBallHomeomorph_apply_circle e c
  rw [hEz, ← hb'apply]
  have hec : b' (e c) = f x := by
    change b' (b'.symm (f (b c))) = f x
    rw [b'.apply_symm_apply, hcx]
  exact congrArg Subtype.val hec

/-- Helper toward Proposition 5.16: the closed upper half-disk used in
the gluing model is itself a closed disk. Its entire planar boundary consists
of the outer semicircle and the real diameter, with both endpoints retained. -/
theorem exists_upper_half_disk_chart :
    ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ polygonDiskUpperHalf,
      ∀ z : Metric.closedBall (0 : ℂ) 1,
        (‖(((h z : polygonDiskUpperHalf) : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 ∨
          ((((h z : polygonDiskUpperHalf) : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0) ↔
          ‖(z : ℂ)‖ = 1 := by
  let s : Set ℂ := Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}
  have hs : IsClosed s := Metric.isClosed_closedBall.inter
    (isClosed_le continuous_const Complex.continuous_im)
  have hc : Convex ℝ s := (convex_closedBall (0 : ℂ) 1).inter (convex_halfSpace_im_ge 0)
  have hcompact : IsCompact s := (isCompact_closedBall (0 : ℂ) 1).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hne : (_root_.interior s).Nonempty := by
    let p : ℂ := (1 / 2 : ℝ) • Complex.I
    have hpball : p ∈ Metric.ball (0 : ℂ) 1 := by
      norm_num [p, Metric.mem_ball, dist_zero_right, norm_smul]
    have hpim : 0 < p.im := by norm_num [p, Complex.smul_im]
    have hopen : IsOpen (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < z.im}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hsub : Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < z.im} ⊆ s :=
      fun z hz => ⟨Metric.ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
    exact ⟨p, mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hopen.mem_nhds ⟨hpball, hpim⟩) hsub)⟩
  obtain ⟨H, hd, hb⟩ := exists_convex_plane_chart s hc hne hcompact.isBounded
  have hd' : H '' Metric.closedBall (0 : ℂ) 1 = s := by
    simpa only [hs.closure_eq] using hd
  let k : Metric.closedBall (0 : ℂ) 1 ≃ₜ s :=
    (H.image (Metric.closedBall (0 : ℂ) 1)).trans (Homeomorph.setCongr hd')
  let e : s ≃ₜ polygonDiskUpperHalf := {
    toFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
    invFun := fun x => ⟨(x : Metric.closedBall (0 : ℂ) 1), ⟨x.val.property, x.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨k.trans e, ?_⟩
  intro z
  have hHz : H (z : ℂ) ∈ s := hd' ▸ Set.mem_image_of_mem H z.property
  have hfront : H (z : ℂ) ∈ frontier s ↔ ‖(z : ℂ)‖ = 1 := by
    rw [← hb]
    constructor
    · rintro ⟨w, hw, heq⟩
      have heq' : w = (z : ℂ) := H.injective heq
      simpa only [heq', Metric.mem_sphere, dist_zero_right] using hw
    · intro hz
      exact ⟨z, by simpa only [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩
  change (‖H (z : ℂ)‖ = 1 ∨ (H (z : ℂ)).im = 0) ↔ _
  rw [← hfront, frontier, hs.closure_eq]
  have hinter : _root_.interior s = Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | 0 < w.im} := by
    change _root_.interior (Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | 0 ≤ w.im}) = _
    rw [interior_inter, interior_closedBall (0 : ℂ) one_ne_zero,
      Complex.interior_setOfPred_le_im]
  rw [hinter]
  change (‖H (z : ℂ)‖ = 1 ∨ (H (z : ℂ)).im = 0) ↔
    H (z : ℂ) ∈ s ∧ ¬ (H (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 ∧ 0 < (H (z : ℂ)).im)
  have hn : ‖H (z : ℂ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hHz.1
  simp only [Metric.mem_ball, dist_zero_right]
  constructor
  · intro heq
    refine ⟨hHz, ?_⟩
    rintro ⟨hlt, him⟩
    rcases heq with h | h
    · exact (ne_of_lt hlt) h
    · exact (ne_of_gt him) h
  · rintro ⟨_, hnot⟩
    by_cases heq : ‖H (z : ℂ)‖ = 1
    · exact Or.inl heq
    · right
      have hlt : ‖H (z : ℂ)‖ < 1 := lt_of_le_of_ne hn heq
      exact le_antisymm (not_lt.mp (fun him => hnot ⟨hlt, him⟩)) hHz.2

/-- Helper toward Proposition 5.16: negation identifies the two closed
half-disks and preserves their entire planar boundaries. -/
@[expose] def polygonDiskHalfNegHomeomorph : polygonDiskUpperHalf ≃ₜ polygonDiskLowerHalf where
  toFun x := ⟨⟨-((x : Metric.closedBall (0 : ℂ) 1) : ℂ), by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using x.val.property⟩,
    by
      change (-((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im ≤ 0
      simpa only [Complex.neg_im] using neg_nonpos.mpr x.property⟩
  invFun x := ⟨⟨-((x : Metric.closedBall (0 : ℂ) 1) : ℂ), by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using x.val.property⟩,
    by
      change 0 ≤ (-((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im
      simpa only [Complex.neg_im] using neg_nonneg.mpr x.property⟩
  left_inv x := Subtype.ext (Subtype.ext (neg_neg _))
  right_inv x := Subtype.ext (Subtype.ext (neg_neg _))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Helper toward Proposition 5.16: the lower half-disk also has a disk chart
with exact outer-semicircle and diameter boundary correspondence. -/
theorem exists_lower_half_disk_chart :
    ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ polygonDiskLowerHalf,
      ∀ z : Metric.closedBall (0 : ℂ) 1,
        (‖(((h z : polygonDiskLowerHalf) : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 ∨
          ((((h z : polygonDiskLowerHalf) : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0) ↔
          ‖(z : ℂ)‖ = 1 := by
  obtain ⟨h, hb⟩ := exists_upper_half_disk_chart
  refine ⟨h.trans polygonDiskHalfNegHomeomorph, ?_⟩
  intro z
  change (‖-((h z : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 ∨
    (-((h z : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0) ↔ _
  simpa only [norm_neg, Complex.neg_im, neg_eq_zero] using hb z

/-- Helper toward Proposition 5.16: a strict lexicographic minimum of two
points cannot belong to their closed segment. Equal real coordinates are
resolved by the imaginary coordinate, so vertical edges are included. -/
theorem not_mem_segment_of_lexicographic_min (u v w : ℂ)
    (hu : v.re < u.re ∨ v.re = u.re ∧ v.im < u.im)
    (hw : v.re < w.re ∨ v.re = w.re ∧ v.im < w.im) :
    v ∉ segment ℝ u w := by
  have hvu : v ≠ u := by
    intro h
    subst u
    rcases hu with h | ⟨_, h⟩ <;> exact (lt_irrefl _) h
  have hvw : v ≠ w := by
    intro h
    subst w
    rcases hw with h | ⟨_, h⟩ <;> exact (lt_irrefl _) h
  rintro ⟨a, b, ha, hb, hab, heq⟩
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith only [hab, ha0]
    have heq' : w = v := by simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using heq
    exact hvw heq'.symm
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith only [hab, hb0]
    have heq' : u = v := by simpa only [ha1, hb0, zero_smul, one_smul, add_zero] using heq
    exact hvu heq'.symm
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hure : v.re ≤ u.re := hu.elim le_of_lt (fun h => h.1.le)
  have hwre : v.re ≤ w.re := hw.elim le_of_lt (fun h => h.1.le)
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hre
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at him
  have hsumre : a * v.re + b * v.re = v.re := by rw [← add_mul, hab, one_mul]
  have hsumim : a * v.im + b * v.im = v.im := by rw [← add_mul, hab, one_mul]
  have haΔ : 0 ≤ a * (u.re - v.re) := mul_nonneg ha (sub_nonneg.mpr hure)
  have hbΔ : 0 ≤ b * (w.re - v.re) := mul_nonneg hb (sub_nonneg.mpr hwre)
  have hzero : a * (u.re - v.re) + b * (w.re - v.re) = 0 := by
    nlinarith only [hre, hsumre]
  have hau : a * (u.re - v.re) = 0 := le_antisymm (by linarith only [hzero, hbΔ]) haΔ
  have hbw : b * (w.re - v.re) = 0 := le_antisymm (by linarith only [hzero, haΔ]) hbΔ
  have hue : v.re = u.re := (sub_eq_zero.mp ((mul_eq_zero.mp hau).resolve_left ha0)).symm
  have hwe : v.re = w.re := (sub_eq_zero.mp ((mul_eq_zero.mp hbw).resolve_left hb0)).symm
  have hui : v.im < u.im := hu.elim (fun h => False.elim ((ne_of_lt h) hue)) And.right
  have hwi : v.im < w.im := hw.elim (fun h => False.elim ((ne_of_lt h) hwe)) And.right
  have hlt := add_lt_add (mul_lt_mul_of_pos_left hui hap) (mul_lt_mul_of_pos_left hwi hbp)
  linarith only [hlt, hsumim, him]

/-- Helper toward Proposition 5.16: at a strict lexicographic minimum, two
nonoverlapping incident polygon edges form a nondegenerate triangle. -/
theorem not_collinear_of_lexicographic_min_of_segments_inter (u v w : ℂ)
    (hu : v.re < u.re ∨ v.re = u.re ∧ v.im < u.im)
    (hw : v.re < w.re ∨ v.re = w.re ∧ v.im < w.im)
    (hinter : segment ℝ u v ∩ segment ℝ v w = {v}) :
    ¬ Collinear ℝ ({u, v, w} : Set ℂ) := by
  intro hcol
  have hvu : v ≠ u := by
    intro h
    subst u
    rcases hu with h | ⟨_, h⟩ <;> exact (lt_irrefl _) h
  have hvw : v ≠ w := by
    intro h
    subst w
    rcases hw with h | ⟨_, h⟩ <;> exact (lt_irrefl _) h
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact not_mem_segment_of_lexicographic_min u v w hu hw h.mem_segment
  · have hm : w ∈ ({v} : Set ℂ) := hinter ▸
        ⟨by simpa only [segment_symm] using h.mem_segment, right_mem_segment ℝ v w⟩
    exact hvw (Set.mem_singleton_iff.mp hm).symm
  · have hm : u ∈ ({v} : Set ℂ) := hinter ▸
        ⟨left_mem_segment ℝ u v, by simpa only [segment_symm] using h.mem_segment⟩
    exact hvu (Set.mem_singleton_iff.mp hm).symm

/-- Helper toward Proposition 5.16: a nonempty finite set of plane points
has a strict lexicographic minimum, with imaginary coordinates breaking ties. -/
theorem exists_lexicographic_min_of_finite (s : Set ℂ) (hs : s.Finite) (hne : s.Nonempty) :
    ∃ v ∈ s, ∀ u ∈ s, u ≠ v →
      v.re < u.re ∨ v.re = u.re ∧ v.im < u.im := by
  obtain ⟨p, hp, hpre⟩ := Set.exists_min_image s Complex.re hs hne
  let t : Set ℂ := {z ∈ s | z.re = p.re}
  have ht : t.Finite := hs.subset (fun _ hz => hz.1)
  obtain ⟨v, hv, hvim⟩ := Set.exists_min_image t Complex.im ht ⟨p, hp, rfl⟩
  refine ⟨v, hv.1, ?_⟩
  intro u hu huv
  have hle : v.re ≤ u.re := hv.2 ▸ hpre u hu
  by_cases heq : v.re = u.re
  · right
    refine ⟨heq, lt_of_le_of_ne (hvim u ⟨hu, heq.symm.trans hv.2⟩) ?_⟩
    intro him
    exact huv (Complex.ext heq.symm him.symm)
  · exact Or.inl (lt_of_le_of_ne hle heq)

namespace Polyline

/-- Helper toward Proposition 5.16: the two incident edges at every cyclic
vertex meet exactly at that vertex, including at the repeated root. -/
theorem incident_segments_inter_eq_singleton_cyclic (c : Polyline) (hc : c.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < c.points.length) :
    let k := if i = 0 then c.points.length - 2 else i - 1
    segment ℝ (c.point k) (c.point i) ∩
      segment ℝ (c.point i) (c.point (i + 1)) = {c.point i} := by
  dsimp only
  by_cases hi0 : i = 0
  · subst i
    simp only [ite_true]
    have hlast : c.points.length - 2 + 1 = c.points.length - 1 := by have := hc.1; omega
    have hroot := hc.2.1
    have hw := hc.2.2.2.2.2
    simpa only [segmentAt, hlast, ← hroot, Set.inter_comm] using hw
  · simp only [ite_eq_right hi0]
    have hidx : i - 1 + 1 = i := by omega
    have hidx2 : i - 1 + 2 = i + 1 := by omega
    have hadj := hc.2.2.2.1 (i - 1) (by omega)
    simpa only [segmentAt, hidx, hidx2] using hadj

/-- Helper toward Proposition 5.16: every cyclically simple polygon has an
extreme vertex whose two incident edges form a nondegenerate candidate ear
triangle. This does not yet assert visibility of the opposite diagonal. -/
theorem exists_noncollinear_lexicographic_min_vertex (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ i : ℕ, i + 1 < c.points.length ∧
      (∀ j : ℕ, j + 1 < c.points.length → c.point j ≠ c.point i →
        (c.point i).re < (c.point j).re ∨
          (c.point i).re = (c.point j).re ∧ (c.point i).im < (c.point j).im) ∧
      let k := if i = 0 then c.points.length - 2 else i - 1
      ¬ Collinear ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ) := by
  let s : Set ℂ := c.point '' {j : ℕ | j < c.points.length - 1}
  have hs : s.Finite := (Set.finite_lt_nat (c.points.length - 1)).image c.point
  have h0 : 0 < c.points.length - 1 := by have := hc.1; omega
  obtain ⟨v, ⟨i, hi, hiv⟩, hmin⟩ := exists_lexicographic_min_of_finite s hs
    ⟨c.point 0, 0, h0, rfl⟩
  subst v
  change i < c.points.length - 1 at hi
  have hi' : i + 1 < c.points.length := by omega
  have hmin' (j : ℕ) (hj : j + 1 < c.points.length) (hne : c.point j ≠ c.point i) :
      (c.point i).re < (c.point j).re ∨
        (c.point i).re = (c.point j).re ∧ (c.point i).im < (c.point j).im :=
    hmin (c.point j) ⟨j, show j < c.points.length - 1 by omega, rfl⟩ hne
  refine ⟨i, hi', hmin', ?_⟩
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hk : k + 1 < c.points.length := by dsimp only [k]; split_ifs <;> omega
  have hkv : c.point (k + 1) = c.point i := by
    dsimp only [k]
    split_ifs with h
    · rw [show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm.trans (congrArg c.point h.symm)
    · congr 1
      omega
  have hkne : c.point k ≠ c.point i := by rw [← hkv]; exact hc.2.2.1 k hk
  have hnne : c.point (i + 1) ≠ c.point i := (hc.2.2.1 i hi').symm
  apply not_collinear_of_lexicographic_min_of_segments_inter
    (c.point k) (c.point i) (c.point (i + 1)) (hmin' k hk hkne) ?_
    (incident_segments_inter_eq_singleton_cyclic c hc i hi')
  by_cases hn : i + 2 < c.points.length
  · exact hmin' (i + 1) hn hnne
  · have hnext : i + 1 = c.points.length - 1 := by omega
    rw [hnext, ← hc.2.1]
    apply hmin' 0 (by have := hc.1; omega)
    simpa only [hnext, hc.2.1] using hnne

/-- Helper toward Proposition 5.16: some nondegenerate candidate ear triangle
has a nonempty open triangular sector at its tip disjoint from the whole
polygon boundary. Identifying its complementary side as `inside`, and extending
visibility to the opposite diagonal, are not asserted here. -/
theorem exists_local_triangle_sector_avoiding_image_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) :
    ∃ i : ℕ, i + 1 < c.points.length ∧
      let k := if i = 0 then c.points.length - 2 else i - 1
      ¬ Collinear ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ) ∧
      ∃ r : ℝ, 0 < r ∧
        (Metric.ball (c.point i) r ∩ _root_.interior
          (convexHull ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ))).Nonempty ∧
        Disjoint (Metric.ball (c.point i) r ∩ _root_.interior
          (convexHull ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ))) c.image := by
  obtain ⟨i, hi, _, hnc⟩ := exists_noncollinear_lexicographic_min_vertex c hc
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hkv : c.point (k + 1) = c.point i := by
    dsimp only [k]
    split_ifs with h
    · rw [show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm.trans (congrArg c.point h.symm)
    · congr 1
      omega
  obtain ⟨r, hr, hlocal⟩ := exists_pos_ball_image_eq_incident_segments_cyclic c hc i hi
  refine ⟨i, hi, hnc, r, hr, ?_, ?_⟩
  · have hv : c.point i ∈ closure (_root_.interior
        (convexHull ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ))) := by
      rw [closure_triangle_interior _ _ _ hnc]
      exact subset_convexHull ℝ _ (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
    obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hv r hr
    exact ⟨z, ⟨by simpa only [Metric.mem_ball, dist_comm] using hdist, hz⟩⟩
  · apply Set.disjoint_left.mpr
    intro z hz hzimage
    have hsegs := (hlocal z hz.1).mp hzimage
    change z ∈ c.segmentAt k ∪ c.segmentAt i at hsegs
    have hboundary : z ∈ segment ℝ (c.point k) (c.point i) ∪
        segment ℝ (c.point i) (c.point (i + 1)) ∪
        segment ℝ (c.point (i + 1)) (c.point k) := by
      left
      simpa only [segmentAt, hkv] using hsegs
    have hfront : z ∈ frontier (_root_.interior
        (convexHull ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ))) :=
      (frontier_triangle_interior _ _ _ hnc).symm ▸ hboundary
    exact hfront.2 (by simpa only [interior_interior] using hz.2)

end Polyline
































































end DirectedDistances.PlanarMap

