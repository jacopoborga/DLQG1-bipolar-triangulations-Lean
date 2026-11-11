/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLPolygonDiskChart6
public import DirectedDistances.PlanarMap.D39PLDiskArcGluing5

/-! Helpers toward Proposition 5.16: compatible boundary arc gluing. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Set Topology

/-- Helper toward Proposition 5.16: two parameterized closed arcs glue when
both intersections consist precisely of their compatibly ordered endpoints. -/
theorem exists_homeomorph_of_two_parameterized_arcs
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) (hcover : s ∪ t = univ)
    (d : Icc (-1 : ℝ) 1 ≃ₜ s) (c : Icc (-1 : ℝ) 1 ≃ₜ t)
    (hc0 : (c ⟨-1, by norm_num⟩ : X) = (d ⟨1, by norm_num⟩ : X))
    (hc1 : (c ⟨1, by norm_num⟩ : X) = (d ⟨-1, by norm_num⟩ : X))
    (hmeet : s ∩ t = {(d ⟨-1, by norm_num⟩ : X), (d ⟨1, by norm_num⟩ : X)})
    (a b : Set Y) (phi : Icc (-1 : ℝ) 1 ≃ₜ a) (psi : Icc (-1 : ℝ) 1 ≃ₜ b)
    (hp0 : (psi ⟨-1, by norm_num⟩ : Y) = (phi ⟨1, by norm_num⟩ : Y))
    (hp1 : (psi ⟨1, by norm_num⟩ : Y) = (phi ⟨-1, by norm_num⟩ : Y))
    (hmeet' : a ∩ b = {(phi ⟨-1, by norm_num⟩ : Y), (phi ⟨1, by norm_num⟩ : Y)}) :
    ∃ H : X ≃ₜ ↥(a ∪ b),
      (∀ u, (H (d u) : Y) = (phi u : Y)) ∧
      (∀ u, (H (c u) : Y) = (psi u : Y)) := by
  let f : s → Y := fun x => phi (d.symm x)
  let g : t → Y := fun x => psi (c.symm x)
  have fi : Function.Injective f := Subtype.val_injective.comp (phi.injective.comp d.symm.injective)
  have gi : Function.Injective g := Subtype.val_injective.comp (psi.injective.comp c.symm.injective)
  have fd (u) : f (d u) = (phi u : Y) := by simp [f]
  have gc (u) : g (c u) = (psi u : Y) := by simp [g]
  have cross : ∀ x : s, ∀ y : t, f x = g y ↔ (x : X) = (y : X) := by
    intro x y
    constructor
    · intro heq
      have hm : f x ∈ a ∩ b := ⟨(phi _).property, heq ▸ (psi _).property⟩
      rw [hmeet'] at hm
      rcases hm with hm | hm
      · have hx : x = d ⟨-1, by norm_num⟩ := fi (hm.trans (fd _).symm)
        have hy : y = c ⟨1, by norm_num⟩ := gi (heq.symm.trans (hm.trans hp1.symm) |>.trans (gc _).symm)
        rw [hx, hy, hc1]
      · have hx : x = d ⟨1, by norm_num⟩ := fi (hm.trans (fd _).symm)
        have hy : y = c ⟨-1, by norm_num⟩ := gi (heq.symm.trans (hm.trans hp0.symm) |>.trans (gc _).symm)
        rw [hx, hy, hc0]
    · intro heq
      have hm : (x : X) ∈ s ∩ t := ⟨x.property, heq.symm ▸ y.property⟩
      rw [hmeet] at hm
      rcases hm with hm | hm
      · have hx : x = d ⟨-1, by norm_num⟩ := Subtype.ext hm
        have hy : y = c ⟨1, by norm_num⟩ := Subtype.ext (heq.symm.trans (hm.trans hc1.symm))
        rw [hx, hy, fd, gc, hp1]
      · have hx : x = d ⟨1, by norm_num⟩ := Subtype.ext hm
        have hy : y = c ⟨-1, by norm_num⟩ := Subtype.ext (heq.symm.trans (hm.trans hc0.symm))
        rw [hx, hy, fd, gc, hp0]
  obtain ⟨H, hHf, hHg⟩ := exists_homeomorph_union_of_closed_cover s t hs ht hcover f g
    (continuous_subtype_val.comp (phi.continuous.comp d.symm.continuous))
    (continuous_subtype_val.comp (psi.continuous.comp c.symm.continuous)) fi gi cross
  have fr : range f = a := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact (phi _).property
    · intro hy
      exact ⟨d (phi.symm ⟨y, hy⟩), (fd _).trans (congrArg Subtype.val (phi.apply_symm_apply _))⟩
  have gr : range g = b := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact (psi _).property
    · intro hy
      exact ⟨c (psi.symm ⟨y, hy⟩), (gc _).trans (congrArg Subtype.val (psi.apply_symm_apply _))⟩
  refine ⟨H.trans (Homeomorph.setCongr (by rw [fr, gr])), ?_, ?_⟩
  · intro u; exact (hHf _).trans (fd u)
  · intro u; exact (hHg _).trans (gc u)

/-- Helper toward Proposition 5.16: the real coordinate parameterizes the
entire diameter piece of the model boundary. -/
@[expose] def upperBoundaryDiameterHomeomorph :
    Icc (-1 : ℝ) 1 ≃ₜ polygonDiskUpperHalfBoundaryDiameter where
  toFun t := ⟨⟨polygonDiskUpperHalfDiameterPoint t, Or.inr (by
    simp [polygonDiskUpperHalfDiameterPoint])⟩, by
      simp [polygonDiskUpperHalfBoundaryDiameter, polygonDiskUpperHalfDiameterPoint]⟩
  invFun x := ⟨((x.1.1 : Metric.closedBall (0 : ℂ) 1) : ℂ).re, by
    have hn : ‖((x.1.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.1.1.val.property
    have hr := Complex.abs_re_le_norm ((x.1.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)
    exact ⟨by linarith [(abs_le.mp (hr.trans hn)).1], (abs_le.mp (hr.trans hn)).2⟩⟩
  left_inv t := by apply Subtype.ext; simp [polygonDiskUpperHalfDiameterPoint]
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    apply Complex.ext
    · simp [polygonDiskUpperHalfDiameterPoint]
    · simpa [polygonDiskUpperHalfDiameterPoint] using x.property.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_re.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val)))

/-- Helper toward Proposition 5.16: the circle semicircle and the model
boundary semicircle have identical underlying complex coordinates. -/
@[expose] def upperBoundarySemicircleHomeomorph :
    {c : Circle // 0 ≤ (c : ℂ).im} ≃ₜ polygonDiskUpperHalfBoundarySemicircle where
  toFun c := ⟨⟨⟨⟨(c.1 : ℂ), by
      simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]⟩,
      c.property⟩, Or.inl (Circle.norm_coe _)⟩, Circle.norm_coe _⟩
  invFun x := ⟨⟨((x.1.1 : Metric.closedBall (0 : ℂ) 1) : ℂ),
      mem_sphere_zero_iff_norm.mpr x.property⟩, x.1.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (show Continuous (fun c : {c : Circle // 0 ≤ (c : ℂ).im} => (c.1 : ℂ)) from
      continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- Helper toward Proposition 5.16: the model boundary is the union of two
intervals meeting just at their oppositely ordered endpoints. -/
theorem exists_upper_boundary_arc_parameters :
    ∃ c : Icc (-1 : ℝ) 1 ≃ₜ polygonDiskUpperHalfBoundarySemicircle,
      (c ⟨-1, by norm_num⟩ : polygonDiskUpperHalfBoundary) =
        (upperBoundaryDiameterHomeomorph ⟨1, by norm_num⟩ : polygonDiskUpperHalfBoundary) ∧
      (c ⟨1, by norm_num⟩ : polygonDiskUpperHalfBoundary) =
        (upperBoundaryDiameterHomeomorph ⟨-1, by norm_num⟩ : polygonDiskUpperHalfBoundary) ∧
      polygonDiskUpperHalfBoundaryDiameter ∩ polygonDiskUpperHalfBoundarySemicircle =
        {(upperBoundaryDiameterHomeomorph ⟨-1, by norm_num⟩ : polygonDiskUpperHalfBoundary),
         (upperBoundaryDiameterHomeomorph ⟨1, by norm_num⟩ : polygonDiskUpperHalfBoundary)} := by
  obtain ⟨e, he0, he1⟩ := exists_homeomorph_Icc_upper_semicircle
  let c := e.trans upperBoundarySemicircleHomeomorph
  refine ⟨c, ?_, ?_, ?_⟩
  · change (upperBoundarySemicircleHomeomorph (e ⟨-1, by norm_num⟩) :
      polygonDiskUpperHalfBoundary) = _
    rw [he0]
    rfl
  · change (upperBoundarySemicircleHomeomorph (e ⟨1, by norm_num⟩) :
      polygonDiskUpperHalfBoundary) = _
    rw [he1]
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change (↑(-1 : Circle) : ℂ) = ((-1 : ℝ) : ℂ)
    simp
  · ext x
    constructor
    · rintro ⟨hx, hn⟩
      change (((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0 at hx
      change ‖((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 at hn
      have hz : ((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ) =
          ((((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)).re : ℂ) := by
        apply Complex.ext <;> simp [hx]
      rw [hz, Complex.norm_real, Real.norm_eq_abs] at hn
      have hr : (((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)).re = -1 ∨
          (((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)).re = 1 := by
        rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with h | h
        · exact Or.inr h
        · exact Or.inl h
      rcases hr with hr | hr
      · left
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        apply Complex.ext <;> simp [upperBoundaryDiameterHomeomorph,
          polygonDiskUpperHalfDiameterPoint, hr, hx]
      · right
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        apply Complex.ext <;> simp [upperBoundaryDiameterHomeomorph,
          polygonDiskUpperHalfDiameterPoint, hr, hx]
    · intro hx
      rcases hx with hx | hx <;> subst x <;>
        constructor <;> norm_num [polygonDiskUpperHalfBoundaryDiameter,
          polygonDiskUpperHalfBoundarySemicircle, upperBoundaryDiameterHomeomorph,
          polygonDiskUpperHalfDiameterPoint]

/-- Helper toward Proposition 5.16: a prescribed proper boundary arc is the
diameter of a model-boundary homeomorphism; the other arc is its semicircle. -/
theorem exists_upper_half_boundary_homeomorph_for_arc
    (S T gamma : Set ℂ) (hT : T ⊆ S)
    (h : Metric.closedBall (0 : ℂ) 1 ≃ₜ S)
    (hb : ∀ z : Metric.closedBall (0 : ℂ) 1,
      (h z : ℂ) ∈ T ↔ ‖(z : ℂ)‖ = 1)
    (hgamma : gamma ⊆ T) (phi : Icc (-1 : ℝ) 1 ≃ₜ gamma)
    (hproper : gamma ≠ T) :
    ∃ f : polygonDiskUpperHalfBoundary ≃ₜ T,
      (∀ t : Icc (-1 : ℝ) 1,
        (f ⟨polygonDiskUpperHalfDiameterPoint t, Or.inr (by
          simp [polygonDiskUpperHalfDiameterPoint])⟩ : ℂ) = (phi t : ℂ)) ∧
      range (fun z : {x : polygonDiskUpperHalf //
          ‖((x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1} =>
        (f ⟨z.1, Or.inl z.2⟩ : ℂ)) = closure (T \ gamma) := by
  have hu : IsClosed polygonDiskUpperHalf :=
    isClosed_le continuous_const (Complex.continuous_im.comp continuous_subtype_val)
  have : CompactSpace polygonDiskUpperHalf := isCompact_iff_compactSpace.mp hu.isCompact
  have hbd : IsClosed {x : polygonDiskUpperHalf |
      ‖((x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 ∨
        (((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0} :=
    (isClosed_eq (continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val))
      continuous_const).union
      (isClosed_eq (Complex.continuous_im.comp
        (continuous_subtype_val.comp continuous_subtype_val)) continuous_const)
  have : CompactSpace polygonDiskUpperHalfBoundary := isCompact_iff_compactSpace.mp hbd.isCompact
  obtain ⟨c, hc0, hc1, hm⟩ := exists_upper_boundary_arc_parameters
  obtain ⟨psi, hp0, hp1, hm'⟩ :=
    exists_boundary_subtype_complement_homeomorph S T gamma hT h hb hgamma phi hproper
  obtain ⟨hs, ht, hcover⟩ := polygonDiskUpperHalfBoundary_closed_cover
  obtain ⟨F, hFd, hFc⟩ := exists_homeomorph_of_two_parameterized_arcs
    _ _ hs ht hcover upperBoundaryDiameterHomeomorph c hc0 hc1 hm
    gamma (closure (T \ gamma)) phi psi hp0 hp1 hm'
  obtain ⟨b, _⟩ := exists_boundary_homeomorph_of_disk_chart S T hT h hb
  have hr : range (fun z : Circle => (b z : ℂ)) = T := by
    ext z
    constructor
    · rintro ⟨z, rfl⟩; exact (b z).property
    · intro hz
      exact ⟨b.symm ⟨z, hz⟩, congrArg Subtype.val (b.apply_symm_apply _)⟩
  have hTc : IsClosed T := by
    rw [← hr]
    exact (isCompact_range (continuous_subtype_val.comp b.continuous)).isClosed
  have hcl : closure (T \ gamma) ⊆ T := closure_minimal sdiff_subset hTc
  have heq : gamma ∪ closure (T \ gamma) = T := by
    apply Subset.antisymm (union_subset hgamma hcl)
    intro z hz
    by_cases hzg : z ∈ gamma
    · exact Or.inl hzg
    · exact Or.inr (subset_closure ⟨hz, hzg⟩)
  let f := F.trans (Homeomorph.setCongr heq)
  refine ⟨f, hFd, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    let y : polygonDiskUpperHalfBoundarySemicircle := ⟨⟨x.1, Or.inl x.2⟩, x.2⟩
    have he : (f y : ℂ) = (psi (c.symm y) : ℂ) := by
      change (F y : ℂ) = _
      simpa only [c.apply_symm_apply] using hFc (c.symm y)
    change (f y : ℂ) ∈ closure (T \ gamma)
    rw [he]
    exact (psi (c.symm y)).property
  · intro hz
    obtain ⟨u, hu⟩ := psi.surjective ⟨z, hz⟩
    refine ⟨⟨(c u).1.1, (c u).property⟩, ?_⟩
    exact (hFc u).trans (congrArg Subtype.val hu)

/-- Helper toward Proposition 5.16: the upper half-disk as a planar subset,
with all geometric points unchanged. -/
@[expose] def upperHalfPlanarHomeomorph : polygonDiskUpperHalf ≃ₜ
    ↥(Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}) where
  toFun x := ⟨(x : Metric.closedBall (0 : ℂ) 1), x.val.property, x.property⟩
  invFun x := ⟨⟨x, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Helper toward Proposition 5.16: a boundary homeomorphism of the upper
half-disk extends across its filled planar model. -/
theorem exists_upper_half_extension
    (S T : Set ℂ) (hT : T ⊆ S)
    (h : Metric.closedBall (0 : ℂ) 1 ≃ₜ S)
    (hb : ∀ z : Metric.closedBall (0 : ℂ) 1,
      (h z : ℂ) ∈ T ↔ ‖(z : ℂ)‖ = 1)
    (f : polygonDiskUpperHalfBoundary ≃ₜ T) :
    ∃ H : polygonDiskUpperHalf ≃ₜ S,
      ∀ x : polygonDiskUpperHalfBoundary, (H x.1 : ℂ) = (f x : ℂ) := by
  let U : Set ℂ := Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}
  let V : Set ℂ := {z | z ∈ U ∧ (‖z‖ = 1 ∨ z.im = 0)}
  let e : polygonDiskUpperHalf ≃ₜ U := upperHalfPlanarHomeomorph
  let b : polygonDiskUpperHalfBoundary ≃ₜ V := {
    toFun := fun x => ⟨((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ),
      ⟨x.1.val.property, x.1.property⟩, x.property⟩
    invFun := fun x => ⟨⟨⟨x, x.property.1.1⟩, x.property.1.2⟩, x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun := ((continuous_subtype_val.subtype_mk _).subtype_mk _).subtype_mk _ }
  obtain ⟨k, hk⟩ := exists_upper_half_disk_chart
  have hV : V ⊆ U := fun _ hx => hx.1
  have kb : ∀ z : Metric.closedBall (0 : ℂ) 1,
      ((k.trans e) z : ℂ) ∈ V ↔ ‖(z : ℂ)‖ = 1 := by
    intro z
    exact ⟨fun hz => (hk z).mp hz.2,
      fun hz => ⟨(e (k z)).property, (hk z).mpr hz⟩⟩
  obtain ⟨H, hH⟩ := exists_disk_homeomorph_extending_boundary U V S T hV hT
    (k.trans e) h kb hb (b.symm.trans f)
  refine ⟨e.trans H, ?_⟩
  intro x
  exact hH (b x)

/-- Helper toward Proposition 5.16: half-disk normalization with a prescribed
parameter on its diameter and the exact complementary outer arc. -/
theorem exists_upper_half_disk_chart_for_arc
    (S T gamma : Set ℂ) (hT : T ⊆ S)
    (h : Metric.closedBall (0 : ℂ) 1 ≃ₜ S)
    (hb : ∀ z : Metric.closedBall (0 : ℂ) 1,
      (h z : ℂ) ∈ T ↔ ‖(z : ℂ)‖ = 1)
    (hgamma : gamma ⊆ T) (phi : Icc (-1 : ℝ) 1 ≃ₜ gamma)
    (hproper : gamma ≠ T) :
    ∃ f : polygonDiskUpperHalf ≃ₜ S,
      (∀ t : Icc (-1 : ℝ) 1,
        (f (polygonDiskUpperHalfDiameterPoint t) : ℂ) = (phi t : ℂ)) ∧
      range (fun z : {x : polygonDiskUpperHalf //
          ‖((x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1} => (f z : ℂ)) =
        closure (T \ gamma) := by
  obtain ⟨f, hf, hr⟩ :=
    exists_upper_half_boundary_homeomorph_for_arc S T gamma hT h hb hgamma phi hproper
  obtain ⟨H, hH⟩ := exists_upper_half_extension S T hT h hb f
  refine ⟨H, ?_, ?_⟩
  · intro t
    exact (hH ⟨polygonDiskUpperHalfDiameterPoint t, Or.inr (by
      simp [polygonDiskUpperHalfDiameterPoint])⟩).trans (hf t)
  · rw [← hr]
    apply congrArg range
    funext z
    exact hH ⟨z.1, Or.inl z.2⟩

/-- Helper toward Proposition 5.16: conjugation exchanges the model half-disks
while fixing the real diameter pointwise. -/
@[expose] def polygonDiskHalfConjHomeomorph :
    polygonDiskUpperHalf ≃ₜ polygonDiskLowerHalf where
  toFun x := ⟨⟨star ((x : Metric.closedBall (0 : ℂ) 1) : ℂ), by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_star] using x.val.property⟩,
    by
      change (star ((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im ≤ 0
      simpa only [Complex.star_def, Complex.conj_im] using neg_nonpos.mpr x.property⟩
  invFun x := ⟨⟨star ((x : Metric.closedBall (0 : ℂ) 1) : ℂ), by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_star] using x.val.property⟩,
    by
      change 0 ≤ (star ((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im
      simpa only [Complex.star_def, Complex.conj_im] using neg_nonneg.mpr x.property⟩
  left_inv x := Subtype.ext (Subtype.ext (star_star _))
  right_inv x := Subtype.ext (Subtype.ext (star_star _))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_star.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_star.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- Helper toward Proposition 5.16: the lower model diameter point with real
coordinate `t`, retaining both endpoints. -/
@[expose] def polygonDiskLowerHalfDiameterPoint (t : Icc (-1 : ℝ) 1) :
    polygonDiskLowerHalf :=
  ⟨(polygonDiskUpperHalfDiameterPoint t).1, by
    simp [polygonDiskUpperHalfDiameterPoint, polygonDiskLowerHalf]⟩

/-- Helper toward Proposition 5.16: lower half-disk normalization preserves
the same prescribed real diameter parameter and complementary outer arc. -/
theorem exists_lower_half_disk_chart_for_arc
    (S T gamma : Set ℂ) (hT : T ⊆ S)
    (h : Metric.closedBall (0 : ℂ) 1 ≃ₜ S)
    (hb : ∀ z : Metric.closedBall (0 : ℂ) 1,
      (h z : ℂ) ∈ T ↔ ‖(z : ℂ)‖ = 1)
    (hgamma : gamma ⊆ T) (phi : Icc (-1 : ℝ) 1 ≃ₜ gamma)
    (hproper : gamma ≠ T) :
    ∃ f : polygonDiskLowerHalf ≃ₜ S,
      (∀ t : Icc (-1 : ℝ) 1,
        (f (polygonDiskLowerHalfDiameterPoint t) : ℂ) = (phi t : ℂ)) ∧
      range (fun z : {x : polygonDiskLowerHalf //
          ‖((x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1} => (f z : ℂ)) =
        closure (T \ gamma) := by
  obtain ⟨f, hf, hr⟩ :=
    exists_upper_half_disk_chart_for_arc S T gamma hT h hb hgamma phi hproper
  let e := polygonDiskHalfConjHomeomorph
  let g := e.symm.trans f
  have he (t : Icc (-1 : ℝ) 1) :
      e.symm (polygonDiskLowerHalfDiameterPoint t) = polygonDiskUpperHalfDiameterPoint t := by
    apply Subtype.ext; apply Subtype.ext
    simp [e, polygonDiskHalfConjHomeomorph, polygonDiskLowerHalfDiameterPoint,
      polygonDiskUpperHalfDiameterPoint]
  refine ⟨g, ?_, ?_⟩
  · intro t
    change (f (e.symm (polygonDiskLowerHalfDiameterPoint t)) : ℂ) = _
    rw [he]
    exact hf t
  · rw [← hr]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨e.symm x, ?_⟩, rfl⟩
      change ‖star ((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1
      simpa only [norm_star] using x.property
    · rintro ⟨x, rfl⟩
      refine ⟨⟨e x, ?_⟩, ?_⟩
      · change ‖star ((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1
        simpa only [norm_star] using x.property
      · change (f (e.symm (e x)) : ℂ) = _
        rw [e.symm_apply_apply]

/-- Helper toward Proposition 5.16: every point on the model seam has the
same interval parameter in the upper and lower diameter embeddings. -/
theorem exists_half_disk_diameter_parameter
    (z : Metric.closedBall (0 : ℂ) 1) (hz : (z : ℂ).im = 0) :
    ∃ t : Icc (-1 : ℝ) 1,
      (polygonDiskUpperHalfDiameterPoint t : Metric.closedBall (0 : ℂ) 1) = z ∧
      (polygonDiskLowerHalfDiameterPoint t : Metric.closedBall (0 : ℂ) 1) = z := by
  have hn : ‖(z : ℂ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  have hr := abs_le.mp ((Complex.abs_re_le_norm (z : ℂ)).trans hn)
  let t : Icc (-1 : ℝ) 1 := ⟨(z : ℂ).re, by constructor <;> linarith⟩
  have he : (polygonDiskUpperHalfDiameterPoint t : Metric.closedBall (0 : ℂ) 1) = z := by
    apply Subtype.ext
    apply Complex.ext <;> simp [polygonDiskUpperHalfDiameterPoint, t, hz]
  exact ⟨t, he, he⟩

/-- Helper toward Proposition 5.16: a chart with the prescribed injective
diameter parameter meets that arc exactly along the real model diameter. -/
theorem upper_half_chart_mem_arc_iff
    (S gamma : Set ℂ) (f : polygonDiskUpperHalf ≃ₜ S)
    (phi : Icc (-1 : ℝ) 1 ≃ₜ gamma)
    (hf : ∀ t, (f (polygonDiskUpperHalfDiameterPoint t) : ℂ) = (phi t : ℂ))
    (x : polygonDiskUpperHalf) :
    (f x : ℂ) ∈ gamma ↔ (((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0 := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := phi.surjective ⟨f x, hx⟩
    have he : f (polygonDiskUpperHalfDiameterPoint t) = f x :=
      Subtype.ext ((hf t).trans (congrArg Subtype.val ht))
    have he' := f.injective he
    rw [← he']
    simp [polygonDiskUpperHalfDiameterPoint]
  · intro hx
    obtain ⟨t, ht, _⟩ := exists_half_disk_diameter_parameter x hx
    have he : polygonDiskUpperHalfDiameterPoint t = x := Subtype.ext ht
    rw [← he, hf]
    exact (phi t).property

/-- Helper toward Proposition 5.16: two already charted disks whose exact
intersection is a proper parameterized boundary arc glue to a disk, with the
union of complementary arcs as the exact image of its unit circle. -/
theorem d39PLArcGluing : D39PLArcGluingStatement := by
  intro S₁ S₂ T₁ T₂ gamma hT₁ hT₂ h₁ h₂ hb₁ hb₂ hinter
    hgamma₁ hgamma₂ phi hproper₁ hproper₂
  obtain ⟨f, hf, hfr⟩ := exists_upper_half_disk_chart_for_arc
    S₁ T₁ gamma hT₁ h₁ hb₁ hgamma₁ phi hproper₁
  obtain ⟨g, hg, hgr⟩ := exists_lower_half_disk_chart_for_arc
    S₂ T₂ gamma hT₂ h₂ hb₂ hgamma₂ phi hproper₂
  have hseam : ∀ x : polygonDiskUpperHalf,
      (f x : ℂ) ∈ S₂ ↔ (((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0 := by
    intro x
    rw [← upper_half_chart_mem_arc_iff S₁ gamma f phi hf x]
    exact ⟨fun hx => hinter ▸ And.intro (f x).property hx,
      fun hx => (hinter.symm ▸ hx : (f x : ℂ) ∈ S₁ ∩ S₂).2⟩
  have hagree : ∀ (z : Metric.closedBall (0 : ℂ) 1) (hz : (z : ℂ).im = 0),
      (f ⟨z, hz.symm.le⟩ : ℂ) = (g ⟨z, hz.le⟩ : ℂ) := by
    intro z hz
    obtain ⟨t, ht, ht'⟩ := exists_half_disk_diameter_parameter z hz
    have hu : polygonDiskUpperHalfDiameterPoint t = ⟨z, hz.symm.le⟩ := Subtype.ext ht
    have hl : polygonDiskLowerHalfDiameterPoint t = ⟨z, hz.le⟩ := Subtype.ext ht'
    rw [← hu, ← hl, hf, hg]
  obtain ⟨H, hHf, hHg, hHb⟩ := exists_disk_chart_of_compatible_half_disk_charts
    S₁ S₂ f g (half_disk_charts_cross_iff_of_seam S₁ S₂ f g hseam hagree)
  refine ⟨H, ?_⟩
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rcases (hHb w).mpr w.property with ⟨x, hx, he⟩ | ⟨y, hy, he⟩
    · exact Or.inl (hfr.le ⟨⟨x, hx⟩, he⟩)
    · exact Or.inr (hgr.le ⟨⟨y, hy⟩, he⟩)
  · intro hz
    rcases hz with hz | hz
    · obtain ⟨x, hx⟩ := hfr.ge hz
      exact ⟨⟨x.1, x.2⟩, (hHf x.1).trans hx⟩
    · obtain ⟨x, hx⟩ := hgr.ge hz
      exact ⟨⟨x.1, x.2⟩, (hHg x.1).trans hx⟩

/-- Helper toward Proposition 5.16: every cyclically simple polygon has a
closed-disk chart with exact polygon-boundary correspondence. -/
theorem Polyline.exists_polygon_disk_chart
    (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure c.inside,
      ∀ z : Metric.closedBall (0 : ℂ) 1,
        (h z : ℂ) ∈ c.image ↔ ‖(z : ℂ)‖ = 1 :=
  Polyline.exists_polygon_disk_chart_of_arc_gluing d39PLArcGluing c hc

end DirectedDistances.PlanarMap
