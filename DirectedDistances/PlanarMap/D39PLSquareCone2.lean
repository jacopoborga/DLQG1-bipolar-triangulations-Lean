/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLSquareCone

/-! Helpers toward Proposition 5.16: product coordinates for the square exterior. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline
open Set Topology

/-- Helper toward Proposition 5.16: points in the closed square exterior have positive norm. -/
theorem supNormC_pos_of_mem_closure_outside (R : ℝ) (hR : 0 < R)
    (z : closure (enclosingSquare R).outside) : 0 < supNormC (z : ℂ) := by
  have hz : R ≤ supNormC (z : ℂ) := by
    simpa only [enclosingSquare_closure_outside_eq_supNormC_ge R hR, Set.mem_ofPred_eq]
      using z.property
  exact lt_of_lt_of_le hR hz

/-- Helper toward Proposition 5.16: radial normalization sends the closed square exterior to
the square boundary. -/
def squareOutsideBoundaryPoint (R : ℝ) (hR : 0 < R)
    (z : closure (enclosingSquare R).outside) : (enclosingSquare R).image := by
  refine ⟨(R / supNormC (z : ℂ)) • (z : ℂ), ?_⟩
  rw [enclosingSquare_image_eq_supNormC R hR]
  have hnorm : 0 < supNormC (z : ℂ) := supNormC_pos_of_mem_closure_outside R hR z
  change supNormC ((R / supNormC (z : ℂ)) • (z : ℂ)) = R
  rw [supNormC_smul_of_nonneg _ (div_nonneg hR.le (le_of_lt hnorm))]
  field_simp

/-- Helper toward Proposition 5.16: the radial coordinate of a closed exterior point is at least
one. -/
def squareOutsideRadius (R : ℝ) (hR : 0 < R)
    (z : closure (enclosingSquare R).outside) : Set.Ici (1 : ℝ) := by
  refine ⟨supNormC (z : ℂ) / R, ?_⟩
  have hz : R ≤ supNormC (z : ℂ) := by
    simpa only [enclosingSquare_closure_outside_eq_supNormC_ge R hR, Set.mem_ofPred_eq]
      using z.property
  exact (le_div_iff₀ hR).2 (by simpa using hz)

/-- Helper toward Proposition 5.16: the radial coordinate product has the expected norm. -/
theorem supNormC_smul_image_radius (R : ℝ) (hR : 0 < R)
    (p : (enclosingSquare R).image × Set.Ici (1 : ℝ)) :
    supNormC ((p.2 : ℝ) • (p.1 : ℂ)) = (p.2 : ℝ) * R := by
  have hw : supNormC (p.1 : ℂ) = R := by
    simpa only [enclosingSquare_image_eq_supNormC R hR, Set.mem_ofPred_eq]
      using p.1.property
  rw [supNormC_smul_of_nonneg _ (le_trans (by norm_num) p.2.property) _, hw]

/-- Helper toward Proposition 5.16: product coordinates reconstruct a point in the closed
square exterior. -/
def squareOutsideProdInverse (R : ℝ) (hR : 0 < R) :
    (enclosingSquare R).image × Set.Ici (1 : ℝ) → closure (enclosingSquare R).outside :=
  fun p => ⟨(p.2 : ℝ) • (p.1 : ℂ), by
    rw [enclosingSquare_closure_outside_eq_supNormC_ge R hR]
    change R ≤ supNormC ((p.2 : ℝ) • (p.1 : ℂ))
    rw [supNormC_smul_image_radius R hR p]
    calc
      R = 1 * R := by ring
      _ ≤ (p.2 : ℝ) * R := mul_le_mul_of_nonneg_right p.2.property hR.le⟩

/-- Helper toward Proposition 5.16: the product coordinate map from the closed square exterior. -/
def squareOutsideProdMap (R : ℝ) (hR : 0 < R) :
    closure (enclosingSquare R).outside →
      (enclosingSquare R).image × Set.Ici (1 : ℝ) := fun z =>
  (squareOutsideBoundaryPoint R hR z, squareOutsideRadius R hR z)

/-- Helper toward Proposition 5.16: the product coordinate maps are continuous. -/
theorem continuous_squareOutsideProdMap (R : ℝ) (hR : 0 < R) :
    Continuous (squareOutsideProdMap R hR) := by
  have hn : Continuous (fun z : closure (enclosingSquare R).outside =>
      supNormC (z : ℂ)) := continuous_supNormC.comp continuous_subtype_val
  have hn0 : ∀ z : closure (enclosingSquare R).outside, supNormC (z : ℂ) ≠ 0 :=
    fun z => ne_of_gt (supNormC_pos_of_mem_closure_outside R hR z)
  have hscale : Continuous (fun z : closure (enclosingSquare R).outside =>
      R / supNormC (z : ℂ)) := continuous_const.div hn hn0
  have hboundary : Continuous (fun z : closure (enclosingSquare R).outside =>
      (R / supNormC (z : ℂ)) • (z : ℂ)) :=
    continuous_smul.comp (hscale.prodMk continuous_subtype_val)
  have hradius : Continuous (fun z : closure (enclosingSquare R).outside =>
      supNormC (z : ℂ) / R) := hn.div_const R
  change Continuous (fun z => (squareOutsideBoundaryPoint R hR z,
    squareOutsideRadius R hR z))
  exact (hboundary.subtype_mk _).prodMk (hradius.subtype_mk _)

/-- Helper toward Proposition 5.16: the product coordinate inverse is continuous. -/
theorem continuous_squareOutsideProdInverse (R : ℝ) (hR : 0 < R) :
    Continuous (squareOutsideProdInverse R hR) := by
  have h : Continuous (fun p : (enclosingSquare R).image × Set.Ici (1 : ℝ) =>
      (p.2 : ℝ) • (p.1 : ℂ)) := by
    exact continuous_smul.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
  exact h.subtype_mk _

/-- Helper toward Proposition 5.16: taking product coordinates after reconstruction is the
identity. -/
theorem squareOutsideProdMap_inverse (R : ℝ) (hR : 0 < R)
    (p : (enclosingSquare R).image × Set.Ici (1 : ℝ)) :
    squareOutsideProdMap R hR (squareOutsideProdInverse R hR p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    change (R / supNormC ((p.2 : ℝ) • (p.1 : ℂ))) •
      ((p.2 : ℝ) • (p.1 : ℂ)) = (p.1 : ℂ)
    rw [supNormC_smul_image_radius R hR p, smul_smul]
    have ht : (p.2 : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one p.2.property)
    have hfac : R / ((p.2 : ℝ) * R) * (p.2 : ℝ) = 1 := by
      field_simp [hR.ne', ht]
    rw [hfac, one_smul]
  · apply Subtype.ext
    change supNormC ((p.2 : ℝ) • (p.1 : ℂ)) / R = (p.2 : ℝ)
    rw [supNormC_smul_image_radius R hR p]
    field_simp [hR.ne']

/-- Helper toward Proposition 5.16: reconstruction after taking product coordinates is the
identity. -/
theorem squareOutsideProdInverse_map (R : ℝ) (hR : 0 < R)
    (z : closure (enclosingSquare R).outside) :
    squareOutsideProdInverse R hR (squareOutsideProdMap R hR z) = z := by
  apply Subtype.ext
  change (supNormC (z : ℂ) / R) •
      ((R / supNormC (z : ℂ)) • (z : ℂ)) = (z : ℂ)
  rw [smul_smul]
  have hN := supNormC_pos_of_mem_closure_outside R hR z
  have hfac : supNormC (z : ℂ) / R * (R / supNormC (z : ℂ)) = 1 := by
    field_simp [hR.ne', hN.ne']
  rw [hfac, one_smul]

/-- Helper toward Proposition 5.16: the closed square exterior is homeomorphic to its boundary
times a closed ray. -/
def squareOutsideProdHomeomorph (R : ℝ) (hR : 0 < R) :
    closure (enclosingSquare R).outside ≃ₜ
      (enclosingSquare R).image × Set.Ici (1 : ℝ) :=
  Homeomorph.mk
    { toFun := squareOutsideProdMap R hR
      invFun := squareOutsideProdInverse R hR
      left_inv := squareOutsideProdInverse_map R hR
      right_inv := squareOutsideProdMap_inverse R hR }
    (continuous_squareOutsideProdMap R hR)
    (continuous_squareOutsideProdInverse R hR)

/-- Helper toward Proposition 5.16: a square boundary point is viewed as a point of its closed
exterior. -/
def squareImageInClosure (R : ℝ) (hR : 0 < R)
    (x : (enclosingSquare R).image) : closure (enclosingSquare R).outside :=
  ⟨x, (enclosingSquare R).image_subset_closure_outside_cyclic
    (enclosingSquare_isCyclicSimple R hR) x.property⟩

/-- Helper toward Proposition 5.16: product coordinates of a boundary point have radial
coordinate one. -/
theorem squareOutsideProdHomeomorph_image (R : ℝ) (hR : 0 < R)
    (x : (enclosingSquare R).image) :
    squareOutsideProdHomeomorph R hR (squareImageInClosure R hR x) =
      (x, ⟨1, le_rfl⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    have hx : supNormC (x : ℂ) = R := by
      simpa only [enclosingSquare_image_eq_supNormC R hR, Set.mem_ofPred_eq]
        using x.property
    change (R / supNormC (x : ℂ)) • (x : ℂ) = (x : ℂ)
    rw [hx]
    simp [hR.ne']
  · apply Subtype.ext
    have hx : supNormC (x : ℂ) = R := by
      simpa only [enclosingSquare_image_eq_supNormC R hR, Set.mem_ofPred_eq]
        using x.property
    change supNormC (x : ℂ) / R = 1
    rw [hx]
    exact div_self hR.ne'

/-- Helper toward Proposition 5.16: conjugating a boundary homeomorphism by the product
coordinates extends it to the closed square exterior. -/
def squareOutsideExtension (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (g : (enclosingSquare R).image ≃ₜ (enclosingSquare R').image) :
    closure (enclosingSquare R).outside ≃ₜ closure (enclosingSquare R').outside :=
  (squareOutsideProdHomeomorph R hR).trans
    ((g.prodCongr (Homeomorph.refl _)).trans (squareOutsideProdHomeomorph R' hR').symm)

/-- Helper toward Proposition 5.16: the exterior extension agrees with the given boundary map. -/
theorem squareOutsideExtension_agrees_on_image (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (g : (enclosingSquare R).image ≃ₜ (enclosingSquare R').image)
    (x : (enclosingSquare R).image) :
    (squareOutsideExtension R R' hR hR' g (squareImageInClosure R hR x) : ℂ) =
      (g x : ℂ) := by
  change ((squareOutsideProdHomeomorph R' hR').symm
    ((g.prodCongr (Homeomorph.refl _))
      (squareOutsideProdHomeomorph R hR (squareImageInClosure R hR x)) :
        (enclosingSquare R').image × Set.Ici (1 : ℝ)) : ℂ) = (g x : ℂ)
  rw [squareOutsideProdHomeomorph_image R hR x]
  change (1 : ℝ) • (g x : ℂ) = (g x : ℂ)
  simp

/-- Helper toward Proposition 5.16: the radial coordinate equals one exactly on the square
boundary. -/
theorem squareOutsideRadius_eq_one_iff_mem_image (R : ℝ) (hR : 0 < R)
    (z : closure (enclosingSquare R).outside) :
    squareOutsideRadius R hR z = ⟨1, le_rfl⟩ ↔
      (z : ℂ) ∈ (enclosingSquare R).image := by
  constructor
  · intro hz
    have hval := congrArg Subtype.val hz
    change supNormC (z : ℂ) / R = 1 at hval
    have hnorm : supNormC (z : ℂ) = R := by
      have := (div_eq_iff hR.ne').mp hval
      simpa using this
    simpa only [enclosingSquare_image_eq_supNormC R hR, Set.mem_ofPred_eq] using hnorm
  · intro hz
    have hnorm : supNormC (z : ℂ) = R := by
      simpa only [enclosingSquare_image_eq_supNormC R hR, Set.mem_ofPred_eq] using hz
    apply Subtype.ext
    change supNormC (z : ℂ) / R = 1
    rw [hnorm]
    exact div_self hR.ne'

/-- Helper toward Proposition 5.16: the radial coordinate is greater than one exactly on the
open square exterior. -/
theorem squareOutsideRadius_gt_one_iff_mem_outside (R : ℝ) (hR : 0 < R)
    (z : closure (enclosingSquare R).outside) :
    1 < (squareOutsideRadius R hR z : ℝ) ↔
      (z : ℂ) ∈ (enclosingSquare R).outside := by
  have hmem : (z : ℂ) ∈ (enclosingSquare R).outside ↔
      R < supNormC (z : ℂ) := by
    simp only [enclosingSquare_outside_eq_supNormC_gt R hR, Set.mem_ofPred_eq]
  have hdiv : 1 < supNormC (z : ℂ) / R ↔ R < supNormC (z : ℂ) := by
    rw [lt_div_iff₀ hR]
    norm_num
  change 1 < supNormC (z : ℂ) / R ↔ (z : ℂ) ∈ (enclosingSquare R).outside
  exact hdiv.trans hmem.symm

/-- Helper toward Proposition 5.16: the extension preserves the product radial coordinate. -/
theorem squareOutsideExtension_preserves_radius (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (g : (enclosingSquare R).image ≃ₜ (enclosingSquare R').image)
    (z : closure (enclosingSquare R).outside) :
    squareOutsideRadius R' hR'
        (squareOutsideExtension R R' hR hR' g z) = squareOutsideRadius R hR z := by
  have hp : squareOutsideProdHomeomorph R' hR'
      (squareOutsideExtension R R' hR hR' g z) =
      (g (squareOutsideBoundaryPoint R hR z), squareOutsideRadius R hR z) := by
    simp [squareOutsideExtension]
    change Prod.map g id (squareOutsideProdMap R hR z) = _
    rfl
  exact congrArg Prod.snd hp

/-- Helper toward Proposition 5.16: the extension carries the boundary part of the closed
exterior onto the boundary part of the target. -/
theorem squareOutsideExtension_image_boundary (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (g : (enclosingSquare R).image ≃ₜ (enclosingSquare R').image) :
    squareOutsideExtension R R' hR hR' g ''
        {z : closure (enclosingSquare R).outside | (z : ℂ) ∈ (enclosingSquare R).image} =
      {z : closure (enclosingSquare R').outside | (z : ℂ) ∈ (enclosingSquare R').image} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (squareOutsideExtension R R' hR hR' g z : ℂ) ∈ (enclosingSquare R').image
    apply (squareOutsideRadius_eq_one_iff_mem_image R' hR'
      (squareOutsideExtension R R' hR hR' g z)).mp
    have hr := squareOutsideExtension_preserves_radius R R' hR hR' g z
    rw [(squareOutsideRadius_eq_one_iff_mem_image R hR z).2 hz] at hr
    exact hr
  · intro hy
    change (y : ℂ) ∈ (enclosingSquare R').image at hy
    refine ⟨(squareOutsideExtension R R' hR hR' g).symm y, ?_, by simp⟩
    apply (squareOutsideRadius_eq_one_iff_mem_image R hR
      ((squareOutsideExtension R R' hR hR' g).symm y)).mp
    have hr := squareOutsideExtension_preserves_radius R R' hR hR' g
      ((squareOutsideExtension R R' hR hR' g).symm y)
    have hr' : squareOutsideRadius R' hR' y =
        squareOutsideRadius R hR ((squareOutsideExtension R R' hR hR' g).symm y) := by
      simpa using hr
    have hy' := (squareOutsideRadius_eq_one_iff_mem_image R' hR' y).2 hy
    exact hr'.symm.trans hy'

/-- Helper toward Proposition 5.16: the extension carries the open exterior part of the closed
exterior onto the target open exterior. -/
theorem squareOutsideExtension_image_outside (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (g : (enclosingSquare R).image ≃ₜ (enclosingSquare R').image) :
    squareOutsideExtension R R' hR hR' g ''
        {z : closure (enclosingSquare R).outside | (z : ℂ) ∈ (enclosingSquare R).outside} =
      {z : closure (enclosingSquare R').outside | (z : ℂ) ∈ (enclosingSquare R').outside} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (squareOutsideExtension R R' hR hR' g z : ℂ) ∈ (enclosingSquare R').outside
    apply (squareOutsideRadius_gt_one_iff_mem_outside R' hR' _).mp
    have hr := squareOutsideExtension_preserves_radius R R' hR hR' g z
    have hz' := (squareOutsideRadius_gt_one_iff_mem_outside R hR z).2 hz
    change 1 < (squareOutsideRadius R' hR'
      (squareOutsideExtension R R' hR hR' g z) : ℝ)
    rw [hr]
    exact hz'
  · intro hy
    change (y : ℂ) ∈ (enclosingSquare R').outside at hy
    refine ⟨(squareOutsideExtension R R' hR hR' g).symm y, ?_, by simp⟩
    apply (squareOutsideRadius_gt_one_iff_mem_outside R hR _).mp
    have hr := squareOutsideExtension_preserves_radius R R' hR hR' g
      ((squareOutsideExtension R R' hR hR' g).symm y)
    have hr' : squareOutsideRadius R' hR' y =
        squareOutsideRadius R hR ((squareOutsideExtension R R' hR hR' g).symm y) := by
      simpa using hr
    have hy' := (squareOutsideRadius_gt_one_iff_mem_outside R' hR' y).2 hy
    change 1 < (squareOutsideRadius R hR
      ((squareOutsideExtension R R' hR hR' g).symm y) : ℝ)
    rw [← hr']
    exact hy'

/-- Helper toward Proposition 5.16, target (3): every homeomorphism of square boundaries extends
to a homeomorphism of their closed exteriors. -/
theorem exists_squareOutsideExtension (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (g : (enclosingSquare R).image ≃ₜ (enclosingSquare R').image) :
    ∃ E : closure (enclosingSquare R).outside ≃ₜ closure (enclosingSquare R').outside,
      ∀ x : (enclosingSquare R).image,
        (E ⟨x, (enclosingSquare R).image_subset_closure_outside_cyclic
          (enclosingSquare_isCyclicSimple R hR) x.property⟩ : ℂ) = (g x : ℂ) := by
  refine ⟨squareOutsideExtension R R' hR hR' g, ?_⟩
  intro x
  exact squareOutsideExtension_agrees_on_image R R' hR hR' g x

/-- Helper toward Proposition 5.16, target (4): the extension agrees on the boundary and maps
both the boundary and open exterior parts onto their counterparts. -/
theorem exists_squareOutsideExtension_with_parts (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (g : (enclosingSquare R).image ≃ₜ (enclosingSquare R').image) :
    ∃ E : closure (enclosingSquare R).outside ≃ₜ closure (enclosingSquare R').outside,
      (∀ x : (enclosingSquare R).image,
        (E ⟨x, (enclosingSquare R).image_subset_closure_outside_cyclic
          (enclosingSquare_isCyclicSimple R hR) x.property⟩ : ℂ) = (g x : ℂ)) ∧
      E '' {x : closure (enclosingSquare R).outside | (x : ℂ) ∈
        (enclosingSquare R).image} =
        {y : closure (enclosingSquare R').outside | (y : ℂ) ∈
          (enclosingSquare R').image} ∧
      E '' {x : closure (enclosingSquare R).outside | (x : ℂ) ∈
        (enclosingSquare R).outside} =
        {y : closure (enclosingSquare R').outside | (y : ℂ) ∈
          (enclosingSquare R').outside} := by
  refine ⟨squareOutsideExtension R R' hR hR' g, ?_, ?_, ?_⟩
  · intro x
    exact squareOutsideExtension_agrees_on_image R R' hR hR' g x
  · exact squareOutsideExtension_image_boundary R R' hR hR' g
  · exact squareOutsideExtension_image_outside R R' hR hR' g

end Polyline
end DirectedDistances.PlanarMap

