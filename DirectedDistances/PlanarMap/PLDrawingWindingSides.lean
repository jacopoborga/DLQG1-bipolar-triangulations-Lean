/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.PlanarMap.GeneralPlaneMapSides











public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace PLDrawing





private def obstructionVertices : Set ℂ :=
  {z | z = 0 ∨ z = 1 ∨ (1 / 2 < z.re ∧ z.re < 1 ∧ z.im ≠ 0)}

private def obstructionVertex (d : Bool) : obstructionVertices :=
  if d then ⟨1, Or.inr (Or.inl rfl)⟩ else ⟨0, Or.inl rfl⟩

private def obstructionArc : Bool → Polyline
  | false => ⟨[0, 1], by simp⟩
  | true => ⟨[1, 0], by simp⟩

private theorem obstructionVertex_injective : Function.Injective obstructionVertex := by
  intro d e h
  have hv := congrArg Subtype.val h
  cases d <;> cases e
  · rfl
  · exact (zero_ne_one (show (0 : ℂ) = 1 from hv)).elim
  · exact (one_ne_zero (show (1 : ℂ) = 0 from hv)).elim
  · rfl

private theorem obstructionArc_image (d : Bool) :
    (obstructionArc d).image = segment ℝ (if d then 1 else 0) (if d then 0 else 1) := by
  rw [← Polyline.range_toPath]
  cases d
  · change Set.range (Path.segment (0 : ℂ) 1) = _
    exact Path.range_segment _ _
  · change Set.range (Path.segment (1 : ℂ) 0) = _
    exact Path.range_segment _ _

private theorem obstructionArc_im {d : Bool} {z : ℂ}
    (h : z ∈ (obstructionArc d).image) : z.im = 0 := by
  rw [obstructionArc_image, segment_eq_image] at h
  obtain ⟨t, _, rfl⟩ := h
  cases d <;> simp

private def obstructionDrawing :
    PLDrawing Bool obstructionVertices Bool.not (Equiv.refl Bool) obstructionVertex where
  flip_involutive := by intro d; cases d <;> rfl
  flip_ne := by intro d; cases d <;> decide
  vert_rotation := fun _ => rfl
  pos := Subtype.val
  pos_injective := Subtype.val_injective
  arc := obstructionArc
  arc_simple := by
    intro d
    have hf : (obstructionArc false).IsSimple := by
      apply Polyline.isSimple_of_XMonotone
      · simp [Polyline.XMonotone, obstructionArc]
      · norm_num [obstructionArc]
    cases d
    · exact hf
    · exact Polyline.isSimple_reverse_transfer _ hf
  arc_length := by intro d; cases d <;> norm_num [obstructionArc]
  arc_start := by intro d; cases d <;> rfl
  arc_finish := by intro d; cases d <;> rfl
  arc_flip := by intro d; cases d <;> rfl
  interior_disjoint := by
    intro d e hne hflip
    cases d <;> cases e <;> simp_all
  interior_avoids_vertices := by
    intro d z hz
    have him := obstructionArc_im hz.1
    rcases z.property with hzero | hone | hstrip
    · apply hz.2
      cases d <;> simp [obstructionArc, Polyline.start, Polyline.finish, hzero]
    · apply hz.2
      cases d <;> simp [obstructionArc, Polyline.start, Polyline.finish, hone]
    · exact hstrip.2.2 him
  locally_finite := fun _ _ => Set.toFinite _
  initial_nonzero := by
    intro d
    cases d <;> norm_num [obstructionArc, Polyline.initialDirection,
      Polyline.point, Polyline.start]
  initial_arg_injective := by
    intro d e h _
    exact obstructionVertex_injective h
  rotation_agreement := by
    intro d
    refine ⟨Set.toFinite _, rfl, rfl, Or.inl ⟨rfl, ?_⟩⟩
    ext e
    exact obstructionVertex_injective.eq_iff

private def obstructionUpperLeft : Set ℂ := {z | z.re < 1 / 2 ∧ 0 < z.im}

private theorem obstructionUpperLeft_convex : Convex ℝ obstructionUpperLeft := by
  exact ((convex_Iio (1 / 2 : ℝ)).linear_preimage Complex.reLm).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)

private theorem obstructionUpperLeft_compl :
    obstructionUpperLeft ⊆ obstructionDrawing.imageᶜ := by
  intro z hz himage
  rcases himage with hvertex | ⟨d, hd⟩
  · obtain ⟨v, rfl⟩ := hvertex
    rcases v.property with hzero | hone | hstrip
    · have h := hz.2
      change 0 < (v.val).im at h
      simp [hzero] at h
    · have h := hz.2
      change 0 < (v.val).im at h
      simp [hone] at h
    · exact (not_lt_of_ge hz.1.le) hstrip.1
  · exact (ne_of_gt hz.2) (obstructionArc_im hd)

private def obstructionFace : obstructionDrawing.Face :=
  ⟨connectedComponentIn obstructionDrawing.imageᶜ Complex.I,
    Complex.I, obstructionUpperLeft_compl (by
      norm_num [obstructionUpperLeft]), rfl⟩

private theorem obstructionUpperLeft_subset_face :
    obstructionUpperLeft ⊆ obstructionFace.val :=
  obstructionUpperLeft_convex.isPreconnected.subset_connectedComponentIn
    (by norm_num [obstructionUpperLeft]) obstructionUpperLeft_compl

private theorem obstruction_dartBorders :
    obstructionDrawing.dartBorders false obstructionFace := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro t ε ht htd hε _
  apply obstructionUpperLeft_subset_face
  have heq : (obstructionDrawing.arc false).start + (t : ℂ) *
      ((obstructionDrawing.arc false).initialDirection +
        (ε : ℂ) * Complex.I * (obstructionDrawing.arc false).initialDirection) =
      (t : ℂ) * (1 + (ε : ℂ) * Complex.I) := by
    simp [obstructionDrawing, obstructionArc, Polyline.start,
      Polyline.initialDirection, Polyline.point]
  rw [heq]
  constructor
  · change ((t : ℂ) * (1 + (ε : ℂ) * Complex.I)).re < 1 / 2
    simp only [Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one,
      add_zero]
    linarith only [htd]
  · simpa using mul_pos ht hε

private theorem obstruction_strip_subset_image {z : ℂ}
    (hz : 1 / 2 < z.re ∧ z.re < 1) : z ∈ obstructionDrawing.image := by
  by_cases him : z.im = 0
  · right
    refine ⟨false, ?_⟩
    change z ∈ (obstructionArc false).image
    rw [obstructionArc_image, segment_eq_image]
    refine ⟨z.re, ⟨by linarith only [hz.1], hz.2.le⟩, ?_⟩
    apply Complex.ext <;> simp [him]
  · exact Or.inl ⟨⟨z, Or.inr (Or.inr ⟨hz.1, hz.2, him⟩)⟩, rfl⟩

private theorem obstruction_not_mem_closure :
    (3 / 4 : ℂ) ∉ closure obstructionFace.val := by
  let U : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsub : obstructionFace.val ⊆ Uᶜ := by
    intro z hz hstrip
    exact obstructionDrawing.face_subset_compl obstructionFace hz
      (obstruction_strip_subset_image hstrip)
  have hclosure := closure_minimal hsub hU.isClosed_compl
  intro h
  exact hclosure h (by norm_num [U])






theorem exists_dartBorders_not_mem_closure_toPath :
    ∃ (V : Type) (vert : Bool → V)
      (P : PLDrawing Bool V Bool.not (Equiv.refl Bool) vert)
      (F : P.Face) (s : {t : I // t ∈ openParams}),
      P.dartBorders false F ∧
        (P.arc false).toPath s.val ∉ closure F.val ∧
        ¬ LeftAtOn F.val (P.arc false).toPath s := by
  let s : {t : I // t ∈ openParams} :=
    ⟨⟨3 / 4, by norm_num⟩, by
      change 0 < (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) < 1
      norm_num⟩
  have hpoint : (obstructionDrawing.arc false).toPath s.val = (3 / 4 : ℂ) := by
    change Path.segment (0 : ℂ) 1 s.val = _
    simp [Path.segment_apply, AffineMap.lineMap_apply_module, s]
  have hnot : (obstructionDrawing.arc false).toPath s.val ∉
      closure obstructionFace.val := by
    rw [hpoint]
    exact obstruction_not_mem_closure
  refine ⟨obstructionVertices, obstructionVertex, obstructionDrawing,
    obstructionFace, s, obstruction_dartBorders, hnot, ?_⟩
  rintro ⟨a, b, ha, has, hsb, hb, q, hq, hqF, hclosure⟩
  apply hnot
  refine closure_mono ?_ hclosure
  intro w hw
  exact hw.1

/- ∀ {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face),
  P.dartBorders d F →
    ∀ s : {t : I // t ∈ openParams}, LeftAtOn F.val (P.arc d).toPath s

`exists_dartBorders_not_mem_closure_toPath` refutes this statement. No
compatibility statement has been added as a premise. Parts (b), (c), and (d)
are not attempted. Dart-vertex surjectivity, used by the supplied neighborhood
lemmas, excludes this counterexample; it is not a field of `PLDrawing`. -/

end PLDrawing

end DirectedDistances.PlanarMap

end
