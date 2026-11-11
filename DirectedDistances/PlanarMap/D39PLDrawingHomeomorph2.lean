/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingHomeomorph
public import DirectedDistances.PlanarMap.FiniteDrawingExterior

/-! # Marked exterior and extension over drawing faces -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Set Topology

namespace PLDrawing
variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: norm-unboundedness of a face is exactly
failure of bornological boundedness. -/
theorem isUnbounded_iff_not_isBounded (F : P.Face) :
    P.IsUnbounded F ↔ ¬ Bornology.IsBounded F.val := by
  change (∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖) ↔ _
  rw [isBounded_iff_forall_norm_le]
  push Not
  rfl

/-- Helper toward Proposition 5.16: a finite drawing has exactly one
unbounded complementary face, expressed using bornological boundedness. -/
theorem existsUnique_not_isBounded_face [Finite D] [Finite V] :
    ∃! U : P.Face, ¬ Bornology.IsBounded U.val := by
  simpa only [← P.isUnbounded_iff_not_isBounded] using P.existsUnique_unbounded_face

/-- Helper toward Proposition 5.16: one closed ball contains the finite
drawing and every face other than its unique unbounded face. -/
theorem exists_closedBall_containing_other_faces [Finite D] [Finite V]
    (U : P.Face) (hU : ¬ Bornology.IsBounded U.val) :
    ∃ R : ℝ, P.image ⊆ Metric.closedBall 0 R ∧
      (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ U.val ∧
      ∀ F : P.Face, F ≠ U → F.val ⊆ Metric.closedBall 0 R := by
  obtain ⟨R, hR, hall⟩ := P.unbounded_face_contains_compl_ball
  have houter := hall U ((P.isUnbounded_iff_not_isBounded U).mpr hU)
  refine ⟨R, hR, houter, ?_⟩
  intro F hne x hx
  by_contra h
  exact Set.disjoint_left.mp (P.disjoint_faces F U hne) hx (houter h)

/-- Helper toward Proposition 5.16: every face different from a marked
unbounded face is bounded. -/
theorem isBounded_face_of_ne_unbounded [Finite D] [Finite V]
    (U : P.Face) (hU : ¬ Bornology.IsBounded U.val)
    (F : P.Face) (hne : F ≠ U) : Bornology.IsBounded F.val := by
  obtain ⟨R, _, _, hR⟩ := P.exists_closedBall_containing_other_faces U hU
  exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset (hR F hne)

end PLDrawing

namespace D39FiniteBall
variable {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)
  (hconn : ∀ d e : B.D, Relation.EqvGen
    (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
include hconn

/-- Helper toward Proposition 5.16: if the same explicitly marked orbit
is unbounded in both drawings, every other orbit is bounded in both. -/
theorem isBounded_plOrbitFace_of_ne_external
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (O : D39BallFaceCycleOrbit B) (hne : O ≠ O_ext) :
    Bornology.IsBounded (B.plOrbitFace vert P hvert O).val ∧
      Bornology.IsBounded (B.plOrbitFace vert P' hvert O).val := by
  constructor
  · exact P.isBounded_face_of_ne_unbounded _ hext.1 _
      (fun h => hne (B.plOrbitFace_injective vert P hvert hconn h))
  · exact P'.isBounded_face_of_ne_unbounded _ hext.2 _
      (fun h => hne (B.plOrbitFace_injective vert P' hvert hconn h))

omit [Finite V] in
/-- Helper toward Proposition 5.16: corresponding bounded faces with
cyclically simple whole boundaries admit an extension of the drawing map. -/
theorem exists_bounded_plOrbitFace_homeomorph
    (f : B.PLImageHomeomorph vert P P')
    (O : D39BallFaceCycleOrbit B) (q q' : Polyline)
    (hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hq : q.image = B.plOrbitBoundary vert P O)
    (hclosed' : q'.start = q'.finish) (hc' : q'.IsCyclicSimple)
    (hq' : q'.image = B.plOrbitBoundary vert P' O)
    (hb : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val)
    (hb' : Bornology.IsBounded (B.plOrbitFace vert P' hvert O).val) :
    ∃ H : closure (B.plOrbitFace vert P hvert O).val ≃ₜ
        closure (B.plOrbitFace vert P' hvert O).val,
      ∀ (x : closure (B.plOrbitFace vert P hvert O).val)
        (hx : (x : ℂ) ∈ P.image),
        (H x : ℂ) = (f.toHomeomorph ⟨x, hx⟩ : ℂ) := by
  have hin := B.plOrbitFace_eq_inside_of_isBounded_cyclicSimple_boundary
    vert P hvert hconn O q hclosed hc hq hb
  have hin' := B.plOrbitFace_eq_inside_of_isBounded_cyclicSimple_boundary
    vert P' hvert hconn O q' hclosed' hc' hq' hb'
  obtain ⟨H, hH⟩ := B.exists_orbit_polygon_inside_homeomorph vert P P'
    f.toHomeomorph f.arc_image O q q' hc hc' hq hq'
  let e := (Homeomorph.setCongr (congrArg closure hin)).trans
    (H.trans (Homeomorph.setCongr (congrArg closure hin').symm))
  refine ⟨e, ?_⟩
  intro x hx
  have hxfront : (x : ℂ) ∈ frontier (B.plOrbitFace vert P hvert O).val :=
    (P.closure_face_inter_image_eq_frontier hvert _) ▸ ⟨x.property, hx⟩
  have hxq : (x : ℂ) ∈ q.image := by
    rw [hq, ← B.frontier_plOrbitFace_eq_plOrbitBoundary vert P hvert hconn O]
    exact hxfront
  exact hH ⟨x, hxq⟩

/-- Helper toward Proposition 5.16: the explicit external-orbit hypothesis
and simple-walk data construct extensions on every bounded orbit. -/
theorem exists_all_bounded_plOrbitFace_homeomorphs
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hsimple : ∀ O : D39BallFaceCycleOrbit B, O ≠ O_ext →
      ∃ q q' : Polyline,
        q.start = q.finish ∧ q.IsCyclicSimple ∧
        q.image = B.plOrbitBoundary vert P O ∧
        q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
        q'.image = B.plOrbitBoundary vert P' O) :
    ∀ O : D39BallFaceCycleOrbit B, O ≠ O_ext →
      ∃ H : closure (B.plOrbitFace vert P hvert O).val ≃ₜ
          closure (B.plOrbitFace vert P' hvert O).val,
        ∀ (x : closure (B.plOrbitFace vert P hvert O).val)
          (hx : (x : ℂ) ∈ P.image),
          (H x : ℂ) = (f.toHomeomorph ⟨x, hx⟩ : ℂ) := by
  intro O hne
  obtain ⟨hb, hb'⟩ := B.isBounded_plOrbitFace_of_ne_external vert P P' hvert hconn
    O_ext hext O hne
  obtain ⟨q, q', hcl, hc, hq, hcl', hc', hq'⟩ := hsimple O hne
  exact B.exists_bounded_plOrbitFace_homeomorph vert P P' hvert hconn f O q q'
    hcl hc hq hcl' hc' hq' hb hb'


omit [Finite V] in
/-- Helper toward Proposition 5.16: a face extension agreeing on its
frontier has the prescribed inverse values on the target frontier. -/
theorem plOrbitFace_homeomorph_symm_agrees
    (f : B.PLImageHomeomorph vert P P') (O : D39BallFaceCycleOrbit B)
    (H : closure (B.plOrbitFace vert P hvert O).val ≃ₜ
      closure (B.plOrbitFace vert P' hvert O).val)
    (hH : ∀ (x : closure (B.plOrbitFace vert P hvert O).val)
      (hx : (x : ℂ) ∈ P.image),
      (H x : ℂ) = (f.toHomeomorph ⟨x, hx⟩ : ℂ))
    (y : closure (B.plOrbitFace vert P' hvert O).val)
    (hy : (y : ℂ) ∈ P'.image) :
    (H.symm y : ℂ) = (f.toHomeomorph.symm ⟨y, hy⟩ : ℂ) := by
  have hyfront : (y : ℂ) ∈ frontier (B.plOrbitFace vert P' hvert O).val :=
    (P'.closure_face_inter_image_eq_frontier hvert _) ▸ ⟨y.property, hy⟩
  have hybound : (y : ℂ) ∈ B.plOrbitBoundary vert P' O := by
    rw [← B.frontier_plOrbitFace_eq_plOrbitBoundary vert P' hvert hconn O]
    exact hyfront
  let x : P.image := f.toHomeomorph.symm ⟨y, hy⟩
  have hxbound : (x : ℂ) ∈ B.plOrbitBoundary vert P O := by
    apply (B.mem_plOrbitBoundary_iff_of_arc_image vert P P'
      f.toHomeomorph f.arc_image O x).mpr
    simpa only [x, Homeomorph.apply_symm_apply] using hybound
  have hxcl : (x : ℂ) ∈ closure (B.plOrbitFace vert P hvert O).val := by
    apply frontier_subset_closure
    rw [B.frontier_plOrbitFace_eq_plOrbitBoundary vert P hvert hconn O]
    exact hxbound
  have heq : H ⟨x, hxcl⟩ = y := by
    apply Subtype.ext
    exact (hH ⟨x, hxcl⟩ x.property).trans
      (congrArg Subtype.val (f.toHomeomorph.apply_symm_apply ⟨y, hy⟩))
  exact congrArg Subtype.val ((congrArg H.symm heq).symm.trans (H.symm_apply_apply _))

end D39FiniteBall

/-- Helper toward Proposition 5.16: compatible homeomorphisms on finitely
many closed planar sets glue on their unions, including noncompact sets. -/
theorem exists_homeomorph_iUnion_closed_sets
    {ι : Type*} [Finite ι] (s t : ι → Set ℂ)
    (hs : ∀ i, IsClosed (s i)) (ht : ∀ i, IsClosed (t i))
    (e : ∀ i, s i ≃ₜ t i)
    (hagree : ∀ i j (x : ℂ) (hi : x ∈ s i) (hj : x ∈ s j),
      (e i ⟨x, hi⟩ : ℂ) = (e j ⟨x, hj⟩ : ℂ))
    (hagree' : ∀ i j (y : ℂ) (hi : y ∈ t i) (hj : y ∈ t j),
      ((e i).symm ⟨y, hi⟩ : ℂ) = ((e j).symm ⟨y, hj⟩ : ℂ)) :
    ∃ H : (⋃ i, s i) ≃ₜ (⋃ i, t i),
      ∀ i (x : s i),
        (H ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (e i x : ℂ) := by
  let a : ι → Set (⋃ i, s i) := fun i => {x | (x : ℂ) ∈ s i}
  let b : ι → Set (⋃ i, t i) := fun i => {x | (x : ℂ) ∈ t i}
  have ha : ∀ i, IsClosed (a i) := fun i => (hs i).preimage continuous_subtype_val
  have hb : ∀ i, IsClosed (b i) := fun i => (ht i).preimage continuous_subtype_val
  have hac : ⋃ i, a i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hbc : ⋃ i, b i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  let f : ∀ i, a i → (⋃ i, t i) := fun i x =>
    ⟨e i ⟨x.val.val, x.property⟩, mem_iUnion.mpr ⟨i, (e i _).property⟩⟩
  let g : ∀ i, b i → (⋃ i, s i) := fun i y =>
    ⟨(e i).symm ⟨y.val.val, y.property⟩,
      mem_iUnion.mpr ⟨i, ((e i).symm _).property⟩⟩
  have hf : ∀ i, Continuous (f i) := by
    intro i
    exact (continuous_subtype_val.comp ((e i).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))).subtype_mk _
  have hg : ∀ i, Continuous (g i) := by
    intro i
    exact (continuous_subtype_val.comp ((e i).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))).subtype_mk _
  obtain ⟨F, hFc, hF⟩ := exists_continuous_map_of_finite_closed_cover a ha hac f hf
    (fun i j x hi hj => Subtype.ext (hagree i j x hi hj))
  obtain ⟨G, hGc, hG⟩ := exists_continuous_map_of_finite_closed_cover b hb hbc g hg
    (fun i j y hi hj => Subtype.ext (hagree' i j y hi hj))
  have hleft : Function.LeftInverse G F := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    rw [hF i ⟨x, hi⟩, hG i ⟨f i ⟨x, hi⟩, (e i _).property⟩]
    apply Subtype.ext
    change ((e i).symm (e i ⟨x.val, hi⟩) : ℂ) = x.val
    exact congrArg Subtype.val ((e i).symm_apply_apply ⟨x, hi⟩)
  have hright : Function.RightInverse G F := by
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp y.property
    rw [hG i ⟨y, hi⟩, hF i ⟨g i ⟨y, hi⟩, ((e i).symm _).property⟩]
    apply Subtype.ext
    change (e i ((e i).symm ⟨y.val, hi⟩) : ℂ) = y.val
    exact congrArg Subtype.val ((e i).apply_symm_apply ⟨y, hi⟩)
  refine ⟨{
    toFun := F
    invFun := G
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hFc
    continuous_invFun := hGc }, ?_⟩
  intro i x
  exact congrArg Subtype.val (hF i ⟨⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩, x.property⟩)


namespace D39FiniteBall
variable {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)
  (hconn : ∀ d e : B.D, Relation.EqvGen
    (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
include hconn

/-- Helper toward Proposition 5.16: extensions on any finite collection
of corresponding faces glue with the drawing map on the union of their
closures. Both directions agree on every overlap. -/
theorem exists_homeomorph_union_selected_plOrbitFaces
    (f : B.PLImageHomeomorph vert P P')
    (A : Set (D39BallFaceCycleOrbit B)) [Finite A]
    (extensions : ∀ O : A,
      ∃ H : closure (B.plOrbitFace vert P hvert O.val).val ≃ₜ
          closure (B.plOrbitFace vert P' hvert O.val).val,
        ∀ (x : closure (B.plOrbitFace vert P hvert O.val).val)
          (hx : (x : ℂ) ∈ P.image),
          (H x : ℂ) = (f.toHomeomorph ⟨x, hx⟩ : ℂ)) :
    ∃ H : ↥(P.image ∪ ⋃ O : A, closure (B.plOrbitFace vert P hvert O.val).val) ≃ₜ
        ↥(P'.image ∪ ⋃ O : A, closure (B.plOrbitFace vert P' hvert O.val).val),
      ∀ x : P.image,
        (H ⟨x, Or.inl x.property⟩ : ℂ) = (f.toHomeomorph x : ℂ) := by
  classical
  choose H hH using extensions
  have hH' (O : A) := B.plOrbitFace_homeomorph_symm_agrees vert P P' hvert hconn
    f O.val (H O) (hH O)
  let s : Option A → Set ℂ
    | none => P.image
    | some O => closure (B.plOrbitFace vert P hvert O.val).val
  let t : Option A → Set ℂ
    | none => P'.image
    | some O => closure (B.plOrbitFace vert P' hvert O.val).val
  let e : ∀ i, s i ≃ₜ t i
    | none => f.toHomeomorph
    | some O => H O
  have hs : ∀ i, IsClosed (s i) := by
    rintro (_ | O)
    · exact P.isCompact_image.isClosed
    · exact isClosed_closure
  have ht : ∀ i, IsClosed (t i) := by
    rintro (_ | O)
    · exact P'.isCompact_image.isClosed
    · exact isClosed_closure
  have hagree : ∀ i j (x : ℂ) (hi : x ∈ s i) (hj : x ∈ s j),
      (e i ⟨x, hi⟩ : ℂ) = (e j ⟨x, hj⟩ : ℂ) := by
    rintro (_ | O) (_ | Q) x hi hj
    · rfl
    · exact (hH Q ⟨x, hj⟩ hi).symm
    · exact hH O ⟨x, hi⟩ hj
    · by_cases heq : O = Q
      · subst Q; rfl
      have hne : B.plOrbitFace vert P hvert O.val ≠ B.plOrbitFace vert P hvert Q.val :=
        fun h => heq (Subtype.ext (B.plOrbitFace_injective vert P hvert hconn h))
      have hx := P.closure_face_inter_subset_image hvert _ _ hne ⟨hi, hj⟩
      exact (hH O ⟨x, hi⟩ hx).trans (hH Q ⟨x, hj⟩ hx).symm
  have hagree' : ∀ i j (y : ℂ) (hi : y ∈ t i) (hj : y ∈ t j),
      ((e i).symm ⟨y, hi⟩ : ℂ) = ((e j).symm ⟨y, hj⟩ : ℂ) := by
    rintro (_ | O) (_ | Q) y hi hj
    · rfl
    · exact (hH' Q ⟨y, hj⟩ hi).symm
    · exact hH' O ⟨y, hi⟩ hj
    · by_cases heq : O = Q
      · subst Q; rfl
      have hne : B.plOrbitFace vert P' hvert O.val ≠ B.plOrbitFace vert P' hvert Q.val :=
        fun h => heq (Subtype.ext (B.plOrbitFace_injective vert P' hvert hconn h))
      have hy := P'.closure_face_inter_subset_image hvert _ _ hne ⟨hi, hj⟩
      exact (hH' O ⟨y, hi⟩ hy).trans (hH' Q ⟨y, hj⟩ hy).symm
  obtain ⟨G, hG⟩ := exists_homeomorph_iUnion_closed_sets s t hs ht e hagree hagree'
  have hsUnion : (⋃ i, s i) =
      P.image ∪ ⋃ O : A, closure (B.plOrbitFace vert P hvert O.val).val := by
    rw [iUnion_option]
  have htUnion : (⋃ i, t i) =
      P'.image ∪ ⋃ O : A, closure (B.plOrbitFace vert P' hvert O.val).val := by
    rw [iUnion_option]
  refine ⟨(Homeomorph.setCongr hsUnion.symm).trans
    (G.trans (Homeomorph.setCongr htUnion)), ?_⟩
  intro x
  exact hG none x

/-- Helper toward Proposition 5.16: the marked exterior and simple bounded
walks yield a homeomorphism of the filled finite drawings, with the prescribed
values on the entire drawing image. -/
theorem exists_bounded_faces_filling_homeomorph
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hsimple : ∀ O : D39BallFaceCycleOrbit B, O ≠ O_ext →
      ∃ q q' : Polyline,
        q.start = q.finish ∧ q.IsCyclicSimple ∧
        q.image = B.plOrbitBoundary vert P O ∧
        q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
        q'.image = B.plOrbitBoundary vert P' O) :
    ∃ H : ↥(P.image ∪ ⋃ O : {O : D39BallFaceCycleOrbit B // O ≠ O_ext},
          closure (B.plOrbitFace vert P hvert O.val).val) ≃ₜ
        ↥(P'.image ∪ ⋃ O : {O : D39BallFaceCycleOrbit B // O ≠ O_ext},
          closure (B.plOrbitFace vert P' hvert O.val).val),
      ∀ x : P.image,
        (H ⟨x, Or.inl x.property⟩ : ℂ) = (f.toHomeomorph x : ℂ) := by
  classical
  have : Finite (D39BallFaceCycleOrbit B) := Finite.of_injective
    (fun O : D39BallFaceCycleOrbit B => O.val) Subtype.val_injective
  exact B.exists_homeomorph_union_selected_plOrbitFaces vert P P' hvert hconn f
    {O | O ≠ O_ext} (fun O => B.exists_all_bounded_plOrbitFace_homeomorphs
      vert P P' hvert hconn f O_ext hext hsimple O.val O.property)


omit hconn [Finite V] in
/-- Helper toward Proposition 5.16: the drawing image and all closed orbit
faces cover the entire plane. This uses geometric face surjectivity. -/
theorem image_union_closure_plOrbitFaces_eq_univ :
    P.image ∪ ⋃ O : (univ : Set (D39BallFaceCycleOrbit B)),
      closure (B.plOrbitFace vert P hvert O.val).val = univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ P.image
  · exact Or.inl hx
  · obtain ⟨F, hxF⟩ := (P.faces_cover_compl x).mpr hx
    obtain ⟨O, rfl⟩ := B.plOrbitFace_surjective vert P hvert F
    exact Or.inr (mem_iUnion.mpr ⟨⟨O, mem_univ O⟩, subset_closure hxF⟩)

/-- Helper toward Proposition 5.16: with the exterior marked in both
drawings, simple bounded boundaries, and an explicitly supplied extension
over the closed exterior agreeing with the prescribed frontier map, there
is a plane homeomorphism mapping each labeled arc onto its counterpart. -/
theorem exists_plane_homeomorph_of_outer_face_extension
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hsimple : ∀ O : D39BallFaceCycleOrbit B, O ≠ O_ext →
      ∃ q q' : Polyline,
        q.start = q.finish ∧ q.IsCyclicSimple ∧
        q.image = B.plOrbitBoundary vert P O ∧
        q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
        q'.image = B.plOrbitBoundary vert P' O)
    (outer_face_extension :
      ∃ H : closure (B.plOrbitFace vert P hvert O_ext).val ≃ₜ
          closure (B.plOrbitFace vert P' hvert O_ext).val,
        ∀ (x : ℂ) (hx : x ∈ frontier (B.plOrbitFace vert P hvert O_ext).val),
          (H ⟨x, frontier_subset_closure hx⟩ : ℂ) =
            (f.toHomeomorph ⟨x,
              (P.face_open_frontier_subset_image hvert _).2 hx⟩ : ℂ)) :
    ∃ H : ℂ ≃ₜ ℂ,
      (∀ x : P.image, H x = (f.toHomeomorph x : ℂ)) ∧
        ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image := by
  classical
  have : Finite (D39BallFaceCycleOrbit B) := Finite.of_injective
    (fun O : D39BallFaceCycleOrbit B => O.val) Subtype.val_injective
  have extensions (O : (univ : Set (D39BallFaceCycleOrbit B))) :
      ∃ H : closure (B.plOrbitFace vert P hvert O.val).val ≃ₜ
          closure (B.plOrbitFace vert P' hvert O.val).val,
        ∀ (x : closure (B.plOrbitFace vert P hvert O.val).val)
          (hx : (x : ℂ) ∈ P.image),
          (H x : ℂ) = (f.toHomeomorph ⟨x, hx⟩ : ℂ) := by
    by_cases hO : O.val = O_ext
    · obtain ⟨H, hH⟩ := outer_face_extension
      subst_vars
      refine ⟨H, ?_⟩
      intro x hx
      exact hH x ((P.closure_face_inter_image_eq_frontier hvert _) ▸ ⟨x.property, hx⟩)
    · exact B.exists_all_bounded_plOrbitFace_homeomorphs vert P P' hvert hconn
        f O_ext hext hsimple O.val hO
  obtain ⟨G, hG⟩ := B.exists_homeomorph_union_selected_plOrbitFaces
    vert P P' hvert hconn f univ extensions
  let a := (Homeomorph.setCongr
    (B.image_union_closure_plOrbitFaces_eq_univ vert P hvert)).trans
      (Homeomorph.Set.univ ℂ)
  let b := (Homeomorph.setCongr
    (B.image_union_closure_plOrbitFaces_eq_univ vert P' hvert)).trans
      (Homeomorph.Set.univ ℂ)
  let H : ℂ ≃ₜ ℂ := a.symm.trans (G.trans b)
  have hH (x : P.image) : H x = (f.toHomeomorph x : ℂ) := hG x
  refine ⟨H, hH, ?_⟩
  intro d
  rw [← f.arc_image d]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxi : x ∈ P.image := Or.inr ⟨d, hx⟩
    exact ⟨⟨x, hxi⟩, hx, (hH ⟨x, hxi⟩).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hH x⟩


/-- Helper toward Proposition 5.16: an orbit face is bounded precisely
when it is different from the explicitly marked unbounded orbit. -/
theorem isBounded_plOrbitFace_iff_ne_external
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : ¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val)
    (O : D39BallFaceCycleOrbit B) :
    Bornology.IsBounded (B.plOrbitFace vert P hvert O).val ↔ O ≠ O_ext := by
  constructor
  · intro hb heq
    exact hext (heq ▸ hb)
  · intro hne
    exact P.isBounded_face_of_ne_unbounded _ hext _
      (fun h => hne (B.plOrbitFace_injective vert P hvert hconn h))

/-- Helper toward Proposition 5.16: removing the marked exterior orbit
selects exactly the closures of all bounded faces. -/
theorem iUnion_nonexternal_closure_plOrbitFaces_eq_bounded
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : ¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) :
    (⋃ O : {O : D39BallFaceCycleOrbit B // O ≠ O_ext},
      closure (B.plOrbitFace vert P hvert O.val).val) =
      ⋃ O : D39BallFaceCycleOrbit B,
        ⋃ (_ : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val),
          closure (B.plOrbitFace vert P hvert O).val := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨⟨O, hne⟩, hx⟩
    exact ⟨O, (B.isBounded_plOrbitFace_iff_ne_external vert P hvert hconn
      O_ext hext O).mpr hne, hx⟩
  · rintro ⟨O, hb, hx⟩
    exact ⟨⟨O, (B.isBounded_plOrbitFace_iff_ne_external vert P hvert hconn
      O_ext hext O).mp hb⟩, hx⟩

/-- Helper toward Proposition 5.16: a homeomorphism on the drawing image
extends to the union with the closures of all bounded faces. The simple-walk
hypothesis is exactly the symmetric bounded-orbit formulation. -/
theorem exists_homeomorph_union_bounded_plOrbitFaces
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hsimple : ∀ O : D39BallFaceCycleOrbit B,
      Bornology.IsBounded (B.plOrbitFace vert P hvert O).val ∨
        Bornology.IsBounded (B.plOrbitFace vert P' hvert O).val →
      ∃ q q' : Polyline,
        q.start = q.finish ∧ q.IsCyclicSimple ∧
        q.image = B.plOrbitBoundary vert P O ∧
        q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
        q'.image = B.plOrbitBoundary vert P' O) :
    ∃ H : ↥(P.image ∪ ⋃ O : D39BallFaceCycleOrbit B,
          ⋃ (_ : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val),
            closure (B.plOrbitFace vert P hvert O).val) ≃ₜ
        ↥(P'.image ∪ ⋃ O : D39BallFaceCycleOrbit B,
          ⋃ (_ : Bornology.IsBounded (B.plOrbitFace vert P' hvert O).val),
            closure (B.plOrbitFace vert P' hvert O).val),
      ∀ x : P.image,
        (H ⟨x, Or.inl x.property⟩ : ℂ) = (f.toHomeomorph x : ℂ) := by
  obtain ⟨H, hH⟩ := B.exists_bounded_faces_filling_homeomorph vert P P' hvert hconn
    f O_ext hext (fun O hne => hsimple O (Or.inl
      ((B.isBounded_plOrbitFace_of_ne_external vert P P' hvert hconn
        O_ext hext O hne).1)))
  have hs := congrArg (fun s : Set ℂ => P.image ∪ s)
    (B.iUnion_nonexternal_closure_plOrbitFaces_eq_bounded vert P hvert hconn O_ext hext.1)
  have ht := congrArg (fun s : Set ℂ => P'.image ∪ s)
    (B.iUnion_nonexternal_closure_plOrbitFaces_eq_bounded vert P' hvert hconn O_ext hext.2)
  refine ⟨(Homeomorph.setCongr hs.symm).trans
    (H.trans (Homeomorph.setCongr ht)), ?_⟩
  exact hH

end D39FiniteBall
end DirectedDistances.PlanarMap
end
