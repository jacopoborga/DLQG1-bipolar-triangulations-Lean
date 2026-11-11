/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness3

/-! # Finite augmentation carriers and exterior parents

the sole coordinator. No drawing uniqueness or numbered result is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: a finite augmented vertex carrier is
equivalent to the original vertices plus finitely many new vertices, with
the original embedding sent exactly to `Sum.inl`. -/
theorem drawing_exists_sum_fin_equiv {V W : Type*} [Finite W] (σ : V ↪ W) :
    ∃ (n : ℕ) (e : W ≃ V ⊕ Fin n), ∀ x, e (σ x) = Sum.inl x := by
  classical
  let T := (Set.range σ)ᶜ
  let := Fintype.ofFinite T
  let f : V ⊕ Fin (Fintype.card T) ≃ W :=
    (Equiv.sumCongr (Equiv.ofInjective σ σ.injective)
      (Fintype.equivFin T).symm).trans (Equiv.Set.sumCompl (Set.range σ))
  refine ⟨Fintype.card T, f.symm, fun x => ?_⟩
  apply f.injective
  exact (f.apply_symm_apply (σ x)).trans rfl

/-- Helper toward Proposition 5.16: surjectivity of the augmented dart-to-vertex
map supplies the finiteness needed for the carrier conversion. -/
theorem drawing_exists_sum_fin_equiv_of_surjective
    {V W : Type*} (C : D39FiniteBall) (v : C.D → W)
    (hv : Function.Surjective v) (σ : V ↪ W) :
    ∃ (n : ℕ) (e : W ≃ V ⊕ Fin n), ∀ x, e (σ x) = Sum.inl x := by
  let : Finite W := Finite.of_surjective v hv
  exact drawing_exists_sum_fin_equiv σ

end D39FiniteBall

namespace PLDrawing

/-- Helper toward Proposition 5.16: change only vertex names along an
equivalence, keeping every dart and its polyline fixed. -/
@[expose] def reindexVertices
    {D V W : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (e : V ≃ W) :
    PLDrawing D W flip rot (e ∘ vert) where
  flip_involutive := P.flip_involutive
  flip_ne := P.flip_ne
  vert_rotation := fun d => congrArg e (P.vert_rotation d)
  pos := P.pos ∘ e.symm
  pos_injective := P.pos_injective.comp e.symm.injective
  arc := P.arc
  arc_simple := P.arc_simple
  arc_length := P.arc_length
  arc_start := by intro d; exact (P.arc_start d).trans (by simp only [Function.comp_apply, e.symm_apply_apply])
  arc_finish := by intro d; exact (P.arc_finish d).trans (by simp only [Function.comp_apply, e.symm_apply_apply])
  arc_flip := P.arc_flip
  interior_disjoint := P.interior_disjoint
  interior_avoids_vertices := fun d w => P.interior_avoids_vertices d (e.symm w)
  locally_finite := P.locally_finite
  initial_nonzero := P.initial_nonzero
  initial_arg_injective := fun d f h => P.initial_arg_injective d f (e.injective h)
  rotation_agreement := by
    intro d
    have hs : {f | (e ∘ vert) f = (e ∘ vert) d} = {f | vert f = vert d} := by
      ext f
      exact e.injective.eq_iff
    rw [hs]
    exact P.rotation_agreement d

/-- Helper toward Proposition 5.16: renaming vertices leaves the geometric
drawing image unchanged. -/
theorem reindexVertices_image
    {D V W : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (e : V ≃ W) :
    (P.reindexVertices e).image = P.image := by
  ext z
  constructor
  · rintro (⟨w, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨e.symm w, rfl⟩
    · exact Or.inr ⟨d, hd⟩
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨e v, by change P.pos (e.symm (e v)) = P.pos v; rw [e.symm_apply_apply]⟩
    · exact Or.inr ⟨d, hd⟩

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: renaming the vertex carrier preserves
the complete open face on the left of every dart. -/
theorem plDartFace_reindexVertices
    {V W : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (e : V ≃ W) (d : B.D) :
    (B.plDartFace (e ∘ vert) (P.reindexVertices e)
      (e.surjective.comp hvert) d).val = (B.plDartFace vert P hvert d).val := by
  let F : (P.reindexVertices e).Face :=
    ⟨(B.plDartFace vert P hvert d).val, by
      rw [P.reindexVertices_image e]
      exact (B.plDartFace vert P hvert d).property⟩
  have hb : (P.reindexVertices e).dartBorders d F :=
    (B.plDartFace_eq_iff vert P hvert d _).mp rfl
  exact congrArg Subtype.val
    ((B.plDartFace_eq_iff (e ∘ vert) (P.reindexVertices e)
      (e.surjective.comp hvert) d F).mpr hb)

/-- Helper toward Proposition 5.16: renaming vertices preserves every
geometric orbit face, hence also its closure and boundedness. -/
theorem plOrbitFace_reindexVertices
    {V W : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (e : V ≃ W)
    (O : D39BallFaceCycleOrbit B) :
    (B.plOrbitFace (e ∘ vert) (P.reindexVertices e)
      (e.surjective.comp hvert) O).val = (B.plOrbitFace vert P hvert O).val := by
  exact B.plDartFace_reindexVertices vert P hvert e O.property.choose

/-- Helper toward Proposition 5.16: an existing finite augmentation can
be expressed on `V ⊕ Fin n` simultaneously in both drawings. The original
vertex embedding becomes `Sum.inl`; all polylines and open orbit faces
are preserved exactly, without a drawing-uniqueness assumption. -/
theorem drawing_exists_sum_fin_reindex
    {V W : Type*} (C : D39FiniteBall) (v : C.D → W)
    (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hv : Function.Surjective v) (σ : V ↪ W) :
    ∃ (n : ℕ) (e : W ≃ V ⊕ Fin n)
      (R R' : PLDrawing C.D (V ⊕ Fin n) C.map.edgeInv C.map.rot (e ∘ v))
      (hw : Function.Surjective (e ∘ v)),
      (∀ x, e (σ x) = Sum.inl x) ∧
      (∀ x, R.pos (Sum.inl x) = Q.pos (σ x)) ∧
      (∀ x, R'.pos (Sum.inl x) = Q'.pos (σ x)) ∧
      (∀ d, R.arc d = Q.arc d) ∧ (∀ d, R'.arc d = Q'.arc d) ∧
      R.image = Q.image ∧ R'.image = Q'.image ∧
      (∀ O, (C.plOrbitFace (e ∘ v) R hw O).val =
        (C.plOrbitFace v Q hv O).val) ∧
      (∀ O, (C.plOrbitFace (e ∘ v) R' hw O).val =
        (C.plOrbitFace v Q' hv O).val) ∧
      (∀ (f : ℕ → C.D) (S : Set ℕ),
        Set.InjOn (fun k => (e ∘ v) (f k)) S ↔ Set.InjOn (fun k => v (f k)) S) := by
  obtain ⟨n, e, he⟩ := C.drawing_exists_sum_fin_equiv_of_surjective v hv σ
  refine ⟨n, e, Q.reindexVertices e, Q'.reindexVertices e,
    e.surjective.comp hv, he, ?_, ?_, fun _ => rfl, fun _ => rfl,
    Q.reindexVertices_image e, Q'.reindexVertices_image e,
    C.plOrbitFace_reindexVertices v Q hv e,
    C.plOrbitFace_reindexVertices v Q' hv e, ?_⟩
  · intro x
    change Q.pos (e.symm (Sum.inl x)) = Q.pos (σ x)
    rw [← he x, e.symm_apply_apply]
  · intro x
    change Q'.pos (e.symm (Sum.inl x)) = Q'.pos (σ x)
    rw [← he x, e.symm_apply_apply]
  · intro f S
    constructor
    · intro h a ha b hb hab
      exact h ha hb (congrArg e hab)
    · intro h a ha b hb hab
      exact h ha hb (e.injective hab)

end D39FiniteBall

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: the triangulation away from one marked
orbit can be realized on the DU1 carrier `V ⊕ Fin n`. The marked open face,
all original data, and the joint closed-face decomposition are retained.
This makes no simplicity or period assertion for the marked orbit. -/
theorem exists_sum_fin_triangulated_drawings_away_from_orbit_with_common_index
    {V : Type u} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a : B.D) :
    ∃ (n : ℕ) (C : D39FiniteBall) (w : C.D → V ⊕ Fin n)
      (ι : B.D ↪ C.D)
      (R R' : PLDrawing C.D (V ⊕ Fin n) C.map.edgeInv C.map.rot w)
      (hw : Function.Surjective w)
      (I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C)),
      (∀ x y : C.D, Relation.EqvGen
        (fun z t => C.map.rot z = t ∨ C.map.edgeInv z = t) x y) ∧
      C.rootDart = ι B.rootDart ∧
      (∀ x, C.map.edgeInv (ι x) = ι (B.map.edgeInv x)) ∧
      (∀ x, w (ι x) = Sum.inl (vert x)) ∧
      (∀ x, C.missing (ι x) ↔ B.missing x) ∧
      (∀ x, C.tail (ι x) ↔ B.tail x) ∧
      (∀ x, R.pos (Sum.inl x) = P.pos x) ∧
      (∀ x, R'.pos (Sum.inl x) = P'.pos x) ∧
      (∀ x, R.arc (ι x) = P.arc x) ∧
      (∀ x, R'.arc (ι x) = P'.arc x) ∧
      (∀ z, C.map.faceSucc.SameCycle (ι a) z ↔
        ∃ y, B.map.faceSucc.SameCycle a y ∧ z = ι y) ∧
      (∀ z, ¬ C.map.faceSucc.SameCycle (ι a) z →
        Function.minimalPeriod C.map.faceSucc z = 3 ∧
        Set.InjOn (fun k : ℕ => w ((C.map.faceSucc : C.D → C.D)^[k] z))
          (Set.Iio 3)) ∧
      (C.plDartFace w R hw (ι a)).val = (B.plDartFace vert P hvert a).val ∧
      (C.plDartFace w R' hw (ι a)).val = (B.plDartFace vert P' hvert a).val ∧
      (∀ O, closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace w R hw S).val) ∧
      (∀ O, closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace w R' hw S).val) := by
  obtain ⟨W, C, v, ι, σ, Q, Q', hv, I, hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', horbit, htri, hface, hface', hcover, hcover'⟩ :=
    B.exists_triangulated_drawings_away_from_orbit_with_common_index
      vert P P' hvert hconn a
  obtain ⟨n, e, heσ⟩ := C.drawing_exists_sum_fin_equiv_of_surjective v hv σ
  let R := Q.reindexVertices e
  let R' := Q'.reindexVertices e
  have hw : Function.Surjective (e ∘ v) := e.surjective.comp hv
  refine ⟨n, C, e ∘ v, ι, R, R', hw, I, hc, hr, hf, ?_, hm, ht,
    ?_, ?_, he, he', horbit, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change e (v (ι x)) = Sum.inl (vert x)
    rw [hvertex x, heσ]
  · intro x
    change Q.pos (e.symm (Sum.inl x)) = P.pos x
    rw [← heσ x, e.symm_apply_apply]
    exact hp x
  · intro x
    change Q'.pos (e.symm (Sum.inl x)) = P'.pos x
    rw [← heσ x, e.symm_apply_apply]
    exact hp' x
  · intro z hz
    obtain ⟨hperiod, hinj⟩ := htri z hz
    refine ⟨hperiod, ?_⟩
    intro k hk l hl hkl
    exact hinj hk hl (e.injective hkl)
  · exact (C.plDartFace_reindexVertices v Q hv e (ι a)).trans hface
  · exact (C.plDartFace_reindexVertices v Q' hv e (ι a)).trans hface'
  · intro O
    change closure (B.plOrbitFace vert P hvert O).val =
      ⋃ S ∈ I O, closure (C.plOrbitFace (e ∘ v) (Q.reindexVertices e) hw S).val
    simp_rw [C.plOrbitFace_reindexVertices v Q hv e]
    exact hcover O
  · intro O
    change closure (B.plOrbitFace vert P' hvert O).val =
      ⋃ S ∈ I O, closure (C.plOrbitFace (e ∘ v) (Q'.reindexVertices e) hw S).val
    simp_rw [C.plOrbitFace_reindexVertices v Q' hv e]
    exact hcover' O

end D39FiniteBall

namespace PLDrawing

/-- Helper toward Proposition 5.16: every corner sector is bounded, since
its defining radial parameter remains inside the vertex ball. This does
not assert boundedness of the entire face containing that sector. -/
theorem isBounded_initialSector
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (r : ℝ) :
    Bornology.IsBounded (P.initialSector d r) := by
  exact Metric.isBounded_ball.subset (P.initialSector_subset_ball d r)

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: in a finite refinement of a drawing,
every unbounded child lies in the original unbounded face. Boundedness of
the other original faces rules out all other parents. -/
theorem drawing_unbounded_face_subset_external
    {V W : Type*} [Finite V] (B C : D39FiniteBall)
    (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (himage : P.image ⊆ Q.image) (F : P.Face)
    (hF : ¬ Bornology.IsBounded F.val) (G : Q.Face)
    (hG : ¬ Bornology.IsBounded G.val) : G.val ⊆ F.val := by
  obtain ⟨H, hH, _⟩ := B.drawing_face_unique_parent C vert v P Q himage G
  by_cases he : H = F
  · exact he ▸ hH
  · exact (hG ((P.isBounded_face_of_ne_unbounded F hF H he).subset hH)).elim

/-- Helper toward Proposition 5.16: a finite refinement has exactly one
unbounded child orbit of the original exterior. A sufficiently large
closed ball contains the whole augmented drawing, and its complement is
contained in this child's open face. No matching between drawings is
assumed or concluded. -/
theorem drawing_existsUnique_unbounded_child_orbit
    {V W : Type*} [Finite V] (B C : D39FiniteBall)
    (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hc : ∀ x y : C.D, Relation.EqvGen
      (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y)
    (himage : P.image ⊆ Q.image) (O : D39BallFaceCycleOrbit B)
    (hext : ¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O).val) :
    ∃! S : D39BallFaceCycleOrbit C,
      (¬ Bornology.IsBounded (C.plOrbitFace v Q hv S).val) ∧
      (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val ∧
      ∃ R : ℝ, Q.image ⊆ Metric.closedBall 0 R ∧
        (Metric.closedBall (0 : ℂ) R)ᶜ ⊆ (C.plOrbitFace v Q hv S).val := by
  let : Finite W := Finite.of_surjective v hv
  obtain ⟨U, hU, huniq⟩ := Q.existsUnique_not_isBounded_face
  obtain ⟨S, hS⟩ := C.plOrbitFace_surjective v Q hv U
  have hUS : ¬ Bornology.IsBounded (C.plOrbitFace v Q hv S).val := by
    rw [hS]
    exact hU
  refine ⟨S, ⟨hUS,
    B.drawing_unbounded_face_subset_external C vert v P Q himage _ hext _ hUS,
    ?_⟩, ?_⟩
  · obtain ⟨R, hR, hout, _⟩ := Q.exists_closedBall_containing_other_faces U hU
    exact ⟨R, hR, hS.symm ▸ hout⟩
  · intro T hT
    apply C.plOrbitFace_injective v Q hv hc
    exact (huniq _ hT.1).trans hS.symm

/-- Helper toward Proposition 5.16: the two unbounded children of a common
refinement have the same original exterior parent index. Both children
belong to that parent's child set in both drawings. Equality of the two
augmented child orbits is a separate assertion. -/
theorem drawing_unbounded_children_common_parent
    {V W : Type*} [Finite V] (B C : D39FiniteBall)
    (vert : B.D → V) (v : C.D → W)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (himage : P.image ⊆ Q.image) (himage' : P'.image ⊆ Q'.image)
    (hparent : ∀ z, ∃ x,
      (C.plDartFace v Q hv z).val ⊆ (B.plDartFace vert P hvert x).val ∧
      (C.plDartFace v Q' hv z).val ⊆ (B.plDartFace vert P' hvert x).val)
    (O : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O).val))
    (S T : D39BallFaceCycleOrbit C)
    (hS : ¬ Bornology.IsBounded (C.plOrbitFace v Q hv S).val)
    (hT : ¬ Bornology.IsBounded (C.plOrbitFace v Q' hv T).val) :
    ((C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val) ∧
    ((C.plOrbitFace v Q' hv S).val ⊆ (B.plOrbitFace vert P' hvert O).val) ∧
    ((C.plOrbitFace v Q hv T).val ⊆ (B.plOrbitFace vert P hvert O).val) ∧
    ((C.plOrbitFace v Q' hv T).val ⊆ (B.plOrbitFace vert P' hvert O).val) := by
  obtain ⟨I, hI, hI', _, _⟩ :=
    B.drawing_exists_common_closed_face_index C vert v P P' Q Q' hvert hv hconn
      himage himage' hparent
  have hs := B.drawing_unbounded_face_subset_external C vert v P Q himage
    _ hext.1 _ hS
  have ht := B.drawing_unbounded_face_subset_external C vert v P' Q' himage'
    _ hext.2 _ hT
  exact ⟨hs, (hI' O S).mp ((hI O S).mpr hs),
    (hI O T).mp ((hI' O T).mpr ht), ht⟩

end D39FiniteBall

/-! ## Remaining geometric constructions

The carrier conversion is proved above, including preservation of the open
orbit faces, closed-face decompositions, and full-period vertex injectivity.
It neither identifies the exterior child nor inserts frame edges.

Three approaches to matching the exterior children were examined here.

1. Common-parent containment: `drawing_unbounded_children_common_parent`
   proves all four containments. The existing
   `drawing_common_parent_containment_iff` (through the common closed-face
   index theorem) synchronizes the old parent, not individual children of
   that parent. There is no injectivity assertion for a parent's child set.
2. Bounded sectors and insertion faces: `isBounded_initialSector` proves
   the sector bound. `exists_chord_arc_in_face` confines the chord interior
   to the old open face; `chordMap_faceSucc_split_orbits` identifies the two
   new combinatorial orbits. Neither bounds the entire cut-off face when
   the old face is exterior. A bounded subset of a face does not bound the
   face. A global side identification for the inserted arc remains needed.
3. Exterior charts: `Polyline.exists_outer_chart` assumes a cyclically
   simple boundary. The old exterior walk may repeat vertices. Applying the
   chart after arbitrary stars first requires locating the exterior triangle;
   no common triangle label follows from the vertex-image formula alone.
   Moreover an arbitrary chart does not preserve polygonal arcs on pullback.

For square-frame insertion, the following three routes were also examined.
The existing common exterior square and far pendant do not guarantee that
the pendant meets the square only at its endpoint. The inspected
`exists_first_contact_segment` clips a segment; applying it to a whole
pendant requires an additional prefix construction and a proved corner slot.
The second route, choosing a square after the entire pendant, gives a square
disjoint from that pendant but leaves its tip strictly inside, so attachment
to a frame corner still requires a controlled continuation. The third route,
transport through the outer chart and square cone, supplies continuous
extensions for already simple boundaries, not the required PL insertion
drawing with prescribed old arcs. These are geometric proof obligations,
not extra hypotheses of any declaration in this file.

The remaining targets below are comments only. No matching or construction
sole coordinator.

### Matching exterior child in a single star (full binders)

∀ {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a : B.D)
    (hext : (¬ Bornology.IsBounded (B.plDartFace vert P hvert a).val) ∧
      (¬ Bornology.IsBounded (B.plDartFace vert P' hvert a).val)),
  ∃ (C : D39FiniteBall) (v : C.D → Option V) (ι : B.D ↪ C.D)
    (Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
    (hv : Function.Surjective v)
    (s : Fin (Function.minimalPeriod B.map.faceSucc a) → C.D),
    (∀ x y : C.D, Relation.EqvGen
      (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y) ∧
    C.rootDart = ι B.rootDart ∧
    (∀ x, C.map.edgeInv (ι x) = ι (B.map.edgeInv x)) ∧
    (∀ x, v (ι x) = some (vert x)) ∧
    (∀ x, C.missing (ι x) ↔ B.missing x) ∧
    (∀ x, C.tail (ι x) ↔ B.tail x) ∧
    (∀ x, Q.pos (some x) = P.pos x) ∧
    (∀ x, Q'.pos (some x) = P'.pos x) ∧
    (∀ x, Q.arc (ι x) = P.arc x) ∧
    (∀ x, Q'.arc (ι x) = P'.arc x) ∧
    (∀ i, Function.minimalPeriod C.map.faceSucc (s i) = 3) ∧
    (∀ i j, C.map.faceSucc.SameCycle (s i) (s j) ↔ i = j) ∧
    (∀ x, ¬ B.map.faceSucc.SameCycle a x → ∀ z,
      C.map.faceSucc.SameCycle (ι x) z ↔
        ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y) ∧
    (∀ z, (∃ i, C.map.faceSucc.SameCycle (s i) z) ∨
      ∃ x, ¬ B.map.faceSucc.SameCycle a x ∧ z = ι x) ∧
    (∃ i,
      (¬ Bornology.IsBounded (C.plDartFace v Q hv (s i)).val) ∧
      (¬ Bornology.IsBounded (C.plDartFace v Q' hv (s i)).val))

### Exterior-star construction from DrawingUniqueness3:429 (full binders)

∀ {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)),
  ∃ (W : Type*) (C : D39FiniteBall) (v : C.D → W)
    (ι : B.D ↪ C.D) (σ : V ↪ W)
    (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hv : Function.Surjective v) (E : D39BallFaceCycleOrbit C)
    (I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C)),
    (∀ d e : C.D, Relation.EqvGen
      (fun x y => C.map.rot x = y ∨ C.map.edgeInv x = y) d e) ∧
    C.rootDart = ι B.rootDart ∧
    (∀ d : B.D, C.map.edgeInv (ι d) = ι (B.map.edgeInv d)) ∧
    (∀ d : B.D, v (ι d) = σ (vert d)) ∧
    (∀ d : B.D, C.missing (ι d) ↔ B.missing d) ∧
    (∀ d : B.D, C.tail (ι d) ↔ B.tail d) ∧
    (∀ x : V, Q.pos (σ x) = P.pos x) ∧
    (∀ x : V, Q'.pos (σ x) = P'.pos x) ∧
    (∀ d : B.D, Q.arc (ι d) = P.arc d) ∧
    (∀ d : B.D, Q'.arc (ι d) = P'.arc d) ∧
    (¬ Bornology.IsBounded (C.plOrbitFace v Q hv E).val) ∧
    (¬ Bornology.IsBounded (C.plOrbitFace v Q' hv E).val) ∧
    (∀ d : C.D, Function.minimalPeriod C.map.faceSucc d = 3 ∧
      Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] d))
        (Set.Iio 3)) ∧
    (∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
    (∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val)

### DU1 from DrawingUniqueness3:472 (full binders)

∀ {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)),
  ∃ (n : ℕ) (C : D39FiniteBall) (v : C.D → V ⊕ Fin n)
    (ι : B.D ↪ C.D)
    (Q Q' : PLDrawing C.D (V ⊕ Fin n) C.map.edgeInv C.map.rot v)
    (hv : Function.Surjective v) (E : D39BallFaceCycleOrbit C)
    (I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C)),
    (∀ d e : C.D, Relation.EqvGen
      (fun x y => C.map.rot x = y ∨ C.map.edgeInv x = y) d e) ∧
    C.rootDart = ι B.rootDart ∧
    (∀ d : B.D, C.map.edgeInv (ι d) = ι (B.map.edgeInv d)) ∧
    (∀ d : B.D, v (ι d) = Sum.inl (vert d)) ∧
    (∀ d : B.D, C.missing (ι d) ↔ B.missing d) ∧
    (∀ d : B.D, C.tail (ι d) ↔ B.tail d) ∧
    (∀ x : V, Q.pos (Sum.inl x) = P.pos x) ∧
    (∀ x : V, Q'.pos (Sum.inl x) = P'.pos x) ∧
    (∀ d : B.D, Q.arc (ι d) = P.arc d) ∧
    (∀ d : B.D, Q'.arc (ι d) = P'.arc d) ∧
    (¬ Bornology.IsBounded (C.plOrbitFace v Q hv E).val) ∧
    (¬ Bornology.IsBounded (C.plOrbitFace v Q' hv E).val) ∧
    (∀ O : D39BallFaceCycleOrbit C, ∃ d ∈ O.val,
      (O = E → Function.minimalPeriod C.map.faceSucc d = 4) ∧
      (O ≠ E → Function.minimalPeriod C.map.faceSucc d = 3) ∧
      Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] d))
        (Set.Iio (Function.minimalPeriod C.map.faceSucc d))) ∧
    (∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
    (∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) -/

end DirectedDistances.PlanarMap
end
