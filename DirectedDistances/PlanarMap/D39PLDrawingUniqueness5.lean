/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness4

/-! # Exterior indices in finite star refinements

Helpers toward Proposition 5.16. The two exterior indices are kept separate:
their equality is not a consequence of uniqueness within either drawing. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: if a star exhausts the replaced orbit,
the unbounded face has a unique star index. Unaffected orbits are excluded
using boundedness of the original nonexterior faces. -/
theorem drawing_existsUnique_unbounded_star_index
    {V W : Type*} [Finite V] (B C : D39FiniteBall)
    (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (hc : ∀ x y : C.D, Relation.EqvGen
      (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y)
    (ι : B.D ↪ C.D) (himage : P.image ⊆ Q.image)
    (harc : ∀ x, Q.arc (ι x) = P.arc x)
    (a : B.D) (hext : ¬ Bornology.IsBounded (B.plDartFace vert P hvert a).val)
    (k : ℕ) (s : Fin k → C.D)
    (hdistinct : ∀ i j, C.map.faceSucc.SameCycle (s i) (s j) ↔ i = j)
    (hexhaustive : ∀ z, (∃ i, C.map.faceSucc.SameCycle (s i) z) ∨
      ∃ x, ¬ B.map.faceSucc.SameCycle a x ∧ z = ι x) :
    ∃! i : Fin k, ¬ Bornology.IsBounded (C.plDartFace v Q hv (s i)).val := by
  let : Finite W := Finite.of_surjective v hv
  obtain ⟨U, hU, huniq⟩ := Q.existsUnique_not_isBounded_face
  obtain ⟨z, hz⟩ := C.plDartFace_surjective v Q hv U
  have hindex : ∃ i, C.plDartFace v Q hv (s i) = U := by
    rcases hexhaustive z with ⟨i, hi⟩ | ⟨x, hx, rfl⟩
    · exact ⟨i, (C.plDartFace_eq_of_sameCycle v Q hv _ _ hi).trans hz⟩
    · have hne : B.plDartFace vert P hvert x ≠ B.plDartFace vert P hvert a := by
        intro heq
        exact hx (B.plDartFace_sameCycle_of_eq vert P hvert hconn x a heq).symm
      have hb := P.isBounded_face_of_ne_unbounded _ hext _ hne
      have hsub := B.drawing_inherited_dart_face_subset C vert v P Q hvert hv
        himage x (ι x) (harc x)
      exact (hU (hz ▸ hb.subset hsub)).elim
  obtain ⟨i, hi⟩ := hindex
  refine ⟨i, ?_, ?_⟩
  · exact (congrArg (fun F : Q.Face => ¬ Bornology.IsBounded F.val) hi).mpr hU
  · intro j hj
    apply (hdistinct j i).mp
    exact C.plDartFace_sameCycle_of_eq v Q hv hc _ _ ((huniq _ hj).trans hi.symm)

/-- Helper toward Proposition 5.16: a star of the common exterior admits
one uniquely unbounded triangle index in each drawing. These indices are
not identified. Every other triangle is bounded in its respective drawing;
all of the original dart, vertex, and unaffected-orbit data persist. -/
theorem exists_star_drawings_with_unique_exterior_indices
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a : B.D)
    (hext : (¬ Bornology.IsBounded (B.plDartFace vert P hvert a).val) ∧
      (¬ Bornology.IsBounded (B.plDartFace vert P' hvert a).val)) :
    ∃ (C : D39FiniteBall) (v : C.D → Option V) (ι : B.D ↪ C.D)
      (Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
      (hv : Function.Surjective v)
      (s : Fin (Function.minimalPeriod B.map.faceSucc a) → C.D)
      (i i' : Fin (Function.minimalPeriod B.map.faceSucc a)),
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
      (∀ j, Function.minimalPeriod C.map.faceSucc (s j) = 3) ∧
      (∀ j, Set.InjOn
        (fun n : ℕ => v ((C.map.faceSucc : C.D → C.D)^[n] (s j))) (Set.Iio 3)) ∧
      (∀ j l, C.map.faceSucc.SameCycle (s j) (s l) ↔ j = l) ∧
      (∀ x, ¬ B.map.faceSucc.SameCycle a x → ∀ z,
        C.map.faceSucc.SameCycle (ι x) z ↔
          ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y) ∧
      (∀ z, (∃ j, C.map.faceSucc.SameCycle (s j) z) ∨
        ∃ x, ¬ B.map.faceSucc.SameCycle a x ∧ z = ι x) ∧
      (∀ j, (¬ Bornology.IsBounded (C.plDartFace v Q hv (s j)).val) ↔ j = i) ∧
      (∀ j, (¬ Bornology.IsBounded (C.plDartFace v Q' hv (s j)).val) ↔ j = i') := by
  classical
  obtain ⟨C, v, ι, Q, Q', s, hv, hc, _, hr, hf, hvertex, hm, ht, _,
    hp, hp', he, he', himage, himage', htri, hinj, _, hdist, hu, hex⟩ :=
    B.exists_star_drawings vert P P' hvert hconn a
      (Function.minimalPeriod B.map.faceSucc a)
      (B.drawing_face_period_ge_two vert P a) rfl
  obtain ⟨i, hi, huniq⟩ := B.drawing_existsUnique_unbounded_star_index C vert v
    P Q hvert hv hconn hc ι himage he a hext.1 _ s hdist hex
  obtain ⟨i', hi', huniq'⟩ := B.drawing_existsUnique_unbounded_star_index C vert v
    P' Q' hvert hv hconn hc ι himage' he' a hext.2 _ s hdist hex
  refine ⟨C, v, ι, Q, Q', hv, s, i, i', hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', htri, hinj, hdist, hu, hex, ?_, ?_⟩
  · intro j
    exact ⟨huniq j, fun h => h ▸ hi⟩
  · intro j
    exact ⟨huniq' j, fun h => h ▸ hi'⟩

/-- Helper toward Proposition 5.16: a connected finite drawing has exactly
one unbounded face orbit, without choosing a geometric face independently
of its combinatorial orbit. -/
theorem drawing_existsUnique_unbounded_orbit
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y) :
    ∃! O : D39BallFaceCycleOrbit B,
      ¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O).val := by
  let : Finite V := Finite.of_surjective vert hvert
  obtain ⟨U, hU, huniq⟩ := P.existsUnique_not_isBounded_face
  obtain ⟨O, hO⟩ := B.plOrbitFace_surjective vert P hvert U
  refine ⟨O, ?_, ?_⟩
  · exact (congrArg (fun F : P.Face => ¬ Bornology.IsBounded F.val) hO).mpr hU
  · intro S hS
    exact B.plOrbitFace_injective vert P hvert hconn ((huniq _ hS).trans hO.symm)

/-- Helper toward Proposition 5.16: all face orbits can be triangulated on
the carrier `V ⊕ Fin n`, with one common closed-face index and uniquely
identified exterior orbits in the two drawings separately. Both exterior
orbits belong to the same original exterior's child set. Their equality
and the insertion of a quadrilateral exterior remain separate obligations. -/
theorem exists_sum_fin_triangulated_drawings_with_separate_exteriors
    {V : Type u} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)) :
    ∃ (n : ℕ) (C : D39FiniteBall) (w : C.D → V ⊕ Fin n)
      (ι : B.D ↪ C.D)
      (R R' : PLDrawing C.D (V ⊕ Fin n) C.map.edgeInv C.map.rot w)
      (hw : Function.Surjective w) (E E' : D39BallFaceCycleOrbit C)
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
      (∀ d, Function.minimalPeriod C.map.faceSucc d = 3 ∧
        Set.InjOn (fun k : ℕ => w ((C.map.faceSucc : C.D → C.D)^[k] d))
          (Set.Iio 3)) ∧
      (∀ S, (¬ Bornology.IsBounded (C.plOrbitFace w R hw S).val) ↔ S = E) ∧
      (∀ S, (¬ Bornology.IsBounded (C.plOrbitFace w R' hw S).val) ↔ S = E') ∧
      E ∈ I O_ext ∧ E' ∈ I O_ext ∧
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace w R hw S).val ⊆ (B.plOrbitFace vert P hvert O).val) ∧
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace w R' hw S).val ⊆ (B.plOrbitFace vert P' hvert O).val) ∧
      (∀ O, closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace w R hw S).val) ∧
      (∀ O, closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace w R' hw S).val) := by
  classical
  obtain ⟨W, C, v, ι, σ, Q, Q', hv, hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', _, hx, hparent⟩ :=
    B.exists_iterated_star_drawings_with_common_parents vert P P' hvert hconn Finset.univ
  have hperiod (d : C.D) : Function.minimalPeriod C.map.faceSucc d = 3 := by
    rcases hx d with hd | ⟨x, havoid, _⟩
    · exact hd
    · exact (havoid x (Finset.mem_univ x) Equiv.Perm.SameCycle.rfl).elim
  have himage : P.image ⊆ Q.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hp x⟩
    · exact Or.inr ⟨ι d, he d ▸ hd⟩
  have himage' : P'.image ⊆ Q'.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hp' x⟩
    · exact Or.inr ⟨ι d, he' d ▸ hd⟩
  obtain ⟨I, hI, hI', hcover, hcover'⟩ :=
    B.drawing_exists_common_closed_face_index C vert v P P' Q Q' hvert hv hconn
      himage himage' hparent
  obtain ⟨E, hE, hEuniq⟩ := C.drawing_existsUnique_unbounded_orbit v Q hv hc
  obtain ⟨E', hE', hEuniq'⟩ := C.drawing_existsUnique_unbounded_orbit v Q' hv hc
  have hmem : E ∈ I O_ext := (hI O_ext E).mpr
    (B.drawing_unbounded_face_subset_external C vert v P Q himage _ hext.1 _ hE)
  have hmem' : E' ∈ I O_ext := (hI' O_ext E').mpr
    (B.drawing_unbounded_face_subset_external C vert v P' Q' himage' _ hext.2 _ hE')
  obtain ⟨n, e, R, R', hw, heσ, hpos, hpos', harc, harc', _, _, hfaces, hfaces', hinj⟩ :=
    C.drawing_exists_sum_fin_reindex v Q Q' hv σ
  refine ⟨n, C, e ∘ v, ι, R, R', hw, E, E', I, hc, hr, hf, ?_, hm, ht,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem, hmem', ?_, ?_, ?_, ?_⟩
  · intro x
    change e (v (ι x)) = Sum.inl (vert x)
    rw [hvertex, heσ]
  · intro x
    exact (hpos x).trans (hp x)
  · intro x
    exact (hpos' x).trans (hp' x)
  · intro x
    exact (harc (ι x)).trans (he x)
  · intro x
    exact (harc' (ι x)).trans (he' x)
  · intro d
    exact ⟨hperiod d, (hinj _ _).mpr (C.drawing_triangle_initialVertices v Q d (hperiod d))⟩
  · intro S
    rw [hfaces S]
    exact ⟨hEuniq S, fun h => h ▸ hE⟩
  · intro S
    rw [hfaces' S]
    exact ⟨hEuniq' S, fun h => h ▸ hE'⟩
  · intro O S
    rw [hfaces S]
    exact hI O S
  · intro O S
    rw [hfaces' S]
    exact hI' O S
  · intro O
    simp_rw [hfaces]
    exact hcover O
  · intro O
    simp_rw [hfaces']
    exact hcover' O

end D39FiniteBall

/-! ## Attempts and remaining statements

The following three approaches were checked against their actual interfaces.

1. Unique unbounded orbits plus common parents. The construction above now
   gives unique indices `i` and `i'`, and a common index `I` containing both
   exterior children. Uniqueness in `Q` compares only two unbounded faces of
   `Q`; it cannot compare a face unbounded in `Q'` without first proving that
   face unbounded in `Q`. No singleton-child property is supplied by `hI`.
2. Bounded ears at each chord. `exists_chord_arc_in_face` supplies a simple
   chord, its two corner inequalities, and containment of its interior in the
   old face. `exists_uniform_edge_strip_separation` separates trimmed arcs,
   but does not construct a chord in a specified strip. A chord confined to
   the old exterior may put infinity on either new orbit. A bounded sector
   at its endpoint does not bound the face it borders. The missing step is a
   controlled chord construction and a proof that its cut-off triangle is
   bounded; the present iteration does not establish either assertion.
3. Transport by image or exterior homeomorphisms. `exists_plImageHomeomorph`
   maps the drawing images, with no map on their complements. The plane
   extension for simple full-period boundaries explicitly requires the same
   exterior orbit in both drawings, precisely the missing matching.
   `Polyline.exists_outer_chart` requires a cyclically simple boundary,
   whereas the original exterior walk can repeat vertices. Its arbitrary
   homeomorphism also has no PL-preservation clause for transported spokes.
   Thus applying that chart before the star is unavailable, and applying the
   plane extension after the star is circular.

These obstructions do not assert nonexistence of the constructions. The
statements below remain comments only, with their source premises intact.
No matching, frame construction, or drawing uniqueness is assumed above.

### Step 1: matching exterior child in one star (Uniqueness4:402)

The proved `exists_star_drawings_with_unique_exterior_indices` retains all
these clauses, adds full-period vertex injectivity, and replaces the final
joint index by two separately unique indices. The missing joint witness is:

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

### Step 2: triangular common exterior (Uniqueness4:438)

The proved `exists_sum_fin_triangulated_drawings_with_separate_exteriors`
provides all the preservation, triangulation, and common-index clauses,
including the specified carrier. The remaining requirement is one exterior
orbit unbounded simultaneously. A matched single star must also be threaded
through the common-index construction; that threading is not claimed here.

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

### Step 3: quadrilateral exterior and DU1 (Uniqueness4:476)

After matching, DU1 additionally requires inserting the frame as darts,
proving its four-period vertex-simple exterior and triangulating the annular
region, while preserving all old arcs and the common decomposition index.
The enclosing-square geometry alone does not perform those insertions.
The three frame routes checked were: attach the existing far pendant to a
preselected square (a first-contact prefix and its corner slot remain needed);
choose the square after the pendant (its tip is then strictly inside, leaving
the continuation and frame insertions open); transport via the square cone
(the map need not preserve PL arcs and does not insert combinatorial darts).

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
