/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLStarChordBoundedSide

/-! # Exterior children of a star chord

Helpers toward Proposition 5.16, using the finite drawing constructions attached
belong to the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: inserting a drawable chord preserves
connectedness of the dart moves. Rotation at the two old vertices connects
the new darts to old darts, and every original dart move lifts. -/
theorem insertChord_drawing_connected
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a b : B.D) (hab : a ≠ b)
    (Q : PLDrawing (B.insertChord a b hab).D V
      (B.insertChord a b hab).map.edgeInv (B.insertChord a b hab).map.rot
      (B.chordVert vert a b)) :
    ∀ x y : (B.insertChord a b hab).D, Relation.EqvGen
      (fun z w => (B.insertChord a b hab).map.rot z = w ∨
        (B.insertChord a b hab).map.edgeInv z = w) x y := by
  let C := B.insertChord a b hab
  let v := B.chordVert vert a b
  let R := fun z w : C.D => C.map.rot z = w ∨ C.map.edgeInv z = w
  have hvertex {x y : C.D} (he : v x = v y) : Relation.EqvGen R x y :=
    CombinatorialMap.eqvGen_of_rotation_sameCycle C.map.rot R (fun _ => Or.inl rfl)
      (Q.rot_sameCycle_of_vert_eq x y he)
  have hlift {x y : B.D} (he : Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y) :
      Relation.EqvGen R (.inl x) (.inl y) := by
    induction he with
    | rel x y he =>
        rcases he with he | he
        · apply hvertex
          change vert x = vert y
          rw [← he, P.vert_rotation]
        · exact Relation.EqvGen.rel _ _ (Or.inr (congrArg Sum.inl he))
    | refl => exact Relation.EqvGen.refl _
    | symm x y he ih => exact ih.symm _ _
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans _ _ _ ihyz
  have hpath (z : C.D) : Relation.EqvGen R z (.inl a) := by
    cases z with
    | inl x => exact hlift (hconn x a)
    | inr t =>
        cases t with
        | false =>
            exact (hvertex (x := .inr false) (y := .inl b) rfl).trans _ _ _
              (hlift (hconn b a))
        | true => exact hvertex rfl
  intro x y
  exact (hpath x).trans _ _ _ ((hpath y).symm _ _)

/-- Helper toward Proposition 5.16: after cutting a two-edge ear from an
exterior face, exactly one of the triangle and residual child is unbounded.
This does not select which child it is. The original source exterior premise
is used only to exclude unchanged old faces. -/
theorem existsUnique_unbounded_chord_child
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a b : B.D) (hvab : vert a ≠ vert b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hext : ¬ Bornology.IsBounded (B.plDartFace vert P hvert b).val)
    (Q : PLDrawing (B.insertChord a b (B.chord_corners_ne vert a b hvab)).D V
      (B.insertChord a b (B.chord_corners_ne vert a b hvab)).map.edgeInv
      (B.insertChord a b (B.chord_corners_ne vert a b hvab)).map.rot
      (B.chordVert vert a b))
    (hpos : ∀ x, Q.pos x = P.pos x)
    (harc : ∀ d : B.D, Q.arc (.inl d) = P.arc d) :
    let C := B.insertChord a b (B.chord_corners_ne vert a b hvab)
    let hv : Function.Surjective (B.chordVert vert a b) := by
      intro x
      obtain ⟨d, rfl⟩ := hvert x
      exact ⟨.inl d, rfl⟩
    ∃! t : Bool, ¬ Bornology.IsBounded
      (C.plDartFace (B.chordVert vert a b) Q hv (.inr t)).val := by
  classical
  dsimp only
  let C := B.insertChord a b (B.chord_corners_ne vert a b hvab)
  let v := B.chordVert vert a b
  have hv : Function.Surjective v := by
    intro x
    obtain ⟨d, rfl⟩ := hvert x
    exact ⟨.inl d, rfl⟩
  let : Finite V := Finite.of_surjective vert hvert
  have hc := B.insertChord_drawing_connected vert P hconn a b
    (B.chord_corners_ne vert a b hvab) Q
  have himage : P.image ⊆ Q.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨x, hpos x⟩
    · exact Or.inr ⟨.inl d, harc d ▸ hd⟩
  obtain ⟨_, hdistinct, _, _, hexhaust⟩ :=
    B.star_chord_orbit_invariant a b (B.chord_corners_ne vert a b hvab) hi hwalk
  obtain ⟨U, hU, huniq⟩ := Q.existsUnique_not_isBounded_face
  obtain ⟨z, hz⟩ := C.plDartFace_surjective v Q hv U
  have hchild : ∃ t : Bool, C.plDartFace v Q hv (.inr t) = U := by
    rcases hexhaust z with htri | hres | ⟨x, hx, rfl⟩
    · exact ⟨true, (C.plDartFace_eq_of_sameCycle v Q hv _ _ htri).trans hz⟩
    · exact ⟨false, (C.plDartFace_eq_of_sameCycle v Q hv _ _ hres).trans hz⟩
    · have hne : B.plDartFace vert P hvert x ≠ B.plDartFace vert P hvert b := by
        intro heq
        exact hx (B.plDartFace_sameCycle_of_eq vert P hvert hconn x b heq).symm
      have hb := P.isBounded_face_of_ne_unbounded _ hext _ hne
      have hsub := B.drawing_inherited_dart_face_subset C vert v P Q hvert hv
        himage x (.inl x) (harc x)
      exact (hU (hz ▸ hb.subset hsub)).elim
  obtain ⟨t, ht⟩ := hchild
  refine ⟨t, ?_, ?_⟩
  · exact (congrArg (fun F : Q.Face => ¬ Bornology.IsBounded F.val) ht).mpr hU
  · intro s hs
    have hsame := C.plDartFace_sameCycle_of_eq v Q hv hc (.inr s) (.inr t)
      ((huniq _ hs).trans ht.symm)
    cases s <;> cases t
    · rfl
    · exact (hdistinct hsame.symm).elim
    · exact (hdistinct hsame).elim
    · rfl

/-- Helper toward Proposition 5.16: for a chord cutting an exterior parent,
the residual child is unbounded exactly when the triangular child is bounded.
Boundedness is a conclusion of this equivalence, not an added premise. -/
theorem chord_residual_unbounded_iff_triangle_bounded
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a b : B.D) (hvab : vert a ≠ vert b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hext : ¬ Bornology.IsBounded (B.plDartFace vert P hvert b).val)
    (Q : PLDrawing (B.insertChord a b (B.chord_corners_ne vert a b hvab)).D V
      (B.insertChord a b (B.chord_corners_ne vert a b hvab)).map.edgeInv
      (B.insertChord a b (B.chord_corners_ne vert a b hvab)).map.rot
      (B.chordVert vert a b))
    (hpos : ∀ x, Q.pos x = P.pos x)
    (harc : ∀ d : B.D, Q.arc (.inl d) = P.arc d) :
    let C := B.insertChord a b (B.chord_corners_ne vert a b hvab)
    let hv : Function.Surjective (B.chordVert vert a b) := by
      intro x
      obtain ⟨d, rfl⟩ := hvert x
      exact ⟨.inl d, rfl⟩
    (¬ Bornology.IsBounded
      (C.plDartFace (B.chordVert vert a b) Q hv (.inr false)).val) ↔
      Bornology.IsBounded
        (C.plDartFace (B.chordVert vert a b) Q hv (.inr true)).val := by
  classical
  obtain ⟨t, ht, huniq⟩ := B.existsUnique_unbounded_chord_child
    vert P hvert hconn a b hvab hi hwalk hext Q hpos harc
  dsimp only
  constructor
  · intro hfalse
    by_contra htrue
    have hs := huniq false hfalse
    have ht' := huniq true htrue
    exact Bool.noConfusion (ht'.trans hs.symm)
  · intro htrue
    cases t with
    | false => exact ht
    | true => exact (ht htrue).elim

end D39FiniteBall
end DirectedDistances.PlanarMap

end

/- Open target (1): bounded-side selection, with the original full binders.
This is a comment, not a declaration or an additional premise.
Names below are read in DirectedDistances.PlanarMap.D39FiniteBall.

∀ {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (a b : B.D) (hvab : vert a ≠ vert b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hcentre : vert (B.map.faceSucc b) ≠ vert a),
  let C := B.insertChord a b (B.chord_corners_ne vert a b hvab)
  ∃ (Q Q' : PLDrawing C.D V C.map.edgeInv C.map.rot
      (B.chordVert vert a b)),
    (∀ v, Q.pos v = P.pos v) ∧ (∀ v, Q'.pos v = P'.pos v) ∧
    (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
    (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) ∧
    Function.minimalPeriod C.map.faceSucc (.inr true) = 3 ∧
    Bornology.IsBounded
      (C.plDartFace (B.chordVert vert a b) Q
        (by
          intro v
          obtain ⟨d, rfl⟩ := hvert v
          exact ⟨.inl d, rfl⟩)
        (.inr true)).val ∧
    Bornology.IsBounded
      (C.plDartFace (B.chordVert vert a b) Q'
        (by
          intro v
          obtain ⟨d, rfl⟩ := hvert v
          exact ⟨.inl d, rfl⟩)
        (.inr true)).val

Three routes checked for target (1):
1. Polygonal separation and exact boundary tracing.
   `Polyline.exists_polygonal_separation` supplies the bounded inside and
   unbounded outside. `plOrbitFace_eq_inside_or_outside_of_cyclicSimple_boundary`
   even identifies the entire face with one side in the connected case.
   Neither statement selects the inside; a simple closed polygon is also
   the frontier of its unbounded complementary component.
2. Signed winding of the oriented face walk.
   `Polyline.angleSum_edge_jump_cyclic_signed` supplies the signed unit jump.
   `faceWalkPolyline_fullPeriod_angleSum_eq_one_of_isBounded` fixes the sign
   only after boundedness is known. Applying that theorem here would assume
   the conclusion. The corner successor order alone has not been shown to
   select an inside point with nonzero winding for the chosen chord.
   The bound `Polyline.closedConcat_hasWinding_bounds32` controls absolute
   winding but likewise does not distinguish zero from one on this face.
3. Construct a chord close to the two-edge boundary path.
   `exists_chord_arc_in_face` gives a simple chord, interior avoidance, and
   the two strict corner inequalities, but uses an arbitrary simple connector
   in the face. `exists_uniform_edge_strip_separation` separates trimmed
   old arcs; it does not construct an oriented collar connector through all
   their bends and the intervening vertex sector. Such a connector, together
   An arbitrary existing chord extension cannot simply be declared bounded.

Open target (2): a common residual exterior child, with full binders.

∀ {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a b : B.D) (hvab : vert a ≠ vert b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hcentre : vert (B.map.faceSucc b) ≠ vert a)
    (hext : (¬ Bornology.IsBounded
      (B.plDartFace vert P hvert b).val) ∧
      (¬ Bornology.IsBounded (B.plDartFace vert P' hvert b).val)),
  let C := B.insertChord a b (B.chord_corners_ne vert a b hvab)
  ∃ (Q Q' : PLDrawing C.D V C.map.edgeInv C.map.rot
      (B.chordVert vert a b)),
    (∀ v, Q.pos v = P.pos v) ∧ (∀ v, Q'.pos v = P'.pos v) ∧
    (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
    (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) ∧
    Function.minimalPeriod C.map.faceSucc (.inr true) = 3 ∧
    (¬ Bornology.IsBounded
      (C.plDartFace (B.chordVert vert a b) Q
        (by
          intro v
          obtain ⟨d, rfl⟩ := hvert v
          exact ⟨.inl d, rfl⟩)
        (.inr false)).val) ∧
    (¬ Bornology.IsBounded
      (C.plDartFace (B.chordVert vert a b) Q'
        (by
          intro v
          obtain ⟨d, rfl⟩ := hvert v
          exact ⟨.inl d, rfl⟩)
        (.inr false)).val)

Three routes checked for target (2):
1. Uniqueness of the unbounded geometric face plus the exhaustive chord
   orbit split. This succeeds above in proving a unique exterior Bool child
   in each drawing, but does not identify it as `false`.
2. Inherit face containment from preserved old dart arcs. This excludes
   every unaffected old orbit, as used in the proof above; neither of the
   two split children is an unaffected orbit, so this does not select one.
3. Exclude the triangle and then use uniqueness. The equivalence
   `chord_residual_unbounded_iff_triangle_bounded` proves this entire
   reduction with no boundedness premise. Applying it to Q and Q' would
   finish target (2) once target (1) constructs bounded triangles in both.
   That geometric construction remains the obstruction; no common exterior
   child or target-equivalent assumption has been introduced.

The optional general DU1 Step 1 construction was not attempted after this
obstruction. No numbered paper result is claimed complete by this file. -/
