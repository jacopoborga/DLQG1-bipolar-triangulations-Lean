/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness5

/-! # Preserving the exterior during bounded-face triangulation

to the sole coordinator. The exterior is retained, rather than subdivided;
no equality between separately chosen exterior children is assumed. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: full-period initial-vertex simplicity
is precisely injectivity of the vertex map on the entire dart orbit. -/
theorem drawing_initialVertices_injOn_iff
    {α V : Type*} [Fintype α] (f : Equiv.Perm α) (vert : α → V) (x : α) :
    Set.InjOn (fun n : ℕ => vert ((f : α → α)^[n] x))
      (Set.Iio (Function.minimalPeriod f x)) ↔
      Set.InjOn vert {y | f.SameCycle x y} := by
  have hrep (y : α) (hy : f.SameCycle x y) :
      ∃ n < Function.minimalPeriod f x, (f : α → α)^[n] x = y := by
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    have hp : 0 < Function.minimalPeriod f x :=
      Function.minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts x)
    refine ⟨n % Function.minimalPeriod f x, Nat.mod_lt _ hp, ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq]
    exact hn
  constructor
  · intro h y hy z hz heq
    obtain ⟨i, hi, rfl⟩ := hrep y hy
    obtain ⟨j, hj, rfl⟩ := hrep z hz
    exact congrArg (fun n => (f : α → α)^[n] x) (h hi hj heq)
  · intro h i hi j hj heq
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp
    exact h (show f.SameCycle x ((f ^ i) x) from Equiv.Perm.SameCycle.rfl.pow_right)
      (show f.SameCycle x ((f ^ j) x) from Equiv.Perm.SameCycle.rfl.pow_right) heq

/-- Helper toward Proposition 5.16: an exact orbit embedding preserves
full-period initial-vertex simplicity, without a successor-commutation
assumption. The common vertex embedding is injective. -/
theorem drawing_initialVertices_injOn_orbit_embedding_iff
    {α β V W : Type*} [Fintype α] [Fintype β]
    (f : Equiv.Perm α) (g : Equiv.Perm β) (vert : α → V) (v : β → W)
    (ι : α ↪ β) (σ : V ↪ W) (hvertex : ∀ y, v (ι y) = σ (vert y))
    (x : α) (z : β) (hz : g.SameCycle (ι x) z)
    (horbit : ∀ t, g.SameCycle (ι x) t ↔
      ∃ y, f.SameCycle x y ∧ t = ι y) :
    Set.InjOn (fun n : ℕ => v ((g : β → β)^[n] z))
      (Set.Iio (Function.minimalPeriod g z)) ↔
      Set.InjOn (fun n : ℕ => vert ((f : α → α)^[n] x))
        (Set.Iio (Function.minimalPeriod f x)) := by
  rw [drawing_initialVertices_injOn_iff, drawing_initialVertices_injOn_iff]
  constructor
  · intro h y hy t ht heq
    apply ι.injective
    apply h
    · exact hz.symm.trans ((horbit _).mpr ⟨y, hy, rfl⟩)
    · exact hz.symm.trans ((horbit _).mpr ⟨t, ht, rfl⟩)
    · rw [hvertex, hvertex, heq]
  · intro h y hy t ht heq
    obtain ⟨a, ha, rfl⟩ := (horbit y).mp (hz.trans hy)
    obtain ⟨b, hb, rfl⟩ := (horbit t).mp (hz.trans ht)
    rw [hvertex, hvertex] at heq
    exact congrArg ι (h ha hb (σ.injective heq))

/-- Helper toward Proposition 5.16: an unchanged original orbit has exactly
one child orbit. The geometric equality needed here follows from the exact
unaffected-orbit description and preservation of the original arcs. -/
theorem drawing_unchanged_orbit_child_iff
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hc : ∀ x y : C.D, Relation.EqvGen
      (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y)
    (ι : B.D ↪ C.D) (himage : P.image ⊆ Q.image)
    (harc : ∀ d, Q.arc (ι d) = P.arc d) (a : B.D)
    (horbit : ∀ z, C.map.faceSucc.SameCycle (ι a) z ↔
      ∃ y, B.map.faceSucc.SameCycle a y ∧ z = ι y)
    (E : D39BallFaceCycleOrbit C) (hE : ι a ∈ E.val)
    (S : D39BallFaceCycleOrbit C) :
    (C.plOrbitFace v Q hv S).val ⊆ (B.plDartFace vert P hvert a).val ↔ S = E := by
  have hface : (C.plOrbitFace v Q hv E).val =
      (B.plDartFace vert P hvert a).val := by
    rw [C.plOrbitFace_eq_plDartFace_of_mem v Q hv E (ι a) hE]
    exact B.drawing_unchanged_orbit_face_eq C vert v P Q hvert hv hc ι
      himage harc a horbit
  constructor
  · intro hsub
    obtain ⟨z, hz, hS⟩ := (C.plOrbitFace v Q hv S).property
    have hzS : z ∈ (C.plOrbitFace v Q hv S).val := hS ▸ mem_connectedComponentIn hz
    have hzE : z ∈ (C.plOrbitFace v Q hv E).val := hface.symm ▸ hsub hzS
    exact C.plOrbitFace_injective v Q hv hc (Q.faces_eq_of_mem hzS hzE)
  · rintro rfl
    exact hface ▸ Set.Subset.rfl






theorem exists_sum_fin_triangulated_drawings_with_preserved_exterior
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
      (hw : Function.Surjective w) (E : D39BallFaceCycleOrbit C)
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
      E.val = ι '' O_ext.val ∧
      (C.plOrbitFace w R hw E).val = (B.plOrbitFace vert P hvert O_ext).val ∧
      (C.plOrbitFace w R' hw E).val = (B.plOrbitFace vert P' hvert O_ext).val ∧
      (∀ S, (¬ Bornology.IsBounded (C.plOrbitFace w R hw S).val) ↔ S = E) ∧
      (∀ S, (¬ Bornology.IsBounded (C.plOrbitFace w R' hw S).val) ↔ S = E) ∧
      (∀ d, d ∉ E.val → Function.minimalPeriod C.map.faceSucc d = 3 ∧
        Set.InjOn (fun k : ℕ => w ((C.map.faceSucc : C.D → C.D)^[k] d))
          (Set.Iio 3)) ∧
      (∀ d ∈ E.val, Function.minimalPeriod C.map.faceSucc d =
        Function.minimalPeriod B.map.faceSucc O_ext.property.choose) ∧
      (∀ d ∈ E.val,
        Set.InjOn (fun k : ℕ => w ((C.map.faceSucc : C.D → C.D)^[k] d))
          (Set.Iio (Function.minimalPeriod C.map.faceSucc d)) ↔
        Set.InjOn (fun k : ℕ => vert
          ((B.map.faceSucc : B.D → B.D)^[k] O_ext.property.choose))
          (Set.Iio (Function.minimalPeriod B.map.faceSucc O_ext.property.choose))) ∧
      I O_ext = {E} ∧
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace w R hw S).val ⊆ (B.plOrbitFace vert P hvert O).val) ∧
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace w R' hw S).val ⊆ (B.plOrbitFace vert P' hvert O).val) ∧
      (∀ O, closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace w R hw S).val) ∧
      (∀ O, closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace w R' hw S).val) := by
  classical
  let a := O_ext.property.choose
  have ha_set : O_ext.val = {x | B.map.faceSucc.SameCycle a x} :=
    O_ext.property.choose_spec
  have ha : a ∈ O_ext.val := ha_set ▸ Equiv.Perm.SameCycle.rfl
  let T := Finset.univ.filter (fun d => ¬ B.map.faceSucc.SameCycle a d)
  have havoid (x : B.D) :
      (∀ b ∈ T, ¬ B.map.faceSucc.SameCycle b x) ↔ B.map.faceSucc.SameCycle a x := by
    constructor
    · intro h
      by_contra hn
      exact h x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hn⟩)
        Equiv.Perm.SameCycle.rfl
    · intro h b hb hh
      exact (Finset.mem_filter.mp hb).2 (h.trans hh.symm)
  obtain ⟨W, C, v, ι, σ, Q, Q', hv, hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', hu, hx, hparent⟩ :=
    B.exists_iterated_star_drawings_with_common_parents vert P P' hvert hconn T
  have horbit := hu a ((havoid a).mpr Equiv.Perm.SameCycle.rfl)
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
  let E : D39BallFaceCycleOrbit C :=
    ⟨{z | C.map.faceSucc.SameCycle (ι a) z}, ι a, rfl⟩
  have hE : ι a ∈ E.val := Equiv.Perm.SameCycle.rfl
  have hface : (C.plOrbitFace v Q hv E).val =
      (B.plOrbitFace vert P hvert O_ext).val := by
    rw [C.plOrbitFace_eq_plDartFace_of_mem v Q hv E (ι a) hE,
      B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O_ext a ha]
    exact B.drawing_unchanged_orbit_face_eq C vert v P Q hvert hv hc ι
      himage he a horbit
  have hface' : (C.plOrbitFace v Q' hv E).val =
      (B.plOrbitFace vert P' hvert O_ext).val := by
    rw [C.plOrbitFace_eq_plDartFace_of_mem v Q' hv E (ι a) hE,
      B.plOrbitFace_eq_plDartFace_of_mem vert P' hvert O_ext a ha]
    exact B.drawing_unchanged_orbit_face_eq C vert v P' Q' hvert hv hc ι
      himage' he' a horbit
  have hsingleton : I O_ext = {E} := by
    ext S
    rw [hI, Set.mem_singleton_iff,
      B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O_ext a ha]
    exact B.drawing_unchanged_orbit_child_iff C vert v P Q hvert hv hc ι
      himage he a horbit E hE S
  obtain ⟨n, e, R, R', hw, heσ, hpos, hpos', harc, harc', _, _,
    hfaces, hfaces', hinj⟩ := C.drawing_exists_sum_fin_reindex v Q Q' hv σ
  have hRface : (C.plOrbitFace (e ∘ v) R hw E).val =
      (B.plOrbitFace vert P hvert O_ext).val := (hfaces E).trans hface
  have hRface' : (C.plOrbitFace (e ∘ v) R' hw E).val =
      (B.plOrbitFace vert P' hvert O_ext).val := (hfaces' E).trans hface'
  refine ⟨n, C, e ∘ v, ι, R, R', hw, E, I, hc, hr, hf, ?_, hm, ht,
    ?_, ?_, ?_, ?_, ?_, hRface, hRface', ?_, ?_, ?_, ?_, ?_, hsingleton,
    ?_, ?_, ?_, ?_⟩
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
  · ext z
    change C.map.faceSucc.SameCycle (ι a) z ↔ z ∈ ι '' O_ext.val
    rw [horbit, ha_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  · intro S
    constructor
    · intro hS
      apply C.plOrbitFace_injective (e ∘ v) R hw hc
      by_contra hne
      exact hS (R.isBounded_face_of_ne_unbounded _ (hRface ▸ hext.1) _ hne)
    · rintro rfl
      exact hRface ▸ hext.1
  · intro S
    constructor
    · intro hS
      apply C.plOrbitFace_injective (e ∘ v) R' hw hc
      by_contra hne
      exact hS (R'.isBounded_face_of_ne_unbounded _ (hRface' ▸ hext.2) _ hne)
    · rintro rfl
      exact hRface' ▸ hext.2
  · intro d hd
    have hperiod : Function.minimalPeriod C.map.faceSucc d = 3 := by
      rcases hx d with hg | ⟨x, havoidx, rfl⟩
      · exact hg
      · exact (hd ((horbit _).mpr ⟨x, (havoid x).mp havoidx, rfl⟩)).elim
    exact ⟨hperiod, (hinj _ _).mpr
      (C.drawing_triangle_initialVertices v Q d hperiod)⟩
  · intro d hd
    exact (drawing_period_of_sameCycle C.map.faceSucc hd).trans
      (drawing_period_of_orbit_embedding B.map.faceSucc C.map.faceSucc ι a horbit)
  · intro d hd
    rw [hinj]
    exact drawing_initialVertices_injOn_orbit_embedding_iff B.map.faceSucc
      C.map.faceSucc vert v ι σ hvertex a d hd horbit
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

/-! ## Attempts and exact remaining obligations

These are open construction statements, not hypotheses of any theorem above.

Three approaches to the single-star matching were examined:

1. Common parents and uniqueness. DU3's containment iff gives the same set
   of child indices in both drawings. DU5's unique-unbounded-index theorem
   gives a unique element for a drawing-dependent predicate on that set.
   It does not make that predicate independent of the drawing. For example,
   on the common set `{0, 1} : Set (Fin 2)`, the predicates `j = 0` and
   `j = 1` each have exactly one solution, with different solutions. This
   refutes the proposed set-theoretic inference, not the existential
   geometric construction in Step 1 below. The singleton theorem above
   applies to an unchanged orbit, not to the several triangles of a star.
2. Bounded ears. `exists_star_chord_step_simple_triangle` gives cyclically
   simple triangle walks and the required corner data, but no assertion
   that their left faces are bounded. The exterior of a simple triangle
   is itself an unbounded face. `exists_chord_arc_in_face` confines the
   new arc to the original face and supplies corner inequalities; it has
   no side-at-infinity conclusion. Selecting bounded ears consistently
   throughout the exterior star remains an additional geometric proof.
3. Transport. `exists_plImageHomeomorph` maps the drawing images, not their
   complements. The plane extension for simple orbit boundaries requires
   the same exterior orbit in both drawings. Using it on the starred
   drawings would assume the missing match. An outer chart before the
   star requires a cyclically simple original boundary, which need not
   hold, and its homeomorphism has no PL pullback guarantee.

For simultaneous triangulation, the three routes were: iterate arbitrary
stars (the exterior labels remain separate); leave the exterior untouched
(proved above, but its period and simplicity remain those of the original);
or star the exterior first and then triangulate away from the resulting
triangle (the first star still needs Step 1). None proves Step 2 yet.

For the frame, the three routes were: attach a far pendant to a preselected
square (a first-contact prefix and the correct corner slot remain needed);
choose the square after the pendant (its endpoint is strictly inside, so
a controlled continuation and frame insertions remain needed); or use an
outer chart and square cone (the simple original boundary and PL transport
requirements are unavailable). A geometric square alone inserts no darts.

The proved reduction preserves the entire original exterior and its exact
period and simplicity. It therefore does not supply period four or
simplicity for an arbitrary original exterior. Step 3 records that missing
frame construction separately from the full DU1 target in Step 4.

### Step 1: a common exterior triangle in a single star (DU5:286)

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

### Step 2: simultaneous triangular exterior (DU5:328)

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

### Step 3: frame insertion before bounded-face triangulation

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
    (∃ d ∈ E.val, Function.minimalPeriod C.map.faceSucc d = 4 ∧
      Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] d))
        (Set.Iio 4)) ∧
    (∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
    (∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val)

### Step 4: complete DU1 (DU5:376)

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

end D39FiniteBall
end DirectedDistances.PlanarMap
end
