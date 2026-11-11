/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLDrawingAugmentation
public import DirectedDistances.PaperProofs.Section5.Prop516PLStarChordBoundedSide
public import DirectedDistances.PaperProofs.Section5.Prop516PLStarChordBoundedSide2
public import DirectedDistances.PaperProofs.Section5.Prop516PLFrameInsertion2

/-! # Triangular exterior and bounded-face refinement

Helpers toward Proposition 5.16 and the finite drawing interpretation of
construction helpers, not a completion claim for a numbered paper result. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: triangulate all bounded faces of two
drawings with a common triangular exterior. The entire open exterior and
its boundary dart orbit are retained, with a singleton exterior child and
one common index for both closed-face decompositions. Vertex simplicity is
proved from period three, rather than assumed. -/
theorem exists_sum_fin_triangulated_drawings_of_triangular_exterior
    {V : Type u} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (htriangle : ∃ a ∈ O_ext.val, Function.minimalPeriod B.map.faceSucc a = 3) :
    ∃ (n : ℕ) (C : D39FiniteBall) (v : C.D → V ⊕ Fin n)
      (ι : B.D ↪ C.D)
      (Q Q' : PLDrawing C.D (V ⊕ Fin n) C.map.edgeInv C.map.rot v)
      (hv : Function.Surjective v) (E : D39BallFaceCycleOrbit C)
      (I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C)),
      (∀ d e : C.D, Relation.EqvGen
        (fun x y => C.map.rot x = y ∨ C.map.edgeInv x = y) d e) ∧
      C.rootDart = ι B.rootDart ∧
      (∀ d, C.map.edgeInv (ι d) = ι (B.map.edgeInv d)) ∧
      (∀ d, v (ι d) = Sum.inl (vert d)) ∧
      (∀ d, C.missing (ι d) ↔ B.missing d) ∧
      (∀ d, C.tail (ι d) ↔ B.tail d) ∧
      (∀ x, Q.pos (Sum.inl x) = P.pos x) ∧
      (∀ x, Q'.pos (Sum.inl x) = P'.pos x) ∧
      (∀ d, Q.arc (ι d) = P.arc d) ∧
      (∀ d, Q'.arc (ι d) = P'.arc d) ∧
      (¬ Bornology.IsBounded (C.plOrbitFace v Q hv E).val) ∧
      (¬ Bornology.IsBounded (C.plOrbitFace v Q' hv E).val) ∧
      (∀ d : C.D, Function.minimalPeriod C.map.faceSucc d = 3 ∧
        Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] d))
          (Set.Iio 3)) ∧
      E.val = ι '' O_ext.val ∧
      (C.plOrbitFace v Q hv E).val = (B.plOrbitFace vert P hvert O_ext).val ∧
      (C.plOrbitFace v Q' hv E).val = (B.plOrbitFace vert P' hvert O_ext).val ∧
      I O_ext = {E} ∧
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val) ∧
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace v Q' hv S).val ⊆ (B.plOrbitFace vert P' hvert O).val) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        closure (B.plOrbitFace vert P hvert O).val =
          ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        closure (B.plOrbitFace vert P' hvert O).val =
          ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) := by
  classical
  obtain ⟨a, ha, hthree⟩ := htriangle
  have hsame : B.map.faceSucc.SameCycle O_ext.property.choose a := by
    exact (show a ∈ {e | B.map.faceSucc.SameCycle O_ext.property.choose e}
      from O_ext.property.choose_spec ▸ ha)
  have hthree0 : Function.minimalPeriod B.map.faceSucc O_ext.property.choose = 3 :=
    (drawing_period_of_sameCycle B.map.faceSucc hsame).symm.trans hthree
  obtain ⟨n, C, v, ι, Q, Q', hv, E, I, hc, hr, hf, hvertex, hm, ht,
    hp, hp', harc, harc', hE, hface, hface', hu, hu', htri,
    hperiod, _hsimp, hsingle, hI, hI', hcover, hcover'⟩ :=
    B.exists_sum_fin_triangulated_drawings_with_preserved_exterior
      vert P P' hvert hconn O_ext hext
  refine ⟨n, C, v, ι, Q, Q', hv, E, I, hc, hr, hf, hvertex, hm, ht,
    hp, hp', harc, harc', (hu E).mpr rfl, (hu' E).mpr rfl, ?_,
    hE, hface, hface', hsingle, hI, hI', hcover, hcover'⟩
  intro d
  by_cases hd : d ∈ E.val
  · have hp3 := (hperiod d hd).trans hthree0
    exact ⟨hp3, C.drawing_triangle_initialVertices v Q d hp3⟩
  · exact htri d hd

/-- Helper toward Proposition 5.16: when all other original face orbits
are retained exactly, a child outside those orbits lies in the one modified
parent. This identifies its geometric parent without choosing star indices. -/
theorem drawing_modified_face_subset_of_unchanged_other_orbits
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hc : ∀ x y : C.D, Relation.EqvGen
      (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y)
    (ι : B.D ↪ C.D) (himage : P.image ⊆ Q.image)
    (harc : ∀ d, Q.arc (ι d) = P.arc d) (a : B.D)
    (horbit : ∀ x, ¬ B.map.faceSucc.SameCycle a x → ∀ z,
      C.map.faceSucc.SameCycle (ι x) z ↔
        ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y)
    (z : C.D)
    (hz : ∀ x, ¬ B.map.faceSucc.SameCycle a x →
      ¬ C.map.faceSucc.SameCycle (ι x) z) :
    (C.plDartFace v Q hv z).val ⊆ (B.plDartFace vert P hvert a).val := by
  obtain ⟨F, hsub, _⟩ :=
    B.drawing_face_unique_parent C vert v P Q himage (C.plDartFace v Q hv z)
  obtain ⟨x, hx⟩ := B.plDartFace_surjective vert P hvert F
  have hsubx : (C.plDartFace v Q hv z).val ⊆
      (B.plDartFace vert P hvert x).val := hx.symm ▸ hsub
  by_cases hax : B.map.faceSucc.SameCycle a x
  · rw [B.plDartFace_eq_of_sameCycle vert P hvert x a hax.symm] at hsubx
    exact hsubx
  · have heq := B.drawing_unchanged_orbit_face_eq C vert v P Q hvert hv hc
      ι himage harc x (horbit x hax)
    obtain ⟨w, hw, hG⟩ := (C.plDartFace v Q hv z).property
    have hwG : w ∈ (C.plDartFace v Q hv z).val := hG ▸ mem_connectedComponentIn hw
    have hwx : w ∈ (C.plDartFace v Q hv (ι x)).val := heq.symm ▸ hsubx hwG
    exact (hz x hax (C.plDartFace_sameCycle_of_eq v Q hv hc (ι x) z
      (Q.faces_eq_of_mem hwx hwG))).elim

/-- Helper toward Proposition 5.16: any simultaneous refinement changing
only one parent orbit has a common index for the closed-face decompositions.
The parent of a new child is derived from the unchanged other orbits; no
common-parent or closed-face decomposition premise is needed. -/
theorem drawing_exists_common_closed_face_index_of_unchanged_other_orbits
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (hc : ∀ x y : C.D, Relation.EqvGen
      (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y)
    (ι : B.D ↪ C.D)
    (himage : P.image ⊆ Q.image) (himage' : P'.image ⊆ Q'.image)
    (harc : ∀ d, Q.arc (ι d) = P.arc d)
    (harc' : ∀ d, Q'.arc (ι d) = P'.arc d) (a : B.D)
    (horbit : ∀ x, ¬ B.map.faceSucc.SameCycle a x → ∀ z,
      C.map.faceSucc.SameCycle (ι x) z ↔
        ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y) :
    ∃ I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C),
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val) ∧
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace v Q' hv S).val ⊆ (B.plOrbitFace vert P' hvert O).val) ∧
      (∀ O, closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
      (∀ O, closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) := by
  classical
  apply B.drawing_exists_common_closed_face_index C vert v P P' Q Q'
    hvert hv hconn himage himage'
  intro z
  by_cases hz : ∃ x, ¬ B.map.faceSucc.SameCycle a x ∧
      C.map.faceSucc.SameCycle (ι x) z
  · obtain ⟨x, _, hcycle⟩ := hz
    refine ⟨x, ?_, ?_⟩
    · rw [C.plDartFace_eq_of_sameCycle v Q hv z (ι x) hcycle.symm]
      exact B.drawing_inherited_dart_face_subset C vert v P Q hvert hv
        himage x (ι x) (harc x)
    · rw [C.plDartFace_eq_of_sameCycle v Q' hv z (ι x) hcycle.symm]
      exact B.drawing_inherited_dart_face_subset C vert v P' Q' hvert hv
        himage' x (ι x) (harc' x)
  · have havoid : ∀ x, ¬ B.map.faceSucc.SameCycle a x →
        ¬ C.map.faceSucc.SameCycle (ι x) z := by
      intro x hx hzx
      exact hz ⟨x, hx, hzx⟩
    exact ⟨a,
      B.drawing_modified_face_subset_of_unchanged_other_orbits C vert v P Q
        hvert hv hc ι himage harc a horbit z havoid,
      B.drawing_modified_face_subset_of_unchanged_other_orbits C vert v P' Q'
        hvert hv hc ι himage' harc' a horbit z havoid⟩

/-- Helper toward Proposition 5.16: intermediate Step 2 assuming exactly
the construction output of Step 1 (a single star with a common unbounded
child). This is an explicitly conditional construction lemma, not an
unconditional drawing-uniqueness or paper theorem. Only the selected star
child must already be triangular; all remaining faces are triangulated
here. Both original closed-face decompositions are constructed and composed. -/
theorem exists_triangulated_drawings_intermediate_of_step1_output
    {V : Type u} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (_hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hstep1 : ∃ (C : D39FiniteBall) (v : C.D → Option V) (ι : B.D ↪ C.D)
      (Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
      (hv : Function.Surjective v)
      (s : Fin (Function.minimalPeriod B.map.faceSucc O_ext.property.choose) → C.D),
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
      (∀ x, ¬ B.map.faceSucc.SameCycle O_ext.property.choose x → ∀ z,
        C.map.faceSucc.SameCycle (ι x) z ↔
          ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y) ∧
      (∀ z, (∃ i, C.map.faceSucc.SameCycle (s i) z) ∨
        ∃ x, ¬ B.map.faceSucc.SameCycle O_ext.property.choose x ∧ z = ι x) ∧
      (∃ i,
        (¬ Bornology.IsBounded (C.plDartFace v Q hv (s i)).val) ∧
        (¬ Bornology.IsBounded (C.plDartFace v Q' hv (s i)).val))) :
    ∃ (W : Type u) (C : D39FiniteBall) (v : C.D → W)
      (ι : B.D ↪ C.D) (σ : V ↪ W)
      (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
      (hv : Function.Surjective v) (E : D39BallFaceCycleOrbit C)
      (I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C)),
      (∀ d e : C.D, Relation.EqvGen
        (fun x y => C.map.rot x = y ∨ C.map.edgeInv x = y) d e) ∧
      C.rootDart = ι B.rootDart ∧
      (∀ d, C.map.edgeInv (ι d) = ι (B.map.edgeInv d)) ∧
      (∀ d, v (ι d) = σ (vert d)) ∧
      (∀ d, C.missing (ι d) ↔ B.missing d) ∧
      (∀ d, C.tail (ι d) ↔ B.tail d) ∧
      (∀ x, Q.pos (σ x) = P.pos x) ∧
      (∀ x, Q'.pos (σ x) = P'.pos x) ∧
      (∀ d, Q.arc (ι d) = P.arc d) ∧
      (∀ d, Q'.arc (ι d) = P'.arc d) ∧
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
          ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) := by
  classical
  obtain ⟨C₀, v₀, ι₀, Q₀, Q₀', hv₀, s, hc₀, hr₀, hf₀, hver₀, hm₀, ht₀,
    hp₀, hp₀', ha₀, ha₀', htri₀, _hdist, hu₀, _hex, i, hi, hi'⟩ := hstep1
  have himage : P.image ⊆ Q₀.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨some x, hp₀ x⟩
    · exact Or.inr ⟨ι₀ d, ha₀ d ▸ hd⟩
  have himage' : P'.image ⊆ Q₀'.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨some x, hp₀' x⟩
    · exact Or.inr ⟨ι₀ d, ha₀' d ▸ hd⟩
  obtain ⟨I₀, _hI₀, _hI₀', hcover₀, hcover₀'⟩ :=
    B.drawing_exists_common_closed_face_index_of_unchanged_other_orbits C₀ vert v₀
      P P' Q₀ Q₀' hvert hv₀ hconn hc₀ ι₀ himage himage' ha₀ ha₀'
      O_ext.property.choose hu₀
  let E₀ : D39BallFaceCycleOrbit C₀ :=
    ⟨{z | C₀.map.faceSucc.SameCycle (s i) z}, s i, rfl⟩
  have hsi : s i ∈ E₀.val := Equiv.Perm.SameCycle.rfl
  have hext₀ : (¬ Bornology.IsBounded (C₀.plOrbitFace v₀ Q₀ hv₀ E₀).val) ∧
      (¬ Bornology.IsBounded (C₀.plOrbitFace v₀ Q₀' hv₀ E₀).val) := by
    rw [C₀.plOrbitFace_eq_plDartFace_of_mem v₀ Q₀ hv₀ E₀ (s i) hsi,
      C₀.plOrbitFace_eq_plDartFace_of_mem v₀ Q₀' hv₀ E₀ (s i) hsi]
    exact ⟨hi, hi'⟩
  obtain ⟨n, C, v, ι₁, Q, Q', hv, E, I₁, hc, hr₁, hf₁, hver₁, hm₁, ht₁,
    hp₁, hp₁', ha₁, ha₁', hE, hE', htri, _hval, _hface, _hface',
    _hsingle, _hI₁, _hI₁', hcover₁, hcover₁'⟩ :=
    C₀.exists_sum_fin_triangulated_drawings_of_triangular_exterior v₀ Q₀ Q₀'
      hv₀ hc₀ E₀ hext₀ ⟨s i, hsi, htri₀ i⟩
  let σ : V ↪ Option V ⊕ Fin n :=
    ⟨fun x => Sum.inl (some x), fun _ _ h => Option.some.inj (Sum.inl.inj h)⟩
  let I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C) :=
    fun O => {S | ∃ T ∈ I₀ O, S ∈ I₁ T}
  refine ⟨Option V ⊕ Fin n, C, v, ι₀.trans ι₁, σ, Q, Q', hv, E, I,
    hc, hr₁.trans (congrArg ι₁ hr₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hE, hE', htri, ?_, ?_⟩
  · intro d
    exact (hf₁ (ι₀ d)).trans (congrArg ι₁ (hf₀ d))
  · intro d
    exact (hver₁ (ι₀ d)).trans (congrArg Sum.inl (hver₀ d))
  · intro d
    exact (hm₁ (ι₀ d)).trans (hm₀ d)
  · intro d
    exact (ht₁ (ι₀ d)).trans (ht₀ d)
  · intro x
    exact (hp₁ (some x)).trans (hp₀ x)
  · intro x
    exact (hp₁' (some x)).trans (hp₀' x)
  · intro d
    exact (ha₁ (ι₀ d)).trans (ha₀ d)
  · intro d
    exact (ha₁' (ι₀ d)).trans (ha₀' d)
  · intro O
    rw [hcover₀ O]
    simp_rw [hcover₁]
    ext z
    simp only [mem_iUnion, I, mem_ofPred_eq]
    constructor
    · rintro ⟨T, hT, S, hS, hz⟩
      exact ⟨S, ⟨T, hT, hS⟩, hz⟩
    · rintro ⟨S, ⟨T, hT, hS⟩, hz⟩
      exact ⟨T, hT, S, hS, hz⟩
  · intro O
    rw [hcover₀' O]
    simp_rw [hcover₁']
    ext z
    simp only [mem_iUnion, I, mem_ofPred_eq]
    constructor
    · rintro ⟨T, hT, S, hS, hz⟩
      exact ⟨S, ⟨T, hT, hS⟩, hz⟩
    · rintro ⟨S, ⟨T, hT, hS⟩, hz⟩
      exact ⟨T, hT, S, hS, hz⟩

end D39FiniteBall
end DirectedDistances.PlanarMap

end






































































