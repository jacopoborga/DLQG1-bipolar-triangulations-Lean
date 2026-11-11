/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLFrameInsertion4
public import DirectedDistances.PaperProofs.Section5.Prop516PLTriangularExterior

/-! Helpers toward Proposition 5.16: common original-face decompositions for -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: pendant insertion preserves dart
connectedness, including both new dart identities. -/
theorem frame_insertPendant_connected (B : D39FiniteBall) (a : B.D)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    ∀ d e : (B.insertPendant a).D, Relation.EqvGen
      (fun x y => (B.insertPendant a).map.rot x = y ∨
        (B.insertPendant a).map.edgeInv x = y) d e := by
  let C := B.insertPendant a
  let R := fun x y : C.D => C.map.rot x = y ∨ C.map.edgeInv x = y
  have hrot (d : B.D) : Relation.EqvGen R (.inl d) (.inl (B.map.rot d)) := by
    by_cases hd : d = a
    · subst d
      exact (Relation.EqvGen.rel (r := R) _ _ (Or.inl (B.pendantRotation_attachment a))).trans
        _ _ _ (Relation.EqvGen.rel _ _ (Or.inl (B.pendantRotation_true a)))
    · exact Relation.EqvGen.rel _ _ (Or.inl (B.pendantRotation_inl_of_ne a d hd))
  have hlift (d e : B.D) : Relation.EqvGen R (.inl d) (.inl e) := by
    induction hconn d e with
    | rel x y h =>
      rcases h with h | h
      · exact h ▸ hrot x
      · exact Relation.EqvGen.rel _ _ (Or.inr (congrArg Sum.inl h))
    | refl => exact Relation.EqvGen.refl _
    | symm x y h ih => exact ih.symm _ _
    | trans x y z h h' ih ih' => exact ih.trans _ _ _ ih'
  have htrue : Relation.EqvGen R (.inr true) (.inl a) :=
    (Relation.EqvGen.rel (r := R) _ _ (Or.inl (B.pendantRotation_attachment a))).symm _ _
  have hpath (d : C.D) : Relation.EqvGen R d (.inl a) := by
    rcases d with d | t
    · exact hlift d a
    · cases t with
      | false => exact (Relation.EqvGen.rel (r := R) _ _ (Or.inr rfl)).trans _ _ _ htrue
      | true => exact htrue
  intro d e
  exact (hpath d).trans _ _ _ ((hpath e).symm _ _)

/-- Helper toward Proposition 5.16: chord insertion preserves dart
connectedness without requiring a simple exterior. -/
theorem frame_insertChord_connected (B : D39FiniteBall) (a b : B.D) (hab : a ≠ b)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    ∀ d e : (B.insertChord a b hab).D, Relation.EqvGen
      (fun x y => (B.insertChord a b hab).map.rot x = y ∨
        (B.insertChord a b hab).map.edgeInv x = y) d e := by
  let C := B.insertChord a b hab
  let R := fun x y : C.D => C.map.rot x = y ∨ C.map.edgeInv x = y
  have hrot (d : B.D) : Relation.EqvGen R (.inl d) (.inl (B.map.rot d)) := by
    by_cases ha : d = a
    · subst d
      exact (Relation.EqvGen.rel (r := R) _ _ (Or.inl (B.chordRotation_a a b hab))).trans
        _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))
    · by_cases hb : d = b
      · subst d
        exact (Relation.EqvGen.rel (r := R) _ _ (Or.inl (B.chordRotation_b a b hab))).trans
          _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))
      · exact Relation.EqvGen.rel _ _ (Or.inl (B.chordRotation_other a b d hab ha hb))
  have hlift (d e : B.D) : Relation.EqvGen R (.inl d) (.inl e) := by
    induction hconn d e with
    | rel x y h =>
      rcases h with h | h
      · exact h ▸ hrot x
      · exact Relation.EqvGen.rel _ _ (Or.inr (congrArg Sum.inl h))
    | refl => exact Relation.EqvGen.refl _
    | symm x y h ih => exact ih.symm _ _
    | trans x y z h h' ih ih' => exact ih.trans _ _ _ ih'
  have hpath (d : C.D) : Relation.EqvGen R d (.inl a) := by
    rcases d with d | t
    · exact hlift d a
    · cases t with
      | false => exact ((Relation.EqvGen.rel (r := R) _ _
          (Or.inl (B.chordRotation_b a b hab))).symm _ _).trans _ _ _ (hlift b a)
      | true => exact (Relation.EqvGen.rel (r := R) _ _
          (Or.inl (B.chordRotation_a a b hab))).symm _ _
  intro d e
  exact (hpath d).trans _ _ _ ((hpath e).symm _ _)

/-- Helper toward Proposition 5.16: an exact retained orbit stays exact
after a pendant whose attachment lies outside that orbit. -/
theorem frame_pendant_retains_orbit (B C : D39FiniteBall) (ι : B.D ↪ C.D)
    (x : B.D) (a : C.D)
    (horbit : ∀ z, C.map.faceSucc.SameCycle (ι x) z ↔
      ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y)
    (ha : ¬ C.map.faceSucc.SameCycle a (ι x)) :
    ∀ z, (C.insertPendant a).map.faceSucc.SameCycle (.inl (ι x)) z ↔
      ∃ y, B.map.faceSucc.SameCycle x y ∧ z = .inl (ι y) := by
  intro z
  change (C.pendantMap a).faceSucc.SameCycle (.inl (ι x)) z ↔ _
  rw [(C.star_pendant_orbit_unaffected a (ι x) ha).1 z]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (horbit w).mp hw
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ι y, (horbit (ι y)).mpr ⟨y, hy, rfl⟩, rfl⟩

/-- Helper toward Proposition 5.16: closing the three pendant sides
changes only the original attachment face orbit. -/
theorem frame_three_sides_closing_retains_orbit (B : D39FiniteBall) (a x : B.D)
    (hx : ¬ B.map.faceSucc.SameCycle a x) :
    let D₁ := B.insertPendant a
    let D₂ := D₁.insertPendant (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let C := D₃.insertChord (.inr false) (.inl (.inl (.inl a))) Sum.inr_ne_inl
    ∀ z : C.D,
      C.map.faceSucc.SameCycle (.inl (.inl (.inl (.inl x)))) z ↔
        ∃ y, B.map.faceSucc.SameCycle x y ∧ z = .inl (.inl (.inl (.inl y))) := by
  dsimp only
  let D₁ := B.insertPendant a
  let D₂ := D₁.insertPendant (.inr false)
  let D₃ := D₂.insertPendant (.inr false)
  let ι₁ : B.D ↪ D₁.D := ⟨Sum.inl, Sum.inl_injective⟩
  let ι₂ : B.D ↪ D₂.D := ⟨fun d => .inl (.inl d), fun _ _ h => Sum.inl.inj (Sum.inl.inj h)⟩
  have h₁ : ∀ z : D₁.D, D₁.map.faceSucc.SameCycle (.inl x) z ↔
      ∃ y, B.map.faceSucc.SameCycle x y ∧ z = .inl y :=
    (B.star_pendant_orbit_unaffected a x hx).1
  have hnot₁ : ¬ D₁.map.faceSucc.SameCycle (.inr false) (.inl x) := by
    intro h
    obtain ⟨y, _, hy⟩ := (h₁ (.inr false)).mp h.symm
    cases hy
  have h₂ := B.frame_pendant_retains_orbit D₁ ι₁ x (.inr false) h₁ hnot₁
  have hnot₂ : ¬ D₂.map.faceSucc.SameCycle (.inr false) (.inl (.inl x)) := by
    intro h
    obtain ⟨y, _, hy⟩ := (h₂ (.inr false)).mp h.symm
    cases hy
  have h₃ := B.frame_pendant_retains_orbit D₂ ι₂ x (.inr false) h₂ hnot₂
  have hnot₃ : ¬ D₃.map.faceSucc.SameCycle (.inl (.inl (.inl x))) (.inr false) := by
    intro h
    obtain ⟨y, _, hy⟩ := (h₃ (.inr false)).mp h
    cases hy
  have hnot_a : ¬ D₃.map.faceSucc.SameCycle (.inl (.inl (.inl x)))
      (.inl (.inl (.inl a))) := by
    intro h
    obtain ⟨y, hy, he⟩ := (h₃ (.inl (.inl (.inl a)))).mp h
    have he' : a = y := Sum.inl.inj (Sum.inl.inj (Sum.inl.inj he))
    subst y
    exact hx hy.symm
  intro z
  change (D₃.chordMap (.inr false) (.inl (.inl (.inl a))) Sum.inr_ne_inl).faceSucc.SameCycle
    (.inl (.inl (.inl (.inl x)))) z ↔ _
  refine (D₃.chordMap_faceSucc_sameCycle_unaffected_iff _ _ Sum.inr_ne_inl _
    hnot₃ hnot_a z).trans ?_
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (h₃ w).mp hw
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨.inl (.inl (.inl y)), (h₃ _).mpr ⟨y, hy, rfl⟩, rfl⟩

/-- Helper toward Proposition 5.16: Step 3 inserts a common exterior
four-cycle and constructs one shared closed-face decomposition, preserving
all original dart identities, tags, arcs and vertex positions. -/
theorem exists_sum_fin_frame_drawings
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)) :
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
        Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] d)) (Set.Iio 4)) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        closure (B.plOrbitFace vert P hvert O).val =
          ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        closure (B.plOrbitFace vert P' hvert O).val =
          ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) := by
  classical
  let a := O_ext.property.choose
  have ha : a ∈ O_ext.val := O_ext.property.choose_spec.symm ▸ Equiv.Perm.SameCycle.rfl
  have hext_a : (¬ Bornology.IsBounded (B.plDartFace vert P hvert a).val) ∧
      (¬ Bornology.IsBounded (B.plDartFace vert P' hvert a).val) := by
    rw [B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O_ext a ha,
      B.plOrbitFace_eq_plDartFace_of_mem vert P' hvert O_ext a ha] at hext
    exact hext
  obtain ⟨R, Q, Q', hR, hb, hp, hp', harc, harc', hc, hc', hct, hct', _, _⟩ :=
    B.exists_pendant_drawings_to_common_enclosingSquare vert P P' hvert a hext_a
  let D₀ := B.insertPendant a
  let w₀ := B.pendantVert vert a
  have hw₀ : Function.Surjective w₀ := B.pendantVert_surjective vert a hvert
  have hQ := B.pendantDrawing_image_subset_closedSquare vert P a Q R hR
    (fun z hz => hb z (Or.inl hz)) hp harc hct
  have hQ' := B.pendantDrawing_image_subset_closedSquare vert P' a Q' R hR
    (fun z hz => hb z (Or.inr hz)) hp' harc' hct'
  let D₁ := D₀.insertPendant (.inr false)
  let w₁ := D₀.pendantVert w₀ (.inr false)
  let D₂ := D₁.insertPendant (.inr false)
  let w₂ := D₁.pendantVert w₁ (.inr false)
  let D₃ := D₂.insertPendant (.inr false)
  let w₃ := D₂.pendantVert w₂ (.inr false)
  let C := D₃.insertChord (.inr false) (.inl (.inl (.inl (.inr false)))) Sum.inr_ne_inl
  let v := D₃.chordVert w₃ (.inr false) (.inl (.inl (.inl (.inr false))))
  let ι : B.D ↪ C.D := ⟨fun d => .inl (.inl (.inl (.inl (.inl d)))),
    fun _ _ h => Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h))))⟩
  let σ : V ↪ Option (Option (Option (Option V))) :=
    ⟨fun x => some (some (some (some x))),
      fun _ _ h => Option.some.inj (Option.some.inj (Option.some.inj (Option.some.inj h)))⟩
  obtain ⟨s, s', t, t', T, T', hv, E, hpos, hpos', he, he', _hF, _hF',
    _hi, _hi', hd, hperiod, hinj, _hout, _hout', hu, hu'⟩ :=
    D₀.exists_common_unbounded_corner_four_cycle w₀ Q Q' hw₀ (.inr false)
      (by rfl) R hR hQ hQ' hc hc'
  have hconnected := B.frame_insertPendant_connected a hconn
  have hconnected₁ := D₀.frame_insertPendant_connected (.inr false) hconnected
  have hconnected₂ := D₁.frame_insertPendant_connected (.inr false) hconnected₁
  have hconnected₃ := D₂.frame_insertPendant_connected (.inr false) hconnected₂
  have hconnectedC := D₃.frame_insertChord_connected (.inr false)
    (.inl (.inl (.inl (.inr false)))) Sum.inr_ne_inl hconnected₃
  have hpos_all (x : V) : T.pos (σ x) = P.pos x := (hpos (some x)).trans (hp x)
  have hpos_all' (x : V) : T'.pos (σ x) = P'.pos x := (hpos' (some x)).trans (hp' x)
  have he_all (d : B.D) : T.arc (ι d) = P.arc d := (he (.inl d)).trans (harc d)
  have he_all' (d : B.D) : T'.arc (ι d) = P'.arc d := (he' (.inl d)).trans (harc' d)
  have himage : P.image ⊆ T.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hpos_all x⟩
    · exact Or.inr ⟨ι d, he_all d ▸ hd⟩
  have himage' : P'.image ⊆ T'.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hpos_all' x⟩
    · exact Or.inr ⟨ι d, he_all' d ▸ hd⟩
  have horbit (x : B.D) (hx : ¬ B.map.faceSucc.SameCycle a x) (z : C.D) :
      C.map.faceSucc.SameCycle (ι x) z ↔
        ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y := by
    have hnot : ¬ D₀.map.faceSucc.SameCycle (.inr false) (.inl x) := by
      exact fun h => hx ((B.star_pendant_sameCycle_inl a x).mp h)
    have hframe := D₀.frame_three_sides_closing_retains_orbit (.inr false) (.inl x) hnot z
    refine hframe.trans ?_
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y, hy, rfl⟩ := (B.star_pendant_orbit_unaffected a x hx).1 w |>.mp hw
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨.inl y, ((B.star_pendant_orbit_unaffected a x hx).1 _).mpr ⟨y, hy, rfl⟩, rfl⟩
  obtain ⟨I, _hI, _hI', hcover, hcover'⟩ :=
    B.drawing_exists_common_closed_face_index_of_unchanged_other_orbits C vert v P P' T T'
      hvert hv hconn hconnectedC ι himage himage' he_all he_all' a horbit
  obtain ⟨n, e, U, U', hw, heσ, hposU, hposU', harcU, harcU', _, _, hfaces, hfaces', hinjU⟩ :=
    C.drawing_exists_sum_fin_reindex v T T' hv σ
  refine ⟨n, C, e ∘ v, ι, U, U', hw, E, I, hconnectedC, rfl,
    (fun _ => rfl), ?_, (fun _ => Iff.rfl), (fun _ => Iff.rfl),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    exact heσ (vert d)
  · intro x
    exact (hposU x).trans (hpos_all x)
  · intro x
    exact (hposU' x).trans (hpos_all' x)
  · intro d
    exact (harcU (ι d)).trans (he_all d)
  · intro d
    exact (harcU' (ι d)).trans (he_all' d)
  · rw [hfaces E]
    exact hu
  · rw [hfaces' E]
    exact hu'
  · exact ⟨.inr false, hd, hperiod, (hinjU _ _).mpr hinj⟩
  · intro O
    simp_rw [hfaces]
    exact hcover O
  · intro O
    simp_rw [hfaces']
    exact hcover' O

/-- Helper toward Proposition 5.16: Step 4 (DU1) inserts a common
quadrilateral exterior and triangulates every bounded face. Both drawings
use the same closed-face decomposition and retain all original data. -/
theorem exists_sum_fin_augmented_drawings
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)) :
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
          ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) := by
  classical
  obtain ⟨n₀, C₀, v₀, ι₀, Q₀, Q₀', hv₀, E₀, I₀, hc₀, hr₀, hf₀, hver₀,
    hm₀, ht₀, hp₀, hp₀', ha₀, ha₀', hu₀, hu₀', hframe, hcover₀, hcover₀'⟩ :=
    B.exists_sum_fin_frame_drawings vert P P' hvert hconn O_ext hext
  have hboundary : ∃ a ∈ E₀.val,
      Function.minimalPeriod C₀.map.faceSucc a = 4 ∧
      Set.InjOn (fun k : ℕ => v₀ ((C₀.map.faceSucc : C₀.D → C₀.D)^[k] a))
        (Set.Iio (Function.minimalPeriod C₀.map.faceSucc a)) := by
    obtain ⟨a, ha, hperiod, hinj⟩ := hframe
    exact ⟨a, ha, hperiod, hperiod.symm ▸ hinj⟩
  obtain ⟨n₁, C, v, ι₁, Q, Q', hv, E, I₁, hc, hr₁, hf₁, hver₁,
    hm₁, ht₁, hp₁, hp₁', ha₁, ha₁', hu, hu', htri, hcover₁, hcover₁'⟩ :=
    C₀.exists_sum_fin_augmented_drawings_of_simple_exterior v₀ Q₀ Q₀' hv₀ hc₀
      E₀ ⟨hu₀, hu₀'⟩ 4 hboundary
  let ι := ι₀.trans ι₁
  let σ : V ↪ (V ⊕ Fin n₀) ⊕ Fin n₁ :=
    ⟨fun x => .inl (.inl x), fun _ _ h => Sum.inl.inj (Sum.inl.inj h)⟩
  let I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C) :=
    fun O => {S | ∃ T ∈ I₀ O, S ∈ I₁ T}
  have hvertex (d : B.D) : v (ι d) = σ (vert d) :=
    (hver₁ (ι₀ d)).trans (congrArg Sum.inl (hver₀ d))
  have hpos (x : V) : Q.pos (σ x) = P.pos x := (hp₁ (.inl x)).trans (hp₀ x)
  have hpos' (x : V) : Q'.pos (σ x) = P'.pos x := (hp₁' (.inl x)).trans (hp₀' x)
  have harc (d : B.D) : Q.arc (ι d) = P.arc d := (ha₁ (ι₀ d)).trans (ha₀ d)
  have harc' (d : B.D) : Q'.arc (ι d) = P'.arc d := (ha₁' (ι₀ d)).trans (ha₀' d)
  have hcover (O : D39BallFaceCycleOrbit B) :
      closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val := by
    rw [hcover₀ O]
    simp_rw [hcover₁]
    ext z
    simp only [mem_iUnion, I, mem_ofPred_eq]
    constructor
    · rintro ⟨T, hT, S, hS, hz⟩
      exact ⟨S, ⟨T, hT, hS⟩, hz⟩
    · rintro ⟨S, ⟨T, hT, hS⟩, hz⟩
      exact ⟨T, hT, S, hS, hz⟩
  have hcover' (O : D39BallFaceCycleOrbit B) :
      closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val := by
    rw [hcover₀' O]
    simp_rw [hcover₁']
    ext z
    simp only [mem_iUnion, I, mem_ofPred_eq]
    constructor
    · rintro ⟨T, hT, S, hS, hz⟩
      exact ⟨S, ⟨T, hT, hS⟩, hz⟩
    · rintro ⟨S, ⟨T, hT, hS⟩, hz⟩
      exact ⟨T, hT, S, hS, hz⟩
  obtain ⟨n, e, U, U', hw, heσ, hposU, hposU', harcU, harcU', _, _, hfaces, hfaces', hinjU⟩ :=
    C.drawing_exists_sum_fin_reindex v Q Q' hv σ
  refine ⟨n, C, e ∘ v, ι, U, U', hw, E, I, hc,
    hr₁.trans (congrArg ι₁ hr₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    exact (hf₁ (ι₀ d)).trans (congrArg ι₁ (hf₀ d))
  · intro d
    exact (congrArg e (hvertex d)).trans (heσ (vert d))
  · intro d
    exact (hm₁ (ι₀ d)).trans (hm₀ d)
  · intro d
    exact (ht₁ (ι₀ d)).trans (ht₀ d)
  · intro x
    exact (hposU x).trans (hpos x)
  · intro x
    exact (hposU' x).trans (hpos' x)
  · intro d
    exact (harcU (ι d)).trans (harc d)
  · intro d
    exact (harcU' (ι d)).trans (harc' d)
  · rw [hfaces E]
    exact hu
  · rw [hfaces' E]
    exact hu'
  · intro O
    obtain ⟨d, hd, hquad, htriangle, hinj⟩ := htri O
    exact ⟨d, hd, hquad, htriangle, (hinjU _ _).mpr hinj⟩
  · intro O
    simp_rw [hfaces]
    exact hcover O
  · intro O
    simp_rw [hfaces']
    exact hcover' O

end D39FiniteBall
end DirectedDistances.PlanarMap

end
