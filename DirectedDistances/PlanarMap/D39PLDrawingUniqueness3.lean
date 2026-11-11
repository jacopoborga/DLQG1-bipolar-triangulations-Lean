/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness2

/-! # Common parents for face subdivisions

Helpers toward Proposition 5.16. These are internal drawing-construction
and integration belong to the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: a face incident to the new star centre
lies in the subdivided original face. Exact preservation of every other
orbit rules out all other geometric parents. -/
theorem drawing_centre_face_subset
    {V : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → Option V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hc : ∀ x y : C.D, Relation.EqvGen
      (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y)
    (ι : B.D ↪ C.D) (himage : P.image ⊆ Q.image)
    (hvertex : ∀ x, v (ι x) = some (vert x))
    (harc : ∀ x, Q.arc (ι x) = P.arc x) (r : C.D)
    (a : B.D)
    (hunaffected : ∀ x, ¬ B.map.faceSucc.SameCycle a x → ∀ z,
      C.map.faceSucc.SameCycle (ι x) z ↔
        ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y)
    (hcentre : none ∈ v '' {z | C.map.faceSucc.SameCycle r z}) :
    (C.plDartFace v Q hv r).val ⊆ (B.plDartFace vert P hvert a).val := by
  obtain ⟨F, hF, _⟩ := B.drawing_face_unique_parent C vert v P Q himage
    (C.plDartFace v Q hv r)
  obtain ⟨x, hx⟩ := B.plDartFace_surjective vert P hvert F
  have hsub : (C.plDartFace v Q hv r).val ⊆ (B.plDartFace vert P hvert x).val :=
    hx.symm ▸ hF
  by_cases ha : B.map.faceSucc.SameCycle a x
  · exact (congrArg Subtype.val (B.plDartFace_eq_of_sameCycle vert P hvert x a
      ha.symm)) ▸ hsub
  · have heq := B.drawing_unchanged_orbit_face_eq C vert v P Q hvert hv hc ι
      himage harc x (hunaffected x ha)
    obtain ⟨z, hz, hG⟩ := (C.plDartFace v Q hv r).property
    have hzG : z ∈ (C.plDartFace v Q hv r).val := hG ▸ mem_connectedComponentIn hz
    have hzI : z ∈ (C.plDartFace v Q hv (ι x)).val := heq.symm ▸ hsub hzG
    have hfaces := Q.faces_eq_of_mem hzI hzG
    have hcycle := C.plDartFace_sameCycle_of_eq v Q hv hc (ι x) r hfaces
    obtain ⟨w, hw, hnone⟩ := hcentre
    obtain ⟨y, _, hwy⟩ := (hunaffected x ha w).mp (hcycle.trans hw)
    rw [hwy, hvertex] at hnone
    cases hnone

/-- Helper toward Proposition 5.16: a complete star subdivision has a
common original parent dart for every augmented face in the two drawings.
This records geometric containment jointly, rather than choosing parents
independently in the two planes. -/
theorem exists_star_drawings_with_common_parents
    {V : Type u} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a : B.D) :
    ∃ (C : D39FiniteBall) (v : C.D → Option V) (ι : B.D ↪ C.D)
      (Q Q' : PLDrawing C.D (Option V) C.map.edgeInv C.map.rot v)
      (hv : Function.Surjective v),
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
      (∀ x, ¬ B.map.faceSucc.SameCycle a x → ∀ z,
        C.map.faceSucc.SameCycle (ι x) z ↔
          ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y) ∧
      (∀ z, Function.minimalPeriod C.map.faceSucc z = 3 ∨
        ∃ x, ¬ B.map.faceSucc.SameCycle a x ∧ z = ι x) ∧
      (∀ z, ∃ x,
        (C.plDartFace v Q hv z).val ⊆ (B.plDartFace vert P hvert x).val ∧
        (C.plDartFace v Q' hv z).val ⊆ (B.plDartFace vert P' hvert x).val) := by
  classical
  let k := Function.minimalPeriod B.map.faceSucc a
  obtain ⟨C, v, ι, Q, Q', s, hv, hc, _, hr, hf, hvertex, hm, ht,
    _, hp, hp', he, he', himage, himage', htri, _, hvertices, _, hu, hex⟩ :=
    B.exists_star_drawings vert P P' hvert hconn a k
      (B.drawing_face_period_ge_two vert P a) rfl
  have hparent (i : Fin k) :
      (C.plDartFace v Q hv (s i)).val ⊆ (B.plDartFace vert P hvert a).val ∧
      (C.plDartFace v Q' hv (s i)).val ⊆ (B.plDartFace vert P' hvert a).val := by
    have hnone : none ∈ v '' {z | C.map.faceSucc.SameCycle (s i) z} := by
      rw [hvertices i]
      exact Set.mem_insert _ _
    exact ⟨B.drawing_centre_face_subset C vert v P Q hvert hv hc ι himage
      hvertex he (s i) a hu hnone,
      B.drawing_centre_face_subset C vert v P' Q' hvert hv hc ι himage'
        hvertex he' (s i) a hu hnone⟩
  refine ⟨C, v, ι, Q, Q', hv, hc, hr, hf, hvertex, hm, ht, hp, hp', he, he',
    hu, ?_, ?_⟩
  · intro z
    rcases hex z with ⟨i, hi⟩ | hz
    · exact Or.inl ((drawing_period_of_sameCycle C.map.faceSucc hi).trans (htri i))
    · exact Or.inr hz
  · intro z
    rcases hex z with ⟨i, hi⟩ | ⟨x, _, rfl⟩
    · refine ⟨a, ?_, ?_⟩
      · exact (congrArg Subtype.val (C.plDartFace_eq_of_sameCycle v Q hv
          (s i) z hi)) ▸ (hparent i).1
      · exact (congrArg Subtype.val (C.plDartFace_eq_of_sameCycle v Q' hv
          (s i) z hi)) ▸ (hparent i).2
    · exact ⟨x, B.drawing_inherited_dart_face_subset C vert v P Q hvert hv
        himage x (ι x) (he x),
        B.drawing_inherited_dart_face_subset C vert v P' Q' hvert hv
          himage' x (ι x) (he' x)⟩

/-- Helper toward Proposition 5.16: finite star iteration propagates a
common original parent for every augmented face, including faces without
any original boundary dart. All unprocessed original orbits persist exactly. -/
theorem exists_iterated_star_drawings_with_common_parents
    {V : Type u} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (S : Finset B.D) :
    ∃ (W : Type u) (C : D39FiniteBall) (v : C.D → W)
      (ι : B.D ↪ C.D) (σ : V ↪ W)
      (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
      (hv : Function.Surjective v),
      (∀ x y : C.D, Relation.EqvGen
        (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y) ∧
      C.rootDart = ι B.rootDart ∧
      (∀ x, C.map.edgeInv (ι x) = ι (B.map.edgeInv x)) ∧
      (∀ x, v (ι x) = σ (vert x)) ∧
      (∀ x, C.missing (ι x) ↔ B.missing x) ∧
      (∀ x, C.tail (ι x) ↔ B.tail x) ∧
      (∀ x, Q.pos (σ x) = P.pos x) ∧
      (∀ x, Q'.pos (σ x) = P'.pos x) ∧
      (∀ x, Q.arc (ι x) = P.arc x) ∧
      (∀ x, Q'.arc (ι x) = P'.arc x) ∧
      (∀ x, (∀ a ∈ S, ¬ B.map.faceSucc.SameCycle a x) → ∀ z,
        C.map.faceSucc.SameCycle (ι x) z ↔
          ∃ y, B.map.faceSucc.SameCycle x y ∧ z = ι y) ∧
      (∀ z, Function.minimalPeriod C.map.faceSucc z = 3 ∨
        ∃ x, (∀ a ∈ S, ¬ B.map.faceSucc.SameCycle a x) ∧ z = ι x) ∧
      (∀ z, ∃ x,
        (C.plDartFace v Q hv z).val ⊆ (B.plDartFace vert P hvert x).val ∧
        (C.plDartFace v Q' hv z).val ⊆ (B.plDartFace vert P' hvert x).val) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨V, B, vert, Function.Embedding.refl _, Function.Embedding.refl _,
      P, P', hvert, hconn, rfl, fun _ => rfl, fun _ => rfl,
      fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl,
      fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
    · intro x _ z
      constructor
      · intro h
        exact ⟨z, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
    · intro z
      exact Or.inr ⟨z, by simp only [Finset.notMem_empty, false_implies, implies_true], rfl⟩
    · intro z
      exact ⟨z, Set.Subset.rfl, Set.Subset.rfl⟩
  | @insert a S ha ih =>
    obtain ⟨W, C, v, ι, σ, Q, Q', hv, hc, hr, hf, hvertex, hm, ht,
      hp, hp', he, he', hu, hx, hparent⟩ := ih
    obtain ⟨E, w, j, R, R', hw, hconnected, hroot, hflip, hvert,
      hmissing, htail, hpos, hpos', harc, harc', hunaffected, hex, hparent'⟩ :=
      C.exists_star_drawings_with_common_parents v Q Q' hv hc (ι a)
    let τ : V ↪ Option W :=
      ⟨fun x => some (σ x), fun _ _ heq => σ.injective (Option.some.inj heq)⟩
    have hcycles (x : B.D) (havoid : ∀ b ∈ S, ¬ B.map.faceSucc.SameCycle b x) :
        C.map.faceSucc.SameCycle (ι a) (ι x) ↔ B.map.faceSucc.SameCycle a x := by
      constructor
      · intro hh
        obtain ⟨y, hy, hyι⟩ := (hu x havoid (ι a)).mp hh.symm
        have hya : a = y := ι.injective hyι
        subst y
        exact hy.symm
      · intro hh
        exact ((hu x havoid (ι a)).mpr ⟨a, hh.symm, rfl⟩).symm
    refine ⟨Option W, E, w, ι.trans j, τ, R, R', hw, hconnected,
      hroot.trans (congrArg j hr), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      exact (hflip (ι x)).trans (congrArg j (hf x))
    · intro x
      exact (hvert (ι x)).trans (congrArg some (hvertex x))
    · intro x
      exact (hmissing (ι x)).trans (hm x)
    · intro x
      exact (htail (ι x)).trans (ht x)
    · intro x
      exact (hpos (σ x)).trans (hp x)
    · intro x
      exact (hpos' (σ x)).trans (hp' x)
    · intro x
      exact (harc (ι x)).trans (he x)
    · intro x
      exact (harc' (ι x)).trans (he' x)
    · intro x havoid z
      have hS : ∀ b ∈ S, ¬ B.map.faceSucc.SameCycle b x :=
        fun b hb => havoid b (Finset.mem_insert_of_mem hb)
      have hnot : ¬ C.map.faceSucc.SameCycle (ι a) (ι x) :=
        fun hh => havoid a (Finset.mem_insert_self a S) ((hcycles x hS).mp hh)
      constructor
      · intro hh
        obtain ⟨y, hy, hz⟩ := (hunaffected (ι x) hnot z).mp hh
        obtain ⟨b, hb, hyb⟩ := (hu x hS y).mp hy
        exact ⟨b, hb, hz.trans (congrArg j hyb)⟩
      · rintro ⟨y, hy, rfl⟩
        exact (hunaffected (ι x) hnot _).mpr
          ⟨ι y, (hu x hS _).mpr ⟨y, hy, rfl⟩, rfl⟩
    · intro z
      rcases hex z with hg | ⟨y, hy, rfl⟩
      · exact Or.inl hg
      · rcases hx y with hgood | ⟨x, havoid, rfl⟩
        · exact Or.inl ((drawing_period_of_orbit_embedding C.map.faceSucc
            E.map.faceSucc j y (hunaffected y hy)).trans hgood)
        · right
          refine ⟨x, ?_, rfl⟩
          intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact fun hh => hy ((hcycles x havoid).mpr hh)
          · exact havoid b hb
    · intro z
      obtain ⟨y, hy, hy'⟩ := hparent' z
      obtain ⟨x, hx, hx'⟩ := hparent y
      exact ⟨x, hy.trans hx, hy'.trans hx'⟩

/-- Helper toward Proposition 5.16: a jointly witnessed parent makes
containment in each original face independent of the choice of drawing.
Connectedness is used to recover the original orbit from its geometric face. -/
theorem drawing_common_parent_containment_iff
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (hparent : ∀ z, ∃ x,
      (C.plDartFace v Q hv z).val ⊆ (B.plDartFace vert P hvert x).val ∧
      (C.plDartFace v Q' hv z).val ⊆ (B.plDartFace vert P' hvert x).val)
    (a : B.D) (z : C.D) :
    (C.plDartFace v Q hv z).val ⊆ (B.plDartFace vert P hvert a).val ↔
      (C.plDartFace v Q' hv z).val ⊆ (B.plDartFace vert P' hvert a).val := by
  obtain ⟨x, hx, hx'⟩ := hparent z
  constructor
  · intro h
    obtain ⟨w, hw, hF⟩ := (C.plDartFace v Q hv z).property
    have hwF : w ∈ (C.plDartFace v Q hv z).val := hF ▸ mem_connectedComponentIn hw
    have heq := P.faces_eq_of_mem (hx hwF) (h hwF)
    have hcycle := B.plDartFace_sameCycle_of_eq vert P hvert hconn x a heq
    exact (congrArg Subtype.val (B.plDartFace_eq_of_sameCycle vert P' hvert
      x a hcycle)) ▸ hx'
  · intro h
    obtain ⟨w, hw, hF⟩ := (C.plDartFace v Q' hv z).property
    have hwF : w ∈ (C.plDartFace v Q' hv z).val := hF ▸ mem_connectedComponentIn hw
    have heq := P'.faces_eq_of_mem (hx' hwF) (h hwF)
    have hcycle := B.plDartFace_sameCycle_of_eq vert P' hvert hconn x a heq
    exact (congrArg Subtype.val (B.plDartFace_eq_of_sameCycle vert P hvert
      x a hcycle)) ▸ hx

/-- Helper toward Proposition 5.16: common parent darts give one common
orbit indexing set for both closed-face union identities. No choice of
parents in the two drawings is made independently. -/
theorem drawing_exists_common_closed_face_index
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (himage : P.image ⊆ Q.image) (himage' : P'.image ⊆ Q'.image)
    (hparent : ∀ z, ∃ x,
      (C.plDartFace v Q hv z).val ⊆ (B.plDartFace vert P hvert x).val ∧
      (C.plDartFace v Q' hv z).val ⊆ (B.plDartFace vert P' hvert x).val) :
    ∃ I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C),
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val) ∧
      (∀ O S, S ∈ I O ↔
        (C.plOrbitFace v Q' hv S).val ⊆ (B.plOrbitFace vert P' hvert O).val) ∧
      (∀ O, closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
      (∀ O, closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) := by
  let I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C) := fun O =>
    {S | (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val}
  have hiff (O : D39BallFaceCycleOrbit B) (S : D39BallFaceCycleOrbit C) :
      S ∈ I O ↔
        (C.plOrbitFace v Q' hv S).val ⊆ (B.plOrbitFace vert P' hvert O).val := by
    obtain ⟨a, ha⟩ := O.property
    obtain ⟨z, hz⟩ := S.property
    have haO : a ∈ O.val := ha.symm ▸ Equiv.Perm.SameCycle.rfl
    have hzS : z ∈ S.val := hz.symm ▸ Equiv.Perm.SameCycle.rfl
    change (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val ↔ _
    rw [C.plOrbitFace_eq_plDartFace_of_mem v Q hv S z hzS,
      C.plOrbitFace_eq_plDartFace_of_mem v Q' hv S z hzS,
      B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O a haO,
      B.plOrbitFace_eq_plDartFace_of_mem vert P' hvert O a haO]
    exact B.drawing_common_parent_containment_iff C vert v P P' Q Q'
      hvert hv hconn hparent a z
  refine ⟨I, fun _ _ => Iff.rfl, hiff, ?_, ?_⟩
  · intro O
    exact B.drawing_closed_orbit_face_eq_iUnion C vert v P Q hvert hv himage O
  · intro O
    rw [B.drawing_closed_orbit_face_eq_iUnion C vert v P' Q' hvert hv himage' O]
    simp_rw [← hiff O]

/-- Helper toward Proposition 5.16: triangulation away from one marked
orbit, retaining its geometric open face in both drawings, with one common
index for every original closed-face decomposition. The marked orbit is
not asserted to have a simple boundary or period four. -/
theorem exists_triangulated_drawings_away_from_orbit_with_common_index
    {V : Type u} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a : B.D) :
    ∃ (W : Type u) (C : D39FiniteBall) (v : C.D → W)
      (ι : B.D ↪ C.D) (σ : V ↪ W)
      (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
      (hv : Function.Surjective v)
      (I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C)),
      (∀ x y : C.D, Relation.EqvGen
        (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y) ∧
      C.rootDart = ι B.rootDart ∧
      (∀ x, C.map.edgeInv (ι x) = ι (B.map.edgeInv x)) ∧
      (∀ x, v (ι x) = σ (vert x)) ∧
      (∀ x, C.missing (ι x) ↔ B.missing x) ∧
      (∀ x, C.tail (ι x) ↔ B.tail x) ∧
      (∀ x, Q.pos (σ x) = P.pos x) ∧
      (∀ x, Q'.pos (σ x) = P'.pos x) ∧
      (∀ x, Q.arc (ι x) = P.arc x) ∧
      (∀ x, Q'.arc (ι x) = P'.arc x) ∧
      (∀ z, C.map.faceSucc.SameCycle (ι a) z ↔
        ∃ y, B.map.faceSucc.SameCycle a y ∧ z = ι y) ∧
      (∀ z, ¬ C.map.faceSucc.SameCycle (ι a) z →
        Function.minimalPeriod C.map.faceSucc z = 3 ∧
        Set.InjOn (fun n : ℕ => v ((C.map.faceSucc : C.D → C.D)^[n] z))
          (Set.Iio 3)) ∧
      (C.plDartFace v Q hv (ι a)).val = (B.plDartFace vert P hvert a).val ∧
      (C.plDartFace v Q' hv (ι a)).val = (B.plDartFace vert P' hvert a).val ∧
      (∀ O, closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
      (∀ O, closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) := by
  classical
  let S := Finset.univ.filter (fun d => ¬ B.map.faceSucc.SameCycle a d)
  have havoid (x : B.D) :
      (∀ b ∈ S, ¬ B.map.faceSucc.SameCycle b x) ↔ B.map.faceSucc.SameCycle a x := by
    constructor
    · intro h
      by_contra hn
      exact h x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hn⟩) Equiv.Perm.SameCycle.rfl
    · intro h b hb hh
      exact (Finset.mem_filter.mp hb).2 (h.trans hh.symm)
  obtain ⟨W, C, v, ι, σ, Q, Q', hv, hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', hu, hx, hparent⟩ :=
    B.exists_iterated_star_drawings_with_common_parents vert P P' hvert hconn S
  have horbit := hu a ((havoid a).mpr Equiv.Perm.SameCycle.rfl)
  have himage : P.image ⊆ Q.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hp x⟩
    · exact Or.inr ⟨ι d, he d ▸ hd⟩
  have himage' : P'.image ⊆ Q'.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hp' x⟩
    · exact Or.inr ⟨ι d, he' d ▸ hd⟩
  obtain ⟨I, _, _, hcover, hcover'⟩ :=
    B.drawing_exists_common_closed_face_index C vert v P P' Q Q' hvert hv hconn
      himage himage' hparent
  refine ⟨W, C, v, ι, σ, Q, Q', hv, I, hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', horbit, ?_,
    B.drawing_unchanged_orbit_face_eq C vert v P Q hvert hv hc ι himage he a horbit,
    B.drawing_unchanged_orbit_face_eq C vert v P' Q' hvert hv hc ι himage' he' a horbit,
    hcover, hcover'⟩
  intro z hz
  have hperiod : Function.minimalPeriod C.map.faceSucc z = 3 := by
    rcases hx z with hg | ⟨x, hS, rfl⟩
    · exact hg
    · exact (hz ((horbit _).mpr ⟨x, (havoid x).mp hS, rfl⟩)).elim
  exact ⟨hperiod, C.drawing_triangle_initialVertices v Q z hperiod⟩

/-! ## Construction attempts and remaining obligations

Three routes were examined before recording the following open targets.

1. Enclosing square plus far pendant. Combining `exists_common_exterior_square`
   and `exists_common_far_exterior_pendant` does not give disjoint frame edges:
   the pendant may cross the square before reaching its endpoint. The existing
   first-contact segment lemma is not a first-contact lemma for that polyline
   and does not identify corresponding square corner slots in both drawings.
   No frame darts were inserted here.
2. Exterior star. `exists_star_drawings` labels the triangles, but its vertex
   image formula does not locate infinity among them. The inspected
   `exists_chord_arc_in_face` only places the chord interior in the old face;
   when that face is unbounded, this does not specify which split face remains
   unbounded. A far centre alone gives no bound on the new spoke polylines.
   Thus the proposed common unbounded triangle is not proved here.
3. Common parent recursion. This route is implemented above: every child gets
   one parent dart simultaneously for both drawings, and containment composes
   through recursion. It gives the common closed-face index without requiring
   any surviving original dart on a child's boundary. It cannot distinguish
   several children having the same original exterior parent. Consequently it
   does not supply the missing exterior-star marker from route 2.

The finite carrier is deliberately existential in the proved construction.

### Remaining exterior-star construction (full binders)

This relaxed construction, with triangular exterior and existential carrier,
would suffice for the existing augmentation restriction theorem. The new
result above supplies common indexing for the iteration away from the marked
orbit, but not a common exterior child when that last orbit is starred.

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

### Remaining DU1 exactly as recorded in DrawingUniqueness2 (full binders)

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
