/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness
public import DirectedDistances.PlanarMap.D39PLExistsImageHomeomorph2
public import DirectedDistances.PlanarMap.D39PLStarFace2

/-! # Finite iteration of face subdivisions

the sole coordinator. These constructions do not assert completion of DU1. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: the period of a finite permutation orbit
is its cardinality, including singleton orbits. -/
theorem drawing_sameCycle_card {α : Type*} [Fintype α]
    (f : Equiv.Perm α) (x : α) :
    Nat.card {y // f.SameCycle x y} = Function.minimalPeriod f x := by
  classical
  let g : Fin (Function.minimalPeriod f x) → {y // f.SameCycle x y} :=
    fun i => ⟨(f : α → α)^[i.val] x,
      (show f.SameCycle x ((f ^ i.val) x) from Equiv.Perm.SameCycle.rfl.pow_right)⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j hij
      apply Fin.ext
      exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        i.isLt j.isLt).mp (congrArg Subtype.val hij)
    · intro y
      obtain ⟨n, hn⟩ := y.property.exists_nat_pow_eq
      have hp : 0 < Function.minimalPeriod f x :=
        Function.minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts x)
      refine ⟨⟨n % Function.minimalPeriod f x, Nat.mod_lt _ hp⟩, ?_⟩
      apply Subtype.ext
      change (f : α → α)^[n % Function.minimalPeriod f x] x = y.val
      rw [Function.iterate_mod_minimalPeriod_eq]
      exact hn
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (Equiv.ofBijective g hg)).symm.trans (Fintype.card_fin _)

/-- Helper toward Proposition 5.16: an exact inclusion-image description of
an unaffected orbit preserves its period, without an assumed successor formula. -/
theorem drawing_period_of_orbit_embedding {α β : Type*} [Fintype α] [Fintype β]
    (f : Equiv.Perm α) (g : Equiv.Perm β) (ι : α ↪ β) (x : α)
    (h : ∀ z, g.SameCycle (ι x) z ↔ ∃ y, f.SameCycle x y ∧ z = ι y) :
    Function.minimalPeriod g (ι x) = Function.minimalPeriod f x := by
  classical
  let j : {y // f.SameCycle x y} → {z // g.SameCycle (ι x) z} :=
    fun y => ⟨ι y.val, (h _).mpr ⟨y.val, y.property, rfl⟩⟩
  have hj : Function.Bijective j := by
    constructor
    · intro a b he
      exact Subtype.ext (ι.injective (congrArg Subtype.val he))
    · intro z
      obtain ⟨y, hy, he⟩ := (h z.val).mp z.property
      exact ⟨⟨y, hy⟩, Subtype.ext he.symm⟩
  rw [← drawing_sameCycle_card g (ι x), ← drawing_sameCycle_card f x]
  exact (Nat.card_congr (Equiv.ofBijective j hj)).symm

/-- Helper toward Proposition 5.16: all representatives of one face orbit
have the same period. -/
theorem drawing_period_of_sameCycle {α : Type*} [Fintype α]
    (f : Equiv.Perm α) {x y : α} (h : f.SameCycle x y) :
    Function.minimalPeriod f y = Function.minimalPeriod f x := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have he : (f : α → α)^[n] x = y := hn
  rw [← he]
  exact Function.minimalPeriod_apply_iterate (f.injective.mem_periodicPts x) n

/-- Helper toward Proposition 5.16: a drawing has no singleton face walk,
since successive initial vertices are distinct. -/
theorem drawing_face_period_ge_two {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) : 2 ≤ Function.minimalPeriod B.map.faceSucc d := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts
    (B.map.faceSucc.injective.mem_periodicPts d)
  have hne : Function.minimalPeriod B.map.faceSucc d ≠ 1 := by
    intro he
    have hr := Function.iterate_minimalPeriod (f := (B.map.faceSucc : B.D → B.D)) (x := d)
    rw [he, Function.iterate_one] at hr
    exact B.star_vert_ne_faceSucc vert P d (congrArg vert hr.symm)
  omega

/-- Helper toward Proposition 5.16: every triangular face of a drawing has
three distinct initial vertices; the closing edge supplies the last inequality. -/
theorem drawing_triangle_initialVertices {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (hp : Function.minimalPeriod B.map.faceSucc d = 3) :
    Set.InjOn (fun n : ℕ => vert ((B.map.faceSucc : B.D → B.D)^[n] d))
      (Set.Iio 3) := by
  apply B.star_three_vertices_inj vert P d
  have hne := B.star_vert_ne_faceSucc vert P
    ((B.map.faceSucc : B.D → B.D)^[2] d)
  have hr := Function.iterate_minimalPeriod (f := (B.map.faceSucc : B.D → B.D)) (x := d)
  rw [hp] at hr
  have he : B.map.faceSucc ((B.map.faceSucc : B.D → B.D)^[2] d) = d := hr
  rw [he] at hne
  exact Ne.symm hne

/-- Helper toward Proposition 5.16: finite star iteration. Every unresolved
original orbit is retained as an exact inclusion image; every other augmented
orbit is triangular. A selected dart may already belong to a processed orbit.
All original root, reversal, tags, vertices and polylines persist in both drawings.
No exterior-face or closed-face-cover assertion is included. -/
theorem exists_iterated_star_drawings
    {V : Type u} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (S : Finset B.D) :
    ∃ (W : Type u) (C : D39FiniteBall) (v : C.D → W)
      (ι : B.D ↪ C.D) (σ : V ↪ W)
      (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v),
      Function.Surjective v ∧
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
        ∃ x, (∀ a ∈ S, ¬ B.map.faceSucc.SameCycle a x) ∧ z = ι x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨V, B, vert, Function.Embedding.refl _, Function.Embedding.refl _,
      P, P', hvert, hconn, rfl, fun _ => rfl, fun _ => rfl,
      fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl,
      fun _ => rfl, fun _ => rfl, ?_, ?_⟩
    · intro x _ z
      constructor
      · intro h
        exact ⟨z, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
    · intro z
      exact Or.inr ⟨z, by simp only [Finset.notMem_empty, false_implies, implies_true], rfl⟩
  | @insert a S ha ih =>
    obtain ⟨W, C, v, ι, σ, Q, Q', hv, hc, hr, hf, hvertex, hm, ht,
      hp, hp', he, he', hu, hx⟩ := ih
    let k := Function.minimalPeriod C.map.faceSucc (ι a)
    obtain ⟨E, w, j, R, R', s, hw, hconnected, _, hroot, hflip, hvert,
      hmissing, htail, _, hpos, hpos', harc, harc', _, _, htri, _, _, _,
      hunaffected, hexhaustive⟩ := C.exists_star_drawings v Q Q' hv hc (ι a) k
        (C.drawing_face_period_ge_two v Q (ι a)) rfl
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
      hroot.trans (congrArg j hr), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      rcases hexhaustive z with ⟨i, hi⟩ | ⟨y, hy, rfl⟩
      · exact Or.inl ((drawing_period_of_sameCycle E.map.faceSucc hi).trans (htri i))
      · rcases hx y with hgood | ⟨x, havoid, rfl⟩
        · exact Or.inl ((drawing_period_of_orbit_embedding C.map.faceSucc
            E.map.faceSucc j y (hunaffected y hy)).trans hgood)
        · right
          refine ⟨x, ?_, rfl⟩
          intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact fun hh => hy ((hcycles x havoid).mpr hh)
          · exact havoid b hb

/-- Helper toward Proposition 5.16: starring a finite set meeting every
original face orbit leaves only triangular, vertex-simple augmented orbits.
In particular, taking all original darts gives such a subdivision. The outer
orbit is not marked or matched between the two augmented drawings. -/
theorem exists_triangulated_drawings
    {V : Type u} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y) :
    ∃ (W : Type u) (C : D39FiniteBall) (v : C.D → W)
      (ι : B.D ↪ C.D) (σ : V ↪ W)
      (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v),
      Function.Surjective v ∧
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
      P.image ⊆ Q.image ∧ P'.image ⊆ Q'.image ∧
      (∀ d, Function.minimalPeriod C.map.faceSucc d = 3 ∧
        Set.InjOn (fun n : ℕ => v ((C.map.faceSucc : C.D → C.D)^[n] d))
          (Set.Iio 3)) ∧
      Nonempty (C.PLImageHomeomorph v Q Q') := by
  classical
  obtain ⟨W, C, v, ι, σ, Q, Q', hv, hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', _, hx⟩ :=
    B.exists_iterated_star_drawings vert P P' hvert hconn Finset.univ
  have hperiod (d : C.D) : Function.minimalPeriod C.map.faceSucc d = 3 := by
    rcases hx d with hgood | ⟨x, havoid, _⟩
    · exact hgood
    · exact (havoid x (Finset.mem_univ x) Equiv.Perm.SameCycle.rfl).elim
  have : Finite W := Finite.of_surjective v hv
  refine ⟨W, C, v, ι, σ, Q, Q', hv, hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', ?_, ?_, ?_, C.exists_plImageHomeomorph v Q Q'⟩
  · rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hp x⟩
    · exact Or.inr ⟨ι d, he d ▸ hd⟩
  · rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hp' x⟩
    · exact Or.inr ⟨ι d, he' d ▸ hd⟩
  · intro d
    exact ⟨hperiod d, C.drawing_triangle_initialVertices v Q d (hperiod d)⟩

/-- Helper toward Proposition 5.16: every face of a larger drawing lies
in exactly one face of the original drawing. Boundaries may meet several
original face closures, so uniqueness is asserted for open faces. -/
theorem drawing_face_unique_parent
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (himage : P.image ⊆ Q.image) (G : Q.Face) :
    ∃! F : P.Face, G.val ⊆ F.val := by
  obtain ⟨z, hz, hG⟩ := G.property
  have hzP : z ∉ P.image := fun h => hz (himage h)
  let F : P.Face := ⟨connectedComponentIn P.imageᶜ z, z, hzP, rfl⟩
  have hzG : z ∈ G.val := hG ▸ mem_connectedComponentIn hz
  refine ⟨F, ?_, ?_⟩
  · rw [hG]
    exact connectedComponentIn_mono z (Set.compl_subset_compl.mpr himage)
  · intro F' hF'
    exact P.faces_eq_of_mem (hF' hzG) (mem_connectedComponentIn hzP)

/-- Helper toward Proposition 5.16: every original closed face is the
union of the augmented closed faces whose open faces lie inside it. This
proves the geometric union identity for each drawing separately; matching
the two geometric indexing sets combinatorially is an additional obligation. -/
theorem drawing_closed_face_eq_iUnion
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (himage : P.image ⊆ Q.image) (F : P.Face) :
    closure F.val = ⋃ G : Q.Face, ⋃ (_ : G.val ⊆ F.val), closure G.val := by
  classical
  have : Finite Q.Face := Finite.of_surjective
    (C.plDartFace v Q hv) (C.plDartFace_surjective v Q hv)
  let A := {G : Q.Face // G.val ⊆ F.val}
  have hcover : F.val ∩ Q.imageᶜ = ⋃ G : A, G.val.val := by
    ext z
    constructor
    · rintro ⟨hzF, hzQ⟩
      obtain ⟨G, hzG⟩ := (Q.faces_cover_compl z).mpr hzQ
      obtain ⟨F', hsub, _⟩ := B.drawing_face_unique_parent C vert v P Q himage G
      have he : F' = F := P.faces_eq_of_mem (hsub hzG) hzF
      exact mem_iUnion.mpr ⟨⟨G, he ▸ hsub⟩, hzG⟩
    · intro hz
      obtain ⟨G, hzG⟩ := mem_iUnion.mp hz
      exact ⟨G.property hzG, Q.face_subset_compl G.val hzG⟩
  have hcl : closure F.val = closure (F.val ∩ Q.imageᶜ) := by
    apply Subset.antisymm
    · apply closure_minimal _ isClosed_closure
      intro z hz
      apply mem_closure_iff.mpr
      intro U hU hzU
      obtain ⟨y, ⟨hyU, hyF⟩, hyQ⟩ := (C.dense_compl_plImage v Q hv).inter_open_nonempty
        (U ∩ F.val) (hU.inter (P.face_open_frontier_subset_image hvert F).1)
        ⟨z, hzU, hz⟩
      exact ⟨y, hyU, hyF, hyQ⟩
    · exact closure_mono inter_subset_left
  rw [hcl, hcover, closure_iUnion_of_finite]
  ext z
  simp only [A, mem_iUnion, Subtype.exists, exists_prop]

/-- Helper toward Proposition 5.16: the geometric closed-face union
identity with augmented face orbits as indices, in the form used by the
restriction theorem. Its indexing predicate still refers to this drawing. -/
theorem drawing_closed_orbit_face_eq_iUnion
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (himage : P.image ⊆ Q.image) (O : D39BallFaceCycleOrbit B) :
    closure (B.plOrbitFace vert P hvert O).val =
      ⋃ S : D39BallFaceCycleOrbit C,
        ⋃ (_ : (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val),
          closure (C.plOrbitFace v Q hv S).val := by
  rw [B.drawing_closed_face_eq_iUnion C vert v P Q hvert hv himage]
  ext z
  constructor
  · intro hz
    obtain ⟨G, hzG⟩ := mem_iUnion.mp hz
    obtain ⟨hG, hzG⟩ := mem_iUnion.mp hzG
    obtain ⟨S, hS⟩ := C.plOrbitFace_surjective v Q hv G
    exact mem_iUnion.mpr ⟨S, mem_iUnion.mpr ⟨hS.symm ▸ hG, hS.symm ▸ hzG⟩⟩
  · intro hz
    obtain ⟨S, hzS⟩ := mem_iUnion.mp hz
    obtain ⟨hS, hzS⟩ := mem_iUnion.mp hzS
    exact mem_iUnion.mpr ⟨C.plOrbitFace v Q hv S, mem_iUnion.mpr ⟨hS, hzS⟩⟩

/-- Helper toward Proposition 5.16: augmented face orbits have unique
original parent orbits when the original drawing is connected. -/
theorem drawing_orbit_unique_parent
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (himage : P.image ⊆ Q.image) (S : D39BallFaceCycleOrbit C) :
    ∃! O : D39BallFaceCycleOrbit B,
      (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val := by
  obtain ⟨F, hF, huniq⟩ :=
    B.drawing_face_unique_parent C vert v P Q himage (C.plOrbitFace v Q hv S)
  obtain ⟨O, hO⟩ := B.plOrbitFace_surjective vert P hvert F
  refine ⟨O, ?_, ?_⟩
  · intro z hz
    exact (congrArg (fun G : P.Face => z ∈ G.val) hO).mpr (hF hz)
  · intro O' hO'
    apply B.plOrbitFace_injective vert P hvert hconn
    exact (huniq _ hO').trans hO.symm

/-- Helper toward Proposition 5.16: the augmented face to the left of an
unchanged original dart lies inside that dart's original left face. The proof
uses a common small left wedge, so it preserves the plane orientation. -/
theorem drawing_inherited_dart_face_subset
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (himage : P.image ⊆ Q.image) (d : B.D) (e : C.D)
    (harc : Q.arc e = P.arc d) :
    (C.plDartFace v Q hv e).val ⊆ (B.plDartFace vert P hvert d).val := by
  let F := B.plDartFace vert P hvert d
  let G := C.plDartFace v Q hv e
  obtain ⟨H, hH, _⟩ := B.drawing_face_unique_parent C vert v P Q himage G
  obtain ⟨δ, hδ, hleft⟩ := (B.plDartFace_eq_iff vert P hvert d F).mp rfl
  obtain ⟨η, hη, hleft'⟩ := (C.plDartFace_eq_iff v Q hv e G).mp rfl
  let t := min δ η / 2
  have ht : 0 < t := half_pos (lt_min hδ hη)
  have htδ : t < δ := (half_lt_self (lt_min hδ hη)).trans_le (min_le_left _ _)
  have htη : t < η := (half_lt_self (lt_min hδ hη)).trans_le (min_le_right _ _)
  have hzF := hleft t t ht htδ ht htδ
  have hzG := hleft' t t ht htη ht htη
  rw [harc] at hzG
  have he : H = F := P.faces_eq_of_mem (hH hzG) hzF
  exact fun z hz => (congrArg (fun J : P.Face => z ∈ J.val) he).mp (hH hz)

/-- Helper toward Proposition 5.16: an augmented orbit containing an
inherited dart lies in the original orbit face containing that dart. -/
theorem drawing_inherited_orbit_face_subset
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (himage : P.image ⊆ Q.image) (O : D39BallFaceCycleOrbit B)
    (S : D39BallFaceCycleOrbit C) (d : B.D) (e : C.D)
    (hd : d ∈ O.val) (he : e ∈ S.val) (harc : Q.arc e = P.arc d) :
    (C.plOrbitFace v Q hv S).val ⊆ (B.plOrbitFace vert P hvert O).val := by
  calc
    (C.plOrbitFace v Q hv S).val = (C.plDartFace v Q hv e).val :=
      congrArg Subtype.val (C.plOrbitFace_eq_plDartFace_of_mem v Q hv S e he)
    _ ⊆ (B.plDartFace vert P hvert d).val :=
      B.drawing_inherited_dart_face_subset C vert v P Q hvert hv himage d e harc
    _ = (B.plOrbitFace vert P hvert O).val :=
      (congrArg Subtype.val (B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O d hd)).symm

/-- Helper toward Proposition 5.16: retaining an entire original face orbit
as an exact inclusion image retains its geometric open face. The absence of
new boundary darts makes the augmented face relatively closed in its parent. -/
theorem drawing_unchanged_orbit_face_eq
    {V W : Type*} (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hc : ∀ x y : C.D, Relation.EqvGen
      (fun z w => C.map.rot z = w ∨ C.map.edgeInv z = w) x y)
    (ι : B.D ↪ C.D) (himage : P.image ⊆ Q.image)
    (harc : ∀ d, Q.arc (ι d) = P.arc d) (a : B.D)
    (horbit : ∀ z, C.map.faceSucc.SameCycle (ι a) z ↔
      ∃ y, B.map.faceSucc.SameCycle a y ∧ z = ι y) :
    (C.plDartFace v Q hv (ι a)).val = (B.plDartFace vert P hvert a).val := by
  let F := B.plDartFace vert P hvert a
  let G := C.plDartFace v Q hv (ι a)
  have hsub : G.val ⊆ F.val :=
    B.drawing_inherited_dart_face_subset C vert v P Q hvert hv himage a (ι a) (harc a)
  have hfront : frontier G.val ⊆ P.image := by
    rw [Q.frontier_face_eq_iUnion_dartBorders_arcs hv G]
    intro z hz
    obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
    have hsame : C.map.faceSucc.SameCycle (ι a) e :=
      C.plDartFace_sameCycle_of_eq v Q hv hc _ _
        ((C.plDartFace_eq_iff v Q hv e G).mpr he).symm
    obtain ⟨d, _, hed⟩ := (horbit e).mp hsame
    rw [hed, harc d] at hze
    exact Or.inr ⟨d, hze⟩
  have hpre : IsPreconnected F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF]
    exact isPreconnected_connectedComponentIn
  have hnonempty : (F.val ∩ G.val).Nonempty := by
    obtain ⟨z, hz, hG⟩ := G.property
    have hzG : z ∈ G.val := hG ▸ mem_connectedComponentIn hz
    exact ⟨z, hsub hzG, hzG⟩
  apply Subset.antisymm hsub
  apply hpre.subset_of_closure_inter_subset (Q.face_open_frontier_subset_image hv G).1 hnonempty
  rintro z ⟨hzcl, hzF⟩
  by_contra hzG
  have hzfront : z ∈ frontier G.val := by
    rw [frontier, (Q.face_open_frontier_subset_image hv G).1.interior_eq]
    exact ⟨hzcl, hzG⟩
  exact P.face_subset_compl F hzF (hfront hzfront)

/-- Helper toward Proposition 5.16: finite star recursion can leave any
one marked orbit untouched. Its open face is retained in both drawings and
every other augmented orbit is triangular. This supplies the bounded-orbit
iteration after a frame has made the marked exterior orbit vertex-simple. -/
theorem exists_triangulated_drawings_away_from_orbit
    {V : Type u} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y) (a : B.D) :
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
      (∀ z, C.map.faceSucc.SameCycle (ι a) z ↔
        ∃ y, B.map.faceSucc.SameCycle a y ∧ z = ι y) ∧
      (∀ z, ¬ C.map.faceSucc.SameCycle (ι a) z →
        Function.minimalPeriod C.map.faceSucc z = 3 ∧
        Set.InjOn (fun n : ℕ => v ((C.map.faceSucc : C.D → C.D)^[n] z))
          (Set.Iio 3)) ∧
      (C.plDartFace v Q hv (ι a)).val = (B.plDartFace vert P hvert a).val ∧
      (C.plDartFace v Q' hv (ι a)).val = (B.plDartFace vert P' hvert a).val := by
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
    hp, hp', he, he', hu, hx⟩ :=
    B.exists_iterated_star_drawings vert P P' hvert hconn S
  have horbit := hu a ((havoid a).mpr Equiv.Perm.SameCycle.rfl)
  have himage : P.image ⊆ Q.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hp x⟩
    · exact Or.inr ⟨ι d, he d ▸ hd⟩
  have himage' : P'.image ⊆ Q'.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨σ x, hp' x⟩
    · exact Or.inr ⟨ι d, he' d ▸ hd⟩
  refine ⟨W, C, v, ι, σ, Q, Q', hv, hc, hr, hf, hvertex, hm, ht,
    hp, hp', he, he', horbit, ?_,
    B.drawing_unchanged_orbit_face_eq C vert v P Q hvert hv hc ι himage he a horbit,
    B.drawing_unchanged_orbit_face_eq C vert v P' Q' hvert hv hc ι himage' he' a horbit⟩
  intro z hz
  have hperiod : Function.minimalPeriod C.map.faceSucc z = 3 := by
    rcases hx z with hg | ⟨x, hS, rfl⟩
    · exact hg
    · exact (hz ((horbit _).mpr ⟨x, (havoid x).mp hS, rfl⟩)).elim
  exact ⟨hperiod, C.drawing_triangle_initialVertices v Q z hperiod⟩

/-- Helper toward Proposition 5.16: the first frame pendant can end at one
common point arbitrarily far to the right in both marked exterior faces.
All original positions and arcs persist, and every other face orbit remains
its exact old-dart inclusion image with unchanged period. This does not yet
construct the closing square edges. -/
theorem exists_common_far_exterior_pendant
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (a : B.D) (ha : a ∈ O_ext.val) (T : ℝ) :
    ∃ (c : ℂ) (Q Q' : PLDrawing (B.insertPendant a).D (Option V)
        (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot
        (B.pendantVert vert a)),
      T < c.re ∧ c.im = 0 ∧
      (∀ x, Q.pos (some x) = P.pos x) ∧
      (∀ x, Q'.pos (some x) = P'.pos x) ∧
      Q.pos none = c ∧ Q'.pos none = c ∧
      (∀ d, Q.arc (.inl d) = P.arc d) ∧
      (∀ d, Q'.arc (.inl d) = P'.arc d) ∧
      Function.minimalPeriod (B.insertPendant a).map.faceSucc (.inr false) =
        Function.minimalPeriod B.map.faceSucc a + 2 ∧
      (∀ x, ¬ B.map.faceSucc.SameCycle a x →
        (∀ z, (B.insertPendant a).map.faceSucc.SameCycle (.inl x) z ↔
          ∃ y, B.map.faceSucc.SameCycle x y ∧ z = .inl y) ∧
        Function.minimalPeriod (B.insertPendant a).map.faceSucc (.inl x) =
          Function.minimalPeriod B.map.faceSucc x) := by
  obtain ⟨r, _, hout, _⟩ := P.exists_closedBall_containing_other_faces
    (B.plOrbitFace vert P hvert O_ext) hext.1
  obtain ⟨r', _, hout', _⟩ := P'.exists_closedBall_containing_other_faces
    (B.plOrbitFace vert P' hvert O_ext) hext.2
  let R : ℝ := max (max r r') (max T 0) + 1
  have hR : 0 < R := by
    have h := (le_max_right T 0).trans (le_max_right (max r r') (max T 0))
    dsimp [R]
    linarith
  have hr : r < R := by
    have h := (le_max_left r r').trans (le_max_left (max r r') (max T 0))
    dsimp [R]
    linarith
  have hr' : r' < R := by
    have h := (le_max_right r r').trans (le_max_left (max r r') (max T 0))
    dsimp [R]
    linarith
  have hT : T < R := by
    have h := (le_max_left T 0).trans (le_max_right (max r r') (max T 0))
    dsimp [R]
    linarith
  have hnorm : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hc : (R : ℂ) ∈ (B.plDartFace vert P hvert a).val := by
    rw [← B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O_ext a ha]
    apply hout
    simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      hnorm, not_le] using hr
  have hc' : (R : ℂ) ∈ (B.plDartFace vert P' hvert a).val := by
    rw [← B.plOrbitFace_eq_plDartFace_of_mem vert P' hvert O_ext a ha]
    apply hout'
    simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      hnorm, not_le] using hr'
  obtain ⟨Q, Q', hp, hp', hq, hq', he, he'⟩ :=
    B.exists_star_pendant_drawings vert P P' hvert a R R hc hc'
  exact ⟨R, Q, Q', hT, rfl, hp, hp', hq, hq', he, he',
    B.star_pendant_face_period a, fun x hx => B.star_pendant_orbit_unaffected a x hx⟩

/-- Helper toward Proposition 5.16: a pendant inserted at an exterior
corner keeps its residual orbit exterior. Every possible unbounded face
outside that orbit would lie in a bounded original face. -/
theorem drawing_pendant_residual_exterior
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ x y : B.D, Relation.EqvGen
      (fun z w => B.map.rot z = w ∨ B.map.edgeInv z = w) x y)
    (a : B.D) (haext : ¬ Bornology.IsBounded (B.plDartFace vert P hvert a).val)
    (Q : PLDrawing (B.insertPendant a).D (Option V)
      (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot
      (B.pendantVert vert a))
    (hpos : ∀ x, Q.pos (some x) = P.pos x)
    (harc : ∀ d, Q.arc (.inl d) = P.arc d) :
    ¬ Bornology.IsBounded
      ((B.insertPendant a).plDartFace (B.pendantVert vert a) Q
        (B.pendantVert_surjective vert a hvert) (.inr false)).val := by
  let C := B.insertPendant a
  let v := B.pendantVert vert a
  have hv : Function.Surjective v := B.pendantVert_surjective vert a hvert
  have himage : P.image ⊆ Q.image := by
    rintro z (⟨x, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨some x, hpos x⟩
    · exact Or.inr ⟨.inl d, harc d ▸ hd⟩
  obtain ⟨U, hU, _⟩ := Q.existsUnique_not_isBounded_face
  obtain ⟨e, he⟩ := C.plDartFace_surjective v Q hv U
  have hres : C.plDartFace v Q hv (.inr false) = U := by
    cases e with
    | inl x =>
      by_cases hx : B.map.faceSucc.SameCycle a x
      · exact (C.plDartFace_eq_of_sameCycle v Q hv _ _
          ((B.star_pendant_sameCycle_inl a x).mpr hx)).trans he
      · have hne : B.plDartFace vert P hvert x ≠ B.plDartFace vert P hvert a := by
          intro hh
          exact hx (B.plDartFace_sameCycle_of_eq vert P hvert hconn x a hh).symm
        have hbounded := P.isBounded_face_of_ne_unbounded
          (B.plDartFace vert P hvert a) haext (B.plDartFace vert P hvert x) hne
        have hsub := B.drawing_inherited_dart_face_subset C vert v P Q hvert hv
          himage x (.inl x) (harc x)
        have hb : Bornology.IsBounded (C.plDartFace v Q hv (.inl x)).val :=
          hbounded.subset hsub
        exact (hU ((congrArg (fun F : Q.Face => Bornology.IsBounded F.val) he).mp hb)).elim
    | inr b =>
      cases b with
      | false => exact he
      | true =>
        have hstep := C.plDartFace_faceSucc v Q hv (.inr true)
        exact hstep.trans he
  exact fun hb => hU
    ((congrArg (fun F : Q.Face => Bornology.IsBounded F.val) hres).mp hb)








































































end D39FiniteBall
end DirectedDistances.PlanarMap
end
