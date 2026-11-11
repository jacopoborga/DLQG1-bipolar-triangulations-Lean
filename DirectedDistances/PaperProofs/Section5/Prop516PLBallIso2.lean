/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso
public import DirectedDistances.PaperProofs.Section5.Prop516GeomBallIsoPackaging2
public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness

/-! # Further PL ball comparison helpers -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

section

variable
    (hDU1 :
      ∀ {V : Type} [Finite V] (A : D39FiniteBall) (vert : A.D → V)
        (P P' : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
        (hvert : Function.Surjective vert)
        (_hconn : ∀ d e : A.D, Relation.EqvGen
          (fun x y => A.map.rot x = y ∨ A.map.edgeInv x = y) d e)
        (O_ext : D39BallFaceCycleOrbit A)
        (_hext : (¬ Bornology.IsBounded (A.plOrbitFace vert P hvert O_ext).val) ∧
          (¬ Bornology.IsBounded (A.plOrbitFace vert P' hvert O_ext).val)),
      ∃ (n : ℕ) (C : D39FiniteBall) (v : C.D → V ⊕ Fin n)
        (ι : A.D ↪ C.D)
        (Q Q' : PLDrawing C.D (V ⊕ Fin n) C.map.edgeInv C.map.rot v)
        (hv : Function.Surjective v) (E : D39BallFaceCycleOrbit C)
        (I : D39BallFaceCycleOrbit A → Set (D39BallFaceCycleOrbit C)),
        (∀ d e : C.D, Relation.EqvGen
          (fun x y => C.map.rot x = y ∨ C.map.edgeInv x = y) d e) ∧
        C.rootDart = ι A.rootDart ∧
        (∀ d : A.D, C.map.edgeInv (ι d) = ι (A.map.edgeInv d)) ∧
        (∀ d : A.D, v (ι d) = Sum.inl (vert d)) ∧
        (∀ d : A.D, C.missing (ι d) ↔ A.missing d) ∧
        (∀ d : A.D, C.tail (ι d) ↔ A.tail d) ∧
        (∀ x : V, Q.pos (Sum.inl x) = P.pos x) ∧
        (∀ x : V, Q'.pos (Sum.inl x) = P'.pos x) ∧
        (∀ d : A.D, Q.arc (ι d) = P.arc d) ∧
        (∀ d : A.D, Q'.arc (ι d) = P'.arc d) ∧
        (¬ Bornology.IsBounded (C.plOrbitFace v Q hv E).val) ∧
        (¬ Bornology.IsBounded (C.plOrbitFace v Q' hv E).val) ∧
        (∀ O : D39BallFaceCycleOrbit C, ∃ d ∈ O.val,
          (O = E → Function.minimalPeriod C.map.faceSucc d = 4) ∧
          (O ≠ E → Function.minimalPeriod C.map.faceSucc d = 3) ∧
          Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] d))
            (Set.Iio (Function.minimalPeriod C.map.faceSucc d))) ∧
        (∀ O : D39BallFaceCycleOrbit A,
          closure (A.plOrbitFace vert P hvert O).val =
            ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
        (∀ O : D39BallFaceCycleOrbit A,
          closure (A.plOrbitFace vert P' hvert O).val =
            ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val))

include hDU1 in
/- Helper toward Proposition 5.16: the general augmentation target DU1
implies finite drawing uniqueness, including monotone dart parametrizations. -/
theorem exists_plDrawing_homeomorph_of_augmentation
    {V : Type} [Finite V] (A : D39FiniteBall) (vert : A.D → V)
    (P P' : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : A.D, Relation.EqvGen
      (fun x y => A.map.rot x = y ∨ A.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit A)
    (hext : (¬ Bornology.IsBounded (A.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (A.plOrbitFace vert P' hvert O_ext).val)) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : V, H (P.pos x) = P'.pos x) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, H ((P.arc d).toPath t) = (P'.arc d).toPath (φ t)) ∧
      ∀ O : D39BallFaceCycleOrbit A,
        H '' (A.plOrbitFace vert P hvert O).val =
          (A.plOrbitFace vert P' hvert O).val := by
  obtain ⟨n, C, v, ι, Q, Q', hv, E, I, hc, _hr, _hf, _hv, _hm, _ht,
    hp, hp', ha, ha', he, he', hs, hcover, hcover'⟩ :=
    hDU1 A vert P P' hvert hconn O_ext hext
  have hsimple : ∀ O : D39BallFaceCycleOrbit C, ∃ d ∈ O.val,
      3 ≤ Function.minimalPeriod C.map.faceSucc d ∧
      Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] d))
        (Set.Iio (Function.minimalPeriod C.map.faceSucc d)) := by
    intro O
    obtain ⟨d, hd, hfour, hthree, hinj⟩ := hs O
    refine ⟨d, hd, ?_, hinj⟩
    by_cases hO : O = E
    · rw [hfour hO]; omega
    · rw [hthree hO]
  obtain ⟨H, hor, hpos, harc, _himage, _hclosed, hface⟩ :=
    A.exists_orientationPreserving_plane_homeomorph_of_augmentation C vert v
      P P' Q Q' hvert hv hc ι Sum.inl hp hp' ha ha' E ⟨he, he'⟩
      hsimple I hcover hcover'
  refine ⟨H, hor, hpos, ?_, hface⟩
  intro d
  have h0 : H (P.arc d).start = (P'.arc d).start := by
    rw [P.arc_start, P'.arc_start, hpos]
  have h1 : H (P.arc d).finish = (P'.arc d).finish := by
    rw [P.arc_finish, P'.arc_finish, hpos]
  obtain ⟨φ, hm, _ha, heq⟩ := exists_path_reparam_of_planeHomeomorph
    (P.arc d).toPath (P'.arc d).toPath
    ((P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d))
    ((P'.arc d).toPath_injective (P'.arc_length d) (P'.arc_simple d))
    H false h0 h1 (by simpa only [Polyline.range_toPath] using harc d)
  exact ⟨φ, hm rfl, heq⟩

/-- Helper toward Proposition 5.16: a representation with the stated PL
dart paths has no geometric loops, on present and missing edges alike. -/
theorem d39PLRepresentation_src_ne_tgt
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (e : B.E) :
    B.map.toPlaneMapWithMissing.src e ≠ B.map.toPlaneMapWithMissing.tgt e := by
  intro he
  let d := x.dartEquiv.symm (e, true)
  have hd : x.dartEquiv d = (e, true) := x.dartEquiv.apply_symm_apply _
  have hpath : (P.arc d).toPath 0 = (P.arc d).toPath 1 := by
    rw [harc, harc]
    simp only [d39DrawingDartArc, hd, ite_true, Path.source, Path.target, he]
  exact zero_ne_one ((P.arc d).toPath_injective
    (P.arc_length d) (P.arc_simple d) hpath)

/-- Helper toward Proposition 5.16: relabel both dart and vertex identities
of a PL drawing, retaining the actual positions and entire polylines. -/
@[expose] def plDrawingRelabel
    {D D' V V' : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}
    (e : D ≃ D') (f : V ≃ V')
    (hf : ∀ d, e (flip d) = flip' (e d))
    (hr : ∀ d, e (rot d) = rot' (e d))
    (hv : ∀ d, f (vert d) = vert' (e d))
    (P : PLDrawing D V flip rot vert) : PLDrawing D' V' flip' rot' vert' := by
  have hfs (d : D') : e.symm (flip' d) = flip (e.symm d) := by
    apply e.injective
    rw [e.apply_symm_apply, hf, e.apply_symm_apply]
  have hrs (d : D') : e.symm (rot' d) = rot (e.symm d) := by
    apply e.injective
    rw [e.apply_symm_apply, hr, e.apply_symm_apply]
  have hvs (d : D') : f.symm (vert' d) = vert (e.symm d) := by
    apply f.injective
    rw [f.apply_symm_apply, hv, e.apply_symm_apply]
  exact {
    flip_involutive := by
      intro d
      apply e.symm.injective
      rw [hfs, hfs, P.flip_involutive]
    flip_ne := by
      intro d hd
      apply P.flip_ne (e.symm d)
      rw [← hfs, hd]
    vert_rotation := by
      intro d
      apply f.symm.injective
      rw [hvs, hvs, hrs, P.vert_rotation]
    pos := fun v => P.pos (f.symm v)
    pos_injective := P.pos_injective.comp f.symm.injective
    arc := fun d => P.arc (e.symm d)
    arc_simple := fun d => P.arc_simple (e.symm d)
    arc_length := fun d => P.arc_length (e.symm d)
    arc_start := by intro d; rw [P.arc_start, hvs]
    arc_finish := by intro d; rw [P.arc_finish, hvs, hfs]
    arc_flip := by intro d; rw [hfs, P.arc_flip]
    interior_disjoint := by
      intro d k hne hflip
      apply P.interior_disjoint
      · exact fun h => hne (e.symm.injective h)
      · intro h
        apply hflip
        apply e.symm.injective
        rw [hfs, h]
    interior_avoids_vertices := fun d v =>
      P.interior_avoids_vertices (e.symm d) (f.symm v)
    locally_finite := by
      intro K hK
      have hset : {d | (K ∩ (P.arc (e.symm d)).image).Nonempty} =
          e '' {d | (K ∩ (P.arc d).image).Nonempty} := by
        ext d
        constructor
        · exact fun h => ⟨e.symm d, h, e.apply_symm_apply d⟩
        · rintro ⟨k, hk, rfl⟩
          change (K ∩ (P.arc (e.symm (e k))).image).Nonempty
          rw [e.symm_apply_apply]
          exact hk
      rw [hset]
      exact (P.locally_finite K hK).image e
    initial_nonzero := fun d => P.initial_nonzero (e.symm d)
    initial_arg_injective := by
      intro d k hd hk
      apply e.symm.injective
      apply P.initial_arg_injective _ _ _ hk
      rw [← hvs, ← hvs, hd]
    rotation_agreement := by
      intro d
      have hstar : e '' {k | vert k = vert (e.symm d)} =
          {k | vert' k = vert' d} := by
        ext k
        constructor
        · rintro ⟨j, hj, rfl⟩
          change vert' (e j) = vert' d
          rw [← hv, ← f.apply_symm_apply (vert' d), hvs, hj]
        · intro hk
          refine ⟨e.symm k, ?_, e.apply_symm_apply k⟩
          change vert (e.symm k) = vert (e.symm d)
          rw [← hvs, ← hvs, hk]
      have h := d39CcwSuccessor_map_equiv e (P.rotation_agreement (e.symm d))
      rw [hstar, e.apply_symm_apply, hr, e.apply_symm_apply] at h
      exact h }

/-- Helper toward Proposition 5.16: relabelling preserves the drawing image
as an exact point-set, including every vertex and missing geometric edge. -/
theorem plDrawingRelabel_image
    {D D' V V' : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}
    (e : D ≃ D') (f : V ≃ V')
    (hf : ∀ d, e (flip d) = flip' (e d))
    (hr : ∀ d, e (rot d) = rot' (e d))
    (hv : ∀ d, f (vert d) = vert' (e d))
    (P : PLDrawing D V flip rot vert) :
    (plDrawingRelabel e f hf hr hv P).image = P.image := by
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨f.symm v, rfl⟩
    · exact Or.inr ⟨e.symm d, hd⟩
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨f v, by change P.pos (f.symm (f v)) = P.pos v; rw [f.symm_apply_apply]⟩
    · exact Or.inr ⟨e d, by change _ ∈ (P.arc (e.symm (e d))).image; rwa [e.symm_apply_apply]⟩

/-- Helper toward Proposition 5.16: rotation-orbit vertices of a finite PL
drawing are precisely its incident vertices, with no extra identifications. -/
@[expose] def plDrawingVertexQuotientEquiv
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (hvert : Function.Surjective vert) :
    CombinatorialMap.VertexQuotient A.map ≃ V := by
  let f : CombinatorialMap.VertexQuotient A.map → V := Quotient.lift vert
    (fun d e h => P.vert_eq_of_rot_sameCycle d e h)
  apply Equiv.ofBijective f
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | _ d =>
      induction b using Quotient.inductionOn with
      | _ e =>
        intro h
        exact Quotient.sound (P.rot_sameCycle_of_vert_eq d e h)
  · intro v
    obtain ⟨d, rfl⟩ := hvert v
    exact ⟨Quotient.mk _ d, rfl⟩

/-- Helper toward Proposition 5.16: an isomorphism of finite balls induces
an equivalence of the vertex carriers of any two PL drawings. -/
@[expose] def plBallVertexEquiv
    {V W : Type*} {A B : D39FiniteBall} (I : D39BallIso A B)
    (vert : A.D → V) (vert' : B.D → W)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (Q : PLDrawing B.D W B.map.edgeInv B.map.rot vert')
    (hv : Function.Surjective vert) (hw : Function.Surjective vert') : V ≃ W :=
  (plDrawingVertexQuotientEquiv A vert P hv).symm.trans
    ((permCycleQuotientEquiv I.toEquiv A.map.rot B.map.rot I.rot_comm).trans
      (plDrawingVertexQuotientEquiv B vert' Q hw))

/-- Helper toward Proposition 5.16: the induced vertex equivalence commutes
with dart incidence, so it is suitable for relabelling the full PL drawing. -/
theorem plBallVertexEquiv_apply
    {V W : Type*} {A B : D39FiniteBall} (I : D39BallIso A B)
    (vert : A.D → V) (vert' : B.D → W)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (Q : PLDrawing B.D W B.map.edgeInv B.map.rot vert')
    (hv : Function.Surjective vert) (hw : Function.Surjective vert') (d : A.D) :
    plBallVertexEquiv I vert vert' P Q hv hw (vert d) = vert' (I.toEquiv d) := by
  have h : vert d = plDrawingVertexQuotientEquiv A vert P hv (Quotient.mk _ d) := rfl
  rw [h]
  change plDrawingVertexQuotientEquiv B vert' Q hw
    (permCycleQuotientEquiv I.toEquiv A.map.rot B.map.rot I.rot_comm
      ((plDrawingVertexQuotientEquiv A vert P hv).symm
        (plDrawingVertexQuotientEquiv A vert P hv (Quotient.mk _ d)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Helper toward Proposition 5.16: an isomorphism of faced balls preserves
and reflects the complete face-successor cycle relation. -/
theorem plBallFaceSameCycle_iff
    {A B : D39FiniteBall} (I : D39BallIso A B) (d e : A.D) :
    A.map.faceSucc.SameCycle d e ↔
      B.map.faceSucc.SameCycle (I.toEquiv d) (I.toEquiv e) := by
  constructor
  · exact rootedSameCycle_map I.toEquiv A.map.faceSucc B.map.faceSucc I.face_comm
  · intro h
    have h' := rootedSameCycle_map I.symm.toEquiv B.map.faceSucc A.map.faceSucc
      I.symm.face_comm h
    simpa only [D39BallIso.symm, Equiv.symm_apply_apply] using h'

/-- Helper toward Proposition 5.16: transport an actual face orbit as its
set of dart images, preserving orbit identity rather than just its cardinality. -/
@[expose] def plBallFaceOrbitMap
    {A B : D39FiniteBall} (I : D39BallIso A B) (O : D39BallFaceCycleOrbit A) :
    D39BallFaceCycleOrbit B := by
  refine ⟨I.toEquiv '' O.val, ?_⟩
  obtain ⟨d, hd⟩ := O.property
  refine ⟨I.toEquiv d, ?_⟩
  ext k
  constructor
  · rintro ⟨j, hj, rfl⟩
    apply (plBallFaceSameCycle_iff I d j).mp
    rw [hd] at hj
    exact hj
  · intro hk
    change B.map.faceSucc.SameCycle (I.toEquiv d) k at hk
    refine ⟨I.toEquiv.symm k, ?_, I.toEquiv.apply_symm_apply k⟩
    rw [hd]
    apply (plBallFaceSameCycle_iff I d (I.toEquiv.symm k)).mpr
    simpa only [I.toEquiv.apply_symm_apply] using hk

/-- Helper toward Proposition 5.16: transport of the selected exterior orbit
under an isomorphism preserving that marker is exact. -/
theorem plBallFaceOrbitMap_external
    {A B : D39FiniteBallWithExternal} (I : D39BallIsoWithExternal A B) :
    plBallFaceOrbitMap I.toD39BallIso A.externalOrbit = B.externalOrbit := by
  apply Subtype.ext
  ext d
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (I.external_iff e).mpr he
  · intro hd
    refine ⟨I.toD39BallIso.toEquiv.symm d, ?_,
      I.toD39BallIso.toEquiv.apply_symm_apply d⟩
    apply (I.external_iff _).mp
    simpa only [I.toD39BallIso.toEquiv.apply_symm_apply] using hd

/-- Helper toward Proposition 5.16: relabelled drawings give the same
geometric face to the transported face orbit, as an exact component set. -/
theorem plDrawingRelabel_orbitFace
    {V W : Type*} {A B : D39FiniteBall} (I : D39BallIso A B)
    (vert : A.D → V) (vert' : B.D → W)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (f : V ≃ W) (hv : ∀ d, f (vert d) = vert' (I.toEquiv d))
    (hvert : Function.Surjective vert) (hvert' : Function.Surjective vert')
    (O : D39BallFaceCycleOrbit A) :
    (B.plOrbitFace vert'
      (plDrawingRelabel I.toEquiv f I.edgeInv_comm I.rot_comm hv P) hvert'
      (plBallFaceOrbitMap I O)).val = (A.plOrbitFace vert P hvert O).val := by
  let Q := plDrawingRelabel I.toEquiv f I.edgeInv_comm I.rot_comm hv P
  have hi : Q.image = P.image :=
    plDrawingRelabel_image I.toEquiv f I.edgeInv_comm I.rot_comm hv P
  let F : Q.Face := ⟨(A.plOrbitFace vert P hvert O).val, by
    simpa only [hi] using (A.plOrbitFace vert P hvert O).property⟩
  obtain ⟨d, hd⟩ := O.property
  have hdO : d ∈ O.val := hd ▸ Equiv.Perm.SameCycle.rfl
  have hdI : I.toEquiv d ∈ (plBallFaceOrbitMap I O).val := ⟨d, hdO, rfl⟩
  have hborder : P.dartBorders d (A.plOrbitFace vert P hvert O) :=
    (A.plOrbitFace_eq_iff vert P hvert O d hdO _).mp rfl
  have hborder' : Q.dartBorders (I.toEquiv d) F := by
    change ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ, 0 < t → t < δ → 0 < ε → ε < δ →
      (P.arc (I.toEquiv.symm (I.toEquiv d))).start + (t : ℂ) *
        ((P.arc (I.toEquiv.symm (I.toEquiv d))).initialDirection +
          (ε : ℂ) * Complex.I * (P.arc (I.toEquiv.symm (I.toEquiv d))).initialDirection)
        ∈ (A.plOrbitFace vert P hvert O).val
    simpa only [PLDrawing.dartBorders, I.toEquiv.symm_apply_apply] using hborder
  have hface := (B.plOrbitFace_eq_iff vert' Q hvert'
    (plBallFaceOrbitMap I O) (I.toEquiv d) hdI F).mpr hborder'
  exact congrArg Subtype.val hface

include hDU1 in
/-- Helper toward Proposition 5.16: exterior-preserving ball isomorphisms
identify two arbitrary finite PL drawings after relabelling, conditional only
on the displayed general augmentation input DU1. Vertices, oriented dart
parametrizations and every actual orbit face are all transported. -/
theorem exists_plBallIso_homeomorph
    {V : Type*} {W : Type} [Finite W]
    {A B : D39FiniteBallWithExternal} (I : D39BallIsoWithExternal A B)
    (vert : A.toD39FiniteBall.D → V) (vert' : B.toD39FiniteBall.D → W)
    (P : PLDrawing A.toD39FiniteBall.D V
      A.toD39FiniteBall.map.edgeInv A.toD39FiniteBall.map.rot vert)
    (Q : PLDrawing B.toD39FiniteBall.D W
      B.toD39FiniteBall.map.edgeInv B.toD39FiniteBall.map.rot vert')
    (hv : Function.Surjective vert) (hw : Function.Surjective vert')
    (hconn : ∀ d e : B.toD39FiniteBall.D, Relation.EqvGen
      (fun x y => B.toD39FiniteBall.map.rot x = y ∨
        B.toD39FiniteBall.map.edgeInv x = y) d e)
    (hext : (¬ Bornology.IsBounded
        (A.toD39FiniteBall.plOrbitFace vert P hv A.externalOrbit).val) ∧
      (¬ Bornology.IsBounded
        (B.toD39FiniteBall.plOrbitFace vert' Q hw B.externalOrbit).val)) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ v, H (P.pos v) = Q.pos
        (plBallVertexEquiv I.toD39BallIso vert vert' P Q hv hw v)) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, H ((P.arc d).toPath t) =
          (Q.arc (I.toD39BallIso.toEquiv d)).toPath (φ t)) ∧
      ∀ O : D39BallFaceCycleOrbit A.toD39FiniteBall,
        H '' (A.toD39FiniteBall.plOrbitFace vert P hv O).val =
          (B.toD39FiniteBall.plOrbitFace vert' Q hw
            (plBallFaceOrbitMap I.toD39BallIso O)).val := by
  let f := plBallVertexEquiv I.toD39BallIso vert vert' P Q hv hw
  have hf : ∀ d, f (vert d) = vert' (I.toD39BallIso.toEquiv d) :=
    plBallVertexEquiv_apply I.toD39BallIso vert vert' P Q hv hw
  let R := plDrawingRelabel I.toD39BallIso.toEquiv f
    I.toD39BallIso.edgeInv_comm I.toD39BallIso.rot_comm hf P
  have hR (O : D39BallFaceCycleOrbit A.toD39FiniteBall) :
      (B.toD39FiniteBall.plOrbitFace vert' R hw
        (plBallFaceOrbitMap I.toD39BallIso O)).val =
          (A.toD39FiniteBall.plOrbitFace vert P hv O).val :=
    plDrawingRelabel_orbitFace I.toD39BallIso vert vert' P f hf hv hw O
  have hRext : ¬ Bornology.IsBounded
      (B.toD39FiniteBall.plOrbitFace vert' R hw B.externalOrbit).val := by
    rw [← plBallFaceOrbitMap_external I, hR]
    exact hext.1
  obtain ⟨H, hor, hp, ha, hfaces⟩ :=
    exists_plDrawing_homeomorph_of_augmentation hDU1 B.toD39FiniteBall vert'
      R Q hw hconn B.externalOrbit ⟨hRext, hext.2⟩
  refine ⟨H, hor, ?_, ?_, ?_⟩
  · intro v
    have h := hp (f v)
    change H (P.pos (f.symm (f v))) = Q.pos (f v) at h
    rwa [f.symm_apply_apply] at h
  · intro d
    obtain ⟨φ, hm, heq⟩ := ha (I.toD39BallIso.toEquiv d)
    refine ⟨φ, hm, ?_⟩
    intro t
    have h := heq t
    change H ((P.arc (I.toD39BallIso.toEquiv.symm
      (I.toD39BallIso.toEquiv d))).toPath t) =
        (Q.arc (I.toD39BallIso.toEquiv d)).toPath (φ t) at h
    rw [Equiv.symm_apply_apply] at h
    exact h
  · intro O
    have h := hfaces (plBallFaceOrbitMap I.toD39BallIso O)
    rwa [hR O] at h

include hDU1 in
/-- Helper toward Proposition 5.16: conditional on general DU1, the faced
ball isomorphism gives the plane homeomorphism, represented vertex positions,
complete geometric edge ranges and every restricted orbit face. This does
not yet construct the retained-ambient-face correspondence for packaging. -/
theorem d39PLRepresentation_ball_planeHomeomorph
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (y : D39DrawingRepresentationData N C)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (hPpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (hQpos : ∀ v, Q.pos v = C.map.toPlaneMapWithMissing.pos (y.vertexEquiv v))
    (hParc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (hQarc : ∀ d t, (Q.arc d).toPath t = d39DrawingDartArc C y d t)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIsoWithExternal
      (d39FacedBallPLWithExternal M P r hr)
      (d39FacedBallPLWithExternal N Q r hr)) :
    let f := plBallVertexEquiv I.toD39BallIso
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
      (d39FacedBallPLDrawing M P r hr) (d39FacedBallPLDrawing N Q r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ v, H (B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v.1)) =
        C.map.toPlaneMapWithMissing.pos (y.vertexEquiv (f v).1)) ∧
      (∀ d : (d39FacedBall M r hr).D,
        H '' Set.range (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d.1).1) =
          Set.range (C.map.toPlaneMapWithMissing.arc
            (y.dartEquiv (I.toD39BallIso.toEquiv d).1).1)) ∧
      ∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
        H '' ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val =
        ((d39FacedBall N r hr).plOrbitFace
          (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
          (d39FacedBallPLDrawing N Q r hr)
          (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
          (plBallFaceOrbitMap I.toD39BallIso O)).val := by
  let := d39FacedBallPLDrawing_finite_vertices N Q r hr
  dsimp only
  obtain ⟨H, hor, hp, ha, hfaces⟩ := exists_plBallIso_homeomorph hDU1 I
    (restrictedVertex P (d39BallDarts M r : Set M.core.D))
    (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
    (d39FacedBallPLDrawing M P r hr) (d39FacedBallPLDrawing N Q r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
    (d39FacedBall_connected N r hr)
    ⟨d39FacedBallPLWithExternal_unbounded M P r hr,
      d39FacedBallPLWithExternal_unbounded N Q r hr⟩
  refine ⟨H, hor, ?_, ?_, hfaces⟩
  · intro v
    have h := hp v
    rw [d39FacedBallPLDrawing_pos, d39FacedBallPLDrawing_pos, hPpos, hQpos] at h
    exact h
  · intro d
    obtain ⟨φ, _hm, heq⟩ := ha d
    have heq' : ∀ t, H ((P.arc d.1).toPath t) =
        (Q.arc (I.toD39BallIso.toEquiv d).1).toPath (φ t) := by
      intro t
      exact heq t
    rw [← d39PLRepresentation_arc_image x P hParc d.1,
      ← d39PLRepresentation_arc_image y Q hQarc (I.toD39BallIso.toEquiv d).1,
      ← Polyline.range_toPath, ← Polyline.range_toPath]
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨φ t, (heq' t).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨(P.arc d.1).toPath (φ.symm t),
        ⟨φ.symm t, rfl⟩, ?_⟩
      simpa only [φ.apply_symm_apply] using heq' (φ.symm t)

end

/-- Helper toward Proposition 5.16: the proved loopless packaging theorem
applies to any two compatible PL representations without additional no-loop
premises. The discrete correspondence and retained-face image equalities
are explicit inputs to this construction helper. -/
theorem d39PLRepresentation_geomBallIso_of_correspondence
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (y : D39DrawingRepresentationData N C)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (hParc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (hQarc : ∀ d t, (Q.arc d).toPath t = d39DrawingDartArc C y d t)
    (r : ℕ) (c : D39GeomBallCorrespondenceV2 r B C)
    (H : ℂ ≃ₜ ℂ) (hH : OrientationPreserving H)
    (hpos : ∀ v, H (B.map.toPlaneMapWithMissing.pos v.1) =
      C.map.toPlaneMapWithMissing.pos (c.vertexEquiv v).1)
    (harc : ∀ e, H '' Set.range (B.map.toPlaneMapWithMissing.arc e.1) =
      Set.range (C.map.toPlaneMapWithMissing.arc (c.edgeEquiv e).1))
    (hface : ∀ F, H '' F.1 = (c.faceEquiv F).1) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) :=
  d39GeomBallIsoV2_of_planeHomeomorph_of_noLoops r B C c
    (fun e => d39PLRepresentation_src_ne_tgt x P hParc e.1)
    (fun e => d39PLRepresentation_src_ne_tgt y Q hQarc e.1)
    H hH hpos harc hface



























































































































































end DirectedDistances.PaperProofs.Section5

end
