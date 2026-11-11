/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness6
public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso4
public import DirectedDistances.PaperProofs.Section5.Prop516PLExteriorTransport

/-! # Exterior-preserving augmentation reductions

and integration remain with the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: full-period vertex simplicity is
independent of the representative of a face-successor orbit. -/
theorem drawing_initialVertices_injOn_of_sameCycle
    {α V : Type*} [Fintype α] (f : Equiv.Perm α) (vert : α → V)
    {x y : α} (hxy : f.SameCycle x y)
    (h : Set.InjOn (fun n : ℕ => vert ((f : α → α)^[n] x))
      (Set.Iio (Function.minimalPeriod f x))) :
    Set.InjOn (fun n : ℕ => vert ((f : α → α)^[n] y))
      (Set.Iio (Function.minimalPeriod f y)) := by
  rw [drawing_initialVertices_injOn_iff] at h ⊢
  intro a ha b hb hab
  exact h (hxy.trans ha) (hxy.trans hb) hab

/-- Helper toward Proposition 5.16: a simple exterior of length `k` can be
retained while every bounded face is triangulated. All augmentation fields
and the two decompositions use the same witnesses. For `k = 4` this is the
entire DU1 conclusion on the explicitly restricted class of drawings whose
original exterior is already a simple quadrilateral. No frame is inserted. -/
theorem exists_sum_fin_augmented_drawings_of_simple_exterior
    {V : Type u} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (k : ℕ)
    (hboundary : ∃ a ∈ O_ext.val,
      Function.minimalPeriod B.map.faceSucc a = k ∧
      Set.InjOn (fun j : ℕ => vert ((B.map.faceSucc : B.D → B.D)^[j] a))
        (Set.Iio (Function.minimalPeriod B.map.faceSucc a))) :
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
      (∀ O : D39BallFaceCycleOrbit C, ∃ d ∈ O.val,
        (O = E → Function.minimalPeriod C.map.faceSucc d = k) ∧
        (O ≠ E → Function.minimalPeriod C.map.faceSucc d = 3) ∧
        Set.InjOn (fun j : ℕ => v ((C.map.faceSucc : C.D → C.D)^[j] d))
          (Set.Iio (Function.minimalPeriod C.map.faceSucc d))) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        closure (B.plOrbitFace vert P hvert O).val =
          ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        closure (B.plOrbitFace vert P' hvert O).val =
          ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) := by
  classical
  obtain ⟨a, ha, hk, hinj⟩ := hboundary
  have hsame : B.map.faceSucc.SameCycle O_ext.property.choose a := by
    exact (show a ∈ {e | B.map.faceSucc.SameCycle O_ext.property.choose e}
      from O_ext.property.choose_spec ▸ ha)
  have hperiod0 : Function.minimalPeriod B.map.faceSucc O_ext.property.choose = k :=
    (drawing_period_of_sameCycle B.map.faceSucc hsame).symm.trans hk
  have hinj0 := drawing_initialVertices_injOn_of_sameCycle B.map.faceSucc
    vert hsame.symm hinj
  obtain ⟨n, C, v, ι, Q, Q', hv, E, I, hc, hr, hf, hvertex, hm, ht,
    hp, hp', harc, harc', _hE, _hface, _hface', hu, hu', htri,
    hperiod, hsimp, _hsingle, _hI, _hI', hcover, hcover'⟩ :=
    B.exists_sum_fin_triangulated_drawings_with_preserved_exterior
      vert P P' hvert hconn O_ext hext
  refine ⟨n, C, v, ι, Q, Q', hv, E, I, hc, hr, hf, hvertex, hm, ht,
    hp, hp', harc, harc', (hu E).mpr rfl, (hu' E).mpr rfl, ?_, hcover, hcover'⟩
  intro O
  let d := O.property.choose
  have hd : d ∈ O.val := O.property.choose_spec ▸ Equiv.Perm.SameCycle.rfl
  by_cases hO : O = E
  · subst O
    refine ⟨d, hd, fun _ => (hperiod d hd).trans hperiod0, ?_,
      (hsimp d hd).mpr hinj0⟩
    intro hne
    exact (hne rfl).elim
  · have hdE : d ∉ E.val := by
      intro hdE
      apply hO
      apply C.plOrbitFace_injective v Q hv hc
      rw [C.plOrbitFace_eq_plDartFace_of_mem v Q hv O d hd,
        C.plOrbitFace_eq_plDartFace_of_mem v Q hv E d hdE]
    obtain ⟨hthree, hsimple⟩ := htri d hdE
    refine ⟨d, hd, fun heq => (hO heq).elim, fun _ => hthree, ?_⟩
    rwa [hthree]

/-- Helper toward Proposition 5.16: a common simple exterior of length at
least three suffices for plane equivalence, even when bounded original
faces repeat vertices. The bounded-face refinement is constructed, and no
DU1 or independent child-matching premise is used. -/
theorem exists_plane_homeomorph_of_simple_exterior
    {V : Type u} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hboundary : ∃ a ∈ O_ext.val,
      3 ≤ Function.minimalPeriod B.map.faceSucc a ∧
      Set.InjOn (fun j : ℕ => vert ((B.map.faceSucc : B.D → B.D)^[j] a))
        (Set.Iio (Function.minimalPeriod B.map.faceSucc a))) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : V, H (P.pos x) = P'.pos x) ∧
      (∀ d, H '' (P.arc d).image = (P'.arc d).image) ∧
      (H '' P.image = P'.image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val) := by
  obtain ⟨a, ha, hk, hinj⟩ := hboundary
  obtain ⟨n, C, v, ι, Q, Q', hv, E, I, hc, _hr, _hf, _hvertex, _hm, _ht,
    hp, hp', harc, harc', hu, hu', hshapes, hcover, hcover'⟩ :=
    B.exists_sum_fin_augmented_drawings_of_simple_exterior
      vert P P' hvert hconn O_ext hext
      (Function.minimalPeriod B.map.faceSucc a) ⟨a, ha, rfl, hinj⟩
  have hsimple : ∀ O : D39BallFaceCycleOrbit C, ∃ d ∈ O.val,
      3 ≤ Function.minimalPeriod C.map.faceSucc d ∧
      Set.InjOn (fun j : ℕ => v ((C.map.faceSucc : C.D → C.D)^[j] d))
        (Set.Iio (Function.minimalPeriod C.map.faceSucc d)) := by
    intro O
    obtain ⟨d, hd, houter, hinner, hs⟩ := hshapes O
    refine ⟨d, hd, ?_, hs⟩
    by_cases hO : O = E
    · rw [houter hO]
      exact hk
    · rw [hinner hO]
  exact B.exists_orientationPreserving_plane_homeomorph_of_augmentation
    C vert v P P' Q Q' hvert hv hc ι Sum.inl hp hp' harc harc'
    E ⟨hu, hu'⟩ hsimple I hcover hcover'

/-- Helper toward Proposition 5.16: on the simple-exterior subdomain the
constructed plane equivalence also preserves each dart's direction through
a strictly increasing reparametrization of the closed unit interval. -/
theorem exists_plDrawing_homeomorph_of_simple_exterior
    {V : Type u} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hboundary : ∃ a ∈ O_ext.val,
      3 ≤ Function.minimalPeriod B.map.faceSucc a ∧
      Set.InjOn (fun j : ℕ => vert ((B.map.faceSucc : B.D → B.D)^[j] a))
        (Set.Iio (Function.minimalPeriod B.map.faceSucc a))) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : V, H (P.pos x) = P'.pos x) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, H ((P.arc d).toPath t) = (P'.arc d).toPath (φ t)) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val) := by
  obtain ⟨H, hor, hpos, harc, _himage, _hclosed, hface⟩ :=
    B.exists_plane_homeomorph_of_simple_exterior
      vert P P' hvert hconn O_ext hext hboundary
  refine ⟨H, hor, hpos, ?_, hface⟩
  intro d
  have hstart : H (P.arc d).start = (P'.arc d).start := by
    rw [P.arc_start, P'.arc_start, hpos]
  have hfinish : H (P.arc d).finish = (P'.arc d).finish := by
    rw [P.arc_finish, P'.arc_finish, hpos]
  obtain ⟨φ, hm, _ha, heq⟩ :=
    DirectedDistances.PaperProofs.Section5.exists_path_reparam_of_planeHomeomorph
    (P.arc d).toPath (P'.arc d).toPath
    ((P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d))
    ((P'.arc d).toPath_injective (P'.arc_length d) (P'.arc_simple d))
    H false hstart hfinish (by simpa only [Polyline.range_toPath] using harc d)
  exact ⟨φ, hm rfl, heq⟩

end D39FiniteBall
end DirectedDistances.PlanarMap

end































































































































































































































