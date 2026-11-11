/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso6

/- # The selected exterior and the raw ball-isomorphism interface

Helpers toward Proposition 5.16, using Definition 3.8
unbounded complementary face of the restricted PL drawing. It is additional
data in `D39FiniteBallWithExternal`, not a field of `D39FiniteBall`.

The results below characterize dart membership and show exactly when the
identity raw isomorphism lifts after choosing two markers. They do not prove
exterior transport for independent represented drawings. Independent source -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16: identity raw transport fixes every
face-successor orbit, independently of any external marker. -/
theorem plBallFaceOrbitMap_refl (A : D39FiniteBall)
    (O : D39BallFaceCycleOrbit A) :
    plBallFaceOrbitMap (D39BallIso.refl A) O = O := by
  apply (plBallFaceOrbitMap_eq_iff (D39BallIso.refl A) O O).mpr
  intro d
  rfl

/-- Helper toward Proposition 5.16: after independently marking the same
raw ball, its identity isomorphism lifts precisely when the markers agree.
Thus the raw fields impose no requirement on those additional markers. -/
theorem d39BallIso_refl_external_lift_iff
    (A : D39FiniteBall) (O S : D39BallFaceCycleOrbit A) :
    (∃ J : D39BallIsoWithExternal ⟨A, O⟩ ⟨A, S⟩,
      J.toD39BallIso = D39BallIso.refl A) ↔ O = S := by
  constructor
  · rintro ⟨J, hJ⟩
    have h := J.external_iff
    rw [hJ] at h
    exact (plBallFaceOrbitMap_refl A O).symm.trans
      ((plBallFaceOrbitMap_eq_iff (D39BallIso.refl A) O S).mpr h)
  · rintro rfl
    exact ⟨D39BallIsoWithExternal.refl ⟨A, O⟩, rfl⟩

/-- Helper toward Proposition 5.16: an explicit raw finite ball admits two
markers for which the identity cannot lift. This is a counterexample at the
marked-data interface only, not a construction of two represented drawings. -/
theorem exists_d39BallIso_refl_without_external_lift :
    ∃ (A : D39FiniteBall) (O S : D39BallFaceCycleOrbit A),
      O ≠ S ∧ ¬ ∃ J : D39BallIsoWithExternal ⟨A, O⟩ ⟨A, S⟩,
        J.toD39BallIso = D39BallIso.refl A := by
  let A : D39FiniteBall :=
    { D := Bool
      map :=
        { edgeInv := Equiv.swap false true
          edgeInv_invol := by intro d; cases d <;> decide
          edgeInv_ne := by intro d; cases d <;> decide
          rot := Equiv.swap false true }
      missing := fun _ => True
      tail := fun _ => False
      rootDart := false
      original := Set.univ
      original_closed := fun _ => Iff.rfl }
  have hf : A.map.faceSucc = 1 := by
    change (Equiv.swap false true)⁻¹ * Equiv.swap false true = 1
    exact inv_mul_cancel _
  let O : D39BallFaceCycleOrbit A :=
    ⟨{e | A.map.faceSucc.SameCycle false e}, false, rfl⟩
  let S : D39BallFaceCycleOrbit A :=
    ⟨{e | A.map.faceSucc.SameCycle true e}, true, rfl⟩
  have hne : O ≠ S := by
    intro h
    have hd : false ∈ O.val := Equiv.Perm.SameCycle.rfl
    have hs : false ∈ S.val := h ▸ hd
    change A.map.faceSucc.SameCycle true false at hs
    rw [hf, Equiv.Perm.sameCycle_one] at hs
    exact Bool.noConfusion hs
  exact ⟨A, O, S, hne, fun h =>
    hne ((d39BallIso_refl_external_lift_iff A O S).mp h)⟩

/-- Helper toward Proposition 5.16: a dart belongs to the selected external
orbit exactly when its own geometric left face is unbounded. This does not
identify externality with the `original` or `missing` tags. -/
theorem mem_plExternalOrbit_iff_not_isBounded_plDartFace
    {V : Type*} [Finite V] (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : A.D, Relation.EqvGen
      (fun x y => A.map.rot x = y ∨ A.map.edgeInv x = y) d e)
    (d : A.D) :
    d ∈ (plExternalOrbit A vert P hvert hconn).val ↔
      ¬ Bornology.IsBounded (A.plDartFace vert P hvert d).val := by
  constructor
  · intro hd
    have hface := A.plOrbitFace_eq_plDartFace_of_mem vert P hvert
      (plExternalOrbit A vert P hvert hconn) d hd
    have hu := (plExternalOrbit_eq_iff A vert P hvert hconn _).mp rfl
    rw [hface] at hu
    exact hu
  · intro hd
    let O : D39BallFaceCycleOrbit A :=
      ⟨{e | A.map.faceSucc.SameCycle d e}, d, rfl⟩
    have hdO : d ∈ O.val := Equiv.Perm.SameCycle.rfl
    have hface := A.plOrbitFace_eq_plDartFace_of_mem vert P hvert O d hdO
    have hu : ¬ Bornology.IsBounded (A.plOrbitFace vert P hvert O).val := by
      rw [hface]
      exact hd
    have hO := (plExternalOrbit_eq_iff A vert P hvert hconn O).mpr hu
    exact hO ▸ hdO

/-- Helper toward Proposition 5.16: the positive-radius represented ball's
external marker tests unboundedness of its restricted dart face. No ambient
finiteness or exterior-preservation assumption is used. -/
theorem d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D) :
    d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val ↔
      ¬ Bornology.IsBounded
        ((d39FacedBall M r hr).plDartFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) d).val := by
  let := d39FacedBallPLDrawing_finite_vertices M P r hr
  exact mem_plExternalOrbit_iff_not_isBounded_plDartFace
    (d39FacedBall M r hr) _ (d39FacedBallPLDrawing M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr)
    (d39FacedBall_connected M r hr) d





































































































end DirectedDistances.PaperProofs.Section5

end
