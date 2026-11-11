/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation3
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation4

/-! Helper toward Proposition 5.16.

This module transports the stage drawing's proved dart-face assignment to
the stage rooted-map face-successor orbits. It makes no paper-completion
claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

/-- Helper toward Proposition 5.16. The geometric left face of a stage dart
is unchanged by the rooted map's face-successor permutation. -/
theorem kmswStageDrawing_leftFace_faceSucc
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d : (kmswStageD39RootedMap w n).core.D) :
    kmswStageDrawing_leftFace P
        ((kmswStageD39RootedMap w n).core.rot.symm
          ((kmswStageD39RootedMap w n).core.edgeInv d)) =
      kmswStageDrawing_leftFace P d := by
  let M := kmswStageD39RootedMap w n
  let f : Equiv.Perm M.core.D := M.core.rot.symm * M.core.edgeInv
  change kmswStageDrawing_leftFace P (f d) = kmswStageDrawing_leftFace P d
  have hborder : P.dartBorders (f d) (kmswStageDrawing_leftFace P (f d)) :=
    (kmswStageDrawing_leftFace_eq_iff P (f d)
      (kmswStageDrawing_leftFace P (f d))).mp rfl
  have hstep := P.dartBorders_flip_rot
      (kmswStageDrawing_vertex_surjective w n) (f d)
      (kmswStageDrawing_leftFace P (f d)) hborder
  have hrev : edgeFlip (kmswStage w n).nextEdge
      (stageRot w n ((stageRot w n).symm (edgeFlip _ d))) = d := by
    rw [Equiv.apply_symm_apply]
    cases d with
    | mk e b => cases b <;> rfl
  have hstep' : P.dartBorders d (kmswStageDrawing_leftFace P (f d)) := by
    change P.dartBorders
      (edgeFlip (kmswStage w n).nextEdge
        (stageRot w n ((stageRot w n).symm (edgeFlip _ d))))
      (kmswStageDrawing_leftFace P (f d)) at hstep
    rw [hrev] at hstep
    exact hstep
  exact ((kmswStageDrawing_leftFace_eq_iff P d
    (kmswStageDrawing_leftFace P (f d))).mpr hstep').symm

/-- Helper toward Proposition 5.16. The geometric left face is constant on
every cycle of the rooted map's face-successor permutation. -/
theorem kmswStageDrawing_leftFace_eq_of_sameCycle
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d e : (kmswStageD39RootedMap w n).core.D)
    (h : Equiv.Perm.SameCycle
      ((kmswStageD39RootedMap w n).core.rot.symm *
        (kmswStageD39RootedMap w n).core.edgeInv) d e) :
    kmswStageDrawing_leftFace P d = kmswStageDrawing_leftFace P e := by
  let M := kmswStageD39RootedMap w n
  let f : Equiv.Perm M.core.D := M.core.rot.symm * M.core.edgeInv
  let face : M.core.D → P.Face := kmswStageDrawing_leftFace P
  have hforward (a : M.core.D) : face (f a) = face a :=
    kmswStageDrawing_leftFace_faceSucc P a
  have hbackward (a : M.core.D) : face (f.symm a) = face a := by
    simpa only [Equiv.apply_symm_apply] using (hforward (f.symm a)).symm
  obtain ⟨i, hi⟩ := h
  have hpow (i : ℤ) : face ((f ^ i) d) = face d := by
    refine Int.induction_on i ?_ ?_ ?_
    · simp only [zpow_zero, Equiv.Perm.one_apply]
    · intro i ih
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_one,
        Equiv.Perm.mul_apply, hforward, ih]
    · intro i ih
      rw [show (-(i : ℤ) - 1) = -1 + -(i : ℤ) by ring,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact (hbackward _).trans ih
  exact (hpow i).symm.trans (congrArg face hi)

/-- Helper toward Proposition 5.16. Equal geometric left faces of stage
darts force those darts into the same rooted-map face-successor cycle. -/
theorem kmswStageDrawing_sameCycle_of_leftFace_eq
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d e : StageDart (kmswStage w n).nextEdge)
    (hface : kmswStageDrawing_leftFace P d =
      kmswStageDrawing_leftFace P e) :
    Equiv.Perm.SameCycle
      ((kmswStageD39RootedMap w n).core.rot.symm *
        (kmswStageD39RootedMap w n).core.edgeInv) d e := by
  let B : D39FiniteBall := {
    D := StageDart (kmswStage w n).nextEdge
    map := kmswMap w n
    missing := (kmswStageDirectedMap w n).missing
    tail := (kmswStageDirectedMap w n).tail
    rootDart := (kmswRootedStage w n).root
    original := Set.univ
    original_closed := by intro x; simp
  }
  have hvert : Function.Surjective (stageVertex w n) :=
    kmswStageDrawing_vertex_surjective w n
  let face := B.plDartFace (stageVertex w n) P hvert
  have hface_bridge (x : B.D) : face x = kmswStageDrawing_leftFace P x := by
    apply P.dartBorders_face_unique x (face x)
      (kmswStageDrawing_leftFace P x)
    · exact (B.plDartFace_eq_iff (stageVertex w n) P hvert x (face x)).mp rfl
    · exact (kmswStageDrawing_leftFace_eq_iff P x
        (kmswStageDrawing_leftFace P x)).mp rfl
  have hconn : ∀ x y : B.D,
      Relation.EqvGen (fun a b => B.map.rot a = b ∨ B.map.edgeInv a = b) x y := by
    intro x y
    let R : B.D → B.D → Prop := fun a b =>
      b = B.map.rot a ∨ b = B.map.rot.symm a ∨
        b = B.map.edgeInv a ∨ b = B.map.edgeInv.symm a
    have hstep {a b : B.D} (hab : R a b) :
        Relation.EqvGen (fun p q => B.map.rot p = q ∨ B.map.edgeInv p = q) a b := by
      rcases hab with hab | hab | hab | hab
      · exact Relation.EqvGen.rel _ _ (Or.inl hab.symm)
      · exact (Relation.EqvGen.rel b a
          (Or.inl (by rw [hab, Equiv.apply_symm_apply]))).symm
      · exact Relation.EqvGen.rel _ _ (Or.inr hab.symm)
      · exact (Relation.EqvGen.rel b a
          (Or.inr (by rw [hab, Equiv.apply_symm_apply]))).symm
    have hconnected := kmswMap_isConnected w n
    change ∀ a b, Relation.ReflTransGen
      (fun p q : StageDart (kmswStage w n).nextEdge =>
        q = (kmswMap w n).rot p ∨ q = (kmswMap w n).rot.symm p ∨
          q = (kmswMap w n).edgeInv p ∨ q = (kmswMap w n).edgeInv.symm p) a b
      at hconnected
    have hpath : Relation.ReflTransGen R x y := by
      exact hconnected x y
    refine Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => Relation.EqvGen
        (fun p q => B.map.rot p = q ∨ B.map.edgeInv p = q) a y) hpath ?_ ?_
    · exact Relation.EqvGen.refl y
    · intro a b hxy _ ih
      exact (hstep hxy).trans _ _ _ ih
  have hface' : face d = face e := by
    rw [hface_bridge d, hface, hface_bridge e]
  have hcycle := B.plDartFace_sameCycle_of_eq
    (stageVertex w n) P hvert hconn d e hface'
  change B.map.faceSucc.SameCycle d e
  exact hcycle



theorem kmswStageDrawing_leftFace_transported_surjective
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) :
    Function.Surjective (fun d : (kmswStageD39RootedMap w n).core.D =>
      P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d)) := by
  intro F
  obtain ⟨d, hd⟩ := kmswStageDrawing_leftFace_surjective P
    (P.toPlaneGraphDrawingFaceEquiv F)
  exact ⟨d, congrArg P.toPlaneGraphDrawingFaceEquiv.symm hd⟩

/-- Helper toward Proposition 5.16. Transport the stage dart's uniquely
determined geometric left face to the finite drawing's geometric face type. -/
noncomputable def kmswStageDrawing_faceOfDart
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) :
    (kmswStageD39RootedMap w n).core.D → P.toPlaneGraphDrawing.Face :=
  fun d => P.toPlaneGraphDrawingFaceEquiv.symm
    (kmswStageDrawing_leftFace P d)

/-- Helper toward Proposition 5.16. The transported stage face assignment is
surjective onto the geometric face carrier of the constructed domain map. -/
theorem kmswStageDrawing_domainFace_surjective
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    let B := kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder;
    Function.Surjective (fun d : (kmswStageD39RootedMap w n).core.D =>
      (P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d) :
        B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)) := by
  dsimp only
  exact kmswStageDrawing_leftFace_transported_surjective P

/-- Helper toward Proposition 5.16. When the quotient direction selects the
reverse representative, the transported left face is on the right of the
stored geometric edge. -/
theorem kmswStageDrawing_leftFace_reverse_sideRightOf
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge)
    (hbit : (kmswStageDrawingDartEdgeDirectionEquiv P d).2 = false) :
    P.toPlaneGraphDrawing.SideRightOf
      (P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d))
      (kmswStageDrawingDartEdgeDirectionEquiv P d).1 := by
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  let e := (E d).1
  let F := P.toPlaneGraphDrawingFaceEquiv.symm
    (kmswStageDrawing_leftFace P d)
  have hd : d = edgeFlip _ e.out := by
    have h := kmswStageDrawingDartEdgeDirectionEquiv_reconstructs P d
    simpa [E, hbit] using h
  have hborder : P.dartBorders (edgeFlip _ e.out)
      (kmswStageDrawing_leftFace P d) := by
    rw [← hd]
    exact (kmswStageDrawing_leftFace_eq_iff P d
      (kmswStageDrawing_leftFace P d)).mp rfl
  intro s
  have hr := P.dartBorders_flip_toPath_rightAtOn
    (kmswStageDrawing_vertex_surjective w n) e.out
    (kmswStageDrawing_leftFace P d) hborder s
  exact (P.toPlaneGraphDrawing_rightAtOn_iff e F s).mpr (by
    simpa [F] using hr)

/-- Helper toward Proposition 5.16. A transported stage face is on the side
of its stored geometric edge selected by the quotient direction bit. -/
theorem kmswStageDrawing_faceOfDart_side
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d : (kmswStageD39RootedMap w n).core.D) :
    if (kmswStageDrawingDartEdgeDirectionEquiv P d).2 then
      P.toPlaneGraphDrawing.SideLeftOf (kmswStageDrawing_faceOfDart P d)
        (kmswStageDrawingDartEdgeDirectionEquiv P d).1
    else
      P.toPlaneGraphDrawing.SideRightOf (kmswStageDrawing_faceOfDart P d)
        (kmswStageDrawingDartEdgeDirectionEquiv P d).1 := by
  change StageDart (kmswStage w n).nextEdge at d
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  let Q : PLDrawing (StageDart (kmswStage w n).nextEdge)
      (Fin (kmswStage w n).nextVertex) (edgeFlip _) (stageRot w n)
      (stageVertex w n) := P
  cases hbit : (E d).2 with
  | true =>
    have hd : d = (E d).1.out := by
      have hrec := kmswStageDrawingDartEdgeDirectionEquiv_reconstructs P d
      simpa [E, hbit] using hrec
    intro s
    have hborderD : P.dartBorders d (kmswStageDrawing_leftFace P d) :=
      (kmswStageDrawing_leftFace_eq_iff P d
        (kmswStageDrawing_leftFace P d)).mp rfl
    have hborder : P.dartBorders (E d).1.out
        (kmswStageDrawing_leftFace P d) := hd ▸ hborderD
    have hl := Q.dartBorders_toPath_leftAtOn
      (kmswStageDrawing_vertex_surjective w n) (E d).1.out
      (kmswStageDrawing_leftFace P d) hborder s
    have hface_eq : Q.toPlaneGraphDrawingFaceEquiv
        (kmswStageDrawing_faceOfDart P d) = kmswStageDrawing_leftFace P d := by
      change P.toPlaneGraphDrawingFaceEquiv
        (P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d)) = _
      exact Equiv.apply_symm_apply _ _
    exact (Q.toPlaneGraphDrawing_leftAtOn_iff (E d).1
      (kmswStageDrawing_faceOfDart P d) s).mpr (hface_eq ▸ hl)
  | false =>
    exact kmswStageDrawing_leftFace_reverse_sideRightOf P d hbit

/-- Helper toward Proposition 5.16. Assemble the finite stage's complete
`D39DrawingRepresentationData` from the proved endpoint, dart, orbit, side,
and root correspondences. -/
theorem kmswStageDrawing_baseRepresentation
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    Nonempty (D39DrawingRepresentationData
      (kmswStageD39RootedMap w n)
      (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder)) := by
  let M := kmswStageD39RootedMap w n
  let B := kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  let faceOfDart : M.core.D → B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face :=
    fun d => P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d)
  have hfaceOrbit : ∀ d e : M.core.D,
      faceOfDart d = faceOfDart e ↔
        Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e := by
    intro d e
    constructor
    · intro h
      apply kmswStageDrawing_sameCycle_of_leftFace_eq P d e
      have h' := congrArg P.toPlaneGraphDrawingFaceEquiv h
      simpa [faceOfDart] using h'
    · intro h
      have h' := kmswStageDrawing_leftFace_eq_of_sameCycle P d e h
      exact congrArg P.toPlaneGraphDrawingFaceEquiv.symm h'
  have hfaceSurj : Function.Surjective faceOfDart := by
    exact kmswStageDrawing_domainFace_surjective P U hU hborder
  refine ⟨d39DrawingRepresentationData_of_fields
    (kmswStageD39RootedMap_vertexEquiv w n)
    P.pos_injective E
    (fun d => kmswStageDrawingDartEdgeDirectionEquiv_tail_endpoint P U hU hborder d)
    (fun d => kmswStageDrawingDartEdgeDirectionEquiv_head_endpoint P U hU hborder d)
    (fun d => kmswStageDrawingDartEdgeDirectionEquiv_edgeFlip P d)
    (fun d => kmswStageDrawingDartEdgeDirectionEquiv_missing P U hU hborder d)
    (fun d hd => kmswStageDrawingDartEdgeDirectionEquiv_orientation P U hU hborder d hd)
    (kmswStageDrawingDartEdgeDirectionEquiv_root P U hU hborder)
    faceOfDart hfaceOrbit hfaceSurj
    (fun d => kmswStageDrawing_faceOfDart_side P d)⟩

end DirectedDistances.PaperProofs.Section5

end
