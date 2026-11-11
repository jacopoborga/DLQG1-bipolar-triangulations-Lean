/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization7
public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitReduction
public import DirectedDistances.PaperProofs.Section5.Prop516ReverseComparison2

/-! # Finite drawing independence toward Proposition 3.9

The exterior-face characterization identifies the common unbounded orbit.
The proved finite PL extension theorem then transports arbitrary finite
stage drawings, without a convex geometric certificate. This does not yet
compare a centered finite window with a whole-plane drawing. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set

private def finiteStageBall (w : ℕ → Fin 3) (n : ℕ) : D39FiniteBall where
  D := StageDart (kmswStage w n).nextEdge
  map := kmswMap w n
  missing := (kmswStageDirectedMap w n).missing
  tail := (kmswStageDirectedMap w n).tail
  rootDart := (kmswRootedStage w n).root
  original := Set.univ
  original_closed := fun _ => Iff.rfl

private theorem finiteStageBall_connected (w : ℕ → Fin 3) (n : ℕ) :
    ∀ d e : (finiteStageBall w n).D, Relation.EqvGen
      (fun x y => (finiteStageBall w n).map.rot x = y ∨
        (finiteStageBall w n).map.edgeInv x = y) d e := by
  intro d e
  have h := kmswMap_isConnected w n d e
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | @tail b c _ hbc ih =>
    apply ih.trans
    rcases hbc with h | h | h | h
    · exact Relation.EqvGen.rel _ _ (Or.inl h.symm)
    · apply Relation.EqvGen.symm
      apply Relation.EqvGen.rel
      left
      exact (congrArg (kmswMap w n).rot h).trans
        ((kmswMap w n).rot.apply_symm_apply _)
    · exact Relation.EqvGen.rel _ _ (Or.inr h.symm)
    · apply Relation.EqvGen.symm
      apply Relation.EqvGen.rel
      right
      exact (congrArg (kmswMap w n).edgeInv h).trans
        ((kmswMap w n).edgeInv.apply_symm_apply _)

/-- Helper toward Proposition 3.9: two arbitrary finite stage drawings
with the source exterior orbit admit one orientation-preserving ambient
homeomorphism preserving all vertex labels and ordered dart paths. -/
theorem uibotFiniteStageDrawing_ambient_homeomorph
    {w : ℕ → Fin 3} {n : ℕ} (P P' : StageDrawing w n)
    (U : P.Face) (U' : P'.Face)
    (hU : P.IsUnbounded U) (hU' : P'.IsUnbounded U')
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (hborder' : ∀ d, P'.dartBorders d U' ↔ (kmswStageDirectedMap w n).IsOuter d) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v, h (P.pos v) = P'.pos v) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, h ((P.arc d).toPath t) = (P'.arc d).toPath (φ t)) := by
  let B := finiteStageBall w n
  let vert := stageVertex w n
  have hv : Function.Surjective vert := kmswStageDrawing_vertex_surjective w n
  obtain ⟨O, hO⟩ := B.plOrbitFace_surjective vert P hv U
  obtain ⟨d, hd⟩ := O.property
  have hdO : d ∈ O.val := hd.symm ▸ Equiv.Perm.SameCycle.rfl
  have hdU := (B.plOrbitFace_eq_iff vert P hv O d hdO U).mp hO
  have hO' : B.plOrbitFace vert P' hv O = U' :=
    (B.plOrbitFace_eq_iff vert P' hv O d hdO U').mpr
      ((hborder' d).mpr ((hborder d).mp hdU))
  obtain ⟨h, ho, hp, ha, _⟩ := ReverseComparison2.exists_plDrawing_homeomorph
    B vert P P' hv (finiteStageBall_connected w n) O
      ⟨hO.symm ▸ (P.isUnbounded_iff_not_isBounded U).mp hU,
        hO'.symm ▸ (P'.isUnbounded_iff_not_isBounded U').mp hU'⟩
  exact ⟨h, ho, hp, ha⟩

/-- Helper toward Proposition 3.9: arbitrary finite drawings of the same
stage and source exterior orbit are isomorphic as rooted directed geometric
maps at every chronological root, preserving all individual edge identities. -/
theorem uibotFiniteStageDrawing_rootedIso
    {w : ℕ → Fin 3} {n : ℕ} (P P' : StageDrawing w n)
    (U : P.Face) (U' : P'.Face)
    (hU : P.IsUnbounded U) (hU' : P'.IsUnbounded U')
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (hborder' : ∀ d, P'.dartBorders d U' ↔ (kmswStageDirectedMap w n).IsOuter d)
    (j : ℕ) (hj : j ≤ n) :
    Nonempty (D39GeomRootedMapIsoV2
      (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j hj)
      (uibotFiniteStageExteriorMap P' U' hU' hborder')
      (uibotFiniteStageExteriorRoot P' j hj)) := by
  obtain ⟨h, ho, hp, ha⟩ :=
    uibotFiniteStageDrawing_ambient_homeomorph P P' U U' hU hU' hborder hborder'
  choose φ hφ hpath using ha
  exact ⟨{
    h := h
    orientationPreserving := ho
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.refl _
    edgeFlip := fun _ => false
    edgeParam := fun e => φ e.out
    edgeParam_mono := fun e _ => hφ e.out
    edgeParam_anti := by intro e he; cases he
    pos_map := hp
    arc_map := fun e t => hpath e.out t
    src_map := fun _ => rfl
    tgt_map := fun _ => rfl
    missing_map := fun _ => Iff.rfl
    orientation_map := by intro e he; exact (Bool.xor_false _).symm
    root_edge_map := rfl
    root_bool_map := (Bool.xor_false _).symm }⟩

/-- Helper toward Proposition 3.9: the same ambient homeomorphism gives
an equivalence of the original finite complementary faces and preserves
retention at every radius. Both directions use the full face closures. -/
theorem uibotFiniteStageDrawing_faceEquiv
    {w : ℕ → Fin 3} {n : ℕ} (P P' : StageDrawing w n)
    (U : P.Face) (U' : P'.Face)
    (hU : P.IsUnbounded U) (hU' : P'.IsUnbounded U')
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (hborder' : ∀ d, P'.dartBorders d U' ↔ (kmswStageDirectedMap w n).IsOuter d)
    (j : ℕ) (hj : j ≤ n) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      ∃ f : P.toPlaneGraphDrawing.Face ≃ P'.toPlaneGraphDrawing.Face,
        (∀ F, h '' F.val = (f F).val) ∧
        ∀ r F,
          F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
            (uibotFiniteStageExteriorRoot P j hj) r ↔
          f F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P' U' hU' hborder')
            (uibotFiniteStageExteriorRoot P' j hj) r := by
  obtain ⟨I⟩ := uibotFiniteStageDrawing_rootedIso P P' U U' hU hU' hborder hborder' j hj
  exact ⟨I.h, I.orientationPreserving, I.faceEquiv,
    fun F => (I.faceEquiv_val F).symm, I.retainedFaces_map⟩

/-- Helper toward Proposition 3.9: the finite drawing-independence
interface in the local-limit reduction is proved from its original exterior
premises, with no additional geometric comparison assumption. -/
theorem uibotDrawingIndependence_proved : UIBOTDrawingIndependence := by
  intro w n j hj P P' U U' hU hU' hborder hborder'
  exact uibotFiniteStageDrawing_rootedIso P P' U U' hU hU' hborder hborder' j hj

end DirectedDistances.PaperProofs.Section3
end
