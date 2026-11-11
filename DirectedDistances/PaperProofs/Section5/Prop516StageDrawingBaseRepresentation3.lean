/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation2
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation4

/-! # Finite stage drawing representation fields

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

/-- Helper toward Proposition 5.16. Reversing a stage dart preserves its
geometric edge identity and flips the direction Boolean in the quotient
dart/edge/direction equivalence. -/
theorem kmswStageDrawingDartEdgeDirectionEquiv_edgeFlip
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) :
    kmswStageDrawingDartEdgeDirectionEquiv P (edgeFlip _ d) =
      ((kmswStageDrawingDartEdgeDirectionEquiv P d).1,
        !(kmswStageDrawingDartEdgeDirectionEquiv P d).2) := by
  apply Prod.ext
  · apply Quotient.sound
    change edgeFlip _ d = d ∨ edgeFlip _ d = edgeFlip _ d
    exact Or.inr rfl
  · unfold kmswStageDrawingDartEdgeDirectionEquiv
    dsimp
    have hq : Quotient.mk P.edgeSetoid (edgeFlip _ d) =
        Quotient.mk P.edgeSetoid d := by
      apply Quotient.sound
      exact Or.inr rfl
    change decide (edgeFlip _ d =
      (Quotient.mk P.edgeSetoid (edgeFlip _ d)).out) =
        !(decide (d = (Quotient.mk P.edgeSetoid d).out))
    rw [hq]
    have hne : d ≠ edgeFlip _ d := by
      intro h
      have hb := congrArg Prod.snd h
      cases hb' : d.2 <;> simp [edgeFlip, hb'] at hb
    rcases P.geometricEdge_out_mk d with hout | hout
    · rw [hout]
      have hflip : edgeFlip _ d ≠ d := fun h => hne h.symm
      simp [hflip]
    · rw [hout]
      cases d with
      | mk i b => cases b <;> simp [edgeFlip]

/-- Helper toward Proposition 5.16. The quotient dart equivalence's Boolean
selects the stage source and target endpoints in the exterior-data domain. -/
theorem kmswStageDrawingDartEdgeDirectionEquiv_tail_endpoint
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (d : StageDart (kmswStage w n).nextEdge) :
    kmswStageD39RootedMap_vertexEquiv w n
        (rootedLocallyFiniteVertexClass
          (kmswStageD39RootedMap w n).core.rot d) =
      if (kmswStageDrawingDartEdgeDirectionEquiv P d).2 then
        ((kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.src)
          (kmswStageDrawingDartEdgeDirectionEquiv P d).1
      else
        ((kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.tgt)
          (kmswStageDrawingDartEdgeDirectionEquiv P d).1 := by
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  change stageVertex w n d =
    if (E d).2 then stageVertex w n (E d).1.out
    else stageVertex w n (edgeFlip _ (E d).1.out)
  cases hbit : (E d).2
  · have hd : edgeFlip _ (E d).1.out = d := by
      have := E.left_inv d
      change (if (E d).2 then (E d).1.out else
        edgeFlip _ (E d).1.out) = d at this
      simpa [hbit] using this
    exact congrArg (stageVertex w n) hd.symm
  · have hd : (E d).1.out = d := by
      have := E.left_inv d
      change (if (E d).2 then (E d).1.out else
        edgeFlip _ (E d).1.out) = d at this
      simpa [hbit] using this
    exact congrArg (stageVertex w n) hd.symm

/-- Helper toward Proposition 5.16. The opposite dart's rotation-orbit vertex
is the other endpoint of the quotient geometric edge. -/
theorem kmswStageDrawingDartEdgeDirectionEquiv_head_endpoint
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (d : StageDart (kmswStage w n).nextEdge) :
    kmswStageD39RootedMap_vertexEquiv w n
        (rootedLocallyFiniteVertexClass
          (kmswStageD39RootedMap w n).core.rot
          ((kmswStageD39RootedMap w n).core.edgeInv d)) =
      if (kmswStageDrawingDartEdgeDirectionEquiv P d).2 then
        ((kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.tgt)
          (kmswStageDrawingDartEdgeDirectionEquiv P d).1
      else
        ((kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.src)
          (kmswStageDrawingDartEdgeDirectionEquiv P d).1 := by
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  change stageVertex w n (edgeFlip _ d) =
    if (E d).2 then stageVertex w n (edgeFlip _ (E d).1.out)
    else stageVertex w n (E d).1.out
  cases hb : (E d).2
  · have hd : edgeFlip _ (E d).1.out = d := by
      have := E.left_inv d
      change (if (E d).2 then (E d).1.out else
        edgeFlip _ (E d).1.out) = d at this
      simpa [hb] using this
    have hflip : edgeFlip _ d = (E d).1.out := by
      have := congrArg (edgeFlip (kmswStage w n).nextEdge) hd
      simpa [edgeFlip] using this.symm
    exact congrArg (stageVertex w n) hflip
  · have hd : (E d).1.out = d := by
      have := E.left_inv d
      change (if (E d).2 then (E d).1.out else
        edgeFlip _ (E d).1.out) = d at this
      simpa [hb] using this
    have hflip : edgeFlip _ d = edgeFlip _ (E d).1.out :=
      congrArg (edgeFlip (kmswStage w n).nextEdge) hd.symm
    exact congrArg (stageVertex w n) hflip

/-- Helper toward Proposition 5.16. On every present stage edge, the
quotient dart Boolean agrees with the geometric forward orientation. -/
theorem kmswStageDrawingDartEdgeDirectionEquiv_orientation
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : ¬ (kmswStageD39RootedMap w n).core.missing d) :
    (kmswStageD39RootedMap w n).core.tail d ↔
      (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.forward
        ⟨(kmswStageDrawingDartEdgeDirectionEquiv P d).1,
          (kmswStageDrawingDartEdgeDirectionEquiv_missing P U hU hborder d).not.mpr
            (by
              change ¬ (kmswStageDirectedMap w n).missing d
              exact hd)⟩ =
        (kmswStageDrawingDartEdgeDirectionEquiv P d).2 := by
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  have hd' : ¬ (kmswStageDirectedMap w n).missing d := by
    change ¬ (kmswStageDirectedMap w n).missing d at hd
    exact hd
  have hpresent : (kmswStage w n).present d.1.val = true := by
    change ¬ ((kmswStage w n).present d.1.val = false) at hd'
    cases hp : (kmswStage w n).present d.1.val <;> simp [hp] at hd' ⊢
  change ((kmswStage w n).present d.1.val = true ∧ d.2 = false) ↔
    (!((E d).1.out).2) = (E d).2
  have hrec := E.left_inv d
  change (if (E d).2 then (E d).1.out else
    edgeFlip _ (E d).1.out) = d at hrec
  cases hb : (E d).2
  · have hrep : d = edgeFlip _ (E d).1.out := by simpa [hb] using hrec.symm
    have hbit : d.2 = !((E d).1.out).2 := by
      simpa [edgeFlip] using congrArg Prod.snd hrep
    simp [hpresent, hb, hbit]
  · have hrep : d = (E d).1.out := by simpa [hb] using hrec.symm
    have hbit : d.2 = (E d).1.out.2 := congrArg Prod.snd hrep
    simp [hpresent, hb, hbit]

/-- Helper toward Proposition 5.16. Each stage dart has a unique geometric
face immediately to its left in the stage drawing. -/
theorem kmswStageDrawing_dartBorders_existsUnique
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) :
    ∃! F : P.Face, P.dartBorders d F := by
  have hvert := kmswStageDrawing_vertex_surjective w n
  obtain ⟨F, hF⟩ := P.dartBorders_exists_of_wedge_compl d
    (P.wedgeIn_compl_image hvert (P.arc d).start
      (P.arc d).initialDirection (P.initial_nonzero d))
  exact ⟨F, hF, fun G hG => P.dartBorders_face_unique d G F hG hF⟩

/-- Helper toward Proposition 5.16. Assign a stage dart the face selected by
the proved existence and uniqueness of its left bordering face. -/
noncomputable def kmswStageDrawing_leftFace
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) : P.Face :=
  (kmswStageDrawing_dartBorders_existsUnique P d).exists.choose

/-- Helper toward Proposition 5.16. The chosen left face is characterized
exactly by the drawing's dart-border predicate. -/
theorem kmswStageDrawing_leftFace_eq_iff
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) (F : P.Face) :
    kmswStageDrawing_leftFace P d = F ↔ P.dartBorders d F := by
  have hs : P.dartBorders d (kmswStageDrawing_leftFace P d) :=
    (kmswStageDrawing_dartBorders_existsUnique P d).exists.choose_spec
  constructor
  · intro h
    exact h ▸ hs
  · intro h
    exact P.dartBorders_face_unique d _ F hs h

/-- Helper toward Proposition 5.16. Every complementary face of the finite
stage drawing is the left face of some stage dart. -/
theorem kmswStageDrawing_leftFace_surjective
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) :
    Function.Surjective (kmswStageDrawing_leftFace P) := by
  intro F
  obtain ⟨d, hd⟩ := P.face_has_bordering_dart
    (kmswStageDrawing_vertex_surjective w n) (kmswRootedStage w n).root F
  exact ⟨d, (kmswStageDrawing_leftFace_eq_iff P d F).2 hd⟩

































































end DirectedDistances.PaperProofs.Section5

end
