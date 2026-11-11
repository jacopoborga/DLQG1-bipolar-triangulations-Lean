/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation14
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation17

/-! Helper toward Definition 3.2: finite outer-word positions. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the four side runs concatenate to the outer word. -/
theorem kmswStageFiniteBoundaryPresentation21_word (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWord w n = kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
      kmswStageLRDartRun w n ++ kmswStageLLDartRun w n := by
  simp [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
    kmswStageLRDartRun, kmswStageLLDartRun]

/-- Helper toward Definition 3.2: outer darts are indexed by `idxOf`, with inverse `get`. -/
@[expose] def kmswStageFiniteBoundaryPresentation21_outerEquiv
    (w : ℕ → Fin 3) (n : ℕ) :
    {d : StageDart (kmswStage w n).nextEdge //
      (kmswStageDirectedMap w n).IsOuter d} ≃ Fin (stageOuterWord w n).length where
  toFun d := ⟨(stageOuterWord w n).idxOf d.val,
    List.idxOf_lt_length_iff.mpr ((kmsw_stage_outer_face_exact w n d.val).1 d.property)⟩
  invFun i := ⟨(stageOuterWord w n).get i,
    (kmsw_stage_outer_face_exact w n _).2 (List.get_mem _ _)⟩
  left_inv _d := Subtype.ext (List.idxOf_get _)
  right_inv i := Fin.ext (List.get_idxOf (stageOuterWord_nodup w n) i)

variable (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))

/-- Helper toward Definition 3.2: natural positions at the four concatenated run offsets. -/
@[expose] def kmswStageFiniteBoundaryPresentation21_position :
    InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J) →
      Fin (stageOuterWord w n).length
  | .upperLeft i => ⟨i.val, by
      rw [kmswStageFiniteBoundaryPresentation21_word]; simp only [List.length_append]
      have := i.isLt; change i.val < (kmswStageULDartRun w n).length at this; omega⟩
  | .upperRight i => ⟨(kmswStageULDartRun w n).length + i.val, by
      rw [kmswStageFiniteBoundaryPresentation21_word]; simp only [List.length_append]
      have := i.isLt; change i.val < (kmswStageURDartRun w n).length at this; omega⟩
  | .lowerRight i => ⟨(kmswStageULDartRun w n).length +
      (kmswStageURDartRun w n).length + i.val, by
      rw [kmswStageFiniteBoundaryPresentation21_word]; simp only [List.length_append]
      have := i.isLt; change i.val < (kmswStageLRDartRun w n).length at this; omega⟩
  | .lowerLeft i => ⟨(kmswStageULDartRun w n).length +
      (kmswStageURDartRun w n).length + (kmswStageLRDartRun w n).length + i.val, by
      rw [kmswStageFiniteBoundaryPresentation21_word]; simp only [List.length_append]
      have := i.isLt; change i.val < (kmswStageLLDartRun w n).length at this; omega⟩

/-- Helper toward Definition 3.2: reading the outer word at a side position recovers its dart. -/
theorem kmswStageFiniteBoundaryPresentation21_get_position
    (i : InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J)) :
    (stageOuterWord w n).get (kmswStageFiniteBoundaryPresentation21_position w n M J i) =
      InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) i := by
  cases i <;> rename_i i
  all_goals
    simp [kmswStageFiniteBoundaryPresentation21_position,
      kmswStageFiniteBoundaryPresentation21_word, InfiniteBoundaryDartIndex.dart_eq,
      kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide, List.get_eq_getElem,
      Nat.add_assoc, i.isLt]

/-- Helper toward Definition 3.2: the offset position is exactly `idxOf` in the outer word. -/
theorem kmswStageFiniteBoundaryPresentation21_position_eq_idxOf
    (i : InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J)) :
    (kmswStageFiniteBoundaryPresentation21_position w n M J i).val =
      (stageOuterWord w n).idxOf
        (InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) i) := by
  rw [← kmswStageFiniteBoundaryPresentation21_get_position w n M J i]
  exact (List.get_idxOf (stageOuterWord_nodup w n) _).symm

/-- Helper toward Definition 3.2: the side positions enumerate the whole finite outer cycle. -/
theorem kmswStageFiniteBoundaryPresentation21_position_bijective :
    Function.Bijective (kmswStageFiniteBoundaryPresentation21_position w n M J) := by
  constructor
  · intro i j hij
    apply kmswStageFiniteBoundaryPresentation_dart_injective w n M J
    rw [← kmswStageFiniteBoundaryPresentation21_get_position w n M J i,
      ← kmswStageFiniteBoundaryPresentation21_get_position w n M J j, hij]
  · intro k
    have hk := k.isLt
    simp only [kmswStageFiniteBoundaryPresentation21_word, List.length_append] at hk
    by_cases h₁ : k.val < (kmswStageULDartRun w n).length
    · exact ⟨.upperLeft ⟨k.val, h₁⟩, Fin.ext rfl⟩
    · by_cases h₂ : k.val < (kmswStageULDartRun w n).length +
          (kmswStageURDartRun w n).length
      · refine ⟨.upperRight ⟨k.val - (kmswStageULDartRun w n).length, by omega⟩, ?_⟩
        apply Fin.ext; dsimp [kmswStageFiniteBoundaryPresentation21_position]; omega
      · by_cases h₃ : k.val < (kmswStageULDartRun w n).length +
            (kmswStageURDartRun w n).length + (kmswStageLRDartRun w n).length
        · refine ⟨.lowerRight ⟨k.val - ((kmswStageULDartRun w n).length +
            (kmswStageURDartRun w n).length), by omega⟩, ?_⟩
          apply Fin.ext; dsimp [kmswStageFiniteBoundaryPresentation21_position]; omega
        · refine ⟨.lowerLeft ⟨k.val - ((kmswStageULDartRun w n).length +
            (kmswStageURDartRun w n).length + (kmswStageLRDartRun w n).length),
            by omega⟩, ?_⟩
          apply Fin.ext; dsimp [kmswStageFiniteBoundaryPresentation21_position]; omega

/-- Helper toward Definition 3.2: the four-run index type is equivalent to the finite outer cycle. -/
@[expose] noncomputable def kmswStageFiniteBoundaryPresentation21_positionEquiv :
    InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J) ≃
      Fin (stageOuterWord w n).length :=
  Equiv.ofBijective _ (kmswStageFiniteBoundaryPresentation21_position_bijective w n M J)

/-- Helper toward Definition 3.2: a side step increases the outer-word index by exactly one. -/
theorem kmswStageFiniteBoundaryPresentation21_side_step
    (i j : InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J)) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J) i = some j ↔
      sideTag (kmswStageFiniteBoundaryPresentation w n M J) i =
        sideTag (kmswStageFiniteBoundaryPresentation w n M J) j ∧
      (kmswStageFiniteBoundaryPresentation21_position w n M J j).val =
        (kmswStageFiniteBoundaryPresentation21_position w n M J i).val + 1 := by
  cases i <;> cases j <;>
    simp [kmswStageFiniteBoundaryPresentation21_position,
      kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide, kmswFiniteRunNext,
      sideNext, sideTag]
  all_goals
    rename_i j i
    constructor
    · rintro ⟨hlt, heq⟩
      injection heq with hfin
      have hv := congrArg Fin.val hfin
      change j.val + 1 = i.val at hv
      omega
    · intro hpos
      have hval : j.val + 1 = i.val := by omega
      have hi := i.isLt
      refine ⟨by omega, ?_⟩
      apply congrArg _
      apply Fin.ext
      exact hval

/-- Helper toward Definition 3.2: the geometric successor reads the next outer-word entry,
including the closing transition and empty side runs. -/
theorem kmswStageFiniteBoundaryPresentation21_successor_get
    (k : Fin (stageOuterWord w n).length) :
    (stageRot w n).symm (edgeFlip _ ((stageOuterWord w n).get k)) =
      (stageOuterWord w n).get (boundaryCycleSucc4 k) := by
  change (kmswMap w n).faceSucc ((stageOuterWord w n).get k) = _
  rw [stageOuterWord_faceSucc w n _ (List.get_mem _ _)]
  exact List.formPerm_apply_getElem _ (stageOuterWord_nodup w n) k.val k.isLt

/-- Helper toward Definition 3.2: geometric successor equality is precisely cyclic index succession. -/
theorem kmswStageFiniteBoundaryPresentation21_successor_iff
    (i j : InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J)) :
    (stageRot w n).symm (edgeFlip _
        (InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) i)) =
      InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) j ↔
    kmswStageFiniteBoundaryPresentation21_position w n M J j =
      boundaryCycleSucc4 (kmswStageFiniteBoundaryPresentation21_position w n M J i) := by
  rw [← kmswStageFiniteBoundaryPresentation21_get_position w n M J i,
    ← kmswStageFiniteBoundaryPresentation21_get_position w n M J j,
    kmswStageFiniteBoundaryPresentation21_successor_get]
  exact (stageOuterWord_nodup w n).get_inj_iff.trans eq_comm

/-- Helper toward Definition 3.2: the cut before UL orders the side tags monotonically. -/
theorem kmswStageFiniteBoundaryPresentation21_tag_mono
    (i j : InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J))
    (h : (kmswStageFiniteBoundaryPresentation21_position w n M J i).val ≤
      (kmswStageFiniteBoundaryPresentation21_position w n M J j).val) :
    (sideTag (kmswStageFiniteBoundaryPresentation w n M J) i).val ≤
      (sideTag (kmswStageFiniteBoundaryPresentation w n M J) j).val := by
  cases i <;> cases j <;>
    simp [kmswStageFiniteBoundaryPresentation21_position,
      sideTag] at h ⊢ <;>
    omega

/-- Helper toward Definition 3.2: the finite outer-word presentation has the exact
cyclic position order required by Presentation17, for every supplied realization. -/
theorem kmswStageFiniteBoundaryPresentation17_finite_position_order
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    FiniteBoundaryPositionOrder4
      (kmswStageFiniteBoundaryPresentation w n M J)
      (fun d => (stageRot w n).symm (d.1, !d.2)) := by
  clear hreal hborder hU U P
  let e := kmswStageFiniteBoundaryPresentation21_positionEquiv w n M J
  have he (i) : e i = kmswStageFiniteBoundaryPresentation21_position w n M J i := rfl
  have hpos : 0 < (stageOuterWord w n).length :=
    List.length_pos_iff.mpr (stageOuterWord_nonempty w n)
  let cut : Fin (stageOuterWord w n).length := ⟨0, hpos⟩
  have hoff (k : Fin (stageOuterWord w n).length) :
      boundaryCycleOffset4 cut k = k.val := by
    simp [boundaryCycleOffset4, cut, Nat.mod_eq_of_lt k.isLt]
  refine ⟨(stageOuterWord w n).length, e, ?_, Or.inr ⟨cut, ?_, ?_⟩⟩
  · intro i j
    exact kmswStageFiniteBoundaryPresentation21_successor_iff w n M J i j
  · intro i j hij
    simp only [hoff] at hij
    apply kmswStageFiniteBoundaryPresentation21_tag_mono w n M J
    change (e (e.symm i)).val ≤ (e (e.symm j)).val
    simpa only [e.apply_symm_apply] using hij
  · intro i j
    simp only [hoff, he]
    exact kmswStageFiniteBoundaryPresentation21_side_step w n M J i j

/-- Helper toward Definition 3.2: the Presentation14 package with its finite-position
premise discharged. Boundary order, side geometry and junction labels remain explicit
open clauses; this helper makes no paper-completion claim. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses21
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (_hU : P.IsUnbounded U)
      (_hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      ULOkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      UROkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LROkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LLOkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
      RequiredFiniteBoundaryJoinEndpointLabels7
        (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
      (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (Fin (kmswStage w n).nextEdge × Bool))
      (G : PLDrawing (Fin (kmswStage w n).nextEdge × Bool)
        (Fin (kmswStage w n).nextVertex) (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial M)) (U : G.Face)
      (S : Fin (kmswStage w n).nextEdge × Bool → Fin (kmswStage w n).nextEdge × Bool),
      kmsw_stage_map_realization32 w n P M ∧
      B = kmswStageFiniteBoundaryPresentationWithJunctions w n M J ∧
      G.image = P.image ∧ IsBoundEdges32 M B G U S := by
  obtain ⟨P, U, hU, hborder, hpackage⟩ :=
    exists_kmswStage_bound_edges32_of_open_clauses14 w n
  refine ⟨P, U, hU, hborder, ?_⟩
  intro hboundary hUL hUR hLR hLL hjoin
  exact hpackage hboundary hUL hUR hLR hLL
    (fun M J hreal => kmswStageFiniteBoundaryPresentation17_finite_position_order
      w n P U hU hborder M J hreal) hjoin

end DirectedDistances.PaperProofs.Section3

end
