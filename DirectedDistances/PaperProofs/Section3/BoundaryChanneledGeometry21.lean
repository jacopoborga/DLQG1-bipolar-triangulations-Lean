/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry20

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the indexed UL and LR darts are present
edges with the orientations required by their respective infinite-side
predicates. The face-side and successor clauses are separate obligations. -/
theorem boundaryChanneledPresentation_sideDarts_oriented21
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) :
    (∀ i : Fin ℓ,
      ∃ hp : ¬ (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.missing
          (boundaryChanneledLeftDart R G i).1,
        (boundaryChanneledLeftDart R G i).2 =
          (boundaryChanneledPlaneMap R G).forward
            ⟨(boundaryChanneledLeftDart R G i).1, hp⟩) ∧
    (∀ i : Fin r,
      ∃ hp : ¬ (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.missing
          (boundaryChanneledRightDart R G i).1,
        (boundaryChanneledRightDart R G i).2 =
          !((boundaryChanneledPlaneMap R G).forward
            ⟨(boundaryChanneledRightDart R G i).1, hp⟩)) := by
  constructor
  · intro i
    let d := boundaryPathDart R.B.leftPath i
    have htail : R.B.map.tail d := by
      simpa [d, boundaryPathDart] using
        (R.B.leftPath.edge_step
          ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.is_lt⟩).2.1
    refine ⟨boundaryChanneledPlaneMap_noMissing R G _, ?_⟩
    have hpair := boundaryChanneledLeftDart_eq_encodedPath20 R G i
    simpa only [← hpair, boundaryChanneledPlaneMap] using
      (boundaryChanneledDartPairEquiv_forward20 R G d htail)
  · intro i
    let p := R.B.rightPath.darts.reverse.get
      ⟨i.val, by
        rw [List.length_reverse, R.B.rightPath.darts_length]
        exact i.is_lt⟩
    have hmem : p ∈ R.B.rightPath.darts :=
      List.mem_reverse.mp (List.get_mem _ _)
    have htail : R.B.map.tail p := by
      rcases List.mem_iff_get.mp hmem with ⟨j, hj⟩
      rw [← hj]
      exact (R.B.rightPath.edge_step j).2.1
    refine ⟨boundaryChanneledPlaneMap_noMissing R G _, ?_⟩
    have hpair := boundaryChanneledRightDart_eq_encodedReverse20 R G i
    have hside := boundaryChanneledDartPairEquiv_forward20 R G p htail
    simpa only [← hpair, boundaryChanneledDartPairEquiv19_flip,
      boundaryChanneledPlaneMap] using congrArg Bool.not hside

/-- Helper toward Definition 3.2: the marked outer face supplies an external
map face, and its source drawing has the left and right winding tests on the
two indexed boundary paths. This records the source-side geometry before its
transfer to the map's `LeftOf` and `RightOf` predicates. -/
theorem boundaryChanneledPresentation_sourceSideData21
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∃ F : (Drawing (boundaryChanneledPlaneMap R G)).Face,
      F.val = (boundaryChanneledMarkedOuterFace R G).val ∧
      (Drawing (boundaryChanneledPlaneMap R G)).IsExternal F ∧
      (∀ i : Fin ℓ, ∀ s : {t : unitInterval // t ∈ openParams},
        LeftAtOn F.val
          (G.arc (boundaryPathDart R.B.leftPath i)).toPath s) ∧
      (∀ i : Fin r, ∀ s : {t : unitInterval // t ∈ openParams},
        RightAtOn F.val
          (G.arc (R.B.rightPath.darts.reverse.get
            ⟨i.val, by
              rw [List.length_reverse, R.B.rightPath.darts_length]
              exact i.is_lt⟩)).toPath s) := by
  let F := G.toPlaneGraphDrawingFaceEquiv.symm
    (boundaryChanneledMarkedOuterFace R G)
  have hFval : F.val = (boundaryChanneledMarkedOuterFace R G).val := rfl
  have hFext : (Drawing (boundaryChanneledPlaneMap R G)).IsExternal F := by
    exact (G.toPlaneGraphDrawing_isExternal_iff F).2 (by
      simpa [F] using hOuterUnbounded)
  refine ⟨F, hFval, hFext, ?_, ?_⟩
  · intro i s
    apply G.dartBorders_toPath_leftAtOn
      (boundaryChanneled_dartTailVertex_surjective R)
    exact boundaryChanneled_leftPath_dartBorders_markedOuterFace R G
      (boundaryPathDart R.B.leftPath i) (List.get_mem _ _)
  · intro i s
    let p := R.B.rightPath.darts.reverse.get
      ⟨i.val, by
        rw [List.length_reverse, R.B.rightPath.darts_length]
        exact i.is_lt⟩
    apply G.dartBorders_flip_toPath_rightAtOn
      (boundaryChanneled_dartTailVertex_surjective R) p
      (boundaryChanneledMarkedOuterFace R G)
    apply boundaryChanneled_reversedRightPath_dartBorders_markedOuterFace R G
    exact List.mem_map.mpr ⟨p, List.get_mem _ _, rfl⟩

/-- Helper toward Definition 3.2: consecutive indexed upper-left darts join
at their common vertex. -/
theorem boundaryChanneledPresentation_upperLeft_successorsJoin21
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) :
    ∀ i j : Fin ℓ,
      (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.next i =
        some j →
      boundaryDartTerminal (boundaryChanneledPlaneMap R G)
          (boundaryChanneledLeftDart R G i) =
        boundaryDartInitial (boundaryChanneledPlaneMap R G)
          (boundaryChanneledLeftDart R G j) := by
  intro i j hnext
  have hidx : j.val = i.val + 1 := by
    change (if h : i.val + 1 < ℓ then some ⟨i.val + 1, h⟩ else none) =
      some j at hnext
    split at hnext
    · injection hnext with heq
      subst j
      rfl
    · cases hnext
  rw [boundaryChanneledLeftDart_terminal,
    boundaryChanneledLeftDart_initial]
  have hhead : R.B.leftPath.vertices[i.val + 1]'(by
      rw [R.B.leftPath.vertices_length]
      exact Nat.succ_lt_succ i.is_lt) =
    dartHeadVertex R.B.map (boundaryPathDart R.B.leftPath i) := by
    simpa [boundaryPathDart] using
      (R.B.leftPath.edge_step
        ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.is_lt⟩).2.2.2
  have htail : R.B.leftPath.vertices[j.val]'(by
      rw [R.B.leftPath.vertices_length]
      exact Nat.lt_succ_of_lt j.is_lt) =
    dartTailVertex R.B.map (boundaryPathDart R.B.leftPath j) := by
    simpa [boundaryPathDart] using
      (R.B.leftPath.edge_step
        ⟨j.val, by rw [R.B.leftPath.darts_length]; exact j.is_lt⟩).2.2.1
  rw [← hhead]
  simpa only [hidx] using htail































end DirectedDistances.PaperProofs.Section3

end
