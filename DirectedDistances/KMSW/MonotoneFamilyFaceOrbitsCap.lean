/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneFamilyFaceOrbits
public import DirectedDistances.KMSW.LimitBoundedFaces
public import DirectedDistances.KMSW.CreationCapExactFrontier
public import DirectedDistances.KMSW.InfiniteTriangulation

/-! Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of the
one-sided KMSW drawing); not a paper result. Source context:
The face-successor convention is the Lean definition `kmswInfFaceSucc` in
`KMSW/InfiniteRotation.lean`; these source lines do not assert the orbit correspondence.

This module names each persistent creation-cap face and records its exact region and the
three known bordering darts. The remaining geometric bridge is to show that every dart
bordering this face is one of those three darts, with the cap on its left. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the one-sided KMSW drawing); not a paper result. Source context:
The face-successor convention is the Lean definition `kmswInfFaceSucc` in
`KMSW/InfiniteRotation.lean`; these source lines do not assert the orbit correspondence.
The creation cap has a unique realized face whose set is the cap region and whose boundary
includes all three oriented darts of the creation triangle. -/
theorem creation_cap_face_existsUnique (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    ∃! F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face,
      F.val =
        ((familyG w (monotone_family_all w) (j.val + 1)).cap
          (stageTriangleRecord_fin_index w j).choose).region ∧
      ∀ d ∈ stageTriangleDartList w j,
        (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F := by
  let i := (stageTriangleRecord_fin_index w j).choose
  have hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j :=
    (stageTriangleRecord_fin_index w j).choose_spec
  obtain ⟨F, hF, hborder⟩ :=
    stageTriangleDarts_border_creation_cap w hfin j i hi
  refine ⟨F.val, ?_, ?_⟩
  · exact ⟨hF, hborder⟩
  · intro G hG
    apply Subtype.ext
    exact (hF.trans hG.1.symm).symm

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the one-sided KMSW drawing); not a paper result. Source context:
The face-successor convention is the Lean definition `kmswInfFaceSucc` in
`KMSW/InfiniteRotation.lean`; these source lines do not assert the orbit correspondence.
The chosen cap face is the unique face with the cap-region and triangle-border
characterization in creation_cap_face_existsUnique. -/
@[expose] noncomputable def capFace (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face :=
  Classical.choose (creation_cap_face_existsUnique w hfin j)

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the one-sided KMSW drawing); not a paper result. Source context:
The face-successor convention is the Lean definition `kmswInfFaceSucc` in
`KMSW/InfiniteRotation.lean`; these source lines do not assert the orbit correspondence.
The selected face has exactly the persistent creation-cap region and all three known
oriented boundary darts. -/
theorem capFace_spec (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    (capFace w hfin j).val =
        ((familyG w (monotone_family_all w) (j.val + 1)).cap
          (stageTriangleRecord_fin_index w j).choose).region ∧
      ∀ d ∈ stageTriangleDartList w j,
        (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d
          (capFace w hfin j) := by
  exact (Classical.choose_spec
    (creation_cap_face_existsUnique w hfin j)).1

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the one-sided KMSW drawing); not a paper result. Source context:
The face-successor convention is the Lean definition `kmswInfFaceSucc` in
`KMSW/InfiniteRotation.lean`; these source lines do not assert the orbit correspondence.
The three creation darts all border the selected persistent cap face. -/
theorem capFace_triangle_darts_border (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let t := stageTriangleDartTriple w j
    P.dartBorders t.1 (capFace w hfin j) ∧
      P.dartBorders t.2.1 (capFace w hfin j) ∧
      P.dartBorders t.2.2 (capFace w hfin j) := by
  have h := (capFace_spec w hfin j).2
  refine ⟨h _ (by simp [stageTriangleDartList]),
    h _ (by simp [stageTriangleDartList]), h _ (by simp [stageTriangleDartList])⟩

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the one-sided KMSW drawing); not a paper result. Source context:
The face-successor convention is the Lean definition `kmswInfFaceSucc` in
`KMSW/InfiniteRotation.lean`; these source lines do not assert the orbit correspondence.
The cap face's frontier consists exactly of the three creation-edge traces. -/
theorem capFace_frontier_eq_creation_arcs (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    frontier (capFace w hfin j).val =
      stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1))
          (stageTriangleRecord w j).1 ∪
        stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1))
          (stageTriangleRecord w j).2.1 ∪
        stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1))
          (stageTriangleRecord w j).2.2 := by
  let i := (stageTriangleRecord_fin_index w j).choose
  have hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j :=
    (stageTriangleRecord_fin_index w j).choose_spec
  rw [(capFace_spec w hfin j).1]
  exact creationCap_frontier_eq_traces w j i hi

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the one-sided KMSW drawing); not a paper result. Source context:
The face-successor convention is the Lean definition `kmswInfFaceSucc` in
`KMSW/InfiniteRotation.lean`; these source lines do not assert the orbit correspondence.
The three creation darts form one cycle of the infinite face successor. -/
theorem capFace_triangle_darts_sameCycle (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    let t := stageTriangleDartTriple w j
    FaceSucc3Cycle (kmswInfFaceSucc w hfin) t.1 t.2.1 t.2.2 :=
  kmswInfFaceSucc_stageTriangle_cycle w hfin j

end DirectedDistances.KMSW

