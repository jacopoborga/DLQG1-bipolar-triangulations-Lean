/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.TwoSidedDrawingFaceClassification
public import DirectedDistances.KMSW.StageTriangleCapSideForced
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary

/-! Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits
of the one-sided KMSW drawing); not a paper result. Sources: -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor
orbits of the one-sided KMSW drawing); not a paper result. Sources:
Each creation triangle's three oriented darts border a common face. This statement does
not identify that face as the bounded cap face; see `capFace_spec` in
`MonotoneFamilyFaceOrbitsCap.lean` and the identification and boundedness results in
`MonotoneFamilyFaceOrbitsIff.lean`. -/
theorem triangle_darts_border_common_face (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let t := stageTriangleDartTriple w j
    ∃ F : P.Face, P.dartBorders t.1 F ∧ P.dartBorders t.2.1 F ∧
      P.dartBorders t.2.2 F := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let t := stageTriangleDartTriple w j
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  obtain ⟨F, _, hborder⟩ := stageTriangleDarts_border_creation_cap w hfin j i hi
  refine ⟨F.val, ?_, ?_, ?_⟩
  · apply hborder t.1
    change t.1 ∈ [t.1, t.2.1, t.2.2]
    simp
  · apply hborder t.2.1
    change t.2.1 ∈ [t.1, t.2.1, t.2.2]
    simp
  · apply hborder t.2.2
    change t.2.2 ∈ [t.1, t.2.1, t.2.2]
    simp

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor
orbits of the one-sided KMSW drawing); not a paper result. Sources:
The external face-successor orbit is exactly the set of darts bordering an
unbounded face, with both darts bordering the unique unbounded face.
This assumes `h : BoundaryHitWitnesses w`, supplying both left and right coordinate hits. -/
theorem faceOrbit_outer_iff_common_unbounded_face (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d e : ℕ × Bool) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    ((kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d ∧
      (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart e) ↔
      ∃ F : P.Face, P.IsUnbounded F ∧ P.dartBorders d F ∧ P.dartBorders e F := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨U, hU, huniq, hborder, _, _, _⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided w hfin h
  constructor
  · rintro ⟨hd, he⟩
    exact ⟨U, hU, (hborder d).2 hd, (hborder e).2 he⟩
  · rintro ⟨F, hF, hd, he⟩
    have hFU : F = U := huniq F hF
    subst F
    exact ⟨(hborder d).1 hd, (hborder e).1 he⟩

end DirectedDistances.KMSW
