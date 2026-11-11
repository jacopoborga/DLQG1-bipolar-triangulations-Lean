/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsFull
public import DirectedDistances.KMSW.MonotoneFamilyCapBounded

/-! not a paper result. This file records creation-orbit exclusion and the bounded-face iff. -/

public section
namespace DirectedDistances.KMSW

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

/-- Helper toward the M_{0,infinity} face correspondence
The premise `h : BoundaryHitWitnesses w` is the two-sided recurrent iid regime.
No creation dart belongs to the outer face-successor orbit. -/
theorem creation_dart_not_outer (h : BoundaryHitWitnesses w)
    (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : d ∈ stageTriangleDartList w j) :
    ¬ (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨U, hU, _, hborder, _, _, _⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided w hfin h
  have hdCap : P.dartBorders d (capFace w hfin j) :=
    (cap_border_iff w hfin j d).2 hd
  intro hdOuter
  have hdU : P.dartBorders d U := (hborder d).2 hdOuter
  have hcapU := dart_border_face_unique w hfin d (capFace w hfin j) U hdCap hdU
  exact capFace_not_unbounded w hfin j (hcapU.symm ▸ hU)

/-- Helper toward the M_{0,infinity} face correspondence
The selected creation cap is not unbounded; this re-exports its boundedness proof. -/
theorem capFace_isBounded_face (j : TriangleCreationTime w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    ¬ P.IsUnbounded (capFace w hfin j) := by
  exact capFace_not_unbounded w hfin j

/-- Helper toward the M_{0,infinity} face correspondence
The premise `h : BoundaryHitWitnesses w` is the two-sided recurrent iid regime.
A realized face is bounded exactly when it is one of the creation cap faces. -/
theorem boundedFace_iff_creation_orbit (h : BoundaryHitWitnesses w)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    ¬ P.IsUnbounded F ↔ ∃ j : TriangleCreationTime w, F = capFace w hfin j := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  constructor
  · intro hF
    obtain ⟨j, hborderEq, _, _, _⟩ :=
      boundedFace_orbit_is_triangle w hfin h F hF
    let d := (stageTriangleDartTriple w j).1
    have hdF : P.dartBorders d F := by
      have hmem : d ∈ {x | P.dartBorders x F} := by
        rw [hborderEq]
        simp [d, stageTriangleDartList]
      exact hmem
    have hdCap : P.dartBorders d (capFace w hfin j) :=
      (cap_border_iff w hfin j d).2 (by simp [d, stageTriangleDartList])
    exact ⟨j, dart_border_face_unique w hfin d F (capFace w hfin j) hdF hdCap⟩
  · rintro ⟨j, rfl⟩
    exact capFace_not_unbounded w hfin j

/-- Helper toward the M_{0,infinity} face correspondence
The premise `h : BoundaryHitWitnesses w` is the two-sided recurrent iid regime.
Every geometric dart is either outer or belongs to one creation triangle, exclusively. -/
theorem dart_outer_or_creation (h : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    Xor ((kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d)
      (∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j) := by
  classical
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  by_cases hdOuter : (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d
  · apply Or.inl
    refine ⟨hdOuter, ?_⟩
    rintro ⟨j, hdTriangle⟩
    exact creation_dart_not_outer w hfin h j d hdTriangle hdOuter
  · obtain ⟨F, hdF⟩ := dart_borders_exists w hfin h d
    have hbounded : ¬ P.IsUnbounded F := by
      intro hF
      obtain ⟨U, _, huniq, hborder, _, _, _⟩ :=
        monotoneFamilyDrawing_realized_boundary_twoSided w hfin h
      have hdU : P.dartBorders d U := huniq F hF ▸ hdF
      exact hdOuter ((hborder d).1 hdU)
    obtain ⟨j, hborderEq, _, _, _⟩ :=
      boundedFace_orbit_is_triangle w hfin h F hbounded
    have hdTriangle : d ∈ stageTriangleDartList w j := by
      change d ∈ {x | P.dartBorders x F} at hdF
      rw [hborderEq] at hdF
      exact hdF
    exact Or.inr ⟨⟨j, hdTriangle⟩, hdOuter⟩

end DirectedDistances.KMSW
