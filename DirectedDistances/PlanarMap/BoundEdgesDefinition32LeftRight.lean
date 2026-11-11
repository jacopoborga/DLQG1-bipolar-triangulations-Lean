/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32
public import DirectedDistances.PlanarMap.FiniteAcyclicPoles

/-! # Left and right boundary names

orientation is bipolar and there are no missing edges, the upper-left and
lower-right boundaries are called the left and right boundaries. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
variable {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: the name for the upper-left boundary in the -/
@[expose] def leftBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) : Set E :=
  upperLeftBoundary32 B

/-- Helper toward Definition 3.2: the name for the lower-right boundary in -/
@[expose] def rightBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) : Set E :=
  lowerRightBoundary32 B

variable {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: if no geometric edge is missing, the
upper-right run in a supplied v7 boundary certificate is empty. -/
theorem upperRightBoundary32_eq_empty_of_no_missing_edges
    (hNoMissing : ∀ e, ¬ M.toPlaneMapWithMissing.missing e)
    (h : IsBoundEdges32 M B G U S) :
    upperRightBoundary32 B = ∅ := by
  ext e
  constructor
  · intro he
    exact (hNoMissing e (upperRightBoundary32_missing h he)).elim
  · intro he
    simp at he

/-- Helper toward Definition 3.2: if no geometric edge is missing, the
lower-left run in a supplied v7 boundary certificate is empty. -/
theorem lowerLeftBoundary32_eq_empty_of_no_missing_edges
    (hNoMissing : ∀ e, ¬ M.toPlaneMapWithMissing.missing e)
    (h : IsBoundEdges32 M B G U S) :
    lowerLeftBoundary32 B = ∅ := by
  ext e
  constructor
  · intro he
    exact (hNoMissing e (lowerLeftBoundary32_missing h he)).elim
  · intro he
    simp at he

/-- Helper toward Definition 3.2: under the no-missing-edge condition and
the supplied v7 certificate, the left and right edge sets have their exact
directed dart-border characterizations, and their sides satisfy the supplied
orientation, external-face, and simple-side facts. The upper-right and
lower-left missing-edge runs are empty. -/
theorem leftRightBoundaries32_of_no_missing_edges
    (hNoMissing : ∀ e, ¬ M.toPlaneMapWithMissing.missing e)
    (h : IsBoundEdges32 M B G U S) :
    upperRightBoundary32 B = ∅ ∧
    lowerLeftBoundary32 B = ∅ ∧
    (∀ e, e ∈ leftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, M.forward ⟨e, hp⟩) U) ∧
    (∀ e, e ∈ rightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, !(M.forward ⟨e, hp⟩)) U) ∧
    ULOkInf B.presentation ∧ LROkInf B.presentation ∧
    IsSimpleBoundarySide M B.presentation.upperLeft ∧
    IsSimpleBoundarySide M B.presentation.lowerRight := by
  rcases h.presentation_facts with
    ⟨_, hul, _, hlr, _, hsul, hslr⟩
  refine ⟨upperRightBoundary32_eq_empty_of_no_missing_edges hNoMissing h,
    lowerLeftBoundary32_eq_empty_of_no_missing_edges hNoMissing h, ?_, ?_, hul,
    hlr, hsul, hslr⟩
  · intro e
    change e ∈ upperLeftBoundary32 B ↔ _
    exact mem_upperLeftBoundary32_iff_forward_dartBorders h e
  · intro e
    change e ∈ lowerRightBoundary32 B ↔ _
    exact mem_lowerRightBoundary32_iff_reverse_dartBorders h e

/-- Helper toward Definition 3.2: in the source's bipolar, no-missing-edge
case, the left and right boundaries have the same supplied-certificate
characterization as their upper-left and lower-right sides. -/
theorem leftRightBoundaries32_of_bipolar_no_missing_edges
    (hBipolar : IsBipolarRel M.step)
    (hNoMissing : ∀ e, ¬ M.toPlaneMapWithMissing.missing e)
    (h : IsBoundEdges32 M B G U S) :
    M.IsAcyclic ∧ upperRightBoundary32 B = ∅ ∧
    lowerLeftBoundary32 B = ∅ ∧
    (∀ e, e ∈ leftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, M.forward ⟨e, hp⟩) U) ∧
    (∀ e, e ∈ rightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, !(M.forward ⟨e, hp⟩)) U) ∧
    ULOkInf B.presentation ∧ LROkInf B.presentation ∧
    IsSimpleBoundarySide M B.presentation.upperLeft ∧
    IsSimpleBoundarySide M B.presentation.lowerRight := by
  exact ⟨hBipolar.1,
    leftRightBoundaries32_of_no_missing_edges hNoMissing h⟩

end DirectedDistances.PlanarMap

end
