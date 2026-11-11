/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Intervals2

/-! # Endpoint-bounded successor runs for Definition 3.2

upper-right and lower-left run transitions follow directly from the infinite
external-face successor clauses. The endpoint-bounded characterizations of
nonempty runs remain under investigation. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
variable {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: if the upper-right run is empty, the
successor of a terminal upper-left dart is the first lower-right dart whenever
the lower-right side is nonempty. -/
theorem IsBoundEdges32.infinite_empty_upperRight_to_lowerRight
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.upperLeft.Index}
    (hstop : B.presentation.upperLeft.next i = none)
    [IsEmpty B.presentation.upperRight.Index]
    (hlr : Nonempty B.presentation.lowerRight.Index) :
    ∃ j : B.presentation.lowerRight.Index,
      S (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight j) ∧
      firstOnSide B.presentation (.lowerRight j) ∧
      boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i)) =
        boundaryDartInitial M
          (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight j)) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  let P := B.presentation
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  have htransition := hbase.2.2.2.2.2
  have hstop' : sideNext P (.upperLeft i) = none := by
    simpa [sideNext] using hstop
  have hexists : ∃ k : InfiniteBoundaryDartIndex P,
      S (InfiniteBoundaryDartIndex.dart P (.upperLeft i)) =
        InfiniteBoundaryDartIndex.dart P k := hbase.2.2.2.2.1 (.upperLeft i)
  rcases hexists with ⟨k, hS⟩
  have hstep := htransition (.upperLeft i) k hS
  rcases hstep with hwithin | ⟨_, hfirst, hnext, hjoin⟩
  · rw [hstop'] at hwithin
    cases hwithin
  · cases k with
    | upperLeft k =>
        have hf : False := by
          norm_num [nextNonemptySide, sideTag, sideDistance] at hnext
        exact hf.elim
    | upperRight k => exact isEmptyElim k
    | lowerRight k => exact ⟨k, hS, hfirst, hjoin⟩
    | lowerLeft k =>
        have hskip := hnext.2.2 2
          (by norm_num [sideTag, sideDistance])
          (by norm_num [sideTag, sideDistance])
        have hne : sideNonempty P 2 := by simpa [sideNonempty] using hlr
        exact (hskip hne).elim

/-- Helper toward Definition 3.2: if the lower-left run is empty, the
successor of a terminal lower-right dart is the first upper-left dart whenever
the upper-left side is nonempty. -/
theorem IsBoundEdges32.infinite_empty_lowerLeft_to_upperLeft
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.lowerRight.Index}
    (hstop : B.presentation.lowerRight.next i = none)
    [IsEmpty B.presentation.lowerLeft.Index]
    (hul : Nonempty B.presentation.upperLeft.Index) :
    ∃ j : B.presentation.upperLeft.Index,
      S (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft j) ∧
      firstOnSide B.presentation (.upperLeft j) ∧
      boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i)) =
        boundaryDartInitial M
          (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft j)) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  let P := B.presentation
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  have htransition := hbase.2.2.2.2.2
  have hstop' : sideNext P (.lowerRight i) = none := by
    simpa [sideNext] using hstop
  have hexists : ∃ k : InfiniteBoundaryDartIndex P,
      S (InfiniteBoundaryDartIndex.dart P (.lowerRight i)) =
        InfiniteBoundaryDartIndex.dart P k := hbase.2.2.2.2.1 (.lowerRight i)
  rcases hexists with ⟨k, hS⟩
  have hstep := htransition (.lowerRight i) k hS
  rcases hstep with hwithin | ⟨_, hfirst, hnext, hjoin⟩
  · rw [hstop'] at hwithin
    cases hwithin
  · cases k with
    | upperLeft k => exact ⟨k, hS, hfirst, hjoin⟩
    | upperRight k =>
        have hskip := hnext.2.2 0
          (by norm_num [sideTag, sideDistance])
          (by norm_num [sideTag, sideDistance])
        have hne : sideNonempty P 0 := by
          simpa [sideNonempty] using hul
        exact (hskip hne).elim
    | lowerRight k =>
        have hf : False := by
          norm_num [nextNonemptySide, sideTag, sideDistance] at hnext
        exact hf.elim
    | lowerLeft k => exact isEmptyElim k

/-- Helper toward Definition 3.2: an empty upper-right index has no edge in
the supplied upper-right boundary set. -/
theorem upperRightBoundary32_eq_empty_of_isEmpty
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    [IsEmpty B.presentation.upperRight.Index] :
    upperRightBoundary32 B = ∅ := by
  ext e
  simp only [upperRightBoundary32, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨i, _⟩
  exact isEmptyElim i

/-- Helper toward Definition 3.2: an empty lower-left index has no edge in
the supplied lower-left boundary set. -/
theorem lowerLeftBoundary32_eq_empty_of_isEmpty
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    [IsEmpty B.presentation.lowerLeft.Index] :
    lowerLeftBoundary32 B = ∅ := by
  ext e
  simp only [lowerLeftBoundary32, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨i, _⟩
  exact isEmptyElim i




























































end DirectedDistances.PlanarMap

end
