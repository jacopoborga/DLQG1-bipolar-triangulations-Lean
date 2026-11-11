/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32







public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
variable {M : DirectedPlaneMapWithMissing V E}
variable {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
variable {rot : Equiv.Perm (E × Bool)}
variable {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
  (boundaryDartInitial M)}
variable {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: every edge in either supplied missing
boundary run is missing in the directed map. -/
theorem IsBoundEdges32.missing_boundary_runs
    (h : IsBoundEdges32 M B G U S) :
    (∀ e, e ∈ upperRightBoundary32 B → M.toPlaneMapWithMissing.missing e) ∧
      ∀ e, e ∈ lowerLeftBoundary32 B → M.toPlaneMapWithMissing.missing e := by
  exact ⟨fun e he => upperRightBoundary32_missing h he,
    fun e he => lowerLeftBoundary32_missing h he⟩

/-- Helper toward Definition 3.2: if the external successor leaves an upper-left
dart and the upper-right side is nonempty, its next boundary dart is on the
upper-right side. -/
theorem nextNonemptySide_upperLeft
    {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {j : InfiniteBoundaryDartIndex P}
    (h : nextNonemptySide P 0 (sideTag P j))
    (hur : Nonempty P.upperRight.Index) :
    ∃ k, j = .upperRight k := by
  cases j with
  | upperLeft k =>
      have hdist := h.2.1
      have hf : False := by norm_num [sideTag, sideDistance] at hdist
      exact False.elim hf
  | upperRight k => exact ⟨k, rfl⟩
  | lowerRight k =>
      have hskip := h.2.2 1 (by norm_num [sideTag, sideDistance])
        (by norm_num [sideTag, sideDistance])
      have hne : sideNonempty P 1 := by simpa [sideNonempty] using hur
      exact (hskip hne).elim
  | lowerLeft k =>
      have hskip := h.2.2 1 (by norm_num [sideTag, sideDistance])
        (by norm_num [sideTag, sideDistance])
      have hne : sideNonempty P 1 := by simpa [sideNonempty] using hur
      exact (hskip hne).elim

/-- Helper toward Definition 3.2: if the external successor leaves an
upper-right dart and the lower-right side is nonempty, its next boundary dart
is on the lower-right side. -/
theorem nextNonemptySide_upperRight
    {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {j : InfiniteBoundaryDartIndex P}
    (h : nextNonemptySide P 1 (sideTag P j))
    (hlr : Nonempty P.lowerRight.Index) :
    ∃ k, j = .lowerRight k := by
  cases j with
  | upperLeft k =>
      have hskip := h.2.2 2 (by norm_num [sideTag, sideDistance])
        (by norm_num [sideTag, sideDistance])
      have hne : sideNonempty P 2 := by simpa [sideNonempty] using hlr
      exact (hskip hne).elim
  | upperRight k =>
      have hdist := h.2.1
      have hf : False := by norm_num [sideTag, sideDistance] at hdist
      exact False.elim hf
  | lowerRight k => exact ⟨k, rfl⟩
  | lowerLeft k =>
      have hskip := h.2.2 2 (by norm_num [sideTag, sideDistance])
        (by norm_num [sideTag, sideDistance])
      have hne : sideNonempty P 2 := by simpa [sideNonempty] using hlr
      exact (hskip hne).elim

/-- Helper toward Definition 3.2: if the external successor leaves a
lower-left dart and the upper-left side is nonempty, its next boundary dart
is on the upper-left side. -/
theorem nextNonemptySide_lowerLeft
    {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {j : InfiniteBoundaryDartIndex P}
    (h : nextNonemptySide P 3 (sideTag P j))
    (hul : Nonempty P.upperLeft.Index) :
    ∃ k, j = .upperLeft k := by
  cases j with
  | upperLeft k => exact ⟨k, rfl⟩
  | upperRight k =>
      have hskip := h.2.2 0 (by norm_num [sideTag, sideDistance])
        (by norm_num [sideTag, sideDistance])
      have hne : sideNonempty P 0 := by simpa [sideNonempty] using hul
      exact (hskip hne).elim
  | lowerRight k =>
      have hskip := h.2.2 0 (by norm_num [sideTag, sideDistance])
        (by norm_num [sideTag, sideDistance])
      have hne : sideNonempty P 0 := by simpa [sideNonempty] using hul
      exact (hskip hne).elim
  | lowerLeft k =>
      have hdist := h.2.1
      have hf : False := by norm_num [sideTag, sideDistance] at hdist
      exact False.elim hf

/-- Helper toward Definition 3.2: each within-side step in the infinite
presentation is exactly the geometric external successor step, with matching
terminal and initial vertices. -/
theorem IsBoundEdges32.infinite_within_side_step
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i j : InfiniteBoundaryDartIndex B.presentation}
    (hnext : sideNext B.presentation i = some j) :
    S (InfiniteBoundaryDartIndex.dart B.presentation i) =
        InfiniteBoundaryDartIndex.dart B.presentation j ∧
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart B.presentation i) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart B.presentation j) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  exact hbase.2.2.2.1 i j hnext

/-- Helper toward Definition 3.2: when the infinite external successor joins
UL directly to LR, the skipped empty UR path retains both endpoint labels at
the join vertex. -/
theorem IsBoundEdges32.infinite_empty_upperRight_at_ul_lr_join
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.upperLeft.Index}
    {j : B.presentation.lowerRight.Index}
    (hstop : B.presentation.upperLeft.next i = none)
    (hS : S (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i)) =
      InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight j)) :
    B.presentation.upperRight.initialVertex? =
        some (boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i))) ∧
      B.presentation.upperRight.terminalVertex? =
        some (boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i))) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  let P := B.presentation
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  have htransition := hbase.2.2.2.2.2
  have hstop' : sideNext P (.upperLeft i) = none := by
    simpa [sideNext] using hstop
  have hstep := htransition (.upperLeft i) (.lowerRight j) hS
  rcases hstep with hwithin | ⟨_, _, hnext, _⟩
  · rw [hstop'] at hwithin
    cases hwithin
  · have hlabels := h3.2.2 (.upperLeft i) (.lowerRight j) hS hstop' hnext
    exact hlabels.2.2 1 (by norm_num [sideTag, sideDistance])
      (by norm_num [sideTag, sideDistance])

/-- Helper toward Definition 3.2: when the infinite external successor joins
LR directly to UL, the skipped empty LL path retains both endpoint labels at
the join vertex. -/
theorem IsBoundEdges32.infinite_empty_lowerLeft_at_lr_ul_join
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.lowerRight.Index}
    {j : B.presentation.upperLeft.Index}
    (hstop : B.presentation.lowerRight.next i = none)
    (hS : S (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i)) =
      InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft j)) :
    B.presentation.lowerLeft.initialVertex? =
        some (boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i))) ∧
      B.presentation.lowerLeft.terminalVertex? =
        some (boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i))) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  let P := B.presentation
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  have htransition := hbase.2.2.2.2.2
  have hstop' : sideNext P (.lowerRight i) = none := by
    simpa [sideNext] using hstop
  have hstep := htransition (.lowerRight i) (.upperLeft j) hS
  rcases hstep with hwithin | ⟨_, _, hnext, _⟩
  · rw [hstop'] at hwithin
    cases hwithin
  · have hlabels := h3.2.2 (.lowerRight i) (.upperLeft j) hS hstop' hnext
    exact hlabels.2.2 3 (by norm_num [sideTag, sideDistance])
      (by norm_num [sideTag, sideDistance])

/-- Helper toward Definition 3.2: in the infinite branch, the successor of a
terminal upper-left dart is the first dart of the upper-right run whenever
that run is nonempty, and the junction vertices agree. -/
theorem IsBoundEdges32.infinite_upperLeft_to_upperRight
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.upperLeft.Index}
    (hstop : B.presentation.upperLeft.next i = none)
    (hur : Nonempty B.presentation.upperRight.Index) :
    ∃ j : B.presentation.upperRight.Index,
      S (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.upperRight j) ∧
      firstOnSide B.presentation (.upperRight j) ∧
      boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i)) =
        boundaryDartInitial M
          (InfiniteBoundaryDartIndex.dart B.presentation (.upperRight j)) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  let P := B.presentation
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  have htransition := hbase.2.2.2.2.2
  have hstop' : sideNext P (.upperLeft i) = none := by
    simpa [sideNext] using hstop
  have hexists : ∃ j : InfiniteBoundaryDartIndex P,
      S (InfiniteBoundaryDartIndex.dart P (.upperLeft i)) =
        InfiniteBoundaryDartIndex.dart P j := hbase.2.2.2.2.1 (.upperLeft i)
  rcases hexists with ⟨j, hS⟩
  have hstep := htransition (.upperLeft i) j hS
  rcases hstep with hwithin | ⟨_, hfirst, hnext, hjoin⟩
  · rw [hstop'] at hwithin
    cases hwithin
  · obtain ⟨jUR, rfl⟩ := nextNonemptySide_upperLeft hnext hur
    exact ⟨jUR, hS, hfirst, hjoin⟩

/-- Helper toward Definition 3.2: a terminal upper-right dart enters the
lower-right run in the infinite branch when that run is nonempty. -/
theorem IsBoundEdges32.infinite_upperRight_to_lowerRight
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.upperRight.Index}
    (hstop : B.presentation.upperRight.next i = none)
    (hlr : Nonempty B.presentation.lowerRight.Index) :
    ∃ j : B.presentation.lowerRight.Index,
      S (InfiniteBoundaryDartIndex.dart B.presentation (.upperRight i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight j) ∧
      firstOnSide B.presentation (.lowerRight j) ∧
      boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.upperRight i)) =
        boundaryDartInitial M
          (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight j)) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  let P := B.presentation
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  have htransition := hbase.2.2.2.2.2
  have hstop' : sideNext P (.upperRight i) = none := by
    simpa [sideNext] using hstop
  have hexists : ∃ j : InfiniteBoundaryDartIndex P,
      S (InfiniteBoundaryDartIndex.dart P (.upperRight i)) =
        InfiniteBoundaryDartIndex.dart P j := hbase.2.2.2.2.1 (.upperRight i)
  rcases hexists with ⟨j, hS⟩
  have hstep := htransition (.upperRight i) j hS
  rcases hstep with hwithin | ⟨_, hfirst, hnext, hjoin⟩
  · rw [hstop'] at hwithin
    cases hwithin
  · obtain ⟨jLR, rfl⟩ := nextNonemptySide_upperRight hnext hlr
    exact ⟨jLR, hS, hfirst, hjoin⟩

/-- Helper toward Definition 3.2: a terminal lower-right dart enters the
lower-left run in the infinite branch when that run is nonempty. -/
theorem IsBoundEdges32.infinite_lowerRight_to_lowerLeft
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.lowerRight.Index}
    (hstop : B.presentation.lowerRight.next i = none)
    (hll : Nonempty B.presentation.lowerLeft.Index) :
    ∃ j : B.presentation.lowerLeft.Index,
      S (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.lowerLeft j) ∧
      firstOnSide B.presentation (.lowerLeft j) ∧
      boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i)) =
        boundaryDartInitial M
          (InfiniteBoundaryDartIndex.dart B.presentation (.lowerLeft j)) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  let P := B.presentation
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  have htransition := hbase.2.2.2.2.2
  have hstop' : sideNext P (.lowerRight i) = none := by
    simpa [sideNext] using hstop
  have hexists : ∃ j : InfiniteBoundaryDartIndex P,
      S (InfiniteBoundaryDartIndex.dart P (.lowerRight i)) =
        InfiniteBoundaryDartIndex.dart P j := hbase.2.2.2.2.1 (.lowerRight i)
  rcases hexists with ⟨j, hS⟩
  have hstep := htransition (.lowerRight i) j hS
  rcases hstep with hwithin | ⟨_, hfirst, hnext, hjoin⟩
  · rw [hstop'] at hwithin
    cases hwithin
  · cases j with
    | upperLeft k =>
        have hskip := hnext.2.2 3 (by norm_num [sideTag, sideDistance])
          (by norm_num [sideTag, sideDistance])
        have hne : sideNonempty P 3 := by simpa [sideNonempty] using hll
        exact (hskip hne).elim
    | upperRight k =>
        have hskip := hnext.2.2 3 (by norm_num [sideTag, sideDistance])
          (by norm_num [sideTag, sideDistance])
        have hne : sideNonempty P 3 := by simpa [sideNonempty] using hll
        exact (hskip hne).elim
    | lowerRight k =>
        have hf : False := by
          simp [nextNonemptySide, sideTag, sideDistance] at hnext
        exact False.elim hf
    | lowerLeft k => exact ⟨k, hS, hfirst, hjoin⟩

/-- Helper toward Definition 3.2: a terminal lower-left dart enters the
upper-left run in the infinite branch when that run is nonempty. -/
theorem IsBoundEdges32.infinite_lowerLeft_to_upperLeft
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.lowerLeft.Index}
    (hstop : B.presentation.lowerLeft.next i = none)
    (hul : Nonempty B.presentation.upperLeft.Index) :
    ∃ j : B.presentation.upperLeft.Index,
      S (InfiniteBoundaryDartIndex.dart B.presentation (.lowerLeft i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft j) ∧
      firstOnSide B.presentation (.upperLeft j) ∧
      boundaryDartTerminal M
          (InfiniteBoundaryDartIndex.dart B.presentation (.lowerLeft i)) =
        boundaryDartInitial M
          (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft j)) := by
  rcases (IsBoundEdges32.infinite_iff hinfinite).mp h with ⟨_, h3⟩
  let P := B.presentation
  have hbase := h3.toIsExternalFaceIntervalOrder2.toIsExternalFaceIntervalOrder
  have htransition := hbase.2.2.2.2.2
  have hstop' : sideNext P (.lowerLeft i) = none := by
    simpa [sideNext] using hstop
  have hexists : ∃ j : InfiniteBoundaryDartIndex P,
      S (InfiniteBoundaryDartIndex.dart P (.lowerLeft i)) =
        InfiniteBoundaryDartIndex.dart P j := hbase.2.2.2.2.1 (.lowerLeft i)
  rcases hexists with ⟨j, hS⟩
  have hstep := htransition (.lowerLeft i) j hS
  rcases hstep with hwithin | ⟨_, hfirst, hnext, hjoin⟩
  · rw [hstop'] at hwithin
    cases hwithin
  · obtain ⟨jUL, rfl⟩ := nextNonemptySide_lowerLeft hnext hul
    exact ⟨jUL, hS, hfirst, hjoin⟩





















































end DirectedDistances.PlanarMap

end
