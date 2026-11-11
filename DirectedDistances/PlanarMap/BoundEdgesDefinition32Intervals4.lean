/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Intervals3

/-! # Exact finite successor runs for Definition 3.2

within-side successor chain is an exact iterate chain of the external-face
successor, and a terminal UR or LL index exits to the first dart of the next
nonempty side. No finiteness of the side index type is assumed. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
variable {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: a finite chain of supplied successors is
exactly the corresponding iterate of a function that agrees with each
supplied successor step. -/
private theorem iterate_eq_of_successor_sequence
    {I D : Type*} (next : I → Option I) (dart : I → D) (S : D → D)
    (hstep : ∀ {i j}, next i = some j → S (dart i) = dart j)
    (start : D) (a : ℕ → I) (n : ℕ)
    (hstart : S start = dart (a 0))
    (hchain : ∀ k < n, next (a k) = some (a (k + 1))) :
    S^[n + 1] start = dart (a n) := by
  induction n with
  | zero =>
      simpa using hstart
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih (fun k hk => hchain k (by omega))]
      exact hstep (hchain n (by omega))

/-- Helper toward Definition 3.2: a first dart on one side has no later
position than any other dart on that side. -/
private theorem position_le_of_first
    {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {position : InfiniteBoundaryDartIndex P → ℤ}
    (hposition : IsBoundaryPositionOrder3 P position)
    {i j : InfiniteBoundaryDartIndex P}
    (htag : sideTag P i = sideTag P j)
    (hfirst : firstOnSide P i) :
    position i ≤ position j := by
  rcases hposition with ⟨_, hnext, hgap, hblock, _⟩
  by_contra hle
  have hlt : position j < position i := by omega
  let z := position i - 1
  obtain ⟨k, hk⟩ := hgap j i z (by omega) (by omega)
  have htagk : sideTag P k = sideTag P i :=
    (hblock j k i (by omega) (by omega) htag.symm).trans htag.symm
  have hnextk : sideNext P k = some i :=
    (hnext k i htagk).2 (by omega)
  exact (hfirst k) hnextk

/-- Helper toward Definition 3.2: the first dart on a side is unique under
the gapless integer position order. -/
private theorem firstOnSide_unique
    {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {position : InfiniteBoundaryDartIndex P → ℤ}
    (hposition : IsBoundaryPositionOrder3 P position)
    {i j : InfiniteBoundaryDartIndex P}
    (htag : sideTag P i = sideTag P j)
    (hfirstI : firstOnSide P i) (hfirstJ : firstOnSide P j) :
    i = j := by
  have hij := position_le_of_first hposition htag hfirstI
  have hji := position_le_of_first hposition htag.symm hfirstJ
  rcases hposition with ⟨hinjective, _, _, _, _⟩
  exact hinjective (by omega)

/-- Helper toward Definition 3.2: a finite upper-right successor chain starts
at the dart immediately following a terminal upper-left dart and exits at the
first lower-right dart when the upper-right chain has a terminal index. -/
theorem IsBoundEdges32.infinite_upperRight_finite_successor_run
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.upperLeft.Index}
    (hstopUL : B.presentation.upperLeft.next i = none)
    (hur : Nonempty B.presentation.upperRight.Index)
    {a : ℕ → B.presentation.upperRight.Index} (n : ℕ)
    (hfirstStart : firstOnSide B.presentation (.upperRight (a 0)))
    (hchain : ∀ k < n, B.presentation.upperRight.next (a k) =
      some (a (k + 1)))
    (hstopUR : B.presentation.upperRight.next (a n) = none)
    (hlr : Nonempty B.presentation.lowerRight.Index) :
    ∃ j : B.presentation.lowerRight.Index,
      firstOnSide B.presentation (.lowerRight j) ∧
      S^[n + 2] (InfiniteBoundaryDartIndex.dart B.presentation
        (.upperLeft i)) =
          InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight j) ∧
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart B.presentation
        (.upperRight (a n))) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart B.presentation
          (.lowerRight j)) := by
  obtain ⟨position, hposition⟩ :=
    ((IsBoundEdges32.infinite_iff hinfinite).mp h).2.positionOrder
  obtain ⟨first, hstart, hfirst, _⟩ :=
    h.infinite_upperLeft_to_upperRight hinfinite hstopUL hur
  have hfirstEq := firstOnSide_unique hposition
    (i := .upperRight first) (j := .upperRight (a 0)) rfl hfirst hfirstStart
  have hstart' : S (InfiniteBoundaryDartIndex.dart B.presentation
      (.upperLeft i)) = InfiniteBoundaryDartIndex.dart B.presentation
        (.upperRight (a 0)) := by
    rw [← hfirstEq]
    exact hstart
  have hstep : ∀ {x y : InfiniteBoundaryDartIndex B.presentation},
      sideNext B.presentation x = some y →
        S (InfiniteBoundaryDartIndex.dart B.presentation x) =
          InfiniteBoundaryDartIndex.dart B.presentation y := by
    intro x y hxy
    exact (h.infinite_within_side_step hinfinite hxy).1
  have hchain' : ∀ k < n,
      sideNext B.presentation (.upperRight (a k)) =
        some (.upperRight (a (k + 1))) := by
    intro k hk
    simpa [sideNext] using hchain k hk
  have hrun := iterate_eq_of_successor_sequence
    (next := sideNext B.presentation)
    (dart := InfiniteBoundaryDartIndex.dart B.presentation) S hstep
    (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i))
    (fun k => .upperRight (a k)) n hstart' hchain'
  obtain ⟨j, hS, hfirst, hjoin⟩ :=
    h.infinite_upperRight_to_lowerRight hinfinite hstopUR hlr
  refine ⟨j, hfirst, ?_, hjoin⟩
  calc
    S^[n + 2] (InfiniteBoundaryDartIndex.dart B.presentation
        (.upperLeft i)) =
        S (S^[n + 1] (InfiniteBoundaryDartIndex.dart B.presentation
          (.upperLeft i))) := by
            rw [Function.iterate_succ_apply']
    _ = S (InfiniteBoundaryDartIndex.dart B.presentation
        (.upperRight (a n))) := congrArg S hrun
    _ = InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight j) := hS

/-- Helper toward Definition 3.2: a finite lower-left successor chain starts
at the dart immediately following a terminal lower-right dart and exits at
the first upper-left dart when the lower-left chain has a terminal index. -/
theorem IsBoundEdges32.infinite_lowerLeft_finite_successor_run
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.lowerRight.Index}
    (hstopLR : B.presentation.lowerRight.next i = none)
    (hll : Nonempty B.presentation.lowerLeft.Index)
    {a : ℕ → B.presentation.lowerLeft.Index} (n : ℕ)
    (hfirstStart : firstOnSide B.presentation (.lowerLeft (a 0)))
    (hchain : ∀ k < n, B.presentation.lowerLeft.next (a k) =
      some (a (k + 1)))
    (hstopLL : B.presentation.lowerLeft.next (a n) = none)
    (hul : Nonempty B.presentation.upperLeft.Index) :
    ∃ j : B.presentation.upperLeft.Index,
      firstOnSide B.presentation (.upperLeft j) ∧
      S^[n + 2] (InfiniteBoundaryDartIndex.dart B.presentation
        (.lowerRight i)) =
          InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft j) ∧
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart B.presentation
        (.lowerLeft (a n))) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart B.presentation
          (.upperLeft j)) := by
  obtain ⟨position, hposition⟩ :=
    ((IsBoundEdges32.infinite_iff hinfinite).mp h).2.positionOrder
  obtain ⟨first, hstart, hfirst, _⟩ :=
    h.infinite_lowerRight_to_lowerLeft hinfinite hstopLR hll
  have hfirstEq := firstOnSide_unique hposition
    (i := .lowerLeft first) (j := .lowerLeft (a 0)) rfl hfirst hfirstStart
  have hstart' : S (InfiniteBoundaryDartIndex.dart B.presentation
      (.lowerRight i)) = InfiniteBoundaryDartIndex.dart B.presentation
        (.lowerLeft (a 0)) := by
    rw [← hfirstEq]
    exact hstart
  have hstep : ∀ {x y : InfiniteBoundaryDartIndex B.presentation},
      sideNext B.presentation x = some y →
        S (InfiniteBoundaryDartIndex.dart B.presentation x) =
          InfiniteBoundaryDartIndex.dart B.presentation y := by
    intro x y hxy
    exact (h.infinite_within_side_step hinfinite hxy).1
  have hchain' : ∀ k < n,
      sideNext B.presentation (.lowerLeft (a k)) =
        some (.lowerLeft (a (k + 1))) := by
    intro k hk
    simpa [sideNext] using hchain k hk
  have hrun := iterate_eq_of_successor_sequence
    (next := sideNext B.presentation)
    (dart := InfiniteBoundaryDartIndex.dart B.presentation) S hstep
    (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i))
    (fun k => .lowerLeft (a k)) n hstart' hchain'
  obtain ⟨j, hS, hfirst, hjoin⟩ :=
    h.infinite_lowerLeft_to_upperLeft hinfinite hstopLL hul
  refine ⟨j, hfirst, ?_, hjoin⟩
  calc
    S^[n + 2] (InfiniteBoundaryDartIndex.dart B.presentation
        (.lowerRight i)) =
        S (S^[n + 1] (InfiniteBoundaryDartIndex.dart B.presentation
          (.lowerRight i))) := by
            rw [Function.iterate_succ_apply']
    _ = S (InfiniteBoundaryDartIndex.dart B.presentation
        (.lowerLeft (a n))) := congrArg S hrun
    _ = InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft j) := hS

end DirectedDistances.PlanarMap

end
