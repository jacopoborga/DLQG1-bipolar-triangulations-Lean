/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Intervals
public import Mathlib.Logic.Function.Iterate

/-! # Successor iterates for Definition 3.2 boundary intervals

infinite interval-order clauses identify each upper-right occurrence with a
finite iterate from the first upper-right dart. The endpoint-to-orbit
equivalences for the full intervals remain under investigation below. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
variable {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: a dart in the upper-right block cannot
precede its first dart in the integer boundary order. -/
private theorem side_first_position_le
    {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {position : InfiniteBoundaryDartIndex P → ℤ}
    (hposition : IsBoundaryPositionOrder3 P position)
    {i j : InfiniteBoundaryDartIndex P}
    (htag : sideTag P i = sideTag P j)
    (hfirst : firstOnSide P i) :
    position i ≤ position j := by
  rcases hposition with ⟨hinjective, hnext, hgap, hblock, _⟩
  by_contra hle
  have hlt : position j < position i := by omega
  let z := position i - 1
  obtain ⟨k, hk⟩ := hgap j i z (by omega) (by omega)
  have htagk : sideTag P k = sideTag P i :=
    (hblock j k i (by omega) (by omega) htag.symm).trans htag.symm
  have hnextk : sideNext P k = some i :=
    (hnext k i htagk).2 (by omega)
  exact (hfirst k) hnextk

/-- Helper toward Definition 3.2: every upper-right occurrence is reached by
successive upper-right steps from a first occurrence, when the side positions
are gapless and within-side steps advance by one. -/
private theorem side_iterate_from_first
    {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {S : E × Bool → E × Bool}
    {position : InfiniteBoundaryDartIndex P → ℤ}
    (hposition : IsBoundaryPositionOrder3 P position)
    (hstep : ∀ {i j : InfiniteBoundaryDartIndex P},
      sideNext P i = some j →
        S (InfiniteBoundaryDartIndex.dart P i) =
          InfiniteBoundaryDartIndex.dart P j)
    {i j : InfiniteBoundaryDartIndex P}
    (htag : sideTag P i = sideTag P j)
    (hfirst : firstOnSide P i) :
    ∃ n : ℕ, S^[n]
      (InfiniteBoundaryDartIndex.dart P i) =
        InfiniteBoundaryDartIndex.dart P j := by
  rcases hposition with ⟨hinjective, hnext, hgap, hblock, hcyclic⟩
  have hle := side_first_position_le
    ⟨hinjective, hnext, hgap, hblock, hcyclic⟩ htag hfirst
  let n : ℕ :=
    (position j - position i).toNat
  have htarget : position j = position i + n := by
    dsimp [n]
    have hcast :
        ((position j - position i).toNat : ℤ) = position j - position i :=
      Int.toNat_of_nonneg (by omega)
    omega
  have hcover : ∀ n : ℕ, ∀ k : InfiniteBoundaryDartIndex P,
      sideTag P k = sideTag P i → position k = position i + n →
        ∃ m : ℕ, S^[m]
          (InfiniteBoundaryDartIndex.dart P i) =
            InfiniteBoundaryDartIndex.dart P k := by
    intro n
    induction n with
    | zero =>
        intro k htagk hk
        have hpos : position k = position i := by
          simpa using hk
        have hidx : k = i := hinjective hpos
        cases hidx
        exact ⟨0, by simp⟩
    | succ n ih =>
        intro k htagk hk
        let z := position i + n
        obtain ⟨m, hm⟩ := hgap i k z (by omega)
          (by omega)
        have htagm : sideTag P m = sideTag P i :=
          hblock i m k (by omega) (by omega) htagk.symm
        have hnext : sideNext P m = some k :=
          (hnext m k (htagm.trans htagk.symm)).2 (by omega)
        obtain ⟨r, hr⟩ := ih m htagm (by omega)
        refine ⟨r + 1, ?_⟩
        rw [Function.iterate_succ_apply']
        rw [hr]
        exact hstep hnext
  exact hcover n j htag.symm htarget

/-- Helper toward Definition 3.2: each supplied upper-right dart is a
positive S-iterate of the terminal upper-left dart. -/
theorem IsBoundEdges32.upperRight_occurrence_is_successor_iterate
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.upperLeft.Index}
    (hstop : B.presentation.upperLeft.next i = none)
    (hur : Nonempty B.presentation.upperRight.Index)
    (j : B.presentation.upperRight.Index) :
    ∃ n : ℕ, S^[Nat.succ n]
      (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.upperRight j) := by
  obtain ⟨first, hstart, hfirst, _⟩ :=
    h.infinite_upperLeft_to_upperRight hinfinite hstop hur
  have h3 := (IsBoundEdges32.infinite_iff hinfinite).mp h |>.2
  rcases h3.positionOrder with ⟨position, hposition⟩
  have hstep : ∀ {a b : InfiniteBoundaryDartIndex B.presentation},
      sideNext B.presentation a = some b →
        S (InfiniteBoundaryDartIndex.dart B.presentation a) =
          InfiniteBoundaryDartIndex.dart B.presentation b := by
    intro a b hab
    exact (h.infinite_within_side_step hinfinite hab).1
  obtain ⟨n, horbit⟩ := side_iterate_from_first hposition hstep (i :=
    .upperRight first) (j := .upperRight j) rfl hfirst
  refine ⟨n, ?_⟩
  rw [Function.iterate_succ_apply, hstart]
  exact horbit

/-- Helper toward Definition 3.2: upper-right membership is equivalent to
occurrence as a positive S-iterate from the terminal upper-left dart, with
the iterated dart retaining the supplied edge identity. -/
theorem IsBoundEdges32.mem_upperRightBoundary32_iff_successor_iterate
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.upperLeft.Index}
    (hstop : B.presentation.upperLeft.next i = none)
    (hur : Nonempty B.presentation.upperRight.Index) (e : E) :
    e ∈ upperRightBoundary32 B ↔
      ∃ j : B.presentation.upperRight.Index, ∃ n : ℕ,
        (InfiniteBoundaryDartIndex.dart B.presentation (.upperRight j)).1 = e ∧
        S^[Nat.succ n] (InfiniteBoundaryDartIndex.dart B.presentation
          (.upperLeft i)) = InfiniteBoundaryDartIndex.dart B.presentation
            (.upperRight j) := by
  constructor
  · intro he
    obtain ⟨j, hje⟩ := (mem_upperRightBoundary32 B e).mp he
    have hje' : (InfiniteBoundaryDartIndex.dart B.presentation
        (.upperRight j)).1 = e := by
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hje
    obtain ⟨n, horbit⟩ := h.upperRight_occurrence_is_successor_iterate
      hinfinite hstop hur j
    exact ⟨j, n, hje', horbit⟩
  · rintro ⟨j, n, hje, _⟩
    exact (mem_upperRightBoundary32 B e).mpr ⟨j, by
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hje⟩

/-- Helper toward Definition 3.2: every upper-right dart reached from the
terminal upper-left dart in the specified positive iterates is a missing
geometric edge. -/
theorem IsBoundEdges32.upperRight_successor_iterate_missing
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.upperLeft.Index}
    (hstop : B.presentation.upperLeft.next i = none)
    (hur : Nonempty B.presentation.upperRight.Index)
    (j : B.presentation.upperRight.Index) (n : ℕ)
    (horbit : S^[Nat.succ n]
      (InfiniteBoundaryDartIndex.dart B.presentation (.upperLeft i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.upperRight j)) :
    M.toPlaneMapWithMissing.missing
      (InfiniteBoundaryDartIndex.dart B.presentation (.upperRight j)).1 := by
  have hmem := (h.mem_upperRightBoundary32_iff_successor_iterate
    hinfinite hstop hur _).mpr ⟨j, n, rfl, horbit⟩
  exact upperRightBoundary32_missing h hmem

/-- Helper toward Definition 3.2: each supplied lower-left dart is a
positive S-iterate of the terminal lower-right dart. -/
theorem IsBoundEdges32.lowerLeft_occurrence_is_successor_iterate
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.lowerRight.Index}
    (hstop : B.presentation.lowerRight.next i = none)
    (hll : Nonempty B.presentation.lowerLeft.Index)
    (j : B.presentation.lowerLeft.Index) :
    ∃ n : ℕ, S^[Nat.succ n]
      (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.lowerLeft j) := by
  obtain ⟨first, hstart, hfirst, _⟩ :=
    h.infinite_lowerRight_to_lowerLeft hinfinite hstop hll
  have h3 := (IsBoundEdges32.infinite_iff hinfinite).mp h |>.2
  rcases h3.positionOrder with ⟨position, hposition⟩
  have hstep : ∀ {a b : InfiniteBoundaryDartIndex B.presentation},
      sideNext B.presentation a = some b →
        S (InfiniteBoundaryDartIndex.dart B.presentation a) =
          InfiniteBoundaryDartIndex.dart B.presentation b := by
    intro a b hab
    exact (h.infinite_within_side_step hinfinite hab).1
  obtain ⟨n, horbit⟩ := side_iterate_from_first hposition hstep (i :=
    .lowerLeft first) (j := .lowerLeft j) rfl hfirst
  refine ⟨n, ?_⟩
  rw [Function.iterate_succ_apply, hstart]
  exact horbit

/-- Helper toward Definition 3.2: lower-left membership is equivalent to
occurrence as a positive S-iterate from the terminal lower-right dart, with
the iterated dart retaining the supplied edge identity. -/
theorem IsBoundEdges32.mem_lowerLeftBoundary32_iff_successor_iterate
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.lowerRight.Index}
    (hstop : B.presentation.lowerRight.next i = none)
    (hll : Nonempty B.presentation.lowerLeft.Index) (e : E) :
    e ∈ lowerLeftBoundary32 B ↔
      ∃ j : B.presentation.lowerLeft.Index, ∃ n : ℕ,
        (InfiniteBoundaryDartIndex.dart B.presentation (.lowerLeft j)).1 = e ∧
        S^[Nat.succ n] (InfiniteBoundaryDartIndex.dart B.presentation
          (.lowerRight i)) = InfiniteBoundaryDartIndex.dart B.presentation
            (.lowerLeft j) := by
  constructor
  · intro he
    obtain ⟨j, hje⟩ := (mem_lowerLeftBoundary32 B e).mp he
    have hje' : (InfiniteBoundaryDartIndex.dart B.presentation
        (.lowerLeft j)).1 = e := by
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hje
    obtain ⟨n, horbit⟩ := h.lowerLeft_occurrence_is_successor_iterate
      hinfinite hstop hll j
    exact ⟨j, n, hje', horbit⟩
  · rintro ⟨j, n, hje, _⟩
    exact (mem_lowerLeftBoundary32 B e).mpr ⟨j, by
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hje⟩

/-- Helper toward Definition 3.2: every lower-left dart reached from the
terminal lower-right dart in the specified positive iterates is a missing
geometric edge. -/
theorem IsBoundEdges32.lowerLeft_successor_iterate_missing
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    {i : B.presentation.lowerRight.Index}
    (hstop : B.presentation.lowerRight.next i = none)
    (hll : Nonempty B.presentation.lowerLeft.Index)
    (j : B.presentation.lowerLeft.Index) (n : ℕ)
    (horbit : S^[Nat.succ n]
      (InfiniteBoundaryDartIndex.dart B.presentation (.lowerRight i)) =
        InfiniteBoundaryDartIndex.dart B.presentation (.lowerLeft j)) :
    M.toPlaneMapWithMissing.missing
      (InfiniteBoundaryDartIndex.dart B.presentation (.lowerLeft j)).1 := by
  have hmem := (h.mem_lowerLeftBoundary32_iff_successor_iterate
    hinfinite hstop hll _).mpr ⟨j, n, rfl, horbit⟩
  exact lowerLeftBoundary32_missing h hmem

















































end DirectedDistances.PlanarMap

end
