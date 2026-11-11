/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder2

/-! # External-face interval order, position refinement

Definition 3.2. It strengthens `IsExternalFaceIntervalOrder2` by requiring a
gapless integer position map whose side fibres are intervals in the prescribed
cyclic order, and by requiring endpoint labels at successor-witnessed finite
junctions, including skipped empty sides. Position disjointness concerns dart
occurrences; the same geometric edge may still occur on distinct sides where
the v2 boundary clauses permit it.

Fidelity doubt: the supplied infinite presentation has no separate flag saying
whether an entirely empty boundary retains finite junction data. Accordingly,
this candidate requires marks at finite junctions witnessed by the external
successor and at the skipped empty sides, but does not infer finite junctions
the supplied finite and limiting boundary conventions. No UIQBOT instance or
paper-completion claim is made. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: a specified injective integer position
map has gapless image, consecutive within-side steps, interval side fibres,
and cyclic UL–UR–LR–LL order up to a linear cut. -/
@[expose] def IsBoundaryPositionOrder3
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (position : InfiniteBoundaryDartIndex P → ℤ) : Prop :=
  Function.Injective position ∧
  (∀ i j, sideTag P i = sideTag P j →
    (sideNext P i = some j ↔ position j = position i + 1)) ∧
  (∀ i j z, position i ≤ z → z ≤ position j → ∃ k, position k = z) ∧
  (∀ i j k, position i ≤ position j → position j ≤ position k →
    sideTag P i = sideTag P k → sideTag P j = sideTag P i) ∧
  (∀ i j k, position i < position j → position j < position k →
    sideTag P i ≠ sideTag P j → sideTag P j ≠ sideTag P k →
    sideTag P i ≠ sideTag P k →
    sideDistance (sideTag P i) (sideTag P j) +
      sideDistance (sideTag P j) (sideTag P k) < 4)

/-- Helper toward Definition 3.2: some injective integer position map gives
the four boundary sides their consecutive cyclic block order. -/
@[expose] def BoundaryPositionOrder3
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) : Prop :=
  ∃ position : InfiniteBoundaryDartIndex P → ℤ,
    IsBoundaryPositionOrder3 P position

/-- Helper toward Definition 3.2: every finite junction witnessed by the
external successor has labels at both incident sides, and each intervening
empty side carries both ends of the same zero-edge path at that vertex. -/
@[expose] def RequiredBoundaryJoinEndpointLabels
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (S : E × Bool → E × Bool) : Prop :=
  ∀ i j : InfiniteBoundaryDartIndex P,
    S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
    sideNext P i = none →
    nextNonemptySide P (sideTag P i) (sideTag P j) →
    let v := boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i)
    sideTerminalVertex? P (sideTag P i) = some v ∧
      sideInitialVertex? P (sideTag P j) = some v ∧
      ∀ k : Fin 4,
        0 < sideDistance (sideTag P i) k →
        sideDistance (sideTag P i) k < sideDistance (sideTag P i) (sideTag P j) →
        sideInitialVertex? P k = some v ∧ sideTerminalVertex? P k = some v

/-- Helper toward Definition 3.2: v2 external-face order strengthened by
block positions and mandatory labels at its finite successor junctions. -/
@[expose] def IsExternalFaceIntervalOrder3
    (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  IsExternalFaceIntervalOrder2 M P G U S ∧
    BoundaryPositionOrder3 P ∧ RequiredBoundaryJoinEndpointLabels P S

namespace BoundaryPositionOrder3

variable {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}

/-- Helper toward Definition 3.2: a next step remains in its side and advances
exactly one position. -/
theorem next_preserves_block (h : BoundaryPositionOrder3 P)
    {i j : InfiniteBoundaryDartIndex P} (hnext : sideNext P i = some j) :
    sideTag P i = sideTag P j ∧
      ∃ position : InfiniteBoundaryDartIndex P → ℤ,
        IsBoundaryPositionOrder3 P position ∧ position j = position i + 1 := by
  rcases h with ⟨position, hposition⟩
  rcases hposition with ⟨hinj, hnextpos, hgap, hblock, hcyclic⟩
  have htag : sideTag P i = sideTag P j := by
    cases i <;> cases j <;> simp [sideNext, sideTag] at hnext ⊢
  exact ⟨htag, ⟨position, ⟨hinj, hnextpos, hgap, hblock, hcyclic⟩,
    (hnextpos i j htag).1 hnext⟩⟩

/-- Helper toward Definition 3.2: a side cannot recur after a different side
in increasing boundary order. -/
theorem no_side_recurrence {position : InfiniteBoundaryDartIndex P → ℤ}
    (h : IsBoundaryPositionOrder3 P position)
    {i j k : InfiniteBoundaryDartIndex P}
    (hij : position i < position j) (hjk : position j < position k)
    (hends : sideTag P i = sideTag P k)
    (hmiddle : sideTag P i ≠ sideTag P j) : False := by
  rcases h with ⟨hinj, hnextpos, hgap, hblock, hcyclic⟩
  apply hmiddle
  exact (hblock i j k hij.le hjk.le hends).symm

/-- Helper toward Definition 3.2: distinct side occurrences occupy distinct
positions; this does not identify or separate their geometric edges. -/
theorem distinct_sides_have_distinct_positions (h : BoundaryPositionOrder3 P)
    {i j : InfiniteBoundaryDartIndex P} (htag : sideTag P i ≠ sideTag P j) :
    ∃ position : InfiniteBoundaryDartIndex P → ℤ,
      Function.Injective position ∧ position i ≠ position j := by
  rcases h with ⟨position, hposition⟩
  rcases hposition with ⟨hinj, hnextpos, hgap, hblock, hcyclic⟩
  refine ⟨position, hinj, ?_⟩
  intro heq
  exact htag (congrArg (sideTag P) (hinj heq))

/-- Helper toward Definition 3.2: every occurrence between two occurrences
of one side belongs to that same consecutive block. -/
theorem membership_between_is_preserved (h : BoundaryPositionOrder3 P)
    {i j k : InfiniteBoundaryDartIndex P}
    : ∃ position : InfiniteBoundaryDartIndex P → ℤ,
      IsBoundaryPositionOrder3 P position ∧
        (∀ (_hij : position i ≤ position j) (_hjk : position j ≤ position k),
          sideTag P i = sideTag P k → sideTag P j = sideTag P i) := by
  rcases h with ⟨position, hposition⟩
  rcases hposition with ⟨hinj, hnextpos, hgap, hblock, hcyclic⟩
  refine ⟨position, ⟨hinj, hnextpos, hgap, hblock, hcyclic⟩, ?_⟩
  intro hij hjk hends
  exact hblock i j k hij hjk hends

end BoundaryPositionOrder3

namespace IsExternalFaceIntervalOrder3

variable {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: v2 identifies the next nonempty side at an
external-successor transition once the source side has ended. -/
private theorem nextNonemptySide_of_v2
    (h : IsExternalFaceIntervalOrder2 M P G U S)
    {i j : InfiniteBoundaryDartIndex P}
    (hS : S (InfiniteBoundaryDartIndex.dart P i) =
      InfiniteBoundaryDartIndex.dart P j)
    (hstop : sideNext P i = none) :
    nextNonemptySide P (sideTag P i) (sideTag P j) := by
  rcases h.1 with ⟨_, _, _, _, _, htransition⟩
  rcases htransition i j hS with hstep | ⟨_, _, hside, _⟩
  · rw [hstop] at hstep
    cases hstep
  · exact hside

/-- Helper toward Definition 3.2: forget the position and mandatory-label
strengthenings. -/
theorem toIsExternalFaceIntervalOrder2
    (h : IsExternalFaceIntervalOrder3 M P G U S) :
    IsExternalFaceIntervalOrder2 M P G U S := h.1

/-- Helper toward Definition 3.2: position blocks form one cyclically ordered
UL–UR–LR–LL boundary word up to the chosen linear cut. -/
theorem positionOrder (h : IsExternalFaceIntervalOrder3 M P G U S) :
    BoundaryPositionOrder3 P := h.2.1

/-- Helper toward Definition 3.2: endpoint labels are present at every
successor-witnessed finite junction, including skipped empty sides. -/
theorem endpointLabels_at_junction
    (h : IsExternalFaceIntervalOrder3 M P G U S)
    {i j : InfiniteBoundaryDartIndex P}
    (hS : S (InfiniteBoundaryDartIndex.dart P i) =
      InfiniteBoundaryDartIndex.dart P j)
    (hstop : sideNext P i = none) :
    sideTerminalVertex? P (sideTag P i) =
        some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i)) ∧
      sideInitialVertex? P (sideTag P j) =
        some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i)) := by
  have hside := nextNonemptySide_of_v2 h.1 hS hstop
  have hlabels := h.2.2 i j hS hstop hside
  exact ⟨hlabels.1, hlabels.2.1⟩

/-- Helper toward Definition 3.2: a skipped empty side is marked by both ends
of its zero-edge path at the junction vertex. -/
theorem skipped_empty_side_is_marked
    (h : IsExternalFaceIntervalOrder3 M P G U S)
    {i j : InfiniteBoundaryDartIndex P} {k : Fin 4}
    (hS : S (InfiniteBoundaryDartIndex.dart P i) =
      InfiniteBoundaryDartIndex.dart P j)
    (hstop : sideNext P i = none)
    (hbefore : 0 < sideDistance (sideTag P i) k)
    (hbetween : sideDistance (sideTag P i) k <
      sideDistance (sideTag P i) (sideTag P j)) :
    sideInitialVertex? P k =
        some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i)) ∧
      sideTerminalVertex? P k =
        some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i)) := by
  have hside := nextNonemptySide_of_v2 h.1 hS hstop
  exact (h.2.2 i j hS hstop hside).2.2 k hbefore hbetween

end IsExternalFaceIntervalOrder3

private theorem infiniteBoundaryDartIndex_isEmpty
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    [IsEmpty P.upperLeft.Index] [IsEmpty P.upperRight.Index]
    [IsEmpty P.lowerRight.Index] [IsEmpty P.lowerLeft.Index] :
    IsEmpty (InfiniteBoundaryDartIndex P) := by
  refine ⟨?_⟩
  intro i
  cases i with
  | upperLeft i => exact isEmptyElim i
  | upperRight i => exact isEmptyElim i
  | lowerRight i => exact isEmptyElim i
  | lowerLeft i => exact isEmptyElim i

/-- Helper toward Definition 3.2: the position and endpoint strengthening
clauses are consistent for an entirely empty listed boundary. -/
theorem empty_boundary_strengthening_is_inhabited
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    [IsEmpty P.upperLeft.Index] [IsEmpty P.upperRight.Index]
    [IsEmpty P.lowerRight.Index] [IsEmpty P.lowerLeft.Index]
    (S : E × Bool → E × Bool) :
    BoundaryPositionOrder3 P ∧ RequiredBoundaryJoinEndpointLabels P S := by
  letI : IsEmpty (InfiniteBoundaryDartIndex P) := infiniteBoundaryDartIndex_isEmpty P
  refine ⟨?_, ?_⟩
  · refine ⟨fun i => isEmptyElim i, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j _
      exact isEmptyElim i
    · intro i j _
      exact isEmptyElim i
    · intro i j z _ _
      exact isEmptyElim i
    · intro i j k _ _ _
      exact isEmptyElim i
    · intro i j k _ _ _ _ _
      exact isEmptyElim i
  · intro i
    exact isEmptyElim i



theorem of_v2_of_empty_boundary
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    [IsEmpty P.upperLeft.Index] [IsEmpty P.upperRight.Index]
    [IsEmpty P.lowerRight.Index] [IsEmpty P.lowerLeft.Index]
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h2 : IsExternalFaceIntervalOrder2 M P G U S) :
    IsExternalFaceIntervalOrder3 M P G U S := by
  have hstrength := empty_boundary_strengthening_is_inhabited P S
  exact ⟨h2, hstrength.1, hstrength.2⟩





















end DirectedDistances.PlanarMap
