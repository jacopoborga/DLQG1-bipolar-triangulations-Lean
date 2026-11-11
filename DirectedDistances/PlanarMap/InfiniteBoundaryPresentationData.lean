/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundaryPresentationData

/-! # Infinite boundary presentation data

describes “four (possibly empty) sets of consecutive all missing or all
non-missing edges” and says the upper-left and lower-right boundaries “will
be (possibly empty) simple directed paths.” This file defines only supplied
presentation data and helper predicates; it does not construct a presentation
for a map or prove a source realization theorem. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

universe uV uE uIndex uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
variable {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: data for one possibly empty, indexed
boundary interval. `Index` may be `ℕ`, `ℤ`, or an empty-allowed subtype of an
ordered index type. `darts` is an embedding, so the indexed oriented darts are
injective. `next` supplies which indices are consecutive; correctness of the
resulting vertex joins is a separate proposition. Endpoint labels are
optional supplied data. -/
structure InfiniteBoundarySide (V : Type uV) (E : Type uE) where
  Index : Type uIndex
  darts : Index ↪ E × Bool
  next : Index → Option Index
  initialVertex? : Option V
  terminalVertex? : Option V

/-- Helper toward Definition 3.2: supplied data for the four possibly empty
infinite boundary intervals. The optional vertex labels retain endpoint and
junction data without asserting their geometric correctness as structure
fields. -/
structure InfiniteBoundaryPresentation (M : DirectedPlaneMapWithMissing V E) where
  upperLeft : InfiniteBoundarySide.{uV, uE, uUL} V E
  upperRight : InfiniteBoundarySide.{uV, uE, uUR} V E
  lowerRight : InfiniteBoundarySide.{uV, uE, uLR} V E
  lowerLeft : InfiniteBoundarySide.{uV, uE, uLL} V E

/-- The initial vertex of an oriented dart, using the stored arc direction
when its traversal bit is `true`. -/
def boundaryDartInitial (M : DirectedPlaneMapWithMissing V E)
    (d : E × Bool) : V :=
  if d.2 then M.toPlaneMapWithMissing.src d.1 else M.toPlaneMapWithMissing.tgt d.1

/-- The terminal vertex of an oriented dart, using the stored arc direction
when its traversal bit is `true`. -/
def boundaryDartTerminal (M : DirectedPlaneMapWithMissing V E)
    (d : E × Bool) : V :=
  if d.2 then M.toPlaneMapWithMissing.tgt d.1 else M.toPlaneMapWithMissing.src d.1

/-- Helper toward Definition 3.2: the upper-left family consists of present
edges whose given traversal agrees with the directed orientation and for
which an external face lies on the left. Consecutive darts join in traversal
order. -/
def ULOkInf (P : InfiniteBoundaryPresentation M) : Prop :=
  (∀ i, ∃ hp : ¬ M.toPlaneMapWithMissing.missing (P.upperLeft.darts i).1,
    (P.upperLeft.darts i).2 = M.forward ⟨(P.upperLeft.darts i).1, hp⟩ ∧
      ∃ F : PlaneGraphDrawing.Face (Drawing M),
        (Drawing M).IsExternal F ∧
          LeftOf M F ⟨(P.upperLeft.darts i).1, hp⟩) ∧
  ∀ i j, P.upperLeft.next i = some j →
    boundaryDartTerminal M (P.upperLeft.darts i) =
      boundaryDartInitial M (P.upperLeft.darts j)

/-- Helper toward Definition 3.2: the upper-right family consists of missing
geometric edges. Consecutive darts join in traversal order. -/
def UROkInf (P : InfiniteBoundaryPresentation M) : Prop :=
  (∀ i, M.toPlaneMapWithMissing.missing (P.upperRight.darts i).1) ∧
  ∀ i j, P.upperRight.next i = some j →
    boundaryDartTerminal M (P.upperRight.darts i) =
      boundaryDartInitial M (P.upperRight.darts j)

/-- Helper toward Definition 3.2: the lower-right family consists of present
edges whose given traversal is opposite the directed orientation and for
which an external face lies on the right of the directed edge. Consecutive
darts join in traversal order. -/
def LROkInf (P : InfiniteBoundaryPresentation M) : Prop :=
  (∀ i, ∃ hp : ¬ M.toPlaneMapWithMissing.missing (P.lowerRight.darts i).1,
    (P.lowerRight.darts i).2 = !(M.forward ⟨(P.lowerRight.darts i).1, hp⟩) ∧
      ∃ F : PlaneGraphDrawing.Face (Drawing M),
        (Drawing M).IsExternal F ∧
          RightOf M F ⟨(P.lowerRight.darts i).1, hp⟩) ∧
  ∀ i j, P.lowerRight.next i = some j →
    boundaryDartTerminal M (P.lowerRight.darts i) =
      boundaryDartInitial M (P.lowerRight.darts j)

/-- Helper toward Definition 3.2: the lower-left family consists of missing
geometric edges. Consecutive darts join in traversal order. -/
def LLOkInf (P : InfiniteBoundaryPresentation M) : Prop :=
  (∀ i, M.toPlaneMapWithMissing.missing (P.lowerLeft.darts i).1) ∧
  ∀ i j, P.lowerLeft.next i = some j →
    boundaryDartTerminal M (P.lowerLeft.darts i) =
      boundaryDartInitial M (P.lowerLeft.darts j)

/-- Indices in the disjoint union of the four side families. -/
inductive InfiniteBoundaryDartIndex (P : InfiniteBoundaryPresentation M) where
  | upperLeft (i : P.upperLeft.Index)
  | upperRight (i : P.upperRight.Index)
  | lowerRight (i : P.lowerRight.Index)
  | lowerLeft (i : P.lowerLeft.Index)

/-- The oriented dart selected by a side-family index. -/
def InfiniteBoundaryDartIndex.dart (P : InfiniteBoundaryPresentation M) :
    InfiniteBoundaryDartIndex P → E × Bool
  | .upperLeft i => P.upperLeft.darts i
  | .upperRight i => P.upperRight.darts i
  | .lowerRight i => P.lowerRight.darts i
  | .lowerLeft i => P.lowerLeft.darts i

/-- Helper toward Definition 3.2: the listed edge set is exactly the external
frontier edge set. As in the finite presentation helper, no edge occurs more
than twice; a repeated occurrence is allowed only when the edge is present
and has external faces on both of its directed sides. -/
def IsBoundaryOrderOfInf (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation M) : Prop :=
  (∀ e, (∃ i : InfiniteBoundaryDartIndex P,
      (InfiniteBoundaryDartIndex.dart P i).1 = e) ↔ ExternalFrontierEdge M e) ∧
  (∀ e (i j k : InfiniteBoundaryDartIndex P),
    (InfiniteBoundaryDartIndex.dart P i).1 = e →
    (InfiniteBoundaryDartIndex.dart P j).1 = e →
    (InfiniteBoundaryDartIndex.dart P k).1 = e →
    i = j ∨ i = k ∨ j = k) ∧
  ∀ e (i j : InfiniteBoundaryDartIndex P), i ≠ j →
    (InfiniteBoundaryDartIndex.dart P i).1 = e →
    (InfiniteBoundaryDartIndex.dart P j).1 = e →
    ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      ∃ F G : PlaneGraphDrawing.Face (Drawing M),
        (Drawing M).IsExternal F ∧ (Drawing M).IsExternal G ∧
          LeftOf M F ⟨e, hp⟩ ∧ RightOf M G ⟨e, hp⟩

/-- An empty side family satisfies the upper-left predicate. -/
theorem ULOkInf_of_isEmpty (P : InfiniteBoundaryPresentation M)
    [IsEmpty P.upperLeft.Index] : ULOkInf P := by
  constructor
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i

/-- An empty side family satisfies the upper-right predicate. -/
theorem UROkInf_of_isEmpty (P : InfiniteBoundaryPresentation M)
    [IsEmpty P.upperRight.Index] : UROkInf P := by
  constructor
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i

/-- An empty side family satisfies the lower-right predicate. -/
theorem LROkInf_of_isEmpty (P : InfiniteBoundaryPresentation M)
    [IsEmpty P.lowerRight.Index] : LROkInf P := by
  constructor
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i

/-- An empty side family satisfies the lower-left predicate. -/
theorem LLOkInf_of_isEmpty (P : InfiniteBoundaryPresentation M)
    [IsEmpty P.lowerLeft.Index] : LLOkInf P := by
  constructor
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem boundaryDartInitial_eq (d : E × Bool) :
    boundaryDartInitial M d =
      if d.2 then M.toPlaneMapWithMissing.src d.1
      else M.toPlaneMapWithMissing.tgt d.1 := by exact boundaryDartInitial.eq_def M d

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem boundaryDartTerminal_eq (d : E × Bool) :
    boundaryDartTerminal M d =
      if d.2 then M.toPlaneMapWithMissing.tgt d.1
      else M.toPlaneMapWithMissing.src d.1 := by exact boundaryDartTerminal.eq_def M d

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem ULOkInf_iff (P : InfiniteBoundaryPresentation M) :
    ULOkInf P ↔
      ((∀ i, ∃ hp : ¬ M.toPlaneMapWithMissing.missing (P.upperLeft.darts i).1,
          (P.upperLeft.darts i).2 = M.forward ⟨(P.upperLeft.darts i).1, hp⟩ ∧
            ∃ F : PlaneGraphDrawing.Face (Drawing M),
              (Drawing M).IsExternal F ∧
                LeftOf M F ⟨(P.upperLeft.darts i).1, hp⟩) ∧
        ∀ i j, P.upperLeft.next i = some j →
          boundaryDartTerminal M (P.upperLeft.darts i) =
            boundaryDartInitial M (P.upperLeft.darts j)) := Iff.rfl

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem UROkInf_iff (P : InfiniteBoundaryPresentation M) :
    UROkInf P ↔
      ((∀ i, M.toPlaneMapWithMissing.missing (P.upperRight.darts i).1) ∧
        ∀ i j, P.upperRight.next i = some j →
          boundaryDartTerminal M (P.upperRight.darts i) =
            boundaryDartInitial M (P.upperRight.darts j)) := Iff.rfl

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem LROkInf_iff (P : InfiniteBoundaryPresentation M) :
    LROkInf P ↔
      ((∀ i, ∃ hp : ¬ M.toPlaneMapWithMissing.missing (P.lowerRight.darts i).1,
          (P.lowerRight.darts i).2 = !(M.forward ⟨(P.lowerRight.darts i).1, hp⟩) ∧
            ∃ F : PlaneGraphDrawing.Face (Drawing M),
              (Drawing M).IsExternal F ∧
                RightOf M F ⟨(P.lowerRight.darts i).1, hp⟩) ∧
        ∀ i j, P.lowerRight.next i = some j →
          boundaryDartTerminal M (P.lowerRight.darts i) =
            boundaryDartInitial M (P.lowerRight.darts j)) := Iff.rfl

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem LLOkInf_iff (P : InfiniteBoundaryPresentation M) :
    LLOkInf P ↔
      ((∀ i, M.toPlaneMapWithMissing.missing (P.lowerLeft.darts i).1) ∧
        ∀ i j, P.lowerLeft.next i = some j →
          boundaryDartTerminal M (P.lowerLeft.darts i) =
            boundaryDartInitial M (P.lowerLeft.darts j)) := Iff.rfl

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem InfiniteBoundaryDartIndex.dart_eq (P : InfiniteBoundaryPresentation M)
    (i : InfiniteBoundaryDartIndex P) :
    InfiniteBoundaryDartIndex.dart P i =
      match i with
      | .upperLeft j => P.upperLeft.darts j
      | .upperRight j => P.upperRight.darts j
      | .lowerRight j => P.lowerRight.darts j
      | .lowerLeft j => P.lowerLeft.darts j := by
  cases i <;> rfl

/-- Helper toward Definition 3.2: unfolding equation. -/
theorem IsBoundaryOrderOfInf_iff (P : InfiniteBoundaryPresentation M) :
    IsBoundaryOrderOfInf M P ↔
      ((∀ e, (∃ i : InfiniteBoundaryDartIndex P,
          (InfiniteBoundaryDartIndex.dart P i).1 = e) ↔ ExternalFrontierEdge M e) ∧
        (∀ e (i j k : InfiniteBoundaryDartIndex P),
          (InfiniteBoundaryDartIndex.dart P i).1 = e →
          (InfiniteBoundaryDartIndex.dart P j).1 = e →
          (InfiniteBoundaryDartIndex.dart P k).1 = e →
          i = j ∨ i = k ∨ j = k) ∧
        ∀ e (i j : InfiniteBoundaryDartIndex P), i ≠ j →
          (InfiniteBoundaryDartIndex.dart P i).1 = e →
          (InfiniteBoundaryDartIndex.dart P j).1 = e →
          ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
            ∃ F G : PlaneGraphDrawing.Face (Drawing M),
              (Drawing M).IsExternal F ∧ (Drawing M).IsExternal G ∧
                LeftOf M F ⟨e, hp⟩ ∧ RightOf M G ⟨e, hp⟩) := Iff.rfl

/-! The first remaining construction statement is recorded, not asserted: an
arbitrary supplied presentation need not describe the external frontier.

```lean
theorem supplied_infinite_presentation_is_boundary_order_of
    {V E : Type*} (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation M) :
    ULOkInf P ∧ UROkInf P ∧ LROkInf P ∧ LLOkInf P ∧
      IsBoundaryOrderOfInf M P
```

This requires a concrete source construction supplying `P` and its
compatibility proofs; this data/helper module supplies neither. -/

end DirectedDistances.PlanarMap

end
