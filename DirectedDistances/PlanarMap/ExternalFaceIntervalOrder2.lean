/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder

/- # Strengthened external-face interval order

present directed UL/LR and missing UR/LL edges. Vertex simplicity includes the
last vertex of a finite side. Supplied endpoint labels describe traversal
endpoints, including the reverse traversal of LR. Empty sides retain their
zero-edge marks, and marks on skipped sides agree with the actual join.
The author rulings of 2026-11-05 and 2026-11-06 permit absent finite endpoint
marks on infinite constructions. No paper-completion claim is made. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uI uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: vertex occurrences on a side consist of
one initial vertex per dart and the terminal vertices with no successor.
This retains the final vertex, which dart-initial injectivity alone omits. -/
@[expose] def boundarySideVertex (M : DirectedPlaneMapWithMissing V E)
    (B : InfiniteBoundarySide.{uV, uE, uI} V E) :
    B.Index ⊕ {i : B.Index // B.next i = none} → V
  | .inl i => boundaryDartInitial M (B.darts i)
  | .inr i => boundaryDartTerminal M (B.darts i.val)

/-- Helper toward Definition 3.2: a side has distinct vertex occurrences,
and its supplied successor has no finite directed cycle. Joins themselves
are required by the corresponding side predicate in the strengthened order. -/
@[expose] def IsSimpleBoundarySide (M : DirectedPlaneMapWithMissing V E)
    (B : InfiniteBoundarySide.{uV, uE, uI} V E) : Prop :=
  Function.Injective (boundarySideVertex M B) ∧
    ∀ i, ¬ Relation.TransGen (fun i j => B.next i = some j) i i

/-- Helper toward Definition 3.2: supplied labels equal the actual first
and last traversal vertices. A supplied label on a nonempty side requires
such an endpoint. On an empty side, two supplied labels mark the same
zero-edge path; neither label is required to exist. -/
@[expose] def BoundarySideEndpointLabels (M : DirectedPlaneMapWithMissing V E)
    (B : InfiniteBoundarySide.{uV, uE, uI} V E) : Prop :=
  (∀ v, B.initialVertex? = some v →
    (Nonempty B.Index → ∃ i, (∀ j, B.next j ≠ some i) ∧
      boundaryDartInitial M (B.darts i) = v) ∧
    ∀ i, (∀ j, B.next j ≠ some i) →
      boundaryDartInitial M (B.darts i) = v) ∧
  (∀ v, B.terminalVertex? = some v →
    (Nonempty B.Index → ∃ i, B.next i = none ∧
      boundaryDartTerminal M (B.darts i) = v) ∧
    ∀ i, B.next i = none → boundaryDartTerminal M (B.darts i) = v) ∧
  (IsEmpty B.Index → ∀ v z,
    B.initialVertex? = some v → B.terminalVertex? = some z → v = z)

/-- Helper toward Definition 3.2: optional initial label of a cyclic side. -/
@[expose] def sideInitialVertex? (P : InfiniteBoundaryPresentation M)
    (k : Fin 4) : Option V :=
  if k.val = 0 then P.upperLeft.initialVertex?
  else if k.val = 1 then P.upperRight.initialVertex?
  else if k.val = 2 then P.lowerRight.initialVertex?
  else P.lowerLeft.initialVertex?

/-- Helper toward Definition 3.2: optional terminal label of a cyclic side. -/
@[expose] def sideTerminalVertex? (P : InfiniteBoundaryPresentation M)
    (k : Fin 4) : Option V :=
  if k.val = 0 then P.upperLeft.terminalVertex?
  else if k.val = 1 then P.upperRight.terminalVertex?
  else if k.val = 2 then P.lowerRight.terminalVertex?
  else P.lowerLeft.terminalVertex?

/-- Helper toward Definition 3.2: endpoint marks on both sides of an actual
transition and on every skipped empty side equal its join vertex. No finite
join is postulated at an infinite end, or when the whole boundary is empty. -/
@[expose] def BoundaryJoinEndpointLabels
    (P : InfiniteBoundaryPresentation M) (S : E × Bool → E × Bool) : Prop :=
  ∀ i j : InfiniteBoundaryDartIndex P,
    S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
    sideNext P i = none →
    let v := boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i)
    (∀ z, sideTerminalVertex? P (sideTag P i) = some z → z = v) ∧
    (∀ z, sideInitialVertex? P (sideTag P j) = some z → z = v) ∧
    ∀ k : Fin 4,
      0 < sideDistance (sideTag P i) k →
      sideDistance (sideTag P i) k < sideDistance (sideTag P i) (sideTag P j) →
      (∀ z, sideInitialVertex? P k = some z → z = v) ∧
      (∀ z, sideTerminalVertex? P k = some z → z = v)

/-- Helper toward Definition 3.2: the interval-order candidate strengthened
by all four side clauses, simple present sides, and correct supplied endpoint -/
@[expose] def IsExternalFaceIntervalOrder2
    (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  IsExternalFaceIntervalOrder M P G U S ∧
  ULOkInf P ∧ UROkInf P ∧ LROkInf P ∧ LLOkInf P ∧
  IsSimpleBoundarySide M P.upperLeft ∧ IsSimpleBoundarySide M P.lowerRight ∧
  BoundarySideEndpointLabels M P.upperLeft ∧
  BoundarySideEndpointLabels M P.upperRight ∧
  BoundarySideEndpointLabels M P.lowerRight ∧
  BoundarySideEndpointLabels M P.lowerLeft ∧ BoundaryJoinEndpointLabels P S

namespace IsExternalFaceIntervalOrder2

variable {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: forget the strengthening clauses. -/
theorem toIsExternalFaceIntervalOrder (h : IsExternalFaceIntervalOrder2 M P G U S) :
    IsExternalFaceIntervalOrder M P G U S := h.1

/-- Helper toward Definition 3.2: the upper-left side clause. -/
theorem ulOkInf (h : IsExternalFaceIntervalOrder2 M P G U S) : ULOkInf P := h.2.1

/-- Helper toward Definition 3.2: the upper-right side clause. -/
theorem urOkInf (h : IsExternalFaceIntervalOrder2 M P G U S) : UROkInf P := h.2.2.1

/-- Helper toward Definition 3.2: the lower-right side clause. -/
theorem lrOkInf (h : IsExternalFaceIntervalOrder2 M P G U S) : LROkInf P := h.2.2.2.1

/-- Helper toward Definition 3.2: the lower-left side clause. -/
theorem llOkInf (h : IsExternalFaceIntervalOrder2 M P G U S) : LLOkInf P := h.2.2.2.2.1

/-- Helper toward Definition 3.2: simplicity of the upper-left side. -/
theorem upperLeft_simple (h : IsExternalFaceIntervalOrder2 M P G U S) :
    IsSimpleBoundarySide M P.upperLeft := h.2.2.2.2.2.1

/-- Helper toward Definition 3.2: simplicity of the lower-right side. -/
theorem lowerRight_simple (h : IsExternalFaceIntervalOrder2 M P G U S) :
    IsSimpleBoundarySide M P.lowerRight := h.2.2.2.2.2.2.1

/-- Helper toward Definition 3.2: upper-left endpoint labels. -/
theorem upperLeft_endpointLabels (h : IsExternalFaceIntervalOrder2 M P G U S) :
    BoundarySideEndpointLabels M P.upperLeft := h.2.2.2.2.2.2.2.1

/-- Helper toward Definition 3.2: upper-right endpoint labels. -/
theorem upperRight_endpointLabels (h : IsExternalFaceIntervalOrder2 M P G U S) :
    BoundarySideEndpointLabels M P.upperRight := h.2.2.2.2.2.2.2.2.1

/-- Helper toward Definition 3.2: lower-right endpoint labels. -/
theorem lowerRight_endpointLabels (h : IsExternalFaceIntervalOrder2 M P G U S) :
    BoundarySideEndpointLabels M P.lowerRight := h.2.2.2.2.2.2.2.2.2.1

/-- Helper toward Definition 3.2: lower-left endpoint labels. -/
theorem lowerLeft_endpointLabels (h : IsExternalFaceIntervalOrder2 M P G U S) :
    BoundarySideEndpointLabels M P.lowerLeft := h.2.2.2.2.2.2.2.2.2.2.1

/-- Helper toward Definition 3.2: endpoint labels at actual joins. -/
theorem join_endpointLabels (h : IsExternalFaceIntervalOrder2 M P G U S) :
    BoundaryJoinEndpointLabels P S := h.2.2.2.2.2.2.2.2.2.2.2

end IsExternalFaceIntervalOrder2

/-- Helper toward Definition 3.2: simplicity includes injectivity of the
initial vertices of all darts in the side. -/
theorem IsSimpleBoundarySide.initial_injective
    {B : InfiniteBoundarySide.{uV, uE, uI} V E}
    (h : IsSimpleBoundarySide M B) :
    Function.Injective (fun i => boundaryDartInitial M (B.darts i)) := by
  intro i j hij
  exact Sum.inl.inj (h.1 (show boundarySideVertex M B (.inl i) =
    boundarySideVertex M B (.inl j) from hij))

/-- Helper toward Definition 3.2: a finite terminal vertex is different
from every dart-initial vertex on the same simple side. -/
theorem IsSimpleBoundarySide.terminal_ne_initial
    {B : InfiniteBoundarySide.{uV, uE, uI} V E}
    (h : IsSimpleBoundarySide M B) (i : B.Index) (hi : B.next i = none)
    (j : B.Index) :
    boundaryDartTerminal M (B.darts i) ≠ boundaryDartInitial M (B.darts j) := by
  intro hij
  have heq := h.1 (show boundarySideVertex M B (.inr ⟨i, hi⟩) =
    boundarySideVertex M B (.inl j) from hij)
  cases heq

















































end DirectedDistances.PlanarMap
