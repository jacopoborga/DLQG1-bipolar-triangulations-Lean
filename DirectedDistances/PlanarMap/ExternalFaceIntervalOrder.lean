/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.InfiniteBoundaryPresentationData
public import DirectedDistances.PlanarMap.PlaneRealization

/-! # External-face interval order

admitted Definition 3.2. The four supplied sides occur in cyclic order
UL → UR → LR → LL, with empty sides skipped. The successor is tied to the
rotation of an actual PL drawing, and coverage relates its external-face darts
to the supplied presentation. No existence of such a drawing or correspondence
between the two drawing models is asserted here. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: the external face stays on the left under
inverse rotation after flipping the incoming dart. -/
@[expose] def IsGeometricExternalFaceSucc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (U : P.Face) (S : D → D) : Prop :=
  P.IsUnbounded U ∧
    ∀ d, P.dartBorders d U →
      S d = rot.symm (flip d) ∧ P.dartBorders (S d) U

variable {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: cyclic side labels UL, UR, LR, LL. -/
@[expose] def sideTag (P : InfiniteBoundaryPresentation M) :
    InfiniteBoundaryDartIndex P → Fin 4
  | .upperLeft _ => 0
  | .upperRight _ => 1
  | .lowerRight _ => 2
  | .lowerLeft _ => 3

/-- Helper toward Definition 3.2: the supplied within-side successor. -/
@[expose] def sideNext (P : InfiniteBoundaryPresentation M) :
    InfiniteBoundaryDartIndex P → Option (InfiniteBoundaryDartIndex P)
  | .upperLeft i => (P.upperLeft.next i).map .upperLeft
  | .upperRight i => (P.upperRight.next i).map .upperRight
  | .lowerRight i => (P.lowerRight.next i).map .lowerRight
  | .lowerLeft i => (P.lowerLeft.next i).map .lowerLeft

/-- Helper toward Definition 3.2: no supplied within-side step precedes this dart. -/
@[expose] def firstOnSide (P : InfiniteBoundaryPresentation M)
    (j : InfiniteBoundaryDartIndex P) : Prop :=
  ∀ i, sideNext P i ≠ some j

/-- Helper toward Definition 3.2: nonemptiness of a supplied side. -/
@[expose] def sideNonempty (P : InfiniteBoundaryPresentation M) (k : Fin 4) : Prop :=
  if k.val = 0 then Nonempty P.upperLeft.Index
  else if k.val = 1 then Nonempty P.upperRight.Index
  else if k.val = 2 then Nonempty P.lowerRight.Index
  else Nonempty P.lowerLeft.Index

/-- Helper toward Definition 3.2: forward cyclic distance among the four sides. -/
@[expose] def sideDistance (a b : Fin 4) : ℕ := (b.val + 4 - a.val) % 4

/-- Helper toward Definition 3.2: the next nonempty side, skipping precisely
the empty intervening sides in the prescribed cyclic order. -/
@[expose] def nextNonemptySide (P : InfiniteBoundaryPresentation M)
    (a b : Fin 4) : Prop :=
  sideNonempty P b ∧ 0 < sideDistance a b ∧
    ∀ c, 0 < sideDistance a c → sideDistance a c < sideDistance a b →
      ¬ sideNonempty P c

/-- Helper toward Definition 3.2: geometric external-face coverage, within-side
steps, and exhaustive cyclic side transitions with vertex joins. This candidate
predicate does not establish the representation bridge for any construction. -/
@[expose] def IsExternalFaceIntervalOrder
    (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation M) {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  IsBoundaryOrderOfInf M P ∧
  (∀ d, G.dartBorders d U ↔
    ∃ i : InfiniteBoundaryDartIndex P, InfiniteBoundaryDartIndex.dart P i = d) ∧
  IsGeometricExternalFaceSucc G U S ∧
  (∀ i j, sideNext P i = some j →
    S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j ∧
    boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
      boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j)) ∧
  (∀ i, ∃ j, S (InfiniteBoundaryDartIndex.dart P i) =
    InfiniteBoundaryDartIndex.dart P j) ∧
  (∀ i j, S (InfiniteBoundaryDartIndex.dart P i) =
      InfiniteBoundaryDartIndex.dart P j →
    sideNext P i = some j ∨
      (sideNext P i = none ∧ firstOnSide P j ∧
        nextNonemptySide P (sideTag P i) (sideTag P j) ∧
        boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
          boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j)))

open DirectedDistances.KMSW DirectedDistances.RandomWalk Filter

/-- Helper toward Definition 3.2: under the standing realization classification,
the KMSW code successor is the geometric external-face successor. -/
theorem kmswInfFaceSucc_isGeometricExternalFaceSucc
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (U : P.Face) (hUnbounded : P.IsUnbounded U)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    IsGeometricExternalFaceSucc P U (kmswInfFaceSucc w hfin) := by
  refine ⟨hUnbounded, fun d hd => ⟨?_, ?_⟩⟩
  · rfl
  · exact (hU _).mpr
      ((limitExternalDart_faceSucc w hfin htrans hR hL0 d).1.mpr ((hU d).mp hd))

/-- Helper toward Definition 3.2: the two UIQBOT boundary rays and their root
junction follow the geometric external-face successor. The left ray advances
in its directed order; the right ray is traversed in reverse directed order.
This transports labelled KMSW darts, without asserting a presentation-to-drawing
correspondence for an arbitrary supplied edge equivalence. -/
theorem kmswInfFaceSucc_geometric_boundarySteps
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (U : P.Face) (hUnbounded : P.IsUnbounded U)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (∀ i, P.dartBorders (kmswLeftBoundaryEdge w i, false) U ∧
      kmswInfFaceSucc w hfin (kmswLeftBoundaryEdge w i, false) =
        (kmswLeftBoundaryEdge w (i + 1), false) ∧
      P.dartBorders (kmswLeftBoundaryEdge w (i + 1), false) U) ∧
    (∀ i, P.dartBorders (kmswRightBoundaryEdge w (i + 1), true) U ∧
      kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w (i + 1), true) =
        (kmswRightBoundaryEdge w i, true) ∧
      P.dartBorders (kmswRightBoundaryEdge w i, true) U) ∧
    (P.dartBorders (kmswRightBoundaryEdge w 0, true) U ∧
      kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w 0, true) =
        (kmswLeftBoundaryEdge w 0, false) ∧
      P.dartBorders (kmswLeftBoundaryEdge w 0, false) U) := by
  have hgeom := kmswInfFaceSucc_isGeometricExternalFaceSucc
    w hfin P U hUnbounded hU htrans hR hL0
  have hleft (i : ℕ) : P.dartBorders (kmswLeftBoundaryEdge w i, false) U :=
    (hU _).mpr ((limitExternalDart_iff w htrans hR hL0 _).mpr
      (Or.inl ⟨i, rfl⟩))
  have hright (i : ℕ) : P.dartBorders (kmswRightBoundaryEdge w i, true) U :=
    (hU _).mpr ((limitExternalDart_iff w htrans hR hL0 _).mpr
      (Or.inr ⟨i, rfl⟩))
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hs := kmswInfFaceSucc_left w hfin (stageOuterWord_faceSucc w) htrans i
    refine ⟨hleft i, hs, ?_⟩
    rw [← hs]
    exact (hgeom.2 _ (hleft i)).2
  · intro i
    have hs := kmswInfFaceSucc_right w hfin (stageOuterWord_faceSucc w) hL0 hR i
    refine ⟨hright (i + 1), hs, ?_⟩
    rw [← hs]
    exact (hgeom.2 _ (hright (i + 1))).2
  · have hs := mapBoundary_junction w hfin htrans hR hL0
    refine ⟨hright 0, hs, ?_⟩
    rw [← hs]
    exact (hgeom.2 _ (hright 0)).2

end DirectedDistances.PlanarMap
