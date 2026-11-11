/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.InfiniteBoundaryPresentationData
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport

/-! # Transport of infinite boundary presentations -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

universe uV uE uV' uE' uUL uUR uLR uLL uI

variable {V : Type uV} {E : Type uE}
variable {V' : Type uV'} {E' : Type uE'}
variable {M : DirectedPlaneMapWithMissing V E}
variable {M' : DirectedPlaneMapWithMissing V' E'}

/-- Helper toward Definition 3.2: an orientation-preserving equivalence of
maps with missing edges, including the parameter direction of every present
oriented arc. -/
structure InfiniteBoundaryMapEquiv
    (M : DirectedPlaneMapWithMissing V E)
    (M' : DirectedPlaneMapWithMissing V' E') where
  map : DirectedPlaneMapWithMissing.HomeoEquiv M M'
  orientationPreserving : OrientationPreserving map.drawing.drawing.h
  arcParam : PresentEdge M → unitInterval ≃ₜ unitInterval
  arcParam_zero : ∀ d, arcParam d 0 = 0
  arcParam_one : ∀ d, arcParam d 1 = 1
  orientedArc_map : ∀ (d : PresentEdge M) (t : unitInterval),
    orientedArc M' ⟨map.drawing.drawing.σE d.1,
      by simpa [map.drawing.missing_map] using d.2⟩ (arcParam d t) =
      map.drawing.drawing.h (orientedArc M d t)

namespace InfiniteBoundaryMapEquiv

/-- Helper toward Definition 3.2: the edge bijection acts on oriented darts
without changing their traversal bit. -/
@[expose] def mapDart (e : InfiniteBoundaryMapEquiv M M') (d : E × Bool) : E' × Bool :=
  (e.map.drawing.drawing.σE d.1, d.2)

/-- Helper toward Definition 3.2: the induced vertex bijection. -/
def mapVertexEquiv (e : InfiniteBoundaryMapEquiv M M') : V ≃ V' :=
  e.map.drawing.drawing.σV

/-- Helper toward Definition 3.2: the image face. -/
def faceMap (e : InfiniteBoundaryMapEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) :
    PlaneGraphDrawing.Face (Drawing M') :=
  e.map.drawing.drawing.faceMap F

/-- Helper toward Definition 3.2: present edges map to present edges. -/
def mapPresentEdge (e : InfiniteBoundaryMapEquiv M M')
    (d : PresentEdge M) : PresentEdge M' :=
  ⟨e.map.drawing.drawing.σE d.1,
    by simpa [e.map.drawing.missing_map] using d.2⟩

/-- Helper toward Definition 3.2: one indexed boundary side is pushed
forward, retaining its index type, successor map and endpoint data. -/
@[expose] def mapDarts (e : InfiniteBoundaryMapEquiv M M')
    {I : Type uI} (darts : I ↪ E × Bool) : I ↪ E' × Bool :=
  ⟨fun i => e.mapDart (darts i), by
    intro i j hij
    apply darts.injective
    exact (Equiv.prodCongr e.map.drawing.drawing.σE (Equiv.refl Bool)).injective hij⟩

/-- Helper toward Definition 3.2: the four indexed boundary sides are
pushed forward through an edge equivalence. -/
@[expose] def pushforward (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) :
    InfiniteBoundaryPresentation.{uV', uE', uUL, uUR, uLR, uLL} M' where
  upperLeft := {
    Index := P.upperLeft.Index
    darts := e.mapDarts P.upperLeft.darts
    next := P.upperLeft.next
    initialVertex? := P.upperLeft.initialVertex?.map e.mapVertexEquiv
    terminalVertex? := P.upperLeft.terminalVertex?.map e.mapVertexEquiv }
  upperRight := {
    Index := P.upperRight.Index
    darts := e.mapDarts P.upperRight.darts
    next := P.upperRight.next
    initialVertex? := P.upperRight.initialVertex?.map e.mapVertexEquiv
    terminalVertex? := P.upperRight.terminalVertex?.map e.mapVertexEquiv }
  lowerRight := {
    Index := P.lowerRight.Index
    darts := e.mapDarts P.lowerRight.darts
    next := P.lowerRight.next
    initialVertex? := P.lowerRight.initialVertex?.map e.mapVertexEquiv
    terminalVertex? := P.lowerRight.terminalVertex?.map e.mapVertexEquiv }
  lowerLeft := {
    Index := P.lowerLeft.Index
    darts := e.mapDarts P.lowerLeft.darts
    next := P.lowerLeft.next
    initialVertex? := P.lowerLeft.initialVertex?.map e.mapVertexEquiv
    terminalVertex? := P.lowerLeft.terminalVertex?.map e.mapVertexEquiv }

@[simp] theorem pushforward_upperRight_darts (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (i : P.upperRight.Index) :
    (e.pushforward P).upperRight.darts i = e.mapDart (P.upperRight.darts i) := rfl

@[simp] theorem pushforward_lowerLeft_darts (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (i : P.lowerLeft.Index) :
    (e.pushforward P).lowerLeft.darts i = e.mapDart (P.lowerLeft.darts i) := rfl

@[simp] theorem mapDarts_apply (e : InfiniteBoundaryMapEquiv M M')
    {I : Type uI} (darts : I ↪ E × Bool) (i : I) :
    e.mapDarts darts i = e.mapDart (darts i) := rfl

/-- Helper toward Definition 3.2: external-face status is preserved. -/
theorem isExternal_faceMap_iff (e : InfiniteBoundaryMapEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) :
    (Drawing M').IsExternal (e.faceMap F) ↔ (Drawing M).IsExternal F :=
  e.map.drawing.drawing.isExternal_faceMap_iff F

/-- Helper toward Definition 3.2: initial vertices of darts commute with
the vertex bijection. -/
theorem boundaryDartInitial_map (e : InfiniteBoundaryMapEquiv M M')
    (d : E × Bool) :
    boundaryDartInitial M' (e.mapDart d) =
      e.mapVertexEquiv (boundaryDartInitial M d) := by
  cases d with
  | mk a b =>
    cases b <;>
      simp [boundaryDartInitial_eq, mapDart, mapVertexEquiv,
        e.map.drawing.drawing.src_map, e.map.drawing.drawing.tgt_map]

/-- Helper toward Definition 3.2: terminal vertices of darts commute with
the vertex bijection. -/
theorem boundaryDartTerminal_map (e : InfiniteBoundaryMapEquiv M M')
    (d : E × Bool) :
    boundaryDartTerminal M' (e.mapDart d) =
      e.mapVertexEquiv (boundaryDartTerminal M d) := by
  cases d with
  | mk a b =>
    cases b <;>
      simp [boundaryDartTerminal_eq, mapDart, mapVertexEquiv,
        e.map.drawing.drawing.src_map, e.map.drawing.drawing.tgt_map]

/-- Helper toward Definition 3.2: the upper-right predicate transports
exactly under missing-tag and endpoint-join preservation. -/
theorem UROkInf_pushforward_iff (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) :
    UROkInf (e.pushforward P) ↔ UROkInf P := by
  rw [UROkInf_iff, UROkInf_iff]
  simp only [pushforward]
  constructor
  · rintro ⟨hm, hj⟩
    constructor
    · intro i
      have hi := hm i
      exact (e.map.drawing.missing_map (P.upperRight.darts i).1).mp hi
    · intro i j hn
      have h := hj i j hn
      change boundaryDartTerminal M'
          (e.mapDart (P.upperRight.darts i)) =
        boundaryDartInitial M' (e.mapDart (P.upperRight.darts j)) at h
      have h' : e.mapVertexEquiv (boundaryDartTerminal M (P.upperRight.darts i)) =
          e.mapVertexEquiv (boundaryDartInitial M (P.upperRight.darts j)) := by
        simpa only [boundaryDartTerminal_map,
          boundaryDartInitial_map] using h
      exact e.mapVertexEquiv.injective h'
  · rintro ⟨hm, hj⟩
    constructor
    · intro i
      have hi := hm i
      change M'.toPlaneMapWithMissing.missing
        (e.map.drawing.drawing.σE (P.upperRight.darts i).1)
      exact (e.map.drawing.missing_map (P.upperRight.darts i).1).mpr hi
    · intro i j hn
      have h := congrArg e.mapVertexEquiv (hj i j hn)
      change boundaryDartTerminal M'
          (e.mapDart (P.upperRight.darts i)) =
        boundaryDartInitial M' (e.mapDart (P.upperRight.darts j))
      simpa only [boundaryDartTerminal_map,
        boundaryDartInitial_map] using h

/-- Helper toward Definition 3.2: the lower-left predicate transports
exactly under missing-tag and endpoint-join preservation. -/
theorem LLOkInf_pushforward_iff (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) :
    LLOkInf (e.pushforward P) ↔ LLOkInf P := by
  rw [LLOkInf_iff, LLOkInf_iff]
  simp only [pushforward]
  constructor
  · rintro ⟨hm, hj⟩
    constructor
    · intro i
      have hi := hm i
      exact (e.map.drawing.missing_map (P.lowerLeft.darts i).1).mp hi
    · intro i j hn
      have h := hj i j hn
      change boundaryDartTerminal M'
          (e.mapDart (P.lowerLeft.darts i)) =
        boundaryDartInitial M' (e.mapDart (P.lowerLeft.darts j)) at h
      have h' : e.mapVertexEquiv (boundaryDartTerminal M (P.lowerLeft.darts i)) =
          e.mapVertexEquiv (boundaryDartInitial M (P.lowerLeft.darts j)) := by
        simpa only [boundaryDartTerminal_map,
          boundaryDartInitial_map] using h
      exact e.mapVertexEquiv.injective h'
  · rintro ⟨hm, hj⟩
    constructor
    · intro i
      have hi := hm i
      change M'.toPlaneMapWithMissing.missing
        (e.map.drawing.drawing.σE (P.lowerLeft.darts i).1)
      exact (e.map.drawing.missing_map (P.lowerLeft.darts i).1).mpr hi
    · intro i j hn
      have h := congrArg e.mapVertexEquiv (hj i j hn)
      change boundaryDartTerminal M'
          (e.mapDart (P.lowerLeft.darts i)) =
        boundaryDartInitial M' (e.mapDart (P.lowerLeft.darts j))
      simpa only [boundaryDartTerminal_map,
        boundaryDartInitial_map] using h













end InfiniteBoundaryMapEquiv

end DirectedDistances.PlanarMap

end
