/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation

/-! four-run presentation data on the vertex and edge-ID carrier used by the KMSW
outer word. The map argument below is supplied data on that carrier; this file
does not identify it with a geometric realization of a stage drawing. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the finite side successor advances one
index in a `Fin n` interval and is absent at its last index. -/
@[expose] def kmswFiniteRunNext {n : ℕ} (i : Fin n) : Option (Fin n) :=
  if h : i.val + 1 < n then some ⟨i.val + 1, h⟩ else none

/-- Helper toward Definition 3.2: an ordered finite dart run with its given
initial and terminal endpoint labels. -/
@[expose] def kmswFiniteRunSide {V E : Type*} (ds : List (E × Bool))
    (hnd : ds.Nodup) (initial terminal : V) : InfiniteBoundarySide V E where
  Index := Fin ds.length
  darts := ⟨fun i => ds[i], by
    intro i j hij
    exact hnd.get_inj_iff.mp hij⟩
  next := kmswFiniteRunNext
  initialVertex? := some initial
  terminalVertex? := some terminal

/-- Helper toward Definition 3.2: each of the four dart runs is duplicate-free,
as follows from the cyclic outer word's duplicate-free property. -/
theorem kmswStage_finite_run_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageULDartRun w n).Nodup ∧
    (kmswStageURDartRun w n).Nodup ∧
    (kmswStageLRDartRun w n).Nodup ∧
    (kmswStageLLDartRun w n).Nodup := by
  have hword : (stageOuterWord w n).Nodup := stageOuterWord_nodup w n
  have hsplit : stageOuterWord w n =
      kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n := by
    simp [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
      kmswStageLRDartRun, kmswStageLLDartRun]
  rw [hsplit] at hword
  rcases List.nodup_append.mp hword with ⟨h₁, hLL, _⟩
  rcases List.nodup_append.mp h₁ with ⟨h₂, hLR, _⟩
  rcases List.nodup_append.mp h₂ with ⟨hUL, hUR, _⟩
  exact ⟨hUL, hUR, hLR, hLL⟩

variable (w : ℕ → Fin 3) (n : ℕ)

/-- Helper toward Definition 3.2: the four finite KMSW side index families
are the `Fin` types of their ordered run lengths, with darts read from the
corresponding run words and endpoint labels supplied by the retained junction
record. -/
@[expose] def kmswStageFiniteBoundaryPresentation
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    InfiniteBoundaryPresentation M := by
  have hnd := kmswStage_finite_run_nodup w n
  exact
    { upperLeft := kmswFiniteRunSide (kmswStageULDartRun w n) hnd.1
        J.lowerLeftUpperLeft J.upperLeftUpperRight
      upperRight := kmswFiniteRunSide (kmswStageURDartRun w n) hnd.2.1
        J.upperLeftUpperRight J.upperRightLowerRight
      lowerRight := kmswFiniteRunSide (kmswStageLRDartRun w n) hnd.2.2.1
        J.upperRightLowerRight J.lowerRightLowerLeft
      lowerLeft := kmswFiniteRunSide (kmswStageLLDartRun w n) hnd.2.2.2
        J.lowerRightLowerLeft J.lowerLeftUpperLeft }

/-- Helper toward Definition 3.2: the finite KMSW presentation retains the
supplied four-junction record. -/
@[expose] def kmswStageFiniteBoundaryPresentationWithJunctions
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    BoundaryPresentationWithJunctions M :=
  { presentation := kmswStageFiniteBoundaryPresentation w n M J
    finiteJunctions? := some J }

/-- Helper toward Definition 3.2: the eight endpoint labels of the finite
four-run presentation reproduce exactly its supplied junction record. This is
a statement about retained data; actual map-endpoint validity is separate. -/
theorem kmswStage_finite_boundary_junction_labels
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    FiniteBoundaryJunctionLabels6
      (kmswStageFiniteBoundaryPresentation w n M J) J := by
  simp [FiniteBoundaryJunctionLabels6, kmswStageFiniteBoundaryPresentation,
    kmswFiniteRunSide]

/-- Helper toward Definition 3.2: the wrapper's optional-junction clause is
exactly the eight equalities for its retained record. -/
theorem kmswStage_finite_boundary_supplied_junction_labels
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    SuppliedFiniteJunctionLabels6
      (kmswStageFiniteBoundaryPresentationWithJunctions w n M J) := by
  simp [SuppliedFiniteJunctionLabels6,
    kmswStageFiniteBoundaryPresentationWithJunctions,
    kmswStage_finite_boundary_junction_labels]

/-- Helper toward Definition 3.2: the UL side tag is zero at every finite
run index. -/
@[simp] theorem kmswStage_finite_boundary_sideTag_upperLeft
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageULDartRun w n).length) :
    sideTag (kmswStageFiniteBoundaryPresentation w n M J)
      (.upperLeft i) = 0 := rfl

/-- Helper toward Definition 3.2: the UR side tag is one at every finite
run index. -/
@[simp] theorem kmswStage_finite_boundary_sideTag_upperRight
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageURDartRun w n).length) :
    sideTag (kmswStageFiniteBoundaryPresentation w n M J)
      (.upperRight i) = 1 := rfl

/-- Helper toward Definition 3.2: the LR side tag is two at every finite
run index. -/
@[simp] theorem kmswStage_finite_boundary_sideTag_lowerRight
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageLRDartRun w n).length) :
    sideTag (kmswStageFiniteBoundaryPresentation w n M J)
      (.lowerRight i) = 2 := rfl

/-- Helper toward Definition 3.2: the LL side tag is three at every finite
run index. -/
@[simp] theorem kmswStage_finite_boundary_sideTag_lowerLeft
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageLLDartRun w n).length) :
    sideTag (kmswStageFiniteBoundaryPresentation w n M J)
      (.lowerLeft i) = 3 := rfl

/-- Helper toward Definition 3.2: UL's within-side successor is computed by
the finite index successor; its equality with the outer-face successor is
left open below because the presentation map still needs geometric transport. -/
theorem kmswStage_finite_boundary_sideNext_upperLeft
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageULDartRun w n).length) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J)
      (.upperLeft i) = Option.map InfiniteBoundaryDartIndex.upperLeft
        (kmswFiniteRunNext i) := by
  rfl

/-- Helper toward Definition 3.2: UR's within-side successor is computed by
the finite index successor. -/
theorem kmswStage_finite_boundary_sideNext_upperRight
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageURDartRun w n).length) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J)
      (.upperRight i) = Option.map InfiniteBoundaryDartIndex.upperRight
        (kmswFiniteRunNext i) := by
  rfl

/-- Helper toward Definition 3.2: LR's within-side successor is computed by
the finite index successor. -/
theorem kmswStage_finite_boundary_sideNext_lowerRight
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageLRDartRun w n).length) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J)
      (.lowerRight i) = Option.map InfiniteBoundaryDartIndex.lowerRight
        (kmswFiniteRunNext i) := by
  rfl

/-- Helper toward Definition 3.2: LL's within-side successor is computed by
the finite index successor. -/
theorem kmswStage_finite_boundary_sideNext_lowerLeft
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageLLDartRun w n).length) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J)
      (.lowerLeft i) = Option.map InfiniteBoundaryDartIndex.lowerLeft
        (kmswFiniteRunNext i) := by
  rfl

/-- Helper toward Definition 3.2: an interior UL index advances to its next
finite index. -/
@[simp] theorem kmswStage_finite_boundary_sideNext_upperLeft_succ
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageULDartRun w n).length)
    (hi : i.val + 1 < (kmswStageULDartRun w n).length) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J) (.upperLeft i) =
      some (.upperLeft ⟨i.val + 1, hi⟩) := by
  rw [kmswStage_finite_boundary_sideNext_upperLeft]
  simp only [kmswFiniteRunNext, dite_eq_left hi]
  rfl

/-- Helper toward Definition 3.2: an interior UR index advances to its next
finite index. -/
@[simp] theorem kmswStage_finite_boundary_sideNext_upperRight_succ
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageURDartRun w n).length)
    (hi : i.val + 1 < (kmswStageURDartRun w n).length) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J) (.upperRight i) =
      some (.upperRight ⟨i.val + 1, hi⟩) := by
  rw [kmswStage_finite_boundary_sideNext_upperRight]
  simp only [kmswFiniteRunNext, dite_eq_left hi]
  rfl

/-- Helper toward Definition 3.2: an interior LR index advances to its next
finite index in the reversed LR run. -/
@[simp] theorem kmswStage_finite_boundary_sideNext_lowerRight_succ
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageLRDartRun w n).length)
    (hi : i.val + 1 < (kmswStageLRDartRun w n).length) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J) (.lowerRight i) =
      some (.lowerRight ⟨i.val + 1, hi⟩) := by
  rw [kmswStage_finite_boundary_sideNext_lowerRight]
  simp only [kmswFiniteRunNext, dite_eq_left hi]
  rfl

/-- Helper toward Definition 3.2: an interior LL index advances to its next
finite index in the reversed LL run. -/
@[simp] theorem kmswStage_finite_boundary_sideNext_lowerLeft_succ
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i : Fin (kmswStageLLDartRun w n).length)
    (hi : i.val + 1 < (kmswStageLLDartRun w n).length) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J) (.lowerLeft i) =
      some (.lowerLeft ⟨i.val + 1, hi⟩) := by
  rw [kmswStage_finite_boundary_sideNext_lowerLeft]
  simp only [kmswFiniteRunNext, dite_eq_left hi]
  rfl

/-- Helper toward Definition 3.2: explicit integer position offsets for the
four sides of the finite cyclic word, cut immediately before UL. -/
@[expose] def kmswStageFiniteBoundaryPosition
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    InfiniteBoundaryDartIndex
      (kmswStageFiniteBoundaryPresentation w n M J) → ℤ
  | .upperLeft i => (i.val : ℤ)
  | .upperRight i =>
      ((kmswStageULDartRun w n).length + i.val : ℕ)
  | .lowerRight i =>
      ((kmswStageULDartRun w n).length + (kmswStageURDartRun w n).length + i.val : ℕ)
  | .lowerLeft i =>
      ((kmswStageULDartRun w n).length + (kmswStageURDartRun w n).length +
        (kmswStageLRDartRun w n).length + i.val : ℕ)



































































end DirectedDistances.PaperProofs.Section3
