/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation5
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package2

/-! module records endpoint transport for a finite stage map and the remaining
carrier obstruction. It does not assert a map construction or paper completion. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the stage drawing induces a plane drawing
on the allocated edge-ID carrier by taking the reversed (east-to-west) path
for each edge ID. -/
@[expose] noncomputable def kmswStageFiniteBoundaryPresentation6PlaneDrawing
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) :
    PlaneGraphDrawing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge) where
  src e := stageVertex w n (e, true)
  tgt e := stageVertex w n (e, false)
  pos := P.pos
  pos_injective := P.pos_injective
  arc e := (P.arc (e, true)).toPath.cast
    (P.arc_start (e, true)).symm (P.arc_finish (e, true)).symm
  arc_injOn e := (P.arc (e, true)).toPath_injOn
    (P.arc_length (e, true)) (P.arc_simple (e, true))
  openArc_disjoint := by
    intro e f hef
    change Disjoint ((P.arc (e, true)).toPath '' openParams)
      ((P.arc (f, true)).toPath '' openParams)
    rw [Polyline.toPath_image_openParams _ (P.arc_length (e, true))
        (P.arc_simple (e, true)),
      Polyline.toPath_image_openParams _ (P.arc_length (f, true))
        (P.arc_simple (f, true))]
    apply P.interior_disjoint
    · intro h
      apply hef
      exact (congrArg Prod.fst h).symm
    · intro h
      have hb := congrArg Prod.snd h
      simp [edgeFlip] at hb
  openArc_avoids := by
    intro e v
    change P.pos v ∉ (P.arc (e, true)).toPath '' openParams
    rw [Polyline.toPath_image_openParams _ (P.arc_length (e, true))
      (P.arc_simple (e, true))]
    exact P.interior_avoids_vertices (e, true) v

/-- Helper toward Definition 3.2: the finite stage plane map built directly
on edge IDs has no missing edges and orients every edge west to east. -/
@[expose] noncomputable def kmswStageFiniteBoundaryPresentation6DirectedPlaneMap
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) :
    DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge) where
  toPlaneMapWithMissing :=
    { toPlaneGraphDrawing := kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P
      missing := fun _ => False
      missing_on_external := by
        intro e he
        exact False.elim he }
  forward := fun _ => false

/-- Helper toward Definition 3.2: the constructed map's directed edge tail
and head are the stage's west and east vertices, respectively. -/
theorem kmswStageFiniteBoundaryPresentation6_constructed_west_east
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (e : Fin (kmswStage w n).nextEdge) :
    let M := kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P
    M.tail ⟨e, by simp [M, kmswStageFiniteBoundaryPresentation6DirectedPlaneMap]⟩ =
      stageVertex w n (e, false) ∧
    M.head ⟨e, by simp [M, kmswStageFiniteBoundaryPresentation6DirectedPlaneMap]⟩ =
      stageVertex w n (e, true) := by
  dsimp only
  simp [DirectedPlaneMapWithMissing.tail, DirectedPlaneMapWithMissing.head,
    kmswStageFiniteBoundaryPresentation6DirectedPlaneMap,
    kmswStageFiniteBoundaryPresentation6PlaneDrawing, edgeFlip]

/-- Helper toward Definition 3.2: the no-missing stage map's initial dart
endpoint agrees with `stageVertex` on the finite `Fin` edge carrier. -/
theorem kmswStageFiniteBoundaryPresentation6_constructed_initial_endpoint
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) :
    boundaryDartInitial (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P) d =
      stageVertex w n d := by
  cases d with
  | mk e b => cases b <;>
      simp [boundaryDartInitial_eq,
        kmswStageFiniteBoundaryPresentation6DirectedPlaneMap,
        kmswStageFiniteBoundaryPresentation6PlaneDrawing, edgeFlip]

/-- Helper toward Definition 3.2: the no-missing stage map's terminal dart
endpoint agrees with the stage vertex at the reversed dart. -/
theorem kmswStageFiniteBoundaryPresentation6_constructed_terminal_endpoint
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) :
    boundaryDartTerminal (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P) d =
      stageVertex w n (edgeFlip _ d) := by
  calc
    boundaryDartTerminal (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P) d =
        boundaryDartInitial (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P)
          (edgeFlip _ d) := by
      cases d with
      | mk e b => cases b <;>
          simp [boundaryDartTerminal_eq, boundaryDartInitial_eq, edgeFlip]
    _ = stageVertex w n (edgeFlip _ d) :=
      kmswStageFiniteBoundaryPresentation6_constructed_initial_endpoint w n P
        (edgeFlip _ d)

/-- Helper toward Definition 3.2: the stage-map realization's initial-endpoint
clause identifies every actual initial endpoint with its KMSW stage vertex. -/
theorem kmswStageFiniteBoundaryPresentation6_initial_endpoint
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (d : StageDart (kmswStage w n).nextEdge) :
    boundaryDartInitial M d = stageVertex w n d :=
  hreal.2.1 d

/-- Helper toward Definition 3.2: once a stage-map realization identifies
initial endpoints, terminal endpoints are identified by reversing the dart. -/
theorem kmswStageFiniteBoundaryPresentation6_terminal_endpoint
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (d : StageDart (kmswStage w n).nextEdge) :
    boundaryDartTerminal M d = stageVertex w n (edgeFlip _ d) := by
  calc
    boundaryDartTerminal M d = boundaryDartInitial M (edgeFlip _ d) := by
      cases d with
      | mk e b => cases b <;>
          simp [boundaryDartTerminal_eq, boundaryDartInitial_eq, edgeFlip]
    _ = stageVertex w n (edgeFlip _ d) :=
      kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal
        (edgeFlip _ d)















































end DirectedDistances.PaperProofs.Section3
