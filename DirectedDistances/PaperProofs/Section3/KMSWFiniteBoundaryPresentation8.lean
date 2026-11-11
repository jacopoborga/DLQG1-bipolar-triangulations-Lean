/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation7
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation4

/-! module transfers the finite stage drawing to the exact missing-edge tags. It
does not assert paper completion. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the edge-ID plane drawing arc for edge `e`
has the same range as the stage's false dart polyline. -/
theorem kmswStageFiniteBoundaryPresentation8_arc_range
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (e : Fin (kmswStage w n).nextEdge) :
    Set.range
        ((kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).arc e) =
      (P.arc (e, false)).image := by
  change Set.range ((P.arc (e, true)).toPath.cast
    (P.arc_start (e, true)).symm (P.arc_finish (e, true)).symm) = _
  change Set.range (P.arc (e, true)).toPath = _
  rw [Polyline.range_toPath]
  exact P.arc_image_flip (e, false)

/-- Helper toward Definition 3.2: the edge-ID plane drawing has the same
drawing image as its underlying stage PL drawing. -/
theorem kmswStageFiniteBoundaryPresentation8_image_eq
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) :
    (kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).image =
      P.image := by
  change (Set.range P.pos ∪ ⋃ e : Fin (kmswStage w n).nextEdge,
      Set.range ((P.arc (e, true)).toPath.cast
        (P.arc_start (e, true)).symm (P.arc_finish (e, true)).symm)) =
    (Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image})
  ext z
  constructor
  · intro hz
    change z ∈ Set.range P.pos ∪ ⋃ e : Fin (kmswStage w n).nextEdge,
      Set.range ((P.arc (e, true)).toPath.cast
        (P.arc_start (e, true)).symm (P.arc_finish (e, true)).symm) at hz
    rcases hz with hpos | harc
    · exact Set.mem_union_left _ hpos
    · rw [Set.mem_iUnion] at harc
      rcases harc with ⟨e, he⟩
      have he' : z ∈ Set.range
          ((kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).arc e) := by
        exact he
      rw [kmswStageFiniteBoundaryPresentation8_arc_range w n P e] at he'
      change z ∈ Set.range P.pos ∪ {z | ∃ d : StageDart (kmswStage w n).nextEdge,
        z ∈ (P.arc d).image}
      exact Or.inr ⟨(e, false), he'⟩
  · intro hz
    change z ∈ Set.range P.pos ∪ {z | ∃ d : StageDart (kmswStage w n).nextEdge,
      z ∈ (P.arc d).image} at hz
    rcases hz with hpos | harc
    · exact Set.mem_union_left _ hpos
    · rcases harc with ⟨d, hd⟩
      apply Or.inr
      rw [Set.mem_iUnion]
      refine ⟨d.1, ?_⟩
      cases d with
      | mk e b =>
        cases b
        · change z ∈ Set.range
            ((kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).arc e)
          rw [kmswStageFiniteBoundaryPresentation8_arc_range w n P e]
          exact hd
        · have hflip : (P.arc (e, true)).image = (P.arc (e, false)).image :=
            P.arc_image_flip (e, false)
          change z ∈ Set.range
            ((kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).arc e)
          rw [kmswStageFiniteBoundaryPresentation8_arc_range w n P e]
          exact hflip ▸ hd

/-- Helper toward Definition 3.2: missing stage edges in the edge-ID drawing
lie in the closure of the unbounded face certified by the outer-dart
criterion. -/
theorem kmswStageFiniteBoundaryPresentation8_missing_external
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (e : Fin (kmswStage w n).nextEdge)
    (he : (kmswStageDirectedMap w n).missing (e, false)) :
    ∃ F : (kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).Face,
      PlaneGraphDrawing.IsExternal
        (kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P) F ∧
      Set.range
        ((kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).arc e) ⊆
          closure F.1 := by
  let d : StageDart (kmswStage w n).nextEdge := (e, false)
  have hd : (kmswStageDirectedMap w n).missing d := by simpa [d] using he
  rcases (kmswStageDirectedMap w n).missing_outer d hd with houter | houter
  · have hsurj : Function.Surjective (stageVertex w n) := by
      intro v
      obtain ⟨d, hd⟩ := stageEndpoint_exists w n v.val v.isLt
      exact ⟨d, Fin.ext (by simpa [stageVertex] using hd)⟩
    let F : (kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).Face :=
      ⟨U.val, by
        simpa [kmswStageFiniteBoundaryPresentation8_image_eq] using U.property⟩
    let F0 := P.toPlaneGraphDrawingFaceEquiv.symm U
    have hExt0 : P.toPlaneGraphDrawing.IsExternal F0 :=
      (P.toPlaneGraphDrawing_isExternal_iff F0).2 hU
    change ¬ Bornology.IsBounded F0.val at hExt0
    have hF0val : F0.val = U.val := rfl
    rw [hF0val] at hExt0
    have hsubset := P.dartBorders_arc_subset_closure hsurj d U
      ((hborder d).2 houter)
    refine ⟨F, ?_, ?_⟩
    · change ¬ Bornology.IsBounded F.val
      simpa [F] using hExt0
    · rw [kmswStageFiniteBoundaryPresentation8_arc_range]
      simpa [F] using hsubset
  · let d' : StageDart (kmswStage w n).nextEdge := edgeFlip _ d
    have hd' : (kmswStageDirectedMap w n).IsOuter d' := houter
    have hsurj : Function.Surjective (stageVertex w n) := by
      intro v
      obtain ⟨d, hd⟩ := stageEndpoint_exists w n v.val v.isLt
      exact ⟨d, Fin.ext (by simpa [stageVertex] using hd)⟩
    let F : (kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).Face :=
      ⟨U.val, by
        simpa [kmswStageFiniteBoundaryPresentation8_image_eq] using U.property⟩
    let F0 := P.toPlaneGraphDrawingFaceEquiv.symm U
    have hExt0 : P.toPlaneGraphDrawing.IsExternal F0 :=
      (P.toPlaneGraphDrawing_isExternal_iff F0).2 hU
    change ¬ Bornology.IsBounded F0.val at hExt0
    have hF0val : F0.val = U.val := rfl
    rw [hF0val] at hExt0
    have hsubset := P.dartBorders_arc_subset_closure hsurj d' U
      ((hborder d').2 hd')
    refine ⟨F, ?_, ?_⟩
    · change ¬ Bornology.IsBounded F.val
      simpa [F] using hExt0
    · rw [kmswStageFiniteBoundaryPresentation8_arc_range]
      have himage : (P.arc d').image = (P.arc d).image := by
        simpa [d, d', edgeFlip] using P.arc_image_flip d
      rw [← himage]
      simpa [F, d] using hsubset

/-- Helper toward Definition 3.2: the edge-ID plane map with the stage's exact
missing tags, using the supplied unbounded face to verify its external-face
field. -/
@[expose] noncomputable def kmswStageFiniteBoundaryPresentation8DirectedPlaneMap
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge) where
  toPlaneMapWithMissing :=
    { toPlaneGraphDrawing :=
        (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P).toPlaneMapWithMissing.toPlaneGraphDrawing
      missing := fun e => (kmswStageDirectedMap w n).missing (e, false)
      missing_on_external :=
        kmswStageFiniteBoundaryPresentation8_missing_external w n P U hU hborder }
  forward := fun _ => false

/-- Helper toward Definition 3.2: the exact-tag edge-ID map realizes the
finite stage drawing, including endpoint, arc, missingness, and orientation
clauses. -/
theorem kmswStageFiniteBoundaryPresentation8_realizes
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    kmsw_stage_map_realization32 w n P
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder) := by
  constructor
  · rfl
  constructor
  · intro d
    cases d with
    | mk e b => cases b <;>
        simp [boundaryDartInitial_eq,
          kmswStageFiniteBoundaryPresentation8DirectedPlaneMap,
          kmswStageFiniteBoundaryPresentation6DirectedPlaneMap,
          kmswStageFiniteBoundaryPresentation6PlaneDrawing,
          stageVertex, edgeFlip]
  constructor
  · intro d
    change Set.range
        ((kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P).toPlaneMapWithMissing.toPlaneGraphDrawing.arc d.1) =
      Set.range (P.arc d).toPath
    cases d with
    | mk e b =>
      cases b with
      | false =>
        change Set.range
          ((kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).arc e) =
            Set.range (P.arc (e, false)).toPath
        calc
          _ = (P.arc (e, false)).image :=
            kmswStageFiniteBoundaryPresentation8_arc_range w n P e
          _ = Set.range (P.arc (e, false)).toPath :=
            (Polyline.range_toPath _).symm
      | true =>
        change Set.range
          ((kmswStageFiniteBoundaryPresentation6PlaneDrawing w n P).arc e) =
            Set.range (P.arc (e, true)).toPath
        calc
          _ = (P.arc (e, false)).image :=
            kmswStageFiniteBoundaryPresentation8_arc_range w n P e
          _ = (P.arc (e, true)).image :=
            (P.arc_image_flip (e, false)).symm
          _ = Set.range (P.arc (e, true)).toPath :=
            (Polyline.range_toPath _).symm
  constructor
  · intro e
    rfl
  · intro e hp
    rfl

/-- Helper toward Definition 3.2: Stage 4's drawing and unique unbounded face
yield an exact-tag finite edge-ID map realizing the stage drawing. -/
theorem exists_kmswStageFiniteBoundaryPresentation8_realization
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (hU : P.IsUnbounded U)
      (_hunique : ∀ F : P.Face, P.IsUnbounded F → F = U)
      (hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
      kmsw_stage_map_realization32 w n P
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder) := by
  obtain ⟨P, U, hU, _hunique, hborder⟩ :=
    DirectedDistances.PaperProofs.Section5.kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter
      w n
  refine ⟨P, U, hU, _hunique, hborder, ?_⟩
  exact kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder

/-- Helper toward Definition 3.2: the exact-tag map retains the initial
upper-left endpoint identity from the no-missing edge-ID drawing. -/
theorem kmswStageFiniteBoundaryPresentation8_upperLeft_first_initial
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    boundaryDartInitial
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      ((kmswStageULDartRun w n).head
        (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  have hreal := kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
  calc
    boundaryDartInitial M ((kmswStageULDartRun w n).head
      (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) =
        stageVertex w n ((kmswStageULDartRun w n).head
          (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) :=
      hreal.2.1 _
    _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft := rfl

/-- Helper toward Definition 3.2: the exact-tag map retains the terminal
upper-left endpoint identity from the no-missing edge-ID drawing. -/
theorem kmswStageFiniteBoundaryPresentation8_upperLeft_last_terminal
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    boundaryDartTerminal
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      ((kmswStageULDartRun w n).getLast
        (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  have hreal := kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
  calc
    boundaryDartTerminal M ((kmswStageULDartRun w n).getLast
      (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) =
        stageVertex w n (edgeFlip _ ((kmswStageULDartRun w n).getLast
          (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n))) :=
      kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal _
    _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight := by
      simp [kmswStageFiniteBoundaryPresentation5Junctions]

/-- Helper toward Definition 3.2: the exact-tag map retains the initial
lower-right endpoint identity from the no-missing edge-ID drawing. -/
theorem kmswStageFiniteBoundaryPresentation8_lowerRight_first_initial
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    boundaryDartInitial
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      ((kmswStageLRDartRun w n).head
        (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  have hreal := kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
  calc
    boundaryDartInitial M ((kmswStageLRDartRun w n).head
      (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) =
        stageVertex w n ((kmswStageLRDartRun w n).head
          (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) :=
      hreal.2.1 _
    _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight := rfl

/-- Helper toward Definition 3.2: the exact-tag map retains the terminal
lower-right endpoint identity from the no-missing edge-ID drawing. -/
theorem kmswStageFiniteBoundaryPresentation8_lowerRight_last_terminal
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    boundaryDartTerminal
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      ((kmswStageLRDartRun w n).getLast
        (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  have hreal := kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
  calc
    boundaryDartTerminal M ((kmswStageLRDartRun w n).getLast
      (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) =
        stageVertex w n (edgeFlip _ ((kmswStageLRDartRun w n).getLast
          (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n))) :=
      kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal _
    _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft := by
      simp [kmswStageFiniteBoundaryPresentation5Junctions]

/-! Open boundary endpoint and finite-join statements, with full binders. For
`(w : ℕ → Fin 3) (n : ℕ)`, the drawing and unique unbounded face supplied by
`kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter` give `P`, `U`,
`hU : P.IsUnbounded U`, and `hborder : ∀ d, P.dartBorders d U ↔
(kmswStageDirectedMap w n).IsOuter d`. Put

    M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap
      w n P U hU hborder
    J := kmswStageFiniteBoundaryPresentation5Junctions w n
    Q := kmswStageFiniteBoundaryPresentation w n M J
    S := fun d => (stageRot w n).symm (d.1, !d.2)

The exact remaining side-label target is the conjunction

    BoundarySideEndpointLabels M Q.upperLeft ∧
    BoundarySideEndpointLabels M Q.upperRight ∧
    BoundarySideEndpointLabels M Q.lowerRight ∧
    BoundarySideEndpointLabels M Q.lowerLeft

and the exact remaining finite-join target is

    RequiredFiniteBoundaryJoinEndpointLabels7 Q S.

Three routes were tried before leaving these targets open. First, transfer the
four endpoint equalities from the no-missing drawing through the realization
theorem; this handles nonempty endpoints but leaves the empty-side equality
cases, which need equality of their adjacent junction vertices. Second, use
the retained `FiniteBoundaryJunctionLabels6` record directly; it identifies
the supplied optional labels but does not identify them with actual map
endpoints. Third, use the geometric successor result of
`KMSWFiniteBoundaryPresentation4` for all four runs; it controls successors
inside runs but leaves the cyclic transitions between runs and their endpoint
equalities unresolved in the exact finite-join predicate. No extra label,
interval-order, or geometric-correspondence premise is introduced. -/

end DirectedDistances.PaperProofs.Section3
