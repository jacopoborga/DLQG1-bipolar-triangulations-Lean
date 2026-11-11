/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation8

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: a nonempty finite run side has the exact
endpoint labels when its first and last darts realize the supplied marks. -/
theorem kmswFiniteRunSide10_endpointLabels
    {V E : Type*} (M : DirectedPlaneMapWithMissing V E)
    (ds : List (E × Bool)) (hnd : ds.Nodup) (initial terminal : V)
    (hne : ds ≠ [])
    (hfirst : boundaryDartInitial M (ds.head hne) = initial)
    (hlast : boundaryDartTerminal M (ds.getLast hne) = terminal) :
    BoundarySideEndpointLabels M (kmswFiniteRunSide ds hnd initial terminal) := by
  have hpos : 0 < ds.length := by
    cases ds with
    | nil => contradiction
    | cons d ds => simp
  let first : Fin ds.length := ⟨0, hpos⟩
  let last : Fin ds.length := ⟨ds.length - 1, by omega⟩
  unfold BoundarySideEndpointLabels
  constructor
  · intro v hv
    have hv : initial = v := Option.some.inj hv
    subst v
    constructor
    · intro _
      refine ⟨first, ?_, ?_⟩
      · intro j hnext
        change kmswFiniteRunNext j = some first at hnext
        simp [kmswFiniteRunNext, first] at hnext
      · change boundaryDartInitial M (ds[0]'hpos) = initial
        rw [← List.head_eq_getElem_zero hne]
        exact hfirst
    · intro i hi
      have hi0 : i.val = 0 := by
        by_contra hzero
        have hpositive : 0 < i.val := Nat.pos_of_ne_zero (by omega)
        let j : Fin ds.length := ⟨i.val - 1, by omega⟩
        have hj : kmswFiniteRunNext j = some i := by
          unfold kmswFiniteRunNext
          rw [dif_pos (by dsimp [j]; omega)]
          congr 1
          apply Fin.ext
          dsimp [j]
          omega
        change kmswFiniteRunNext j = some i at hj
        exact hi j hj
      have hiEq : i = first := Fin.ext hi0
      subst i
      change boundaryDartInitial M (ds[0]'hpos) = initial
      rw [← List.head_eq_getElem_zero hne]
      exact hfirst
  · constructor
    · intro v hv
      have hv : terminal = v := Option.some.inj hv
      subst v
      constructor
      · intro _
        refine ⟨last, ?_, ?_⟩
        · simp [kmswFiniteRunSide, kmswFiniteRunNext, last]
          omega
        · change boundaryDartTerminal M (ds[ds.length - 1]'last.isLt) = terminal
          rw [← List.getLast_eq_getElem hne]
          exact hlast
      · intro i hi
        have hiLast : i.val = ds.length - 1 := by
          by_contra hval
          have hlt : i.val + 1 < ds.length := by omega
          have hnext : kmswFiniteRunNext i = some ⟨i.val + 1, hlt⟩ := by
            simp [kmswFiniteRunNext, hlt]
          change kmswFiniteRunNext i = none at hi
          rw [hnext] at hi
          cases hi
        have hiEq : i = last := Fin.ext hiLast
        subst i
        change boundaryDartTerminal M (ds[ds.length - 1]'last.isLt) = terminal
        rw [← List.getLast_eq_getElem hne]
        exact hlast
    · intro hempty
      exact isEmptyElim (hempty.false first)

/-- Helper toward Definition 3.2: the exact-tag upper-left run has its
transferred initial and terminal endpoint labels. -/
theorem kmswStageFiniteBoundaryPresentation10_upperLeft_endpointLabels
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    BoundarySideEndpointLabels
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      (kmswStageFiniteBoundaryPresentation w n
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        (kmswStageFiniteBoundaryPresentation5Junctions w n)).upperLeft := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  let ds := kmswStageULDartRun w n
  have hnd := (kmswStage_finite_run_nodup w n).1
  have hne := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have hfirst := kmswStageFiniteBoundaryPresentation8_upperLeft_first_initial
    w n P U hU hborder
  have hlast := kmswStageFiniteBoundaryPresentation8_upperLeft_last_terminal
    w n P U hU hborder
  change BoundarySideEndpointLabels M (kmswFiniteRunSide ds hnd
    J.lowerLeftUpperLeft J.upperLeftUpperRight)
  exact kmswFiniteRunSide10_endpointLabels M ds hnd
    J.lowerLeftUpperLeft J.upperLeftUpperRight hne hfirst hlast

/-- Helper toward Definition 3.2: the exact-tag lower-right run has its
transferred initial and terminal endpoint labels. -/
theorem kmswStageFiniteBoundaryPresentation10_lowerRight_endpointLabels
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    BoundarySideEndpointLabels
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      (kmswStageFiniteBoundaryPresentation w n
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        (kmswStageFiniteBoundaryPresentation5Junctions w n)).lowerRight := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  let ds := kmswStageLRDartRun w n
  have hnd := (kmswStage_finite_run_nodup w n).2.2.1
  have hne := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  have hfirst := kmswStageFiniteBoundaryPresentation8_lowerRight_first_initial
    w n P U hU hborder
  have hlast := kmswStageFiniteBoundaryPresentation8_lowerRight_last_terminal
    w n P U hU hborder
  change BoundarySideEndpointLabels M (kmswFiniteRunSide ds hnd
    J.upperRightLowerRight J.lowerRightLowerLeft)
  exact kmswFiniteRunSide10_endpointLabels M ds hnd
    J.upperRightLowerRight J.lowerRightLowerLeft hne hfirst hlast

/-- Helper toward Definition 3.2: when the upper-right missing run is empty,
the concrete four-corner record identifies its two endpoint vertices. -/
theorem kmswStageFiniteBoundaryPresentation10_upperRight_empty_corner_eq
    (w : ℕ → Fin 3) (n : ℕ)
    (hempty : (kmswStage w n).UR = []) :
    (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight := by
  let s := kmswStage w n
  have hchain := kmswStage_boundary_chain_invariant w n
  rcases hchain with ⟨_, _, _, _, hLRne, _, hURempty⟩
  have hend : s.east s.active = s.east (s.LR.getLast hLRne) :=
    hURempty hLRne (by simpa [s] using hempty)
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hULne := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have hLRrunne := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  have hULlast : (kmswStageULDartRun w n).getLast hULne =
      ((⟨s.active, act_lt_nextEdge w (Nat.le_refl n)⟩ : Fin s.nextEdge), false) := by
    simp [kmswStageULDartRun, stageDarts, hxs, s]
  have hLRhead : (kmswStageLRDartRun w n).head hLRrunne =
      ((⟨s.LR.getLast hLRne, stageRun_edge_bound w n _
        (Or.inr (List.getLast_mem hLRne))⟩ : Fin s.nextEdge), true) := by
    simp [kmswStageLRDartRun, stageDarts, s]
  apply Fin.ext
  rw [kmswStageFiniteBoundaryPresentation5_upperLeftUpperRight,
    kmswStageFiniteBoundaryPresentation5_upperRightLowerRight,
    hULlast, hLRhead]
  simpa [stageVertex, stageEndpoint, edgeFlip, s] using hend

/-- Helper toward Definition 3.2: an empty upper-right side has its endpoint
labels by the derived equality of the concrete four-corner vertices. -/
theorem kmswStageFiniteBoundaryPresentation10_upperRight_endpointLabels_of_empty
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (hempty : (kmswStage w n).UR = []) :
    BoundarySideEndpointLabels
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      (kmswStageFiniteBoundaryPresentation w n
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        (kmswStageFiniteBoundaryPresentation5Junctions w n)).upperRight := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  let ds := kmswStageURDartRun w n
  have hcorner := kmswStageFiniteBoundaryPresentation10_upperRight_empty_corner_eq w n hempty
  have hrun : ds = [] := by simp [ds, kmswStageURDartRun, stageDarts, hempty]
  have hnd := (kmswStage_finite_run_nodup w n).2.1
  change BoundarySideEndpointLabels M
    (kmswFiniteRunSide ds hnd J.upperLeftUpperRight J.upperRightLowerRight)
  have hmarks : J.upperLeftUpperRight = J.upperRightLowerRight := by
    simpa [J] using hcorner
  simpa [BoundarySideEndpointLabels, kmswFiniteRunSide, kmswFiniteRunNext,
    hrun, hmarks]

/-- Helper toward Definition 3.2: when the upper-right run is nonempty, its
first and last darts meet the concrete upper-left and lower-right corners. -/
theorem kmswStageFiniteBoundaryPresentation10_upperRight_nonempty_endpoints
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (hne : kmswStageURDartRun w n ≠ []) :
    (boundaryDartInitial
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        ((kmswStageURDartRun w n).head hne) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight) ∧
    (boundaryDartTerminal
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        ((kmswStageURDartRun w n).getLast hne) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight) := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let ds := kmswStageURDartRun w n
  let s := kmswStage w n
  have hULne := (kmswStage_UL_nonempty_active_last w n).1
  have hLRne := kmswStage_LR_nonempty w n
  have hURne : s.UR ≠ [] := by
    intro h
    apply hne
    simp [ds, kmswStageURDartRun, stageDarts, s, h]
  have hrun := kmswStage_boundary_chain_invariant w n
  have hfirst : boundaryDartInitial M (ds.head hne) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight := by
    cases hr : s.UR with
    | nil => exact (hURne hr).elim
    | cons e es =>
      have hrel : s.east (s.UL.getLast hULne) = s.west e := by
        have hsplit : s.UL.dropLast ++ [s.UL.getLast hULne] = s.UL :=
          List.dropLast_append_getLast hULne
        have heq : s.UL ++ s.UR =
            s.UL.dropLast ++ s.UL.getLast hULne :: e :: es := by
          rw [hr]
          calc
            s.UL ++ e :: es = (s.UL.dropLast ++ [s.UL.getLast hULne]) ++ e :: es :=
              congrArg (fun xs => xs ++ e :: es) hsplit.symm
            _ = s.UL.dropLast ++ s.UL.getLast hULne :: e :: es := by
              simp [List.append_assoc]
        exact (List.isChain_iff_forall_rel_of_append_cons_cons.mp hrun.1) heq
      have hd : ds.head hne =
          ((⟨e, stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inr (by simpa [s, hr] using List.head_mem (s := s.UR)))))⟩ : Fin s.nextEdge), false) := by
        simp [ds, kmswStageURDartRun, stageDarts, s, hr]
      have ⟨xs, hxs⟩ := kmswStage_UL_last w n
      have hULlast : (kmswStageULDartRun w n).getLast
          (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n) =
          ((⟨s.active, act_lt_nextEdge w (Nat.le_refl n)⟩ : Fin s.nextEdge), false) := by
        simp [kmswStageULDartRun, stageDarts, hxs, s]
      have hULlastEdge : s.UL.getLast hULne = s.active := by
        have hlast? : s.UL.getLast? = some s.active := by
          rw [hxs]
          simp [s]
        rw [List.getLast?_eq_getLast_of_ne_nil hULne] at hlast?
        simpa [s] using Option.some.inj hlast?
      rw [hULlastEdge] at hrel
      have hreal := kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
      calc
        boundaryDartInitial M (ds.head hne) = stageVertex w n (ds.head hne) := hreal.2.1 _
        _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight := by
          rw [hd, kmswStageFiniteBoundaryPresentation5_upperLeftUpperRight, hULlast]
          apply Fin.ext
          simpa [stageVertex, stageEndpoint, edgeFlip, s] using hrel.symm
  have hlast : boundaryDartTerminal M (ds.getLast hne) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight := by
    have hend := hrun.2.2.2.1
    have hlastEq : s.east (s.UR.getLast hURne) = s.east (s.LR.getLast hLRne) := by
      have hUpper : (s.UL ++ s.UR).getLast? = some (s.UR.getLast hURne) := by
        rw [List.getLast?_append_of_ne_nil s.UL hURne,
          List.getLast?_eq_getLast_of_ne_nil hURne]
      have hLower : (s.LL ++ s.LR).getLast? = some (s.LR.getLast hLRne) := by
        rw [List.getLast?_append_of_ne_nil s.LL hLRne,
          List.getLast?_eq_getLast_of_ne_nil hLRne]
      change Option.map s.east (s.UL ++ s.UR).getLast? =
        Option.map s.east (s.LL ++ s.LR).getLast? at hend
      rw [hUpper, hLower] at hend
      exact Option.some.inj (by simpa using hend)
    have hlastD : ds.getLast hne =
        ((⟨s.UR.getLast hURne, stageRun_edge_bound w n _
          (Or.inl (Or.inl (Or.inr (List.getLast_mem hURne))))⟩ : Fin s.nextEdge), false) := by
      simp [ds, kmswStageURDartRun, stageDarts, s]
    have hLRhead : (kmswStageLRDartRun w n).head
        (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n) =
        ((⟨s.LR.getLast hLRne, stageRun_edge_bound w n _
          (Or.inr (List.getLast_mem hLRne))⟩ : Fin s.nextEdge), true) := by
      simp [kmswStageLRDartRun, stageDarts, s]
    have hreal := kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
    calc
      boundaryDartTerminal M (ds.getLast hne) =
          stageVertex w n (edgeFlip _ (ds.getLast hne)) :=
        kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal _
      _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight := by
        rw [hlastD, kmswStageFiniteBoundaryPresentation5_upperRightLowerRight, hLRhead]
        apply Fin.ext
        simpa [stageVertex, stageEndpoint, edgeFlip, s] using hlastEq
  exact ⟨hfirst, hlast⟩

/-- Helper toward Definition 3.2: the exact-tag upper-right side has its
endpoint labels in both its empty and nonempty cases. -/
theorem kmswStageFiniteBoundaryPresentation10_upperRight_endpointLabels
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    BoundarySideEndpointLabels
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      (kmswStageFiniteBoundaryPresentation w n
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        (kmswStageFiniteBoundaryPresentation5Junctions w n)).upperRight := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  let ds := kmswStageURDartRun w n
  by_cases hne : ds = []
  · have hempty : (kmswStage w n).UR = [] := by
      by_contra h
      have hds : ds ≠ [] := by simp [ds, kmswStageURDartRun, stageDarts, h]
      exact hds hne
    exact kmswStageFiniteBoundaryPresentation10_upperRight_endpointLabels_of_empty
      w n P U hU hborder hempty
  · have hnd := (kmswStage_finite_run_nodup w n).2.1
    have he := kmswStageFiniteBoundaryPresentation10_upperRight_nonempty_endpoints
      w n P U hU hborder hne
    change BoundarySideEndpointLabels M
      (kmswFiniteRunSide ds hnd J.upperLeftUpperRight J.upperRightLowerRight)
    exact kmswFiniteRunSide10_endpointLabels M ds hnd
      J.upperLeftUpperRight J.upperRightLowerRight hne he.1 he.2

/-- Helper toward Definition 3.2: when the lower-left missing run is empty,
the concrete four-corner record identifies its two endpoint vertices. -/
theorem kmswStageFiniteBoundaryPresentation10_lowerLeft_empty_corner_eq
    (w : ℕ → Fin 3) (n : ℕ)
    (hempty : (kmswStage w n).LL = []) :
    (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft := by
  let s := kmswStage w n
  have hchain := kmswStage_boundary_chain_invariant w n
  rcases hchain with ⟨_, _, hstart, _, hLRne, _, _⟩
  have hULne := (kmswStage_UL_nonempty_active_last w n).1
  have hup : boundaryStart s (s.UL ++ s.UR) =
      some (s.west (s.UL.head hULne)) := by
    unfold boundaryStart
    rw [List.head?_append_of_ne_nil _ hULne, List.head?_eq_some_head hULne]
    rfl
  have hlow : boundaryStart s (s.LL ++ s.LR) =
      some (s.west (s.LR.head hLRne)) := by
    unfold boundaryStart
    rw [hempty]
    simp only [List.nil_append]
    rw [List.head?_eq_some_head hLRne]
    rfl
  have hvertices : s.west (s.UL.head hULne) = s.west (s.LR.head hLRne) := by
    rw [hup, hlow] at hstart
    exact Option.some.inj hstart
  have hULrunne := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have hLRrunne := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  have hULhead : (kmswStageULDartRun w n).head hULrunne =
      ((⟨s.UL.head hULne, stageRun_edge_bound w n _
        (Or.inl (Or.inl (Or.inl (List.head_mem _))))⟩ : Fin s.nextEdge), false) := by
    simp [kmswStageULDartRun, stageDarts, s]
  have hLRlast : (kmswStageLRDartRun w n).getLast hLRrunne =
      ((⟨s.LR.head hLRne, stageRun_edge_bound w n _
        (Or.inr (by simpa [s] using List.head_mem (s := s.LR)))⟩ : Fin s.nextEdge), true) := by
    simp [kmswStageLRDartRun, stageDarts, s]
  apply Fin.ext
  rw [kmswStageFiniteBoundaryPresentation5_lowerRightLowerLeft,
    kmswStageFiniteBoundaryPresentation5_lowerLeftUpperLeft,
    hLRlast, hULhead]
  simpa [stageVertex, stageEndpoint, edgeFlip, s] using hvertices.symm

/-- Helper toward Definition 3.2: an empty lower-left side has its endpoint
labels by the derived equality of the concrete four-corner vertices. -/
theorem kmswStageFiniteBoundaryPresentation10_lowerLeft_endpointLabels_of_empty
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (hempty : (kmswStage w n).LL = []) :
    BoundarySideEndpointLabels
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      (kmswStageFiniteBoundaryPresentation w n
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        (kmswStageFiniteBoundaryPresentation5Junctions w n)).lowerLeft := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  let ds := kmswStageLLDartRun w n
  have hcorner := kmswStageFiniteBoundaryPresentation10_lowerLeft_empty_corner_eq w n hempty
  have hrun : ds = [] := by simp [ds, kmswStageLLDartRun, stageDarts, hempty]
  have hnd := (kmswStage_finite_run_nodup w n).2.2.2
  change BoundarySideEndpointLabels M
    (kmswFiniteRunSide ds hnd J.lowerRightLowerLeft J.lowerLeftUpperLeft)
  have hmarks : J.lowerRightLowerLeft = J.lowerLeftUpperLeft := by
    simpa [J] using hcorner
  simpa [BoundarySideEndpointLabels, kmswFiniteRunSide, kmswFiniteRunNext,
    hrun, hmarks]

/-- Helper toward Definition 3.2: when the lower-left run is nonempty, its
first and last darts meet the concrete lower-right and upper-left corners. -/
theorem kmswStageFiniteBoundaryPresentation10_lowerLeft_nonempty_endpoints
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (hne : kmswStageLLDartRun w n ≠ []) :
    (boundaryDartInitial
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        ((kmswStageLLDartRun w n).head hne) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft) ∧
    (boundaryDartTerminal
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        ((kmswStageLLDartRun w n).getLast hne) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft) := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let ds := kmswStageLLDartRun w n
  let s := kmswStage w n
  have hULne := (kmswStage_UL_nonempty_active_last w n).1
  have hLRne := kmswStage_LR_nonempty w n
  have hLLne : s.LL ≠ [] := by
    intro h
    apply hne
    simp [ds, kmswStageLLDartRun, stageDarts, s, h]
  have hchain := kmswStage_boundary_chain_invariant w n
  obtain ⟨f, fs, hLR⟩ : ∃ f fs, s.LR = f :: fs := by
    cases hr : s.LR with
    | nil => exact (hLRne hr).elim
    | cons f fs => exact ⟨f, fs, rfl⟩
  have hfirst : boundaryDartInitial M (ds.head hne) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft := by
    cases hl : s.LL with
    | nil => exact (hLLne hl).elim
    | cons e es =>
      have hrel : s.east (s.LL.getLast hLLne) = s.west (s.LR.head hLRne) := by
        have hsplit : s.LL.dropLast ++ [s.LL.getLast hLLne] = s.LL :=
          List.dropLast_append_getLast hLLne
        have hlowerChain := hchain.2.1
        rw [hl, hLR] at hlowerChain
        have heq : s.LL ++ s.LR =
            s.LL.dropLast ++ s.LL.getLast hLLne :: f :: fs := by
          calc
            s.LL ++ s.LR = (s.LL.dropLast ++ [s.LL.getLast hLLne]) ++ s.LR :=
              congrArg (fun xs => xs ++ s.LR) hsplit.symm
            _ = s.LL.dropLast ++ s.LL.getLast hLLne :: f :: fs := by
              rw [hLR]
              simp [List.append_assoc]
        have heq' : e :: es ++ f :: fs =
            s.LL.dropLast ++ s.LL.getLast hLLne :: f :: fs := by
          simpa [hl, hLR] using heq
        have hrel' :=
          (List.isChain_iff_forall_rel_of_append_cons_cons.mp hlowerChain) heq'
        simpa [hl, hLR] using hrel'
      have hd : ds.head hne =
          ((⟨s.LL.getLast hLLne, stageRun_edge_bound w n _
            (Or.inl (Or.inr (List.getLast_mem hLLne)))⟩ : Fin s.nextEdge), true) := by
        simp [ds, kmswStageLLDartRun, stageDarts, s]
      have hLRlast : (kmswStageLRDartRun w n).getLast
          (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n) =
          ((⟨s.LR.head hLRne, stageRun_edge_bound w n _
            (Or.inr (by simpa [s] using List.head_mem (s := s.LR)))⟩ : Fin s.nextEdge), true) := by
        simp [kmswStageLRDartRun, stageDarts, s]
      have hreal := kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
      calc
        boundaryDartInitial M (ds.head hne) = stageVertex w n (ds.head hne) := hreal.2.1 _
        _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft := by
          rw [hd, kmswStageFiniteBoundaryPresentation5_lowerRightLowerLeft, hLRlast]
          apply Fin.ext
          simpa [stageVertex, stageEndpoint, edgeFlip, s] using hrel
  have hlast : boundaryDartTerminal M (ds.getLast hne) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft := by
    have hstart := hchain.2.2.1
    have hstartEq : s.west (s.LL.head hLLne) = s.west (s.UL.head hULne) := by
      have hupper : boundaryStart s (s.UL ++ s.UR) =
          some (s.west (s.UL.head hULne)) := by
        unfold boundaryStart
        rw [List.head?_append_of_ne_nil _ hULne, List.head?_eq_some_head hULne]
        rfl
      have hlower : boundaryStart s (s.LL ++ s.LR) =
          some (s.west (s.LL.head hLLne)) := by
        unfold boundaryStart
        rw [List.head?_append_of_ne_nil _ hLLne, List.head?_eq_some_head hLLne]
        rfl
      rw [hupper, hlower] at hstart
      exact Option.some.inj hstart.symm
    have hd : ds.getLast hne =
        ((⟨s.LL.head hLLne, stageRun_edge_bound w n _
          (Or.inl (Or.inr (List.head_mem _)))⟩ : Fin s.nextEdge), true) := by
      simp [ds, kmswStageLLDartRun, stageDarts, s]
    have hULhead : (kmswStageULDartRun w n).head
        (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n) =
        ((⟨s.UL.head hULne, stageRun_edge_bound w n _
          (Or.inl (Or.inl (Or.inl (List.head_mem _))))⟩ : Fin s.nextEdge), false) := by
      simp [kmswStageULDartRun, stageDarts, s]
    have hreal := kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
    calc
      boundaryDartTerminal M (ds.getLast hne) =
          stageVertex w n (edgeFlip _ (ds.getLast hne)) :=
        kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal _
      _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft := by
        rw [hd, kmswStageFiniteBoundaryPresentation5_lowerLeftUpperLeft, hULhead]
        apply Fin.ext
        simpa [stageVertex, stageEndpoint, edgeFlip, s] using hstartEq
  exact ⟨hfirst, hlast⟩

/-- Helper toward Definition 3.2: the exact-tag lower-left side has its
endpoint labels in both its empty and nonempty cases. -/
theorem kmswStageFiniteBoundaryPresentation10_lowerLeft_endpointLabels
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    BoundarySideEndpointLabels
      (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
      (kmswStageFiniteBoundaryPresentation w n
        (kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder)
        (kmswStageFiniteBoundaryPresentation5Junctions w n)).lowerLeft := by
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  let ds := kmswStageLLDartRun w n
  by_cases hne : ds = []
  · have hempty : (kmswStage w n).LL = [] := by
      by_contra h
      have hds : ds ≠ [] := by simp [ds, kmswStageLLDartRun, stageDarts, h]
      exact hds hne
    exact kmswStageFiniteBoundaryPresentation10_lowerLeft_endpointLabels_of_empty
      w n P U hU hborder hempty
  · have hnd := (kmswStage_finite_run_nodup w n).2.2.2
    have he := kmswStageFiniteBoundaryPresentation10_lowerLeft_nonempty_endpoints
      w n P U hU hborder hne
    change BoundarySideEndpointLabels M
      (kmswFiniteRunSide ds hnd J.lowerRightLowerLeft J.lowerLeftUpperLeft)
    exact kmswFiniteRunSide10_endpointLabels M ds hnd
      J.lowerRightLowerLeft J.lowerLeftUpperLeft hne he.1 he.2




























end DirectedDistances.PaperProofs.Section3
