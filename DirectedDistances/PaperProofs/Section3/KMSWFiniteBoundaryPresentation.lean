/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder5
public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder7
public import DirectedDistances.KMSW.StageBoundaryMap
public import DirectedDistances.KMSW.StageIncidenceChains
public import DirectedDistances.KMSW.KMSWStageFrontierChain
public import DirectedDistances.PaperProofs.Section3.KMSWBdyOuterFace

/-! combinatorics. The imported run lemmas do not construct a geometric boundary
presentation; no geometric correspondence or paper-result claim is made here. -/

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the ordered four-run outer word and its
face-successor rule, in UL, UR, reversed LR, reversed LL order. -/
theorem kmswStage_finite_outer_run_decomposition (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWordVal w n =
      ((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false)) ++
      ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
      ((kmswStage w n).LL.reverse.map fun e => (e, true)) ∧
    ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d :=
  kmswStage_outer_face_orbit_runs w n

/-- Helper toward Definition 3.2: the finite four-run boundary chain
present and missing runs. -/
theorem kmswStage_finite_run_endpoint_invariant (w : ℕ → Fin 3) (n : ℕ) :
    kmswBoundaryChainInvariant (kmswStage w n) :=
  kmswStage_boundary_chain_invariant w n

/-- Helper toward Definition 3.2: the finite run-endpoint record identifies
the UL/UR junction with the active edge's east endpoint and the LL/UL
junction with the first UL edge's west endpoint; it also records each run's
chain and present/missing status. -/
theorem kmswStage_finite_run_junction_record (w : ℕ → Fin 3) (n : ℕ) :
    KMSWStageFrontierChain w n :=
  kmswStageFrontierChain_all w n

/-- Helper toward Definition 3.2: the UR west darts and LL east darts in the
finite run decomposition are missing and lie on the distinguished outer
face. -/
theorem kmswStage_finite_missing_run_darts (w : ℕ → Fin 3) (n : ℕ) :
    (∀ e : Fin (kmswStage w n).nextEdge,
      e.val ∈ (kmswStage w n).UR →
        (kmswStageDirectedMap w n).missing (e, false) ∧
          (kmswStageDirectedMap w n).IsOuter (e, false)) ∧
    (∀ e : Fin (kmswStage w n).nextEdge,
      e.val ∈ (kmswStage w n).LL →
        (kmswStageDirectedMap w n).missing (e, true) ∧
          (kmswStageDirectedMap w n).IsOuter (e, true)) := by
  constructor
  · intro e he
    exact (kmswStageDirectedMap_UR_west w n e).mpr he
  · intro e he
    exact (kmswStageDirectedMap_LL_east w n e).mpr he

/-- Helper toward Definition 3.2: each outer-face dart belongs to exactly
one of the four finite KMSW boundary runs. -/
theorem kmswStage_finite_outer_dart_run_partition (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : (kmswStageDirectedMap w n).IsOuter d) :
    (d ∈ kmswStageULDartsFinset w n ∧
        d ∉ kmswStageURDartsFinset w n ∧ d ∉ kmswStageLRDartsFinset w n ∧
          d ∉ kmswStageLLDartsFinset w n) ∨
      (d ∈ kmswStageURDartsFinset w n ∧
        d ∉ kmswStageULDartsFinset w n ∧ d ∉ kmswStageLRDartsFinset w n ∧
          d ∉ kmswStageLLDartsFinset w n) ∨
      (d ∈ kmswStageLRDartsFinset w n ∧
        d ∉ kmswStageULDartsFinset w n ∧ d ∉ kmswStageURDartsFinset w n ∧
          d ∉ kmswStageLLDartsFinset w n) ∨
      (d ∈ kmswStageLLDartsFinset w n ∧
        d ∉ kmswStageULDartsFinset w n ∧ d ∉ kmswStageURDartsFinset w n ∧
          d ∉ kmswStageLRDartsFinset w n) :=
  kmswStage_outer_dart_exactly_one w n d hd

/-- Helper toward Definition 3.2: the finite cyclic position successor of the
four-run word is the KMSW face successor. -/
theorem kmswStage_finite_outer_position_successor (w : ℕ → Fin 3) (n : ℕ) :
    ∀ i (hi : i < (stageOuterWord w n).length),
      (kmswStageDirectedMap w n).toCombinatorialMap.faceSucc
          ((stageOuterWord w n)[i]'hi) =
        (stageOuterWord w n)[(i + 1) % (stageOuterWord w n).length]'
          (Nat.mod_lt _ (Nat.zero_le i |>.trans_lt hi)) := by
  exact (kmsw_bdy_outer_face_cyclic_order w n).2.2




















































end DirectedDistances.PaperProofs.Section3
end
