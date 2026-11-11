/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWBdyFinal

 

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Every dart of the stage directed map lies on its distinguished external
face exactly when it belongs to the four-run outer word -/
theorem kmsw_stage_outer_face_exact (w : ℕ → Fin 3) (n : ℕ) :
    ∀ d, (kmswStageDirectedMap w n).IsOuter d ↔ d ∈ stageOuterWord w n := by
  intro d
  exact (mem_iff_isOuter (kmswStageDirectedMap w n)
    (stageOuterNonemptyWord w n) (kmsw_bdy_source_four_arcs w n).1.1 d).symm

/-- The directed stage map's underlying combinatorial map is the KMSW stage
map, so its `faceSucc` is the same permutation used by the outer-word cycle -/
theorem kmswStageDirectedMap_toCombinatorialMap (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageDirectedMap w n).toCombinatorialMap = kmswMap w n := rfl

/-- Both present segments are nonempty at every finite stage, and the active -/
theorem kmsw_bdy_outer_segments_nonempty (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL ≠ [] ∧
    (kmswStage w n).LR ≠ [] ∧
    (kmswStage w n).active ∈ (kmswStage w n).UL := by
  refine ⟨(kmswStage_UL_nonempty_active_last w n).1,
    kmswStage_LR_nonempty w n, ?_⟩
  obtain ⟨es, hUL⟩ := kmswStage_UL_last w n
  rw [hUL]
  simp

/-- The cyclic outer-face traversal is UL, UR, reversed LR, reversed LL, and
then back to UL. This is clockwise in the source figure. The source defines
the upper-left (resp. lower-right) boundary using edges oriented so that “the
external face ... is immediately to the left (resp. right) of e” and joins
the missing upper-right/lower-left runs between the corresponding endpoints
wording is “oriented so that the external face of $\frk m$ is immediately to
the left (resp.\ right) of $e$.” The word below agrees with that convention;
it traverses the drawn outer boundary clockwise. -/
theorem kmsw_bdy_outer_face_cyclic_order (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWordVal w n =
      ((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false)) ++
      ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
      ((kmswStage w n).LL.reverse.map fun e => (e, true)) ∧
    (∀ d ∈ stageOuterWord w n,
      (kmswStageDirectedMap w n).toCombinatorialMap.faceSucc d =
        (stageOuterWord w n).formPerm d) ∧
    (∀ i (hi : i < (stageOuterWord w n).length),
      (kmswStageDirectedMap w n).toCombinatorialMap.faceSucc
          ((stageOuterWord w n)[i]'hi) =
        (stageOuterWord w n)[(i + 1) % (stageOuterWord w n).length]'
          (Nat.mod_lt _ (Nat.zero_le i |>.trans_lt hi))) := by
  have h := kmsw_bdy_geometric_outer_order w n
  refine ⟨h.1, ?_, ?_⟩
  · intro d hd
    rw [kmswStageDirectedMap_toCombinatorialMap]
    exact h.2 d hd
  · intro i hi
    rw [kmswStageDirectedMap_toCombinatorialMap]
    exact kmsw_bdy_geometric_outer_successor w n i hi

/-- The upper-left segment is traversed in increasing record-time order from
the lower-left end toward the active edge. Its record-time list `recUL` is
increasing and maps to UL (`lem-kmsw-bdy` (iii), -/
theorem kmsw_bdy_outer_UL_record_order (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL = (recUL w n).map (act w) ∧
    (recUL w n).Pairwise (· < ·) := by
  classical
  constructor
  · simpa only [recUL] using (kmsw_bdy_source_ordered_boundary_lists w n).1
  · have hrange : (List.range (n + 1)).Pairwise (· < ·) :=
      List.pairwise_lt_range
    simpa only [recUL] using hrange.filter fun m =>
      decide (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j)

/- exact outer-face membership, underlying-map agreement, segment nonemptiness,
clockwise cyclic order, and increasing UL record-time order. This is a helper -/
theorem kmsw_bdy_outer_face_checks (w : ℕ → Fin 3) (n : ℕ) :
    (∀ d, (kmswStageDirectedMap w n).IsOuter d ↔ d ∈ stageOuterWord w n) ∧
    (kmswStageDirectedMap w n).toCombinatorialMap = kmswMap w n ∧
    ((kmswStage w n).UL ≠ [] ∧
      (kmswStage w n).LR ≠ [] ∧
      (kmswStage w n).active ∈ (kmswStage w n).UL) ∧
    (stageOuterWordVal w n =
        ((kmswStage w n).UL.map fun e => (e, false)) ++
        ((kmswStage w n).UR.map fun e => (e, false)) ++
        ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
        ((kmswStage w n).LL.reverse.map fun e => (e, true)) ∧
      (∀ d ∈ stageOuterWord w n,
        (kmswStageDirectedMap w n).toCombinatorialMap.faceSucc d =
          (stageOuterWord w n).formPerm d) ∧
      (∀ i (hi : i < (stageOuterWord w n).length),
        (kmswStageDirectedMap w n).toCombinatorialMap.faceSucc
            ((stageOuterWord w n)[i]'hi) =
          (stageOuterWord w n)[(i + 1) % (stageOuterWord w n).length]'
            (Nat.mod_lt _ (Nat.zero_le i |>.trans_lt hi)))) ∧
    ((kmswStage w n).UL = (recUL w n).map (act w) ∧
      (recUL w n).Pairwise (· < ·)) := by
  exact ⟨kmsw_stage_outer_face_exact w n,
    kmswStageDirectedMap_toCombinatorialMap w n,
    kmsw_bdy_outer_segments_nonempty w n,
    kmsw_bdy_outer_face_cyclic_order w n,
    kmsw_bdy_outer_UL_record_order w n⟩

end DirectedDistances.PaperProofs.Section3
