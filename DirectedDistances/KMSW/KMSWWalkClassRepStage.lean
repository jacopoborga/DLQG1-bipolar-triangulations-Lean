/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWForwardClass
public import DirectedDistances.PlanarMap.DirectedMapMarkMissing

/-! # The KMSW walk-class representative over its stage map

the canonical dart relabelling with the KMSW stage and its right boundary, then
transport a right-boundary prefix marking. Procedure reading legal-step convention remains -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- the canonical representative's directed map is isomorphic to the stage map; -/
@[expose] noncomputable def kmswWalkClassRep_mapIso {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    DirectedMapWithMissingIso (kmswWalkClassRep hn c).B.map
      (kmswStageDirectedMap (codeExtend c) (n - 1)) := by
  classical
  let B := kmswWalkClassBase hn c
  let D := StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge
  let e := Fintype.equivFin D
  let J := (B.transportIso e).symm
  change DirectedMapWithMissingIso (B.transport e).map B.map
  exact {
    toEquiv := J.toEquiv
    rot_comm := J.rot_comm
    edgeInv_comm := J.edgeInv_comm
    missing_iff := J.missing_iff
    tail_iff := J.tail_iff
    outer_iff := J.outer_iff }

/-- the walk-class representative's right path is the LR edge list in
source-to-sink order, represented by the tail dart of each edge; procedure -/
theorem kmswWalkClassBase_rightPath_darts {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (kmswWalkClassBase hn c).rightPath.darts =
      stageDarts (kmswStage (codeExtend c) (n - 1))
        (kmswStage (codeExtend c) (n - 1)).LR false
        (fun e he => stageRun_edge_bound (codeExtend c) (n - 1) e (Or.inr he)) := by
  classical
  let s := kmswStage (codeExtend c) (n - 1)
  let w := codeExtend c
  let m := n - 1
  let hp := kmswWalkClassBase_paths hn c
  let P := Classical.choose hp
  let Q := Classical.choose (Classical.choose_spec hp)
  have h := Classical.choose_spec (Classical.choose_spec hp)
  have hQ := h.2
  have hrun : Q.darts.reverse.map (edgeFlip s.nextEdge) =
      kmswStageLRDartRun w m := by
    exact hQ
  have hstage :
      (stageDarts s s.LR false
        (fun e he => stageRun_edge_bound w m e (Or.inr he))).reverse.map
          (edgeFlip s.nextEdge) = kmswStageLRDartRun w m := by
    simp only [stageDarts, ← List.map_reverse, List.reverse_attach,
      List.map_map, kmswStageLRDartRun]
    apply List.map_congr_left
    intro e he
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl
  change Q.darts = stageDarts s s.LR false
      (fun e he => stageRun_edge_bound w m e (Or.inr he))
  calc
    Q.darts = (Q.darts.reverse.map (edgeFlip s.nextEdge)).reverse.map
        (edgeFlip s.nextEdge) := by
      simp [List.map_reverse, List.map_map, Function.comp_def, edgeFlip]
    _ = (kmswStageLRDartRun w m).reverse.map (edgeFlip s.nextEdge) := by
      rw [hrun]
    _ = stageDarts s s.LR false
        (fun e he => stageRun_edge_bound w m e (Or.inr he)) := by
      calc
        (kmswStageLRDartRun w m).reverse.map (edgeFlip s.nextEdge) =
            ((stageDarts s s.LR false
              (fun e he => stageRun_edge_bound w m e (Or.inr he))).reverse.map
                (edgeFlip s.nextEdge)).reverse.map (edgeFlip s.nextEdge) := by
          rw [hstage]
        _ = stageDarts s s.LR false
            (fun e he => stageRun_edge_bound w m e (Or.inr he)) := by
          simp [List.map_reverse, List.map_map, Function.comp_def, edgeFlip]

/-- the canonical representative's right-path darts map back to the base -/
theorem kmswWalkClassRep_rightPath_darts_map {ℓ r n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ r n) :
    ((kmswWalkClassRep hn c).B.rightPath.darts.map
      (kmswWalkClassRep_mapIso hn c).toEquiv) =
        (kmswWalkClassBase hn c).rightPath.darts := by
  classical
  let B := kmswWalkClassBase hn c
  let D := StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge
  let e := Fintype.equivFin D
  change ((B.transport e).rightPath.darts.map e.symm) = B.rightPath.darts
  rw [← (B.transportIso e).rightDarts]
  simp [BipolarTriangulationWithBoundaryBase.transportIso]

end DirectedDistances.KMSW
