/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MapCutVertices
public import DirectedDistances.KMSW.InfiniteTriangulation
public import DirectedDistances.KMSW.UIQBOTOrientation

/-! Supporting lemmas for paper labels `def-cut-vertex`, `def-uiqbot` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.PaperProofs.Section4

open Filter Quiver MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW







theorem uiqbot_carrier :
    -- the root edge is edge `0`, from vertex `0` to vertex `1` (deterministic, all `w`)
    (∀ w : ℕ → Fin 3, edgeWest w 0 = 0 ∧ edgeEast w 0 = 1) ∧
    -- every finite stage is planar and acyclic (deterministic, all `w`)
    (∀ w : ℕ → Fin 3, ∀ n : ℕ,
      (kmswMap w n).IsPlanar ∧ (kmswStageDirectedMap w n).IsAcyclic) ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        -- the external face: left chain forward, right chain backward, joined at the root
        (∀ i, kmswInfFaceSucc w hfin (kmswLeftBoundaryEdge w i, false) =
            (kmswLeftBoundaryEdge w (i + 1), false)) ∧
        (∀ i, kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w (i + 1), true) =
            (kmswRightBoundaryEdge w i, true)) ∧
        kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w 0, true) =
            (kmswLeftBoundaryEdge w 0, false) ∧
        -- the boundary chains are exactly the edges eventually always on the upper-left /
        -- lower-right boundary lists (the reading used by `def-cut-vertex`)
        (∀ e : ℕ, IsLeftBoundaryEdge w e ↔ ∃ i, e = kmswLeftBoundaryEdge w i) ∧
        (∀ e : ℕ, IsRightBoundaryEdge w e ↔ ∃ i, e = kmswRightBoundaryEdge w i) ∧
        -- every other face is a triangle
        (∀ d : ℕ × Bool,
          (∀ i, d ≠ (kmswLeftBoundaryEdge w i, false)) →
          (∀ i, d ≠ (kmswRightBoundaryEdge w i, true)) →
          ∃! j : TriangleCreationTime w,
            d ∈ stageTriangleDartList w j ∧
              FaceSucc3Cycle (kmswInfFaceSucc w hfin)
                (stageTriangleDartTriple w j).1
                (stageTriangleDartTriple w j).2.1
                (stageTriangleDartTriple w j).2.2) ∧
        -- no missing edges in the limit
        (∀ e : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true) ∧
        -- connected from the source, acyclic, unique source `0`, no sink
        (∀ v : ℕ, (∃ n, v < (kmswStage w n).nextVertex) →
          Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩) ∧
        acyclic (PresentVertex w) ∧
        (∀ v : ℕ, (∃ n, v < (kmswStage w n).nextVertex) →
          ((¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔ v = 0)) ∧
        (∀ v : ℕ, (∃ n, v < (kmswStage w n).nextVertex) →
          ∃ e, EdgePresent w e ∧ edgeWest w e = v) := by
  refine ⟨fun w => ⟨rfl, rfl⟩,
    fun w n => ⟨kmswMap_isPlanar w n, kmswStageDirectedMap_isAcyclic w n⟩, ?_⟩
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices,
    pitmanCodes_ae_infinite_face_structure.1, pitmanCodes_ae_eventually_present,
    pitmanCodes_ae_source_and_no_sink] with ω hcut hface hpres horient
  obtain ⟨-, htrans, hR, hL0, -⟩ := hcut
  obtain ⟨hfin, htri⟩ := hface
  obtain ⟨hacyc, hsrc, hsink⟩ := horient
  have hcycle := fun m => stageOuterWord_faceSucc (pitmanCode (fun i => ω (i + 1))) m
  exact ⟨hfin, kmswInfFaceSucc_left _ hfin hcycle htrans,
    kmswInfFaceSucc_right _ hfin hcycle hL0 hR,
    kmswInfFaceSucc_junction _ hfin hcycle hL0 htrans hR,
    isLeftBoundaryEdge_iff _ htrans, isRightBoundaryEdge_iff _ hR, htri, hpres,
    fun v hv => allocated_vertex_reachable_from_zero _ hL0 v hv, hacyc, hsrc, hsink⟩

end DirectedDistances.PaperProofs.Section4
