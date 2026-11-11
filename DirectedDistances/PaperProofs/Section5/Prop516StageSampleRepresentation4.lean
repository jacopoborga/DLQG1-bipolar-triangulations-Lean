/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRepresentation3
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleBaseRepresentation

/-! # Sample-rooted stage representation assembly

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. Assemble the sample-rooted stage's
order-three representation using its constructed base representation and the
two remaining fields. -/
def diskSampleRootedStageD39DrawingRepresentationData3_of_base_data_fields
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (hRotationField : ∀ d :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
    D39TopologicalCcwSuccessor
      {e | rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e =
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d}
      (d39DrawingDartArc
        (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G)
        (diskSampleRootedStageD39DrawingRepresentationData ell n hell p P G))
      d ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d))
    (hFrontierField : ∀ (d :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D)
      (v : RootedLocallyFiniteVertex
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot),
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).map.toPlaneMapWithMissing.pos
        ((diskSampleRootedStageD39DrawingRepresentationData ell n hell p P G).vertexEquiv v) ∈
        frontier
          ((diskSampleRootedStageD39DrawingRepresentationData ell n hell p P G).faceOfDart d).val ↔
        ∃ e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
          Equiv.Perm.SameCycle
            ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot.symm *
              (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv) d e ∧
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e = v) :
    D39DrawingRepresentationData3
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G) := by
  let hBase : D39DrawingRepresentationData
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G) :=
    diskSampleRootedStageD39DrawingRepresentationData ell n hell p P G
  exact diskSampleRootedStageD39DrawingRepresentationData3_of_sample_fields
    ell n hell p P G hBase hRotationField hFrontierField

/-- Helper toward Proposition 5.16. In the sample stage drawing, a named
vertex lies on a face frontier exactly when it is an endpoint of a dart
bordering that face. -/
theorem diskSampleRootedStageDrawing_pos_mem_frontier_iff_exists_dartBorders_endpoint
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (F : P.Face)
    (v : Fin (kmswStage (diskSampleCanonicalStageCode ell n hell p) n).nextVertex) :
    P.pos v ∈ frontier F.val ↔
      ∃ d : StageDart
          (kmswStage (diskSampleCanonicalStageCode ell n hell p) n).nextEdge,
        P.dartBorders d F ∧
          (stageVertex (diskSampleCanonicalStageCode ell n hell p) n d = v ∨
            stageVertex (diskSampleCanonicalStageCode ell n hell p) n
              (edgeFlip _ d) = v) := by
  exact P.mem_pos_frontier_iff_exists_dartBorders_endpoint
    (kmswStageDrawing_vertex_surjective (diskSampleCanonicalStageCode ell n hell p) n)
    F v

















































end DirectedDistances.PaperProofs.Section5

end
