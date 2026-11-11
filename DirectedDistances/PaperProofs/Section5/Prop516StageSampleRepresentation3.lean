/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleBaseRepresentation
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRepresentation
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingFrontierIncidence2
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRotation

/-! # Finite sample stage representation continuation

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. Assemble the sample-rooted stage's
order-three representation once its base representation and the two remaining
fields are supplied. -/
def diskSampleRootedStageD39DrawingRepresentationData3_of_sample_fields
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (hBase : D39DrawingRepresentationData
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G))
    (hRotationField : ∀ d :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
    D39TopologicalCcwSuccessor
      {e | rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e =
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d}
      (d39DrawingDartArc
        (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G) hBase)
      d ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d))
    (hFrontierField : ∀ (d :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D)
      (v : RootedLocallyFiniteVertex
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot),
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).map.toPlaneMapWithMissing.pos
        (hBase.vertexEquiv v) ∈
        frontier (hBase.faceOfDart d).val ↔
        ∃ e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
          Equiv.Perm.SameCycle
            ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot.symm *
              (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv) d e ∧
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e = v) :
    D39DrawingRepresentationData3
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G) := by
  exact
    { toD39DrawingRepresentationData := hBase
      rotation_topological_successor := hRotationField
      vertex_frontier_incidence := hFrontierField }













































































end DirectedDistances.PaperProofs.Section5

end
