/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRootedIso
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRotation
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingFrontierIncidence

/-! # Finite sample stage representation

This file makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. The canonical finite KMSW code used by
the sample-rooted stage map and its stage drawing. -/
@[expose] noncomputable def diskSampleCanonicalStageCode (ell n : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) : ℕ → Fin 3 :=
  finiteCodeExtend (n := n + 1)
    ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val

/-- Helper toward Proposition 5.16. The sample-rooted stage map, viewed as a
local topology rooted map, has drawing representation data of order three once its exact
base, topological-order, and frontier-incidence fields are supplied. -/
noncomputable def diskSampleRootedStageD39DrawingRepresentationData3_of_fields
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (hBase : D39DrawingRepresentationData
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (kmswStageDrawingDomainRootedMap P G))
    (hRotationField : ∀ d :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
      D39TopologicalCcwSuccessor
        {e | rootedLocallyFiniteVertexClass
          (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e =
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d}
        (d39DrawingDartArc (kmswStageDrawingDomainRootedMap P G) hBase)
        d
        ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d))
    (hFrontierField : ∀ (d :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D)
      (v : RootedLocallyFiniteVertex
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot),
      (kmswStageDrawingDomainRootedMap P G).map.toPlaneMapWithMissing.pos
          (hBase.vertexEquiv v) ∈
        frontier (hBase.faceOfDart d).val ↔
      ∃ e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
        Equiv.Perm.SameCycle
          ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot.symm *
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv)
          d e ∧
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e = v) :
    D39DrawingRepresentationData3
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (kmswStageDrawingDomainRootedMap P G) := by
  exact
    { toD39DrawingRepresentationData := hBase
      rotation_topological_successor := hRotationField
      vertex_frontier_incidence := hFrontierField }

/-- Helper toward Proposition 5.16. Transport the sample-rooted stage
representation to the finite sample's local topology rooted map using the rooted-map
isomorphism; that isomorphism is constructed by rewriting the rooted-map
equality proved for the sample. -/
noncomputable def diskSampleRootedD39DrawingRepresentationData3_of_fields
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (hBase : D39DrawingRepresentationData
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (kmswStageDrawingDomainRootedMap P G))
    (hRotationField : ∀ d :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
      D39TopologicalCcwSuccessor
        {e | rootedLocallyFiniteVertexClass
          (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e =
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d}
        (d39DrawingDartArc (kmswStageDrawingDomainRootedMap P G) hBase)
        d
        ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d))
    (hFrontierField : ∀ (d :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D)
      (v : RootedLocallyFiniteVertex
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot),
      (kmswStageDrawingDomainRootedMap P G).map.toPlaneMapWithMissing.pos
          (hBase.vertexEquiv v) ∈
        frontier (hBase.faceOfDart d).val ↔
      ∃ e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
        Equiv.Perm.SameCycle
          ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot.symm *
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv)
          d e ∧
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e = v) :
    D39DrawingRepresentationData3
      (diskRootedD39MapOfSample n ell hell p)
      (kmswStageDrawingDomainRootedMap P G) := by
  let hStage := diskSampleRootedStageD39DrawingRepresentationData3_of_fields
    ell n hell p P G hBase hRotationField hFrontierField
  exact D39DrawingRepresentationData3.transportCombinatorialData
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample ell n hell p)
    hStage






























end DirectedDistances.PaperProofs.Section5

end
