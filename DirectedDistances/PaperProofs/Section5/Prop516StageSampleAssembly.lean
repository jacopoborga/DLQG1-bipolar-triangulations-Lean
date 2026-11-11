/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleFrontierField
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRotationField
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleBaseRepresentation

/-! # Sample stage assembly

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/- The current `Prop516StageSampleBaseRepresentation` contains the root-mark
correspondence lemma, but it does not contain the face-value or dart-arc value
the imported representation value is not definitionally equal to either the
PL left face or the PL stage arc. No premise or placeholder is introduced.

Target (1), the representation-face cycle equivalence, remains:

    ∀ (ell n : ℕ) (hell : 0 < ell)
      (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
        q.IsChanneled} × Fin ell)
      (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
      (d e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D),
      P.dartBorders e
          (P.toPlaneGraphDrawingFaceEquiv
            ((diskSampleRootedStageD39DrawingRepresentationData ell n hell p P G).faceOfDart d)) ↔
        Equiv.Perm.SameCycle
          ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot.symm *
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv) d e

Three routes were checked. (1) `rfl` does not expose the imported face
assignment. (2) No face-value theorem is present in the current base file to
rewrite with. (3) `faceOrbit_iff` identifies equality of represented faces
with `SameCycle`, but does not identify the represented face with the PL left
face needed by the dart-border theorem at FrontierField:29.

Target (2), the exact sample `hFrontierField`, remains:

    ∀ (ell n : ℕ) (hell : 0 < ell)
      (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
        q.IsChanneled} × Fin ell)
      (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n),
      let M := (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
      let hBase := diskSampleRootedStageD39DrawingRepresentationData
        ell n hell p P G
      ∀ (d : M.core.D)
        (v : RootedLocallyFiniteVertex M.core.D M.core.rot),
        B.map.toPlaneMapWithMissing.pos (hBase.vertexEquiv v) ∈
            frontier (hBase.faceOfDart d).val ↔
          ∃ e : M.core.D,
            Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
              rootedLocallyFiniteVertexClass M.core.rot e = v

Three routes were checked. (1) The PL frontier-union and endpoint theorem
reduces membership to a border and endpoint, but needs the missing represented
face/PL-face transport. (2) `faceOrbit_iff` does not identify geometric border
witnesses. (3) The `face_left_of_dart` side condition has no available converse
to `dartBorders`.

Target (3a), the sample dart-arc identity, remains:

    ∀ (ell n : ℕ) (hell : 0 < ell)
      (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
        q.IsChanneled} × Fin ell)
      (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
      (d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D),
      d39DrawingDartArc
        (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G)
        (diskSampleRootedStageD39DrawingRepresentationData ell n hell p P G)
        d = (P.arc d).toPath

Three routes were checked. (1) `rfl` fails on the imported representation
value. (2) Unfolding the sample domain and representation does not expose the
base representation body, and no dart-arc value theorem is in the current
base file. (3) The endpoint and orientation fields do not identify individual
edges in the multigraph, so comparing the quotient edge map does not establish
the represented dart-arc value.

Target (3b), the exact sample `hRotationField`, remains:

    ∀ (ell n : ℕ) (hell : 0 < ell)
      (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
        q.IsChanneled} × Fin ell)
      (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
      (d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D),
      D39TopologicalCcwSuccessor
        {e | rootedLocallyFiniteVertexClass
          (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e =
          rootedLocallyFiniteVertexClass
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d}
        (d39DrawingDartArc
          (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G)
          (diskSampleRootedStageD39DrawingRepresentationData ell n hell p P G))
        d ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d)

Three routes were checked. (1) `plDrawing_toPath_rotation_topological_ccwSuccessor`
applies to `P.arc`, but converting its function to the represented arc needs
the open dart-arc identity. (2) The KMSW stage successor theorem has the same
PL-arc limitation for this sample representation. (3) The finite drawing's
initial-direction order does not itself provide the required ambient
orientation-preserving straightening for the represented paths.

Target (4), the sample representation assembled with no field premise,
remains:

    ∀ (ell n : ℕ) (hell : 0 < ell)
      (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
        q.IsChanneled} × Fin ell)
      (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P),
      D39DrawingRepresentationData3
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap
        (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G)

Three routes were checked. (1) Representation4's assembler requires both
exact fields. (2) Representation3 constructs the same output record from the
same two fields. (3) The base representation supplies neither field, and
there is no field-free constructor that can fill those required components.
No frontier, rotation, arc, or target-equivalent premise was added. -/

end DirectedDistances.PaperProofs.Section5

end
