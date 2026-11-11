/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516RootExteriorEncoding
public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect10

/-! Helpers toward Proposition 5.16: the sampled missing root is an outer dart
of the finite stage drawing, and that drawing can be reindexed onto the
sample's rooted-map vertex classes for the exterior-marked ball construction.
No Proposition 5.16 completion is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: the reversed sample root dart borders
the certified unbounded face of the same Direct10 stage drawing. -/
theorem diskSampleExteriorDomain_reversedRoot_dartBorders
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (_hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
    P.dartBorders
      (kmswDiskRootDart
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1)
        (Fin.cast (by omega : ell = (ell + 1) - 1) p.2)) U := by
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
  let k : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) p.2
  have houter :
      (kmswStageDirectedMap
        (diskSampleCanonicalStageCode ell n hell p) n).IsOuter
        (kmswDiskRootDart c k) := by
    change (kmswStageDirectedMap
      (finiteCodeExtend (n := n + 1) c.val) n).IsOuter
      (kmswDiskRootDart c k)
    exact kmswDiskRootDart_isOuter (by omega : 2 ≤ ell + 1) c k
  apply (hborder (kmswDiskRootDart c k)).2
  exact houter

/-- Helper toward Proposition 5.16: reindex the Direct10 sample stage
drawing onto the rotation-class vertices of its sample local topology rooted map. Dart
identities, edge reversal, rotation, positions, and polylines are preserved. -/
@[expose] noncomputable def diskSampleRootedStagePLDrawing
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n) :
    PLDrawing (diskRootedD39MapOfSample n ell hell p).core.D
      (RootedLocallyFiniteVertex
        (diskRootedD39MapOfSample n ell hell p).core.D
        (diskRootedD39MapOfSample n ell hell p).core.rot)
      (diskRootedD39MapOfSample n ell hell p).core.edgeInv
      (diskRootedD39MapOfSample n ell hell p).core.rot
      (d39VertexClass (diskRootedD39MapOfSample n ell hell p)) := by
  let w := diskSampleCanonicalStageCode ell n hell p
  let E := diskSampleRootedStageMap_vertexEquiv ell n hell p
  have hv : ∀ d, E.symm (stageVertex w n d) =
      d39VertexClass (diskRootedD39MapOfSample n ell hell p) d := by
    intro d
    change E.symm (stageVertex
      (finiteCodeExtend (n := n + 1)
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val) n d) =
      rootedLocallyFiniteVertexClass
        (diskSampleRootedStageMap ell n hell p).rot d
    rw [← diskSampleRootedStageMap_vertexEquiv_dart ell n hell p d]
    exact E.symm_apply_apply _
  exact plDrawingRelabel (Equiv.refl _) E.symm
    (by intro d; rfl) (by intro d; rfl) hv P

/-- Helper toward Proposition 5.16: the vertex-reindexed sample drawing has
the same plane image as the stage drawing. -/
theorem diskSampleRootedStagePLDrawing_image
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n) :
    (diskSampleRootedStagePLDrawing ell n hell p P).image = P.image := by
  let w := diskSampleCanonicalStageCode ell n hell p
  let E := diskSampleRootedStageMap_vertexEquiv ell n hell p
  change (P.reindexVertices E.symm).image = P.image
  exact P.reindexVertices_image E.symm

/-- Helper toward Proposition 5.16: for every positive radius, the
exterior-marked finite sample class is the reversed-root lift of its
unmarked faced-ball class. -/
theorem diskSampleExteriorMarkedBallClass_eq_rootLift
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d)
    (r : ℕ) (hr : 0 < r) :
    Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal
          (diskRootedD39MapOfSample n ell hell p)
          (diskSampleRootedStagePLDrawing ell n hell p P) r hr) =
      Prop516RootExteriorEncoding.rootLift
        (d39BallClass (diskRootedD39MapOfSample n ell hell p) r hr) := by
  let M := diskRootedD39MapOfSample n ell hell p
  let Q := diskSampleRootedStagePLDrawing ell n hell p P
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
  let k : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) p.2
  have hroot : M.core.edgeInv M.rootMark.dart = kmswDiskRootDart c k := by
    change (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.rootMark.dart = _
    rw [diskSampleRootedStageMap_rootMark_eq_frameDart]
    rfl
  have himage : Q.image = P.image :=
    diskSampleRootedStagePLDrawing_image ell n hell p P
  let U' : Q.Face := ⟨U.val, by
    obtain ⟨z, hz, hface⟩ := U.property
    exact ⟨z, by rw [himage]; exact hz, by rw [himage]; exact hface⟩⟩
  have hU' : Q.IsUnbounded U' := hU
  have hborder' : Q.dartBorders (M.core.edgeInv M.rootMark.dart) U' := by
    rw [hroot]
    change P.dartBorders (kmswDiskRootDart c k) U
    exact diskSampleExteriorDomain_reversedRoot_dartBorders
      ell n hell p P U hU hborder
  exact Prop516RootExteriorEncoding.markedBallClass_eq_rootLift
    M Q r hr U' hU' hborder'

end DirectedDistances.PaperProofs.Section5

end
