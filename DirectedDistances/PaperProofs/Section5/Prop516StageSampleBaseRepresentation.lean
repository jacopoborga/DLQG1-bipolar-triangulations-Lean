/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRepresentation2
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation4

/-! # Sample-rooted stage drawing base representation

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16. The sample root mark is the selected
missing frame dart, namely the reversal of `kmswDiskRootDart` at the cast
sample index. -/
theorem diskSampleRootedStageMap_rootMark_eq_frameDart
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell) :
    (diskSampleRootedStageMap ell n hell p).toD39RootedMap.rootMark.dart =
      edgeFlip _ (kmswDiskRootDart
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1)
        (Fin.cast (by omega : ell = (ell + 1) - 1) p.2)) := by
  rfl

/-- Helper toward Proposition 5.16. The selected sample frame dart is missing
in the sample map, and its edge is supported by the certified exterior face
of any compatible stage drawing. -/
theorem diskSampleRootedStageMap_frameDart_missing
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell) :
    let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
    let k : Fin ((ell + 1) - 1) :=
      Fin.cast (by omega : ell = (ell + 1) - 1) p.2
    (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.missing
      (edgeFlip _ (kmswDiskRootDart c k)) := by
  dsimp
  change (kmswStageDirectedMap
      (finiteCodeExtend (n := n + 1)
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val)
      n).missing
      (edgeFlip _ (kmswDiskRootDart
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1)
        (Fin.cast (by omega : ell = (ell + 1) - 1) p.2)))
  exact ((kmswStageDirectedMap
      (finiteCodeExtend (n := n + 1)
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val)
      n).missing_edgeInv _).mp (kmswDiskRootDart_missing _ _)

/-- Helper toward Proposition 5.16. Build the same geometric stage drawing
with the sample's missing frame edge as its ordered root mark. Its missing
edge condition follows from the certified exterior face; connectivity and
local finiteness are unchanged. -/
@[expose] def diskSampleRootedStageDrawingDomainRootedMap
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    D39DomainRootedMapV2 := by
  let w := diskSampleCanonicalStageCode ell n hell p
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
  let k : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) p.2
  let frameDart : StageDart (kmswStage w n).nextEdge :=
    edgeFlip _ (kmswDiskRootDart c k)
  let missing : P.GeometricEdge → Prop := fun e =>
    (kmswStageDirectedMap w n).missing e.out
  let forward : {e : P.GeometricEdge // ¬ missing e} → Bool :=
    fun e => !e.val.out.2
  let hmissingExternal :=
    kmswStageDrawing_missingEdges_external_of_exteriorFace P
      G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff
  let M := finitePLDrawingDirectedMap P missing forward hmissingExternal
  let root := kmswStageDrawingDartEdgeDirectionEquiv P frameDart
  have hconn : ∀ v v' : Fin (kmswStage w n).nextVertex,
      (d39GeomGraph M).Reachable v v' := by
    simpa [M, missing, forward] using
      kmswStageDrawing_geometricGraph_connected_of_external P hmissingExternal
  have hframeMissing : (kmswStageDirectedMap w n).missing frameDart := by
    dsimp [frameDart]
    exact ((kmswStageDirectedMap w n).missing_edgeInv _).mp
      (kmswDiskRootDart_missing c k)
  have hroot : M.toPlaneMapWithMissing.missing root.1 := by
    change (kmswStageDirectedMap w n).missing root.1.out
    dsimp [root, kmswStageDrawingDartEdgeDirectionEquiv]
    rcases P.geometricEdge_out_mk frameDart with hout | hout
    · rw [hout]
      exact hframeMissing
    · rw [hout]
      exact (kmswStageDirectedMap w n).missing_edgeInv frameDart |>.2 hframeMissing
  exact finitePLDrawingD39DomainRootedMapV2 P missing forward
    hmissingExternal root hconn (Or.inl hroot)

/-- Helper toward Proposition 5.16. The sample-rooted domain keeps the stage
missing tags on every dart, with the missing root dart matched to the domain's
ordered edge mark. -/
theorem diskSampleRootedStageDrawingDomain_root_mark_and_missing
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
    let M := (diskSampleRootedStageMap ell n hell p).toD39RootedMap
    kmswStageDrawingDartEdgeDirectionEquiv P M.rootMark.dart = B.root ∧
    ∀ d : M.core.D,
      B.map.toPlaneMapWithMissing.missing
        (kmswStageDrawingDartEdgeDirectionEquiv P d).1 ↔ M.core.missing d := by
  dsimp
  constructor
  · rfl
  · intro d
    let w := diskSampleCanonicalStageCode ell n hell p
    change (kmswStageDirectedMap w n).missing
        (Quotient.mk P.edgeSetoid d).out ↔
      (kmswStageDirectedMap w n).missing d
    rcases P.geometricEdge_out_mk d with hout | hout
    · rw [hout]
    · rw [hout]
      exact (kmswStageDirectedMap w n).missing_edgeInv d

/-- Helper toward Proposition 5.16. The sample-rooted stage map has a drawing
representation over the domain rooted at the sample's missing frame edge. -/
noncomputable def diskSampleRootedStageD39DrawingRepresentationData
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    D39DrawingRepresentationData
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G) := by
  let w := diskSampleCanonicalStageCode ell n hell p
  let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  let faceOfDart : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D →
      B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face :=
    fun d => P.toPlaneGraphDrawingFaceEquiv.symm
      (kmswStageDrawing_leftFace P d)
  have hfaceOrbit : ∀ d e :
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
      faceOfDart d = faceOfDart e ↔
        Equiv.Perm.SameCycle
          (((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot).symm *
            (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv)
          d e := by
    intro d e
    constructor
    · intro h
      apply kmswStageDrawing_sameCycle_of_leftFace_eq P d e
      have h' := congrArg P.toPlaneGraphDrawingFaceEquiv h
      simpa [faceOfDart] using h'
    · intro h
      have h' := kmswStageDrawing_leftFace_eq_of_sameCycle P d e h
      exact congrArg P.toPlaneGraphDrawingFaceEquiv.symm h'
  have hfaceSurj : Function.Surjective faceOfDart := by
    exact kmswStageDrawing_domainFace_surjective P G.exteriorFace
      G.exteriorFace_unbounded G.dartBorders_iff
  refine d39DrawingRepresentationData_of_fields
    (kmswStageD39RootedMap_vertexEquiv w n)
    P.pos_injective E
    (fun d => kmswStageDrawingDartEdgeDirectionEquiv_tail_endpoint P
      G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff d)
    (fun d => kmswStageDrawingDartEdgeDirectionEquiv_head_endpoint P
      G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff d)
    (fun d => kmswStageDrawingDartEdgeDirectionEquiv_edgeFlip P d)
    (fun d => kmswStageDrawingDartEdgeDirectionEquiv_missing P
      G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff d)
    (fun d hd => kmswStageDrawingDartEdgeDirectionEquiv_orientation P
      G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff d hd)
    (by
      change E ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.rootMark.dart) = B.root
      rfl)
    faceOfDart hfaceOrbit hfaceSurj
    (fun d => by
      change StageDart (kmswStage w n).nextEdge at d
      change if (E d).2 then
          P.toPlaneGraphDrawing.SideLeftOf
            (P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d))
            (E d).1
        else P.toPlaneGraphDrawing.SideRightOf
            (P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d))
            (E d).1
      let Q : PLDrawing (StageDart (kmswStage w n).nextEdge)
          (Fin (kmswStage w n).nextVertex) (edgeFlip _) (stageRot w n)
          (stageVertex w n) := P
      cases hbit : (E d).2 with
      | true =>
        have hd : d = (E d).1.out := by
          have hrec := kmswStageDrawingDartEdgeDirectionEquiv_reconstructs P d
          simpa [E, hbit] using hrec
        intro s
        have hborderD : P.dartBorders d (kmswStageDrawing_leftFace P d) :=
          (kmswStageDrawing_leftFace_eq_iff P d
            (kmswStageDrawing_leftFace P d)).mp rfl
        have hborder : P.dartBorders (E d).1.out
            (kmswStageDrawing_leftFace P d) := hd ▸ hborderD
        have hl := Q.dartBorders_toPath_leftAtOn
          (kmswStageDrawing_vertex_surjective w n) (E d).1.out
          (kmswStageDrawing_leftFace P d) hborder s
        have hface_eq : Q.toPlaneGraphDrawingFaceEquiv
            (P.toPlaneGraphDrawingFaceEquiv.symm
              (kmswStageDrawing_leftFace P d)) = kmswStageDrawing_leftFace P d := by
          change P.toPlaneGraphDrawingFaceEquiv
            (P.toPlaneGraphDrawingFaceEquiv.symm
              (kmswStageDrawing_leftFace P d)) = _
          exact Equiv.apply_symm_apply _ _
        exact (Q.toPlaneGraphDrawing_leftAtOn_iff (E d).1
          (P.toPlaneGraphDrawingFaceEquiv.symm
            (kmswStageDrawing_leftFace P d)) s).mpr (hface_eq ▸ hl)
      | false =>
        exact kmswStageDrawing_leftFace_reverse_sideRightOf P d hbit)

/-- Helper toward Proposition 5.16. The frame mark is missing in the sample,
whereas the KMSW active stage root mark is present; the former is the mark
used in the sample-rooted drawing domain above. -/
theorem diskSampleRootedStageMap_frame_mark_status
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell) :
    let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
    let k : Fin ((ell + 1) - 1) :=
      Fin.cast (by omega : ell = (ell + 1) - 1) p.2
    (diskSampleRootedStageMap ell n hell p).toD39RootedMap.rootMark =
      .missing (edgeFlip _ (kmswDiskRootDart c k)) (by
        change (kmswStageDirectedMap
          (finiteCodeExtend (n := n + 1) c.val) n).missing
          (edgeFlip _ (kmswDiskRootDart c k))
        exact ((kmswStageDirectedMap
          (finiteCodeExtend (n := n + 1) c.val) n).missing_edgeInv _).mp
          (kmswDiskRootDart_missing c k)) := by
  rfl

/-- Helper toward Proposition 5.16. The sample's local topology root mark is the
missing frame dart, while the stage local topology root mark is its present active root. -/
theorem diskSampleRootedStageMap_and_stage_rootMarks
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell) :
    let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
    let k : Fin ((ell + 1) - 1) :=
      Fin.cast (by omega : ell = (ell + 1) - 1) p.2
    let w := diskSampleCanonicalStageCode ell n hell p
    (kmswStageD39RootedMap w n).rootMark =
      .present (kmswRootedStage w n).root
        (kmswRootedStage w n).root_present
        (kmswRootedStage w n).root_tail ∧
    (diskSampleRootedStageMap ell n hell p).toD39RootedMap.rootMark =
      .missing (edgeFlip _ (kmswDiskRootDart c k))
        (by
          change (kmswStageDirectedMap w n).missing
            (edgeFlip _ (kmswDiskRootDart c k))
          exact ((kmswStageDirectedMap w n).missing_edgeInv _).mp
            (kmswDiskRootDart_missing c k)) := by
  dsimp
  constructor <;> rfl

/- The exact remaining field target to `D39DrawingRepresentationData3` is:

    ∀ (ell n : ℕ) (hell : 0 < ell)
      (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
        q.IsChanneled} × Fin ell)
      (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P),
      let M := (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
      let hBase := diskSampleRootedStageD39DrawingRepresentationData
        ell n hell p P G
      (∀ d : M.core.D,
        D39TopologicalCcwSuccessor
          {e | rootedLocallyFiniteVertexClass M.core.rot e =
            rootedLocallyFiniteVertexClass M.core.rot d}
          (d39DrawingDartArc B hBase) d (M.core.rot d)) ∧
      (∀ (d : M.core.D)
        (v : RootedLocallyFiniteVertex M.core.D M.core.rot),
        B.map.toPlaneMapWithMissing.pos (hBase.vertexEquiv v) ∈
          frontier (hBase.faceOfDart d).val ↔
        ∃ e : M.core.D,
          Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
            rootedLocallyFiniteVertexClass M.core.rot e = v)

The dart-arc identity needed for the stage drawing transfer remains, with the
same sample, drawing, and base binders and this additional dart binder:

    ∀ (ell n : ℕ) (hell : 0 < ell)
      (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
        q.IsChanneled} × Fin ell)
      (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
      (d : ((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.D),
      d39DrawingDartArc
        (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G)
        (diskSampleRootedStageD39DrawingRepresentationData ell n hell p P G)
        d = (P.arc d).toPath

The side/orientation, face-orbit, and frontier routes are documented in
`Prop516StageDrawingRotation.lean` and
`Prop516StageDrawingFrontierIncidence2.lean`; the arc-identity obstruction is
recorded in `Prop516StageSampleRepresentation2.lean`. -/

/-- Helper toward Proposition 5.16. The sample base representation maps its
ordered root dart to the drawing domain's ordered root mark. -/
@[simp] theorem diskSampleRootedStageD39DrawingRepresentationData_root_correspondence
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    kmswStageDrawingDartEdgeDirectionEquiv P
        ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.rootMark.dart) =
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).root := by
  rfl

end DirectedDistances.PaperProofs.Section5

end
