/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleAssembly
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleFrontierField
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRotationField
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleBaseRepresentation

/-! # Sample stage assembly with exposed base data

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. The sample base representation, written
as a structure literal so its face and dart assignments remain reducible. -/
@[expose] noncomputable def diskSampleRootedStageD39DrawingRepresentationDataExplicit
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
  have hfaceSurj : Function.Surjective faceOfDart :=
    kmswStageDrawing_domainFace_surjective P G.exteriorFace
      G.exteriorFace_unbounded G.dartBorders_iff
  exact
    { vertexEquiv := kmswStageD39RootedMap_vertexEquiv w n
      positions_injective := P.pos_injective
      dartEquiv := E
      dart_tail_vertex := fun d =>
        kmswStageDrawingDartEdgeDirectionEquiv_tail_endpoint P
          G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff d
      dart_head_vertex := fun d =>
        kmswStageDrawingDartEdgeDirectionEquiv_head_endpoint P
          G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff d
      dart_edgeInv := fun d =>
        kmswStageDrawingDartEdgeDirectionEquiv_edgeFlip P d
      dart_missing := fun d =>
        kmswStageDrawingDartEdgeDirectionEquiv_missing P
          G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff d
      dart_orientation := fun d hd =>
        kmswStageDrawingDartEdgeDirectionEquiv_orientation P
          G.exteriorFace G.exteriorFace_unbounded G.dartBorders_iff d hd
      root_mark := by
        change E ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.rootMark.dart) = B.root
        rfl
      faceOfDart := faceOfDart
      faceOrbit_iff := hfaceOrbit
      face_surjective := hfaceSurj
      face_left_of_dart := fun d => by
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
          exact kmswStageDrawing_leftFace_reverse_sideRightOf P d hbit }

/-- Helper toward Proposition 5.16. The explicit base record assigns each dart
to its PL left face. -/
@[simp] theorem diskSampleRootedStageD39DrawingRepresentationDataExplicit_faceOfDart
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
    (diskSampleRootedStageD39DrawingRepresentationDataExplicit
      ell n hell p P G).faceOfDart d =
      P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d) := rfl

/-- Helper toward Proposition 5.16. The explicit base record uses the stage
vertex correspondence. -/
@[simp] theorem diskSampleRootedStageD39DrawingRepresentationDataExplicit_vertexEquiv
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (v : RootedLocallyFiniteVertex
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot) :
    (diskSampleRootedStageD39DrawingRepresentationDataExplicit
      ell n hell p P G).vertexEquiv v =
      kmswStageD39RootedMap_vertexEquiv
        (diskSampleCanonicalStageCode ell n hell p) n v := rfl

/-- Helper toward Proposition 5.16. The explicit base record uses the PL
dart-to-edge-direction correspondence. -/
@[simp] theorem diskSampleRootedStageD39DrawingRepresentationDataExplicit_dartEquiv
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
    (diskSampleRootedStageD39DrawingRepresentationDataExplicit
      ell n hell p P G).dartEquiv d =
      kmswStageDrawingDartEdgeDirectionEquiv P d := rfl

/-- Helper toward Proposition 5.16. The explicit sample record's face
assignment has the exact face-successor cycle correspondence. -/
theorem diskSampleRootedStageD39DrawingRepresentationDataExplicit_faceOrbit_iff
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (d e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
    (diskSampleRootedStageD39DrawingRepresentationDataExplicit
      ell n hell p P G).faceOfDart d =
        (diskSampleRootedStageD39DrawingRepresentationDataExplicit
          ell n hell p P G).faceOfDart e ↔
      Equiv.Perm.SameCycle
        (((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot).symm *
          (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv) d e :=
  (diskSampleRootedStageD39DrawingRepresentationDataExplicit
    ell n hell p P G).faceOrbit_iff d e






























































/-- Helper toward Proposition 5.16. Frontier incidence for the explicit
sample base record follows from the PL border characterization and its
face-cycle correspondence. -/
theorem diskSampleRootedStage_frontierField_explicit
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    let M := (diskSampleRootedStageMap ell n hell p).toD39RootedMap
    let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
    let hBase := diskSampleRootedStageD39DrawingRepresentationDataExplicit
      ell n hell p P G
    ∀ (d : M.core.D)
      (v : RootedLocallyFiniteVertex M.core.D M.core.rot),
      B.map.toPlaneMapWithMissing.pos (hBase.vertexEquiv v) ∈
          frontier (hBase.faceOfDart d).val ↔
        ∃ e : M.core.D,
          Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
            rootedLocallyFiniteVertexClass M.core.rot e = v := by
  dsimp only
  let w := diskSampleCanonicalStageCode ell n hell p
  intro d v
  change P.pos (kmswStageD39RootedMap_vertexEquiv w n v) ∈
      frontier (kmswStageDrawing_leftFace P d).val ↔
    ∃ e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
      Equiv.Perm.SameCycle
        ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot.symm *
          (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv) d e ∧
        rootedLocallyFiniteVertexClass
          (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e = v
  have hstage (e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
      stageVertex w n e = kmswStageD39RootedMap_vertexEquiv w n
        (rootedLocallyFiniteVertexClass
          (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e) := by
    change stageVertex w n e = kmswStageD39RootedMap_vertexEquiv w n
      (rootedLocallyFiniteVertexClass (stageRot w n) e)
    rfl
  rw [P.mem_pos_frontier_iff_exists_dartBorders_endpoint
    (kmswStageDrawing_vertex_surjective w n)
    (kmswStageDrawing_leftFace P d)
    (kmswStageD39RootedMap_vertexEquiv w n v)]
  constructor
  · rintro ⟨e, hborder, hend | hend⟩
    · have hcycle :=
        (diskSampleRootedStageDrawing_dartBorders_leftFace_iff_sameCycle
          ell n hell p P d e).mp hborder
      refine ⟨e, hcycle, ?_⟩
      apply (kmswStageD39RootedMap_vertexEquiv w n).injective
      calc
        kmswStageD39RootedMap_vertexEquiv w n
            (rootedLocallyFiniteVertexClass
              (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e) =
            stageVertex w n e := (hstage e).symm
        _ = kmswStageD39RootedMap_vertexEquiv w n v := hend
    · have hcycle :=
        (diskSampleRootedStageDrawing_dartBorders_leftFace_iff_sameCycle
          ell n hell p P d e).mp hborder
      let e' := (stageRot w n).symm (edgeFlip _ e)
      have hstep : Equiv.Perm.SameCycle
          ((stageRot w n).symm * edgeFlip _) e e' := by
        dsimp [e']
        exact ⟨1, by simp⟩
      have hcycle' : Equiv.Perm.SameCycle
          ((stageRot w n).symm * edgeFlip _) d e' := hcycle.trans hstep
      have hrot : Equiv.Perm.SameCycle (stageRot w n) e' (edgeFlip _ e) := by
        dsimp [e']
        exact ⟨1, by simp⟩
      have hvertex : stageVertex w n e' = stageVertex w n (edgeFlip _ e) := by
        apply Fin.ext
        exact (stageRot_sameCycle_iff_endpoint_eq w n e' (edgeFlip _ e)).1 hrot
      have hborder' :=
        (diskSampleRootedStageDrawing_dartBorders_leftFace_iff_sameCycle
          ell n hell p P d e').mpr hcycle'
      refine ⟨e', hcycle', ?_⟩
      apply (kmswStageD39RootedMap_vertexEquiv w n).injective
      calc
        kmswStageD39RootedMap_vertexEquiv w n
            (rootedLocallyFiniteVertexClass
              (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e') =
            stageVertex w n e' := (hstage e').symm
        _ = stageVertex w n (edgeFlip _ e) := hvertex
        _ = kmswStageD39RootedMap_vertexEquiv w n v := hend
  · rintro ⟨e, hcycle, hv⟩
    have hend : stageVertex w n e = kmswStageD39RootedMap_vertexEquiv w n v := by
      calc
        stageVertex w n e =
            kmswStageD39RootedMap_vertexEquiv w n
              (rootedLocallyFiniteVertexClass
                (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e) :=
            hstage e
        _ = kmswStageD39RootedMap_vertexEquiv w n v :=
            congrArg (kmswStageD39RootedMap_vertexEquiv w n) hv
    exact ⟨e,
      (diskSampleRootedStageDrawing_dartBorders_leftFace_iff_sameCycle
        ell n hell p P d e).mpr hcycle,
      Or.inl hend⟩

end DirectedDistances.PaperProofs.Section5

end
