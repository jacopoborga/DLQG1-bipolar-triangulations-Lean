/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect9
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation14
public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly4

/- Helper toward Proposition 5.16: construct the sample-rooted geometric domain
and its complete Data3 representation from the finite drawing's proved
exterior-face data. The construction retains the sampled missing root and
all face, dart, vertex and rotation fields. It needs no triangle-cell or
exterior-sector certificate and no literal reversed-path schedule equality.
coordinator; no whole-paper or Proposition 5.16 completion is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval

/-- Helper toward Proposition 5.16. Build the same geometric stage drawing
with the sample's missing frame edge as its ordered root mark. Its missing
edge condition follows from the certified exterior face; connectivity and
local finiteness are unchanged. -/
@[expose] def diskSampleExteriorDomain
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
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
      U hU hborder
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

/-- Helper toward Proposition 5.16: whenever the stronger StageGeom record
is available, the exterior-only domain is exactly the existing sample
domain, including its missing root and all individual edge identities. -/
theorem diskSampleExteriorDomain_eq_stageGeomDomain
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    diskSampleExteriorDomain ell n hell p P G.exteriorFace
        G.exteriorFace_unbounded G.dartBorders_iff =
      diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G := by
  rfl

/-- Helper toward Proposition 5.16. The sample base representation, written
as a structure literal so its face and dart assignments remain reducible. -/
@[expose] noncomputable def diskSampleExteriorBase
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
    D39DrawingRepresentationData
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskSampleExteriorDomain ell n hell p P U hU hborder) := by
  let w := diskSampleCanonicalStageCode ell n hell p
  let B := diskSampleExteriorDomain ell n hell p P U hU hborder
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
    kmswStageDrawing_domainFace_surjective P U
      hU hborder
  exact
    { vertexEquiv := kmswStageD39RootedMap_vertexEquiv w n
      positions_injective := P.pos_injective
      dartEquiv := E
      dart_tail_vertex := fun d =>
        kmswStageDrawingDartEdgeDirectionEquiv_tail_endpoint P
          U hU hborder d
      dart_head_vertex := fun d =>
        kmswStageDrawingDartEdgeDirectionEquiv_head_endpoint P
          U hU hborder d
      dart_edgeInv := fun d =>
        kmswStageDrawingDartEdgeDirectionEquiv_edgeFlip P d
      dart_missing := fun d =>
        kmswStageDrawingDartEdgeDirectionEquiv_missing P
          U hU hborder d
      dart_orientation := fun d hd =>
        kmswStageDrawingDartEdgeDirectionEquiv_orientation P
          U hU hborder d hd
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

/-- Helper toward Proposition 5.16. Frontier incidence for the explicit
sample base record follows from the PL border characterization and its
face-cycle correspondence. -/
theorem diskSampleExteriorBase_frontierField
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
    let M := (diskSampleRootedStageMap ell n hell p).toD39RootedMap
    let B := diskSampleExteriorDomain ell n hell p P U hU hborder
    let hBase := diskSampleExteriorBase
      ell n hell p P U hU hborder
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

/-- Helper toward Proposition 5.16. The explicit sample representation draws
each dart along the selected PL representative, with path reversal exactly
when its direction bit is false. -/
theorem diskSampleExteriorBase_dartArc_formula
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
    let B := diskSampleExteriorDomain ell n hell p P U hU hborder
    let hBase := diskSampleExteriorBase
      ell n hell p P U hU hborder
    ∀ d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
      ∀ t, d39DrawingDartArc B hBase d t =
        if (kmswStageDrawingDartEdgeDirectionEquiv P d).2 then
          (P.arc (kmswStageDrawingDartEdgeDirectionEquiv P d).1.out).toPath t
        else
          (P.arc (kmswStageDrawingDartEdgeDirectionEquiv P d).1.out).toPath.symm t := by
  let B := diskSampleExteriorDomain ell n hell p P U hU hborder
  let hBase := diskSampleExteriorBase
    ell n hell p P U hU hborder
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  have hE (d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
      hBase.dartEquiv d = E d := by
    rfl
  have hGraph : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing =
      P.toPlaneGraphDrawing := by
    rfl
  have hArc (e : P.GeometricEdge) (t : I) :
      P.toPlaneGraphDrawing.arc e t = (P.arc e.out).toPath t := by
    change ((P.arc e.out).toPath.cast
      (P.arc_start e.out).symm (P.arc_finish e.out).symm) t = _
    rfl
  have hArcSymm (e : P.GeometricEdge) (t : I) :
      (P.toPlaneGraphDrawing.arc e).symm t = (P.arc e.out).toPath.symm t := by
    change ((P.arc e.out).toPath.cast
      (P.arc_start e.out).symm (P.arc_finish e.out).symm).symm t = _
    rw [((Path.cast_symm (P.arc e.out).toPath
      (P.arc_start e.out).symm (P.arc_finish e.out).symm).symm)]
    rfl
  change ∀ d t, d39DrawingDartArc B hBase d t =
    if (E d).2 then (P.arc (E d).1.out).toPath t
    else (P.arc (E d).1.out).toPath.symm t
  intro d t
  rw [d39DrawingDartArc, hE d, hGraph]
  cases hbit : (E d).2
  · simpa only [hbit, Bool.false_eq_true, ↓reduceIte] using hArcSymm (E d).1 t
  · simpa only [hbit, ↓reduceIte] using hArc (E d).1 t

/-- Helper toward Proposition 5.16. The explicit sample represented arc is
an endpoint preserving reparameterization of the PL dart path, including the
reversal case where a reversed path differs from the reversed point list. -/
theorem diskSampleExteriorBase_dartArc_reparam
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
    let B := diskSampleExteriorDomain ell n hell p P U hU hborder
    let hBase := diskSampleExteriorBase
      ell n hell p P U hU hborder
    ∀ d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
      ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, d39DrawingDartArc B hBase d t = (P.arc d).toPath (φ t) := by
  let B := diskSampleExteriorDomain ell n hell p P U hU hborder
  let hBase := diskSampleExteriorBase
    ell n hell p P U hU hborder
  change ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
    ∀ t, d39DrawingDartArc B hBase d t = (P.arc d).toPath (φ t)
  intro d
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  have hformula :=
    diskSampleExteriorBase_dartArc_formula
      ell n hell p P U hU hborder d
  let Q : PLDrawing (StageDart (kmswStage (diskSampleCanonicalStageCode ell n hell p) n).nextEdge)
      (Fin (kmswStage (diskSampleCanonicalStageCode ell n hell p) n).nextVertex)
      (edgeFlip _) (stageRot (diskSampleCanonicalStageCode ell n hell p) n)
      (stageVertex (diskSampleCanonicalStageCode ell n hell p) n) := P
  let dStage : StageDart (kmswStage (diskSampleCanonicalStageCode ell n hell p) n).nextEdge := d
  change ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
    ∀ t, d39DrawingDartArc B hBase d t = (Q.arc dStage).toPath (φ t)
  have hEd : E dStage = E d := by
    rfl
  have hdraw (t : I) : d39DrawingDartArc B hBase d t =
      if (E d).2 then (Q.arc (E d).1.out).toPath t
      else (Q.arc (E d).1.out).toPath.symm t := by
    simpa only [B, hBase, E, Q] using hformula t
  cases hbit : (E d).2
  · have hdStage : dStage = edgeFlip _ (E d).1.out := by
      have hrec := kmswStageDrawingDartEdgeDirectionEquiv_reconstructs P dStage
      rw [hEd] at hrec
      simpa [hbit] using hrec
    have harc : Q.arc dStage = (Q.arc (E d).1.out).reverse := by
      calc
        Q.arc dStage = Q.arc (edgeFlip _ (E d).1.out) := congrArg Q.arc hdStage
        _ = (Q.arc (E d).1.out).reverse := Q.arc_flip _
    obtain ⟨φ, h0, h1, hφ⟩ := polyline_reverse_toPath_exists_reparam
      (Q.arc (E d).1.out)
      (Q.arc_length (E d).1.out) (Q.arc_simple (E d).1.out)
    refine ⟨φ, h0, h1, ?_⟩
    intro t
    have hdrawt := hdraw t
    calc
      d39DrawingDartArc B hBase d t =
          (Q.arc (E d).1.out).toPath.symm t := by
        simpa only [hbit, Bool.false_eq_true, ↓reduceIte] using hdrawt
      _ = (Q.arc (E d).1.out).reverse.toPath (φ t) := hφ t
      _ = (Q.arc dStage).toPath (φ t) := by rw [← harc]
  · have hdStage : dStage = (E d).1.out := by
      have hrec := kmswStageDrawingDartEdgeDirectionEquiv_reconstructs P dStage
      rw [hEd] at hrec
      simpa [hbit] using hrec
    refine ⟨Homeomorph.refl I, rfl, rfl, ?_⟩
    intro t
    have hdrawt := hdraw t
    calc
      d39DrawingDartArc B hBase d t = (Q.arc (E d).1.out).toPath t := by
        simpa only [hbit, ↓reduceIte] using hdrawt
      _ = (Q.arc dStage).toPath t := by rw [hdStage]

/-- Helper toward Proposition 5.16. The explicit sample representation has
the topological counterclockwise successor field, transported from the PL
stage drawing through its dart reparameterizations. -/
theorem diskSampleExteriorBase_rotationField
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
    let M := (diskSampleRootedStageMap ell n hell p).toD39RootedMap
    let B := diskSampleExteriorDomain ell n hell p P U hU hborder
    let hBase := diskSampleExteriorBase
      ell n hell p P U hU hborder
    ∀ d : M.core.D,
      D39TopologicalCcwSuccessor
        {e | rootedLocallyFiniteVertexClass M.core.rot e =
          rootedLocallyFiniteVertexClass M.core.rot d}
        (d39DrawingDartArc B hBase) d (M.core.rot d) := by
  let B := diskSampleExteriorDomain ell n hell p P U hU hborder
  let hBase := diskSampleExteriorBase
    ell n hell p P U hU hborder
  change ∀ d, D39TopologicalCcwSuccessor
    {e | rootedLocallyFiniteVertexClass
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e =
      rootedLocallyFiniteVertexClass
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d}
    (d39DrawingDartArc B hBase) d
    ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d)
  let w := diskSampleCanonicalStageCode ell n hell p
  let hparams := diskSampleExteriorBase_dartArc_reparam
    ell n hell p P U hU hborder
  intro d
  let φ : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D → I ≃ₜ I :=
    fun e => Classical.choose (hparams e)
  have hparam0 (e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
      φ e 0 = 0 := (Classical.choose_spec (hparams e)).1
  have hparam1 (e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
      φ e 1 = 1 := (Classical.choose_spec (hparams e)).2.1
  have harcs : d39DrawingDartArc
        (diskSampleExteriorDomain ell n hell p P U hU hborder)
        (diskSampleExteriorBase
          ell n hell p P U hU hborder) =
      fun e t => (P.arc e).toPath (φ e t) := by
    funext e t
    exact (Classical.choose_spec (hparams e)).2.2 t
  have hvertex (e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
      stageVertex w n e = kmswStageD39RootedMap_vertexEquiv w n
        (rootedLocallyFiniteVertexClass (stageRot w n) e) := by
    rfl
  have hstar (e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
      rootedLocallyFiniteVertexClass (stageRot w n) e =
          rootedLocallyFiniteVertexClass (stageRot w n) d ↔
        stageVertex w n e = stageVertex w n d := by
    constructor
    · intro he
      calc
        stageVertex w n e =
            kmswStageD39RootedMap_vertexEquiv w n
              (rootedLocallyFiniteVertexClass (stageRot w n) e) :=
          (hvertex e).symm
        _ = kmswStageD39RootedMap_vertexEquiv w n
              (rootedLocallyFiniteVertexClass (stageRot w n) d) :=
          congrArg (kmswStageD39RootedMap_vertexEquiv w n) he
        _ = stageVertex w n d := hvertex d
    · intro he
      apply (kmswStageD39RootedMap_vertexEquiv w n).injective
      calc
        kmswStageD39RootedMap_vertexEquiv w n
            (rootedLocallyFiniteVertexClass (stageRot w n) e) =
          stageVertex w n e := hvertex e
        _ = stageVertex w n d := he
        _ = kmswStageD39RootedMap_vertexEquiv w n
            (rootedLocallyFiniteVertexClass (stageRot w n) d) :=
          (hvertex d).symm
  have hPL := plDrawing_toPath_rotation_topological_ccwSuccessor P d
  have htransfer := d39TopologicalCcwSuccessor_comp_intervalHomeomorph
    {e | stageVertex w n e = stageVertex w n d}
    (fun e t => (P.arc e).toPath t) φ hparam0 hparam1 hPL
  change D39TopologicalCcwSuccessor
    {e | rootedLocallyFiniteVertexClass (stageRot w n) e =
      rootedLocallyFiniteVertexClass (stageRot w n) d}
    (d39DrawingDartArc
      (diskSampleExteriorDomain ell n hell p P U hU hborder)
      (diskSampleExteriorBase
        ell n hell p P U hU hborder)) d (stageRot w n d)
  rw [harcs]
  have hset : {e | rootedLocallyFiniteVertexClass (stageRot w n) e =
      rootedLocallyFiniteVertexClass (stageRot w n) d} =
    {e | stageVertex w n e = stageVertex w n d} := by
    ext e
    exact hstar e
  rw [hset]
  exact htransfer

/-- Helper toward Proposition 5.16: the sample-rooted Data3 record needs
only the exterior-face data already supplied by the all-stage induction. -/
@[expose] noncomputable def diskSampleExteriorData3
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
    D39DrawingRepresentationData3
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskSampleExteriorDomain ell n hell p P U hU hborder) where
  toD39DrawingRepresentationData := diskSampleExteriorBase ell n hell p P U hU hborder
  rotation_topological_successor :=
    diskSampleExteriorBase_rotationField ell n hell p P U hU hborder
  vertex_frontier_incidence :=
    diskSampleExteriorBase_frontierField ell n hell p P U hU hborder

section SampleComparison

variable (ell n : ℕ) (hell : 0 < ell)
  (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
    q.IsChanneled} × Fin ell)
  (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
  (U : P.Face) (hU : P.IsUnbounded U)
  (hborder : ∀ d, P.dartBorders d U ↔
    (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d)

/-- Helper toward Proposition 5.16: the constructed domain's ordered root
is the sampled missing frame edge, not the present active-stage root. -/
theorem diskSampleExteriorDomain_root_missing :
    (diskSampleExteriorDomain ell n hell p P U hU hborder).map.toPlaneMapWithMissing.missing
      (diskSampleExteriorDomain ell n hell p P U hU hborder).root.1 := by
  let x := diskSampleExteriorData3 ell n hell p P U hU hborder
  rw [← x.root_mark]
  apply (x.dart_missing _).mpr
  rw [diskSampleRootedStageMap_rootMark_eq_frameDart]
  exact diskSampleRootedStageMap_frameDart_missing ell n hell p

/-- Helper toward Proposition 5.16: the exterior-only sample construction
has a unique geometric face on each signed side of an edge. -/
theorem diskSampleExteriorDomain_signed_face_unique
    (a : P.GeometricEdge) (b : Bool)
    (F G : (diskSampleExteriorDomain ell n hell p P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : if b then
      (diskSampleExteriorDomain ell n hell p P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a
    else (diskSampleExteriorDomain ell n hell p P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a)
    (hG : if b then
      (diskSampleExteriorDomain ell n hell p P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf G a
    else (diskSampleExteriorDomain ell n hell p P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf G a) :
    F = G := by
  cases b
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_right_face_unique_of_surjective
      P (kmswStageDrawing_vertex_surjective _ n) a F G hF hG
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_left_face_unique_of_surjective
      P (kmswStageDrawing_vertex_surjective _ n) a F G hF hG

/-- Helper toward Proposition 5.16: retained-face assignment into the
constructed sample representation, without a StageGeom certificate. -/
theorem diskSampleExteriorData3_retained_face_assignment
    {M : D39RootedMap} {B : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (e : D39GeomBallIsoV2 r B.map B.root
      (diskSampleExteriorDomain ell n hell p P U hU hborder).map
      (diskSampleExteriorDomain ell n hell p P U hU hborder).root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r) :
    (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).1 =
      (diskSampleExteriorData3 ell n hell p P U hU hborder).faceOfDart
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x
          (diskSampleExteriorData3 ell n hell p P U hU hborder) e d).1 := by
  let y := diskSampleExteriorData3 ell n hell p P U hU hborder
  have hs := d39DrawingRepresentationData3_geomBallIso_faceEquiv_imageSide x y e d hret
  apply diskSampleExteriorDomain_signed_face_unique ell n hell p P U hU hborder
    _ _ _ _ hs.1
  have ht := hs.2.2
  rw [hs.2.1] at ht
  exact ht

/-- Helper toward Proposition 5.16: original faces are preserved and
reflected between the constructed sample and the canonical UIBHBOT domain.
Both directions use proved signed uniqueness on the actual carriers. -/
theorem diskSampleExteriorData3_uibhbot_original_face_preservation
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    {N : D39RootedMap} {r : ℕ}
    (y : D39DrawingRepresentationData3 N (uibhbotD39CanonicalRepresentation13Domain W D))
    (e : D39GeomBallIsoV2 r
      (diskSampleExteriorDomain ell n hell p P U hU hborder).map
      (diskSampleExteriorDomain ell n hell p P U hU hborder).root
      (uibhbotD39CanonicalRepresentation13Domain W D).map
      (uibhbotD39CanonicalRepresentation13Domain W D).root)
    (d : {d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D //
      d ∈ d39BallDarts (diskSampleRootedStageMap ell n hell p).toD39RootedMap r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv
        (diskSampleExteriorData3 ell n hell p P U hU hborder) y e d ∈
        (d39FacedBall N r e.radius_pos).original ↔
      d ∈ (d39FacedBall (diskSampleRootedStageMap ell n hell p).toD39RootedMap
        r e.radius_pos).original := by
  let x := diskSampleExteriorData3 ell n hell p P U hU hborder
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  constructor
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      y r e.radius_pos (E d)).mp hd
    have heq := diskSampleExteriorData3_retained_face_assignment
      ell n hell p P U hU hborder y e.symm (E d) hret
    have hback : d39DrawingRepresentationData3_geomBallIso_ballDartEquiv
        y x e.symm (E d) = d := by
      rw [geomBallIso_ballDartEquiv_symm_apply]
      exact E.symm_apply_apply d
    change (e.symm.faceEquiv ⟨y.faceOfDart (E d).1, hret⟩).1 =
      x.faceOfDart
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv y x e.symm (E d)).1 at heq
    rw [hback] at heq
    apply (d39DrawingRepresentationData3_original_iff_face_retained
      x r e.radius_pos d).mpr
    rw [← heq]
    exact (e.symm.faceEquiv ⟨y.faceOfDart (E d).1, hret⟩).property
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      x r e.radius_pos d).mp hd
    have heq := uibhbotCanonicalDomain_geomBallIso_retained_face_assignment
      W D x y e d hret
    apply (d39DrawingRepresentationData3_original_iff_face_retained
      y r e.radius_pos (E d)).mpr
    rw [← heq]
    exact (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).property

/-- Helper toward Proposition 5.16: a geometric ball isomorphism between
the constructed finite sample and canonical UIBHBOT gives the complete
combinatorial faced-ball isomorphism, with no extra representation premise. -/
theorem diskSampleExteriorDomain_uibhbot_facedBallIso
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W)
    (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r
      (diskSampleExteriorDomain ell n hell p P U hU hborder).map
      (diskSampleExteriorDomain ell n hell p P U hU hborder).root
      (uibhbotD39CanonicalRepresentation13Domain W D).map
      (uibhbotD39CanonicalRepresentation13Domain W D).root) :
    Nonempty (D39BallIso
      (d39FacedBall (diskRootedD39MapOfSample n ell hell p) r hr)
      (d39FacedBall
        (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr)) := by
  obtain ⟨y⟩ := uibhbotD39CanonicalRepresentation14_data3 W hW D
  apply d39BallIso_of_geomBallIsoV2_of_original_iff r hr
    (diskSampleExteriorData3 ell n hell p P U hU hborder) y e
  intro d
  exact diskSampleExteriorData3_uibhbot_original_face_preservation
    ell n hell p P U hU hborder W D y e d

end SampleComparison

/-- Helper toward Proposition 5.16: every finite sample has a correctly
rooted Data3 representation on a constructed PL carrier. The all-stage
exterior-face theorem discharges every geometric input to this existence
claim; the full StageGeom certificate is not used. -/
theorem diskSample_exists_exteriorData3
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell) :
    ∃ (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (U : P.Face) (hU : P.IsUnbounded U)
      (hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d),
      Nonempty (D39DrawingRepresentationData3 (diskRootedD39MapOfSample n ell hell p)
        (diskSampleExteriorDomain ell n hell p P U hU hborder)) := by
  obtain ⟨P, U, hU, _, hborder⟩ :=
    kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter
      (diskSampleCanonicalStageCode ell n hell p) n
  exact ⟨P, U, hU, hborder,
    ⟨diskSampleExteriorData3 ell n hell p P U hU hborder⟩⟩

/-- Helper toward Proposition 5.16: choose the finite sample's drawing and
representation together with its geometric-to-combinatorial comparison
against every canonical UIBHBOT witness. There is no geometric certificate
or uniqueness hypothesis on the finite sample in this existence statement. -/
theorem diskSample_exists_exteriorData3_and_uibhbot_facedBallIso
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell) :
    ∃ (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (U : P.Face) (hU : P.IsUnbounded U)
      (hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d),
      Nonempty (D39DrawingRepresentationData3 (diskRootedD39MapOfSample n ell hell p)
        (diskSampleExteriorDomain ell n hell p P U hU hborder)) ∧
      ∀ (W : ℤ → Fin 3) (_hW : W ∈ uibhbotRootedPlanarMapConullEvent)
        (D : UIBHBOTD39CanonicalDomainWitness W) (r : ℕ) (hr : 0 < r),
        Nonempty (D39GeomBallIsoV2 r
          (diskSampleExteriorDomain ell n hell p P U hU hborder).map
          (diskSampleExteriorDomain ell n hell p P U hU hborder).root
          (uibhbotD39CanonicalRepresentation13Domain W D).map
          (uibhbotD39CanonicalRepresentation13Domain W D).root) →
        Nonempty (D39BallIso
          (d39FacedBall (diskRootedD39MapOfSample n ell hell p) r hr)
          (d39FacedBall
            (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr)) := by
  obtain ⟨P, U, hU, hborder, hx⟩ := diskSample_exists_exteriorData3 ell n hell p
  refine ⟨P, U, hU, hborder, hx, ?_⟩
  intro W hW D r hr he
  obtain ⟨e⟩ := he
  exact diskSampleExteriorDomain_uibhbot_facedBallIso
    ell n hell p P U hU hborder W hW D r hr e














end DirectedDistances.PaperProofs.Section5
end
