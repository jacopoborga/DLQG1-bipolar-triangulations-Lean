/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleAssembly2
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRepresentation4
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation12

/-! # Sample stage assembly with transported rotation

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Proposition 5.16. The explicit sample representation draws
each dart along the selected PL representative, with path reversal exactly
when its direction bit is false. -/
theorem diskSampleRootedStageD39DrawingRepresentationDataExplicit_dartArc_formula
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
    let hBase := diskSampleRootedStageD39DrawingRepresentationDataExplicit
      ell n hell p P G
    ∀ d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
      ∀ t, d39DrawingDartArc B hBase d t =
        if (kmswStageDrawingDartEdgeDirectionEquiv P d).2 then
          (P.arc (kmswStageDrawingDartEdgeDirectionEquiv P d).1.out).toPath t
        else
          (P.arc (kmswStageDrawingDartEdgeDirectionEquiv P d).1.out).toPath.symm t := by
  let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
  let hBase := diskSampleRootedStageD39DrawingRepresentationDataExplicit
    ell n hell p P G
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
theorem diskSampleRootedStageD39DrawingRepresentationDataExplicit_dartArc_reparam
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
    let hBase := diskSampleRootedStageD39DrawingRepresentationDataExplicit
      ell n hell p P G
    ∀ d : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D,
      ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, d39DrawingDartArc B hBase d t = (P.arc d).toPath (φ t) := by
  let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
  let hBase := diskSampleRootedStageD39DrawingRepresentationDataExplicit
    ell n hell p P G
  change ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
    ∀ t, d39DrawingDartArc B hBase d t = (P.arc d).toPath (φ t)
  intro d
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  have hformula :=
    diskSampleRootedStageD39DrawingRepresentationDataExplicit_dartArc_formula
      ell n hell p P G d
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
theorem diskSampleRootedStageD39DrawingRepresentationDataExplicit_rotationField
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    let M := (diskSampleRootedStageMap ell n hell p).toD39RootedMap
    let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
    let hBase := diskSampleRootedStageD39DrawingRepresentationDataExplicit
      ell n hell p P G
    ∀ d : M.core.D,
      D39TopologicalCcwSuccessor
        {e | rootedLocallyFiniteVertexClass M.core.rot e =
          rootedLocallyFiniteVertexClass M.core.rot d}
        (d39DrawingDartArc B hBase) d (M.core.rot d) := by
  let B := diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G
  let hBase := diskSampleRootedStageD39DrawingRepresentationDataExplicit
    ell n hell p P G
  change ∀ d, D39TopologicalCcwSuccessor
    {e | rootedLocallyFiniteVertexClass
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot e =
      rootedLocallyFiniteVertexClass
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d}
    (d39DrawingDartArc B hBase) d
    ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot d)
  let w := diskSampleCanonicalStageCode ell n hell p
  let hparams := diskSampleRootedStageD39DrawingRepresentationDataExplicit_dartArc_reparam
    ell n hell p P G
  intro d
  let φ : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D → I ≃ₜ I :=
    fun e => Classical.choose (hparams e)
  have hparam0 (e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
      φ e 0 = 0 := (Classical.choose_spec (hparams e)).1
  have hparam1 (e : (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.D) :
      φ e 1 = 1 := (Classical.choose_spec (hparams e)).2.1
  have harcs : d39DrawingDartArc
        (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G)
        (diskSampleRootedStageD39DrawingRepresentationDataExplicit
          ell n hell p P G) =
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
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G)
      (diskSampleRootedStageD39DrawingRepresentationDataExplicit
        ell n hell p P G)) d (stageRot w n d)
  rw [harcs]
  have hset : {e | rootedLocallyFiniteVertexClass (stageRot w n) e =
      rootedLocallyFiniteVertexClass (stageRot w n) d} =
    {e | stageVertex w n e = stageVertex w n d} := by
    ext e
    exact hstar e
  rw [hset]
  exact htransfer

/-- Helper toward Proposition 5.16. The explicit sample base record, its
frontier field, and the transported rotation field assemble a field-free
order-three drawing representation. -/
noncomputable def diskSampleRootedStageD39DrawingRepresentationData3_explicit
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P) :
    D39DrawingRepresentationData3
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G) := by
  exact diskSampleRootedStageD39DrawingRepresentationData3_of_sample_fields
    ell n hell p P G
    (diskSampleRootedStageD39DrawingRepresentationDataExplicit ell n hell p P G)
    (diskSampleRootedStageD39DrawingRepresentationDataExplicit_rotationField
      ell n hell p P G)
    (diskSampleRootedStage_frontierField_explicit ell n hell p P G)

end DirectedDistances.PaperProofs.Section5

end
