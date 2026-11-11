/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect8
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleAssembly3
public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed
public import DirectedDistances.KMSW.UIQBOTRealizationFaceDegree






public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4

/-- Helper toward Proposition 5.16: each signed side in the exterior-face
construction of a finite-stage domain has at most one geometric face. -/
theorem kmswStageExteriorDomain_signed_face_unique
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (a : P.GeometricEdge) (b : Bool)
    (F G : (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : if b then
      (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a
    else (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a)
    (hG : if b then
      (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf G a
    else (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf G a) :
    F = G := by
  cases b
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_right_face_unique_of_surjective
      P (kmswStageDrawing_vertex_surjective w n) a F G hF hG
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_left_face_unique_of_surjective
      P (kmswStageDrawing_vertex_surjective w n) a F G hF hG

/-- Helper toward Proposition 5.16: changing the stage's root mark to its
sampled missing edge leaves signed face uniqueness on the actual carrier. -/
theorem diskSampleDomain_signed_face_unique
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    (a : P.GeometricEdge) (b : Bool)
    (F H : (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : if b then
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a
    else (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a)
    (hH : if b then
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf H a
    else (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf H a) :
    F = H := by
  cases b
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_right_face_unique_of_surjective
      P (kmswStageDrawing_vertex_surjective _ n) a F H hF hH
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_left_face_unique_of_surjective
      P (kmswStageDrawing_vertex_surjective _ n) a F H hF hH

/-- Helper toward Proposition 5.16: retained-face assignment into the
sample domain follows on its actual carrier for every Data3 representation
of that domain. The StageGeom witness is still an explicit dependency. -/
theorem diskSampleDomain_geomBallIso_retained_face_assignment
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (G : StageGeom (diskSampleCanonicalStageCode ell n hell p) n P)
    {M N : D39RootedMap} {B : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G))
    (e : D39GeomBallIsoV2 r B.map B.root
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).map
      (diskSampleRootedStageDrawingDomainRootedMap ell n hell p P G).root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r) :
    (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).1 =
      y.faceOfDart (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 := by
  have hs := d39DrawingRepresentationData3_geomBallIso_faceEquiv_imageSide x y e d hret
  apply diskSampleDomain_signed_face_unique ell n hell p P G _ _ _ _ hs.1
  have ht := hs.2.2
  rw [hs.2.1] at ht
  exact ht

/-- Helper toward Proposition 5.16: signed uniqueness also holds on the
actual canonical UIQBOT directed-map carrier. Finite incidence supplies
vertex incidence; no transience or boundary-order premise is needed here. -/
theorem uiqbotPresentation_signed_face_unique
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (a : (uiqbotPresentationDrawing w hfin).GeometricEdge) (b : Bool)
    (F G : (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : if b then
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a
    else (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a)
    (hG : if b then
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf G a
    else (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf G a) :
    F = G := by
  cases b
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_right_face_unique_of_surjective
      (uiqbotPresentationDrawing w hfin) (kmswLimitDartVertex_surjective w hfin)
      a F G hF hG
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_left_face_unique_of_surjective
      (uiqbotPresentationDrawing w hfin) (kmswLimitDartVertex_surjective w hfin)
      a F G hF hG

end DirectedDistances.PaperProofs.Section5
