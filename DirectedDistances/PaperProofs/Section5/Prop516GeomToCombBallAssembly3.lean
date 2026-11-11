/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly2

/-! # Face-side transport for the geometric-to-combinatorial ball map

Helpers toward Proposition 5.16. This file transports the represented dart's
left-side datum across the geometric ball isomorphism and records the remaining
face assignment and faced-ball isomorphism obligations. No paper-completion
claim is made. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

private theorem d39GeomBallIsoV2_strictMono_endpoints_local (φ : I ≃ₜ I)
    (hφ : StrictMono φ) : φ 0 = 0 ∧ φ 1 = 1 := by
  have h0 : φ 0 ≤ 0 := by
    have h := hφ.monotone (show (0 : I) ≤ φ.symm 0 from (φ.symm 0).property.1)
    simpa using h
  have h1 : 1 ≤ φ 1 := by
    have hle : φ.symm 1 ≤ (1 : I) := by
      change (φ.symm 1).val ≤ (1 : ℝ)
      exact (φ.symm 1).property.2
    have h := hφ.monotone hle
    simpa using h
  exact ⟨le_antisymm h0 (show (0 : I) ≤ φ 0 from (φ 0).property.1),
    le_antisymm (φ 1).property.2 h1⟩

private theorem d39GeomBallIsoV2_strictAnti_endpoints_local (φ : I ≃ₜ I)
    (hφ : StrictAnti φ) : φ 0 = 1 ∧ φ 1 = 0 := by
  have h0 : 1 ≤ φ 0 := by
    have h := hφ.antitone (show (0 : I) ≤ φ.symm 1 from (φ.symm 1).property.1)
    simpa using h
  have h1 : φ 1 ≤ 0 := by
    have hle : φ.symm 0 ≤ (1 : I) := by
      change (φ.symm 0).val ≤ (1 : ℝ)
      exact (φ.symm 0).property.2
    have h := hφ.antitone hle
    simpa using h
  exact ⟨le_antisymm (show φ 0 ≤ (1 : I) from (φ 0).property.2) h0,
    le_antisymm h1 (show (0 : I) ≤ φ 1 from (φ 1).property.1)⟩

private theorem d39GeomBallIsoV2_sideRightOf_map
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (F : {F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces B.map B.root r})
    (a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r}) :
    B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F.1 a.1 ↔
      if e.edgeFlip a then
        C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (e.faceEquiv F).1 (e.edgeEquiv a).1
      else
        C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (e.faceEquiv F).1 (e.edgeEquiv a).1 := by
  cases hflip : e.edgeFlip a
  · have hmono := e.edgeParam_mono a hflip
    obtain ⟨h0, h1⟩ := d39GeomBallIsoV2_strictMono_endpoints_local
      (e.edgeParam a) hmono
    have hpath : ∀ t : I,
        ((B.map.toPlaneMapWithMissing.arc a.1).map e.h.continuous) t =
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).reparam
            (e.edgeParam a) (e.edgeParam a).continuous h0 h1 t := by
      intro t
      exact e.arc_map a t
    change B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F.1 a.1 ↔ _
    change (∀ s, RightAtOn F.1.val
      (B.map.toPlaneMapWithMissing.arc a.1) s) ↔ _
    change (∀ s, RightAtOn F.1.val
      (B.map.toPlaneMapWithMissing.arc a.1) s) ↔
      (∀ s, RightAtOn ((e.faceEquiv F).1).val
        (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s)
    calc
      (∀ s, RightAtOn F.1.val (B.map.toPlaneMapWithMissing.arc a.1) s) ↔
          (∀ s, RightAtOn (e.h '' F.1.val)
            ((B.map.toPlaneMapWithMissing.arc a.1).map e.h.continuous) s) := by
        apply forall_congr'
        intro s
        exact rightAtOn_map_iff _ _ s e.h e.orientationPreserving
      _ ↔ (∀ s, RightAtOn (e.h '' F.1.val)
          ((C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).reparam
            (e.edgeParam a) (e.edgeParam a).continuous h0 h1) s) := by
        apply forall_congr'
        intro s
        exact rightAtOn_congr_fun _ _ _ s hpath
      _ ↔ (∀ s, RightAtOn (e.h '' F.1.val)
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s) :=
        forall_rightAtOn_reparam_iff _ _ (e.edgeParam a) h0 h1
      _ = (∀ s, RightAtOn ((e.faceEquiv F).1).val
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s) := by
        rw [← e.face_image_map F]
  · have hanti := e.edgeParam_anti a hflip
    obtain ⟨h0, h1⟩ := d39GeomBallIsoV2_strictAnti_endpoints_local
      (e.edgeParam a) hanti
    let ψ := (e.edgeParam a).trans unitInterval.symmHomeomorph
    have hψ0 : ψ 0 = 0 := by
      change σ (e.edgeParam a 0) = 0
      rw [h0, unitInterval.symm_one]
    have hψ1 : ψ 1 = 1 := by
      change σ (e.edgeParam a 1) = 1
      rw [h1, unitInterval.symm_zero]
    have hpath : ∀ t : I,
        ((B.map.toPlaneMapWithMissing.arc a.1).map e.h.continuous) t =
          ((C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).symm.reparam
            ψ ψ.continuous hψ0 hψ1) t := by
      intro t
      change e.h (B.map.toPlaneMapWithMissing.arc a.1 t) =
        C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1
          (σ (σ (e.edgeParam a t)))
      rw [unitInterval.symm_symm]
      exact e.arc_map a t
    change B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F.1 a.1 ↔ _
    change (∀ s, RightAtOn F.1.val
      (B.map.toPlaneMapWithMissing.arc a.1) s) ↔ _
    change (∀ s, RightAtOn F.1.val
      (B.map.toPlaneMapWithMissing.arc a.1) s) ↔
      (∀ s, LeftAtOn ((e.faceEquiv F).1).val
        (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s)
    calc
      (∀ s, RightAtOn F.1.val (B.map.toPlaneMapWithMissing.arc a.1) s) ↔
          (∀ s, RightAtOn (e.h '' F.1.val)
            ((B.map.toPlaneMapWithMissing.arc a.1).map e.h.continuous) s) := by
        apply forall_congr'
        intro s
        exact rightAtOn_map_iff _ _ s e.h e.orientationPreserving
      _ ↔ (∀ s, RightAtOn (e.h '' F.1.val)
          ((C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).symm.reparam
            ψ ψ.continuous hψ0 hψ1) s) := by
        apply forall_congr'
        intro s
        exact rightAtOn_congr_fun _ _ _ s hpath
      _ ↔ (∀ s, RightAtOn (e.h '' F.1.val)
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).symm s) :=
        forall_rightAtOn_reparam_iff _ _ ψ hψ0 hψ1
      _ ↔ (∀ s, LeftAtOn (e.h '' F.1.val)
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s) :=
        forall_rightAtOn_symm_iff _ _
      _ = (∀ s, LeftAtOn ((e.faceEquiv F).1).val
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s) := by
        rw [← e.face_image_map F]

/-- Helper toward Proposition 5.16: an original dart in the faced ball has
its represented geometric face among the retained faces. -/
theorem d39DrawingRepresentationData3_original_dart_face_retained
    {M : D39RootedMap} {B : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original) :
    x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r := by
  change d39BallContainsOriginalFace M r d.1 at hd
  apply (d39DrawingRepresentationData3_retainedFace_iff_ballOrbitVertices
    x r d.1).2
  exact (d39BallContainsOriginalFace_iff M r d.1).1 hd

/-- Helper toward Proposition 5.16: the retained geometric image face has
the same left-side incidence as the represented image dart. The equality of
these faces still requires a uniqueness theorem for winding-side incidence
in the general plane-graph drawing. -/
theorem d39DrawingRepresentationData3_geomBallIso_faceEquiv_imageSide
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r) :
    let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
      ⟨(x.dartEquiv d.1).1,
        (d39DrawingRepresentationData3_ballDarts_iff x r d.1).mp d.2⟩
    (if Bool.xor (x.dartEquiv d.1).2 (e.edgeFlip a) then
      C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
        (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).1 (e.edgeEquiv a).1
    else
      C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
        (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).1 (e.edgeEquiv a).1) ∧
    (let q := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d
     (y.dartEquiv q.1 =
        ((e.edgeEquiv a).1,
          Bool.xor (x.dartEquiv d.1).2 (e.edgeFlip a))) ∧
     (if (y.dartEquiv q.1).2 then
       C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
         (y.faceOfDart q.1) (y.dartEquiv q.1).1
     else
       C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
         (y.faceOfDart q.1) (y.dartEquiv q.1).1)) := by
  dsimp only
  let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
    ⟨(x.dartEquiv d.1).1,
      (d39DrawingRepresentationData3_ballDarts_iff x r d.1).mp d.2⟩
  let F : {F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces B.map B.root r} :=
    ⟨x.faceOfDart d.1, hret⟩
  have hsource := x.face_left_of_dart d.1
  have hpair :
      y.dartEquiv
          (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 =
        ((e.edgeEquiv a).1,
          Bool.xor (x.dartEquiv d.1).2 (e.edgeFlip a)) := by
    simp [d39DrawingRepresentationData3_geomBallIso_ballDartEquiv,
      d39GeomBallIsoV2RepresentationDartEquiv,
      d39GeomBallIsoV2DirectedEdgeEquiv, a]
  have htarget :
      let q := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d
      if (y.dartEquiv q.1).2 then
        C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (y.faceOfDart q.1) (y.dartEquiv q.1).1
      else
        C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (y.faceOfDart q.1) (y.dartEquiv q.1).1 := by
    dsimp only
    exact y.face_left_of_dart
      (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1
  refine ⟨?_, ?_⟩
  · cases hb : (x.dartEquiv d.1).2
    · have hsource' :
        B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (x.faceOfDart d.1) (x.dartEquiv d.1).1 := by
        simpa [hb] using hsource
      cases hf : e.edgeFlip a
      · have hmap := (d39GeomBallIsoV2_sideRightOf_map e F a).mp hsource'
        simpa [a, F, hb, hf] using hmap
      · have hmap := (d39GeomBallIsoV2_sideRightOf_map e F a).mp hsource'
        simpa [a, F, hb, hf] using hmap
    · have hsource' :
        B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (x.faceOfDart d.1) (x.dartEquiv d.1).1 := by
        simpa [hb] using hsource
      cases hf : e.edgeFlip a
      · have hmap := (d39GeomBallIsoV2_sideLeftOf_map e F a).mp hsource'
        simpa [a, F, hb, hf] using hmap
      · have hmap := (d39GeomBallIsoV2_sideLeftOf_map e F a).mp hsource'
        simpa [a, F, hb, hf] using hmap
  · exact ⟨hpair, htarget⟩





























































end DirectedDistances.PaperProofs.Section5

end
