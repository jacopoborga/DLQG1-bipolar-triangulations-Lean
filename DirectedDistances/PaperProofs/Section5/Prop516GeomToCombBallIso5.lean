/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso4

/-! # Retained-face side transport for geometric-to-combinatorial balls

Helpers toward Proposition 5.16. This file records the side-incidence
transport supplied by a geometric ball isomorphism and the remaining exact
face-successor obstruction. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. A strictly increasing homeomorphism of
the unit interval fixes its endpoints. -/
private theorem d39GeomBallIsoV2_strictMono_endpoints (φ : I ≃ₜ I)
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

/-- Helper toward Proposition 5.16. A strictly decreasing homeomorphism of
the unit interval reverses its endpoints. -/
private theorem d39GeomBallIsoV2_strictAnti_endpoints (φ : I ≃ₜ I)
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

/-- Helper toward Proposition 5.16. A retained geometric face on the left
of a represented edge is transported to the left of its image when the edge
storage direction is preserved, and to the right when it is reversed. -/
theorem d39GeomBallIsoV2_sideLeftOf_map
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (F : {F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces B.map B.root r})
    (a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r}) :
    B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F.1 a.1 ↔
      if e.edgeFlip a then
        C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (e.faceEquiv F).1 (e.edgeEquiv a).1
      else
        C.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (e.faceEquiv F).1 (e.edgeEquiv a).1 := by
  cases hflip : e.edgeFlip a
  · have hmono := e.edgeParam_mono a hflip
    obtain ⟨h0, h1⟩ := d39GeomBallIsoV2_strictMono_endpoints
      (e.edgeParam a) hmono
    have hpath : ∀ t : I,
        ((B.map.toPlaneMapWithMissing.arc a.1).map e.h.continuous) t =
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).reparam
            (e.edgeParam a) (e.edgeParam a).continuous h0 h1 t := by
      intro t
      exact e.arc_map a t
    change B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F.1 a.1 ↔ _
    change (∀ s, LeftAtOn F.1.val
      (B.map.toPlaneMapWithMissing.arc a.1) s) ↔ _
    change (∀ s, LeftAtOn F.1.val
      (B.map.toPlaneMapWithMissing.arc a.1) s) ↔
      (∀ s, LeftAtOn ((e.faceEquiv F).1).val
        (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s)
    calc
      (∀ s, LeftAtOn F.1.val (B.map.toPlaneMapWithMissing.arc a.1) s) ↔
          (∀ s, LeftAtOn (e.h '' F.1.val)
            ((B.map.toPlaneMapWithMissing.arc a.1).map e.h.continuous) s) := by
        apply forall_congr'
        intro s
        exact leftAtOn_map_iff _ _ s e.h e.orientationPreserving
      _ ↔ (∀ s, LeftAtOn (e.h '' F.1.val)
          ((C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).reparam
            (e.edgeParam a) (e.edgeParam a).continuous h0 h1) s) := by
        apply forall_congr'
        intro s
        exact leftAtOn_congr_fun _ _ _ s hpath
      _ ↔ (∀ s, LeftAtOn (e.h '' F.1.val)
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s) :=
        forall_leftAtOn_reparam_iff _ _ (e.edgeParam a) h0 h1
      _ = (∀ s, LeftAtOn ((e.faceEquiv F).1).val
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s) := by
        rw [← e.face_image_map F]
  · have hanti := e.edgeParam_anti a hflip
    simp
    obtain ⟨h0, h1⟩ := d39GeomBallIsoV2_strictAnti_endpoints
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
    change B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F.1 a.1 ↔ _
    change (∀ s, LeftAtOn F.1.val
      (B.map.toPlaneMapWithMissing.arc a.1) s) ↔ _
    change (∀ s, LeftAtOn F.1.val
      (B.map.toPlaneMapWithMissing.arc a.1) s) ↔
      (∀ s, RightAtOn ((e.faceEquiv F).1).val
        (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s)
    calc
      (∀ s, LeftAtOn F.1.val (B.map.toPlaneMapWithMissing.arc a.1) s) ↔
          (∀ s, LeftAtOn (e.h '' F.1.val)
            ((B.map.toPlaneMapWithMissing.arc a.1).map e.h.continuous) s) := by
        apply forall_congr'
        intro s
        exact leftAtOn_map_iff _ _ s e.h e.orientationPreserving
      _ ↔ (∀ s, LeftAtOn (e.h '' F.1.val)
          ((C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).symm.reparam
            ψ ψ.continuous hψ0 hψ1) s) := by
        apply forall_congr'
        intro s
        exact leftAtOn_congr_fun _ _ _ s hpath
      _ ↔ (∀ s, LeftAtOn (e.h '' F.1.val)
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).symm s) :=
        forall_leftAtOn_reparam_iff _ _ ψ hψ0 hψ1
      _ ↔ (∀ s, RightAtOn (e.h '' F.1.val)
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s) :=
        forall_leftAtOn_symm_iff _ _
      _ = (∀ s, RightAtOn ((e.faceEquiv F).1).val
          (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) s) := by
        rw [← e.face_image_map F]






























end DirectedDistances.PaperProofs.Section5

end
