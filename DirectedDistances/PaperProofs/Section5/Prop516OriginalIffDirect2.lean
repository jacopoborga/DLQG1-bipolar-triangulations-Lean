/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect
public import DirectedDistances.PaperProofs.Section5.Prop516LeftSideHalfDisk3









public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap Set
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open scoped Topology

/-- Helper toward Proposition 5.16: two faces of the general drawing
containing the same point are equal. No PL structure is required. -/
theorem d39PlaneGraphDrawing_faces_eq_of_mem
    {V E : Type*} (D : PlaneGraphDrawing V E)
    {F G : D.Face} {z : ℂ} (hzF : z ∈ F.val) (hzG : z ∈ G.val) :
    F = G := by
  obtain ⟨x, _, hF⟩ := F.property
  obtain ⟨y, _, hG⟩ := G.property
  apply Subtype.ext
  calc
    F.val = connectedComponentIn D.imageᶜ x := hF
    _ = connectedComponentIn D.imageᶜ z :=
      connectedComponentIn_eq (hF ▸ hzF)
    _ = connectedComponentIn D.imageᶜ y :=
      (connectedComponentIn_eq (hG ▸ hzG)).symm
    _ = G.val := hG.symm

/-- Helper toward Proposition 5.16: a connected subset of the complement
meeting two general drawing faces identifies them. This supplies the final
connected-component step on the carrier of `D39DrawingRepresentationData3`. -/
theorem d39PlaneGraphDrawing_face_eq_of_common_connected_region
    {V E : Type*} (D : PlaneGraphDrawing V E) {U : Set ℂ}
    (hUconn : IsConnected U) (hUavoid : U ⊆ D.imageᶜ)
    (F G : D.Face) (hUF : (U ∩ F.val).Nonempty)
    (hUG : (U ∩ G.val).Nonempty) : F = G := by
  obtain ⟨x, hxU, hxF⟩ := hUF
  obtain ⟨y, hyU, hyG⟩ := hUG
  obtain ⟨z, _, hF⟩ := F.property
  have hxComp : x ∈ connectedComponentIn D.imageᶜ z := hF ▸ hxF
  have hyComp : y ∈ connectedComponentIn D.imageᶜ x :=
    hUconn.isPreconnected.subset_connectedComponentIn hxU hUavoid hyU
  have hyF : y ∈ F.val := by
    rw [hF, connectedComponentIn_eq hxComp]
    exact hyComp
  exact d39PlaneGraphDrawing_faces_eq_of_mem D hyF hyG

/-- Helper toward Proposition 5.16: every nonempty connected region avoiding
the general drawing is contained in exactly one face. The region need not be
open, and the drawing need not be closed or polygonal. -/
theorem d39PlaneGraphDrawing_exists_unique_face_of_connected_region
    {V E : Type*} (D : PlaneGraphDrawing V E) {U : Set ℂ}
    (hUconn : IsConnected U) (hUavoid : U ⊆ D.imageᶜ) :
    ∃! F : D.Face, U ⊆ F.val := by
  obtain ⟨z, hzU⟩ := hUconn.nonempty
  let F : D.Face :=
    ⟨connectedComponentIn D.imageᶜ z, z, hUavoid hzU, rfl⟩
  have hUF : U ⊆ F.val :=
    hUconn.isPreconnected.subset_connectedComponentIn hzU hUavoid
  refine ⟨F, hUF, ?_⟩
  intro G hUG
  exact d39PlaneGraphDrawing_faces_eq_of_mem D (hUG hzU) (hUF hzU)




































































































end DirectedDistances.PaperProofs.Section5
