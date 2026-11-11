/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly4
public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly3








public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: if a connected region avoids the PL
drawing and meets two of its faces, those faces are equal. This is the final
connected-component step in the proposed local half-disk argument. -/
theorem d39PLDrawing_face_eq_of_common_connected_region
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) {U : Set ℂ}
    (hUconn : IsConnected U) (hUavoid : U ⊆ P.imageᶜ)
    (F F' : P.Face) (hUF : (U ∩ F.val).Nonempty)
    (hUF' : (U ∩ F'.val).Nonempty) : F = F' := by
  obtain ⟨x, hxU, hxF⟩ := hUF
  obtain ⟨y, hyU, hyF'⟩ := hUF'
  obtain ⟨z, _, hF⟩ := F.property
  have hxComp : x ∈ connectedComponentIn P.imageᶜ z := by
    simpa only [hF] using hxF
  have hyCompX : y ∈ connectedComponentIn P.imageᶜ x :=
    (hUconn.isPreconnected.subset_connectedComponentIn hxU hUavoid) hyU
  have hcomp : connectedComponentIn P.imageᶜ z =
      connectedComponentIn P.imageᶜ x := connectedComponentIn_eq hxComp
  have hyF : y ∈ F.val := by
    rw [hF, hcomp]
    exact hyCompX
  exact P.faces_eq_of_mem hyF hyF'






































end DirectedDistances.PaperProofs.Section5

end

