/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapEndpointSwap





public section

namespace DirectedDistances.PlanarMap

open Set

variable {V E V' E' : Type*}

namespace PlaneGraphDrawing

/-- Helper toward Definition 3.1: an edge image lies in an external face's
closure exactly when it lies in that face's frontier. -/
theorem range_subset_closure_iff_frontier_of_face_complement
    (D : PlaneGraphDrawing V E)
    (F : D.Face) (e : E) :
    Set.range (D.arc e) ⊆ closure F.val ↔
      Set.range (D.arc e) ⊆ frontier F.val := by
  have hface : F.val ⊆ D.imageᶜ := D.face_subset_compl_image F
  constructor
  · intro h x hx
    rw [frontier_eq_closure_inter_closure]
    refine ⟨h hx, ?_⟩
    have hximage : x ∈ D.image := by
      change x ∈ Set.range D.pos ∪ ⋃ f : E, Set.range (D.arc f)
      exact Or.inr (Set.mem_iUnion.2 ⟨e, hx⟩)
    have hxnotface : x ∉ F.val := by
      intro hxF
      exact hface hxF hximage
    exact subset_closure hxnotface
  · intro h
    exact h.trans frontier_subset_closure

end PlaneGraphDrawing

namespace PlaneMapWithMissing

/-- The source-form missing-edge condition: each missing edge is contained in
the frontier of at least one external face. Helper toward Definition 3.1. -/
def MissingOnExternalBoundary (M : PlaneMapWithMissing V E) : Prop :=
  ∀ e, M.missing e →
    ∃ F : M.toPlaneGraphDrawing.Face,
      M.toPlaneGraphDrawing.IsExternal F ∧
        Set.range (M.arc e) ⊆ frontier F.val

/-- The frontier formulation is equivalent to the carrier's closure
formulation of the missing-edge condition. Helper toward Definition 3.1. -/
theorem missingOnExternalBoundary_iff (M : PlaneMapWithMissing V E) :
    M.MissingOnExternalBoundary ↔
      (∀ e, M.missing e →
        ∃ F : M.toPlaneGraphDrawing.Face,
          M.toPlaneGraphDrawing.IsExternal F ∧
            Set.range (M.arc e) ⊆ closure F.val) := by
  constructor
  · intro h e he
    rcases h e he with ⟨F, hF, hfrontier⟩
    exact ⟨F, hF,
      (M.toPlaneGraphDrawing.range_subset_closure_iff_frontier_of_face_complement
        F e).mpr hfrontier⟩
  · intro h e he
    rcases h e he with ⟨F, hF, hclosure⟩
    exact ⟨F, hF,
      (M.toPlaneGraphDrawing.range_subset_closure_iff_frontier_of_face_complement
        F e).mp hclosure⟩

end PlaneMapWithMissing

namespace DirectedPlaneMapWithMissing

variable {M : DirectedPlaneMapWithMissing V E}
  {M' : DirectedPlaneMapWithMissing V' E'}

/-- The source-form missing-edge boundary condition is invariant under a
combined homeomorphism and endpoint-storage swap. Helper toward Definition
3.1. -/
theorem missingOnExternalBoundary_map_iff
    (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M') :
    (M'.endpointSwap e.swap).toPlaneMapWithMissing.MissingOnExternalBoundary ↔
      M.toPlaneMapWithMissing.MissingOnExternalBoundary := by
  rw [PlaneMapWithMissing.missingOnExternalBoundary_iff,
    PlaneMapWithMissing.missingOnExternalBoundary_iff]
  constructor
  · intro h f hf
    have htarget := h (e.homeo.drawing.drawing.σE f)
    exact (e.missing_on_external_map_iff f).mpr htarget hf
  · intro h g hg
    let f := e.homeo.drawing.drawing.σE.symm g
    have htarget :
        (M'.endpointSwap e.swap).toPlaneMapWithMissing.missing
          (e.homeo.drawing.drawing.σE f) := by
      simpa [f] using hg
    have hsource : M.toPlaneMapWithMissing.missing f :=
      (e.missing_map f).mp htarget
    have hboundary := h f hsource
    have hsourceCondition : M.toPlaneMapWithMissing.missing f →
        ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F ∧
            Set.range (M.toPlaneMapWithMissing.arc f) ⊆ closure F.val :=
      fun _ => hboundary
    have htargetCondition := (e.missing_on_external_map_iff f).mp hsourceCondition
    have hindex : e.homeo.drawing.drawing.σE f = g := by
      dsimp [f]
      exact e.homeo.drawing.drawing.σE.apply_symm_apply g
    rw [hindex] at htargetCondition htarget
    exact htargetCondition htarget

end DirectedPlaneMapWithMissing

end DirectedDistances.PlanarMap

end

