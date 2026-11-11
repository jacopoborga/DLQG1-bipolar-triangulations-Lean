/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapEndpointSwap

/-! Supporting lemmas for paper labels `defn:planar-map-with-missing-edges` (see CORRESPONDENCE.md). -/







public section

universe u v

namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

variable {V : Type u} {E : Type v}



theorem def_missing_edges_provider_v2 :
    ∀ (M : DirectedPlaneMapWithMissing V E),
      (∀ e, M.toPlaneMapWithMissing.missing e →
        ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F ∧
            Set.range (M.toPlaneMapWithMissing.arc e) ⊆ closure F.val) ∧
      (∀ u w,
        M.step u w ↔
          ∃ e : {e : E // ¬ M.toPlaneMapWithMissing.missing e},
            M.tail e = u ∧ M.head e = w) ∧
      (M.IsAcyclic ↔ ∀ v, ¬ Relation.TransGen M.step v v) := by
  intro M
  exact ⟨M.toPlaneMapWithMissing.missing_on_external,
    fun _ _ => M.step_iff _ _, M.isAcyclic_iff⟩

/-- Supporting theorem for Definition 3.1: its missing-edge face condition,
present-edge steps, and acyclicity predicate are preserved by `HomeoEquiv`. -/
theorem def_missing_edges_homeo_invariant
    {V' : Type u} {E' : Type v}
    (M : DirectedPlaneMapWithMissing V E)
    (M' : DirectedPlaneMapWithMissing V' E')
    (e : DirectedPlaneMapWithMissing.HomeoEquiv M M') :
    (∀ f, M'.toPlaneMapWithMissing.missing (e.drawing.drawing.σE f) ↔
      M.toPlaneMapWithMissing.missing f) ∧
    (∀ f,
      (M.toPlaneMapWithMissing.missing f →
        ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F ∧
            Set.range (M.toPlaneMapWithMissing.arc f) ⊆ closure F.val) ↔
      (M'.toPlaneMapWithMissing.missing (e.drawing.drawing.σE f) →
        ∃ F' : M'.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          M'.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F' ∧
            Set.range (M'.toPlaneMapWithMissing.arc (e.drawing.drawing.σE f)) ⊆
              closure F'.val)) ∧
    (∀ u w,
      M.step u w ↔
        M'.step (e.drawing.drawing.σV u) (e.drawing.drawing.σV w)) ∧
    (M.IsAcyclic ↔ M'.IsAcyclic) := by
  exact ⟨e.drawing.missing_map, e.drawing.missing_on_external_map_iff,
    e.step_map_iff, e.isAcyclic_map_iff⟩

/-- Supporting theorem for Definition 3.1: the same clauses are preserved by
endpoint storage swap after a `HomeoEndpointSwapEquiv`. -/
theorem def_missing_edges_endpointSwap_invariant
    {V' : Type u} {E' : Type v}
    (M : DirectedPlaneMapWithMissing V E)
    (M' : DirectedPlaneMapWithMissing V' E')
    (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (swap : E' → Bool) :
    (∀ f,
      (M'.endpointSwap swap).toPlaneMapWithMissing.missing
          (e.drawing.drawing.σE f) ↔
        M.toPlaneMapWithMissing.missing f) ∧
    (∀ f,
      (M.toPlaneMapWithMissing.missing f →
        ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F ∧
            Set.range (M.toPlaneMapWithMissing.arc f) ⊆ closure F.val) ↔
      ((M'.endpointSwap swap).toPlaneMapWithMissing.missing
          (e.drawing.drawing.σE f) →
        ∃ F' : (M'.endpointSwap swap).toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          (M'.endpointSwap swap).toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal
            F' ∧
            Set.range ((M'.endpointSwap swap).toPlaneMapWithMissing.arc
              (e.drawing.drawing.σE f)) ⊆ closure F'.val)) ∧
    (∀ u w,
      M.step u w ↔
        (M'.endpointSwap swap).step
          (e.drawing.drawing.σV u) (e.drawing.drawing.σV w)) ∧
    (M.IsAcyclic ↔ (M'.endpointSwap swap).IsAcyclic) := by
  let endpointEquiv : PlaneMapWithMissing.HomeoEndpointSwapEquiv
      M.toPlaneMapWithMissing M'.toPlaneMapWithMissing := ⟨e.drawing, swap⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    exact (endpointSwap_missing M'.toPlaneMapWithMissing swap
      (e.drawing.drawing.σE f)).trans (e.drawing.missing_map f)
  · intro f
    exact endpointEquiv.missingOnExternal_map_iff f
  · intro u w
    exact (e.step_map_iff u w).trans
      (DirectedPlaneMapWithMissing.endpointSwap_step_iff M' swap _ _).symm
  · exact e.isAcyclic_map_iff.trans
      (DirectedPlaneMapWithMissing.endpointSwap_isAcyclic_iff M' swap).symm

end DirectedDistances.PaperProofs.SourceResults

end
