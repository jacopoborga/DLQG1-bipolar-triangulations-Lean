/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.MissingEdgesDefinition
public import DirectedDistances.PlanarMap.GeneralPlaneMapExternalBoundary

/-! Supporting lemmas for paper labels `defn:planar-map-with-missing-edges` (see CORRESPONDENCE.md). -/







public section

universe u v

namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

variable {V : Type u} {E : Type v}











theorem def_missing_edges_source_provider :
    (∀ M : PlaneMapWithMissing V E, M.MissingOnExternalBoundary) ∧
    (∀ M : {M : DirectedPlaneMapWithMissing V E // M.IsAcyclic},
      M.1.toPlaneMapWithMissing.MissingOnExternalBoundary ∧
      (∀ u w, M.1.step u w ↔
        ∃ e : {e : E // ¬ M.1.toPlaneMapWithMissing.missing e},
          M.1.tail e = u ∧ M.1.head e = w) ∧
      (∀ x, ¬ Relation.TransGen M.1.step x x)) ∧
    (∀ {V' : Type u} {E' : Type v} (M : DirectedPlaneMapWithMissing V E)
      (M' : DirectedPlaneMapWithMissing V' E')
      (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M'),
      (M.IsAcyclic ↔ (M'.endpointSwap e.swap).IsAcyclic) ∧
      ((M'.endpointSwap e.swap).toPlaneMapWithMissing.MissingOnExternalBoundary ↔
        M.toPlaneMapWithMissing.MissingOnExternalBoundary) ∧
      (∀ f, (M'.endpointSwap e.swap).toPlaneMapWithMissing.missing
          (e.homeo.drawing.drawing.σE f) ↔ M.toPlaneMapWithMissing.missing f) ∧
      (∀ x y, M.step x y ↔ (M'.endpointSwap e.swap).step
        (e.homeo.drawing.drawing.σV x) (e.homeo.drawing.drawing.σV y))) := by
  refine ⟨fun M => (PlaneMapWithMissing.missingOnExternalBoundary_iff M).mpr
      M.missing_on_external, fun M => ?_, fun M M' e => ?_⟩
  · exact ⟨(PlaneMapWithMissing.missingOnExternalBoundary_iff _).mpr
        M.1.toPlaneMapWithMissing.missing_on_external,
      fun u w => M.1.step_iff u w, M.2⟩
  · exact ⟨e.isAcyclic_map_iff,
      DirectedPlaneMapWithMissing.missingOnExternalBoundary_map_iff e,
      e.missing_map, e.step_map_iff⟩

end DirectedDistances.PaperProofs.SourceResults

end
