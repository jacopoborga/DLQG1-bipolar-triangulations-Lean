 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.MissingEdgesSourceProvider

/-!
# Definition 3.1 (`defn:planar-map-with-missing-edges`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/



















public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

universe u v

 
theorem defn_planar_map_with_missing_edges {V : Type u} {E : Type v} :
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
        (e.homeo.drawing.drawing.σV x) (e.homeo.drawing.drawing.σV y))) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_missing_edges_source_provider
 
 

end DirectedDistances.Paper.Section3
 
