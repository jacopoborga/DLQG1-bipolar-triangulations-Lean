/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Carriers4

/-! Supporting lemmas for paper labels `defn:bound-edges` (see CORRESPONDENCE.md). -/
























public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap




theorem def_bound_edges_source_provider :
    UIQBOTBoundEdges32Source ∧ UIBHBOTBoundEdges32Source ∧
    KMSWStageBoundEdges32Source ∧ BoundaryChanneledBoundEdges32Source ∧
    M0CutSuppliedBoundEdges32Source :=
  bound_edges_definition32_source_with_m0Cut

end DirectedDistances.PaperProofs.SourceResults
