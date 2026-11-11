 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BoundEdgesDefinition32Provider

/-!
# Definition 3.2 (`defn:bound-edges`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/


























public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.PlanarMap

 
theorem def_bound_edges :
    UIQBOTBoundEdges32Source ∧ UIBHBOTBoundEdges32Source ∧
    KMSWStageBoundEdges32Source ∧ BoundaryChanneledBoundEdges32Source ∧
    M0CutSuppliedBoundEdges32Source :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_bound_edges_source_provider
 
 

end DirectedDistances.Paper.Section3
 
