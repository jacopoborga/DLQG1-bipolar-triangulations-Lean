/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalDomain

/-! # Canonical UIBHBOT root mark in the Definition 3.8 domain

Helpers toward Definition 3.8 consumers. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Set

noncomputable section

/-- Helper toward Definition 3.8 consumers: the code-defined UIBHBOT root
edge is the left-lower edge created at local time one in the window beginning
at time one. -/
theorem uibhbotD39RootEdge_codeIdentity (W : ℤ → Fin 3) :
    uibhbotRootEdge W =
      wholePlaneEdgeι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1) := rfl









































end

end DirectedDistances.PaperProofs.Section5
