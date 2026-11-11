/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass11
public import DirectedDistances.Probability.BSLocalCylinderMeasurable

/-! Helpers toward Proposition 5.16 (`prop-disk-bs-conv`).

# Orientation of the UIBHBOT variable seam transfer -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16 (`prop-disk-bs-conv`): the variable-seam
orientation statement recorded at `UIBHBOTD39CanonicalClass8.lean:109`.
CanonicalClass9 proves the winding-preservation result used here; this
re-export keeps its exact binders available in the Proposition 5.16 chain. -/
theorem uibhbotVerticalSeamTransfer_orientationPreserving_prop516
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    OrientationPreserving (uibhbotVerticalSeamTransfer f g hf hg) :=
  uibhbotVerticalSeamTransfer_orientationPreserving f g hf hg

end DirectedDistances.PaperProofs.Section5

end
