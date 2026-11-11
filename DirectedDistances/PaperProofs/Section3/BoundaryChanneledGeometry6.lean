/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry4
import Mathlib.Topology.MetricSpace.Bounded

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open Metric

/-- Helper toward Definition 3.2: the finite channeled drawing has a concrete
closed-ball bound. The bound uses only finiteness of its vertex and dart
carriers; it does not locate the marked outer cycle relative to infinity. -/
theorem boundaryChanneled_image_subset_closedBall
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    ∃ ρ : ℝ, G.image ⊆ closedBall (0 : ℂ) ρ := by
  exact G.isBounded_image.subset_closedBall 0













































































































end DirectedDistances.PaperProofs.Section3

end
end
