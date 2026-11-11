/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso8

/-! # Successor uniqueness toward Proposition 5.16

Helper toward Proposition 5.16. This file isolates the already available
uniqueness principle for one direction system and records the remaining
independent-straightener and first-return obligations. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. In a finite star with distinct direction
arguments, two counterclockwise-successor witnesses for the same direction
function agree. -/
theorem d39_CcwSuccessor_unique
    {D : Type*} {star : Set D} {dir : D → ℂ} {d e f : D}
    (harg : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (he : CcwSuccessor star dir d e)
    (hf : CcwSuccessor star dir d f) : e = f :=
  d39CcwSuccessor_unique harg he hf































































































end DirectedDistances.PaperProofs.Section5

end
