/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.SDPRelatingX1X










public section
namespace DirectedDistances.PaperProofs.Section6

open Quiver MeasureTheory DirectedDistances.KMSW

/-- almost surely for iid codes. The SDP boundary Busemann functions `X0` of `M_{0,∞}` and `X1` of
`M_{1,∞}` exist, and every such pair satisfies `eqn-sdp-relating1`, `eqn-sdp-relating2` and -/
theorem lem_sdp_relating_X1_X :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
        (∃ X0 : ℤ → ℤ, IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0) ∧
        (∃ X1 : ℤ → ℤ,
          IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => w (1 + i)) h1) X1) ∧
        ∀ X0' X1' : ℤ → ℤ,
          IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0' →
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => w (1 + i)) h1) X1' →
          (ω 1 = 2 → (X0' (-1), X0' 1) =
            (X1' (-2) - min (X1' (-1)) 1, -min (X1' (-1)) 1)) ∧
          (ω 1 = 0 → (X0' (-1), X0' 1) = (-X1' 1 - 1, -1)) ∧
          (ω 1 = 1 → (X0' (-1), X0' 1) =
            (X1' (-1) - min 0 (X1' 2 + 1), X1' 2 - min 0 (X1' 2 + 1))) :=
  DirectedDistances.Recursive.iidCodes_ae_sdp_relating_X1_X_all

end DirectedDistances.PaperProofs.Section6
