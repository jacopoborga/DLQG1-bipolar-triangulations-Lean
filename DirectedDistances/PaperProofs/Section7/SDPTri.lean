/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BusemannItemForms





public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver MeasureTheory DirectedDistances.KMSW

/-- for iid codes, with `M_{0,∞}` the KMSW map of the carrier `fun i => ω (i + 1)`, every SDP
boundary Busemann function `X` satisfies
`SDP(x_ℓ, x_k) ≥ X(ℓ) - X(k)` for `0 ≤ ℓ < k`. Reachability of `x_k` from `x_ℓ` is part of -/
theorem lem_sdp_tri :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (X : ℤ → ℤ),
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => ω (i + 1)) h) X →
        ∀ l k : ℤ, 0 ≤ l → l < k →
          Reachable (boundaryPresentVertex (fun i => ω (i + 1)) h l)
            (boundaryPresentVertex (fun i => ω (i + 1)) h k) ∧
          X l - X k ≤
            ((sdp (boundaryPresentVertex (fun i => ω (i + 1)) h l)
              (boundaryPresentVertex (fun i => ω (i + 1)) h k)).toNat : ℤ) :=
  DirectedDistances.KMSW.lem_sdp_tri

end DirectedDistances.PaperProofs.Section7
