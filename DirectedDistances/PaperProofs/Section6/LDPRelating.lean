/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.LDPRelatingX1X









public section
namespace DirectedDistances.PaperProofs.Section6

open Quiver MeasureTheory DirectedDistances.KMSW

/-- almost surely for iid codes. The LDP boundary Busemann functions `X0` of `M_{0,∞}` and `X1` of
`M_{1,∞}` exist, and every such pair satisfies `eqn-ldp-relating1`, `eqn-ldp-relating2` and -/
theorem lem_ldp_relating_X1_X :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin0 : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ hfin1 : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => w (1 + i)) n).nextEdge ∧
          ((kmswStage (fun i => w (1 + i)) n).west e = v ∨
            (kmswStage (fun i => w (1 + i)) n).east e = v)}.Finite,
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
        (∃ X0 : ℤ → ℤ,
          IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin0)
            (boundaryPresentVertex w h0) X0) ∧
        (∃ X1 : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
            (boundaryPresentVertex (fun i => w (1 + i)) h1) X1) ∧
        ∀ X0' X1' : ℤ → ℤ,
          IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin0)
            (boundaryPresentVertex w h0) X0' →
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
            (boundaryPresentVertex (fun i => w (1 + i)) h1) X1' →
          (ω 1 = 2 → (X0' (-1), X0' 1) =
            (X1' (-2) - max (X1' (-1)) 1, -max (X1' (-1)) 1)) ∧
          (ω 1 = 0 → (X0' (-1), X0' 1) = (-X1' 1 - 1, -1)) ∧
          (ω 1 = 1 → (X0' (-1), X0' 1) = (X1' (-1), X1' 2)) :=
  DirectedDistances.Recursive.iidCodes_ae_ldp_relating_X1_X_all

end DirectedDistances.PaperProofs.Section6
