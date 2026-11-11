/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BusemannM0Unconditional












public section
namespace DirectedDistances.PaperProofs.Section1

open Quiver MeasureTheory DirectedDistances.KMSW

 
theorem thm_busemann_sdp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannSDP
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) :=
  iidCodes_ae_boundaryBusemannSDP_existsUnique

/-- hit-indexed boundary labelling, almost surely for iid codes. Local finiteness `hfin` makes -/
theorem thm_busemann_ldp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannLDP
              (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) :=
  iidCodes_ae_boundaryBusemannLDP_existsUnique

end DirectedDistances.PaperProofs.Section1
