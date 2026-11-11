/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat4

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`). This file exports the
canonical assembly's marked ambient outer face. It records the remaining
restricted-orbit representation bridge and mirrored comparison. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

/-- Helper toward Proposition 5.9. The canonical assembly's marked outer
dart borders its ambient unbounded face, as specified by the canonical
assembly plane-face correspondence. -/
theorem prop59_canonicalAssembly_outerDart_borders_ambientUnboundedFace
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) :
    let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
    let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
    let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
    let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
    let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa D.pastRightPositive
    let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
    let outerFace := A (Quotient.mk _ (uibhbotWholePlaneOuterDart W))
    G.dartBorders M.core.outer outerFace ∧ G.IsUnbounded outerFace := by
  let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa D.pastRightPositive
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let outerFace := A (Quotient.mk _ (uibhbotWholePlaneOuterDart W))
  have houter : M.core.outer = uibhbotWholePlaneOuterDart W := by
    change (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).outer = _
    rfl
  have hborder : G.dartBorders (uibhbotWholePlaneOuterDart W) outerFace :=
    uibhbotD39Assembly_faceOrbitEquiv_dartBorders W D
      (uibhbotWholePlaneOuterDart W)
  have hunbounded : G.IsUnbounded outerFace :=
    (uibhbot_assembly_isUnbounded_iff_outer_dartBorders
      W D.rotation D.boundary D.pastLeftUnbounded D.pastRightNonnegative
      D.pastFiniteIncidence P hp ha F hf hFim hFa D.pastRightPositive _).2 hborder
  exact ⟨houter ▸ hborder, hunbounded⟩
































































end DirectedDistances.PaperProofs.Section5

end
