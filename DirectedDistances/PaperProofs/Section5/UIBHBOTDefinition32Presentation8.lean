/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTDefinition32Presentation7
public import DirectedDistances.PlanarMap.PLDrawingWindingSides18

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the UIBHBOT presentation has no upper-left
or lower-right indices, so their `LeftOf` and `RightOf` clauses are vacuous. -/
theorem uibhbotDefinition32Presentation_leftRightSidePredicates
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
    (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
      (uibhbotPastMonotoneDrawing W hfin).pos)
    (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
      ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
    (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (shiftedStream W 0) (H.1 0))
      (kmswLimitDartVertex (shiftedStream W 0)))
    (hf : F.pos = uibhbotSeparationFuturePos W H h0)
    (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
    (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
      h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    ULOkInf (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
      hFim hFa hRpos e hinj) ∧
    LROkInf (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
      hFim hFa hRpos e hinj) := by
  have h := uibhbotDefinition32Presentation_emptySides W H h0 hL hR hfin P hp ha F hf
    hFim hFa hRpos e hinj
  exact ⟨h.1, h.2.2⟩

















































end DirectedDistances.PaperProofs.Section5

end
