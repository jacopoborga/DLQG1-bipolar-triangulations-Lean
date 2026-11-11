/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTDefinition32Presentation2
public import DirectedDistances.PaperProofs.SourceResults.UIBHBOTDefinitionV2

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
  DirectedDistances.PlanarMap DirectedDistances.PaperProofs.SourceResults
open scoped Classical

/-- Helper toward Definition 3.2: a present edge cannot border an unbounded
assembly face. The assembly characterization says every dart bordering an
unbounded face belongs to a missing edge. -/
theorem uibhbot_presentEdge_borders_only_bounded_faces
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
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) :
    ∀ a : (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).GeometricEdge,
      wholePlaneEdgePresent W a.out.1 →
        ∀ d : WholePlaneDart W, d.1 = a.out.1 →
          ∀ K : (uibhbotCcw_assemblyDrawing
            W H h0 hL hR hfin P hp ha F hf hFim hFa).Face,
            (uibhbotCcw_assemblyDrawing
              W H h0 hL hR hfin P hp ha F hf hFim hFa).dartBorders d K →
              ¬ (uibhbotCcw_assemblyDrawing
                W H h0 hL hR hfin P hp ha F hf hFim hFa).IsUnbounded K := by
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  intro a hpresent d hedge K hborder hUnbounded
  have hmissing := (uibhbot_assembly_unbounded_dartBorders_iff
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos K hUnbounded d).mp hborder
  have hpresent : wholePlaneEdgePresent W d.1 := by
    rw [hedge]
    exact hpresent
  exact hmissing.2 hpresent





















































end DirectedDistances.PaperProofs.Section5

end
