/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalDomain2

/-! # Canonical UIBHBOT root domain in Definition 3.8

Helpers toward Definition 3.8 consumers. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Set

noncomputable section

/-- Helper toward Definition 3.8 consumers: the canonical root mark is the
code-built west root edge with the quotient representative Boolean. -/
theorem uibhbotD39CanonicalRootMark_edge (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) :
    (by
      classical
      exact
        let P := uibhbotD39PastCanonicalDrawing W hL hR hfin
        let F := uibhbotD39FutureCanonicalDrawing W H h0
        let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P
          (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
          (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin) F
          (uibhbotD39FutureCanonicalDrawing_pos W H h0)
          (uibhbotD39FutureCanonicalDrawing_image W H h0)
          (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)
        (uibhbotAssemblyD39RootMark W H h0 hL hR hfin P
          (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
          (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin) F
          (uibhbotD39FutureCanonicalDrawing_pos W H h0)
          (uibhbotD39FutureCanonicalDrawing_image W H h0)
          (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)).1 =
          Quotient.mk G.edgeSetoid
            (wholePlaneEdgeι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1), false) ∧
        (uibhbotAssemblyD39RootMark W H h0 hL hR hfin P
          (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
          (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin) F
          (uibhbotD39FutureCanonicalDrawing_pos W H h0)
          (uibhbotD39FutureCanonicalDrawing_image W H h0)
          (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)).2 =
          decide ((Quotient.mk G.edgeSetoid
            (wholePlaneEdgeι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1), false)).out =
              ((wholePlaneEdgeι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1), false) :
                WholePlaneDart W))) := by
  let P := uibhbotD39PastCanonicalDrawing W hL hR hfin
  let F := uibhbotD39FutureCanonicalDrawing W H h0
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P
    (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin) F
    (uibhbotD39FutureCanonicalDrawing_pos W H h0)
    (uibhbotD39FutureCanonicalDrawing_image W H h0)
    (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)
  have hmark := uibhbotAssemblyD39RootMark_eq W H h0 hL hR hfin P
    (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin) F
    (uibhbotD39FutureCanonicalDrawing_pos W H h0)
    (uibhbotD39FutureCanonicalDrawing_image W H h0)
    (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)
  rw [uibhbotD39RootEdge_codeIdentity] at hmark
  constructor
  · exact congrArg Prod.fst hmark
  · exact congrArg Prod.snd hmark

/-- Helper toward Definition 3.8 consumers: almost surely the canonical
UIBHBOT assembly has a valid root mark, together with its canonical drawing
witnesses and the source's rooted edge enumeration. -/
theorem uibhbotCodeLawRel_ae_d39CanonicalRootValid :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W),
      e 0 = uibhbotRootEdge W ∧
        (uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin
          (uibhbotD39PastCanonicalDrawing W hL hR hfin)
          (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
          (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
          (uibhbotD39FutureCanonicalDrawing W H h0)
          (uibhbotD39FutureCanonicalDrawing_pos W H h0)
          (uibhbotD39FutureCanonicalDrawing_image W H h0)
          (uibhbotD39FutureCanonicalDrawing_arcImage W H h0) hRpos).missing
          (uibhbotAssemblyD39RootMark W H h0 hL hR hfin
            (uibhbotD39PastCanonicalDrawing W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
            (uibhbotD39FutureCanonicalDrawing W H h0)
            (uibhbotD39FutureCanonicalDrawing_pos W H h0)
            (uibhbotD39FutureCanonicalDrawing_image W H h0)
            (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)).1 := by
  filter_upwards [def_uibhbot_provider_v2] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P₀, hp₀, ha₀, F₀, hf₀, hFim₀, hFa₀,
    hRpos, e, hprovider⟩
  rcases hprovider with ⟨_, _, _, _, _, _, _, _, _, _, he, _, _, _, _, _,
    hrootMissing, _, _, _, _, _⟩
  have hrootAbsent : ¬ wholePlaneEdgePresent W (uibhbotRootEdge W) := by
    have hiff := uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
      W H h0 hL hR hfin P₀ hp₀ ha₀ F₀ hf₀ hFim₀ hFa₀ hRpos
      (uibhbotRootEdge W, false)
    exact hiff.mp hrootMissing
  let P := uibhbotD39PastCanonicalDrawing W hL hR hfin
  let hp := uibhbotD39PastCanonicalDrawing_pos W hL hR hfin
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin
  let F := uibhbotD39FutureCanonicalDrawing W H h0
  let hf := uibhbotD39FutureCanonicalDrawing_pos W H h0
  let hFim := uibhbotD39FutureCanonicalDrawing_image W H h0
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W H h0
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hcanonicalMissing : M.missing
      (Quotient.mk G.edgeSetoid (uibhbotRootEdge W, false)) := by
    exact (uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      (uibhbotRootEdge W, false)).2 hrootAbsent
  have hmark := uibhbotD39CanonicalRootMark_edge W H h0 hL hR hfin hRpos
  refine ⟨H, h0, hL, hR, hfin, hRpos, e, he, ?_⟩
  change M.missing (uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa).1
  rw [hmark.1]
  exact hcanonicalMissing

/-- Helper toward Definition 3.8 consumers: almost surely the canonical
UIBHBOT assembly is in the complete geometric domain of Definition 3.8. -/
theorem uibhbotCodeLawRel_ae_d39CanonicalGeomDomain :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W),
      e 0 = uibhbotRootEdge W ∧
        D39GeomDomain
          (uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin
            (uibhbotD39PastCanonicalDrawing W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
            (uibhbotD39FutureCanonicalDrawing W H h0)
            (uibhbotD39FutureCanonicalDrawing_pos W H h0)
            (uibhbotD39FutureCanonicalDrawing_image W H h0)
            (uibhbotD39FutureCanonicalDrawing_arcImage W H h0) hRpos)
          (uibhbotAssemblyD39RootMark W H h0 hL hR hfin
            (uibhbotD39PastCanonicalDrawing W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
            (uibhbotD39FutureCanonicalDrawing W H h0)
            (uibhbotD39FutureCanonicalDrawing_pos W H h0)
            (uibhbotD39FutureCanonicalDrawing_image W H h0)
            (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)) := by
  filter_upwards [uibhbotCodeLawRel_ae_d39CanonicalRootValid] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, hRpos, e, he, hrootValid⟩
  let P := uibhbotD39PastCanonicalDrawing W hL hR hfin
  let hp := uibhbotD39PastCanonicalDrawing_pos W hL hR hfin
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin
  let F := uibhbotD39FutureCanonicalDrawing W H h0
  let hf := uibhbotD39FutureCanonicalDrawing_pos W H h0
  let hFim := uibhbotD39FutureCanonicalDrawing_image W H h0
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W H h0
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  refine ⟨H, h0, hL, hR, hfin, hRpos, e, he, ?_⟩
  refine ⟨uibhbotAssemblyD39_connected W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos,
    uibhbotAssemblyD39_locallyFinite W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos,
    ?_⟩
  exact Or.inl hrootValid


end

end DirectedDistances.PaperProofs.Section5
