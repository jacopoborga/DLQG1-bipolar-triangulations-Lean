/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Final

/-! # Lemma 5.5 (`lem-geo-infty-ind`) — isolated source provider


For every `x : XDP` and every boundary index `k : ℤ`, the left and right side submaps of the
infinite cut geodesic from `x_k` are observed as optional marked classes
(`lemma55LeftSideClassOption`, `lemma55RightSideClassOption2`). The provider states:
both observables are almost surely present (so the arbitrary `default` class is irrelevant);
after forgetting the boundary and seam marks (`forgetMarksOptionClassValue`, ROOT ruling of
2026-11-06 on d319: the source asserts ordinary side-submap laws), the two sides are
independent; the right-side law is the same for all `k ≥ 0`; the left-side law is the same for
all `k ≤ 0`. All clauses are conclusions; there are no hypotheses beyond the default class. -/

public section

namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.Paper.Section4

/-- provider: almost-sure presence of both side observables, independence of the unmarked left and
right side submap classes, and the two half-index law clauses. -/
theorem lem_geo_infty_ind_source_provider (default : GeometricSideClass) :
    ∀ (x : XDP) (k : ℤ),
      (lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W))) ∧
      (lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x k W))) ∧
      IndepFun
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k)
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k →
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x 0)) ∧
      (k ≤ 0 →
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x 0)) := by
  intro x k
  obtain ⟨hL, hR, -, -, -⟩ := lemma55_marked_sides default x k
  exact ⟨hL, hR, lemma55_unmarked_sides default x k⟩

end DirectedDistances.PaperProofs.SourceResults
