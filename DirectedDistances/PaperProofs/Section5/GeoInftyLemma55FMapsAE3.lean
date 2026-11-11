/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE2

/-! Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.5. The nonpositive R-minus class reader is present
almost surely, so its presence indicator is a.e. measurable under the observed
presentation law. -/
theorem aemeasurable_RMinusSidePresentation_classOption_isSome
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable
      (fun W => (RMinusSidePresentation.classOption
        (decodeRMinus x k (rightSideObsNonpos x k W))).isSome)
      wholePlaneIIDCodeMeasure := by
  refine ⟨fun _ => true, measurable_const, ?_⟩
  change ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
    (RMinusSidePresentation.classOption
      (decodeRMinus x k (rightSideObsNonpos x k W))).isSome = true
  exact ae_decodeRMinus_rightSideObsNonpos_classOption_isSome x k hk








































end DirectedDistances.PaperProofs.Section5
