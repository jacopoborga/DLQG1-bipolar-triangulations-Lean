/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE3
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly3
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55LeftLawClause

 

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk

/-- Helper toward Lemma 5.5. The actual right optional class reader is present
almost surely at each nonnegative boundary index. -/
theorem ae_lemma55RightSideClassOption_isSome_nonnegative
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (lemma55RightSideClassOption x k W).isSome := by
  cases x with
  | ldp =>
      filter_upwards
        [m0RightSideClassOption_ae_eq_RPlusPresentationClass true k hk,
          (boundaryFutureThinSides_package XDP.ldp k).2.2.2.2.2]
        with W heq hcoherent
      change (m0RightSideClassOption true k W).isSome
      rw [heq]
      have hreal := decodeRPlus_rightSideObsNonneg_realization_isSome
        XDP.ldp k W hcoherent
      simp [hreal]
  | sdp =>
      filter_upwards
        [m0RightSideClassOption_ae_eq_RPlusPresentationClass false k hk,
          (boundaryFutureThinSides_package XDP.sdp k).2.2.2.2.2]
        with W heq hcoherent
      change (m0RightSideClassOption false k W).isSome
      rw [heq]
      have hreal := decodeRPlus_rightSideObsNonneg_realization_isSome
        XDP.sdp k W hcoherent
      simp [hreal]















































end DirectedDistances.PaperProofs.Section5
