/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Reduction
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55LeftObservable
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly8
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55RightObservable

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: the slice class option is present almost surely
at every fixed boundary index. -/
theorem ae_m0CutGeodesicSliceClassOption_isSome (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (m0CutGeodesicSliceClassOption x k W).isSome := by
  filter_upwards [ae_m0CutGeodesicSliceWitness x] with W hW
  simp [m0CutGeodesicSliceClassOption, hW]


















































end DirectedDistances.PaperProofs.Section5
