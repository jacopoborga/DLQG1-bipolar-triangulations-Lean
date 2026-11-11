 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.GeoInftyIndLemma55Provider

/-!
# Lemma 5.5 (`lem-geo-infty-ind`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/

















public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.Paper.Section4

 
theorem lem_geo_infty_ind (default : GeometricSideClass) :
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
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x 0)) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_geo_infty_ind_source_provider default
 
 

end DirectedDistances.Paper.Section5
 
