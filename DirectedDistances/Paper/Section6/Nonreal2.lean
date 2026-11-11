 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.Section6Laws

/-!
# Lemma 6.7 (`lem:nonreal2`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/














public section
namespace DirectedDistances.Paper.Section6

open MeasureTheory Filter Asymptotics
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7
open DirectedDistances.PaperProofs.Section6
open scoped Topology

local notation "f" => incrementLawsIdentified_ldpF
local notation "g" => incrementLawsIdentified_ldpG
local notation "hat" =>
  SDPExpansion.sdpHat incrementLawsIdentified_sdpF incrementLawsIdentified_sdpG
local notation "cf" => SDPExpansion.integerCF incrementLawsIdentified_sdpF

 
theorem lem_nonreal2 :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL)
          (identifiedLDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, 0 ≤ k → g k = 0) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ incrementLawsIdentified_sdpF k) ∧
    HasSum incrementLawsIdentified_sdpF 1 ∧
    (∀ k : ℤ, 0 ≤ incrementLawsIdentified_sdpG k) ∧
    HasSum incrementLawsIdentified_sdpG 1 ∧
    (∀ k : ℤ, k < -1 → incrementLawsIdentified_sdpG k = 0) ∧
    (∃ delta : ℝ, 0 < delta ∧
       (∀ t ∈ Set.Ioo 0 delta,
         let F := (integerCF incrementLawsIdentified_ldpF t).re
         (integerCF incrementLawsIdentified_ldpF t).im = 0 ∧
         (3 * F - 1) ^ 2 - 4 * F ^ 3 < 0 ∧
           ∀ z : ℂ, (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + F = 0 →
             z.im ≠ 0) ∧
       ContinuousOn (ldpHat incrementLawsIdentified_ldpF) (Set.Ioo 0 delta) ∧
       (∀ t ∈ Set.Ioo 0 delta,
         let F := (integerCF incrementLawsIdentified_ldpF t).re
         (F : ℂ) ^ 2 * (ldpHat incrementLawsIdentified_ldpF t) ^ 2 +
           (3 * (F : ℂ) - 1) * ldpHat incrementLawsIdentified_ldpF t + F = 0) ∧
       (∀ t ∈ Set.Ioo 0 delta, (ldpHat incrementLawsIdentified_ldpF t).im ≠ 0) ∧
       (∀ alpha beta : ℝ → ℝ,
         ContinuousOn alpha (Set.Ioo 0 delta) → ContinuousOn beta (Set.Ioo 0 delta) →
         (∀ s ∈ Set.Ioo 0 delta,
           let F := (integerCF incrementLawsIdentified_ldpF s).re
           (F : ℂ) ^ 2 * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) ^ 2 +
             (3 * (F : ℂ) - 1) * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) + F = 0) →
         ∀ s ∈ Set.Ioo 0 delta, beta s ≠ 0)) ∧
    (∃ delta : ℝ, 0 < delta ∧
       (∀ t ∈ Set.Ioo 0 delta,
         let F := (cf t).re
         (cf t).im = 0 ∧
         (3 * F - 1) ^ 2 - 4 * F ^ 3 < 0 ∧
           ∀ z : ℂ, (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + F = 0 →
             z.im ≠ 0) ∧
       ContinuousOn hat (Set.Ioo 0 delta) ∧
       (∀ t ∈ Set.Ioo 0 delta,
         let F := (cf t).re
         (F : ℂ) ^ 2 * (hat t) ^ 2 + (3 * (F : ℂ) - 1) * hat t + F = 0) ∧
       (∀ t ∈ Set.Ioo 0 delta, (hat t).im ≠ 0) ∧
       (∀ alpha beta : ℝ → ℝ,
         ContinuousOn alpha (Set.Ioo 0 delta) → ContinuousOn beta (Set.Ioo 0 delta) →
         (∀ s ∈ Set.Ioo 0 delta,
           let F := (cf s).re
           (F : ℂ) ^ 2 * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) ^ 2 +
             (3 * (F : ℂ) - 1) * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) + F = 0) →
         ∀ s ∈ Set.Ioo 0 delta, beta s ≠ 0)) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_nonreal2_provider
 
 

end DirectedDistances.Paper.Section6
 
