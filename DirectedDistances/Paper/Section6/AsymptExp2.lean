 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.Section6Laws

/-!
# Proposition 6.2 (`prop:asympt-exp2`)

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

 
theorem prop_asympt_exp2 :
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
    (let kappa : ℝ := 3 + f 0
    let a : ℝ := (kappa / 2) ^ (1 / 3 : ℝ)
    let d : ℂ := ((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2
    0 < kappa ∧
      ((fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (a : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) ∧
      ((fun t : ℝ => negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) -
        (d * (a : ℂ)) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ))) ∧
      ((fun t : ℝ => negativeCF g t - 1 -
        (d * (a : ℂ)) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)))) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.prop_asympt_exp2_provider
 
 

end DirectedDistances.Paper.Section6
 
