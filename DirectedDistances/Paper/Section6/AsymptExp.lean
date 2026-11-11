 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.Section6Laws

/-!
# Proposition 6.8 (`prop:asympt-exp`)

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

open DirectedDistances.Recursive.SDPExpansion

local notation "f" => incrementLawsIdentified_sdpF
local notation "g" => incrementLawsIdentified_sdpG

 
theorem prop_asympt_exp :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, k < -1 → g k = 0) ∧
    (let kappa : ℝ := 3 - 6 * g (-1) ^ 2 - f 0
    let b : ℝ := g (-1) ^ (2 / 3 : ℝ)
    let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2
    let dMinus : ℂ := ((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2
    kappa = 0 ∧ 0 < g (-1) ∧
      ((fun t : ℝ => SDPExpansion.integerCF f t -
        ((1 : ℂ) - (b : ℂ) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) ∧
      ((fun t : ℝ => SDPExpansion.negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) +
        (((2 * g (-1) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ) -
        (dPlus * (b : ℂ)) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ))) ∧
      ((fun t : ℝ => sdpCF g t - 1 -
        (dMinus * (b : ℂ)) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ)))) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.prop_asympt_exp_provider
 
 

end DirectedDistances.Paper.Section6
 
