 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.Section6Laws

/-!
# Lemma 6.6 (`lem:Y-not-const`)

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

 
theorem lem_y_not_const :
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
    ((∀ c : ℤ, f c < 1) ∧ 0 < f 0) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_y_not_const_provider
 
 

end DirectedDistances.Paper.Section6
 
