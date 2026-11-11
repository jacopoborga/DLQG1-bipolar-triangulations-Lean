 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BusemannUIBHBOT

/-!
# Proposition 5.11 (`prop-busemann-uihbot`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/
















public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5 DirectedDistances.PaperProofs.Section7



theorem prop_busemann_uihbot :
    (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      (∀ k : ℤ, IsLeast {t : ℤ | (wholePlaneWordIntegral W t).1 = k}
        (uibhbotBoundaryHitTime k W)) ∧
      uibhbotBoundaryHitTime 0 W = 0 ∧
      StrictAnti (fun k : ℤ => uibhbotBoundaryHitTime k W) ∧
      ∃ e : ℤ → WholePlaneEdge W,
        (∀ k : ℤ,
          wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k) ∧
          ∃ N n : ℕ, 0 < n ∧ (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
            e k = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n)) ∧
        Function.Injective e ∧ e 0 = uibhbotRootEdge W) ∧
    (∃ X : (ℤ → Fin 3) → ℤ → ℤ,
      (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        IsUIBHBOTBusemannLDP W (X W) ∧
          ∀ Y : ℤ → ℤ, IsUIBHBOTBusemannLDP W Y → Y = X W) ∧
      iIndepFun (fun k W => X W k - X W (k - 1))
        (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) ∧
      ∀ k : ℤ, IdentDistrib (fun W => X W k - X W (k - 1))
        (fun W => identifiedLDPBusemann W 0 - identifiedLDPBusemann W (0 - 1))
        (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) wholePlaneIIDCodeMeasure) ∧
    (∃ X : (ℤ → Fin 3) → ℤ → ℤ,
      (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        IsUIBHBOTBusemannSDP W (X W) ∧
          ∀ Y : ℤ → ℤ, IsUIBHBOTBusemannSDP W Y → Y = X W) ∧
      iIndepFun (fun k W => X W k - X W (k - 1))
        (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) ∧
      ∀ k : ℤ, IdentDistrib (fun W => X W k - X W (k - 1))
        (fun W => identifiedSDPBusemann W 0 - identifiedSDPBusemann W (0 - 1))
        (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) wholePlaneIIDCodeMeasure) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.prop_busemann_uihbot_provider
 
 

end DirectedDistances.Paper.Section5
 
