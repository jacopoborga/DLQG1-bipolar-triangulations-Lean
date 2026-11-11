/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.QuadrantWalk





public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory

/-- Isolated proof provider for corrected Lemma 5.14; packaging only. -/
theorem quadrant_walk_corrected :
    DirectedDistances.PaperProofs.Section5.sourceQuadrantHatPath
        ⟂ᵢ[DirectedDistances.RandomWalk.iidCodeMeasure]
      DirectedDistances.PaperProofs.Section5.sourceQuadrantPrimedPath ∧
    (∀ n, DirectedDistances.RandomWalk.iidCodeMeasure.map (fun ω =>
      fun j : Fin (n + 1) =>
        DirectedDistances.PaperProofs.Section5.sourceQuadrantHatPath ω j.val) =
      ((Measure.uniformOfFinset
        (Finset.univ : Finset (Fin n → Fin 3))).map
        (DirectedDistances.RandomWalk.lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
            ((0 : ℝ) + 1)) else 0)) ∧
    (∀ᵐ ω ∂DirectedDistances.RandomWalk.iidCodeMeasure,
      DirectedDistances.PaperProofs.Section5.sourceQuadrantPrimedPath ω 0 = (0, 0) ∧
        DirectedDistances.PaperProofs.Section5.sourceQuadrantPrimedPath ω 1 = (0, 1)) ∧
    (∀ n, DirectedDistances.RandomWalk.iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
      DirectedDistances.PaperProofs.Section5.sourceQuadrantPrimedPath ω (j.val + 1) -
        DirectedDistances.PaperProofs.Section5.sourceQuadrantPrimedPath ω 1) =
        ((Measure.uniformOfFinset
          (Finset.univ : Finset (Fin n → Fin 3))).map
          (DirectedDistances.RandomWalk.lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).2 then
            ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) /
              ((0 : ℝ) + 1)) else 0)) ∧
    (AEMeasurable DirectedDistances.PaperProofs.Section5.sourceQuadrantHatPath
        DirectedDistances.RandomWalk.iidCodeMeasure ∧
      AEMeasurable DirectedDistances.PaperProofs.Section5.sourceQuadrantPrimedPath
        DirectedDistances.RandomWalk.iidCodeMeasure) :=
by exact DirectedDistances.PaperProofs.Section5.quadrant_walk_corrected

end DirectedDistances.PaperProofs.SourceResults
