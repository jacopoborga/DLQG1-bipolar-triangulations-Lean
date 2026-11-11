 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BipolarTriangulationSourceProvider

/-!
# Definition 1.1 (`def-bipolar`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/

















public section
namespace DirectedDistances.Paper.Section1

open DirectedDistances.PlanarMap

universe u v

 
theorem def_bipolar {V : Type u} {E : Type v} :
    (∀ M : DirectedPlaneMap V E,
      (M.IsAcyclic ↔ ∀ v, ¬ Relation.TransGen M.step v v) ∧
      (M.IsBipolar ↔
        M.IsAcyclic ∧ Subsingleton {v : V // M.IsSource v} ∧
          Subsingleton {v : V // M.IsSink v}) ∧
      (M.IsBipolarTriangulationBySides ↔
        M.IsBipolar ∧ ∀ F : M.toPlaneGraphDrawing.Face,
          M.toPlaneGraphDrawing.IsInternal F →
            M.toPlaneGraphDrawing.sideDegree F = 3)) ∧
    (∀ (M : DirectedPlaneMap V E) (_hA : M.IsAcyclic),
      M.IsBipolarTriangulationBySides ↔
        (Subsingleton {v : V // M.IsSource v} ∧
          Subsingleton {v : V // M.IsSink v} ∧
          ∀ F : M.toPlaneGraphDrawing.Face,
            M.toPlaneGraphDrawing.IsInternal F →
              M.toPlaneGraphDrawing.sideDegree F = 3)) ∧
    (∀ {V' : Type u} {E' : Type v}
      {M : DirectedPlaneMap V E} {M' : DirectedPlaneMap V' E'}
      (_e : DirectedPlaneMap.OrientedHomeoEquiv M M'),
      (M.IsAcyclic ↔ M'.IsAcyclic) ∧
      (M.IsBipolar ↔ M'.IsBipolar) ∧
      (M.IsBipolarTriangulationBySides ↔
        M'.IsBipolarTriangulationBySides)) ∧
    (∀ (M : DirectedPlaneMap V E) (swap : E → Bool),
      ((M.endpointSwap swap).IsAcyclic ↔ M.IsAcyclic) ∧
      ((M.endpointSwap swap).IsBipolar ↔ M.IsBipolar) ∧
      ((M.endpointSwap swap).IsBipolarTriangulationBySides ↔
        M.IsBipolarTriangulationBySides)) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_bipolar_triangulation_provider
 
 

end DirectedDistances.Paper.Section1
 
