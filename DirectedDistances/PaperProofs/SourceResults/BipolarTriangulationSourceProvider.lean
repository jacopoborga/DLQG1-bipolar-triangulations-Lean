/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapSideDegreeChecks
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport

/- not installed, not counted. It packages the existing acyclicity, bipolarity,
side-degree, and invariance results. The degree notion here is the
compatibility with the side-free face degree remains a separate open
obligation, recorded below with full binders. -/

public section

universe u v

namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

variable {V : Type u} {E : Type v}

/-- not installed, not counted.

It records acyclicity as absence of a nonempty directed cycle, bipolarity as
acyclicity with at most one source and sink, and the side-degree reading of
the triangulation condition. It also gives the acyclic-binder form and the
proved invariances under orientation-preserving directed homeomorphisms and
endpoint-storage swaps. -/
theorem def_bipolar_triangulation_provider :
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
        M.IsBipolarTriangulationBySides)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M
    exact ⟨M.isAcyclic_iff, M.isBipolar_iff, Iff.rfl⟩
  · intro M _hA
    constructor
    · rintro ⟨⟨_, hSource, hSink⟩, hDegree⟩
      exact ⟨hSource, hSink, hDegree⟩
    · rintro ⟨hSource, hSink, hDegree⟩
      exact ⟨⟨_hA, hSource, hSink⟩, hDegree⟩
  · intro V' E' M M' _e
    exact ⟨_e.toHomeoEquiv.isAcyclic_map_iff,
      _e.toHomeoEquiv.isBipolar_map_iff,
      _e.isBipolarTriangulationBySides_iff⟩
  · intro M swap
    exact ⟨DirectedPlaneMap.endpointSwap_isAcyclic_iff M swap,
      DirectedPlaneMap.endpointSwap_isBipolar_iff M swap,
      endpointSwap_isBipolarTriangulationBySides_iff M swap⟩















end DirectedDistances.PaperProofs.SourceResults

end
