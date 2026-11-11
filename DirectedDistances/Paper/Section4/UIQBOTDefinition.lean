 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIQBOTDefinitionV2

/-!
# Definition 4.1 (`def-uiqbot`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/


















public section
namespace DirectedDistances.Paper.Section4

open Filter MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open Quiver
open scoped Classical

 
theorem def_uiqbot :
    iidCodeMeasure.map
        (fun ω => integrateCodes (pitmanCode (fun i => ω (i + 1)))) =
      conditionedVectorPathLaw 0 0 ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∃ htrans : Tendsto (L w) atTop atTop,
          ∃ hR : ∀ a : ℤ, ∃ n, R w n ≤ a,
            ∃ hL0 : ∀ j, 0 ≤ L w j,
              (Tendsto (L w) atTop atTop ∧
                (∀ a : ℤ, ∃ n, R w n ≤ a) ∧ (∀ j, 0 ≤ L w j)) ∧
                ∃ Q : ∀ n, StageDrawing w n,
                  (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
                  ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
                    (kmswInfRot w hfin) (kmswLimitDartVertex w),
                    (∀ n v, P.pos v.val = (Q n).pos v) ∧
                    (∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d) ∧
                    ∃ U : P.Face,
                      P.IsUnbounded U ∧
                      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
                      (∀ d, P.dartBorders d U ↔ limitExternalDart w d) ∧
                      (∀ d, P.dartBorders d U ↔
                        (∃ i, d = (kmswLeftBoundaryEdge w i, false)) ∨
                        (∃ i, d = (kmswRightBoundaryEdge w i, true))) ∧
                      ∃ hmapP : ∃ M : DirectedPlaneMap ℕ P.GeometricEdge,
                        ∃ iota : ℕ ≃ P.GeometricEdge,
                          M.toPlaneGraphDrawing = P.toPlaneGraphDrawing ∧
                          (∀ e, M.tail (iota e) = edgeWest w e ∧
                            M.head (iota e) = edgeEast w e) ∧
                          M.IsAcyclic ∧
                          (∀ q : P.GeometricEdge, ∃ e, iota e = q ∧ EdgePresent w e) ∧
                          M.IsSource 0 ∧ (∀ v, M.IsSource v → v = 0) ∧
                          ∀ v, ¬ M.IsSink v,
                      let M := Classical.choose hmapP
                      let iota := Classical.choose (Classical.choose_spec hmapP)
                      M.toPlaneGraphDrawing = P.toPlaneGraphDrawing ∧
                      (∀ e, M.tail (iota e) = edgeWest w e ∧
                        M.head (iota e) = edgeEast w e) ∧
                      M.IsAcyclic ∧
                      (∀ q : P.GeometricEdge, ∃ e, iota e = q ∧ EdgePresent w e) ∧
                      M.IsSource 0 ∧ (∀ v, M.IsSource v → v = 0) ∧
                      (∀ v, ¬ M.IsSink v) ∧
                      M.tail (iota 0) = 0 ∧ M.head (iota 0) = 1 ∧
                      (∀ i, P.dartBorders (kmswLeftBoundaryEdge w i, false) U) ∧
                      (∀ i, P.dartBorders (kmswRightBoundaryEdge w i, true) U) ∧
                      (∀ i, kmswInfFaceSucc w hfin (kmswLeftBoundaryEdge w i, false) =
                        (kmswLeftBoundaryEdge w (i + 1), false)) ∧
                      (∀ i, kmswInfFaceSucc w hfin
                        (kmswRightBoundaryEdge w (i + 1), true) =
                        (kmswRightBoundaryEdge w i, true)) ∧
                      kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w 0, true) =
                        (kmswLeftBoundaryEdge w 0, false) ∧
                      ∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsInternal K →
                        M.toPlaneGraphDrawing.faceDegree K = 3 :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_uiqbot_provider_v2
 
 

end DirectedDistances.Paper.Section4
 
