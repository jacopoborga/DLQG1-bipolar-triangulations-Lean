/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIQBOTDefinitionProvider
public import DirectedDistances.KMSW.UIQBOTRealizationFaceDegree

/- not installed, not counted.

face of the shared directed map `M` has `faceDegree = 3` (actual neighbourhood multiplicities,
Definition 1.1 "faces all have degree three, except possibly the external face",

The plane realization is now taken from the deterministic
`kmswConstructedPlaneRealization_with_faceDegree` for the same walk hypotheses as the
source/sink carrier, so the stage agreement, unique unbounded face, boundary-dart
characterization and the face-degree clause all refer to one drawing `P`; the directed map `M`
is the carrier's map on that same `P`. Nothing is assumed: no face, degree or law premise. -/

public section

namespace DirectedDistances.PaperProofs.SourceResults

open Filter MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open Quiver
open scoped Classical

/-- not counted: the v1 statement with the internal `faceDegree = 3` clause appended for the same
realization `P` and directed map `M`. -/
theorem def_uiqbot_provider_v2 :
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
                        M.toPlaneGraphDrawing.faceDegree K = 3 := by
  refine ⟨uiqbot_integrated_code_law, ?_⟩
  filter_upwards [uiqbot_ae_general_source_sink_carrier] with ω hcarrier
  let w := pitmanCode (fun i => ω (i + 1))
  rcases hcarrier with ⟨hfin, htrans, hR, hL0, hmap⟩
  obtain ⟨Q, hQ, P, hpos, harc, U, hUb, hUuniq, hBorders, -, -, -, -, hdeg⟩ :=
    kmswConstructedPlaneRealization_with_faceDegree w hfin htrans hR hL0
  have hroot := (uiqbot_carrier.1 w)
  have hleft : ∀ i, P.dartBorders (kmswLeftBoundaryEdge w i, false) U := by
    intro i
    apply (hBorders (kmswLeftBoundaryEdge w i, false)).2
    exact (limitExternalDart_iff w htrans hR hL0 _).2 (Or.inl ⟨i, rfl⟩)
  have hright : ∀ i, P.dartBorders (kmswRightBoundaryEdge w i, true) U := by
    intro i
    apply (hBorders (kmswRightBoundaryEdge w i, true)).2
    exact (limitExternalDart_iff w htrans hR hL0 _).2 (Or.inr ⟨i, rfl⟩)
  have hboundaryChar : ∀ d, P.dartBorders d U ↔
      (∃ i, d = (kmswLeftBoundaryEdge w i, false)) ∨
      (∃ i, d = (kmswRightBoundaryEdge w i, true)) := by
    intro d
    exact (hBorders d).trans (limitExternalDart_iff w htrans hR hL0 d)
  have hleftSucc : ∀ i, kmswInfFaceSucc w hfin (kmswLeftBoundaryEdge w i, false) =
      (kmswLeftBoundaryEdge w (i + 1), false) := by
    intro i
    exact kmswInfFaceSucc_left w hfin (stageOuterWord_faceSucc w) htrans i
  have hrightSucc : ∀ i, kmswInfFaceSucc w hfin
      (kmswRightBoundaryEdge w (i + 1), true) = (kmswRightBoundaryEdge w i, true) := by
    intro i
    exact kmswInfFaceSucc_right w hfin (stageOuterWord_faceSucc w) hL0 hR i
  have hjunction := kmswInfFaceSucc_junction w hfin (stageOuterWord_faceSucc w)
    hL0 htrans hR
  refine ⟨hfin, htrans, hR, hL0, ⟨htrans, hR, hL0⟩, Q, hQ, P, hpos, harc, U, hUb,
    hUuniq, hBorders, hboundaryChar, hmap P, ?_⟩
  dsimp
  have hprops := Classical.choose_spec (Classical.choose_spec (hmap P))
  rcases hprops with ⟨hdraw, hcompat, hac, hpresent, hsource, hunique, hnosink⟩
  refine ⟨hdraw, hcompat, hac, hpresent, hsource, hunique, hnosink, ?_, ?_,
    hleft, hright, hleftSucc, hrightSucc, hjunction, ?_⟩
  · exact (hcompat 0).1 |>.trans hroot.1
  · exact (hcompat 0).2 |>.trans hroot.2
  · rw [hdraw]
    exact hdeg

end DirectedDistances.PaperProofs.SourceResults
