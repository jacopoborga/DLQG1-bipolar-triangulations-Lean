/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIQBOTGeneralCarrierVertices
public import DirectedDistances.KMSW.UIQBOTPlaneRealization
public import DirectedDistances.KMSW.KMSWConstructedGeometricEdgeEquiv
public import DirectedDistances.PaperProofs.Section4.UIQBOTCarrier
public import DirectedDistances.PaperProofs.Section4.UIQBOTIntegratedCodeLaw

/- not installed, not counted.

Represented source clauses:
* Lines 1–12: the integrated Pitman code path has law
  `conditionedVectorPathLaw 0 0`, including its finite-horizon conditioned-walk
  Radon–Nikodym description.
* Lines 14–18: the KMSW limit has a stage-compatible plane realization.
* Lines 18–21: on the same realization, the directed map has its KMSW edge
  endpoints, an acyclic orientation, unique source at vertex zero, no sink,
  and every geometric edge is present.
* Lines 22–24: one unique unbounded face has exactly the `limitExternalDart`
  darts; the left and right boundary edge chains lie on that face and follow
  the stated face-successor order. The root is KMSW edge zero, directed from
  vertex zero to vertex one.

Not represented: a measurable random variable with values in a homeomorphism
quotient and its map-valued pushforward law. Externality follows the recorded ruling Q-EXT-FACE in
statement is needed for this representation-level provider:
homeomorphism invariance sufficed for Definition 3.1 there. This provider makes
no claim that it proves the whole paper's UIQBOT map-law interpretation.

All map clauses use the same `P`, `M`, and `iota`. The realization witness
and the source/sink carrier witness are combined by proof irrelevance of their
proposition-valued walk hypotheses, not by assuming either result. -/

public section

namespace DirectedDistances.PaperProofs.SourceResults

open Filter MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open Quiver
open scoped Classical

/-- not installed and not counted. The code law and all geometric/orientation
clauses are stated on their source carriers with one shared realization and
one shared directed map. -/
theorem def_uiqbot_provider :
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
                        (kmswLeftBoundaryEdge w 0, false) := by
  refine ⟨uiqbot_integrated_code_law, ?_⟩
  filter_upwards [uiqbot_ae_general_source_sink_carrier,
    uiqbot_ae_constructed_plane_realization] with ω hcarrier hreal
  let w := pitmanCode (fun i => ω (i + 1))
  rcases hcarrier with ⟨hfin, htrans, hR, hL0, hmap⟩
  rcases hreal with ⟨hfin', htrans', hR', hL0', hreal⟩
  have hreal' : KMSWConstructedPlaneRealizationStatement w hfin htrans hR hL0 := by
    exact hreal
  dsimp [KMSWConstructedPlaneRealizationStatement] at hreal'
  rcases hreal' with ⟨Q, hQ, P, hpos, harc, U, hUb, hUuniq, hBorders⟩
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
    hleft, hright, hleftSucc, hrightSucc, hjunction⟩
  · exact (hcompat 0).1 |>.trans hroot.1
  · exact (hcompat 0).2 |>.trans hroot.2


end DirectedDistances.PaperProofs.SourceResults
