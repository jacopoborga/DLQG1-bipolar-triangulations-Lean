/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierSection7b
public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierSection7
public import DirectedDistances.PaperProofs.Section3.UIBOTSourceStatementPart2






















public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

local instance uibotLawStatementsSection7MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotLawStatementsSection7BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: the exact UIBOT probability law in the
source statement has the installed measurable whole-plane class pushforward
as its underlying measure. No local-limit identification is a premise. -/
theorem uibotLawSection7_eq_map :
    (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0}) =
      wholePlaneIIDCodeMeasure.map uibotSection7ClassMap := rfl

/-- Helper toward Proposition 3.9: Borel predicates on classes hold almost
surely under the UIBOT law exactly when their measurable class pullbacks do.
The sole hypothesis is measurability, not the predicate's truth. -/
theorem uibotLawSection7_ae_iff
    (P : D39GeomRootedMapClass.{0} → Prop) (hP : MeasurableSet {x | P x}) :
    let μ := uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved
    (∀ᵐ x ∂(μ : Measure D39GeomRootedMapClass.{0}), P x) ↔
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure, P (uibotSection7ClassMap W) := by
  change (∀ᵐ x ∂wholePlaneIIDCodeMeasure.map uibotSection7ClassMap, P x) ↔ _
  exact ae_map_iff
    (measurable_uibotMeasurableWholePlaneClassMap
      uibotDeterministicComparison_proved).aemeasurable hP

/-- Helper toward Proposition 3.9: the common Section 7 certificate is
Borel and conull under the exact UIBOT law, by the measurable class map. -/
theorem uibotLawSection7_certificate :
    let μ := uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved
    MeasurableSet {x | uibotSection7bCertificate x} ∧
      ∀ᵐ x ∂(μ : Measure D39GeomRootedMapClass.{0}), uibotSection7bCertificate x := by
  refine ⟨measurableSet_uibotSection7bCertificate, ?_⟩
  apply (uibotLawSection7_ae_iff _ measurableSet_uibotSection7bCertificate).mpr
  filter_upwards [uibotSection7b_transport_ae] with W hW
  exact hW.2.2

/-- Helper toward Proposition 3.9: the recovered code and both complete
integer-indexed Busemann sequences used by all four law statements are Borel. -/
theorem uibotLawSection7_measurable :
    Measurable uibotRecoveredCode ∧
    Measurable (fun x => (uibotGeomBusemannObservables x).1.1) ∧
    Measurable (fun x => (uibotGeomBusemannObservables x).1.2) :=
  ⟨uibotSection7b_measurable.1, uibotSection7b_measurable.2.1,
    uibotSection7b_measurable.2.2.1⟩

/-- Helper toward Proposition 3.9: all finite-window events of either
fixed Borel sequence are Borel, with exactly the code probability under
the UIBOT law. The statement includes every size, threshold and exponent. -/
theorem uibotLawSection7_window (longest : Bool) (k : ℕ) (A p : ℝ) :
    let μ := uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved
    MeasurableSet {x : D39GeomRootedMapClass.{0} | ∀ l : ℤ,
      -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then (uibotGeomBusemannObservables x).1.1
        else (uibotGeomBusemannObservables x).1.2) l : ℝ)| ≤ A * (k : ℝ) ^ p} ∧
    (μ : Measure D39GeomRootedMapClass.{0}).real {x | ∀ l : ℤ,
      -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then (uibotGeomBusemannObservables x).1.1
        else (uibotGeomBusemannObservables x).1.2) l : ℝ)| ≤ A * (k : ℝ) ^ p} =
    wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ,
      -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then identifiedLDPBusemann W
        else identifiedSDPBusemann W) l : ℝ)| ≤ A * (k : ℝ) ^ p} :=
  uibotSection7b_window_transport longest k A p





theorem uibotLawSection7_longPath :
    let μ := uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved
    ∀ᵐ x ∂(μ : Measure D39GeomRootedMapClass.{0}),
      uibotSection7LongPathProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.1 :=
  uibotSection7b_longPath_transport





theorem uibotLawSection7_ldpFluctuation :
    let μ := uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved
    (∀ᵐ x ∂(μ : Measure D39GeomRootedMapClass.{0}),
      uibotSection7LDPCutProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.1) ∧
    (∀ k : ℕ, ∀ A : ℝ,
      MeasurableSet {x : D39GeomRootedMapClass.{0} | ∀ l : ℤ,
        -(k : ℤ) ≤ l → l ≤ k →
        |((uibotGeomBusemannObservables x).1.1 l : ℝ)| ≤
          A * (k : ℝ) ^ (3 / 2 : ℝ)}) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        (μ : Measure D39GeomRootedMapClass.{0}).real {x | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |((uibotGeomBusemannObservables x).1.1 l : ℝ)| ≤
            A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  refine ⟨uibotSection7b_ldpCut_transport, ?_, uibotSection7b_ldpFluctuation_transport⟩
  · intro k A
    exact (uibotLawSection7_window true k A (3 / 2)).1





theorem uibotLawSection7_sdpTri :
    let μ := uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved
    ∀ᵐ x ∂(μ : Measure D39GeomRootedMapClass.{0}),
      uibotSection7SDPTriProperty (uibotRecoveredCode x) :=
  uibotSection7b_sdpTri_transport





theorem uibotLawSection7_sdpFluctuation :
    let μ := uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved
    (∀ᵐ x ∂(μ : Measure D39GeomRootedMapClass.{0}),
      uibotSection7SDPCutProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.2) ∧
    (∀ k : ℕ, ∀ A : ℝ,
      MeasurableSet {x : D39GeomRootedMapClass.{0} | ∀ l : ℤ,
        -(k : ℤ) ≤ l → l ≤ k →
        |((uibotGeomBusemannObservables x).1.2 l : ℝ)| ≤
          A * (k : ℝ) ^ (3 / 4 : ℝ)}) ∧
    ∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
        1 - delta ≤ (μ : Measure D39GeomRootedMapClass.{0}).real {x | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |((uibotGeomBusemannObservables x).1.2 l : ℝ)| ≤
            A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  refine ⟨uibotSection7b_sdpCut_transport, ?_, uibotSection7b_sdpFluctuation_transport⟩
  · intro k A
    exact (uibotLawSection7_window false k A (3 / 4)).1

/-- Helper toward Proposition 3.9: all four transported consumers under
the UIBOT law share one cut, with the complete edge and distance
identifications, both fixed sequences, stopped-stage paths, unique SDP
Busemann characterization, reachability and finiteness retained together.
The intrinsic geometric qualifier is not removed. -/
theorem uibotLawSection7_sharedCut :
    let μ := uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved
    ∀ᵐ x ∂(μ : Measure D39GeomRootedMapClass.{0}),
    let W := uibotRecoveredCode x
    let L := (uibotGeomBusemannObservables x).1.1
    let S := (uibotGeomBusemannObservables x).1.2
    ∃ H : WholePlaneRotationHypothesis W,
    ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
    ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
    let w := shiftedStream W 0
    let V := wholePlaneVertexι W 0
    let E := wholePlaneEdgeι W 0
    let D := m0CutData W H h hLL
    (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ j, D.x j = V (boundaryVertex w h j)) ∧
      (D.rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        D.rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W D.rootDart.1 = D.x 0 ∧
        wholePlaneEdgeEast W D.rootDart.1 = D.x 1 ∧
        wholePlaneEdgePresent W D.rootDart.1 ∧ D.tail D.rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ j : ℤ, j ≤ -1 ∧ e = boundaryOuterEdge w h j)) ∧
      (∀ e, D.missing (E e) ↔
        ∃ j : ℤ, j ≤ -1 ∧ e = boundaryOuterEdge w h j) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, D.sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, D.ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ j j', D.sdp (D.x j) (D.x j') =
        DirectedDistances.sdp (boundaryPresentVertex w h j) (boundaryPresentVertex w h j')) ∧
      (∀ j j', D.ldp (D.x j) (D.x j') =
        presentLdp (boundaryPresentVertex w h j) (boundaryPresentVertex w h j'))) ∧
    IsIdentifiedM0BusemannLDP D L ∧
    IsIdentifiedM0BusemannSDP D S ∧
    (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
    (∀ ell k : ℕ, 1 ≤ ell → ell < k →
      let n := boundaryHitTime w h (-(k : ℤ))
      ∃ (N : ℕ) (p : Fin (N + 1) → WholePlaneVertex W),
        (∀ i : Fin N, m0CutDirectedStep W H D.seam (p i.castSucc) (p i.succ)) ∧
        IdentifiedStagePath W V n N p ∧
        (max (L (-(ell : ℤ)) - L (-(k : ℤ))) 0).toNat ≤ N) ∧
    ∀ X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X →
      ∀ l k : ℤ, 0 ≤ l → l < k →
        m0CutReachable W H D.seam (D.x l) (D.x k) ∧
        D.sdp (D.x l) (D.x k) ≠ ⊤ ∧
        X l - X k ≤ ((D.sdp (D.x l) (D.x k)).toNat : ℤ) :=
  uibotSection7b_sharedCut_transport

end DirectedDistances.PaperProofs.Section3
end
