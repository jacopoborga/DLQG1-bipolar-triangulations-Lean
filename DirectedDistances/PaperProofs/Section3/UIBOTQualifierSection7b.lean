/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierSection7
public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart8

/- # Common Borel observables for the Section 7 consumers

104–111,233–238,287–292`. This module continues the transported forms of
The common certificate is proved conull from the installed anchors, and
the joint shared-cut conclusion and probability bounds have no additional
premises. This does not remove the geometric qualifier. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

local instance uibotQualifierSection7bMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotQualifierSection7bBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

private def completeProperty (x : D39GeomRootedMapClass.{0}) : Prop :=
  uibotSection7LongPathProperty (uibotRecoveredCode x)
      (uibotGeomBusemannObservables x).1.1 ∧
  uibotSection7LDPCutProperty (uibotRecoveredCode x)
      (uibotGeomBusemannObservables x).1.1 ∧
  uibotSection7SDPTriProperty (uibotRecoveredCode x) ∧
  uibotSection7SDPCutProperty (uibotRecoveredCode x)
      (uibotGeomBusemannObservables x).1.2

private theorem completeProperty_ae :
    ∀ᵐ x ∂uibotSection7GeometricLaw, completeProperty x := by
  let B := aemeasurable_uibotCodeBusemannObservables.mk uibotCodeBusemannObservables
  let Q := fun W =>
    uibotSection7LongPathProperty W (B W).1.1 ∧
    uibotSection7LDPCutProperty W (B W).1.1 ∧
    uibotSection7SDPTriProperty W ∧
    uibotSection7SDPCutProperty W (B W).1.2
  have hi : uibotSection7GeometricLaw.map uibotRecoveredCode = wholePlaneIIDCodeMeasure := by
    rw [Measure.map_map measurable_uibotRecoveredCode
      (measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)]
    exact (Measure.map_congr uibotRecoveredCode_ae).trans Measure.map_id
  have hQ : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, Q W := by
    filter_upwards [DirectedDistances.Paper.Section7.lem_long_path,
      DirectedDistances.Paper.Section7.lem_ldp_fluctuation.1,
      DirectedDistances.Paper.Section7.lem_sdp_tri,
      DirectedDistances.Paper.Section7.lem_sdp_fluctuation.1,
      aemeasurable_uibotCodeBusemannObservables.ae_eq_mk]
      with W h1 h3 h5 h7 heq
    have hL := congrArg (fun B => B.1.1) heq
    have hS := congrArg (fun B => B.1.2) heq
    change identifiedLDPBusemann W = (B W).1.1 at hL
    change identifiedSDPBusemann W = (B W).1.2 at hS
    change uibotSection7LongPathProperty _ _ ∧ uibotSection7LDPCutProperty _ _ ∧
      uibotSection7SDPTriProperty _ ∧ uibotSection7SDPCutProperty _ _
    rw [← hL, ← hS]
    exact ⟨h1, h3, h5, h7⟩
  rw [← hi] at hQ
  exact ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable hQ

/- Helper toward Proposition 3.9: one Borel certificate for the four
joint Busemann observable. Its complement is a measurable null hull. -/
@[expose] def uibotSection7bCertificate (x : D39GeomRootedMapClass.{0}) : Prop :=
  x ∉ toMeasurable uibotSection7GeometricLaw {y | ¬ (
    uibotSection7LongPathProperty (uibotRecoveredCode y)
      (uibotGeomBusemannObservables y).1.1 ∧
    uibotSection7LDPCutProperty (uibotRecoveredCode y)
      (uibotGeomBusemannObservables y).1.1 ∧
    uibotSection7SDPTriProperty (uibotRecoveredCode y) ∧
    uibotSection7SDPCutProperty (uibotRecoveredCode y)
      (uibotGeomBusemannObservables y).1.2)}

/-- Helper toward Proposition 3.9: the common Section 7 certificate is Borel. -/
theorem measurableSet_uibotSection7bCertificate :
    MeasurableSet {x | uibotSection7bCertificate x} :=
  (measurableSet_toMeasurable _ _).compl

/-- Helper toward Proposition 3.9: the common certificate holds on one
event of full geometric pushforward measure. -/
theorem uibotSection7bCertificate_ae :
    ∀ᵐ x ∂uibotSection7GeometricLaw, uibotSection7bCertificate x := by
  rw [ae_iff]
  simp only [uibotSection7bCertificate, not_not]
  change uibotSection7GeometricLaw
    (toMeasurable uibotSection7GeometricLaw {y | ¬ completeProperty y}) = 0
  rw [measure_toMeasurable]
  exact ae_iff.mp completeProperty_ae

/-- Helper toward Proposition 3.9: one measurable conull set supports all
four consumers on the same recovered code and fixed joint Busemann observable. -/
theorem uibotSection7b_consumers_conull :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      uibotSection7GeometricLaw Sᶜ = 0 ∧ ∀ x ∈ S,
      uibotSection7LongPathProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.1 ∧
      uibotSection7LDPCutProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.1 ∧
      uibotSection7SDPTriProperty (uibotRecoveredCode x) ∧
      uibotSection7SDPCutProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.2 := by
  refine ⟨{x | uibotSection7bCertificate x},
    measurableSet_uibotSection7bCertificate, ae_iff.mp uibotSection7bCertificate_ae, ?_⟩
  intro x hx
  change uibotSection7bCertificate x at hx
  change completeProperty x
  by_contra hn
  exact hx (subset_toMeasurable uibotSection7GeometricLaw {y | ¬ completeProperty y} hn)

/-- Helper toward Proposition 3.9: Lemma 7.1 uses the same fixed Borel
LDP sequence as the fluctuation consumer, with the whole stopped-stage path
statement and its shared cut witnesses retained in the conclusion. -/
theorem uibotSection7b_longPath_transport :
    ∀ᵐ x ∂uibotSection7GeometricLaw,
      uibotSection7LongPathProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.1 := by
  filter_upwards [completeProperty_ae] with x hx
  exact hx.1

/-- Helper toward Proposition 3.9: Lemma 7.3's cut characterization uses
the fixed Borel LDP sequence and retains the shared cut witnesses. -/
theorem uibotSection7b_ldpCut_transport :
    ∀ᵐ x ∂uibotSection7GeometricLaw,
      uibotSection7LDPCutProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.1 := by
  filter_upwards [completeProperty_ae] with x hx
  exact hx.2.1

/-- Helper toward Proposition 3.9: Lemma 7.5 retains every carrier, edge,
root, missing-edge, distance, uniqueness, reachability and finiteness clause
on the same Borel certificate as the other three consumers. -/
theorem uibotSection7b_sdpTri_transport :
    ∀ᵐ x ∂uibotSection7GeometricLaw,
      uibotSection7SDPTriProperty (uibotRecoveredCode x) := by
  filter_upwards [completeProperty_ae] with x hx
  exact hx.2.2.1

/-- Helper toward Proposition 3.9: Lemma 7.7's cut characterization uses
the fixed Borel SDP sequence and retains the shared cut witnesses. -/
theorem uibotSection7b_sdpCut_transport :
    ∀ᵐ x ∂uibotSection7GeometricLaw,
      uibotSection7SDPCutProperty (uibotRecoveredCode x)
        (uibotGeomBusemannObservables x).1.2 := by
  filter_upwards [completeProperty_ae] with x hx
  exact hx.2.2.2

/-- Helper toward Proposition 3.9: one code event recovers the code,
both entire Busemann sequences, and the common Borel certificate together.
All integer indices and all four consumers use this same event. -/
theorem uibotSection7b_transport_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      uibotRecoveredCode (uibotSection7ClassMap W) = W ∧
      (uibotGeomBusemannObservables (uibotSection7ClassMap W)).1 =
        (identifiedLDPBusemann W, identifiedSDPBusemann W) ∧
      uibotSection7bCertificate (uibotSection7ClassMap W) := by
  have hc := ae_of_ae_map
    (measurable_uibotMeasurableWholePlaneClassMap
      uibotDeterministicComparison_proved).aemeasurable uibotSection7bCertificate_ae
  filter_upwards [uibotRecoveredCode_ae, uibotGeomBusemannObservables_ae, hc]
    with W hi heq hcert
  exact ⟨hi, (congrArg Prod.fst heq).symm, hcert⟩

private theorem window_measurable (longest : Bool) (k : ℕ) (A p : ℝ) :
    MeasurableSet {x : D39GeomRootedMapClass.{0} | ∀ l : ℤ,
      -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then (uibotGeomBusemannObservables x).1.1
        else (uibotGeomBusemannObservables x).1.2) l : ℝ)| ≤ A * (k : ℝ) ^ p} := by
  have hm : Measurable (fun x => if longest then (uibotGeomBusemannObservables x).1.1
      else (uibotGeomBusemannObservables x).1.2) := by
    cases longest
    · exact measurable_uibotGeomBusemannObservables.fst.snd
    · exact measurable_uibotGeomBusemannObservables.fst.fst
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le
    ((measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp
      ((measurable_pi_apply l).comp hm)) measurable_const

/-- Helper toward Proposition 3.9: each finite-window predicate for
either fixed Borel sequence is Borel, and its probability equals the code
probability exactly, for every size, level and exponent. -/
theorem uibotSection7b_window_transport (longest : Bool) (k : ℕ) (A p : ℝ) :
    MeasurableSet {x : D39GeomRootedMapClass.{0} | ∀ l : ℤ,
      -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then (uibotGeomBusemannObservables x).1.1
        else (uibotGeomBusemannObservables x).1.2) l : ℝ)| ≤ A * (k : ℝ) ^ p} ∧
    uibotSection7GeometricLaw.real {x | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then (uibotGeomBusemannObservables x).1.1
        else (uibotGeomBusemannObservables x).1.2) l : ℝ)| ≤ A * (k : ℝ) ^ p} =
    wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |((if longest then identifiedLDPBusemann W
        else identifiedSDPBusemann W) l : ℝ)| ≤ A * (k : ℝ) ^ p} := by
  refine ⟨window_measurable longest k A p, ?_⟩
  rw [Measure.real, Measure.map_apply
    (measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)
    (window_measurable longest k A p)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [uibotSection7b_transport_ae] with W hW
  apply propext
  change (∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
    |((if longest then (uibotGeomBusemannObservables (uibotSection7ClassMap W)).1.1
      else (uibotGeomBusemannObservables (uibotSection7ClassMap W)).1.2) l : ℝ)|
      ≤ A * (k : ℝ) ^ p) ↔ _
  rw [hW.2.1]

/-- Helper toward Proposition 3.9: Lemma 7.3 for the fixed joint Borel
observable. The same nonnegative C works for every positive size k and
every A greater than one, in the source quantifier order. -/
theorem uibotSection7b_ldpFluctuation_transport :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        uibotSection7GeometricLaw.real {x | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |((uibotGeomBusemannObservables x).1.1 l : ℝ)| ≤
            A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  obtain ⟨C, hC, hb⟩ := DirectedDistances.Paper.Section7.lem_ldp_fluctuation.2
  refine ⟨C, hC, ?_⟩
  intro k hk A hA
  have heq := (uibotSection7b_window_transport true k A (3 / 2)).2
  simp only [ite_true] at heq
  rw [heq]
  exact hb k hk A hA

/-- Helper toward Proposition 3.9: Lemma 7.7 for the fixed joint Borel
observable. For each positive delta, one threshold A0 greater than one is
chosen before every positive size k and every A at least A0. -/
theorem uibotSection7b_sdpFluctuation_transport :
    ∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
        1 - delta ≤ uibotSection7GeometricLaw.real {x | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |((uibotGeomBusemannObservables x).1.2 l : ℝ)| ≤
            A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  intro delta hd
  obtain ⟨A0, hA0, hb⟩ := DirectedDistances.Paper.Section7.lem_sdp_fluctuation.2 delta hd
  refine ⟨A0, hA0, ?_⟩
  intro k hk A hA
  have heq := (uibotSection7b_window_transport false k A (3 / 4)).2
  simp only [Bool.false_eq_true, ite_false] at heq
  rw [heq]
  exact hb k hk A hA

/-- Helper toward Proposition 3.9: all four consumers on one shared
cut, with the fixed Borel LDP and SDP sequences. This keeps every geometric
identification from Lemma 7.5, the stopped-stage paths from Lemma 7.1,
Busemann uniqueness, and simultaneous finite-distance inequalities. The
cut hypotheses are propositions, so their proof witnesses agree by proof
irrelevance; no new geometric identification is assumed. -/
theorem uibotSection7b_sharedCut_transport :
    ∀ᵐ x ∂uibotSection7GeometricLaw,
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
        X l - X k ≤ ((D.sdp (D.x l) (D.x k)).toNat : ℤ) := by
  filter_upwards [uibotSection7b_sdpTri_transport, uibotSection7b_longPath_transport,
    uibotSection7b_sdpCut_transport] with x h5 h1 h7
  obtain ⟨H, h, hLL, hids, huniq, htri⟩ := h5
  obtain ⟨H1, h1, hLL1, hL, hpath⟩ := h1
  obtain ⟨H7, h7, hLL7, hS⟩ := h7
  exact ⟨H, h, hLL, hids, hL, hS, huniq, hpath, htri⟩

/-- Helper toward Proposition 3.9: the recovered code, both complete
sequences, and the common certificate are all Borel on the geometric class. -/
theorem uibotSection7b_measurable :
    Measurable uibotRecoveredCode ∧
    Measurable (fun x => (uibotGeomBusemannObservables x).1.1) ∧
    Measurable (fun x => (uibotGeomBusemannObservables x).1.2) ∧
    MeasurableSet {x | uibotSection7bCertificate x} :=
  ⟨measurable_uibotRecoveredCode,
    measurable_uibotGeomBusemannObservables.fst.fst,
    measurable_uibotGeomBusemannObservables.fst.snd,
    measurableSet_uibotSection7bCertificate⟩

/-- Helper toward Proposition 3.9: each complete source predicate has
the common Borel representative after F, simultaneously for all consumers.
This is an almost-sure equivalence, not a pointwise geometric identification. -/
theorem uibotSection7b_consumers_ae_iff :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (uibotSection7LongPathProperty W (identifiedLDPBusemann W) ↔
        uibotSection7bCertificate (uibotSection7ClassMap W)) ∧
      (uibotSection7LDPCutProperty W (identifiedLDPBusemann W) ↔
        uibotSection7bCertificate (uibotSection7ClassMap W)) ∧
      (uibotSection7SDPTriProperty W ↔
        uibotSection7bCertificate (uibotSection7ClassMap W)) ∧
      (uibotSection7SDPCutProperty W (identifiedSDPBusemann W) ↔
        uibotSection7bCertificate (uibotSection7ClassMap W)) := by
  obtain ⟨S, _, hnull, hall⟩ := uibotSection7b_consumers_conull
  have hSae : ∀ᵐ x ∂uibotSection7GeometricLaw, x ∈ S := ae_iff.mpr hnull
  have hc := ae_of_ae_map
    (measurable_uibotMeasurableWholePlaneClassMap
      uibotDeterministicComparison_proved).aemeasurable hSae
  filter_upwards [uibotSection7b_transport_ae, hc] with W hW hS
  obtain ⟨h1, h3, h5, h7⟩ := hall _ hS
  rw [hW.1, hW.2.1] at h1 h3 h7
  rw [hW.1] at h5
  exact ⟨iff_of_true h1 hW.2.2, iff_of_true h3 hW.2.2,
    iff_of_true h5 hW.2.2, iff_of_true h7 hW.2.2⟩

end DirectedDistances.PaperProofs.Section3
end
