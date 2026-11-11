/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart6
public import DirectedDistances.Paper.Section7.LongPath
public import DirectedDistances.Paper.Section7.LDPFluctuation
public import DirectedDistances.Paper.Section7.SDPTri
public import DirectedDistances.Paper.Section7.SDPFluctuation











public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

local instance uibotQualifierSection7MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotQualifierSection7BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: the proved measurable geometric class map. -/
abbrev uibotSection7ClassMap :=
  uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved

/-- Helper toward Proposition 3.9: the iid geometric pushforward law. -/
abbrev uibotSection7GeometricLaw := wholePlaneIIDCodeMeasure.map uibotSection7ClassMap

private theorem uibotSection7ClassMap_measurable : Measurable uibotSection7ClassMap :=
  measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved

private theorem inverse_law
    (G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3)) (hG : Measurable G)
    (hi : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, G (uibotSection7ClassMap W) = W) :
    uibotSection7GeometricLaw.map G = wholePlaneIIDCodeMeasure := by
  rw [Measure.map_map hG uibotSection7ClassMap_measurable]
  calc
    wholePlaneIIDCodeMeasure.map (G ∘ uibotSection7ClassMap) = wholePlaneIIDCodeMeasure.map id :=
      Measure.map_congr hi
    _ = wholePlaneIIDCodeMeasure := Measure.map_id

private theorem borel_refinement
    (G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3)) (hG : Measurable G)
    (hi : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, G (uibotSection7ClassMap W) = W)
    (Q : (ℤ → Fin 3) → Prop) (hQ : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, Q W) :
    ∃ P : D39GeomRootedMapClass.{0} → Prop,
      MeasurableSet {x | P x} ∧ (∀ᵐ x ∂uibotSection7GeometricLaw, P x) ∧
      (∀ x, P x → Q (G x)) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, Q W ↔ P (uibotSection7ClassMap W)) := by
  let s := (toMeasurable wholePlaneIIDCodeMeasure {W | ¬ Q W})ᶜ
  have hs : MeasurableSet s := (measurableSet_toMeasurable _ _).compl
  have hsae : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∈ s := by
    rw [ae_iff]
    simp only [s, Set.mem_compl_iff, not_not]
    change wholePlaneIIDCodeMeasure (toMeasurable wholePlaneIIDCodeMeasure {W | ¬ Q W}) = 0
    rw [measure_toMeasurable]
    exact ae_iff.mp hQ
  have hsub (W) (hW : W ∈ s) : Q W := by
    by_contra hn
    exact hW (subset_toMeasurable wholePlaneIIDCodeMeasure {W | ¬ Q W} hn)
  have hsmap : ∀ᵐ x ∂uibotSection7GeometricLaw, G x ∈ s := by
    have h := hsae
    rw [← inverse_law G hG hi] at h
    exact ae_of_ae_map hG.aemeasurable h
  refine ⟨fun x => G x ∈ s, hs.preimage hG, hsmap, fun x hx => hsub _ hx, ?_⟩
  filter_upwards [hQ, hsae, hi] with W hW hsW hiW
  exact iff_of_true hW (hiW.symm ▸ hsW)

private theorem window_measurable
    (Y : D39GeomRootedMapClass.{0} → (ℤ → ℤ)) (hY : Measurable Y)
    (k : ℕ) (A p : ℝ) :
    MeasurableSet {x | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(Y x l : ℝ)| ≤ A * (k : ℝ) ^ p} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le
    ((measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp
      ((measurable_pi_apply l).comp hY)) measurable_const

private theorem window_probability
    (X : (ℤ → Fin 3) → (ℤ → ℤ))
    (Y : D39GeomRootedMapClass.{0} → (ℤ → ℤ)) (hY : Measurable Y)
    (heq : X =ᵐ[wholePlaneIIDCodeMeasure] Y ∘ uibotSection7ClassMap)
    (k : ℕ) (A p : ℝ) :
    uibotSection7GeometricLaw.real {x | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(Y x l : ℝ)| ≤ A * (k : ℝ) ^ p} =
    wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(X W l : ℝ)| ≤ A * (k : ℝ) ^ p} := by
  rw [Measure.real, Measure.map_apply uibotSection7ClassMap_measurable (window_measurable Y hY k A p)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [heq] with W hW
  apply propext
  change (∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
    |(Y (uibotSection7ClassMap W) l : ℝ)| ≤ A * (k : ℝ) ^ p) ↔ _
  rw [show Y (uibotSection7ClassMap W) = X W from hW.symm]

/-- Helper toward Proposition 3.9: the complete simultaneous Lemma 7.1
predicate, with one triple of cut witnesses and an explicit full LDP sequence. -/
@[expose] def uibotSection7LongPathProperty (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : WholePlaneRotationHypothesis W,
  ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
  ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
  let w := shiftedStream W 0
  let V := wholePlaneVertexι W 0
  let D := m0CutData W H h hLL
  IsIdentifiedM0BusemannLDP D X ∧
  ∀ ell k : ℕ, 1 ≤ ell → ell < k →
    let n := boundaryHitTime w h (-(k : ℤ))
    ∃ (N : ℕ) (p : Fin (N + 1) → WholePlaneVertex W),
      (∀ i : Fin N, m0CutDirectedStep W H D.seam (p i.castSucc) (p i.succ)) ∧
      IdentifiedStagePath W V n N p ∧
      (max (X (-(ell : ℤ)) - X (-(k : ℤ))) 0).toNat ≤ N

/-- Helper toward Proposition 3.9: the full shared-cut characterization
used by Lemma 7.3, with an explicit full integer-indexed sequence. -/
@[expose] def uibotSection7LDPCutProperty (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : WholePlaneRotationHypothesis W,
  ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
  ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
    IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X

/-- Helper toward Proposition 3.9: the full shared-cut characterization
used by Lemma 7.7, with an explicit full integer-indexed sequence. -/
@[expose] def uibotSection7SDPCutProperty (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : WholePlaneRotationHypothesis W,
  ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
  ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
    IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X

/-- Helper toward Proposition 3.9: Lemma 7.1 transported through a Borel
recovered code and a Borel full LDP sequence. The Borel certificate implies
the entire stopped-stage statement, retaining the shared cut witnesses. -/
theorem uibotSection7_longPath_transport :
    ∃ (G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3))
      (L : D39GeomRootedMapClass.{0} → (ℤ → ℤ))
      (P : D39GeomRootedMapClass.{0} → Prop),
      Measurable G ∧ Measurable L ∧ MeasurableSet {x | P x} ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, G (uibotSection7ClassMap W) = W ∧
        L (uibotSection7ClassMap W) = identifiedLDPBusemann W ∧
        (uibotSection7LongPathProperty W (identifiedLDPBusemann W) ↔ P (uibotSection7ClassMap W))) ∧
      (∀ᵐ x ∂uibotSection7GeometricLaw, P x) ∧
      (∀ x, P x → uibotSection7LongPathProperty (G x) (L x)) := by
  obtain ⟨G, hG, hi⟩ := uibotRecovery_exists_borel_inverse
  let X := aemeasurable_identifiedLDPBusemann.mk identifiedLDPBusemann
  have hm : Measurable X := aemeasurable_identifiedLDPBusemann.measurable_mk
  have he : identifiedLDPBusemann =ᵐ[wholePlaneIIDCodeMeasure] X :=
    aemeasurable_identifiedLDPBusemann.ae_eq_mk
  have hQ : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, uibotSection7LongPathProperty W (X W) := by
    filter_upwards [DirectedDistances.Paper.Section7.lem_long_path, he] with W hW heW
    exact heW ▸ hW
  obtain ⟨P, hP, hPae, hPQ, hPe⟩ := borel_refinement G hG hi _ hQ
  refine ⟨G, X ∘ G, P, hG, hm.comp hG, hP, ?_, hPae, hPQ⟩
  filter_upwards [hi, he, hPe] with W hiW heW hpW
  refine ⟨hiW, ?_, ?_⟩
  · change X (G (uibotSection7ClassMap W)) = identifiedLDPBusemann W
    rw [hiW]
    exact heW.symm
  · rw [heW]
    exact hpW

/-- Helper toward Proposition 3.9: Lemma 7.3 on the geometric pushforward
law, with a Borel full sequence and cut certificate. One nonnegative C is
chosen before every positive k and every A greater than one. -/
theorem uibotSection7_ldpFluctuation_transport :
    ∃ (G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3))
      (L : D39GeomRootedMapClass.{0} → (ℤ → ℤ))
      (P : D39GeomRootedMapClass.{0} → Prop),
      Measurable G ∧ Measurable L ∧ MeasurableSet {x | P x} ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, G (uibotSection7ClassMap W) = W ∧
        L (uibotSection7ClassMap W) = identifiedLDPBusemann W ∧
        (uibotSection7LDPCutProperty W (identifiedLDPBusemann W) ↔ P (uibotSection7ClassMap W))) ∧
      (∀ᵐ x ∂uibotSection7GeometricLaw, P x) ∧
      (∀ x, P x → uibotSection7LDPCutProperty (G x) (L x)) ∧
      (∀ k : ℕ, ∀ A : ℝ, MeasurableSet {x | ∀ l : ℤ,
        -(k : ℤ) ≤ l → l ≤ k → |(L x l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)}) ∧
      (∀ k : ℕ, ∀ A : ℝ,
        uibotSection7GeometricLaw.real {x | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(L x l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} =
        wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(identifiedLDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)}) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ)) ≤ uibotSection7GeometricLaw.real {x | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k → |(L x l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  obtain ⟨G, hG, hi⟩ := uibotRecovery_exists_borel_inverse
  let X := aemeasurable_identifiedLDPBusemann.mk identifiedLDPBusemann
  have hm : Measurable X := aemeasurable_identifiedLDPBusemann.measurable_mk
  have he : identifiedLDPBusemann =ᵐ[wholePlaneIIDCodeMeasure] X :=
    aemeasurable_identifiedLDPBusemann.ae_eq_mk
  have hQ : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, uibotSection7LDPCutProperty W (X W) := by
    filter_upwards [DirectedDistances.Paper.Section7.lem_ldp_fluctuation.1, he] with W hW heW
    exact heW ▸ hW
  obtain ⟨P, hP, hPae, hPQ, hPe⟩ := borel_refinement G hG hi _ hQ
  have hL : Measurable (X ∘ G) := hm.comp hG
  have hfactor : identifiedLDPBusemann =ᵐ[wholePlaneIIDCodeMeasure] (X ∘ G) ∘ uibotSection7ClassMap := by
    filter_upwards [hi, he] with W hiW heW
    change identifiedLDPBusemann W = X (G (uibotSection7ClassMap W))
    rw [hiW]
    exact heW
  refine ⟨G, X ∘ G, P, hG, hL, hP, ?_, hPae, hPQ,
    fun k A => window_measurable _ hL k A _,
    fun k A => window_probability _ _ hL hfactor k A _, ?_⟩
  · filter_upwards [hi, hfactor, he, hPe] with W hiW hfW heW hpW
    refine ⟨hiW, hfW.symm, ?_⟩
    rw [heW]
    exact hpW
  · obtain ⟨C, hC, hb⟩ := DirectedDistances.Paper.Section7.lem_ldp_fluctuation.2
    refine ⟨C, hC, ?_⟩
    intro k hk A hA
    rw [window_probability _ _ hL hfactor]
    exact hb k hk A hA

/-- Helper toward Proposition 3.9: Lemma 7.7 on the geometric pushforward
law, with a Borel full SDP sequence and cut certificate. For each delta,
one threshold A0 works simultaneously for all positive k and A at least A0. -/
theorem uibotSection7_sdpFluctuation_transport :
    ∃ (G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3))
      (S : D39GeomRootedMapClass.{0} → (ℤ → ℤ))
      (P : D39GeomRootedMapClass.{0} → Prop),
      Measurable G ∧ Measurable S ∧ MeasurableSet {x | P x} ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, G (uibotSection7ClassMap W) = W ∧
        S (uibotSection7ClassMap W) = identifiedSDPBusemann W ∧
        (uibotSection7SDPCutProperty W (identifiedSDPBusemann W) ↔ P (uibotSection7ClassMap W))) ∧
      (∀ᵐ x ∂uibotSection7GeometricLaw, P x) ∧
      (∀ x, P x → uibotSection7SDPCutProperty (G x) (S x)) ∧
      (∀ k : ℕ, ∀ A : ℝ, MeasurableSet {x | ∀ l : ℤ,
        -(k : ℤ) ≤ l → l ≤ k → |(S x l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)}) ∧
      (∀ k : ℕ, ∀ A : ℝ,
        uibotSection7GeometricLaw.real {x | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(S x l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} =
        wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(identifiedSDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)}) ∧
      ∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
        ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
          1 - delta ≤ uibotSection7GeometricLaw.real {x | ∀ l : ℤ,
            -(k : ℤ) ≤ l → l ≤ k → |(S x l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  obtain ⟨G, hG, hi⟩ := uibotRecovery_exists_borel_inverse
  let X := aemeasurable_identifiedSDPBusemann.mk identifiedSDPBusemann
  have hm : Measurable X := aemeasurable_identifiedSDPBusemann.measurable_mk
  have he : identifiedSDPBusemann =ᵐ[wholePlaneIIDCodeMeasure] X :=
    aemeasurable_identifiedSDPBusemann.ae_eq_mk
  have hQ : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, uibotSection7SDPCutProperty W (X W) := by
    filter_upwards [DirectedDistances.Paper.Section7.lem_sdp_fluctuation.1, he] with W hW heW
    exact heW ▸ hW
  obtain ⟨P, hP, hPae, hPQ, hPe⟩ := borel_refinement G hG hi _ hQ
  have hS : Measurable (X ∘ G) := hm.comp hG
  have hfactor : identifiedSDPBusemann =ᵐ[wholePlaneIIDCodeMeasure] (X ∘ G) ∘ uibotSection7ClassMap := by
    filter_upwards [hi, he] with W hiW heW
    change identifiedSDPBusemann W = X (G (uibotSection7ClassMap W))
    rw [hiW]
    exact heW
  refine ⟨G, X ∘ G, P, hG, hS, hP, ?_, hPae, hPQ,
    fun k A => window_measurable _ hS k A _,
    fun k A => window_probability _ _ hS hfactor k A _, ?_⟩
  · filter_upwards [hi, hfactor, he, hPe] with W hiW hfW heW hpW
    refine ⟨hiW, hfW.symm, ?_⟩
    rw [heW]
    exact hpW
  · intro delta hd
    obtain ⟨A0, hA0, hb⟩ := DirectedDistances.Paper.Section7.lem_sdp_fluctuation.2 delta hd
    refine ⟨A0, hA0, ?_⟩
    intro k hk A hA
    rw [window_probability _ _ hS hfactor]
    exact hb k hk A hA

/-- Helper toward Proposition 3.9: the complete Lemma 7.5 predicate,
including the original carrier, edge, root, missing-edge and distance
identifications, unique Busemann function, reachability and finite SDP. -/
@[expose] def uibotSection7SDPTriProperty (W : ℤ → Fin 3) : Prop :=
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
  (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
  ∀ X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X →
    ∀ l k : ℤ, 0 ≤ l → l < k →
      m0CutReachable W H D.seam (D.x l) (D.x k) ∧
      D.sdp (D.x l) (D.x k) ≠ ⊤ ∧
      X l - X k ≤ ((D.sdp (D.x l) (D.x k)).toNat : ℤ)

/-- Helper toward Proposition 3.9: Lemma 7.5 transported as one Borel
conull certificate implying the full simultaneous statement on the Borel
recovered code. No cut witness or Busemann uniqueness clause is split off. -/
theorem uibotSection7_sdpTri_transport :
    ∃ (G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3))
      (P : D39GeomRootedMapClass.{0} → Prop),
      Measurable G ∧ MeasurableSet {x | P x} ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, G (uibotSection7ClassMap W) = W ∧
        (uibotSection7SDPTriProperty W ↔ P (uibotSection7ClassMap W))) ∧
      (∀ᵐ x ∂uibotSection7GeometricLaw, P x) ∧
      (∀ x, P x → uibotSection7SDPTriProperty (G x)) := by
  obtain ⟨G, hG, hi⟩ := uibotRecovery_exists_borel_inverse
  have hQ : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, uibotSection7SDPTriProperty W :=
    DirectedDistances.Paper.Section7.lem_sdp_tri
  obtain ⟨P, hP, hPae, hPQ, hPe⟩ := borel_refinement G hG hi _ hQ
  refine ⟨G, P, hG, hP, ?_, hPae, hPQ⟩
  filter_upwards [hi, hPe] with W hiW hpW
  exact ⟨hiW, hpW⟩

end DirectedDistances.PaperProofs.Section3
end
