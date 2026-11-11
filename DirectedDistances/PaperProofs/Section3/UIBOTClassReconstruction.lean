/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTSourceStatementPart2
public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart7
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassBorel
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric





















public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory Filter Set
open scoped ENNReal Topology

local instance uibotClassReconstructionMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotClassReconstructionBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

private abbrev reconstructionMap :=
  uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved

private def windowClasses : Set D39GeomRootedMapClass.{0} :=
  range (fun p : (Σ N : ℕ, Fin (2 * N) → Fin 3) =>
    Quotient.mk d39DomainSetoid (uibotWindowRepresentative p.1 p.2))

private theorem ae_mem_closure_windows :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, reconstructionMap W ∈ closure windowClasses := by
  have heq : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N r : ℕ,
      UIBOTRootWindowCapture (shiftedStream W N) N (r + 1) →
      d39GeomBallClassMap r (reconstructionMap W) =
        Quotient.mk (d39GeomBallClassSetoid r)
          (uibotWindowRepresentative N (fun i => shiftedStream W N i.val)) :=
    ae_all_iff.mpr (fun N => ae_all_iff.mpr (fun r =>
      uibotMeasurableWholePlaneClassMap_ae_window uibotDeterministicComparison_proved N r))
  filter_upwards [heq, wholePlaneIID_ae_eventual_uibotRootWindowCapture] with W hW hcap
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨r, hr⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt hε)
  obtain ⟨N, hN⟩ := hcap (r + 1)
  refine ⟨Quotient.mk d39DomainSetoid
    (uibotWindowRepresentative N (fun i => shiftedStream W N i.val)),
    ⟨⟨N, (fun i => shiftedStream W N i.val)⟩, rfl⟩, ?_⟩
  have hm : Quotient.mk d39DomainSetoid
      (uibotWindowRepresentative N (fun i => shiftedStream W N i.val)) ∈
      Metric.eball (reconstructionMap W) ((1 / 2 : ℝ≥0∞) ^ r) := by
    rw [d39GeomClass_openBall_eq_ballClass]
    change d39GeomBallClassMap r _ = d39GeomBallClassMap r _
    rw [d39GeomBallClassMap_mk]
    exact hW N r (hN N le_rfl)
  change edist _ _ < _ at hm
  rw [edist_comm] at hm
  exact hm.trans (by simpa only [one_div] using hr)

private theorem zero_iff_distances (x y : D39GeomRootedMapClass.{0})
    (hy : y ∈ closure windowClasses) :
    edist x y = 0 ↔ ∀ c ∈ windowClasses, edist x c = edist y c := by
  constructor
  · intro h c _
    exact edist_congr_right h
  · intro h
    apply le_antisymm _ bot_le
    apply le_of_forall_gt
    intro ε hε
    obtain ⟨c, hc, hyc⟩ := EMetric.mem_closure_iff.mp hy ε hε
    have hxc : edist x c < ε := (h c hc) ▸ hyc
    have hcy : edist c y < ε := by rwa [edist_comm]
    exact (d39ClassDistance_ultrametric x c y).trans_lt (max_lt hxc hcy)

private def windowDistance (x y : D39GeomRootedMapClass.{0}) : ℝ≥0∞ :=
  ⨅ p : (Σ N : ℕ, Fin (2 * N) → Fin 3),
    max (edist x (Quotient.mk d39DomainSetoid (uibotWindowRepresentative p.1 p.2)))
      (edist y (Quotient.mk d39DomainSetoid (uibotWindowRepresentative p.1 p.2)))

private theorem windowDistance_eq (x y : D39GeomRootedMapClass.{0})
    (hy : y ∈ closure windowClasses) : windowDistance x y = edist x y := by
  apply le_antisymm
  · have hs : windowClasses ⊆ {c : D39GeomRootedMapClass.{0} |
        windowDistance x y ≤ max (edist x c) (edist y c)} := by
      rintro c ⟨p, rfl⟩
      exact iInf_le (fun q : (Σ N : ℕ, Fin (2 * N) → Fin 3) =>
        max (edist x (Quotient.mk d39DomainSetoid (uibotWindowRepresentative q.1 q.2)))
          (edist y (Quotient.mk d39DomainSetoid (uibotWindowRepresentative q.1 q.2)))) p
    have hclosed : IsClosed {c : D39GeomRootedMapClass.{0} |
        windowDistance x y ≤ max (edist x c) (edist y c)} :=
      isClosed_le continuous_const
        ((continuous_const.edist continuous_id).max (continuous_const.edist continuous_id))
    have h := closure_minimal hs hclosed hy
    exact h.trans (max_le le_rfl (by rw [edist_self]; exact bot_le))
  · apply le_iInf
    intro p
    have h : edist x y ≤ max
        (edist x (Quotient.mk d39DomainSetoid (uibotWindowRepresentative p.1 p.2)))
        (edist (Quotient.mk d39DomainSetoid (uibotWindowRepresentative p.1 p.2)) y) :=
      d39ClassDistance_ultrametric x _ y
    rwa [edist_comm
      (Quotient.mk d39DomainSetoid (uibotWindowRepresentative p.1 p.2)) y] at h

/-- Helper toward Proposition 3.9: the reconstruction distance admits a
Borel scalar version agreeing with it whenever the reconstructed class lies
in the closure of the countable window family. That condition holds on a
Borel conull set of recovered codes; no global second countability is used. -/
theorem uibotClassReconstruction_borel_distance :
    ∃ (S : Set (ℤ → Fin 3)) (D : D39GeomRootedMapClass.{0} → ℝ≥0∞),
      MeasurableSet S ∧ (∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∈ S) ∧
      (∀ᵐ x ∂(uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
        Measure D39GeomRootedMapClass.{0}), uibotRecoveredCode x ∈ S) ∧
      Measurable D ∧ ∀ x : D39GeomRootedMapClass.{0}, uibotRecoveredCode x ∈ S →
        D x = edist x (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
          (uibotRecoveredCode x)) := by
  let S : Set (ℤ → Fin 3) := {W | reconstructionMap W ∈ closure windowClasses}
  have hF : Measurable reconstructionMap :=
    measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
  have hS : MeasurableSet S := isClosed_closure.measurableSet.preimage hF
  refine ⟨S, fun x => windowDistance x (reconstructionMap (uibotRecoveredCode x)),
    hS, ae_mem_closure_windows, ?_, ?_, ?_⟩
  · apply (ae_map_iff hF.aemeasurable (hS.preimage measurable_uibotRecoveredCode)).mpr
    filter_upwards [uibotRecoveredCode_ae, ae_mem_closure_windows] with W hinv hW
    rw [hinv]
    exact hW
  · apply Measurable.iInf
    intro p
    exact (measurable_edist_left).max
      ((measurable_edist_left).comp (hF.comp measurable_uibotRecoveredCode))
  · intro x hx
    exact windowDistance_eq _ _ hx

/-- Helper toward Proposition 3.9: there is a Borel conull set of good
codes for which the zero-distance reconstruction event, intersected with
the recovered-code preimage of this set, is Borel and conull for the fixed
whole-plane geometric law. No measurability of class equality is used. -/
theorem uibotClassReconstruction_measurable_conull :
    ∃ S : Set (ℤ → Fin 3), MeasurableSet S ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∈ S) ∧
      MeasurableSet {x : D39GeomRootedMapClass.{0} |
        edist x (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
          (uibotRecoveredCode x)) = 0 ∧
          uibotRecoveredCode x ∈ S} ∧
      (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
        Measure D39GeomRootedMapClass.{0})
        {x | edist x (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
          (uibotRecoveredCode x)) = 0 ∧
          uibotRecoveredCode x ∈ S}ᶜ = 0 := by
  let S : Set (ℤ → Fin 3) := {W | reconstructionMap W ∈ closure windowClasses}
  have hF : Measurable reconstructionMap :=
    measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
  have hS : MeasurableSet S := isClosed_closure.measurableSet.preimage hF
  have hY : Measurable (fun x => reconstructionMap (uibotRecoveredCode x)) :=
    hF.comp measurable_uibotRecoveredCode
  have hE : MeasurableSet {x : D39GeomRootedMapClass.{0} |
      ∀ c ∈ windowClasses, edist x c = edist (reconstructionMap (uibotRecoveredCode x)) c} := by
    have hcount : windowClasses.Countable := countable_range _
    have hm : MeasurableSet (⋂ c ∈ windowClasses,
        {x : D39GeomRootedMapClass.{0} |
          edist x c = edist (reconstructionMap (uibotRecoveredCode x)) c}) :=
      MeasurableSet.biInter hcount (fun c _ =>
      measurableSet_eq_fun (measurable_edist_left (x := c))
        ((measurable_edist_left (x := c)).comp hY))
    simpa only [ofPred_forall, Function.comp_def] using hm
  have hT : MeasurableSet {x : D39GeomRootedMapClass.{0} |
      edist x (reconstructionMap (uibotRecoveredCode x)) = 0 ∧
        uibotRecoveredCode x ∈ S} := by
    have hevent : {x : D39GeomRootedMapClass.{0} |
        edist x (reconstructionMap (uibotRecoveredCode x)) = 0 ∧
          uibotRecoveredCode x ∈ S} =
        {x | ∀ c ∈ windowClasses,
          edist x c = edist (reconstructionMap (uibotRecoveredCode x)) c} ∩
          uibotRecoveredCode ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨hz, hs⟩
        exact ⟨(zero_iff_distances _ _ hs).mp hz, hs⟩
      · rintro ⟨hd, hs⟩
        exact ⟨(zero_iff_distances _ _ hs).mpr hd, hs⟩
    rw [hevent]
    exact hE.inter (hS.preimage measurable_uibotRecoveredCode)
  refine ⟨S, hS, ae_mem_closure_windows, hT, ?_⟩
  have hpre : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      edist (reconstructionMap W)
        (reconstructionMap (uibotRecoveredCode (reconstructionMap W))) = 0 ∧
          uibotRecoveredCode (reconstructionMap W) ∈ S := by
    filter_upwards [uibotRecoveredCode_ae, ae_mem_closure_windows] with W hinv hW
    rw [hinv]
    exact ⟨edist_self _, hW⟩
  have hconull := (ae_map_iff hF.aemeasurable hT).mpr hpre
  exact mem_ae_iff.mp hconull

/-- Helper toward Proposition 3.9: reconstruction from the recovered
entire code has zero Definition 3.8 distance almost surely under the fixed
geometric whole-plane law. This does not identify global geometric classes. -/
theorem uibotClassReconstruction_ae_edist_zero :
    ∀ᵐ x ∂(uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0}),
      edist x (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
        (uibotRecoveredCode x)) = 0 := by
  obtain ⟨S, _, _, _, hT⟩ := uibotClassReconstruction_measurable_conull
  have h : ∀ᵐ x ∂(uibotWholePlaneGeometricProbabilityLaw
      uibotDeterministicComparison_proved : Measure D39GeomRootedMapClass.{0}),
      edist x (reconstructionMap (uibotRecoveredCode x)) = 0 ∧
        uibotRecoveredCode x ∈ S := mem_ae_iff.mpr hT
  exact h.mono (fun _ hx => hx.1)

/-- Helper toward Proposition 3.9: every representative of almost every
sample has all positive-radius geometric balls isomorphic to every
representative of the reconstructed class, retaining edge identities,
root, orientation, missing tags and retained original faces. -/
theorem uibotClassReconstruction_ae_all_balls :
    ∀ᵐ x ∂(uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0}),
      ∀ A B : D39DomainRootedMap.{0},
        Quotient.mk d39DomainSetoid A = x →
        Quotient.mk d39DomainSetoid B =
          uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
            (uibotRecoveredCode x) →
        ∀ r : ℕ, 0 < r → Nonempty (D39GeomBallIsoV2 r A.map A.root B.map B.root) := by
  filter_upwards [uibotClassReconstruction_ae_edist_zero] with x hx
  intro A B hA hB r hr
  have hz : edist (Quotient.mk d39DomainSetoid A)
      (Quotient.mk d39DomainSetoid B) = 0 := by rw [hA, hB]; exact hx
  exact (d39ClassDistance_le_pow_iff_nonempty hr A B).mp (by rw [hz]; exact bot_le)

private theorem recoveredCode_law :
    (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0}).map uibotRecoveredCode = wholePlaneIIDCodeMeasure := by
  change (wholePlaneIIDCodeMeasure.map reconstructionMap).map uibotRecoveredCode = _
  rw [Measure.map_map measurable_uibotRecoveredCode
    (measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)]
  exact (Measure.map_congr uibotRecoveredCode_ae).trans Measure.map_id

/-- Helper toward Proposition 3.9: almost every sampled class has every
positive-radius ball isomorphic to the source whole-plane construction at
its recovered code. The same rotation, past/future boundary witnesses and
edge-presence witnesses work for every representative and every radius. -/
theorem uibotClassReconstruction_ae_source_balls :
    ∀ᵐ x ∂(uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0}),
      let W := uibotRecoveredCode x
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
        let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
        ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = x →
          ∀ r : ℕ, 0 < r → Nonempty (D39GeomBallIsoV2 r A.map A.root
            (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)) := by
  have hsource := uibotMeasurableWholePlaneClassMap_ae_source
  rw [← recoveredCode_law] at hsource
  have hsource' := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable hsource
  filter_upwards [uibotClassReconstruction_ae_all_balls, hsource'] with x hx hs
  obtain ⟨H, h0, hpast, hp, heq, _, _⟩ := hs
  refine ⟨H, h0, hpast, hp, ?_⟩
  dsimp only
  intro A hA r hr
  exact hx A (uibotWholePlaneSourceDomain _ H
    (WholePlanePastGlueDrawing.glueDrawing _ h0 hpast H) hp) hA heq.symm r hr

end DirectedDistances.PaperProofs.Section3
end
