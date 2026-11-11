/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTSourceStatementPart1
public import DirectedDistances.PaperProofs.Section3.UIBOTWholePlaneSourcePart4

/- # Source statement of the UIBOT KMSW local-limit law

the UIBOT defined by the finite local limit at line 224 and the whole-plane
KMSW union and root at lines 100–107. The topology is the installed

One measurable random class and one probability law work for every fixed
pair of positive boundary lengths and every admissible diverging size
sequence. The class is almost surely the installed source construction on
its original edge identities, rooted at lambda zero. The normalized walk
has independent increments with the exact printed three-step uniform law.
All finite-law, deterministic-comparison and whole-plane witnesses are
supplied by existing proofs, rather than hypotheses of the statement.

No open mathematical statement is retained as a premise here. Independent
coordinator; this file alone does not declare a numbered-result closure. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

local instance uibotSourceStatementPart2GeomMeasurable :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotSourceStatementPart2GeomBorel :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: uniform finite source maps with a
uniform actual-edge root converge, for every fixed positive boundary pair
and admissible diverging size sequence, to one law on the installed
Definition 3.8 geometric class space. This law is the iid pushforward of
the source whole-plane KMSW construction of the normalized walk, rooted
at lambda zero; every local limit equals it. All source identifications
and the independent uniform increment law are conclusions. -/
theorem prop_kmsw_uibot_source :
    ∃ (F : (ℤ → Fin 3) → D39GeomRootedMapClass.{0})
      (μ : ProbabilityMeasure D39GeomRootedMapClass.{0}),
      Measurable F ∧
      (∀ W : ℤ → Fin 3,
        wholePlaneWordIntegral W 0 = (0, 0) ∧
        ∀ t : ℤ, wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t =
          lazyTwoDimensionalStep (W t)) ∧
      iIndepFun (fun t (W : ℤ → Fin 3) =>
        wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t)
        wholePlaneIIDCodeMeasure ∧
      (∀ t : ℤ,
        wholePlaneIIDCodeMeasure.map (fun W =>
          wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t) =
          Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        ∃ (H : WholePlaneRotationHypothesis W)
          (h0 : BoundaryHitWitnesses (shiftedStream W 0))
          (hpast : BoundaryHitWitnesses (kmswPastCode W))
          (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
          let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
          F W = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
          uibotWholePlaneSourceRoot W H G =
            (wholePlaneEdgeι W 0 0,
              (uibotWholePlaneSourceDirectedMap W H G hp).forward
                (wholePlaneEdgeι W 0 0)) ∧
          d39GeomRootVertex (uibotWholePlaneSourceMap W H G hp)
            (uibotWholePlaneSourceRoot W H G) =
              wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0) ∧
          Infinite (WholePlaneVertex W) ∧
          (uibotWholePlaneSourceDirectedMap W H G hp).IsBipolarTriangulation) ∧
      (μ : Measure D39GeomRootedMapClass.{0}) = wholePlaneIIDCodeMeasure.map F ∧
      ∀ (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
        (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
        (hsize : ∀ k, 1 ≤ ns k)
        (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))),
        Tendsto (fun k => uibotFiniteSourceEdgeProbabilityLaw ℓ ρ (ns k)
          hℓ hρ (hsize k) (hne k)) atTop (𝓝 μ) ∧
        ∀ ν : ProbabilityMeasure D39GeomRootedMapClass.{0},
          Tendsto (fun k => uibotFiniteSourceEdgeProbabilityLaw ℓ ρ (ns k)
            hℓ hρ (hsize k) (hne k)) atTop (𝓝 ν) → ν = μ := by
  refine ⟨uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved,
    uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved,
    measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved,
    fun W => ⟨uibotSourceWalk_zero W, uibotSourceWalk_increment W⟩,
    uibotSourceWalk_independent_increments, uibotSourceWalk_increment_law, ?_, rfl, ?_⟩
  · filter_upwards [uibotMeasurableWholePlaneClassMap_ae_normalized_source] with W hW
    obtain ⟨_, _, H, h0, hpast, hp, hclass, _, _, hroot, hinf, _, htri,
      hrootDir, _, _, _⟩ := hW
    exact ⟨H, h0, hpast, hp, hclass, hrootDir, hroot, hinf, htri⟩
  · intro ℓ ρ hℓ hρ ns hns hsize hne
    have hconv := uibotFiniteSourceEdgeProbabilityLaw_tendsto
      ℓ ρ hℓ hρ ns hns hsize hne
    exact ⟨hconv, fun _ hν => tendsto_nhds_unique hν hconv⟩

end DirectedDistances.PaperProofs.Section3
end
