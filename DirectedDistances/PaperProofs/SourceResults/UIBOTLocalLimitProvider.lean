/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTSourceStatementPart2

/-! Supporting lemmas for paper labels `prop-kmsw-uibot` (see CORRESPONDENCE.md). -/

























public section
noncomputable section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

-- The geometric Borel structure on rooted map classes.
local instance instBorelD39Class_UIBOTLocalLimitProvider :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance instBorelSpaceD39Class_UIBOTLocalLimitProvider :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩




theorem prop_kmsw_uibot_source_provider :
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
            hℓ hρ (hsize k) (hne k)) atTop (𝓝 ν) → ν = μ :=
  prop_kmsw_uibot_source

end DirectedDistances.PaperProofs.SourceResults
