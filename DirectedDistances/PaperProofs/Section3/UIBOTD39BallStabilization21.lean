/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization20
public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitReduction2

/- # The measurable geometric ball-law reduction with DC discharged

The deterministic comparison proved in session 11 discharges the sole open
input of `uibotMeasurableGeometricBallLaw_tendsto_of_comparison`. The same
measurable representative is identified almost surely with the glued
whole-plane drawing, including its domain witness and chronological root.
Ball-class index `r` denotes geometric radius `r + 1`.

fresh kernel validation remain with the sole coordinator before paper credit. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter
open scoped Topology ENNReal

local instance ballStabilization21MeasurableSpace : MeasurableSpace D39GeomRootedMapClass :=
  borel D39GeomRootedMapClass

/-- Helper toward Proposition 3.9: the whole-plane representative supplied
by the proved DC is Borel measurable, with no deterministic comparison premise. -/
theorem uibotMeasurableWholePlaneClassMap_measurable_proved :
    Measurable (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved) :=
  measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved

/-- Helper toward Proposition 3.9: the measurable representative is almost
surely the exact glued whole-plane geometric map, with the same witnesses
for its rotation, drawing, edge presence, root and geometric domain. -/
theorem uibotMeasurableWholePlaneClassMap_ae_represents_proved :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
        (hdom : D39GeomDomain
          (uibotWholePlaneGeometricMap W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
          (uibotWholePlaneGeometricRoot W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))),
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W =
          Quotient.mk d39DomainSetoid
            ({ V := WholePlaneVertex W,
               E := (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H).GeometricEdge,
               map := uibotWholePlaneGeometricMap W H
                 (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp,
               root := uibotWholePlaneGeometricRoot W H
                 (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H),
               domain := hdom } : D39DomainRootedMap) :=
  uibotMeasurableWholePlaneClassMap_ae_represents uibotDeterministicComparison_proved

/-- Helper toward Proposition 3.9: for fixed positive boundary lengths,
the actual uniform finite-map geometric ball masses converge to those of
the measurable whole-plane realization along every admissible size sequence
tending to infinity. DC and drawing independence are not premises. -/
theorem uibotMeasurableGeometricBallLaw_tendsto_proved
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (r : ℕ) (b : Quotient (d39GeomBallClassSetoid r)) :
    Tendsto (fun k =>
      (uibotFiniteUniformSampleLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k))
        {p | d39GeomBallClassMap r
          (uibotFiniteGeometricClassMap ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) p) = b})
      atTop (𝓝 (wholePlaneIIDCodeMeasure
        {W | d39GeomBallClassMap r
          (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) = b})) :=
  uibotMeasurableGeometricBallLaw_tendsto_of_comparison uibotDeterministicComparison_proved
    ℓ ρ hℓ hρ ns hns hsize hne r b

end DirectedDistances.PaperProofs.Section3

end
