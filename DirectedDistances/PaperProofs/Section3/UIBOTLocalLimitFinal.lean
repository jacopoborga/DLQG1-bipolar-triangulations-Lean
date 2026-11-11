/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization19
public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitLaw

/- # Geometric local-limit helpers toward Proposition 3.9

comparison discharges DC in the existing convergence results. The finite
carrier remains `KMSWMapIsoClass`, with the source-attribution obligations
listed below. This file does not claim Proposition 3.9. Independent source -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter
open scoped Topology ENNReal

local instance uibotLocalLimitFinalMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}

local instance uibotLocalLimitFinalBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: finite uniform-map, uniform-all-edge-root
geometric laws converge weakly along every diverging admissible size sequence
with fixed positive boundary lengths, using the proved comparison. -/
theorem uibotFiniteGeometricProbabilityLaw_tendsto
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) :
    Tendsto (fun k => uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k)
      hℓ hρ (hsize k) (hne k)) atTop
      (𝓝 (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved)) := by
  exact uibotFiniteGeometricProbabilityLaw_tendsto_of_comparison
    uibotDeterministicComparison_proved ℓ ρ hℓ hρ ns hns hsize hne

/-- Helper toward Proposition 3.9: the convergent finite geometric laws
have limit measure equal to the measurable iid KMSW pushforward, with the
deterministic comparison supplied by its proof. -/
theorem uibotGeometricLocalLimit_eq_iidPushforward
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) :
    letI _uibotLocalLimitFinalLimitNonempty :
        Nonempty (ProbabilityMeasure D39GeomRootedMapClass.{0}) :=
      ⟨uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved⟩
    ((limUnder atTop (fun k => uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k)
        hℓ hρ (hsize k) (hne k)) : ProbabilityMeasure D39GeomRootedMapClass.{0}) :
          Measure D39GeomRootedMapClass.{0}) =
      wholePlaneIIDCodeMeasure.map
        (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved) := by
  exact uibotGeometricLocalLimit_eq_iidPushforward_of_comparison
    uibotDeterministicComparison_proved ℓ ρ hℓ hρ ns hns hsize hne

/-- Helper toward Proposition 3.9: every fixed geometric ball-class mass
converges to its measurable whole-plane iid mass. The index `r` denotes
geometric radius `r + 1`; no comparison or drawing-independence premise remains. -/
theorem uibotFiniteGeometricBallLaw_tendsto
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
          (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) = b})) := by
  exact uibotMeasurableGeometricBallLaw_tendsto_of_comparison
    uibotDeterministicComparison_proved ℓ ρ hℓ hρ ns hns hsize hne r b

/-- Helper toward Proposition 3.9: the full finite drawing-independence
binder is already proved, for every stage and chronological root, from the
original exterior-face premises (`UIBOTD39BallStabilization8.lean:151`). -/
theorem uibotDrawingIndependence : UIBOTDrawingIndependence :=
  uibotDrawingIndependence_proved
















































































































end DirectedDistances.PaperProofs.Section3

end
