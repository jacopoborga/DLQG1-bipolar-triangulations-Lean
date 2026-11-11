module

public import DirectedDistances.PaperProofs.Section4.FirstHitCodeDistanceIndependence
public import Mathlib.Probability.Independence.Conditional

/-! first-hit conditional independence of the past cut outputs given the uncentered future and
the past XDP distance; the renewal-time selection T_{m_k}, the T_0 branch and the infinite
source-map (F4c) identification are not treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory

/-- the first-hit conditional independence of the past cut outputs given the uncentered future
and the past XDP distance; the renewal-time selection T_{m_k}, the T_0 branch and the
infinite source-map (F4c) identification are not treated; not the paper result. -/
theorem firstHitPastAllCuts_condIndepFun_sigma (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    ProbabilityTheory.CondIndepFun (MeasurableSpace.comap B inferInstance)
      (Measurable.comap_le ((measurable_conditionedFirstHit_future r).prodMk
        ((measurable_firstHitPastXdpLength x r).comp
          ((measurable_stoppedMap r hr).comp measurable_pathCode))))
      (fun p => (C p).1) (fun p => (C p).2) μ := by
  classical
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let M := fun p => stoppedMap r hr (pathCode p)
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let C := firstHitPastAllCuts x r ∘ M
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hB : Measurable B := (measurable_conditionedFirstHit_future r).prodMk
    ((measurable_firstHitPastXdpLength x r).comp hM)
  have hC : Measurable C := (measurable_firstHitPastAllCuts x r).comp hM
  let κ := condDistrib (fun p => (C p).1) B μ ×ₖ
    condDistrib (fun p => (C p).2) B μ
  have hFactor : condDistrib C B μ =ᵐ[μ.map B] κ := by
    have hOld : condDistrib C B μ =ᵐ[μ.map B] fun b =>
        (condDistrib (fun p => (C p).1) B μ b).prod
          (condDistrib (fun p => (C p).2) B μ b) := by
      simpa only [μ, τ, M, Y, B, C] using
        firstHitPastAllCuts_conditionalIndependence x r hr
    filter_upwards [hOld] with b hb
    change condDistrib C B μ b =
      (condDistrib (fun p => (C p).1) B μ ×ₖ
        condDistrib (fun p => (C p).2) B μ) b
    rw [Kernel.prod_apply]
    exact hb
  have hPair := (condDistrib_ae_eq_iff_measure_eq_compProd
    hB.aemeasurable hC.aemeasurable κ).mp hFactor
  have hJoint : μ.map (fun p => (B p, C p)) =
      (Kernel.id ×ₖ
        (condDistrib (fun p => (C p).1) B μ ×ₖ
          condDistrib (fun p => (C p).2) B μ)) ∘ₘ μ.map B := by
    rw [← Measure.compProd_eq_comp_prod]
    exact hPair
  have hLeft : Measurable (fun p => (C p).1) := hC.fst
  have hRight : Measurable (fun p => (C p).2) := hC.snd
  exact (ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    (μ := μ) (f := fun p => (C p).1) (g := fun p => (C p).2)
    hLeft hRight hB).2 hJoint

/-- the first-hit conditional independence of the past cut outputs given the uncentered future
and the past XDP distance; the renewal-time selection T_{m_k}, the T_0 branch and the
infinite source-map (F4c) identification are not treated; not the paper result. This uses
the measurable past-length map B for the conditioning σ-algebra and records its almost-sure
identity with the code-distance conditioning variable, since the latter is only
almost-everywhere measurable. -/
theorem firstHitCodeDistance_condIndepFun_sigma (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    ProbabilityTheory.CondIndepFun (MeasurableSpace.comap B inferInstance)
      (Measurable.comap_le ((measurable_conditionedFirstHit_future r).prodMk
        ((measurable_firstHitPastXdpLength x r).comp
          ((measurable_stoppedMap r hr).comp measurable_pathCode))))
      (fun p => (C p).1) (fun p => (C p).2) μ ∧
      B =ᵐ[μ] firstHitCodeDistanceConditioning x r hr := by
  dsimp only
  constructor
  · exact firstHitPastAllCuts_condIndepFun_sigma x r hr
  · exact (firstHitCodeDistanceConditioning_ae_eq_pastConditioning x r hr).symm

end DirectedDistances.PaperProofs.Section4
