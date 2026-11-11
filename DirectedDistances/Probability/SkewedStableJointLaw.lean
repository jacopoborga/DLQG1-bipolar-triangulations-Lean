module

public import DirectedDistances.Probability.SkewedStableJointBlocks
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.LevyConvergence

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Scalar finite-dimensional helper toward E-STABLE / thm-busemann-conv
consecutive disjoint-block normalized iid sums to the product skewed stable law; no functional
convergence, path tightness or Busemann law identification is claimed; not the paper result.
The limit law μlim is supplied as a hypothesis with the product characteristic function; its
existence is not established here (see SkewedStableLimitExists.lean). -/
theorem tendsto_skewStable_blockVector_law_of_charFun
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hX : ∀ i, Measurable (X i)) {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν))
    {k : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (hmono : Monotone t)
    (μlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (hμlim : ∀ θ : EuclideanSpace ℝ (Fin k),
      charFun (μlim : Measure _) θ = ∏ i : Fin k, Complex.exp
        (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
          ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ))))) :
    Tendsto
      (fun n : ℕ ↦
        (⟨P.map (skewStableBlockVector (k := k) (t := t) (ν := ν) X n),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))))
      atTop (@nhds (ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
        MeasureTheory.ProbabilityMeasure.instTopologicalSpace μlim) := by
  apply (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2
  intro θ
  rw [hμlim θ]
  simpa only [ProbabilityMeasure.coe_mk] using
    (tendsto_charFun_skewStable_blockVector hindep hident hX hν hexp ht0 hmono θ)

end DirectedDistances.Probability
