/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.ScalingPathMarginalsIdentified
public import DirectedDistances.Recursive.BusemannStableHalfIdentification
import all DirectedDistances.PaperProofs.Section1.ScalingPathMarginalsIdentified
import all DirectedDistances.Recursive.BusemannStableHalfIdentification

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/



















public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.Probability DirectedDistances.RandomWalk
open DirectedDistances.Recursive
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result. The joint characteristic
function of consecutive increments for every ordered partition starting at zero.
Empty partitions and repeated times are included. The product specifies stationary
independent increments, with characteristic exponent `Ψ` and zero drift location. -/
@[expose] def StablePartitionLaw (Ψ : ℝ → ℂ)
    (μ : ProbabilityMeasure CadlagLocalZero) : Prop :=
  ∀ (k : ℕ) (t : Fin (k + 1) → Set.Ici (0 : ℝ)),
    (t 0 : ℝ) = 0 → Monotone t → ∀ u : Fin k → ℝ,
    (∫ x : CadlagLocalZero, Complex.exp
      (((∑ j : Fin k, u j *
        (x.1.1 (t j.succ) - x.1.1 (t j.castSucc)) : ℝ) : ℂ) * Complex.I)
        ∂(μ : Measure CadlagLocalZero)) =
      ∏ j : Fin k, Complex.exp
        (-((((t j.succ : ℝ) - (t j.castSucc : ℝ) : ℝ) : ℂ) * Ψ (u j)))

/-- Helper toward Theorem 1.6; not a paper result. Full process exponent
characterization for the LDP positive half. For `α = 2/3`, a negative stable
subordinator has `Ψ(u) = c |u|^α (1 + i tan(πα/2) sign u)`;
`tan(π/3) = √3`. Here `c = a/2`, whereas the symmetric negative half has
coefficient `a`. Positivity excludes the degenerate process. There is no location
term. This predicate records the exponent characterization, not a separate
almost-sure antitonicity proof. -/
@[expose] def LdpStableHalfLaw (a : ℝ)
    (μ : ProbabilityMeasure CadlagLocalZero) : Prop :=
  0 < a ∧ StablePartitionLaw (fun u =>
    ((a / 2 : ℝ) : ℂ) * (|u| ^ (2 / 3 : ℝ) : ℝ) *
      (1 + Complex.I * (Real.sqrt 3 : ℂ) *
        ((if 0 < u then (1 : ℝ) else if u < 0 then -1 else 0) : ℂ))) μ

/-- Helper toward Theorem 1.6; not a paper result. Full process exponent
characterization for the SDP positive half. The spectrally positive convention is
`Ψ(u) = c |u|^α (1 - i tan(πα/2) sign u)` with `α = 4/3`;
`tan(2π/3) = -√3`, so the factor is `1 + i √3 sign u`. Here `c = b/2`,
whereas the symmetric negative half has coefficient `b`. There is no location
term. This predicate records the exponent characterization, not a separate
almost-sure nonnegative-jump proof. -/
@[expose] def SdpStableHalfLaw (b : ℝ)
    (μ : ProbabilityMeasure CadlagLocalZero) : Prop :=
  0 < b ∧ StablePartitionLaw (fun u =>
    ((b / 2 : ℝ) : ℂ) * (|u| ^ (4 / 3 : ℝ) : ℝ) *
      (1 + Complex.I * (Real.sqrt 3 : ℂ) *
        ((if 0 < u then (1 : ℝ) else if u < 0 then -1 else 0) : ℂ))) μ

/-- Helper toward Theorem 1.6; not a paper result. Symmetric strictly stable
process exponent characterization: `Ψ(u) = c |u|^α`, with `0 < α ≤ 2`, `c > 0`,
and no location term. The partition formula specifies the entire process law,
not merely its marginal at time one. -/
@[expose] def SymmetricStableProcessLaw (α c : ℝ)
    (μ : ProbabilityMeasure CadlagLocalZero) : Prop :=
  0 < α ∧ α ≤ 2 ∧ 0 < c ∧
    StablePartitionLaw (fun u => (c : ℂ) * (|u| ^ α : ℝ)) μ

/-- Helper toward Theorem 1.6; not a paper result. Probability law of the
identified LDP literal floor path under the whole-plane code probability. -/
@[expose] noncomputable def identifiedLDPScalingLaw (n : ℕ) :
    ProbabilityMeasure WholeLineCadlag :=
  ⟨wholePlaneIIDCodeMeasure.map (identifiedLDPScalingPath n),
    (Measure.isProbabilityMeasure_map_iff
      (aemeasurable_identifiedLDPScalingPath n)).2 inferInstance⟩

/-- Helper toward Theorem 1.6; not a paper result. Probability law of the
identified SDP literal floor path under the whole-plane code probability. -/
@[expose] noncomputable def identifiedSDPScalingLaw (n : ℕ) :
    ProbabilityMeasure WholeLineCadlag :=
  ⟨wholePlaneIIDCodeMeasure.map (identifiedSDPScalingPath n),
    (Measure.isProbabilityMeasure_map_iff
      (aemeasurable_identifiedSDPScalingPath n)).2 inferInstance⟩

/-- Helper toward Theorem 1.6; not a paper result. Exact LDP law transport. -/
theorem identifiedLDPScalingLaw_eq (n : ℕ) :
    identifiedLDPScalingLaw n = ldpBusemannWholeLineLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  exact identifiedLDPScalingPath_map_eq_wholeLineLaw n

/-- Helper toward Theorem 1.6; not a paper result. Exact SDP law transport. -/
theorem identifiedSDPScalingLaw_eq (n : ℕ) :
    identifiedSDPScalingLaw n = sdpBusemannWholeLineLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  exact identifiedSDPScalingPath_map_eq_wholeLineLaw n









@[expose] def thm16Statement : Prop :=
  ∃ (a b : ℝ) (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
    LdpStableHalfLaw a μL ∧ SymmetricStableProcessLaw (2 / 3) a νL ∧
    SdpStableHalfLaw b μS ∧ SymmetricStableProcessLaw (4 / 3) b νS ∧
    Tendsto identifiedLDPScalingLaw atTop
      (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
    Tendsto identifiedSDPScalingLaw atTop
      (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero))

/-- Helper toward Theorem 1.6; not a paper result. Positive-half partition
identification is unconditional for every limit of the actual positive laws. -/
theorem positiveHalfLimits_stable :
    (∀ μ, Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ) →
      LdpStableHalfLaw ldpStableHalfScale μ) ∧
    (∀ μ, Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ) →
      SdpStableHalfLaw sdpStableHalfScale μ) := by
  constructor
  · intro μ hμ
    exact ⟨ldpStableHalfScale_pos,
      ldpBusemannPositiveHalfLimit_partition_fin hμ⟩
  · intro μ hμ
    exact ⟨sdpStableHalfScale_pos,
      sdpBusemannPositiveHalfLimit_partition_fin hμ⟩

/-- Helper toward Theorem 1.6; not a paper result. Unconditional functional
convergence of both identified literal floor laws to independent-product gluings,
retaining positive-half convergence and actual shifted-negative-half convergence.
No negative-half stable identification is assumed. -/
theorem identifiedScalingLaws_tendsto :
    ∃ (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
      Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μL) ∧
      LdpBusemannWholeLineNegativeHalfConverges νL ∧
      Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μS) ∧
      SdpBusemannWholeLineNegativeHalfConverges νS ∧
      Tendsto identifiedLDPScalingLaw atTop
        (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
      Tendsto identifiedSDPScalingLaw atTop
        (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero)) := by
  obtain ⟨μL, νL, hL, _, hnL, _, hcL⟩ := ldpBusemannWholeLineLaw_tendsto_ldpCode
  obtain ⟨μS, νS, hS, _, hnS, _, hcS⟩ := sdpBusemannWholeLineLaw_tendsto_sdpCode
  refine ⟨μL, νL, μS, νS, hL, hnL, hS, hnS, ?_, ?_⟩
  · exact hcL.congr' (Eventually.of_forall fun n =>
      (identifiedLDPScalingLaw_eq n).symm)
  · exact hcS.congr' (Eventually.of_forall fun n =>
      (identifiedSDPScalingLaw_eq n).symm)

/-- Helper toward Theorem 1.6; not a paper result. The exact remaining
partition-identification obligation, on every actual shifted-negative-half limit.
The exponents have the full shared scales, not the positive-half half-coefficients.
This is an openly stated proof obligation, not an assumed external theorem. -/
@[expose] def NegativeHalfPartitionIdentification : Prop :=
  (∀ ν, LdpBusemannWholeLineNegativeHalfConverges ν →
    StablePartitionLaw
      (fun u => (ldpStableHalfScale : ℂ) * (|u| ^ (2 / 3 : ℝ) : ℝ)) ν) ∧
  (∀ ν, SdpBusemannWholeLineNegativeHalfConverges ν →
    StablePartitionLaw
      (fun u => (sdpStableHalfScale : ℂ) * (|u| ^ (4 / 3 : ℝ) : ℝ)) ν)

/-- CONDITIONAL reduction toward Theorem 1.6; not a paper result. The sole
premise identifies the full partition exponents of the actual negative-half
limits. Positive-half identification and whole-line functional convergence are
proved unconditionally above. The conclusion has the representation and coverage
limits explicitly documented in `thm16Statement`. -/
theorem thm16_of_negativeHalves (hneg : NegativeHalfPartitionIdentification) :
    thm16Statement := by
  obtain ⟨μL, νL, μS, νS, hL, hnL, hS, hnS, hcL, hcS⟩ :=
    identifiedScalingLaws_tendsto
  exact ⟨ldpStableHalfScale, sdpStableHalfScale, μL, νL, μS, νS,
    positiveHalfLimits_stable.1 μL hL,
    ⟨by norm_num, by norm_num, ldpStableHalfScale_pos, hneg.1 νL hnL⟩,
    positiveHalfLimits_stable.2 μS hS,
    ⟨by norm_num, by norm_num, sdpStableHalfScale_pos, hneg.2 νS hnS⟩,
    hcL, hcS⟩

end DirectedDistances.PaperProofs.Section1
