/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.BusemannConvergenceIdentified
import all DirectedDistances.Recursive.BusemannStableNegativeHalfIdentification

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/












public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory ProbabilityTheory
open DirectedDistances.Probability DirectedDistances.Recursive

/-- Helper toward Theorem 1.6; not a paper result. Every actual LDP negative-half
limit satisfies the full symmetric partition law with the shared positive scale.
Empty partitions and repeated times are included. -/
theorem ldpNegativeHalf_stablePartitionLaw
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : LdpBusemannWholeLineNegativeHalfConverges ν) :
    StablePartitionLaw
      (fun u => (ldpStableHalfScale : ℂ) * (|u| ^ (2 / 3 : ℝ) : ℝ)) ν := by
  intro k t ht0 ht u
  let s : ℕ → Set.Ici (0 : ℝ) := fun j => t ⟨min j k, by omega⟩
  have hs0 : (s 0 : ℝ) = 0 := by simpa [s] using ht0
  have hs : Monotone s := fun i j hij => ht (min_le_min_right k hij)
  have h := ldpBusemannNegativeHalfLimit_partition hν k s hs0 hs u
  have hsucc (j : Fin k) : s (j.val + 1) = t j.succ := by
    dsimp [s]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  have hcast (j : Fin k) : s j.val = t j.castSucc := by
    dsimp [s]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  simpa only [hsucc, hcast, ← ldpStableHalfScale_eq_negativeHalfLdpScale] using h

/-- Helper toward Theorem 1.6; not a paper result. Every actual SDP negative-half
limit satisfies the full symmetric partition law with the shared positive scale.
Empty partitions and repeated times are included. -/
theorem sdpNegativeHalf_stablePartitionLaw
    {ν : ProbabilityMeasure CadlagLocalZero}
    (hν : SdpBusemannWholeLineNegativeHalfConverges ν) :
    StablePartitionLaw
      (fun u => (sdpStableHalfScale : ℂ) * (|u| ^ (4 / 3 : ℝ) : ℝ)) ν := by
  intro k t ht0 ht u
  let s : ℕ → Set.Ici (0 : ℝ) := fun j => t ⟨min j k, by omega⟩
  have hs0 : (s 0 : ℝ) = 0 := by simpa [s] using ht0
  have hs : Monotone s := fun i j hij => ht (min_le_min_right k hij)
  have h := sdpBusemannNegativeHalfLimit_partition hν k s hs0 hs u
  have hsucc (j : Fin k) : s (j.val + 1) = t j.succ := by
    dsimp [s]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  have hcast (j : Fin k) : s j.val = t j.castSucc := by
    dsimp [s]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  simpa only [hsucc, hcast, ← sdpStableHalfScale_eq_negativeHalfSdpScale] using h

/-- Helper toward Theorem 1.6; not a paper result. Both actual shifted
negative-half limits have their full shared-scale symmetric stable exponents. -/
theorem negativeHalfPartitionIdentification_holds : NegativeHalfPartitionIdentification :=
  ⟨fun _ hν => ldpNegativeHalf_stablePartitionLaw hν,
    fun _ hν => sdpNegativeHalf_stablePartitionLaw hν⟩

/-- Helper toward Theorem 1.6; not a paper result. Unconditional realization of
the existing identified-law convergence statement, with its documented topology,
path-support, and geometric-identification coverage limits. -/
theorem thm16_holds : thm16Statement :=
  thm16_of_negativeHalves negativeHalfPartitionIdentification_holds

end DirectedDistances.PaperProofs.Section1
