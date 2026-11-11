module

public import DirectedDistances.Recursive.BusemannWholeLineConditional

import Mathlib.Topology.Order.LeftRightLim

public section
namespace DirectedDistances.Recursive

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result.
The positive zero-at-zero half used in whole-line gluing. -/
@[expose] noncomputable def ldpBusemannWholeLinePositiveHalf (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocalZero :=
  ldpBusemannPositiveHalfPathZero n ω

/-- Helper toward Theorem 1.6; not a paper result.
The reflected sample sequence with a zero initial value. -/
@[expose] noncomputable def ldpBusemannNegativeSamples (ω : ℕ → Fin 3)
    (j : ℕ) : ℤ :=
  if j = 0 then 0 else busemannLDPMeasurableVersion ω (-((j : ℤ) + 1))

/-- Helper toward Theorem 1.6; not a paper result.
The reflected negative half, set to zero on its first step interval. -/
@[expose] noncomputable def ldpBusemannWholeLineNegativeHalfPath (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocal :=
  scaledIntegerPositiveHalfPath n (ldpBusemannNegativeSamples ω)

/-- Helper toward Theorem 1.6; not a paper result.
The reflected negative half is zero at its origin. -/
theorem ldpBusemannWholeLineNegativeHalfPath_zero (n : ℕ) (ω : ℕ → Fin 3) :
    (ldpBusemannWholeLineNegativeHalfPath n ω).1 ⟨0, le_rfl⟩ = 0 := by
  simp [ldpBusemannWholeLineNegativeHalfPath, scaledIntegerPositiveHalfPath,
    ldpBusemannNegativeSamples]

/-- Helper toward Theorem 1.6; not a paper result.
The reflected negative half as an input to zero-at-zero gluing. -/
@[expose] noncomputable def ldpBusemannWholeLineNegativeHalf (n : ℕ)
    (ω : ℕ → Fin 3) : CadlagLocalZero :=
  ⟨ldpBusemannWholeLineNegativeHalfPath n ω,
    ldpBusemannWholeLineNegativeHalfPath_zero n ω⟩

/-- Helper toward Theorem 1.6; not a paper result.
The negative half path samples the reflected integer sequence. -/
theorem ldpBusemannWholeLineNegativeHalfPath_apply (n : ℕ) (ω : ℕ → Fin 3)
    (s : Set.Ici (0 : ℝ)) :
    (ldpBusemannWholeLineNegativeHalfPath n ω).1 s =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (ldpBusemannNegativeSamples ω ⌊((n + 1 : ℕ) : ℝ) * (s : ℝ)⌋₊ : ℝ) := by
  rfl

private theorem subtype_coe_tendsto_left {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t : Set.Ici (0 : ℝ) => (t : ℝ))
      (nhdsWithin ⟨s, hs.le⟩ (Set.Iio ⟨s, hs.le⟩))
      (nhdsWithin s (Set.Iio s)) := by
  apply ContinuousWithinAt.tendsto_nhdsWithin
  · exact continuous_subtype_val.continuousWithinAt
  · intro t ht
    exact Set.mem_Iio.mpr (Subtype.coe_lt_coe.mpr ht)

private theorem scaledIntegerPositiveHalfPath_leftLim (n : ℕ) (z : ℕ → ℤ)
    {s : ℝ} (hs : 0 < s) :
    (scaledIntegerPositiveHalfPath n z).1.leftLim ⟨s, hs.le⟩ =
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (z (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ) := by
  have hne : NeBot (𝓝[<] (⟨s, hs.le⟩ : Set.Ici (0 : ℝ))) :=
    nhdsLT_neBot_of_exists_lt ⟨⟨0, le_rfl⟩, hs⟩
  have h := floorStep_left_limit (fun j : ℤ => (z j.toNat : ℝ))
    (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity) s
  have hc := h.comp (subtype_coe_tendsto_left hs)
  have hc' : Tendsto (fun t : Set.Ici (0 : ℝ) =>
      ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (z ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ))
      (nhdsWithin ⟨s, hs.le⟩ (Set.Iio ⟨s, hs.le⟩))
      (𝓝 (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
        (z (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ))) := by
    convert hc using 1
    · funext t
      congr 2
  change (fun t : Set.Ici (0 : ℝ) =>
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (z ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ)).leftLim ⟨s, hs.le⟩ = _
  exact leftLim_eq_of_tendsto (f := fun t : Set.Ici (0 : ℝ) =>
    ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (z ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ))
    (a := ⟨s, hs.le⟩)
    (y := ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
      (z (⌈((n + 1 : ℕ) : ℝ) * s⌉ - 1).toNat : ℝ))
    (h := hne) hc'

end DirectedDistances.Recursive
