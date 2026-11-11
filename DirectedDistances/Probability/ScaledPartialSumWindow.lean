/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodFloorStep
public import DirectedDistances.Probability.SkorokhodJ1WindowPolish
public import DirectedDistances.Probability.HeavyTailMaximal
public import DirectedDistances.Probability.HeavyTailNoCenter

import Mathlib.MeasureTheory.Order.Lattice

/-! # Scaled partial sums on a finite càdlàg window -/

@[expose] public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*}

/-- Helper toward E-STABLE / Theorem 1.6
extended by zero to nonpositive integer indices; not the paper result. -/
def partialSumZ (X : ℕ → Ω → ℝ) (ω : Ω) : ℤ → ℝ := fun m =>
  if 0 < m then ∑ j ∈ Finset.range m.toNat, X j ω else 0

/-- Helper toward E-STABLE / Theorem 1.6
`[0,T]`, packaged using `floorStepWindow`; not the paper result. -/
noncomputable def scaledPartialSumWindow (X : ℕ → Ω → ℝ) (ν : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) (ω : Ω) : J1WindowD T hT :=
  ⟨floorStepWindow (partialSumZ X ω)
    (((n + 1 : ℕ) : ℝ) ^ (-(1 / ν))) ((n + 1 : ℕ) : ℝ)
    (by positivity) T hT⟩

/-- Helper toward E-STABLE / Theorem 1.6
window is its floored integer sample; not the paper result. -/
theorem scaledPartialSumWindow_apply (X : ℕ → Ω → ℝ) (ν : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) (ω : Ω) (t : J1Window T) :
    (scaledPartialSumWindow X ν n hT ω).path.1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
        partialSumZ X ω ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋ := by
  rfl

/-- Helper toward E-STABLE / Theorem 1.6
measurable when its increments are measurable; not the paper result. -/
theorem partialSumZ_measurable [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (m : ℤ) :
    Measurable (fun ω => partialSumZ X ω m) := by
  unfold partialSumZ
  split_ifs
  · exact Finset.measurable_sum _ fun j _ => hX j
  · exact measurable_const

private theorem partialSumZ_nat (X : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) :
    partialSumZ X ω (k : ℤ) = ∑ j ∈ Finset.range k, X j ω := by
  cases k with
  | zero => simp [partialSumZ]
  | succ k => simp [partialSumZ]

/-- Helper toward E-STABLE / Theorem 1.6
partial sums through `floor ((n + 1) * T)`; not the paper result. -/
noncomputable def scaledPartialSumWindow_sampleMax (X : ℕ → Ω → ℝ)
    (ν T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (⌊((n + 1 : ℕ) : ℝ) * T⌋₊ + 1)).sup'
    Finset.nonempty_range_add_one fun k =>
      |((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
        ∑ j ∈ Finset.range k, X j ω|

/-- Helper toward E-STABLE / Theorem 1.6
maximum over its possible floor indices; not the paper result. -/
theorem scaledPartialSumWindow_sup_eq_sampleMax (X : ℕ → Ω → ℝ)
    (ν : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T) (ω : Ω) :
    (⨆ t : J1Window T,
      |(scaledPartialSumWindow X ν n hT ω).path.1 t|) =
        scaledPartialSumWindow_sampleMax X ν T n ω := by
  classical
  let b : ℝ := (n + 1 : ℕ)
  let K : ℕ := ⌊b * T⌋₊
  let f : ℕ → ℝ := fun k =>
    |b ^ (-(1 / ν)) * ∑ j ∈ Finset.range k, X j ω|
  have hb : 0 < b := by dsimp [b]; positivity
  have hK : (K : ℝ) ≤ b * T := by
    dsimp [K]
    exact Nat.floor_le (mul_nonneg hb.le hT.le)
  have hupper : ∀ t : J1Window T,
      |(scaledPartialSumWindow X ν n hT ω).path.1 t| ≤
        (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one f := by
    intro t
    rw [scaledPartialSumWindow_apply]
    let q := b * (t : ℝ)
    have hq0 : 0 ≤ q := mul_nonneg hb.le t.property.1
    have hqT : q ≤ b * T := mul_le_mul_of_nonneg_left t.property.2 hb.le
    have hqK : Nat.floor q ≤ K := Nat.floor_mono hqT
    have hfloor : (Nat.floor q : ℤ) = ⌊q⌋ := Int.natCast_floor_eq_floor hq0
    rw [← hfloor, partialSumZ_nat]
    apply (Finset.le_sup'_iff (s := Finset.range (K + 1))
      (H := Finset.nonempty_range_add_one) (f := f)).2
    refine ⟨Nat.floor q, Finset.mem_range.mpr (Nat.lt_succ_of_le hqK), ?_⟩
    exact le_rfl
  have hbounded : BddAbove (Set.range fun t : J1Window T =>
      |(scaledPartialSumWindow X ν n hT ω).path.1 t|) := by
    refine ⟨(Finset.range (K + 1)).sup' Finset.nonempty_range_add_one f, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hupper t
  have : Nonempty (J1Window T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  apply le_antisymm
  · change (⨆ t : J1Window T,
      |(scaledPartialSumWindow X ν n hT ω).path.1 t|) ≤
        (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one f
    exact ciSup_le hupper
  · apply (Finset.sup'_le_iff (s := Finset.range (K + 1))
      (H := Finset.nonempty_range_add_one) (f := f)).2
    intro k hk
    have hkK : k ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    let t : J1Window T := ⟨(k : ℝ) / b, by
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hb.le
      · rw [div_le_iff₀ hb]
        exact (Nat.cast_le.mpr hkK).trans (by simpa [mul_comm] using hK)⟩
    have hbt : b * (t : ℝ) = k := by
      dsimp [t]
      field_simp
    have hfloor : ⌊b * (t : ℝ)⌋ = (k : ℤ) := by
      rw [hbt]
      simp
    have hvalue : f k = |(scaledPartialSumWindow X ν n hT ω).path.1 t| := by
      rw [scaledPartialSumWindow_apply, hfloor, partialSumZ_nat]
    rw [hvalue]
    exact le_ciSup_of_le hbounded t le_rfl

/-- Helper toward E-STABLE / Theorem 1.6
scaled partial-sum maximum; not the paper result. -/
theorem scaledPartialSumWindow_sampleMax_tight
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (ν C T : ℝ) (hT : 0 < T)
    (hν0 : 0 < ν) (hν2 : ν < 2) (_hνne : ν ≠ 1)
    (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hX : ∀ j, Measurable (X j))
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν))
    (hcenter : ν < 1 ∨
      (1 < ν ∧ Integrable (X 0) P ∧ ∫ ω, X 0 ω ∂P = 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ n : ℕ,
      P.real {ω | M < scaledPartialSumWindow_sampleMax X ν T n ω} ≤ ε := by
  have hC0 : 0 ≤ C := by
    have htail1 := hTail 1 (by norm_num)
    have hprob : 0 ≤ P.real {ω | 1 < |X 0 ω|} := by positivity
    have htail1' : P.real {ω | 1 < |X 0 ω|} ≤ C := by
      simpa using htail1
    linarith
  have hTail' : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ (C + 1) * x ^ (-ν) := by
    intro x hx
    calc P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν) := hTail x hx
      _ ≤ (C + 1) * x ^ (-ν) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
  have hbounds : ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ B : ℝ, 1 ≤ B → P.real {ω | ∃ j ≤ k,
        B * (k : ℝ) ^ (1 / ν) <
          |∑ i ∈ Finset.range j, X i ω|} ≤ D * B ^ (-ν) := by
    rcases hcenter with hsmall | ⟨hlarge, hInt, hmean⟩
    · exact heavyTail_maximal_lt_one (P := P) (xi := X) hX hind hident ν
        (C + 1) hν0 hsmall (by positivity) hTail'
    · exact heavyTail_maximal (P := P) (xi := X) hX hind hident ν
        (C + 1) hν0 hν2 (by positivity) hTail'
        (Or.inr ⟨hlarge, hInt, hmean⟩)
  obtain ⟨D, hD, hmax⟩ := hbounds
  intro ε hε
  let A : ℝ := (D / ε) ^ (1 / ν) + 1
  have hratio : 0 < D / ε := div_pos hD hε
  have hroot : 0 ≤ (D / ε) ^ (1 / ν) := Real.rpow_nonneg hratio.le _
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hA0 : 0 < A := by linarith
  have hrootA : (D / ε) ^ (1 / ν) ≤ A := by
    dsimp [A]
    linarith
  have hrootν : ((D / ε) ^ (1 / ν)) ^ ν = D / ε := by
    rw [← Real.rpow_mul hratio.le, one_div,
      inv_mul_cancel₀ hν0.ne', Real.rpow_one]
  have hAν : D / ε ≤ A ^ ν := by
    calc D / ε = ((D / ε) ^ (1 / ν)) ^ ν := hrootν.symm
      _ ≤ A ^ ν := Real.rpow_le_rpow hroot hrootA hν0.le
  have hAν0 : 0 < A ^ ν := Real.rpow_pos_of_pos hA0 _
  have hDbound : D * A ^ (-ν) ≤ ε := by
    rw [Real.rpow_neg hA0.le, ← div_eq_mul_inv]
    apply (div_le_iff₀ hAν0).2
    calc D = (D / ε) * ε := by field_simp
      _ ≤ A ^ ν * ε := mul_le_mul_of_nonneg_right hAν hε.le
      _ = ε * A ^ ν := by ring
  let M : ℝ := A * T ^ (1 / ν)
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos hA0 (Real.rpow_pos_of_pos hT _)
  refine ⟨M, ?_⟩
  intro n
  let b : ℝ := (n + 1 : ℕ)
  let K : ℕ := ⌊b * T⌋₊
  let p : ℝ := 1 / ν
  have hb : 0 < b := by dsimp [b]; positivity
  have hp : 0 < p := by dsimp [p]; exact one_div_pos.mpr hν0
  have hK : (K : ℝ) ≤ b * T := by
    dsimp [K]
    exact Nat.floor_le (mul_nonneg hb.le hT.le)
  have hget : ∀ ω, M < scaledPartialSumWindow_sampleMax X ν T n ω →
      ∃ k, k ≤ K ∧ M < |b ^ (-p) *
        ∑ j ∈ Finset.range k, X j ω| := by
    intro ω hω
    change M < (Finset.range (K + 1)).sup'
      Finset.nonempty_range_add_one (fun k =>
        |b ^ (-p) * ∑ j ∈ Finset.range k, X j ω|) at hω
    obtain ⟨k, hk, hval⟩ := (Finset.lt_sup'_iff
      (s := Finset.range (K + 1)) (H := Finset.nonempty_range_add_one)
      (f := fun k => |b ^ (-p) * ∑ j ∈ Finset.range k, X j ω|)).mp hω
    exact ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk), hval⟩
  by_cases hK0 : K = 0
  · have hempty : {ω | M < scaledPartialSumWindow_sampleMax X ν T n ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      obtain ⟨k, hk, hval⟩ := hget ω hω
      have hk0 : k = 0 := by omega
      subst k
      simp at hval
      linarith
    rw [hempty]
    simpa using hε.le
  · have hKpos : 1 ≤ K := by omega
    have hKpow : (K : ℝ) ^ p ≤ b ^ p * T ^ p := by
      calc (K : ℝ) ^ p ≤ (b * T) ^ p :=
          Real.rpow_le_rpow (by positivity) hK hp.le
        _ = b ^ p * T ^ p := by rw [Real.mul_rpow hb.le hT.le]
    have hthreshold : A * (K : ℝ) ^ p ≤ M * b ^ p := by
      calc A * (K : ℝ) ^ p ≤ A * (b ^ p * T ^ p) :=
          mul_le_mul_of_nonneg_left hKpow hA0.le
        _ = M * b ^ p := by dsimp [M, p]; ring
    have hbpow : 0 < b ^ p := Real.rpow_pos_of_pos hb _
    have hsubset : {ω | M < scaledPartialSumWindow_sampleMax X ν T n ω} ⊆
        {ω | ∃ j ≤ K, A * (K : ℝ) ^ p <
          |∑ i ∈ Finset.range j, X i ω|} := by
      intro ω hω
      obtain ⟨k, hk, hval⟩ := hget ω hω
      have hscaled : M < (b ^ p)⁻¹ *
          |∑ i ∈ Finset.range k, X i ω| := by
        simpa [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hb _),
          Real.rpow_neg hb.le] using hval
      have hraw : M * b ^ p < |∑ i ∈ Finset.range k, X i ω| := by
        calc M * b ^ p = b ^ p * M := by ring
          _ < b ^ p * ((b ^ p)⁻¹ *
              |∑ i ∈ Finset.range k, X i ω|) :=
            mul_lt_mul_of_pos_left hscaled hbpow
          _ = |∑ i ∈ Finset.range k, X i ω| := by field_simp
      refine ⟨k, hk, ?_⟩
      exact lt_of_le_of_lt hthreshold hraw
    exact (measureReal_mono hsubset).trans (hmax K hKpos A hA1 |>.trans hDbound)

/-- Helper toward E-STABLE / Theorem 1.6
from its finite maximum representation; not the paper result. -/
theorem scaledPartialSumWindow_sup_measurable [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (ν : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) :
    Measurable (fun ω => ⨆ t : J1Window T,
      |(scaledPartialSumWindow X ν n hT ω).path.1 t|) := by
  have hfun : (fun ω => ⨆ t : J1Window T,
      |(scaledPartialSumWindow X ν n hT ω).path.1 t|) =
      fun ω => scaledPartialSumWindow_sampleMax X ν T n ω := by
    funext ω
    exact scaledPartialSumWindow_sup_eq_sampleMax X ν n hT ω
  rw [hfun]
  unfold scaledPartialSumWindow_sampleMax
  change Measurable (fun ω =>
    (Finset.range (⌊((n + 1 : ℕ) : ℝ) * T⌋₊ + 1)).sup'
      Finset.nonempty_range_add_one (fun k =>
        |((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
          ∑ j ∈ Finset.range k, X j ω|))
  apply Finset.measurable_range_sup''
  intro k hk
  exact continuous_abs.measurable.comp
    (((measurable_const.mul (Finset.measurable_sum _ fun j _ => hX j))))

end DirectedDistances.Probability
