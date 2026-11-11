/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalPrefixMeasurability
public import DirectedDistances.RandomWalk.ConditionedVectorPastRegeneration

/-! # Actual source-law regeneration on a deterministic renewal rank slice

Internal assembly of the three itemized conditions in the proof of Lemma 4.9
are proved measurable in the actual finite-prefix sigma algebra, then the
full source RN law supplies the unnormalized future law on their intersection
with the future lower barrier. No random renewal time is defined here. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- The literal first two rank conditions of Lemma 4.9 are measurable in the
sigma algebra of the actual `Fin (n+1)` prefix, with no measurability premise. -/
theorem measurableSet_renewal_prefix_condition_fin_comap (m n : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) inferInstance]
      {p : ℕ → ℤ × ℤ |
        (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
          (((Finset.Icc 1 n).filter fun j =>
            (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
              ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)} := by
  let E : Set (ℕ → ℤ × ℤ) :=
    {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)}
  let P : (ℕ → ℤ × ℤ) → (Fin (n + 1) → ℤ × ℤ) := fun p j => p j.val
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨P '' E, (Set.to_countable (P '' E)).measurableSet, ?_⟩
  ext p
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hprefix : ∀ i, i ≤ n → q i = p i := by
      intro i hi
      exact congrFun hpq ⟨i, Nat.lt_succ_of_le hi⟩
    exact (renewal_prefix_condition_congr q p m n hprefix).mp hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- The three literal finite-rank conditions in the proof of Lemma 4.9 give
the actual full two-dimensional unnormalized future law. Only the source
probability law and its unchanged all-horizon RN definition are inputs. -/
theorem conditionedSource_renewal_rank_slice_restrict
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (m n : ℕ) :
    let P : Set (ℕ → ℤ × ℤ) :=
      {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        (((Finset.Icc 1 n).filter fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)}
    let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
    (ν.restrict (P ∩ B)).map (fun p => fun k => p (n + k) - p n) =
      ν (P ∩ B) • ν := by
  exact conditionedSource_past_restrict_regeneration ν hRN n _
    (measurableSet_renewal_prefix_condition_fin_comap m n)

/-- The same actual future-law identity on the literal global-success rank
slice. The global and truncated success counts are identified in the proof,
not supplied as an extra premise. No claim about the special time `T₀` is made. -/
theorem conditionedSource_global_rank_slice_restrict
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (m n : ℕ) :
    let E : Set (ℕ → ℤ × ℤ) :=
      {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        (((Finset.Icc 1 n).filter fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → (p j).1 ≤ (p i).1).card = m) ∧
        (∀ i, n ≤ i → (p n).1 ≤ (p i).1)}
    (ν.restrict E).map (fun p => fun k => p (n + k) - p n) = ν E • ν := by
  let E : Set (ℕ → ℤ × ℤ) :=
    {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1).card = m) ∧
      (∀ i, n ≤ i → (p n).1 ≤ (p i).1)}
  let P : Set (ℕ → ℤ × ℤ) :=
    {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)}
  let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
  have hset : E = P ∩ B := by
    ext p
    constructor
    · rintro ⟨ha, hcard, hbar⟩
      obtain ⟨ha', hcard', hbar'⟩ :=
        (renewal_success_rank_factorization (fun j => (p j).1)
          (fun j => (p j).2) m n).mp ⟨ha, hcard, hbar⟩
      exact ⟨⟨ha', hcard'⟩, fun k => hbar' (n + k) (Nat.le_add_right n k)⟩
    · rintro ⟨⟨ha, hcard⟩, hbar⟩
      have hbar' : ∀ i, n ≤ i → (p n).1 ≤ (p i).1 := by
        intro i hi
        simpa only [Nat.add_sub_of_le hi] using hbar (i - n)
      exact (renewal_success_rank_factorization (fun j => (p j).1)
        (fun j => (p j).2) m n).mpr ⟨ha, hcard, hbar'⟩
  change (ν.restrict E).map (fun p => fun k => p (n + k) - p n) = ν E • ν
  rw [hset]
  exact conditionedSource_renewal_rank_slice_restrict ν hRN m n

end DirectedDistances.RandomWalk
