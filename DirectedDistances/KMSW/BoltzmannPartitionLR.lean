/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoltzmannRightLawProcedure
public import DirectedDistances.PlanarMap.FiniteBoltzmannMapLaw
import DirectedDistances.KMSW.KMSWProcedureReading

/-! # Fixed-left-length Boltzmann partition bounds

Helper toward `def-boltzmann-lr` / `lem-lr-ind` -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open scoped ENNReal

/-- The fixed-left-length partition is bounded by the partition over all
left boundary lengths, by including its map classes into the dependent union.
Helper toward `def-boltzmann-lr` / `lem-lr-ind` -/
theorem boltzmannPartition_le_right (ℓ r : ℕ) :
    boltzmannPartition ℓ r ≤ rightBoltzmannPartition r := by
  classical
  let f : BoltzmannSpace ℓ r → AllBoltzmannSpace r := fun q => ⟨ℓ, q⟩
  have hf : Function.Injective f := by
    intro x y h
    rcases Sigma.mk.inj_iff.mp h with ⟨_, hxy⟩
    exact eq_of_heq hxy
  calc
    boltzmannPartition ℓ r =
        ∑' x : BoltzmannSpace ℓ r, allBoltzmannWeight (f x) := by
      simp [boltzmannPartition, f, allBoltzmannWeight, boltzmannWeight]
    _ ≤ ∑' q : AllBoltzmannSpace r, allBoltzmannWeight q :=
      tsum_comp_le_tsum_of_injective hf allBoltzmannWeight
    _ = rightBoltzmannPartition r := by
      rfl






theorem boltzmannPartition_ne_top (ℓ r : ℕ) (hr : 1 ≤ r) :
    boltzmannPartition ℓ r ≠ ⊤ := by
  apply ne_of_lt
  exact lt_of_le_of_lt (boltzmannPartition_le_right ℓ r)
    (lt_top_iff_ne_top.mpr (rightBoltzmannPartition_pos_lt_top r hr).2)





theorem boltzmannPartition_ne_zero (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) :
    boltzmannPartition ℓ r ≠ 0 := by
  classical
  let a : ℕ := ℓ - 1
  let b : ℕ := r - 1
  let N : ℕ := 2 * a + 2 * b + 1
  let Zfun : ℕ → ℤ × ℤ := fun k =>
    if k < a then (0, (k : ℤ))
    else if k < 2 * a + b then ((k - a : ℕ), (2 * a : ℤ) - k)
    else ((3 * a + 2 * b - k : ℕ), -(b : ℤ))
  let Z : Fin N → ℤ × ℤ := fun k => Zfun k.val
  have hN : N = 2 * a + 2 * b + 1 := rfl
  have hlen : N - 1 = 2 * a + 2 * b := by simp [hN]
  have hℓ' : ℓ = a + 1 := by dsimp [a]; omega
  have hr' : r = b + 1 := by dsimp [b]; omega
  have hstart : Z ⟨0, by dsimp [N]; omega⟩ = (0, 0) := by
    change Zfun 0 = (0, 0)
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · simp [Zfun, ha, hb]
      · have hbpos : 0 < b := by omega
        simp [Zfun, ha, hbpos]
    · have hapos : 0 < a := by omega
      simp [Zfun, hapos]
  have hstepsNat : ∀ k, k < 2 * a + 2 * b →
      Zfun (k + 1) - Zfun k ∈ ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
    intro k hk
    by_cases h₁ : k < a
    · by_cases h₂ : k + 1 < a
      · simp [Zfun, h₁, h₂, Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq]
      · have heq : k + 1 = a := by omega
        have hnext : ¬ k + 1 < a := by omega
        have hnext' : k + 1 < 2 * a + b := by omega
        simp [Zfun, h₁, hnext, hnext', Set.mem_insert_iff,
          Set.mem_singleton_iff, Prod.mk.injEq]; omega
    · have h₁' : ¬ k + 1 < a := by omega
      by_cases h₂ : k < 2 * a + b
      · by_cases h₃ : k + 1 < 2 * a + b
        · simp [Zfun, h₁, h₁', h₂, h₃, Set.mem_insert_iff,
            Set.mem_singleton_iff, Prod.mk.injEq]; omega
        · have heq : k + 1 = 2 * a + b := by omega
          have hnext : ¬ k + 1 < 2 * a + b := by omega
          simp [Zfun, h₁, h₁', h₂, hnext, Set.mem_insert_iff,
            Set.mem_singleton_iff, Prod.mk.injEq]; omega
      · have h₂' : ¬ k + 1 < 2 * a + b := by omega
        simp [Zfun, h₁, h₁', h₂, h₂', Set.mem_insert_iff,
          Set.mem_singleton_iff, Prod.mk.injEq]; omega
  have hsteps : ∀ i : Fin (N - 1),
      Z ⟨i.val + 1, by omega⟩ - Z ⟨i.val, by omega⟩ ∈
        ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
    intro i
    have hi : i.val < 2 * a + 2 * b := by rw [← hlen]; exact i.isLt
    simpa [Z] using hstepsNat i.val hi
  have hend : Z ⟨N - 1, by omega⟩ = ((ℓ : ℤ) - 1, -(r : ℤ) + 1) := by
    change Zfun (N - 1) = ((ℓ : ℤ) - 1, -(r : ℤ) + 1)
    rw [hlen]
    have hn₁ : ¬ 2 * a + 2 * b < a := by omega
    have hn₂ : ¬ 2 * a + 2 * b < 2 * a + b := by omega
    simp [Zfun, hn₁, hn₂, hℓ', hr']
    omega
  have hcone : ∀ k : Fin N, 0 ≤ (Z k).1 ∧ -(r : ℤ) + 1 ≤ (Z k).2 := by
    intro k
    by_cases h₁ : k.val < a
    · constructor
      · change 0 ≤ (Zfun k.val).1
        simp [Zfun, h₁]
      · change -(r : ℤ) + 1 ≤ (Zfun k.val).2
        simp [Zfun, h₁]
        rw [hr']
        norm_cast
        omega
    · by_cases h₂ : k.val < 2 * a + b
      · constructor
        · change 0 ≤ (Zfun k.val).1
          simp [Zfun, h₁, h₂]
        · change -(r : ℤ) + 1 ≤ (Zfun k.val).2
          simp [Zfun, h₁, h₂]
          rw [hr']
          omega
      · have hk : k.val ≤ 2 * a + 2 * b := by
          have := k.isLt
          dsimp [N] at this
          omega
        constructor
        · change 0 ≤ (Zfun k.val).1
          simp [Zfun, h₁, h₂]
        · change -(r : ℤ) + 1 ≤ (Zfun k.val).2
          simp [Zfun, h₁, h₂]
          rw [hr']
          omega
  let c : KMSWWalkClass ℓ r N :=
    walkClassOfWalk Z (by dsimp [N]; omega) hstart hsteps hend hcone
  have hn : 1 ≤ N := by dsimp [N]; omega
  let ω : BoltzmannSpace ℓ r := ⟨N, kmswProcedureEquiv ℓ r N hn c⟩
  intro hzero
  have hall : ∀ x : BoltzmannSpace ℓ r, boltzmannWeight x = 0 := by
    rw [boltzmannPartition] at hzero
    exact tsum_eq_zero_iff.mp hzero
  have hbase : (1 / 3 : ℝ≥0∞) ≠ 0 := by norm_num
  have hweight : boltzmannWeight ω ≠ 0 := by
    simp only [boltzmannWeight, ω]
    exact pow_ne_zero N hbase
  exact hweight (hall ω)




theorem boltzmannPartition_ne_zero_and_ne_top (ℓ r : ℕ)
    (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) :
    boltzmannPartition ℓ r ≠ 0 ∧ boltzmannPartition ℓ r ≠ ⊤ := by
  exact ⟨boltzmannPartition_ne_zero ℓ r hℓ hr, boltzmannPartition_ne_top ℓ r hr⟩

end DirectedDistances.KMSW
