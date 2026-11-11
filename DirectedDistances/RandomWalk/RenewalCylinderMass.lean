/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorBarrierJoint
import Mathlib.Tactic.FieldSimp

/-! Supporting lemmas for paper labels `lem-walk-bdy-sum` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Intersecting a genuine source-word cylinder with the future barrier above
its own endpoint cancels the conditioned endpoint weight. Killed words have
zero mass; the horizon-zero empty word is included. -/
theorem conditionedSource_prefix_inter_endpoint_barrier_mass
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (n : ℕ) (w : Fin n → Fin 3) :
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
    ν.real (C ∩ {p | ∀ j, (p n).1 ≤ (p (n + j)).1}) =
      if ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1 then
        ((3 : ℝ) ^ n)⁻¹ else 0 := by
  classical
  let C : Set (ℕ → ℤ × ℤ) :=
    {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
  let B : Set (ℕ → ℤ × ℤ) := {p | ∀ j, (p n).1 ≤ (p (n + j)).1}
  have hRN0 : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) /
              (((0 : ℕ) : ℝ) + 1)) else 0) := by
    simpa only [Nat.cast_zero] using hRN
  have hatom := conditionedSource_prefix_atom 0 0 ν hRN0 n w
  simp only [Nat.cast_zero] at hatom
  by_cases hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1
  · rw [ite_eq_left hw]
    let X : ℕ := (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1.toNat
    have hX : (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 = (X : ℤ) :=
      (Int.toNat_of_nonneg (hw (Fin.last n))).symm
    have hp (p : ℕ → ℤ × ℤ) (hc : p ∈ C) : (p n).1 = (X : ℤ) := by
      have hh := congrFun hc (Fin.last n)
      change p n = lazyTwoDimensionalPrefix 0 0 w (Fin.last n) at hh
      exact (congrArg Prod.fst hh).trans hX
    have hset : C ∩ B = C ∩ {p | ∀ j, (X : ℤ) ≤ (p (n + j)).1} := by
      ext p
      constructor
      · rintro ⟨hc, hb⟩
        change ∀ j, (p n).1 ≤ (p (n + j)).1 at hb
        refine ⟨hc, ?_⟩
        change ∀ j, (X : ℤ) ≤ (p (n + j)).1
        simpa only [hp p hc] using hb
      · rintro ⟨hc, hb⟩
        change ∀ j, (X : ℤ) ≤ (p (n + j)).1 at hb
        refine ⟨hc, ?_⟩
        change ∀ j, (p n).1 ≤ (p (n + j)).1
        simpa only [hp p hc] using hb
    have hjoint := conditionedSource_prefix_inter_future_barrier
      0 0 ν hRN0 n X X w hw le_rfl hX
    simp only [Nat.cast_zero, Nat.sub_self, zero_add, Nat.cast_zero] at hjoint
    have hatomR : ν.real C = ((X : ℝ) + 1) * ((3 : ℝ) ^ n)⁻¹ := by
      change (ν C).toReal = _
      change ν C = _ at hatom
      rw [hatom, ite_eq_left hw]
      simp only [zero_add, div_one, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_pow, ENNReal.toReal_ofNat]
      rw [hX]
      simp only [Int.cast_natCast]
      rw [ENNReal.toReal_ofReal (by positivity)]
    change ν.real (C ∩ B) = _
    rw [hset, hjoint, hatomR]
    have hne : (X : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · rw [ite_eq_right hw]
    have hzeroC : ν C = 0 := by
      change ν C = _ at hatom
      rw [hatom, ite_eq_right hw, zero_mul]
    have hzero : ν (C ∩ B) = 0 := measure_mono_null Set.inter_subset_left hzeroC
    change (ν (C ∩ B)).toReal = 0
    rw [hzero, ENNReal.toReal_zero]

end DirectedDistances.RandomWalk
