/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorBarrierJoint
public import DirectedDistances.RandomWalk.LazyVectorTranslation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Translating both coordinates of a source cylinder is exactly the same
word cylinder with start zero. -/
theorem lazyTwoDimensionalPrefix_shift_cylinder (n : ℕ) (x y : ℤ)
    (w : Fin n → Fin 3) :
    {p : ℕ → ℤ × ℤ | (fun j : Fin (n + 1) => p j.val - (x, y)) =
      lazyTwoDimensionalPrefix 0 0 w} =
    {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix x y w} := by
  ext p
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    rw [← lazyTwoDimensionalPrefix_sub_start x y w j] at hj
    exact sub_left_injective hj
  · intro h
    funext j
    rw [congrFun h j, lazyTwoDimensionalPrefix_sub_start]

/-- Subtracting the start sends the complete actual word image to the
zero-start actual word image, with both coordinates retained. -/
theorem lazyTwoDimensionalPrefix_shift_mem_range (n : ℕ) (x y : ℤ)
    (p : ℕ → ℤ × ℤ)
    (hp : (fun j : Fin (n + 1) => p j.val) ∈
      Set.range (@lazyTwoDimensionalPrefix n x y)) :
    (fun j : Fin (n + 1) => p j.val - (x, y)) ∈
      Set.range (@lazyTwoDimensionalPrefix n 0 0) := by
  obtain ⟨w, hw⟩ := hp
  refine ⟨w, ?_⟩
  funext j
  rw [← congrFun hw j, lazyTwoDimensionalPrefix_sub_start]

/-- Conditioning the actual source law above its initial height, then
subtracting its full initial vector, produces the zero-start source RN law
at every horizon. No pre-existing zero-start law is assumed. -/
theorem conditionedSource_above_start_shift_RN
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) :
    let B : Set (ℕ → ℤ × ℤ) := {p | ∀ j, (x : ℤ) ≤ (p j).1}
    let μ : Measure (ℕ → ℤ × ℤ) :=
      (ProbabilityTheory.cond ν B).map (fun p => fun j => p j - ((x : ℤ), y))
    ∀ n : ℕ, μ.map (fun p => fun j : Fin (n + 1) => p j.val) =
      (((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0)) := by
  let B : Set (ℕ → ℤ × ℤ) := {p | ∀ j, (x : ℤ) ≤ (p j).1}
  have hBmeas : MeasurableSet B := by
    change MeasurableSet {p : ℕ → ℤ × ℤ | ∀ j, (x : ℤ) ≤ (p j).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le measurable_const (measurable_pi_apply j).fst
  have hBreal : ν.real B = 1 / ((x : ℝ) + 1) := by
    simpa only [Nat.cast_zero, sub_zero, zero_add] using
      conditionedSource_barrier_probability x y ν hRN 0 (Nat.zero_le x)
  have hBne : ν B ≠ 0 := by
    intro h
    have hz : ν.real B = 0 := by rw [Measure.real, h, ENNReal.toReal_zero]
    rw [hBreal] at hz
    exact (ne_of_gt (by positivity : 0 < 1 / ((x : ℝ) + 1))) hz
  let : IsProbabilityMeasure (ProbabilityTheory.cond ν B) := cond_isProbabilityMeasure hBne
  dsimp only
  intro n
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton q)]
  change (ProbabilityTheory.cond ν B)
    ((fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val - ((x : ℤ), y)) ⁻¹' {q}) = _
  by_cases hq : q ∈ Set.range (@lazyTwoDimensionalPrefix n 0 0)
  · obtain ⟨w, rfl⟩ := hq
    have hatom := conditionedTwoDimensionalPrefix_atom n 0 0 w
    simp only [Nat.cast_zero] at hatom
    change (ProbabilityTheory.cond ν B)
      {p | (fun j : Fin (n + 1) => p j.val - ((x : ℤ), y)) =
        lazyTwoDimensionalPrefix 0 0 w} = _
    rw [lazyTwoDimensionalPrefix_shift_cylinder]
    let C : Set (ℕ → ℤ × ℤ) := {p | (fun j : Fin (n + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y w}
    by_cases hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1
    · have ha : ∀ j, (x : ℤ) ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 :=
        (lazyTwoDimensionalPrefix_above_start_iff (x : ℤ) y w).mpr hw
      have hsurv : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 :=
        fun j => le_trans (by positivity) (ha j)
      let X : ℕ := (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1.toNat
      have hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ) :=
        (Int.toNat_of_nonneg (hsurv (Fin.last n))).symm
      have hxX : x ≤ X := by
        have hh := ha (Fin.last n)
        rw [hX] at hh
        exact_mod_cast hh
      have hjoint := conditionedSource_prefix_inter_barrier x y ν hRN n X x w ha hX
      change ν.real (C ∩ B) = _ at hjoint
      have hCmass : ν.real C =
          (((X : ℝ) + 1) / ((x : ℝ) + 1)) * (1 / 3 : ℝ) ^ n := by
        change (ν {p | (fun j : Fin (n + 1) => p j.val) =
          lazyTwoDimensionalPrefix (x : ℤ) y w}).toReal = _
        rw [conditionedSource_prefix_atom x y ν hRN n w, ite_eq_left hsurv, hX]
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_inv, ENNReal.toReal_pow]
        simp only [Int.cast_natCast, ENNReal.toReal_ofNat, one_div, inv_pow]
      have hz : ((lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 : ℝ) =
          (X : ℝ) - (x : ℝ) := by
        have hh := congrArg Prod.fst
          (lazyTwoDimensionalPrefix_sub_start (x : ℤ) y w (Fin.last n))
        change (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 - (x : ℤ) =
          (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 at hh
        rw [hX] at hh
        exact_mod_cast hh.symm
      have hzeroWeight :
          0 ≤ (((lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 : ℝ) + 1) / (0 + 1) := by
        have hh : 0 ≤ ((lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 : ℝ) :=
          Int.cast_nonneg (hw (Fin.last n))
        exact div_nonneg (add_nonneg hh zero_le_one) (by positivity)
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ?_).mp
      · rw [ProbabilityTheory.cond_apply hBmeas, ENNReal.toReal_mul,
          ENNReal.toReal_inv, Set.inter_comm]
        change (ν.real B)⁻¹ * ν.real (C ∩ B) = _
        rw [hBreal, hjoint, hCmass, hatom,
          ite_eq_left hw, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal hzeroWeight,
          ENNReal.toReal_inv, ENNReal.toReal_pow]
        simp only [zero_add, div_one, ENNReal.toReal_ofNat, hz,
          Nat.cast_sub hxX]
        have hxden : (x : ℝ) + 1 ≠ 0 := by positivity
        have hXden : (X : ℝ) + 1 ≠ 0 := by positivity
        simp only [one_div, inv_pow]
        field_simp [hxden, hXden]
      · rw [hatom]
        split_ifs <;> finiteness
    · have he : B ∩ C = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro p ⟨hp, hc⟩
        apply hw
        apply (lazyTwoDimensionalPrefix_above_start_iff (x : ℤ) y w).mp
        intro j
        exact (congrFun hc j) ▸ hp j.val
      rw [ProbabilityTheory.cond_apply hBmeas]
      change (ν B)⁻¹ * ν (B ∩ C) = _
      rw [he, measure_empty, mul_zero, hatom,
        ite_eq_right hw, zero_mul]
  · have hleft :
        (ProbabilityTheory.cond ν B)
          ((fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) =>
            p j.val - ((x : ℤ), y)) ⁻¹' {q}) = 0 := by
      rw [ProbabilityTheory.cond_apply hBmeas]
      have hz : ν (B ∩ (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) =>
          p j.val - ((x : ℤ), y)) ⁻¹' {q}) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [conditionedSource_ae_prefix_mem_range x y ν hRN n] with p hp
        rintro ⟨_, hshift⟩
        apply hq
        have h := lazyTwoDimensionalPrefix_shift_mem_range n (x : ℤ) y p hp
        exact (Set.mem_singleton_iff.mp hshift) ▸ h
      rw [hz, mul_zero]
    rw [hleft]
    have hright :
        (((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
          {q} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [lazyTwoDimensionalPrefix_withDensity_ae_mem_range n 0 0
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0)] with z hz
      intro he
      exact hq ((Set.mem_singleton_iff.mp he) ▸ hz)
    exact hright.symm

end DirectedDistances.RandomWalk
