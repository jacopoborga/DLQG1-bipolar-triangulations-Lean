/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalPrefixMass
import DirectedDistances.RandomWalk.ConditionedVectorPrefixSupport
import DirectedDistances.RandomWalk.ConditionedVectorFactorization
import DirectedDistances.RandomWalk.RenewalSuccessMeasurability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Joint future-barrier lower bound on regular records

Internal proof infrastructure for Lemma 4.12, (4.13) in joint form
to decompose both events over the genuine finite word cylinders. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators

/-- The joint future-barrier lower bound on the regular strict-record event,
with the manuscript's constants and full future quantifier retained. This is -/
theorem regularRecord_futureBarrier_joint_lower (ν : Measure (ℕ → ℤ × ℤ))
    [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (n : ℕ) (hn : 1 ≤ n) :
    (1 / 101) * (Real.sqrt n)⁻¹ *
        ν.real {p : ℕ → ℤ × ℤ | (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} ≤
      ν.real ({p : ℕ → ℤ × ℤ | ∀ j, (p n).1 ≤ (p (n + j)).1} ∩
        {p : ℕ → ℤ × ℤ | (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n}) := by
  classical
  let F : Set (ℕ → ℤ × ℤ) :=
    {p | (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
      Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n}
  let B : Set (ℕ → ℤ × ℤ) := {p | ∀ j, (p n).1 ≤ (p (n + j)).1}
  let C (w : Fin n → Fin 3) : Set (ℕ → ℤ × ℤ) :=
    {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
  let A (w : Fin n → Fin 3) : Set (ℕ → ℤ × ℤ) := C w ∩ F
  let D (w : Fin n → Fin 3) : Set (ℕ → ℤ × ℤ) := (C w ∩ F) ∩ B

  have hRN0 : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) /
              (((0 : ℕ) : ℝ) + 1)) else 0) := by
    simpa only [Nat.cast_zero] using hRN

  have hCoordinate : Measurable (fun p : ℕ → ℤ × ℤ => ((p n).1 : ℝ)) :=
    (measurable_of_countable fun z : ℤ => (z : ℝ)).comp
      ((measurable_pi_apply n).fst)
  have hBounds : MeasurableSet {p : ℕ → ℤ × ℤ |
      Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧
        ((p n).1 : ℝ) ≤ 100 * Real.sqrt n} := by
    exact (measurableSet_le measurable_const hCoordinate).inter
      (measurableSet_le hCoordinate measurable_const)
  have hF : MeasurableSet F := by
    change MeasurableSet
      ({p : ℕ → ℤ × ℤ | ∀ j < n, (p n).2 ≤ (p j).2 - 1} ∩
        {p | Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧
          ((p n).1 : ℝ) ≤ 100 * Real.sqrt n})
    exact (measurableSet_renewal_strict_record n).inter hBounds
  have hB : MeasurableSet B := measurableSet_renewal_future_barrier n
  have hC : ∀ w : Fin n → Fin 3, MeasurableSet (C w) := by
    intro w
    exact (measurableSet_singleton _).preimage (by fun_prop)
  have hA : ∀ w : Fin n → Fin 3, MeasurableSet (A w) :=
    fun w => (hC w).inter hF
  have hD : ∀ w : Fin n → Fin 3, MeasurableSet (D w) :=
    fun w => ((hC w).inter hF).inter hB

  have hAcover : F =ᵐ[ν] ⋃ w : Fin n → Fin 3, A w := by
    filter_upwards [conditionedSource_ae_prefix_mem_range 0 0 ν hRN0 n] with p hp
    apply propext
    constructor
    · intro hpF
      obtain ⟨w, hw⟩ := hp
      refine Set.mem_iUnion.mpr ⟨w, ?_⟩
      change p ∈ C w ∧ p ∈ F
      exact ⟨hw.symm, hpF⟩
    · intro hpA
      obtain ⟨w, ⟨_, hpF⟩⟩ := Set.mem_iUnion.mp hpA
      exact hpF
  have hDcover : F ∩ B =ᵐ[ν] ⋃ w : Fin n → Fin 3, D w := by
    filter_upwards [conditionedSource_ae_prefix_mem_range 0 0 ν hRN0 n] with p hp
    apply propext
    constructor
    · rintro ⟨hpF, hpB⟩
      obtain ⟨w, hw⟩ := hp
      refine Set.mem_iUnion.mpr ⟨w, ?_⟩
      change (p ∈ C w ∧ p ∈ F) ∧ p ∈ B
      exact ⟨⟨hw.symm, hpF⟩, hpB⟩
    · intro hpD
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hpD
      change (p ∈ C w ∧ p ∈ F) ∧ p ∈ B at hw
      obtain ⟨⟨_, hpF⟩, hpB⟩ := hw
      exact ⟨hpF, hpB⟩

  have hdisA : Pairwise (Disjoint on A) := by
    intro w v hwv
    apply Set.disjoint_left.mpr
    rintro p ⟨hcw, _⟩ ⟨hcv, _⟩
    apply hwv
    apply lazyTwoDimensionalPrefix_injective 0 0
    exact hcw.symm.trans hcv
  have hdisD : Pairwise (Disjoint on D) := by
    intro w v hwv
    apply Set.disjoint_left.mpr
    rintro p ⟨⟨hcw, _⟩, _⟩ ⟨⟨hcv, _⟩, _⟩
    apply hwv
    apply lazyTwoDimensionalPrefix_injective 0 0
    exact hcw.symm.trans hcv

  have hsumA : ν.real F = ∑ w : Fin n → Fin 3, ν.real (A w) := by
    calc
      ν.real F = ν.real (⋃ w : Fin n → Fin 3, A w) :=
        congrArg ENNReal.toReal (measure_congr hAcover)
      _ = ∑ w : Fin n → Fin 3, ν.real (A w) :=
        measureReal_iUnion_fintype hdisA hA
  have hsumD : ν.real (F ∩ B) = ∑ w : Fin n → Fin 3, ν.real (D w) := by
    calc
      ν.real (F ∩ B) = ν.real (⋃ w : Fin n → Fin 3, D w) :=
        congrArg ENNReal.toReal (measure_congr hDcover)
      _ = ∑ w : Fin n → Fin 3, ν.real (D w) :=
        measureReal_iUnion_fintype hdisD hD

  have hterm (w : Fin n → Fin 3) :
      (1 / 101) * (Real.sqrt n)⁻¹ * ν.real (A w) ≤ ν.real (D w) := by
    have hword (p : ℕ → ℤ × ℤ) (hc : p ∈ C w) :
        (p ∈ F) ↔
          (∀ j (hj : j < n),
            (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).2 ≤
              (lazyTwoDimensionalPrefix 0 0 w (⟨j, by omega⟩ : Fin (n + 1))).2 - 1) ∧
          Real.sqrt n / 100 ≤
            ((lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 : ℝ) ∧
          ((lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 : ℝ) ≤ 100 * Real.sqrt n := by
      have hpref := hc
      have hpLast : p n = lazyTwoDimensionalPrefix 0 0 w (Fin.last n) := by
        exact congrFun hpref (Fin.last n)
      constructor
      · rintro ⟨hrec, hlo, hup⟩
        refine ⟨?_, ?_, ?_⟩
        · intro j hj
          have hpj : p j = lazyTwoDimensionalPrefix 0 0 w
              (⟨j, by omega⟩ : Fin (n + 1)) := congrFun hpref ⟨j, by omega⟩
          have h := hrec j hj
          rw [hpLast, hpj] at h
          exact h
        · simpa only [hpLast] using hlo
        · simpa only [hpLast] using hup
      · rintro ⟨hrec, hlo, hup⟩
        refine ⟨?_, ?_, ?_⟩
        · intro j hj
          have hpj : p j = lazyTwoDimensionalPrefix 0 0 w
              (⟨j, by omega⟩ : Fin (n + 1)) := congrFun hpref ⟨j, by omega⟩
          have h := hrec j hj
          rw [hpLast, hpj]
          exact h
        · simpa only [hpLast] using hlo
        · simpa only [hpLast] using hup

    by_cases hFw :
        (∀ j (hj : j < n),
          (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).2 ≤
            (lazyTwoDimensionalPrefix 0 0 w (⟨j, by omega⟩ : Fin (n + 1))).2 - 1) ∧
        Real.sqrt n / 100 ≤
          ((lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 : ℝ) ∧
        ((lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 : ℝ) ≤ 100 * Real.sqrt n
    · have hAeq : A w = C w := by
        ext p
        constructor
        · exact fun hp => hp.1
        · intro hc
          exact ⟨hc, (hword p hc).2 hFw⟩
      have hDeq : D w = C w ∩ B := by
        ext p
        constructor
        · rintro ⟨⟨hc, _⟩, hb⟩
          exact ⟨hc, hb⟩
        · rintro ⟨hc, hb⟩
          exact ⟨⟨hc, (hword p hc).2 hFw⟩, hb⟩
      by_cases hsurvive :
          ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1
      · let X : ℕ := (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1.toNat
        have hX : (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 = (X : ℤ) :=
          (Int.toNat_of_nonneg (hsurvive (Fin.last n))).symm
        have hXupper : (X : ℝ) ≤ 100 * Real.sqrt n := by
          have h := hFw.2.2
          rw [hX] at h
          simpa only [Int.cast_natCast] using h
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt hnR
        have hden : (X : ℝ) + 1 ≤ 101 * Real.sqrt n := by
          nlinarith
        have hcoeff :
            (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ ≤ 1 / ((X : ℝ) + 1) := by
          calc
            (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ = (101 * Real.sqrt n)⁻¹ := by
              field_simp
            _ = 1 / (101 * Real.sqrt n) := by rw [one_div]
            _ ≤ 1 / ((X : ℝ) + 1) :=
              one_div_le_one_div_of_le (by positivity) hden

        have hbarrier := conditionedSource_prefix_inter_future_barrier
          0 0 ν hRN0 n X X w hsurvive le_rfl hX
        have hpEndpoint (p : ℕ → ℤ × ℤ) (hc : p ∈ C w) :
            (p n).1 = (X : ℤ) := by
          have hh := congrFun hc (Fin.last n)
          change p n = lazyTwoDimensionalPrefix 0 0 w (Fin.last n) at hh
          exact (congrArg Prod.fst hh).trans hX
        have hbarrierSet : C w ∩ B = C w ∩
            {p | ∀ j, (X : ℤ) ≤ (p (n + j)).1} := by
          ext p
          constructor
          · rintro ⟨hc, hb⟩
            refine ⟨hc, ?_⟩
            change ∀ j, (p n).1 ≤ (p (n + j)).1 at hb
            change ∀ j, (X : ℤ) ≤ (p (n + j)).1
            simpa only [hpEndpoint p hc] using hb
          · rintro ⟨hc, hb⟩
            refine ⟨hc, ?_⟩
            change ∀ j, (X : ℤ) ≤ (p (n + j)).1 at hb
            change ∀ j, (p n).1 ≤ (p (n + j)).1
            simpa only [hpEndpoint p hc] using hb
        change ν.real (C w ∩ {p | ∀ j, (X : ℤ) ≤ (p (n + j)).1}) = _ at hbarrier
        have hmass : ν.real (C w ∩ B) = ν.real (C w) / ((X : ℝ) + 1) := by
          have hbarrier' :
              ν.real (C w ∩ {p | ∀ j, (X : ℤ) ≤ (p (n + j)).1}) =
                ν.real (C w) / ((X : ℝ) + 1) := by
            simpa only [Nat.sub_self, Nat.cast_zero, zero_add, mul_one] using hbarrier
          rw [hbarrierSet]
          exact hbarrier'
        calc
          (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ * ν.real (A w) =
              (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ * ν.real (C w) := by rw [hAeq]
          _ ≤ ν.real (C w) / ((X : ℝ) + 1) := by
            calc
              (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ * ν.real (C w) ≤
                  (1 / ((X : ℝ) + 1)) * ν.real (C w) :=
                mul_le_mul_of_nonneg_right hcoeff measureReal_nonneg
              _ = ν.real (C w) / ((X : ℝ) + 1) := by
                rw [one_div, mul_comm, div_eq_mul_inv]
          _ = ν.real (C w ∩ B) := hmass.symm
          _ = ν.real (D w) := by rw [hDeq]
      · have hatom := conditionedSource_prefix_atom 0 0 ν hRN0 n w
        simp only [Nat.cast_zero] at hatom
        have hzeroC : ν (C w) = 0 := by
          change ν {p | (fun j : Fin (n + 1) => p j.val) =
            lazyTwoDimensionalPrefix 0 0 w} = 0
          rw [hatom, ite_eq_right hsurvive, zero_mul]
        have hzeroD : ν (D w) = 0 :=
          measure_mono_null (show D w ⊆ C w from fun _ hp => hp.1.1) hzeroC
        have hzeroA : ν (A w) = 0 := by rw [hAeq, hzeroC]
        simp only [Measure.real, hzeroA, hzeroD, ENNReal.toReal_zero]
        simp
    · have hAempty : A w = ∅ := by
        ext p
        change (p ∈ C w ∧ p ∈ F) ↔ False
        constructor
        · rintro ⟨hc, hF⟩
          exact hFw ((hword p hc).1 hF)
        · exact fun h => False.elim h
      have hDempty : D w = ∅ := by
        ext p
        change ((p ∈ C w ∧ p ∈ F) ∧ p ∈ B) ↔ False
        constructor
        · rintro ⟨⟨hc, hF⟩, _⟩
          exact hFw ((hword p hc).1 hF)
        · exact fun h => False.elim h
      rw [hAempty, hDempty]
      simp

  have hsum :
      (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ *
          (∑ w : Fin n → Fin 3, ν.real (A w)) ≤
        ∑ w : Fin n → Fin 3, ν.real (D w) := by
    calc
      (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ *
          (∑ w : Fin n → Fin 3, ν.real (A w)) =
        ∑ w : Fin n → Fin 3,
          ((1 / 101 : ℝ) * (Real.sqrt n)⁻¹ * ν.real (A w)) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ w : Fin n → Fin 3, ν.real (D w) :=
        Finset.sum_le_sum fun w _ => hterm w

  have hsum' :
      (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ * ν.real F ≤ ν.real (F ∩ B) := by
    rw [hsumA, hsumD]
    exact hsum
  change (1 / 101 : ℝ) * (Real.sqrt n)⁻¹ * ν.real F ≤ ν.real (B ∩ F)
  exact hsum'.trans_eq (congrArg ν.real (Set.inter_comm F B))

end DirectedDistances.RandomWalk
