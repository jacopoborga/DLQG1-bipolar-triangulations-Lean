/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalFiniteTimeAssembly
public import DirectedDistances.RandomWalk.RenewalTimeRankBridge
public import DirectedDistances.RandomWalk.RenewalSuccessMeasurability
public import DirectedDistances.RandomWalk.RenewalZeroTimeLaw
public import DirectedDistances.RandomWalk.RenewalHistorySlice












public section

namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- Internal supplied-object consequence for the literal renewal-success
graph. This does not define or approve the manuscript renewal times and
does not establish the geometric equivalence of Lemma 4.8. -/
theorem conditionedSource_selector_condDistrib_ae_eq_const
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (m : ℕ)
    (T : (ℕ → ℤ × ℤ) → WithTop ℕ)
    (hGraph : ∀ p, IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (T p)) :
    let μf : Measure {p // T p < ⊤} := ν.comap
      (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ))
    let history :=
      stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val)
    let future :=
      stoppedVectorFuture (finiteTimeIndex T) (fun ω => ω.val)
    condDistrib future history μf =ᵐ[μf.map history]
      Kernel.const (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ν := by
  classical

  -- Uniqueness identifies every fiber of the supplied object.
  have hFiber (p : ℕ → ℤ × ℤ) (t : WithTop ℕ) :
      T p = t ↔ IsPositiveSuccessTime (fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m t := by
    constructor
    · intro ht
      rw [← ht]
      exact hGraph p
    · intro ht
      obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime
        (fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m
      exact (hu (T p) (hGraph p)).trans (hu t ht).symm

  have hMeasFiber (t : WithTop ℕ) : MeasurableSet {p | T p = t} := by
    have hEq :
        {p | T p = t} =
          {p | IsPositiveSuccessTime (fun j =>
            (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
              ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m t} := by
      ext p
      exact hFiber p t
    rw [hEq]
    induction t using ENat.recTopCoe with
    | top =>
        exact measurableSet_isPositiveSuccessTime_top _
          (fun j _ => measurableSet_renewal_success j) m
    | coe n =>
        exact measurableSet_isPositiveSuccessTime_natCast _
          (fun j _ => measurableSet_renewal_success j) m n

  -- Countability of ENat turns the measurable fibers into measurability.
  have measurableT : Measurable (T : (ℕ → ℤ × ℤ) → WithTop ℕ) := by
    intro s _
    have hPreimage :
        T ⁻¹' s = ⋃ t : s, {p | T p = t.val} := by
      ext p
      constructor
      · intro hp
        exact Set.mem_iUnion.mpr ⟨⟨T p, hp⟩, rfl⟩
      · intro hp
        obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hp
        change T p = t.val at ht
        change T p ∈ s
        rw [ht]
        exact t.property
    rw [hPreimage]
    exact MeasurableSet.iUnion (fun t => hMeasFiber t.val)

  apply finiteTime_condDistrib_ae_eq_const_of_slice_laws
    ν ν T measurableT
  intro n H hH

  let A : Set (ℕ → ℤ × ℤ) :=
    {p | (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
      Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H}

  have hA : MeasurableSet[MeasurableSpace.comap
      (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val)
      inferInstance] A :=
    measurableSet_history_test_prefix_comap H hH n

  by_cases hm : m = 0
  · have hZero (p : ℕ → ℤ × ℤ) : T p = 0 := by
      exact (isPositiveSuccessTime_zero_iff _ (T p)).mp
        (hm ▸ hGraph p)

    by_cases hn : n = 0
    · subst n
      have hEvent :
          {p | T p = ((0 : ℕ) : WithTop ℕ) ∧
            (⟨0, fun j : Fin (0 + 1) => p j.val⟩ :
              Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H} = A := by
        ext p
        exact ⟨fun hp => hp.2, fun hp => ⟨hZero p, hp⟩⟩
      rw [hEvent]
      exact conditionedSource_zero_time_history_restrict ν hRN A hA
    · have hNe : (0 : WithTop ℕ) ≠ (n : WithTop ℕ) := by
        intro he
        apply hn
        exact (WithTop.coe_injective he).symm
      have hEvent :
          {p | T p = (n : WithTop ℕ) ∧
            (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
              Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact hNe ((hZero p).symm.trans hp.1)
      rw [hEvent]
      simp only [Measure.restrict_empty, Measure.map_zero,
        measure_empty, zero_smul]

  · have hmPos : 0 < m := Nat.pos_of_ne_zero hm

    let P : Set (ℕ → ℤ × ℤ) :=
      {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        (((Finset.Icc 1 n).filter fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)}
    let B : Set (ℕ → ℤ × ℤ) :=
      {p | ∀ k, (p n).1 ≤ (p (n + k)).1}

    have hEvent :
        {p | T p = (n : WithTop ℕ) ∧
          (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
            Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H} =
          A ∩ (P ∩ B) := by
      ext p
      change (T p = (n : WithTop ℕ) ∧ p ∈ A) ↔
        p ∈ A ∧ p ∈ P ∩ B
      constructor
      · rintro ⟨ht, htest⟩
        exact ⟨htest, (isPositiveSuccessTime_renewal_natCast_iff p hmPos n).mp
          ((hFiber p (n : WithTop ℕ)).mp ht)⟩
      · rintro ⟨htest, hrank⟩
        exact ⟨(hFiber p (n : WithTop ℕ)).mpr
          ((isPositiveSuccessTime_renewal_natCast_iff p hmPos n).mpr hrank), htest⟩

    rw [hEvent]
    exact conditionedSource_renewal_history_slice_restrict
      ν hRN m n A hA

end DirectedDistances.RandomWalk
