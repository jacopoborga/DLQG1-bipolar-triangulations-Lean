/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Count

import Mathlib.Analysis.SpecificLimits.Basic

/-! # Renewal count dichotomy

The generic measure theoretic core of Proposition 4.3 (`prop-cut-vertex`),
probabilities and a divergent expected count force the count to be infinite
almost surely. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory
open scoped ENNReal

/- The finite threshold is characterized by the existence of a finset of
successes of the specified size. -/
private theorem measurableSet_finite_encard_setOf_mem' {Ω : Type*} [MeasurableSpace Ω]
    (G : ℕ → Set Ω) (hG : ∀ n, MeasurableSet (G n)) (k : ℕ) :
    MeasurableSet {ω | (k : ℕ∞) ≤ {n | ω ∈ G n}.encard} := by
  classical
  have hrepr (ω : Ω) :
      ((k : ℕ∞) ≤ {n | ω ∈ G n}.encard) ↔
        ∃ s : Finset ℕ, s.card = k ∧ ∀ n ∈ s, ω ∈ G n := by
    constructor
    · intro hk
      obtain ⟨u, hus, hue⟩ := Set.exists_subset_encard_eq hk
      have hufin : u.Finite := Set.finite_of_encard_eq_coe hue
      refine ⟨hufin.toFinset, ?_, ?_⟩
      · have hcard : (hufin.toFinset.card : ℕ∞) = (k : ℕ∞) := by
          rw [← hufin.encard_eq_coe_toFinset_card]
          exact hue
        exact ENat.natCast_inj.mp hcard
      · intro n hn
        have hn' : n ∈ u := by
          simpa only [Set.Finite.mem_toFinset] using hn
        exact hus hn'
    · rintro ⟨s, hs, hall⟩
      have hsSub : (s : Set ℕ) ⊆ {n | ω ∈ G n} := by
        intro n hn
        exact hall n (by simpa using hn)
      simpa [hs] using Set.encard_mono hsSub
  have hforall (s : Finset ℕ) : MeasurableSet {ω : Ω | ∀ n ∈ s, ω ∈ G n} := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
      have heq : {ω : Ω | ∀ j ∈ insert n s, ω ∈ G j} =
          G n ∩ {ω : Ω | ∀ j ∈ s, ω ∈ G j} := by
        ext ω
        simp
      rw [heq]
      exact (hG n).inter ih
  rw [show {ω : Ω | (k : ℕ∞) ≤ {n | ω ∈ G n}.encard} =
      ⋃ s : Finset ℕ, {ω | s.card = k} ∩ {ω | ∀ n ∈ s, ω ∈ G n} by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
        exact hrepr ω]
  exact MeasurableSet.iUnion fun s => by
    have hcard : MeasurableSet {ω : Ω | s.card = k} := by
      by_cases hs : s.card = k <;> simp [hs]
    exact hcard.inter (hforall s)

/-- Measurability of a lower tail event for the cardinality of a random subset
of `ℕ`. For finite thresholds the event is a countable union over finsets; the
top threshold is the intersection of the finite ones. Helper for Proposition 4.3 -/
theorem measurableSet_le_encard_setOf_mem {Ω : Type*} [MeasurableSpace Ω]
    (G : ℕ → Set Ω) (hG : ∀ n, MeasurableSet (G n)) (m : ℕ∞) :
    MeasurableSet {ω | m ≤ {n | ω ∈ G n}.encard} := by
  cases m using ENat.recTopCoe with
  | coe k => exact measurableSet_finite_encard_setOf_mem' G hG k
  | top =>
    have hEq : {ω : Ω | (⊤ : ℕ∞) ≤ {n | ω ∈ G n}.encard} =
        ⋂ k : ℕ, {ω | (k : ℕ∞) ≤ {n | ω ∈ G n}.encard} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, top_le_iff]
      exact ENat.eq_top_iff_forall_ge
    rw [hEq]
    exact MeasurableSet.iInter fun k => measurableSet_finite_encard_setOf_mem' G hG k

private theorem encard_eq_tsum_indicator_nat (s : Set ℕ) :
    (s.encard : ℝ≥0∞) = ∑' n : ℕ, s.indicator (fun _ => (1 : ℝ≥0∞)) n := by
  classical
  rw [← Measure.count_apply (by measurability : MeasurableSet s)]
  simp [Measure.count, ← tsum_subtype]

/-- The integral of the random cardinality is the sum of the individual
success probabilities. Helper for Proposition 4.3 (`prop-cut-vertex`), -/
theorem lintegral_encard_setOf_mem {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : ℕ → Set Ω) (hG : ∀ n, MeasurableSet (G n)) :
    ∫⁻ ω, ({n | ω ∈ G n}.encard : ℝ≥0∞) ∂μ = ∑' n, μ (G n) := by
  have hpoint (ω : Ω) :
      ({n | ω ∈ G n}.encard : ℝ≥0∞) =
        ∑' n, ({ω' | ω' ∈ G n}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
    rw [encard_eq_tsum_indicator_nat]
    apply tsum_congr
    intro n
    rfl
  calc
    ∫⁻ ω, ({n | ω ∈ G n}.encard : ℝ≥0∞) ∂μ =
        ∫⁻ ω, ∑' n, ({ω' | ω' ∈ G n}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
          congr 1
          funext ω
          exact hpoint ω
    _ = ∑' n, ∫⁻ ω, ({ω' | ω' ∈ G n}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ :=
      lintegral_tsum fun n => (measurable_const.indicator (hG n)).aemeasurable
    _ = ∑' n, μ (G n) := by
      apply tsum_congr
      intro n
      change ∫⁻ ω, (G n).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ = μ (G n)
      exact lintegral_indicator_one (hG n)

private theorem ennreal_encard_eq_tsum_tail (k : ℕ∞) :
    (k : ℝ≥0∞) = ∑' m : ℕ, if ((m + 1 : ℕ) : ℕ∞) ≤ k then (1 : ℝ≥0∞) else 0 := by
  cases k using ENat.recTopCoe with
  | top =>
    rw [ENat.toENNReal_top]
    have hfun : (fun m : ℕ =>
        if ((m + 1 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0) = fun _ => 1 := by
      funext m
      simp
    rw [hfun]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) (c := (1 : ℝ≥0∞)) (by simp)).symm
  | coe n =>
    rw [ENat.toENNReal_coe]
    rw [tsum_eq_sum (s := Finset.range n)]
    symm
    · calc
        (∑ m ∈ Finset.range n, if ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) then (1 : ℝ≥0∞) else 0) =
            ∑ m ∈ Finset.range n, (1 : ℝ≥0∞) := by
              apply Finset.sum_congr rfl
              intro m hm
              have hle : m + 1 ≤ n := Nat.succ_le_iff.mpr (Finset.mem_range.mp hm)
              have hle' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) :=
                ENat.natCast_le_natCast.mpr hle
              rw [if_pos hle']
        _ = n := by simp
    · intro m hm
      simp only [Finset.mem_range, not_lt] at hm
      have hlt : (n : ℕ∞) < ((m + 1 : ℕ) : ℕ∞) :=
        ENat.natCast_lt_natCast.mpr (by omega)
      have hnot : ¬ ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := not_le_of_gt hlt
      rw [if_neg hnot]

/-- Tail formula for an `ℕ∞`-valued measurable count. Used in the proof of -/
theorem lintegral_eq_tsum_measure_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → ℕ∞) (hK : Measurable K) :
    ∫⁻ ω, (K ω : ℝ≥0∞) ∂μ =
      ∑' m : ℕ, μ {ω | ((m + 1 : ℕ) : ℕ∞) ≤ K ω} := by
  have htail (m : ℕ) : MeasurableSet {ω | ((m + 1 : ℕ) : ℕ∞) ≤ K ω} :=
    (Set.to_countable {k : ℕ∞ | ((m + 1 : ℕ) : ℕ∞) ≤ k}).measurableSet.preimage hK
  have hpoint (ω : Ω) :
      (K ω : ℝ≥0∞) =
        ∑' m : ℕ,
          ({ω | ((m + 1 : ℕ) : ℕ∞) ≤ K ω}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using ennreal_encard_eq_tsum_tail (K ω)
  calc
    ∫⁻ ω, (K ω : ℝ≥0∞) ∂μ =
        ∫⁻ ω, ∑' m : ℕ,
          ({ω' | ((m + 1 : ℕ) : ℕ∞) ≤ K ω'}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
            congr 1
            funext ω
            exact hpoint ω
    _ = ∑' m : ℕ, ∫⁻ ω,
          ({ω' | ((m + 1 : ℕ) : ℕ∞) ≤ K ω'}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ :=
        lintegral_tsum fun m => (measurable_const.indicator (htail m)).aemeasurable
    _ = ∑' m : ℕ, μ {ω | ((m + 1 : ℕ) : ℕ∞) ≤ K ω} := by
      apply tsum_congr
      intro m
      change ∫⁻ ω, ({ω' | ((m + 1 : ℕ) : ℕ∞) ≤ K ω'}.indicator
          (fun _ => (1 : ℝ≥0∞))) ω ∂μ = μ {ω | ((m + 1 : ℕ) : ℕ∞) ≤ K ω}
      exact lintegral_indicator_one (htail m)

/-! The proof below uses the tail formula for the random encard. -/

/-- A divergent sum of success probabilities, together with the renewal tail
identity, forces infinitely many successes almost surely. -/
theorem ae_infinite_of_geometric_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℕ → Set Ω) (hG : ∀ n, MeasurableSet (G n))
    (hrenew : ∀ m : ℕ,
      μ {ω | ((m + 1 : ℕ) : ℕ∞) ≤ {n | ω ∈ G n}.encard} =
        μ {ω | (m : ℕ∞) ≤ {n | ω ∈ G n}.encard} *
          μ {ω | (1 : ℕ∞) ≤ {n | ω ∈ G n}.encard})
    (hsum : ∑' n, μ (G n) = ∞) :
    ∀ᵐ ω ∂μ, {n | ω ∈ G n}.Infinite := by
  let K : Ω → ℕ∞ := fun ω => {n | ω ∈ G n}.encard
  have hKmeas : Measurable K := by
    apply ENat.measurable_iff.2
    intro n
    have hlow : MeasurableSet {ω | (n : ℕ∞) ≤ K ω} := by
      simpa only [K] using measurableSet_le_encard_setOf_mem G hG n
    have hhigh : MeasurableSet {ω | ((n + 1 : ℕ) : ℕ∞) ≤ K ω} := by
      simpa only [K, Nat.cast_add, Nat.cast_one] using
        measurableSet_le_encard_setOf_mem G hG (n + 1)
    have heq : K ⁻¹' {(n : ℕ∞)} =
        {ω | (n : ℕ∞) ≤ K ω} \ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ K ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]
      constructor
      · intro h
        rw [h]
        constructor
        · exact le_rfl
        · simpa only [ENat.natCast_le_natCast] using (show ¬ n + 1 ≤ n by omega)
      · rintro ⟨hn, hn1⟩
        cases hv : K ω using ENat.recTopCoe with
        | top => simp [hv] at hn1
        | coe j =>
          simp only [hv, ENat.natCast_le_natCast] at hn hn1
          have : j = n := by omega
          subst j
          rfl
    rw [heq]
    exact hlow.diff hhigh
  let a : ℝ≥0∞ := μ {ω | (1 : ℕ∞) ≤ K ω}
  have htail (m : ℕ) :
      μ {ω | (m : ℕ∞) ≤ K ω} = a ^ m := by
    induction m with
    | zero =>
      simp [a, K]
    | succ m ih =>
      simpa [K, a, ih, pow_succ] using hrenew m
  have hlin : ∫⁻ ω, (K ω : ℝ≥0∞) ∂μ = ∞ := by
    rw [lintegral_encard_setOf_mem μ G hG]
    exact hsum
  have htailSum :
      ∫⁻ ω, (K ω : ℝ≥0∞) ∂μ = ∑' m : ℕ, a ^ (m + 1) := by
    rw [lintegral_eq_tsum_measure_tail μ K hKmeas]
    refine tsum_congr fun m => ?_
    rw [htail]
  have ha_le : a ≤ 1 := by
    dsimp [a]
    calc
      μ {ω | (1 : ℕ∞) ≤ K ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have ha_eq : a = 1 := by
    by_contra hne
    have ha_lt : a < 1 := lt_of_le_of_ne ha_le hne
    have hwhole : (∑' m : ℕ, a ^ m) < ∞ :=
      tsum_geometric_lt_top.mpr ha_lt
    have htail_lt : (∑' m : ℕ, a ^ (m + 1)) < ∞ := by
      apply lt_of_le_of_lt (tsum_le_tsum fun m => ?_) hwhole
      calc
        a ^ (m + 1) = a ^ m * a := by rw [pow_succ]
        _ ≤ a ^ m * 1 := by gcongr
        _ = a ^ m := by simp
    have hsumTop : (∑' m : ℕ, a ^ (m + 1)) = ∞ := by
      calc
        (∑' m : ℕ, a ^ (m + 1)) = ∫⁻ ω, (K ω : ℝ≥0∞) ∂μ := htailSum.symm
        _ = ∞ := hlin
    exact (lt_irrefl ∞) (hsumTop ▸ htail_lt)
  have htail_one (m : ℕ) : μ {ω | (m : ℕ∞) ≤ K ω} = 1 := by
    rw [htail m, ha_eq]
    simp
  have hnonTopNull : μ {ω | K ω ≠ ⊤} = 0 := by
    apply le_antisymm
    · calc
        μ {ω | K ω ≠ ⊤} ≤ μ (⋃ m : ℕ, {ω | ¬ (m : ℕ∞) ≤ K ω}) :=
          measure_mono (by
            intro ω hω
            rw [Set.mem_iUnion]
            by_contra hno
            apply hω
            rw [ENat.eq_top_iff_forall_ge]
            intro m
            by_contra hm
            exact hno ⟨m, hm⟩)
        _ ≤ ∑' m : ℕ, μ {ω | ¬ (m : ℕ∞) ≤ K ω} := measure_iUnion_le _
        _ = 0 := by
          rw [tsum_eq_zero_iff]
          intro m
          have hmeas : MeasurableSet {ω | (m : ℕ∞) ≤ K ω} := by
            simpa only [K] using measurableSet_le_encard_setOf_mem G hG m
          have hzero : μ ({ω | (m : ℕ∞) ≤ K ω})ᶜ = 0 := by
            rw [measure_compl hmeas (by finiteness), measure_univ, htail_one m]
            simp
          simpa only [show {ω | ¬ (m : ℕ∞) ≤ K ω} =
              ({ω | (m : ℕ∞) ≤ K ω})ᶜ by ext; simp] using hzero
    · exact bot_le
  have hKtop : ∀ᵐ ω ∂μ, K ω = ⊤ := by
    rw [ae_iff]
    exact hnonTopNull
  filter_upwards [hKtop] with ω hω
  exact Set.encard_eq_top_iff.mp (by simpa [K] using hω)

end DirectedDistances.Probability
