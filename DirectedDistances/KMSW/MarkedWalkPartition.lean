/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StoppedWalkLawSum
public import DirectedDistances.PaperProofs.Section3.BoltzmannMarks

/-! Supporting lemmas for paper labels `def-boltzmann-right` (see CORRESPONDENCE.md). -/

/-! # Marked stopped-walk partition sum

This file proves the walk-level size-biased normalization bridge for Lemma
Definition 1.10 (`def-boltzmann-right`,
giving `L(tau) + 1` choices, as in the proof. The legal-step convention/marked-vertex convention rulings remain
and source isomorphism-class carrier, including `m₀`; this helper is not
counted as the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

private theorem finiteWord_integrate_eq_codeWalk_marked {ell r n : ℕ}
    (c : KMSWWalkClass ell r n) (ω : ℕ → Fin 3)
    (hprefix : ∀ i : Fin (n - 1), ω (i.val + 1) = c.val i)
    (k : ℕ) (hk : k ≤ n - 1) :
    integrateCodes (finiteCodeExtend c.val) k = codeWalk ω k := by
  rw [codeWalk_eq_integrateCodes]
  unfold integrateCodes
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hit : i < n - 1 := lt_of_lt_of_le hik hk
  simpa [finiteCodeExtend, hit] using
    congrArg lazyTwoDimensionalStep (hprefix ⟨i, hit⟩).symm





theorem boltzmannMarkWeight_eq_indexWeight_of_mem
    (r : ℕ) (i : StoppedWalkIndex r) (ω : ℕ → Fin 3)
    (hω : ω ∈ stoppedWalkIndexSet i) :
    boltzmannMarkWeight r ω = ((i.2.1 + 1 : ℕ) : ℝ) := by
  classical
  rcases i with ⟨n, ⟨ell, c⟩⟩
  by_cases hn : 1 ≤ n
  · simp only [stoppedWalkIndexSet, hn, ↓reduceIte] at hω
    rcases hω with ⟨hprefix, hlast⟩
    have hevent := stoppedCylinder_subset_eventSlice hn c ⟨hprefix, hlast⟩
    have hτ : boltzmannTau r ω = n := hevent.2
    rcases c.property with ⟨hend, _⟩
    have hprev : codeWalk ω (n - 1) =
        ((ell : ℤ) - 1, -(r : ℤ) + 1) := by
      rw [← finiteWord_integrate_eq_codeWalk_marked c ω hprefix
        (n - 1) le_rfl]
      exact hend
    have hstep : codeWalk ω n - codeWalk ω (n - 1) = (1, -1) := by
      have hindex : (n - 1) + 1 = n := by omega
      simpa [hindex, hlast, lazyTwoDimensionalStep] using
        codeWalk_succ_sub ω (n - 1)
    have hwalk : codeWalk ω n =
        codeWalk ω (n - 1) + (1, -1) := by
      calc
        codeWalk ω n =
            (codeWalk ω n - codeWalk ω (n - 1)) + codeWalk ω (n - 1) := by abel
        _ = (1, -1) + codeWalk ω (n - 1) := by rw [hstep]
        _ = codeWalk ω (n - 1) + (1, -1) := by abel
    have hL : (codeWalk ω n).1 = (ell : ℤ) := by
      rw [hwalk, hprev]
      simp only [Prod.fst_add]
      omega
    simp [boltzmannMarkWeight, hτ, hL]
  · simp [stoppedWalkIndexSet, hn] at hω

private theorem measurable_stoppedWalkIndexSet_marked {r : ℕ}
    (i : StoppedWalkIndex r) : MeasurableSet (stoppedWalkIndexSet i) := by
  classical
  by_cases hn : 1 ≤ i.1
  · simp only [stoppedWalkIndexSet, hn, ↓reduceIte]
    have hpref : Measurable (fun ω : ℕ → Fin 3 =>
        fun j : Fin (i.1 - 1) => ω (j.val + 1)) :=
      Measurable.of_eval fun j => measurable_pi_apply (j.val + 1)
    have hlast : Measurable (fun ω : ℕ → Fin 3 => ω i.1) :=
      measurable_pi_apply i.1
    rw [show stoppedCylinder i.2.2 =
        {ω : ℕ → Fin 3 | (fun j : Fin (i.1 - 1) => ω (j.val + 1)) = i.2.2.val} ∩
          {ω : ℕ → Fin 3 | ω i.1 = 2} by
      ext ω
      simp [stoppedCylinder, funext_iff]]
    exact (hpref (measurableSet_singleton i.2.2.val)).inter
      (hlast (measurableSet_singleton 2))
  · simp only [stoppedWalkIndexSet, hn, ↓reduceIte]
    exact MeasurableSet.empty

private theorem lintegral_markWeight_stoppedWalkIndexSet
    (r : ℕ) (i : StoppedWalkIndex r) :
    ∫⁻ ω in stoppedWalkIndexSet i,
      ENNReal.ofReal (boltzmannMarkWeight r ω) ∂iidCodeMeasure =
      if 1 ≤ i.1 then
        (i.2.1 + 1 : ENNReal) *
          (1 / 3 : ENNReal) ^ i.1
      else 0 := by
  classical
  by_cases hn : 1 ≤ i.1
  · rcases i with ⟨n, ⟨ell, c⟩⟩
    simp only [stoppedWalkIndexSet, hn, ↓reduceIte]
    have hset : MeasurableSet (stoppedCylinder c) := by
      simpa [stoppedWalkIndexSet, hn] using
        measurable_stoppedWalkIndexSet_marked ⟨n, ⟨ell, c⟩⟩
    rw [show (∫⁻ ω in stoppedCylinder c,
        ENNReal.ofReal (boltzmannMarkWeight r ω) ∂iidCodeMeasure) =
        ∫⁻ ω in stoppedCylinder c, (ell + 1 : ENNReal) ∂iidCodeMeasure by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hset] with ω hω
      have hweight := boltzmannMarkWeight_eq_indexWeight_of_mem r
        ⟨n, ⟨ell, c⟩⟩ ω (by simpa [stoppedWalkIndexSet, hn] using hω)
      rw [hweight, ENNReal.ofReal_natCast]
      norm_num
    ]
    rw [lintegral_const, Measure.restrict_apply_univ,
      iidCodeMeasure_stoppedCylinder_mass hn c]
  · simp only [stoppedWalkIndexSet, hn, ↓reduceIte]
    rw [Measure.restrict_empty, lintegral_zero_measure]

/-- The event-restricted integral is the explicit countable sum over stopped
walks, with each walk weighted by its `ℓ + 1` possible left-boundary vertex
marks. This is the walk-level partition identity for Lemma 3.12 and Definition
map transfer needs Theorem 3.5 and the source carrier including `m₀`. -/
theorem boltzmannMarkWeight_lintegral_eq_tsum_walkMarks
    (r : ℕ) (hr : 1 ≤ r) :
    (∫⁻ ω in boltzmannEvent r,
      ENNReal.ofReal (boltzmannMarkWeight r ω) ∂iidCodeMeasure) =
      ∑' n : ℕ, ∑' ell : ℕ,
        if 1 ≤ n then
          (ell + 1 : ENNReal) *
            (Fintype.card (KMSWWalkClass ell r n) : ENNReal) *
              (1 / 3 : ENNReal) ^ n
        else 0 := by
  classical
  rw [boltzmannEvent_eq_iUnion_stoppedWalkIndex r hr]
  rw [lintegral_iUnion (fun i => measurable_stoppedWalkIndexSet_marked i)
    (stoppedWalkIndexSet_pairwiseDisjoint hr)]
  change (∑' i : StoppedWalkIndex r,
      ∫⁻ ω in stoppedWalkIndexSet i,
        ENNReal.ofReal (boltzmannMarkWeight r ω) ∂iidCodeMeasure) = _
  simp_rw [lintegral_markWeight_stoppedWalkIndexSet]
  change (∑' i : (Σ n : ℕ, Σ ell : ℕ, KMSWWalkClass ell r n),
      if 1 ≤ i.1 then
        (i.2.1 + 1 : ENNReal) * (1 / 3 : ENNReal) ^ i.1
      else 0) = _
  rw [tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_sigma']
  apply tsum_congr
  intro ell
  by_cases hn : 1 ≤ n
  · simp only [hn, ↓reduceIte]
    rw [tsum_fintype]
    simp [mul_assoc, mul_left_comm, mul_comm]
  · simp [hn]

/-- The walk marked partition function `C̃_r`, expressed by its countable sum
over `(n, ℓ, walk)` marks. The measure on maps and its normalization require
Theorem 3.5 and are outside this helper. -/
@[expose] noncomputable def markedWalkPartitionFunction (r : ℕ) : ENNReal :=
  ∑' n : ℕ, ∑' ell : ℕ,
    if 1 ≤ n then
      (ell + 1 : ENNReal) *
        (Fintype.card (KMSWWalkClass ell r n) : ENNReal) *
          (1 / 3 : ENNReal) ^ n
    else 0





theorem markedWalkPartitionFunction_lt_top_and_eq_probability_mul_conditional
    (r : ℕ) (hr : 1 ≤ r) :
    markedWalkPartitionFunction r < ⊤ ∧
      markedWalkPartitionFunction r = iidCodeMeasure (boltzmannEvent r) *
        (∫⁻ ω, ENNReal.ofReal (boltzmannMarkWeight r ω)
          ∂(iidCodeMeasure[|boltzmannEvent r])) := by
  have hsum := boltzmannMarkWeight_lintegral_eq_tsum_walkMarks r hr
  have hbound := boltzmann_lintegral_le_one r hr
  have hfinite : markedWalkPartitionFunction r < ⊤ := by
    rw [markedWalkPartitionFunction, ← hsum]
    exact lt_of_le_of_lt hbound (by simp)
  have hprob : iidCodeMeasure (boltzmannEvent r) ≠ 0 := by
    exact (measureReal_ne_zero_iff (by finiteness)).mp
      (ne_of_gt (boltzmann_event_positive r hr))
  have hcond := boltzmann_conditional_lintegral_eq_div r hr
  refine ⟨hfinite, ?_⟩
  rw [markedWalkPartitionFunction, ← hsum, hcond]
  exact (ENNReal.mul_div_cancel hprob (by finiteness)).symm

/-- A marked index consists of a stopped-walk index and one of its `ℓ + 1`
left-boundary vertex marks. -/
@[expose] def MarkedWalkIndex (r : ℕ) :=
  Σ i : StoppedWalkIndex r, Fin (i.2.1 + 1)

instance instCountableMarkedWalkIndex (r : ℕ) : Countable (MarkedWalkIndex r) := by
  unfold MarkedWalkIndex
  infer_instance

/-- Countable atomic-mass sum on marked walk indices, assigning mass `3⁻ⁿ`
to each marked positive-time walk and zero to zero-time indices. Its total mass
sum identity is not the map-level Lemma 3.12. -/
theorem markedWalkIndex_tsum_atomMass_eq_partitionFunction (r : ℕ) :
    (∑' p : MarkedWalkIndex r,
      if 1 ≤ p.1.1 then (1 / 3 : ENNReal) ^ p.1.1 else 0) =
      markedWalkPartitionFunction r := by
  classical
  rw [markedWalkPartitionFunction]
  change (∑' p : (Σ i : StoppedWalkIndex r, Fin (i.2.1 + 1)),
      if 1 ≤ p.1.1 then (1 / 3 : ENNReal) ^ p.1.1 else 0) = _
  rw [tsum_sigma']
  simp_rw [tsum_fintype]
  simp_rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  simp_rw [mul_ite, mul_zero]
  change (∑' i : (Σ n : ℕ, Σ ell : ℕ, KMSWWalkClass ell r n),
      if 1 ≤ i.1 then
        ((i.2.1 + 1 : ℕ) : ENNReal) * (1 / 3 : ENNReal) ^ i.1
      else 0) = _
  rw [tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_sigma']
  apply tsum_congr
  intro ell
  by_cases hn : 1 ≤ n
  · simp only [hn, ↓reduceIte]
    rw [tsum_fintype]
    simp [mul_assoc, mul_left_comm, mul_comm]
  · simp [hn]

/-- After dividing by `C̃_r`, each positive-time marked walk pair has mass
`3⁻ⁿ/C̃_r`, the walk-level marked law in Lemma 3.12 and Definition 1.10.
Map-level transfer and the source carrier remain separate obligations. -/
@[expose] noncomputable def normalizedMarkedWalkIndexMass
    (r : ℕ) (p : MarkedWalkIndex r) : ENNReal :=
  (if 1 ≤ p.1.1 then (1 / 3 : ENNReal) ^ p.1.1 else 0) /
    markedWalkPartitionFunction r

theorem normalizedMarkedWalkIndex_atomMass
    (r : ℕ) (p : MarkedWalkIndex r) (hn : 1 ≤ p.1.1) :
    normalizedMarkedWalkIndexMass r p =
      (1 / 3 : ENNReal) ^ p.1.1 / markedWalkPartitionFunction r := by
  simp [normalizedMarkedWalkIndexMass, hn]

end DirectedDistances.KMSW
