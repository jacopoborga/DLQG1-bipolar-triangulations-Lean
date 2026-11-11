/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWMapLawFromWalk

/-! Supporting lemmas for paper labels `lem-kmsw-boltzmann` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The full Boltzmann partition over all left boundary lengths. helper toward
paper result. -/
@[expose] noncomputable def rightBoltzmannPartition (r : ℕ) : ENNReal :=
  ∑' q : AllBoltzmannSpace r, allBoltzmannWeight q

private theorem no_zeroEdgeMapClass (ℓ r : ℕ) :
    IsEmpty (KMSWMapIsoClass ℓ r 0) := by
  constructor
  intro c
  refine Quotient.inductionOn c ?_
  intro R
  have hcount : R.dartCount = 0 := by
    have h := R.dartCount_eq_two_mul
    omega
  have hlen : R.B.rightPath.darts.length = r := R.B.rightPath.darts_length
  have hpos : 0 < R.B.rightPath.darts.length := by
    rw [hlen]
    exact R.B.right_length_pos
  let i : Fin R.B.rightPath.darts.length := ⟨0, hpos⟩
  have d : Fin R.dartCount := R.B.rightPath.darts.get i
  rw [hcount] at d
  exact Fin.elim0 d

/-- The initial single-edge map occupies the one-total-edge layer of the
right-boundary carrier. helper toward `lem-kmsw-boltzmann` -/
theorem initialSingleEdge_mem_rightBoltzmannSpace :
    ∃ q : AllBoltzmannSpace 1, q.2.1 = 1 := by
  exact ⟨⟨1, ⟨1, Quotient.mk _ KMSWMapRep.singleEdge⟩⟩, rfl⟩

/-- Every class in the dependent Boltzmann carrier has positive total edge
count; in particular its zero-edge fiber is absent. The index `1` remains in
the carrier and includes the single-edge map. helper toward
paper result. -/
theorem allBoltzmannSpace_size_pos (r : ℕ) (q : AllBoltzmannSpace r) :
    1 ≤ q.2.1 := by
  rcases q with ⟨ℓ, n, c⟩
  change 1 ≤ n
  cases n with
  | zero => exact False.elim ((no_zeroEdgeMapClass ℓ r).false c)
  | succ n => omega

/-- Under the named final-prefix surjectivity input, the stopped-map range is
exactly the positive-total-edge part of the full carrier. helper toward
paper result. -/
theorem stoppedWalkMap_range_eq_positive (r : ℕ)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    Set.range (@stoppedWalkMap r) = {q : AllBoltzmannSpace r | 1 ≤ q.2.1} := by
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    exact i.2
  · intro hq
    rcases q with ⟨ℓ, n, c⟩
    change 1 ≤ n at hq
    exact stoppedWalkMap_range_of_prefix r ℓ n hq (hsurj ℓ n hq) c

/-- Under the named final-prefix surjectivity input, every class in the full
carrier is represented by a positive stopped walk. helper toward
paper result. -/
private theorem stoppedWalkMap_range_eq_univ (r : ℕ)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    Set.range (@stoppedWalkMap r) = Set.univ := by
  rw [stoppedWalkMap_range_eq_positive r hsurj]
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact allBoltzmannSpace_size_pos r q

/-- Under the named final-prefix surjectivity input, the full partition equals
the partition over the stopped-map range. helper toward
paper result. -/
theorem rightBoltzmannPartition_eq_stoppedMapRangePartition (r : ℕ)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    rightBoltzmannPartition r = stoppedMapRangePartition r := by
  classical
  let hrange := stoppedWalkMap_range_eq_univ r hsurj
  let e : {q : AllBoltzmannSpace r //
      q ∈ Set.range (@stoppedWalkMap r)} ≃ AllBoltzmannSpace r := {
    toFun := fun q => q.1
    invFun := fun q => ⟨q, by rw [hrange]; exact Set.mem_univ q⟩
    left_inv := by intro q; exact Subtype.ext rfl
    right_inv := by intro q; rfl }
  change (∑' q : AllBoltzmannSpace r, allBoltzmannWeight q) =
    ∑' q : {q : AllBoltzmannSpace r //
      q ∈ Set.range (@stoppedWalkMap r)}, allBoltzmannWeight q.1
  rw [← e.tsum_eq (fun q => allBoltzmannWeight q)]
  rfl

/-- Under the named final-prefix surjectivity input, the full partition is
the probability of the stopped-walk event. helper toward
paper result. -/
theorem rightBoltzmannPartition_eq_eventProbability (r : ℕ) (hr : 1 ≤ r)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    rightBoltzmannPartition r = iidCodeMeasure (boltzmannEvent r) := by
  rw [rightBoltzmannPartition_eq_stoppedMapRangePartition r hsurj,
    stoppedMapRangePartition_eq_eventProbability r hr]

private theorem boltzmannEvent_measure_ne_zero (r : ℕ) (hr : 1 ≤ r) :
    iidCodeMeasure (boltzmannEvent r) ≠ 0 := by
  have hp := boltzmann_event_positive r hr
  exact (measureReal_ne_zero_iff (by finiteness)).mp (ne_of_gt hp)

private theorem boltzmannEvent_measure_le_one (r : ℕ) :
    iidCodeMeasure (boltzmannEvent r) ≤ 1 := by
  calc
    iidCodeMeasure (boltzmannEvent r) ≤ iidCodeMeasure Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

/-- The full partition is positive and finite under the named final-prefix
surjectivity input. Positivity uses `boltzmann_event_positive`; finiteness uses
that the conditioning event has probability at most one. helper toward
paper result. -/
theorem rightBoltzmannPartition_normalizer (r : ℕ) (hr : 1 ≤ r)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    0 < rightBoltzmannPartition r ∧ rightBoltzmannPartition r < ⊤ := by
  rw [rightBoltzmannPartition_eq_eventProbability r hr hsurj]
  exact ⟨pos_iff_ne_zero.mpr (boltzmannEvent_measure_ne_zero r hr),
    lt_of_le_of_lt (boltzmannEvent_measure_le_one r) ENNReal.one_lt_top⟩

/-- Full right-boundary Boltzmann weights, normalized by the full partition.
not the paper result. -/
@[expose] noncomputable def rightBoltzmannLaw (r : ℕ)
    (h0 : rightBoltzmannPartition r ≠ 0)
    (htop : rightBoltzmannPartition r ≠ ⊤) :
    Measure (AllBoltzmannSpace r) := by
  let _h0 := h0
  let _htop := htop
  exact
  (rightBoltzmannPartition r)⁻¹ •
    Measure.sum (fun q : AllBoltzmannSpace r =>
      allBoltzmannWeight q • Measure.dirac q)

/-- An atom of the full right-boundary Boltzmann measure has weight divided by
the full partition. helper toward `lem-kmsw-boltzmann`
conditional on the named surjectivity input where used; not the paper result. -/
theorem rightBoltzmannLaw_singleton (r : ℕ)
    (h0 : rightBoltzmannPartition r ≠ 0)
    (htop : rightBoltzmannPartition r ≠ ⊤)
    (q : AllBoltzmannSpace r) :
    rightBoltzmannLaw r h0 htop {q} =
      allBoltzmannWeight q / rightBoltzmannPartition r := by
  rw [rightBoltzmannLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_smul_dirac_singleton]
  simp only [div_eq_mul_inv, mul_comm]

/-- The full-partition-normalized right-boundary measure has total mass one
whenever its partition is positive and finite. helper toward
not the paper result. -/
theorem rightBoltzmannLaw_isProbabilityMeasure (r : ℕ)
    (h0 : rightBoltzmannPartition r ≠ 0)
    (htop : rightBoltzmannPartition r ≠ ⊤) :
    IsProbabilityMeasure (rightBoltzmannLaw r h0 htop) := by
  refine ⟨?_⟩
  rw [rightBoltzmannLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  change (rightBoltzmannPartition r)⁻¹ * rightBoltzmannPartition r = 1
  exact ENNReal.inv_mul_cancel h0 htop

/-- An atom after mapping the full right-boundary Boltzmann measure through
`some` has its weight divided by the full partition. helper toward
paper result. -/
theorem rightBoltzmannLaw_map_some_singleton (r : ℕ)
    (h0 : rightBoltzmannPartition r ≠ 0)
    (htop : rightBoltzmannPartition r ≠ ⊤)
    (q : AllBoltzmannSpace r) :
    (rightBoltzmannLaw r h0 htop).map some {some q} =
      allBoltzmannWeight q / rightBoltzmannPartition r := by
  have hsome : Measurable (some : AllBoltzmannSpace r →
      Option (AllBoltzmannSpace r)) := by
    intro s hs
    trivial
  rw [Measure.map_apply hsome (measurableSet_singleton (some q))]
  have hpre : (some : AllBoltzmannSpace r → Option (AllBoltzmannSpace r)) ⁻¹'
      {some q} = {q} := by
    ext x
    simp
  rw [hpre, rightBoltzmannLaw_singleton]

private theorem boltzmannEvent_inter_stoppedMap_none_empty (r : ℕ)
    (hr : 1 ≤ r) :
    boltzmannEvent r ∩ stoppedMap r hr ⁻¹' {none} = ∅ := by
  ext ω
  constructor
  · rintro ⟨hE, hnone⟩
    have hdecomp := boltzmannEvent_eq_iUnion_stoppedWalkIndex r hr
    have hmem : ω ∈ ⋃ j : StoppedWalkIndex r, stoppedWalkIndexSet j := by
      rw [← hdecomp]
      exact hE
    rcases Set.mem_iUnion.mp hmem with ⟨j, hj⟩
    have hjpos : 1 ≤ j.1 := by
      by_contra h
      have hjzero : j.1 = 0 := by omega
      simp [stoppedWalkIndexSet, hjzero] at hj
    have hidx : stoppedIndex r hr ω = some j := by
      have hmem' : ω ∈ stoppedIndex r hr ⁻¹' {some j} := by
        rw [stoppedIndex_preimage_singleton]
        exact hj
      simpa using hmem'
    have hval : stoppedMap r hr ω = some (stoppedWalkMap ⟨j, hjpos⟩) := by
      simp [stoppedMap, hidx, stoppedWalkMapOption, hjpos]
    have hnone' : stoppedMap r hr ω = none := Set.mem_singleton_iff.mp hnone
    rw [hval] at hnone'
    cases hnone'
  · intro h
    simp at h

/-- The conditional stopped-map law equals the full right-boundary
Boltzmann law mapped into `Option`, under the named final-prefix surjectivity
input. The atom comparison uses the conditional map formula on every positive
size class and the zero mass of `none` on the stopping event. helper toward
paper result. -/
theorem iidCodeMeasure_cond_map_eq_rightBoltzmannLaw_map_some (r : ℕ)
    (hr : 1 ≤ r)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n)
    (h0 : rightBoltzmannPartition r ≠ 0)
    (htop : rightBoltzmannPartition r ≠ ⊤) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr) =
      (rightBoltzmannLaw r h0 htop).map some := by
  apply Measure.ext_of_singleton
  intro x
  cases x with
  | none =>
      rw [Measure.map_apply (measurable_stoppedMap r hr)
        (measurableSet_singleton (none : Option (AllBoltzmannSpace r)))]
      rw [ProbabilityTheory.cond_apply'
        (measurable_stoppedMap r hr
          (measurableSet_singleton (none : Option (AllBoltzmannSpace r))))
        iidCodeMeasure]
      rw [boltzmannEvent_inter_stoppedMap_none_empty r hr]
      simp
      have hsome : Measurable (some : AllBoltzmannSpace r →
          Option (AllBoltzmannSpace r)) := by
        intro s hs
        trivial
      rw [Measure.map_apply hsome
        (measurableSet_singleton (none : Option (AllBoltzmannSpace r)))]
      have hpre : (some : AllBoltzmannSpace r → Option (AllBoltzmannSpace r)) ⁻¹'
          {none} = ∅ := by
        ext q
        simp
      rw [hpre, measure_empty]
  | some q =>
      have hn := allBoltzmannSpace_size_pos r q
      rcases q with ⟨ℓ, n, c⟩
      change 1 ≤ n at hn
      have hprefix := hsurj ℓ n hn
      calc
        (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr)
            {some (⟨ℓ, ⟨n, c⟩⟩ : AllBoltzmannSpace r)} =
          allBoltzmannWeight (⟨ℓ, ⟨n, c⟩⟩ : AllBoltzmannSpace r) /
            iidCodeMeasure (boltzmannEvent r) :=
          iidCodeMeasure_cond_map_singleton_mass_of_prefix r hr ℓ n hn
            hprefix c
        _ = allBoltzmannWeight (⟨ℓ, ⟨n, c⟩⟩ : AllBoltzmannSpace r) /
            rightBoltzmannPartition r := by
          rw [← rightBoltzmannPartition_eq_eventProbability r hr hsurj]
        _ = (rightBoltzmannLaw r h0 htop).map some
            {some (⟨ℓ, ⟨n, c⟩⟩ : AllBoltzmannSpace r)} :=
          (rightBoltzmannLaw_map_some_singleton r h0 htop
            (⟨ℓ, ⟨n, c⟩⟩ : AllBoltzmannSpace r)).symm

end DirectedDistances.KMSW
