/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoltzmannRightLaw
public import DirectedDistances.KMSW.MarkedWalkPartition

/-! # Left-boundary-vertex-marked right-boundary Boltzmann law

conditional on the named surjectivity input where used; not the paper result.
The mark is a left-boundary vertex, represented by `Fin (ℓ + 1)`. This file
does not assert the printed marked-boundary-edge clause. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The right-boundary Boltzmann maps with a marked left-boundary vertex.
The fiber `Fin (ℓ + 1)` records the ordered left-boundary vertex positions.
conditional on the named surjectivity input where used; not the paper result. -/
@[expose] noncomputable def RightVertexMarkedBoltzmannSpace (r : ℕ) :=
  Σ q : AllBoltzmannSpace r, Fin (q.1 + 1)

noncomputable instance (r : ℕ) :
    MeasurableSpace (RightVertexMarkedBoltzmannSpace r) := ⊤

instance (r : ℕ) : Countable (RightVertexMarkedBoltzmannSpace r) := by
  unfold RightVertexMarkedBoltzmannSpace
  infer_instance

/-- The marked map has the Boltzmann weight of its underlying map.
conditional on the named surjectivity input where used; not the paper result. -/
@[expose] noncomputable def rightVertexMarkedWeight {r : ℕ}
    (p : RightVertexMarkedBoltzmannSpace r) : ENNReal :=
  allBoltzmannWeight p.1

/-- The partition function over right-boundary maps with a marked
left-boundary vertex. Helper toward `lem-boltzmann-finite`
surjectivity input where used; not the paper result. -/
@[expose] noncomputable def rightVertexMarkedPartition (r : ℕ) : ENNReal :=
  ∑' p : RightVertexMarkedBoltzmannSpace r, rightVertexMarkedWeight p

/-- Summing over the `ℓ + 1` vertex marks multiplies each map's weight by its
left boundary length plus one. Helper toward `lem-boltzmann-finite`
surjectivity input where used; not the paper result. -/
theorem rightVertexMarkedPartition_eq_tsum (r : ℕ) :
    rightVertexMarkedPartition r =
      ∑' q : AllBoltzmannSpace r,
        ((q.1 + 1 : ℕ) : ENNReal) * allBoltzmannWeight q := by
  classical
  rw [rightVertexMarkedPartition]
  change (∑' p : (Σ q : AllBoltzmannSpace r, Fin (q.1 + 1)),
      allBoltzmannWeight p.1) = _
  rw [tsum_sigma']
  apply tsum_congr
  intro q
  rw [tsum_fintype]
  simp [Finset.sum_const, nsmul_eq_mul]

private abbrev PositiveStoppedWalkIndex (r : ℕ) :=
  {i : StoppedWalkIndex r // 1 ≤ i.1}

private abbrev PositiveMarkedWalkIndex (r : ℕ) :=
  Σ i : PositiveStoppedWalkIndex r, Fin (i.1.2.1 + 1)

private noncomputable def positiveStoppedWalkIndexEquiv (r : ℕ)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    PositiveStoppedWalkIndex r ≃ AllBoltzmannSpace r := by
  have hsurjective : Function.Surjective (@stoppedWalkMap r) := by
    intro q
    have hrange := stoppedWalkMap_range_eq_positive r hsurj
    have hq : q ∈ Set.range (@stoppedWalkMap r) := by
      rw [hrange]
      exact allBoltzmannSpace_size_pos r q
    exact Set.mem_range.mp hq
  exact Equiv.ofBijective (@stoppedWalkMap r)
    ⟨stoppedWalkMap_injective r, hsurjective⟩

private noncomputable def positiveMarkedWalkMapEquiv (r : ℕ)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    PositiveMarkedWalkIndex r ≃ RightVertexMarkedBoltzmannSpace r := by
  exact Equiv.sigmaCongr (positiveStoppedWalkIndexEquiv r hsurj)
    (fun i => Equiv.refl (Fin (i.1.2.1 + 1)))

private noncomputable def positiveMarkedWalkSigmaEquiv (r : ℕ) :
    PositiveMarkedWalkIndex r ≃
      Σ n : {n : ℕ // 1 ≤ n},
        Σ ell : ℕ, Σ _c : KMSWWalkClass ell r n.1, Fin (ell + 1) := by
  refine {
    toFun := fun p =>
      ⟨⟨p.1.1.1, p.1.2⟩, ⟨p.1.1.2.1, ⟨p.1.1.2.2, p.2⟩⟩⟩
    invFun := fun p =>
      ⟨⟨⟨p.1.1, ⟨p.2.1, p.2.2.1⟩⟩, p.1.2⟩, p.2.2.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro p
    cases p with
    | mk i mark => cases i with | mk i hi => cases i with | mk n w => cases w with | mk ell c => rfl
  · intro p
    cases p with
    | mk n w => cases n with | mk n hn => cases w with | mk ell w => cases w with | mk c mark => rfl

private theorem positiveMarkedWalkIndex_tsum_eq_markedWalkPartitionFunction
    (r : ℕ) :
    (∑' p : PositiveMarkedWalkIndex r,
      (1 / 3 : ENNReal) ^ p.1.1.1) = markedWalkPartitionFunction r := by
  classical
  let e := positiveMarkedWalkSigmaEquiv r
  calc
    (∑' p : PositiveMarkedWalkIndex r,
        (1 / 3 : ENNReal) ^ p.1.1.1) =
      ∑' p : (Σ n : {n : ℕ // 1 ≤ n},
          Σ ell : ℕ, Σ c : KMSWWalkClass ell r n.1, Fin (ell + 1)),
        (1 / 3 : ENNReal) ^ p.1.1 := by
          rw [← e.tsum_eq (fun p => (1 / 3 : ENNReal) ^ p.1.1)]
          apply tsum_congr
          intro p
          rfl
    _ = ∑' n : {n : ℕ // 1 ≤ n},
          ∑' ell : ℕ, ∑' c : KMSWWalkClass ell r n.1,
            ∑' mark : Fin (ell + 1), (1 / 3 : ENNReal) ^ n.1 := by
          simp_rw [tsum_sigma']
    _ = ∑' n : {n : ℕ // 1 ≤ n},
          ∑' ell : ℕ,
            ((ell + 1 : ℕ) : ENNReal) *
              (Fintype.card (KMSWWalkClass ell r n.1) : ENNReal) *
                (1 / 3 : ENNReal) ^ n.1 := by
          apply tsum_congr
          intro n
          apply tsum_congr
          intro ell
          simp only [tsum_fintype]
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm]
    _ = markedWalkPartitionFunction r := by
          let f : ℕ → ENNReal := fun n => ∑' ell : ℕ,
            ((ell + 1 : ℕ) : ENNReal) *
              (Fintype.card (KMSWWalkClass ell r n) : ENNReal) *
                (1 / 3 : ENNReal) ^ n
          have hsub :
              (∑' n : {n : ℕ // 1 ≤ n},
                ∑' ell : ℕ,
                  ((ell + 1 : ℕ) : ENNReal) *
                    (Fintype.card (KMSWWalkClass ell r n.1) : ENNReal) *
                      (1 / 3 : ENNReal) ^ n.1) =
              ∑' n : ℕ, Set.indicator {n : ℕ | 1 ≤ n}
                (fun n => ∑' ell : ℕ,
                  ((ell + 1 : ℕ) : ENNReal) *
                    (Fintype.card (KMSWWalkClass ell r n) : ENNReal) *
                      (1 / 3 : ENNReal) ^ n) n := by
            exact _root_.tsum_subtype
              (s := {n : ℕ | 1 ≤ n})
              (f := fun n : ℕ => ∑' ell : ℕ,
                ((ell + 1 : ℕ) : ENNReal) *
                  (Fintype.card (KMSWWalkClass ell r n) : ENNReal) *
                    (1 / 3 : ENNReal) ^ n)
          unfold markedWalkPartitionFunction
          change (∑' n : {n : ℕ // 1 ≤ n}, f n.1) = _
          rw [hsub]
          apply tsum_congr
          intro n
          by_cases hn : 1 ≤ n <;> simp [hn, Set.indicator]

/-- Under the named final-prefix surjectivity input, the marked map partition
is the walk-level marked partition. Reindexing uses `stoppedWalkMap`, whose
first coordinate is the stopped walk's left length. Helper toward
conditional on the named surjectivity input where used; not the paper result. -/
theorem rightVertexMarkedPartition_eq_markedWalkPartitionFunction
    (r : ℕ) (hr : 1 ≤ r)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    rightVertexMarkedPartition r = markedWalkPartitionFunction r := by
  classical
  have _hr : 1 ≤ r := hr
  let e := positiveMarkedWalkMapEquiv r hsurj
  calc
    rightVertexMarkedPartition r =
        ∑' p : PositiveMarkedWalkIndex r,
          rightVertexMarkedWeight (e p) := by
      rw [rightVertexMarkedPartition]
      rw [← e.tsum_eq (fun p => rightVertexMarkedWeight p)]
    _ = ∑' p : PositiveMarkedWalkIndex r,
          (1 / 3 : ENNReal) ^ p.1.1.1 := by
      apply tsum_congr
      intro p
      rcases p with ⟨⟨⟨n, ⟨ell, c⟩⟩, hn⟩, mark⟩
      change allBoltzmannWeight
        (stoppedWalkMap ⟨⟨n, ⟨ell, c⟩⟩, hn⟩) = _
      simp [allBoltzmannWeight, stoppedWalkMap, boltzmannWeight]
    _ = markedWalkPartitionFunction r :=
      positiveMarkedWalkIndex_tsum_eq_markedWalkPartitionFunction r

/-- The marked map partition is positive and finite for positive right
boundary length, under the named final-prefix surjectivity input. Finiteness
is transferred from the walk-level marked partition; positivity follows by
comparison with the unmarked partition. Helper toward `lem-boltzmann-finite`
surjectivity input where used; not the paper result. -/
theorem rightVertexMarkedPartition_normalizer (r : ℕ) (hr : 1 ≤ r)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    0 < rightVertexMarkedPartition r ∧ rightVertexMarkedPartition r < ⊤ := by
  have hwalk :=
    markedWalkPartitionFunction_lt_top_and_eq_probability_mul_conditional r hr
  have hpartition := rightVertexMarkedPartition_eq_markedWalkPartitionFunction
    r hr hsurj
  have hfinite : rightVertexMarkedPartition r < ⊤ := by
    rw [hpartition]
    exact hwalk.1
  have hmono : rightBoltzmannPartition r ≤ rightVertexMarkedPartition r := by
    rw [rightVertexMarkedPartition_eq_tsum]
    apply tsum_le_tsum
    intro q
    have hcount : (1 : ENNReal) ≤ ((q.1 + 1 : ℕ) : ENNReal) := by
      exact_mod_cast (show 1 ≤ q.1 + 1 by omega)
    calc
      allBoltzmannWeight q = 1 * allBoltzmannWeight q := by rw [one_mul]
      _ ≤ ((q.1 + 1 : ℕ) : ENNReal) * allBoltzmannWeight q := by
        gcongr
  have hpos := (rightBoltzmannPartition_normalizer r hr hsurj).1
  exact ⟨lt_of_lt_of_le hpos hmono, hfinite⟩

/-- The normalized law on maps with a marked left-boundary vertex. Its weight
is the underlying map's Boltzmann weight, divided by the marked partition.
conditional on the named surjectivity input where used; not the paper result. -/
@[expose] noncomputable def rightVertexMarkedBoltzmannLaw (r : ℕ) :
    Measure (RightVertexMarkedBoltzmannSpace r) :=
  (rightVertexMarkedPartition r)⁻¹ •
    Measure.sum (fun p : RightVertexMarkedBoltzmannSpace r =>
      rightVertexMarkedWeight p • Measure.dirac p)

/-- The normalized marked map law is a probability measure under the named
surjectivity input. Helper toward `lem-boltzmann-finite`
surjectivity input where used; not the paper result. -/
theorem rightVertexMarkedBoltzmannLaw_isProbabilityMeasure (r : ℕ)
    (hr : 1 ≤ r)
    (hsurj : ∀ ℓ n, 1 ≤ n → KMSWPeanoPrefixExistsFinal ℓ r n) :
    IsProbabilityMeasure (rightVertexMarkedBoltzmannLaw r) := by
  refine ⟨?_⟩
  rw [rightVertexMarkedBoltzmannLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  change (rightVertexMarkedPartition r)⁻¹ *
    (∑' p : RightVertexMarkedBoltzmannSpace r, rightVertexMarkedWeight p) = 1
  rw [← rightVertexMarkedPartition]
  rcases rightVertexMarkedPartition_normalizer r hr hsurj with ⟨hpos, htop⟩
  exact ENNReal.inv_mul_cancel (pos_iff_ne_zero.mp hpos) htop.ne

/-- The walk-level finite conditional-expectation bound in the source's
numeric form, independent of the map-level surjectivity input. The integrand
is `L(τ) + 1` on the event-conditioned walk law. Helper toward
not the paper result. -/
theorem lem_boltzmann_finite_expectation (r : ℕ) (hr : 1 ≤ r) :
    (∫⁻ ω in boltzmannEvent r,
      ENNReal.ofReal
        ((((codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
      ∂iidCodeMeasure) / iidCodeMeasure (boltzmannEvent r) < ⊤ :=
  boltzmann_conditional_lintegral_lt_top r hr

end DirectedDistances.KMSW
