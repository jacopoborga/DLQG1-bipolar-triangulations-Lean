module

public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.CutSeparationAE
import Mathlib.Order.OrderIsoNat

/-! # Infinite extremal present paths from the source

The infinite paths retain the IDs of present directed edges. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.RandomWalk

/-- An infinite set of natural times containing zero has an increasing enumeration
starting at zero. Applied to the explicit barriers in -/
theorem infinite_natSet_exists_enumeration_zero (S : Set ℕ) (hS : S.Infinite)
    (hzero : 0 ∈ S) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ n 0 = 0 ∧ Set.range n = S := by
  let : Infinite S := hS.to_subtype
  let e : ℕ ≃o S := Nat.Subtype.orderIsoOfNat S
  let n : ℕ → ℕ := fun k => (e k).val
  have hn : StrictMono n := by
    intro a b hab
    exact e.strictMono hab
  refine ⟨n, hn, ?_, ?_⟩
  · have hle := e.monotone (Nat.zero_le (e.symm ⟨0, hzero⟩))
    have hz : e (e.symm ⟨0, hzero⟩) = ⟨0, hzero⟩ := e.apply_symm_apply _
    rw [hz] at hle
    exact Nat.eq_zero_of_le_zero hle
  · ext t
    constructor
    · rintro ⟨k, rfl⟩
      exact (e k).property
    · intro ht
      exact ⟨e.symm ⟨t, ht⟩, congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)⟩

/-- Nonnegativity of the horizontal coordinate makes zero a record for the -/
theorem zero_mem_records_of_L_nonneg (w : ℕ → Fin 3) (hL : ∀ j, 0 ≤ L w j) :
    0 ∈ {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j} := by
  constructor
  · intro j hj
    exact False.elim (Nat.not_lt_zero j hj)
  · intro j _
    simpa only [L, Finset.range_zero, Finset.sum_empty] using hL j

/-- Equality in the present-vertex carrier, strengthening the existing ID -/
theorem recordVertex_zero_eq_source (w : ℕ → Fin 3) :
    recordVertex w 0 = (⟨0⟩ : PresentVertex w) := rfl

/-- Infinitely many explicit records, including zero, give both kinds of
infinite extremal path from the source (`def-infinite-geo`, -/
theorem infinite_records_exists_source_extremal (w : ℕ → Fin 3)
    (hS : {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}.Infinite)
    (hzero : 0 ∈ {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}) :
    (∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) ∧
    (∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) := by
  obtain ⟨n, hn, hnzero, hrange⟩ :=
    infinite_natSet_exists_enumeration_zero _ hS hzero
  have hmem (k : ℕ) :
      (∀ j < n k, R w (n k) ≤ R w j - 1) ∧
        ∀ j, n k ≤ j → L w (n k) ≤ L w j := by
    have : n k ∈ Set.range n := ⟨k, rfl⟩
    rw [hrange] at this
    exact this
  have h := recordSequence_exists_infinite_extremal w n hn
    (fun k => (hmem k).1) (fun k => (hmem k).2)
  rw [hnzero, recordVertex_zero_eq_source] at h
  exact h

/-- For Pitman-flipped iid codes, almost surely both infinite extremal
present-edge paths exist from the source (`def-infinite-geo`,
the paper's intervals `1 ≤ a ≤ b`, with zero-based stream index `a - 1`. -/
theorem pitmanCodes_ae_exists_source_infinite_extremal :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      (∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) ∧
      (∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) := by
  filter_upwards [pitmanCodes_ae_infinite_cutSeparation_records] with ω hS
  apply infinite_records_exists_source_extremal _ hS
  apply zero_mem_records_of_L_nonneg
  intro j
  rw [kmsw_L_eq]
  exact integrateCodes_pitmanCode_fst_nonneg _ j

end DirectedDistances.KMSW
