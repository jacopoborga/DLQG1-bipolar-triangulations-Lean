module

public import DirectedDistances.KMSW.UIBHBOTRootRecord

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT \(M^\flat\),
concatenation; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

/-- Cumulative integer time of block `k` in the two-sided stopped-word concatenation; helper
toward Proposition 5.16 (`prop-disk-bs-conv`), for the UIBHBOT construction
helper, not the paper result. -/
@[expose] def uibhbotBlockBoundary (w : ℤ → List (Fin 3)) (k : ℤ) : ℤ :=
  if 0 ≤ k then
    ∑ i ∈ Finset.Ico 0 k, ((w i).length : ℤ)
  else
    -∑ i ∈ Finset.Ico k 0, ((w i).length : ℤ)

/-- Block zero starts at time zero in the stopped-excursion concatenation; helper toward
Proposition 5.16 (`prop-disk-bs-conv`) and the UIBHBOT construction
helper, not the paper result. -/
theorem uibhbotBlockBoundary_zero (w : ℤ → List (Fin 3)) :
    uibhbotBlockBoundary w 0 = 0 := by
  simp [uibhbotBlockBoundary]

/-- Consecutive block boundaries differ by the intervening word length; helper toward
Proposition 5.16 (`prop-disk-bs-conv`) and the UIBHBOT construction
helper, not the paper result. -/
theorem uibhbotBlockBoundary_succ (w : ℤ → List (Fin 3)) (k : ℤ) :
    uibhbotBlockBoundary w (k + 1) =
      uibhbotBlockBoundary w k + ((w k).length : ℤ) := by
  by_cases hk : 0 ≤ k
  · have hk' : 0 ≤ k + 1 := by omega
    rw [uibhbotBlockBoundary, ite_eq_left hk', uibhbotBlockBoundary, ite_eq_left hk]
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one (f := fun i : ℤ => ((w i).length : ℤ))
      (by omega : (0 : ℤ) ≤ k)]
  · have hk0 : k < 0 := by omega
    have hsum :
        ∑ i ∈ Finset.Ico k 0, ((w i).length : ℤ) =
          ((w k).length : ℤ) +
            ∑ i ∈ Finset.Ico (k + 1) 0, ((w i).length : ℤ) := by
      calc
        _ = ∑ i ∈ insert k (Finset.Ico (k + 1) 0), ((w i).length : ℤ) := by
          rw [Finset.insert_Ico_add_one_left_eq_Ico hk0]
        _ = _ := by rw [Finset.sum_insert (by simp)]
    by_cases hk' : k + 1 < 0
    · rw [uibhbotBlockBoundary, ite_eq_right (by omega),
        uibhbotBlockBoundary, ite_eq_right (by omega)]
      rw [hsum]
      ring
    · have heq : k = -1 := by omega
      subst k
      have hsum0 :
          ∑ i ∈ Finset.Ico (-1 : ℤ) 0, ((w i).length : ℤ) =
            ((w (-1 : ℤ)).length : ℤ) := by
        rw [← Finset.insert_Ico_add_one_left_eq_Ico (by decide : (-1 : ℤ) < 0)]
        simp
      simp [uibhbotBlockBoundary, hsum0]

/-- Positive word lengths make block boundary times strictly increasing; helper toward
Proposition 5.16 (`prop-disk-bs-conv`) and the UIBHBOT construction
helper, not the paper result. -/
theorem uibhbotBlockBoundary_strictMono (w : ℤ → List (Fin 3))
    (hw : ∀ k, 1 ≤ (w k).length) : StrictMono (uibhbotBlockBoundary w) := by
  apply strictMono_int_of_lt_succ
  intro k
  rw [uibhbotBlockBoundary_succ]
  have hlen : (0 : ℤ) < ((w k).length : ℤ) := by
    exact_mod_cast (hw k)
  omega

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^flat,
order, with their letters unchanged; not the paper result. -/
theorem uibhbotCodeWord_nonneg_reading (w : ℤ → List (Fin 3))
    (hwords : ∀ k : ℤ, 1 ≤ (w k).length) (i : ℕ) :
    uibhbotCodeWord w hwords (i : ℤ) =
      uibhbotBlockLetter (fun k => w (k : ℤ)) (fun k => hwords (k : ℤ)) i := by
  simp [uibhbotCodeWord]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^flat,
reversing each block without changing its letters; backward integration negates the steps; not
the paper result. -/
theorem uibhbotCodeWord_neg_reading (w : ℤ → List (Fin 3))
    (hwords : ∀ k : ℤ, 1 ≤ (w k).length) (i : ℕ) :
    uibhbotCodeWord w hwords (-(i : ℤ) - 1) =
      uibhbotBlockLetter (fun k => (w (-(k : ℤ) - 1)).reverse)
        (fun k => by simpa only [List.length_reverse] using hwords (-(k : ℤ) - 1)) i := by
  have hneg : ¬ 0 ≤ -(i : ℤ) - 1 := by omega
  have hnat : (-(-(i : ℤ) - 1) - 1).toNat = i := by omega
  simp only [uibhbotCodeWord, ite_eq_right hneg, hnat]

private theorem uibhbotBlockBoundary_nat (w : ℤ → List (Fin 3)) (k : ℕ) :
    uibhbotBlockBoundary w (k : ℤ) =
      ∑ j ∈ Finset.range k, ((w (j : ℤ)).length : ℤ) := by
  induction k with
  | zero => simp [uibhbotBlockBoundary]
  | succ k ih =>
      have hc : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by norm_num
      rw [hc, uibhbotBlockBoundary_succ, ih, Finset.sum_range_succ]

private theorem uibhbotBlockBoundary_neg_nat (w : ℤ → List (Fin 3)) (k : ℕ) :
    uibhbotBlockBoundary w (-(k : ℤ)) =
      -∑ j ∈ Finset.range k, ((w (-(j : ℤ) - 1)).length : ℤ) := by
  induction k with
  | zero => simp [uibhbotBlockBoundary]
  | succ k ih =>
      have hc : -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 := by omega
      have hstep : uibhbotBlockBoundary w (-(k : ℤ)) =
          uibhbotBlockBoundary w (-((k + 1 : ℕ) : ℤ)) +
            ((w (-(k : ℤ) - 1)).length : ℤ) := by
        calc
          uibhbotBlockBoundary w (-(k : ℤ)) =
              uibhbotBlockBoundary w ((-(k : ℤ) - 1) + 1) := by congr 1; omega
          _ = uibhbotBlockBoundary w (-(k : ℤ) - 1) +
              ((w (-(k : ℤ) - 1)).length : ℤ) :=
            uibhbotBlockBoundary_succ w (-(k : ℤ) - 1)
          _ = uibhbotBlockBoundary w (-((k + 1 : ℕ) : ℤ)) +
              ((w (-(k : ℤ) - 1)).length : ℤ) := by rw [hc]
      calc
        uibhbotBlockBoundary w (-((k + 1 : ℕ) : ℤ)) =
            uibhbotBlockBoundary w (-(k : ℤ)) -
              ((w (-(k : ℤ) - 1)).length : ℤ) := by rw [hstep]; ring
        _ = -(∑ j ∈ Finset.range k, ((w (-(j : ℤ) - 1)).length : ℤ)) -
              ((w (-(k : ℤ) - 1)).length : ℤ) := by rw [ih]
        _ = -∑ j ∈ Finset.range (k + 1),
              ((w (-(j : ℤ) - 1)).length : ℤ) := by
          rw [Finset.sum_range_succ]
          ring

private theorem uibhbotFlatMapRange_length (f : ℕ → List (Fin 3)) (k : ℕ) :
    ((List.range k).flatMap f).length = ∑ j ∈ Finset.range k, (f j).length := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp [List.range_succ, List.flatMap_append, ih, Finset.sum_range_succ]

private theorem uibhbotFlatMapRange_count_le (f : ℕ → List (Fin 3))
    (hpos : ∀ j, 0 < (f j).length) (k : ℕ) :
    k ≤ ((List.range k).flatMap f).length := by
  rw [uibhbotFlatMapRange_length]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hp := hpos k
      omega

private theorem uibhbotTakeFlatMapRange_blocks (f : ℕ → List (Fin 3))
    (k n : ℕ) (hkn : k ≤ n)
    (hlen : ((List.range k).flatMap f).length = n) :
    ((List.range n).flatMap f).take n = (List.range k).flatMap f := by
  have hrange : List.range n = List.range k ++ (List.range (n - k)).map (fun x => k + x) := by
    calc
      List.range n = List.range (k + (n - k)) := by congr 1; omega
      _ = List.range k ++ (List.range (n - k)).map (fun x => k + x) := by
        rw [List.range_add]
  rw [hrange, List.flatMap_append, List.flatMap_map]
  simp [hlen]

private theorem uibhbotFlatMapRange_displacement (f : ℕ → List (Fin 3)) (k : ℕ) :
    ((((List.range k).flatMap f).map lazyTwoDimensionalStep).sum) =
      ∑ j ∈ Finset.range k, ((f j).map lazyTwoDimensionalStep).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp [List.range_succ, List.flatMap_append, ih, List.map_append,
        List.sum_append, Finset.sum_range_succ]

/-- The integrated walk at a forward block boundary sums the preceding block displacements;
helper toward Proposition 5.16 (`prop-disk-bs-conv`) and the UIBHBOT construction
helper, not the paper result. -/
theorem uibhbotConcatWalk_forward_blockBoundary (w : ℤ → List (Fin 3))
    (hwords : ∀ k : ℤ, 1 ≤ (w k).length) (k : ℕ) :
    uibhbotConcatWalk w (uibhbotBlockBoundary w (k : ℤ)) =
      ∑ j ∈ Finset.range k, ((w (j : ℤ)).map lazyTwoDimensionalStep).sum := by
  let f : ℕ → List (Fin 3) := fun j => w (j : ℤ)
  let n : ℕ := ((List.range k).flatMap f).length
  have hlen : n = ∑ j ∈ Finset.range k, (f j).length := by
    dsimp [n]
    exact uibhbotFlatMapRange_length f k
  have hboundary : uibhbotBlockBoundary w (k : ℤ) = (n : ℤ) := by
    rw [uibhbotBlockBoundary_nat]
    simp [n, hlen, f]
  have hpos : ∀ j, 0 < (f j).length := by
    intro j
    have h := hwords (j : ℤ)
    dsimp [f]
    omega
  have hkn : k ≤ n := by
    dsimp [n]
    exact uibhbotFlatMapRange_count_le f hpos k
  have htake := uibhbotTakeFlatMapRange_blocks f k n hkn (by rfl)
  have hcast : ((List.range n).map (fun j : ℕ => (j : ℤ))).flatMap
      (fun j : ℤ => w j) = (List.range n).flatMap f := by
    rw [List.flatMap_map]
  rw [hboundary]
  simp only [uibhbotConcatWalk,
    ite_eq_left (show 0 ≤ (n : ℤ) by positivity), Int.toNat_natCast, bind_pure_comp]
  rw [show (Nat.cast <$> List.range n).flatMap (fun j : ℤ => w j) =
      (List.range n).flatMap f from hcast]
  change ((((List.range n).flatMap f).take n).map lazyTwoDimensionalStep).sum = _
  rw [htake, uibhbotFlatMapRange_displacement]

/-- The integrated walk at a backward block boundary is the negative sum of preceding
reversed-word displacements, equal to the original word displacements; helper toward
Proposition 5.16 (`prop-disk-bs-conv`) and the UIBHBOT construction
helper, not the paper result. -/
theorem uibhbotConcatWalk_backward_blockBoundary (w : ℤ → List (Fin 3))
    (hwords : ∀ k : ℤ, 1 ≤ (w k).length) (k : ℕ) :
    uibhbotConcatWalk w (uibhbotBlockBoundary w (-(k : ℤ))) =
      -∑ j ∈ Finset.range k, ((w (-(j : ℤ) - 1)).map lazyTwoDimensionalStep).sum := by
  let f : ℕ → List (Fin 3) := fun j => (w (-(j : ℤ) - 1)).reverse
  let n : ℕ := ((List.range k).flatMap f).length
  have hlen : n = ∑ j ∈ Finset.range k, (f j).length := by
    dsimp [n]
    exact uibhbotFlatMapRange_length f k
  have hboundary : uibhbotBlockBoundary w (-(k : ℤ)) = -(n : ℤ) := by
    rw [uibhbotBlockBoundary_neg_nat]
    simp [n, hlen, f]
  have hpos : ∀ j, 0 < (f j).length := by
    intro j
    have h := hwords (-(j : ℤ) - 1)
    dsimp [f]
    simpa only [List.length_reverse] using (show 0 < (w (-(j : ℤ) - 1)).length by omega)
  have hkn : k ≤ n := by
    dsimp [n]
    exact uibhbotFlatMapRange_count_le f hpos k
  have htake := uibhbotTakeFlatMapRange_blocks f k n hkn (by rfl)
  by_cases hk : k = 0
  · subst k
    simp [uibhbotBlockBoundary, uibhbotConcatWalk]
  have hn : 0 < n := lt_of_lt_of_le (Nat.pos_of_ne_zero hk) hkn
  have hcast : ((List.range n).map (fun j : ℕ => (j : ℤ))).flatMap
      (fun j : ℤ => (w (-j - 1)).reverse) = (List.range n).flatMap f := by
    rw [List.flatMap_map]
  rw [hboundary]
  have htime : (-(-(n : ℤ))).toNat = n := by simp
  simp only [uibhbotConcatWalk, ite_eq_right (by omega : ¬ 0 ≤ -(n : ℤ)), htime,
    bind_pure_comp]
  rw [show (Nat.cast <$> List.range n).flatMap
      (fun j : ℤ => (w (-j - 1)).reverse) = (List.range n).flatMap f from hcast]
  change -((((List.range n).flatMap f).take n).map lazyTwoDimensionalStep).sum = _
  rw [htake, uibhbotFlatMapRange_displacement]
  simp [f, List.map_reverse, List.sum_reverse]

private theorem uibhbotStoppedDisplacement_sum_fst (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (k : ℕ) :
    (∑ j ∈ Finset.range k, ((w (j : ℤ)).map lazyTwoDimensionalStep).sum).1 = -(k : ℤ) := by
  rw [Prod.fst_sum]
  calc
    _ = ∑ j ∈ Finset.range k, (-1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hw (j : ℤ)).2.1
    _ = -(k : ℤ) := by simp

private theorem uibhbotStoppedBackwardDisplacement_sum_fst (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      ((w (-(j : ℤ) - 1)).map lazyTwoDimensionalStep).sum).1 = -(k : ℤ) := by
  rw [Prod.fst_sum]
  calc
    _ = ∑ j ∈ Finset.range k, (-1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hw (-(j : ℤ) - 1)).2.1
    _ = -(k : ℤ) := by simp

/-- For stopped excursion words, the first coordinate is `-k` at every integer block boundary
`k`; helper toward Proposition 5.16 (`prop-disk-bs-conv`) and the UIBHBOT construction
helper, not the paper result. -/
theorem uibhbotConcatWalk_stopped_blockBoundary_fst (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (k : ℤ) :
    (uibhbotConcatWalk w (uibhbotBlockBoundary w k)).1 = -k := by
  by_cases hk : 0 ≤ k
  · have hn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
    rw [← hn, uibhbotConcatWalk_forward_blockBoundary w (fun i => (hw i).1)]
    exact uibhbotStoppedDisplacement_sum_fst w hw k.toNat
  · let n : ℕ := (-k).toNat
    have hn : (n : ℤ) = -k := by
      dsimp [n]
      exact Int.toNat_of_nonneg (by omega)
    have hk' : k = -(n : ℤ) := by omega
    rw [hk', uibhbotConcatWalk_backward_blockBoundary w (fun i => (hw i).1)]
    rw [Prod.fst_neg, uibhbotStoppedBackwardDisplacement_sum_fst w hw n]

end DirectedDistances.KMSW
