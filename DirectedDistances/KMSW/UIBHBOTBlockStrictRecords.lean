module

public import DirectedDistances.KMSW.UIBHBOTBlockRecords

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^♭,
concatenation; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private abbrev uibhbotFirstSum (v : List (Fin 3)) : ℤ :=
  ((v.map lazyTwoDimensionalStep).sum).1

private theorem uibhbotFlatMapRange_length (f : ℕ → List (Fin 3)) (k : ℕ) :
    ((List.range k).flatMap f).length = ∑ j ∈ Finset.range k, (f j).length := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp [List.range_succ, List.flatMap_append, ih, Finset.sum_range_succ]

private theorem uibhbotFlatMapRange_displacement (f : ℕ → List (Fin 3)) (k : ℕ) :
    ((((List.range k).flatMap f).map lazyTwoDimensionalStep).sum) =
      ∑ j ∈ Finset.range k, ((f j).map lazyTwoDimensionalStep).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp [List.range_succ, List.flatMap_append, ih, List.map_append,
        List.sum_append, Finset.sum_range_succ]

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

private theorem uibhbotBlockBoundary_nat (w : ℤ → List (Fin 3)) (k : ℕ) :
    uibhbotBlockBoundary w (k : ℤ) =
      ∑ j ∈ Finset.range k, ((w (j : ℤ)).length : ℤ) := by
  induction k with
  | zero => simp [uibhbotBlockBoundary]
  | succ k ih =>
      have hc : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by norm_num
      rw [hc, uibhbotBlockBoundary_succ, ih, Finset.sum_range_succ]

private theorem uibhbotFlatMapRange_prefix (f : ℕ → List (Fin 3))
    {a b : ℕ} (hab : a ≤ b) :
    (List.range a).flatMap f <+: (List.range b).flatMap f := by
  have hb : b = a + (b - a) := by omega
  rw [hb, List.range_add, List.flatMap_append]
  exact List.prefix_append _ _

private theorem uibhbotTake_eq_of_prefix {α : Type*} {xs ys : List α}
    (h : xs <+: ys) (n : ℕ) (hn : n ≤ xs.length) : xs.take n = ys.take n := by
  rcases h with ⟨tail, rfl⟩
  simp [List.take_append, Nat.sub_eq_zero_of_le hn]

private theorem uibhbotTake_append_length_add {α : Type*} (xs ys : List α)
    (i : ℕ) :
    (xs ++ ys).take (xs.length + i) = xs ++ ys.take i := by
  rw [List.take_append]
  simp

private theorem uibhbotConcatWalk_forward_inside (w : ℤ → List (Fin 3))
    (hwords : ∀ k : ℤ, 1 ≤ (w k).length) (k i : ℕ)
    (hi : i ≤ (w (k : ℤ)).length) :
    (uibhbotConcatWalk w (uibhbotBlockBoundary w (k : ℤ) + i)).1 =
      (∑ j ∈ Finset.range k,
        ((w (j : ℤ)).map lazyTwoDimensionalStep).sum).1 +
        uibhbotFirstSum ((w (k : ℤ)).take i) := by
  let f : ℕ → List (Fin 3) := fun j => w (j : ℤ)
  let pre : List (Fin 3) := (List.range k).flatMap f
  let full : List (Fin 3) := (List.range (k + 1)).flatMap f
  let n : ℕ := pre.length
  have hn : n = ∑ j ∈ Finset.range k, (f j).length := by
    dsimp [n, pre]
    exact uibhbotFlatMapRange_length f k
  have hboundary : uibhbotBlockBoundary w (k : ℤ) = (n : ℤ) := by
    rw [uibhbotBlockBoundary_nat]
    simp [n, hn, f]
  have hpre : k ≤ n := by
    dsimp [n, pre, f]
    apply uibhbotFlatMapRange_count_le
    intro j
    have h := hwords (j : ℤ)
    omega
  have hfull : full = pre ++ w (k : ℤ) := by
    dsimp [full, pre, f]
    rw [List.range_succ, List.flatMap_append]
    simp
  have hfullLen : full.length = n + (w (k : ℤ)).length := by
    rw [hfull]
    simp [n]
  have hm : k + 1 ≤ n + i ∨ i = 0 := by omega
  have hmi : n + i ≤ full.length := by rw [hfullLen]; omega
  have hcast (m : ℕ) :
      ((List.range m).map (fun j : ℕ => (j : ℤ))).flatMap
          (fun j : ℤ => w j) =
        (List.range m).flatMap f := by
    rw [List.flatMap_map]
  have htake :
      ((List.range (n + i)).flatMap f).take (n + i) =
        pre ++ (w (k : ℤ)).take i := by
    by_cases hiz : i = 0
    · subst i
      have hprefix' : pre <+: (List.range n).flatMap f := by
        change (List.range k).flatMap f <+: (List.range n).flatMap f
        exact uibhbotFlatMapRange_prefix f (a := k) (b := n) hpre
      have htake' := uibhbotTake_eq_of_prefix hprefix' n (by
        exact le_rfl)
      simpa [n] using htake'.symm
    · have hprefix' : full <+: (List.range (n + i)).flatMap f := by
        have hk : k + 1 ≤ n + i := by omega
        change (List.range (k + 1)).flatMap f <+:
          (List.range (n + i)).flatMap f
        exact uibhbotFlatMapRange_prefix f (a := k + 1) (b := n + i) hk
      have ht := uibhbotTake_eq_of_prefix hprefix' (n + i) hmi
      have happend : full.take (n + i) = pre ++ (w (k : ℤ)).take i := by
        rw [hfull, uibhbotTake_append_length_add]
      exact ht.symm.trans happend
  have htCast :
      (uibhbotBlockBoundary w (k : ℤ) + i) = ((n + i : ℕ) : ℤ) := by
    rw [hboundary]
    norm_cast
  rw [htCast]
  have hnonneg : 0 ≤ ((n + i : ℕ) : ℤ) := by positivity
  simp only [uibhbotConcatWalk, ite_eq_left hnonneg, Int.toNat_natCast,
    bind_pure_comp]
  have hcast' :
      (Nat.cast <$> List.range (n + i)).flatMap (fun j : ℤ => w j) =
        (List.range (n + i)).flatMap f := by
    simpa using hcast (n + i)
  rw [hcast', htake, List.map_append, List.sum_append, Prod.fst_add]
  have hdisp := congrArg Prod.fst (uibhbotFlatMapRange_displacement f k)
  change ((pre.map lazyTwoDimensionalStep).sum).1 = _ at hdisp
  rw [hdisp]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^♭,
not the paper result. -/
theorem uibhbotConcatWalk_forward_withinBlock_fst (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) (k i : ℕ)
    (hi : i < (w (k : ℤ)).length) :
    -(k : ℤ) ≤
      (uibhbotConcatWalk w
        (uibhbotBlockBoundary w (k : ℤ) + i)).1 := by
  have hformula := uibhbotConcatWalk_forward_inside w
    (fun j => (hw j).1) k i hi.le
  have hprefix := (hw (k : ℤ)).2.2 i hi
  change -1 < uibhbotFirstSum ((w (k : ℤ)).take i) at hprefix
  have hsum : 0 ≤ uibhbotFirstSum ((w (k : ℤ)).take i) := by omega
  have htotal :
      (∑ j ∈ Finset.range k,
        ((w (j : ℤ)).map lazyTwoDimensionalStep).sum).1 = -(k : ℤ) := by
    rw [Prod.fst_sum]
    calc
      _ = ∑ j ∈ Finset.range k, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hw (j : ℤ)).2.1
      _ = -(k : ℤ) := by simp
  rw [hformula, htotal]
  omega

private theorem uibhbotFirstSum_reverse_take_drop (v : List (Fin 3)) (i : ℕ)
    (hi : i ≤ v.length) :
    uibhbotFirstSum (v.reverse.take (v.length - i)) = uibhbotFirstSum (v.drop i) := by
  rw [List.take_reverse]
  simp [uibhbotFirstSum, List.map_reverse, List.sum_reverse, Nat.sub_sub_self hi]

private theorem uibhbotStoppedDropFirstSum_le_neg_one (v : List (Fin 3))
    (hv : IsStoppedExcursionWord v) {i : ℕ} (hi : i < v.length) :
    uibhbotFirstSum (v.drop i) ≤ -1 := by
  have hprefix := hv.2.2 i hi
  change -1 < uibhbotFirstSum (v.take i) at hprefix
  have hsplit : uibhbotFirstSum v =
      uibhbotFirstSum (v.take i) + uibhbotFirstSum (v.drop i) := by
    have hparts :
        ((v.map lazyTwoDimensionalStep).take i).sum +
          ((v.map lazyTwoDimensionalStep).drop i).sum =
            (v.map lazyTwoDimensionalStep).sum := by
      calc
        _ = ((v.map lazyTwoDimensionalStep).take i ++
            (v.map lazyTwoDimensionalStep).drop i).sum := by rw [List.sum_append]
        _ = _ := by rw [List.take_append_drop]
    have hfst := congrArg Prod.fst hparts.symm
    change ((v.map lazyTwoDimensionalStep).sum).1 =
      ((v.map lazyTwoDimensionalStep).take i).sum.1 +
        ((v.map lazyTwoDimensionalStep).drop i).sum.1 at hfst
    simpa [uibhbotFirstSum, List.map_take, List.map_drop] using hfst
  have htotal : uibhbotFirstSum v = -1 := hv.2.1
  omega

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

private theorem uibhbotConcatWalk_backward_inside (w : ℤ → List (Fin 3))
    (hwords : ∀ k : ℤ, 1 ≤ (w k).length) (k i : ℕ)
    (hi : i < (w (-(k : ℤ) - 1)).length) :
    (uibhbotConcatWalk w
      (uibhbotBlockBoundary w (-(k : ℤ) - 1) + i)).1 =
      -((∑ j ∈ Finset.range k,
        ((w (-(j : ℤ) - 1)).map lazyTwoDimensionalStep).sum).1 +
        uibhbotFirstSum ((w (-(k : ℤ) - 1)).drop i)) := by
  let f : ℕ → List (Fin 3) := fun j => (w (-(j : ℤ) - 1)).reverse
  let pre : List (Fin 3) := (List.range k).flatMap f
  let word : List (Fin 3) := w (-(k : ℤ) - 1)
  let n : ℕ := pre.length
  have hn : n = ∑ j ∈ Finset.range k, (f j).length := by
    dsimp [n, pre]
    exact uibhbotFlatMapRange_length f k
  have hboundary : uibhbotBlockBoundary w (-(k : ℤ) - 1) = -((n + word.length : ℕ) : ℤ) := by
    have hbn := uibhbotBlockBoundary_neg_nat w (k + 1)
    have hk : -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 := by omega
    rw [hk] at hbn
    have hlenZ : (n : ℤ) =
        ∑ j ∈ Finset.range k, ((w (-(j : ℤ) - 1)).length : ℤ) := by
      dsimp [n, pre]
      rw [uibhbotFlatMapRange_length]
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      simp [f]
    rw [hbn]
    rw [Finset.sum_range_succ, ← hlenZ]
    push_cast
    ring
  have hpre : k ≤ n := by
    dsimp [n, pre, f]
    apply uibhbotFlatMapRange_count_le
    intro j
    have h := hwords (-(j : ℤ) - 1)
    simpa only [List.length_reverse] using (show 0 < (w (-(j : ℤ) - 1)).length by omega)
  have hwordpos : 0 < word.length := by
    dsimp [word]
    have h := hwords (-(k : ℤ) - 1)
    omega
  have hiword : i < word.length := by simpa [word] using hi
  have hfull : (List.range (k + 1)).flatMap f = pre ++ word.reverse := by
    dsimp [pre, f, word]
    rw [List.range_succ, List.flatMap_append]
    simp
  have hfullLen : ((List.range (k + 1)).flatMap f).length = n + word.length := by
    rw [hfull]
    simp [n]
  let r : ℕ := word.length - i
  let m : ℕ := n + r
  have hrpos : 0 < r := by
    dsimp [r]
    omega
  have hmle : m ≤ n + word.length := by
    dsimp [m, r]
    omega
  have hmblocks : k + 1 ≤ m := by
    dsimp [m]
    omega
  have hprefix : (List.range (k + 1)).flatMap f <+: (List.range m).flatMap f :=
    uibhbotFlatMapRange_prefix f hmblocks
  have htakePrefix := uibhbotTake_eq_of_prefix hprefix m (by
    rw [hfullLen]
    exact hmle)
  have htakeFull :
      ((List.range m).flatMap f).take m = pre ++ word.reverse.take r := by
    calc
      _ = ((List.range (k + 1)).flatMap f).take m := htakePrefix.symm
      _ = (pre ++ word.reverse).take m := by rw [hfull]
      _ = pre ++ word.reverse.take r := by
        rw [uibhbotTake_append_length_add]
  have htime :
      uibhbotBlockBoundary w (-(k : ℤ) - 1) + i = -(m : ℤ) := by
    rw [hboundary]
    dsimp [m, r]
    have hi' : i ≤ word.length := hiword.le
    omega
  have hcast (q : ℕ) :
      ((List.range q).map (fun j : ℕ => (j : ℤ))).flatMap
          (fun j : ℤ => (w (-j - 1)).reverse) = (List.range q).flatMap f := by
    rw [List.flatMap_map]
  have hnegative : -(m : ℤ) < 0 := by
    have : 0 < m := by dsimp [m]; omega
    omega
  have hnat : (-(-(m : ℤ))).toNat = m := by simp
  rw [htime]
  simp only [uibhbotConcatWalk,
    ite_eq_right (show ¬ 0 ≤ -(m : ℤ) by omega), hnat, bind_pure_comp]
  have hcast' : (Nat.cast <$> List.range m).flatMap
      (fun j : ℤ => (w (-j - 1)).reverse) = (List.range m).flatMap f := by
    simpa using hcast m
  rw [hcast', htakeFull, List.map_append, List.sum_append]
  have hdisp := congrArg Prod.fst (uibhbotFlatMapRange_displacement f k)
  change ((pre.map lazyTwoDimensionalStep).sum).1 = _ at hdisp
  have hrevsum :
      (∑ j ∈ Finset.range k, ((f j).map lazyTwoDimensionalStep).sum) =
        ∑ j ∈ Finset.range k,
          ((w (-(j : ℤ) - 1)).map lazyTwoDimensionalStep).sum := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [f]
    simp [List.map_reverse, List.sum_reverse]
  have hdisp' : ((pre.map lazyTwoDimensionalStep).sum).1 =
      (∑ j ∈ Finset.range k,
        ((w (-(j : ℤ) - 1)).map lazyTwoDimensionalStep).sum).1 := by
    calc
      _ = (∑ j ∈ Finset.range k, ((f j).map lazyTwoDimensionalStep).sum).1 := hdisp
      _ = _ := by rw [hrevsum]
  have hreverse := uibhbotFirstSum_reverse_take_drop word i hi.le
  have hreverse' : (((word.reverse.take r).map lazyTwoDimensionalStep).sum).1 =
      uibhbotFirstSum (word.drop i) := by
    dsimp [uibhbotFirstSum] at hreverse ⊢
    simpa [r] using hreverse
  change -(((pre.map lazyTwoDimensionalStep).sum).1 +
      (((word.reverse.take r).map lazyTwoDimensionalStep).sum).1) = _
  rw [hdisp', hreverse']

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^♭,
every point before its endpoint stays at or above the block's starting level; not the paper
result. -/
theorem uibhbotConcatWalk_backward_withinBlock_fst (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) (k i : ℕ)
    (hi : i < (w (-(k : ℤ) - 1)).length) :
    (k : ℤ) + 1 ≤
      (uibhbotConcatWalk w
        (uibhbotBlockBoundary w (-(k : ℤ) - 1) + i)).1 := by
  have hformula := uibhbotConcatWalk_backward_inside w
    (fun j => (hw j).1) k i hi
  have hprefix := (hw (-(k : ℤ) - 1)).2.2 i hi
  change -1 < uibhbotFirstSum ((w (-(k : ℤ) - 1)).take i) at hprefix
  have hprev : (∑ j ∈ Finset.range k,
      ((w (-(j : ℤ) - 1)).map lazyTwoDimensionalStep).sum).1 = -(k : ℤ) := by
    rw [Prod.fst_sum]
    calc
      _ = ∑ j ∈ Finset.range k, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hw (-(j : ℤ) - 1)).2.1
      _ = -(k : ℤ) := by simp
  have hdrop := uibhbotStoppedDropFirstSum_le_neg_one
    (w (-(k : ℤ) - 1)) (hw _) hi
  rw [hformula]
  rw [hprev]
  omega

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; UIBHBOT M^flat,
each block interval; not the paper result. -/
theorem uibhbotConcatWalk_blockInterval_fst (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, IsStoppedExcursionWord (w k)) (j t : ℤ)
    (hlo : uibhbotBlockBoundary w j ≤ t)
    (hhi : t < uibhbotBlockBoundary w (j + 1)) :
    -j ≤ (uibhbotConcatWalk w t).1 := by
  by_cases hj : 0 ≤ j
  · let k := j.toNat
    have hjcast : (k : ℤ) = j := Int.toNat_of_nonneg hj
    let i := (t - uibhbotBlockBoundary w j).toNat
    have hiCast : (i : ℤ) = t - uibhbotBlockBoundary w j :=
      Int.toNat_of_nonneg (by omega)
    have htime : uibhbotBlockBoundary w j + (i : ℤ) = t := by
      omega
    have hi : i < (w j).length := by
      have hz : (i : ℤ) < (w j).length := by
        rw [← htime, uibhbotBlockBoundary_succ] at hhi
        omega
      exact_mod_cast hz
    have hik : i < (w (k : ℤ)).length := by rw [hjcast]; exact hi
    have htime' : uibhbotBlockBoundary w (k : ℤ) + (i : ℤ) = t := by
      rw [hjcast]
      exact htime
    have hbound := uibhbotConcatWalk_forward_withinBlock_fst w hw k i hik
    rw [← htime']
    have hlevel : -(k : ℤ) = -j := by omega
    simpa only [hlevel] using hbound
  · let k := (-j - 1).toNat
    have hkcast : (k : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
    have hjcast : -(k : ℤ) - 1 = j := by omega
    let i := (t - uibhbotBlockBoundary w j).toNat
    have hiCast : (i : ℤ) = t - uibhbotBlockBoundary w j :=
      Int.toNat_of_nonneg (by omega)
    have htime : uibhbotBlockBoundary w j + (i : ℤ) = t := by
      omega
    have hi : i < (w j).length := by
      have hz : (i : ℤ) < (w j).length := by
        rw [← htime, uibhbotBlockBoundary_succ] at hhi
        omega
      exact_mod_cast hz
    have hik : i < (w (-(k : ℤ) - 1)).length := by rw [hjcast]; exact hi
    have htime' :
        uibhbotBlockBoundary w (-(k : ℤ) - 1) + (i : ℤ) = t := by
      rw [hjcast]
      exact htime
    have hbound := uibhbotConcatWalk_backward_withinBlock_fst w hw k i hik
    rw [← htime']
    have hlevel : (k : ℤ) + 1 = -j := by omega
    simpa only [hlevel] using hbound
