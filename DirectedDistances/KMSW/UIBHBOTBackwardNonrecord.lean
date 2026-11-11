module

public import DirectedDistances.KMSW.UIBHBOTRotationHypothesis
public import DirectedDistances.RandomWalk.UIBHBOTPastRUnbounded
public import DirectedDistances.RandomWalk.UIBHBOTForwardUnbounded

/-! Helper statements toward Proposition 5.16 (UIBHBOT M^♭,
in the source); not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open MeasureTheory
open scoped Classical

private theorem cast_list (xs : List ℕ) :
    (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl

private theorem range_snd (f : ℕ → ℤ × ℤ) (n : ℕ) :
    ((List.range n).map f).sum.2 =
      ∑ i ∈ Finset.range n, (f i).2 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem window_integral_snd (W : ℤ → Fin 3) (N j : ℕ) :
    R (shiftedStream W N) N +
      (wholePlaneWordIntegral W ((j : ℤ) - N)).2 =
      R (shiftedStream W N) j := by
  by_cases hj : j < N
  · have hd : ((j : ℤ) - N) < 0 := by omega
    have hc : (-((j : ℤ) - N)).toNat = N - j := by omega
    simp only [wholePlaneWordIntegral, ite_eq_right (not_le.mpr hd), Prod.snd_neg,
      hc, bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_snd]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).2) j (N - j)
    have ht : (∑ i ∈ Finset.range (N - j),
        (lazyTwoDimensionalStep (shiftedStream W N (j + i))).2) =
        ∑ i ∈ Finset.range (N - j),
          (lazyTwoDimensionalStep (W (-(i : ℤ) - 1))).2 := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show j + (N - j) = N by omega, ht] at he
    change R (shiftedStream W N) N = R (shiftedStream W N) j + _ at he
    omega
  · have hd : 0 ≤ (j : ℤ) - N := by omega
    have hc : ((j : ℤ) - N).toNat = j - N := by omega
    simp only [wholePlaneWordIntegral, ite_eq_left hd, hc,
      bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_snd]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).2) N (j - N)
    have ht : (∑ i ∈ Finset.range (j - N),
        (lazyTwoDimensionalStep (shiftedStream W N (N + i))).2) =
        ∑ i ∈ Finset.range (j - N), (lazyTwoDimensionalStep (W (i : ℤ))).2 := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show N + (j - N) = j by omega, ht] at he
    exact he.symm

private theorem uibhbotBlockBoundary_neg_nat_local (w : ℤ → List (Fin 3)) (k : ℕ) :
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

private theorem uibhbotBlockBoundary_neg_nat_le (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (k : ℕ) :
    uibhbotBlockBoundary w (-(k : ℤ)) ≤ -(k : ℤ) := by
  rw [uibhbotBlockBoundary_neg_nat_local]
  have hsum : (k : ℤ) ≤
      ∑ j ∈ Finset.range k, ((w (-(j : ℤ) - 1)).length : ℤ) := by
    calc
      (k : ℤ) = ∑ _j ∈ Finset.range k, (1 : ℤ) := by simp
      _ ≤ ∑ j ∈ Finset.range k, ((w (-(j : ℤ) - 1)).length : ℤ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact_mod_cast (hw (-(j : ℤ) - 1)).1
  omega

private theorem nonneg_add_of_nat_ge_neg (x : ℤ) (M : ℕ)
    (hM : (-x).toNat ≤ M) : 0 ≤ x + (M : ℤ) := by
  by_cases hx : x < 0
  · have hxcast : ((-x).toNat : ℤ) = -x := Int.toNat_of_nonneg (by omega)
    have hMcast : ((-x).toNat : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    rw [hxcast] at hMcast
    omega
  · omega

private theorem uibhbotConcatWalk_backward_blockBoundary_snd
    (w : ℤ → List (Fin 3)) (hw : ∀ k, IsStoppedExcursionWord (w k))
    (k : ℕ) :
    (uibhbotConcatWalk w (uibhbotBlockBoundary w (-(k : ℤ)))).2 =
      -uibhbotBackwardRPartialSum w k := by
  rw [uibhbotConcatWalk_backward_blockBoundary w (fun i => (hw i).1) k]
  simp [uibhbotBackwardRPartialSum, uibhbotWordRDisplacement,
    Prod.snd_neg, Prod.snd_sum]




theorem uibhbot_hP2_of_backwardRUnbounded (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hU : ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k) :
    ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
         R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k) := by
  intro t
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  let K : ℕ := (-t).toNat + 1
  let B : ℤ := (Finset.range K).sup' (by simp [K])
    (fun j => uibhbotBackwardRPartialSum w j)
  have htimeK : (-(K : ℤ)) < t := by
    dsimp [K]
    by_cases ht : t < 0
    · rw [Int.toNat_of_nonneg (by omega : 0 ≤ -t)]
      omega
    · have ht0 : 0 ≤ t := by omega
      have hneg : (-t).toNat = 0 := by
        rw [Int.toNat_of_nonpos (show -t ≤ 0 by omega)]
      rw [hneg]
      omega
  obtain ⟨k, hk⟩ := hU (max (-(uibhbotConcatWalk w t).2) B)
  have hkR : -(uibhbotConcatWalk w t).2 < uibhbotBackwardRPartialSum w k :=
    lt_of_le_of_lt (le_max_left _ _) hk
  have hkB : B < uibhbotBackwardRPartialSum w k :=
    lt_of_le_of_lt (le_max_right _ _) hk
  have hKk : K ≤ k := by
    by_contra hnot
    have hlt : k < K := Nat.lt_of_not_ge hnot
    have hle : uibhbotBackwardRPartialSum w k ≤ B := by
      dsimp [B]
      exact Finset.le_sup' (f := fun j => uibhbotBackwardRPartialSum w j)
        (Finset.mem_range.mpr hlt)
    exact (not_lt_of_ge hle) hkB
  let b := uibhbotBlockBoundary w (-(k : ℤ))
  have hbt : b < t := by
    dsimp [b]
    have hKkZ : (K : ℤ) ≤ (k : ℤ) := by exact_mod_cast hKk
    have hneg : -(k : ℤ) ≤ -(K : ℤ) := by omega
    exact (uibhbotBlockBoundary_neg_nat_le w hw k).trans_lt
      (lt_of_le_of_lt hneg htimeK)
  have hbr : (uibhbotConcatWalk w b).2 < (uibhbotConcatWalk w t).2 := by
    dsimp [b]
    rw [uibhbotConcatWalk_backward_blockBoundary_snd w hw k]
    omega
  let M₀ := max (-b).toNat (-t).toNat
  refine ⟨M₀, ?_⟩
  intro M hM
  have hMb : (-b).toNat ≤ M := (le_max_left _ _).trans hM
  have hMt : (-t).toNat ≤ M := (le_max_right _ _).trans hM
  have hb0 : 0 ≤ b + (M : ℤ) := nonneg_add_of_nat_ge_neg b M hMb
  have ht0 : 0 ≤ t + (M : ℤ) := nonneg_add_of_nat_ge_neg t M hMt
  let ib := (b + (M : ℤ)).toNat
  let it := (t + (M : ℤ)).toNat
  have hbi : (ib : ℤ) - M = b := by
    dsimp [ib]
    rw [Int.toNat_of_nonneg hb0]
    omega
  have hti : (it : ℤ) - M = t := by
    dsimp [it]
    rw [Int.toNat_of_nonneg ht0]
    omega
  have hib : ib < it := by
    have hlt : (ib : ℤ) < (it : ℤ) := by omega
    exact_mod_cast hlt
  have hwb := window_integral_snd W M ib
  have hwt := window_integral_snd W M it
  rw [hbi] at hwb
  rw [hti] at hwt
  rw [wholePlaneWordIntegral_uibhbotCodeWord] at hwb
  rw [wholePlaneWordIntegral_uibhbotCodeWord] at hwt
  have hRlt : R (shiftedStream W M) ib < R (shiftedStream W M) it := by
    rw [← hwb, ← hwt]
    omega
  constructor
  · exact ht0
  · have hmin := runningMin_le (R (shiftedStream W M)) it ib (Nat.le_of_lt hib)
    change minR (shiftedStream W M) it < R (shiftedStream W M) it
    exact lt_of_le_of_lt hmin hRlt





theorem uibhbotWordFamilyLaw_ae_hP2_of_pos
    (h : 0 < uibhbotWordFamilyLaw
      {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k}) :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
          0 ≤ t + (M : ℤ) ∧
          (let k := (t + (M : ℤ)).toNat
           minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
             R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k) := by
  have h01 := uibhbotWordFamilyLaw_backwardRUnbounded_zero_one
  have hone : uibhbotWordFamilyLaw
      {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} = 1 := by
    rcases h01 with hzero | hone
    · rw [hzero] at h
      exact (lt_irrefl _ h).elim
    · exact hone
  have hE : MeasurableSet
      {w : ℤ → List (Fin 3) | ∀ A : ℤ, ∃ k : ℕ,
        A < uibhbotBackwardRPartialSum w k} := by
    rw [← uibhbotBackwardWordUnboundedEvent_preimage]
    exact measurableSet_uibhbotBackwardWordUnboundedEvent.preimage
      measurable_uibhbotBackwardWordSequence
  have hUae := (mem_ae_iff_prob_eq_one hE).2 hone
  filter_upwards [ae_uibhbotWordFamily_all_stopped, hUae] with w hw hU
  change ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k at hU
  exact ⟨hw, uibhbot_hP2_of_backwardRUnbounded w hw hU⟩

end DirectedDistances.KMSW
