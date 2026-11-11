module

public import DirectedDistances.KMSW.PastReversalColimit
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel
public import DirectedDistances.KMSW.WholePlanePastGlueData
import DirectedDistances.KMSW.MeasurableCutEvents
import DirectedDistances.RandomWalk.ExcursionBlockUniformTail
import Mathlib.Tactic.FinCases

/-! # One-sided facts for the conditioned UIBHBOT past

These are prerequisites for a drawing adapted to the conditioned past. They do not
assert a whole-plane drawing or a realized face correspondence. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section5

private theorem cast_list (xs : List ℕ) :
    (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl

private theorem range_sum (f : ℕ → ℤ × ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp only [List.range_zero, List.map_nil, List.sum_nil,
      Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton, Finset.sum_range_succ, ih]

private theorem step_swap (c : Fin 3) :
    lazyTwoDimensionalStep (Equiv.swap (0 : Fin 3) 1 c) =
      -Prod.swap (lazyTwoDimensionalStep c) := by
  fin_cases c <;> norm_num [Equiv.swap_apply_def, lazyTwoDimensionalStep]

/-- Reading the negative-time letters backwards with the KMSW swap exchanges the
coordinates of the original walk at negative times. -/
theorem kmswPastCode_coordinates (W : ℤ → Fin 3) (n : ℕ) :
    L (kmswPastCode W) n = (wholePlaneWordIntegral W (-(n : ℤ))).2 ∧
      R (kmswPastCode W) n = (wholePlaneWordIntegral W (-(n : ℤ))).1 := by
  by_cases hn : n = 0
  · subst n
    simp [L, R, wholePlaneWordIntegral]
  have hneg : ¬ 0 ≤ -(n : ℤ) := by omega
  have hidx (i : ℕ) : -1 - (i : ℤ) = -(i : ℤ) - 1 := by omega
  simp only [wholePlaneWordIntegral, ite_eq_right hneg, neg_neg,
    Int.toNat_natCast, bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_sum,
    Prod.snd_neg, Prod.fst_neg, Prod.fst_sum, Prod.snd_sum, L, R,
    kmswPastCode, step_swap, Prod.fst_neg, Prod.snd_neg, Prod.swap,
    Finset.sum_neg_distrib, hidx, and_self]

private theorem negative_level_hit (f : ℕ → ℤ) (hf : f 0 = 0)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (a : ℤ) (ha : a < 0)
    (hbelow : ∃ n, f n ≤ a) : ∃ n, f n = a := by
  let n := Nat.find hbelow
  have hn : f n ≤ a := Nat.find_spec hbelow
  have hpos : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hz, hf] at hn
    omega
  have hprev : a < f (n - 1) := by
    have hh := Nat.find_min hbelow (show n - 1 < n by omega)
    omega
  have hs := hstep (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hs
  exact ⟨n, by omega⟩

private theorem stopped_past_leftHit (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hU : ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k) :
    ∀ a : ℤ, a ≤ -1 → ∃ n,
      L (kmswPastCode (uibhbotCodeWord w (fun k => (hw k).1))) n = a := by
  intro a ha
  refine negative_level_hit _ (by simp [L]) ?_ a (by omega) ?_
  · intro n
    have hs : L (kmswPastCode (uibhbotCodeWord w (fun k => (hw k).1))) (n + 1) =
        L (kmswPastCode (uibhbotCodeWord w (fun k => (hw k).1))) n +
          (lazyTwoDimensionalStep
            (kmswPastCode (uibhbotCodeWord w (fun k => (hw k).1)) n)).1 :=
      Finset.sum_range_succ _ _
    rw [hs]
    change _ ≤ _ + (_ - 1)
    omega
  · obtain ⟨k, hk⟩ := hU (-a)
    let b := uibhbotBlockBoundary w (-(k : ℤ))
    have hb : b ≤ 0 := by
      have h := (uibhbotBlockBoundary_strictMono w (fun i => (hw i).1)).monotone
        (show -(k : ℤ) ≤ 0 by omega)
      simpa only [uibhbotBlockBoundary_zero] using h
    have ht : -(((-b).toNat : ℕ) : ℤ) = b := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -b)]
      omega
    refine ⟨(-b).toNat, ?_⟩
    rw [(kmswPastCode_coordinates _ _).1, ht,
      wholePlaneWordIntegral_uibhbotCodeWord]
    dsimp only [b]
    rw [uibhbotConcatWalk_backward_blockBoundary w (fun i => (hw i).1) k]
    have he : (-(∑ j ∈ Finset.range k,
        ((w (-(j : ℤ) - 1)).map lazyTwoDimensionalStep).sum)).2 =
        -uibhbotBackwardRPartialSum w k := by
      simp only [Prod.snd_neg, Prod.snd_sum, uibhbotBackwardRPartialSum,
        uibhbotWordRDisplacement]
    rw [he]
    omega

private theorem stopped_past_R_pos (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (n : ℕ) (hn : 0 < n) :
    0 < R (kmswPastCode (uibhbotCodeWord w (fun k => (hw k).1))) n := by
  have hr := kmswStage_reverse_R
    (kmswPastCode (uibhbotCodeWord w (fun k => (hw k).1)))
    (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) n) n
    (kmswPastCode_rev _ n) (j := n) le_rfl
  have hs := uibhbotCode_strictRecord w hw n hn 0 hn
  have hz : L (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) n) 0 = 0 := by
    simp only [L, Finset.range_zero, Finset.sum_empty]
  rw [Nat.sub_self, hz] at hr
  rw [hz] at hs
  omega

private theorem measurable_kmswPastCode : Measurable kmswPastCode := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_of_countable (Equiv.swap (0 : Fin 3) 1)).comp
    (measurable_pi_apply (-1 - (i : ℤ)))

/-- Almost surely the conditioned past code hits every negative L-level, simultaneously. -/
theorem uibhbotCodeLawRel_ae_past_leftHit :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a := by
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
  apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable ?_).mpr
  · have hE : MeasurableSet
        {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} := by
      rw [← uibhbotBackwardWordUnboundedEvent_preimage]
      exact measurableSet_uibhbotBackwardWordUnboundedEvent.preimage
        measurable_uibhbotBackwardWordSequence
    filter_upwards [ae_uibhbotWordFamily_all_stopped,
      (mem_ae_iff_prob_eq_one hE).mpr uibhbotWordFamilyLaw_backwardRUnbounded] with w hw hU
    rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
    exact stopped_past_leftHit w hw hU
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun n =>
        (measurableSet_L n (fun x => x = a)).preimage measurable_kmswPastCode

/-- Almost surely R is zero at time zero and strictly positive at every positive time
of the past code. In particular, it never hits a negative level. -/
theorem uibhbotCodeLawRel_ae_past_R_nonneg :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      (∀ n, 0 ≤ R (kmswPastCode W) n) ∧
        (∀ n, 0 < n → 0 < R (kmswPastCode W) n) := by
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
  apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable ?_).mpr
  · filter_upwards [ae_uibhbotWordFamily_all_stopped] with w hw
    rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
    constructor
    · intro n
      by_cases hn : n = 0
      · subst n; simp only [R, Finset.range_zero, Finset.sum_empty, le_refl]
      · exact (stopped_past_R_pos w hw n (by omega)).le
    · exact stopped_past_R_pos w hw
  · change MeasurableSet
      ({W : ℤ → Fin 3 | ∀ n, 0 ≤ R (kmswPastCode W) n} ∩
        {W : ℤ → Fin 3 | ∀ n, 0 < n → 0 < R (kmswPastCode W) n})
    apply MeasurableSet.inter
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun n =>
        (measurableSet_R n (fun x => 0 ≤ x)).preimage measurable_kmswPastCode
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        (measurableSet_R n (fun x => 0 < x)).preimage measurable_kmswPastCode

/-- The conditioned past code almost surely has finite geometric incidence, including
missing edges. This supplies the incidence input of `monotoneLimitDrawing`
without any past boundary-hit witness. -/
theorem uibhbotCodeLawRel_ae_past_finiteIncidence :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      KMSWFiniteIncidence (kmswPastCode W) := by
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
  apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable
    (measurableSet_finiteIncidence.preimage measurable_kmswPastCode)).mpr
  filter_upwards [uibhbotWordFamilyLaw_ae_rotationHypothesis] with w hrot
  obtain ⟨hw, hrot⟩ := hrot
  rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
  exact WholePlanePastGlueData.past_finiteIncidence _ hrot

end DirectedDistances.KMSW
