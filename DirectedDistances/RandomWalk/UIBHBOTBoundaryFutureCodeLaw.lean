module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel
public import DirectedDistances.RandomWalk.UIBHBOTForwardPrefixLaw
public import DirectedDistances.RandomWalk.UIBHBOTWordShift
public import DirectedDistances.KMSW.UIBHBOTLevelBarrier
public import DirectedDistances.KMSW.WholePlaneLemma38IntegerStart
public import DirectedDistances.KMSW.WholePlaneRunSubmap









public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
@[expose] def UIBHBOTBoundaryHit (k t : ℤ) (W : ℤ → Fin 3) : Prop :=
  (wholePlaneWordIntegral W t).1 = k ∧
    ∀ s : ℤ, s < t → (wholePlaneWordIntegral W s).1 ≠ k

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
@[expose] noncomputable def uibhbotBoundaryHitTime (k : ℤ) (W : ℤ → Fin 3) : ℤ :=
  by
    classical
    exact if h : ∃ t : ℤ, UIBHBOTBoundaryHit k t W then Classical.choose h else 0

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem boundaryHit_unique {k t s : ℤ} {W : ℤ → Fin 3}
    (ht : UIBHBOTBoundaryHit k t W) (hs : UIBHBOTBoundaryHit k s W) : t = s := by
  rcases lt_trichotomy t s with h | h | h
  · exact (hs.2 t h ht.1).elim
  · exact h
  · exact (ht.2 s h hs.1).elim

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotBoundaryHitTime_eq {k t : ℤ} {W : ℤ → Fin 3}
    (ht : UIBHBOTBoundaryHit k t W) : uibhbotBoundaryHitTime k W = t := by
  have he : ∃ s, UIBHBOTBoundaryHit k s W := ⟨t, ht⟩
  rw [uibhbotBoundaryHitTime, dite_eq_left he]
  exact boundaryHit_unique (Classical.choose_spec he) ht

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem measurable_integral (t : ℤ) :
    Measurable (fun W : ℤ → Fin 3 => wholePlaneWordIntegral W t) := by
  have hm (xs : List ℤ) (f : ℤ → ℤ) : Measurable (fun W : ℤ → Fin 3 =>
      (xs.map (fun i => lazyTwoDimensionalStep (W (f i)))).sum) := by
    induction xs with
    | nil => exact measurable_const
    | cons a xs ih =>
        exact ((measurable_of_countable lazyTwoDimensionalStep).comp
          (measurable_pi_apply (f a))).add ih
  unfold wholePlaneWordIntegral
  split
  · exact hm _ id
  · exact (hm _ (fun i => -i - 1)).neg

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem measurableSet_uibhbotBoundaryHit (k t : ℤ) :
    MeasurableSet {W | UIBHBOTBoundaryHit k t W} := by
  unfold UIBHBOTBoundaryHit
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_integral t).fst measurable_const).inter
    (MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun (measurable_integral s).fst measurable_const).compl)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem measurable_uibhbotBoundaryHitTime (k : ℤ) :
    Measurable (uibhbotBoundaryHitTime k) := by
  classical
  have he : MeasurableSet {W | ∃ t, UIBHBOTBoundaryHit k t W} :=
    by simpa only [Set.ofPred_exists] using
      MeasurableSet.iUnion (fun t => measurableSet_uibhbotBoundaryHit k t)
  refine measurable_to_countable' fun t => ?_
  have hf : (uibhbotBoundaryHitTime k) ⁻¹' {t} =
      {W | UIBHBOTBoundaryHit k t W} ∪
        (if t = 0 then {W | ∃ s, UIBHBOTBoundaryHit k s W}ᶜ else ∅) := by
    ext W
    by_cases h : ∃ s, UIBHBOTBoundaryHit k s W
    · have hs := Classical.choose_spec h
      have ht := uibhbotBoundaryHitTime_eq hs
      change uibhbotBoundaryHitTime k W = t ↔
        UIBHBOTBoundaryHit k t W ∨
          W ∈ (if t = 0 then {W | ∃ s, UIBHBOTBoundaryHit k s W}ᶜ else ∅)
      have hn : W ∉ (if t = 0 then
          {W | ∃ s, UIBHBOTBoundaryHit k s W}ᶜ else ∅) := by
        split_ifs <;> simp [h]
      rw [or_iff_left hn]
      constructor
      · intro hw
        rw [ht] at hw
        exact hw ▸ hs
      · intro hw
        exact uibhbotBoundaryHitTime_eq hw
    · have hn : ¬ UIBHBOTBoundaryHit k t W := fun ht => h ⟨t, ht⟩
      simp [uibhbotBoundaryHitTime, h, hn, eq_comm]
  rw [hf]
  split_ifs
  · exact (measurableSet_uibhbotBoundaryHit k t).union he.compl
  · exact (measurableSet_uibhbotBoundaryHit k t).union MeasurableSet.empty

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
@[expose] noncomputable def uibhbotFutureCode (k : ℤ) (W : ℤ → Fin 3) : ℕ → Fin 3
  | 0 => 0
  | n + 1 => W (uibhbotBoundaryHitTime k W + (n : ℤ))

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureCode_zero (k : ℤ) (W : ℤ → Fin 3) :
    uibhbotFutureCode k W 0 = 0 := rfl

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureCode_succ (k : ℤ) (W : ℤ → Fin 3) (n : ℕ) :
    uibhbotFutureCode k W (n + 1) = W (uibhbotBoundaryHitTime k W + (n : ℤ)) := rfl

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem measurable_uibhbotFutureCode (k : ℤ) : Measurable (uibhbotFutureCode k) := by
  apply Measurable.of_eval
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n =>
      have hm : Measurable (fun p : (ℤ → Fin 3) × ℤ => p.1 (p.2 + (n : ℤ))) :=
        measurable_from_prod_countable_left fun t => measurable_pi_apply (t + (n : ℤ))
      exact hm.comp (measurable_id.prodMk (measurable_uibhbotBoundaryHitTime k))

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotBoundaryHit_codeWordRel (k : ℤ) (w : ℤ → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) :
    UIBHBOTBoundaryHit k (uibhbotBlockBoundary w (-k)) (uibhbotCodeWordRel w) := by
  rw [uibhbotCodeWordRel_eq w (fun j => (hw j).1)]
  constructor
  · rw [wholePlaneWordIntegral_uibhbotCodeWord,
      uibhbotConcatWalk_stopped_blockBoundary_fst w hw]
    omega
  · intro s hs he
    rw [wholePlaneWordIntegral_uibhbotCodeWord] at he
    have hr := uibhbotConcatWalk_blockEndpoint_strictRecord w hw (-k - 1) s
      (by simpa only [sub_add_cancel] using hs)
    have hb := uibhbotConcatWalk_stopped_blockBoundary_fst w hw (-k)
    have ha : -k - 1 + 1 = -k := by omega
    rw [ha, hb, he] at hr
    omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotBoundaryHitTime_codeWordRel (k : ℤ) (w : ℤ → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) :
    uibhbotBoundaryHitTime k (uibhbotCodeWordRel w) = uibhbotBlockBoundary w (-k) :=
  uibhbotBoundaryHitTime_eq (uibhbotBoundaryHit_codeWordRel k w hw)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotBoundaryHitTime_spec (k : ℤ) (W : ℤ → Fin 3)
    (h : ∃ t, UIBHBOTBoundaryHit k t W) :
    UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W := by
  rw [uibhbotBoundaryHitTime_eq (Classical.choose_spec h)]
  exact Classical.choose_spec h

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem ae_uibhbotBoundaryHit :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W := by
  have hS : MeasurableSet {W | ∀ k : ℤ, ∃ t : ℤ, UIBHBOTBoundaryHit k t W} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun k =>
      MeasurableSet.iUnion fun t => measurableSet_uibhbotBoundaryHit k t
  have he : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ, ∃ t, UIBHBOTBoundaryHit k t W := by
    change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
    apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable hS).mpr
    filter_upwards [ae_uibhbotWordFamily_all_stopped] with w hw
    exact fun k => ⟨uibhbotBlockBoundary w (-k), uibhbotBoundaryHit_codeWordRel k w hw⟩
  exact he.mono fun W hW k => uibhbotBoundaryHitTime_spec k W (hW k)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private def decodeForwardPath (p : ℕ → ℤ × ℤ) : ℕ → Fin 3
  | 0 => 0
  | n + 1 => if (p (n + 1) - p n).1 = -1 then 0
      else if (p (n + 1) - p n).1 = 0 then 1 else 2

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem measurable_decodeForwardPath : Measurable decodeForwardPath := by
  apply Measurable.of_eval
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n =>
      exact Measurable.ite
        (measurableSet_eq_fun
          ((measurable_pi_apply (n + 1)).sub (measurable_pi_apply n)).fst
          measurable_const) measurable_const
        (Measurable.ite
          (measurableSet_eq_fun
            ((measurable_pi_apply (n + 1)).sub (measurable_pi_apply n)).fst
            measurable_const) measurable_const measurable_const)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem decodeForwardPath_codeWalk (ω : ℕ → Fin 3) (hω : ω 0 = 0) :
    decodeForwardPath (codeWalk ω) = ω := by
  funext n
  cases n with
  | zero => exact hω.symm
  | succ n =>
      simp only [decodeForwardPath, codeWalk_succ_sub]
      generalize ω (n + 1) = c
      fin_cases c <;> rfl

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem integral_succ (W : ℤ → Fin 3) (n : ℕ) :
    wholePlaneWordIntegral W ((n + 1 : ℕ) : ℤ) - wholePlaneWordIntegral W n =
      lazyTwoDimensionalStep (W n) := by
  have hc (xs : List ℕ) : (Nat.cast <$> xs : List ℤ) =
      xs.map (fun i : ℕ => (i : ℤ)) := rfl
  simp only [wholePlaneWordIntegral, Nat.cast_nonneg, ite_true, Int.toNat_natCast,
    bind_pure_comp, hc, List.map_map, Function.comp_def]
  change ((List.range (n + 1)).map
      (fun i : ℕ => lazyTwoDimensionalStep (W (i : ℤ)))).sum -
    ((List.range n).map (fun i : ℕ => lazyTwoDimensionalStep (W (i : ℤ)))).sum = _
  simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
    List.sum_singleton, add_sub_cancel_left]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem decodeForwardPath_concat (w : ℤ → List (Fin 3))
    (hw : ∀ j, 1 ≤ (w j).length) :
    decodeForwardPath (fun n : ℕ => uibhbotConcatWalk w n) =
      fun n : ℕ => if n = 0 then 0 else uibhbotCodeWordRel w ((n : ℤ) - 1) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      change (if (uibhbotConcatWalk w ↑(n + 1) - uibhbotConcatWalk w ↑n).1 = -1
        then 0 else if (uibhbotConcatWalk w ↑(n + 1) -
          uibhbotConcatWalk w ↑n).1 = 0 then 1 else 2) = _
      rw [show uibhbotConcatWalk w ((n + 1 : ℕ) : ℤ) =
          wholePlaneWordIntegral (uibhbotCodeWord w hw) ((n + 1 : ℕ) : ℤ) from
          (wholePlaneWordIntegral_uibhbotCodeWord w hw _).symm,
        show uibhbotConcatWalk w (n : ℤ) =
          wholePlaneWordIntegral (uibhbotCodeWord w hw) n from
          (wholePlaneWordIntegral_uibhbotCodeWord w hw _).symm]
      rw [integral_succ]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      rw [uibhbotCodeWordRel_eq w hw]
      generalize uibhbotCodeWord w hw (n : ℤ) = c
      fin_cases c <;> rfl

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotCodeLawRel_map_forward :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
      (fun W => fun n : ℕ => if n = 0 then 0 else W ((n : ℤ) - 1)) =
        iidCodeMeasure := by
  have hm : Measurable (fun W : ℤ → Fin 3 =>
      fun n : ℕ => if n = 0 then 0 else W ((n : ℤ) - 1)) := by
    apply Measurable.of_eval
    intro n
    split_ifs <;> fun_prop
  change (uibhbotWordFamilyLaw.map uibhbotCodeWordRel).map _ = _
  rw [Measure.map_map hm measurable_uibhbotCodeWordRel]
  calc
    _ = uibhbotWordFamilyLaw.map
        (fun w => decodeForwardPath (fun n : ℕ => uibhbotConcatWalk w n)) := by
      apply Measure.map_congr
      filter_upwards [uibhbotWordFamilyLaw_ae_codeWordRel] with w hw
      obtain ⟨hw, _⟩ := hw
      exact (decodeForwardPath_concat w (fun j => (hw j).1)).symm
    _ = (iidCodeMeasure.map (fun ω => codeWalk ω)).map decodeForwardPath := by
      have hmforward : Measurable
          (fun w : ℤ → List (Fin 3) => fun n : ℕ => uibhbotConcatWalk w n) := by
        apply Measurable.of_eval
        intro n
        have hb : ∀ m : ℕ, Measurable (fun w : ℤ → List (Fin 3) =>
            (List.range m).flatMap (fun k : ℕ => w (k : ℤ))) := by
          intro m
          induction m with
          | zero => exact measurable_const
          | succ m ih =>
              simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
              exact (measurable_of_countable
                (fun p : List (Fin 3) × List (Fin 3) => p.1 ++ p.2)).comp
                  (ih.prodMk (measurable_pi_apply (m : ℤ)))
        have hf := (measurable_of_countable (fun v : List (Fin 3) =>
          ((v.take n).map lazyTwoDimensionalStep).sum)).comp (hb n)
        have hc (xs : List ℕ) : (Nat.cast <$> xs : List ℤ) =
            xs.map (fun i : ℕ => (i : ℤ)) := rfl
        simpa only [uibhbotConcatWalk, Nat.cast_nonneg, ite_true, Int.toNat_natCast,
          bind_pure_comp, hc, List.flatMap_map, Function.comp_def] using hf
      rw [← uibhbotWordFamilyLaw_map_forward_path,
        Measure.map_map measurable_decodeForwardPath hmforward]
      rfl
    _ = iidCodeMeasure := by
      rw [Measure.map_map measurable_decodeForwardPath measurable_codeWalk]
      have ha : ∀ᵐ ω ∂iidCodeMeasure, ω 0 = 0 :=
        DirectedDistances.Probability.markovTrajectory_ae_start
          (Kernel.const (Fin 3) uniformCodeMeasure) 0
      calc
        _ = iidCodeMeasure.map id := Measure.map_congr (ha.mono fun ω hω =>
          decodeForwardPath_codeWalk ω hω)
        _ = _ := Measure.map_id

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem block_count_le (f : ℕ → List (Fin 3)) (hf : ∀ j, 1 ≤ (f j).length)
    (m : ℕ) : m ≤ ((List.range m).flatMap f).length := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
      have h := hf m
      omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem block_letter_at (f : ℕ → List (Fin 3)) (hf : ∀ j, 1 ≤ (f j).length)
    (m i : ℕ) (hi : i < (f m).length) :
    uibhbotBlockLetter f hf (((List.range m).flatMap f).length + i) = (f m)[i] := by
  let q := ((List.range m).flatMap f).length + i
  have hm : m + 1 ≤ q + 1 := by
    have h := block_count_le f hf m
    dsimp [q]
    omega
  have hp : (List.range (m + 1)).flatMap f <+:
      (List.range (q + 1)).flatMap f := by
    have he : q + 1 = (m + 1) + (q + 1 - (m + 1)) := by omega
    conv_rhs => rw [he, List.range_add, List.flatMap_append]
    exact List.prefix_append _ _
  have hlen : q < ((List.range (m + 1)).flatMap f).length := by
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.length_append]
    dsimp [q]
    omega
  unfold uibhbotBlockLetter
  exact (hp.getElem hlen).symm.trans (by
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simp [q])

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem boundary_nat_length (w : ℤ → List (Fin 3)) (m : ℕ) :
    uibhbotBlockBoundary w (m : ℤ) =
      (((List.range m).flatMap (fun j : ℕ => w (j : ℤ))).length : ℤ) := by
  induction m with
  | zero => simp [uibhbotBlockBoundary_zero]
  | succ m ih =>
      rw [Nat.cast_add, Nat.cast_one, uibhbotBlockBoundary_succ, ih]
      simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.length_append, Nat.cast_add]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem boundary_neg_length (w : ℤ → List (Fin 3)) (m : ℕ) :
    uibhbotBlockBoundary w (-(m : ℤ)) =
      -(((List.range m).flatMap (fun j : ℕ => w (-(j : ℤ) - 1))).length : ℤ) := by
  induction m with
  | zero => simp [uibhbotBlockBoundary_zero]
  | succ m ih =>
      have he := uibhbotBlockBoundary_succ w (-((m + 1 : ℕ) : ℤ))
      have ha : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by omega
      rw [ha, ih] at he
      simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.length_append, Nat.cast_add]
      have hb : -((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 1 := by omega
      rw [hb] at he
      simp only [Nat.cast_add, Nat.cast_one] at *
      have hc : -(m : ℤ) - 1 = -((m : ℤ) + 1) := by omega
      simp only [hc] at *
      omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem codeWord_at_block (w : ℤ → List (Fin 3))
    (hw : ∀ j, 1 ≤ (w j).length) (j : ℤ) (i : ℕ) (hi : i < (w j).length) :
    uibhbotCodeWord w hw (uibhbotBlockBoundary w j + (i : ℤ)) = (w j)[i] := by
  by_cases hj : 0 ≤ j
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [boundary_nat_length]
    have hn : 0 ≤
        (((List.range m).flatMap (fun j : ℕ => w (j : ℤ))).length : ℤ) + i := by
      positivity
    simp only [uibhbotCodeWord, ite_eq_left hn]
    have hc :
        ((((List.range m).flatMap (fun j : ℕ => w (j : ℤ))).length : ℤ) + i).toNat =
          ((List.range m).flatMap (fun j : ℕ => w (j : ℤ))).length + i := by omega
    rw [hc]
    exact block_letter_at _ _ m i hi
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, j = -((m + 1 : ℕ) : ℤ) := by
      refine ⟨(-j - 1).toNat, ?_⟩
      have h := Int.toNat_of_nonneg (show 0 ≤ -j - 1 by omega)
      omega
    subst j
    rw [boundary_neg_length]
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.length_append, Nat.cast_add]
    let f : ℕ → List (Fin 3) := fun q => (w (-(q : ℤ) - 1)).reverse
    have hlen : ((List.range m).flatMap f).length =
        ((List.range m).flatMap (fun q : ℕ => w (-(q : ℤ) - 1))).length := by
      simp only [List.length_flatMap, f, List.length_reverse]
    have hm'' : -((m : ℤ) + 1) = -(m : ℤ) - 1 := by omega
    simp only [Nat.cast_add, Nat.cast_one, hm''] at hi ⊢
    have hn : ¬ 0 ≤
        -((((List.range m).flatMap (fun j : ℕ => w (-(j : ℤ) - 1))).length : ℤ) +
          ((w (-(m : ℤ) - 1)).length : ℤ)) + i := by omega
    simp only [uibhbotCodeWord, ite_eq_right hn]
    have hc :
        (-(-((((List.range m).flatMap (fun j : ℕ => w (-(j : ℤ) - 1))).length : ℤ) +
          ((w (-(m : ℤ) - 1)).length : ℤ)) + i) - 1).toNat =
          ((List.range m).flatMap f).length + ((w (-(m : ℤ) - 1)).length - 1 - i) := by
      rw [hlen]
      omega
    rw [hc]
    have hi' : (w (-(m : ℤ) - 1)).length - 1 - i < (f m).length := by
      dsimp [f]
      rw [List.length_reverse]
      omega
    rw [block_letter_at f (fun q => by
      simpa only [f, List.length_reverse] using hw (-(q : ℤ) - 1)) m _ hi']
    simp only [f, List.getElem_reverse]
    congr 1
    omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem boundary_shift (w : ℤ → List (Fin 3)) (t j : ℤ) :
    uibhbotBlockBoundary (fun a => w (a + t)) j =
      uibhbotBlockBoundary w (j + t) - uibhbotBlockBoundary w t := by
  induction j using Int.induction_on with
  | zero => simp only [uibhbotBlockBoundary_zero, zero_add, sub_self]
  | succ n ih =>
      have ha : (n : ℤ) + 1 + t = ((n : ℤ) + t) + 1 := by omega
      rw [uibhbotBlockBoundary_succ, ha, uibhbotBlockBoundary_succ, ih]
      omega
  | pred n ih =>
      have hs := uibhbotBlockBoundary_succ (fun a => w (a + t)) (-(n : ℤ) - 1)
      have ht := uibhbotBlockBoundary_succ w (-(n : ℤ) - 1 + t)
      have ha : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
      have hb : -(n : ℤ) - 1 + t + 1 = -(n : ℤ) + t := by omega
      rw [ha, ih] at hs
      rw [hb] at ht
      omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotCodeWordRel_boundary_suffix (w : ℤ → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) (k : ℤ) (n : ℕ) :
    uibhbotCodeWordRel w (uibhbotBlockBoundary w (-k) + (n : ℤ)) =
      uibhbotCodeWordRel (fun j => w (j - k)) n := by
  let v : ℤ → List (Fin 3) := fun j => w (j - k)
  have hv : ∀ j, IsStoppedExcursionWord (v j) := fun j => hw (j - k)
  obtain ⟨j, hlo, hhi⟩ := uibhbotConcatWalk_exists_block v hv (n : ℤ)
  let i : ℕ := ((n : ℤ) - uibhbotBlockBoundary v j).toNat
  have hi : (i : ℤ) = (n : ℤ) - uibhbotBlockBoundary v j :=
    Int.toNat_of_nonneg (by omega)
  have hil : i < (v j).length := by
    rw [uibhbotBlockBoundary_succ] at hhi
    omega
  have hb : uibhbotBlockBoundary v j =
      uibhbotBlockBoundary w (j - k) - uibhbotBlockBoundary w (-k) :=
    boundary_shift w (-k) j
  have hn : (n : ℤ) = uibhbotBlockBoundary v j + (i : ℤ) := by omega
  have hn' : uibhbotBlockBoundary w (-k) + (n : ℤ) =
      uibhbotBlockBoundary w (j - k) + (i : ℤ) := by omega
  rw [uibhbotCodeWordRel_eq w (fun j => (hw j).1)]
  change _ = uibhbotCodeWordRel v n
  rw [uibhbotCodeWordRel_eq v (fun j => (hv j).1), hn', hn,
    codeWord_at_block w (fun j => (hw j).1) (j - k) i hil,
    codeWord_at_block v (fun j => (hv j).1) j i hil]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureCode_codeWordRel (k : ℤ) (w : ℤ → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) :
    uibhbotFutureCode k (uibhbotCodeWordRel w) =
      fun n : ℕ => if n = 0 then 0 else
        uibhbotCodeWordRel (fun j => w (j - k)) ((n : ℤ) - 1) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      rw [uibhbotFutureCode_succ, uibhbotBoundaryHitTime_codeWordRel k w hw,
        uibhbotCodeWordRel_boundary_suffix w hw k n]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureCode_law (k : ℤ) :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map (uibhbotFutureCode k) =
      iidCodeMeasure := by
  let F : (ℤ → Fin 3) → ℕ → Fin 3 :=
    fun W n => if n = 0 then 0 else W ((n : ℤ) - 1)
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro n
    dsimp only [F]
    split_ifs <;> fun_prop
  have hs : Measurable (fun w : ℤ → List (Fin 3) => fun j => w (j - k)) := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply (j - k)
  change (uibhbotWordFamilyLaw.map uibhbotCodeWordRel).map _ = _
  rw [Measure.map_map (measurable_uibhbotFutureCode k) measurable_uibhbotCodeWordRel]
  calc
    _ = uibhbotWordFamilyLaw.map
        (fun w => F (uibhbotCodeWordRel (fun j => w (j - k)))) := by
      apply Measure.map_congr
      filter_upwards [ae_uibhbotWordFamily_all_stopped] with w hw
      exact uibhbotFutureCode_codeWordRel k w hw
    _ = ((uibhbotWordFamilyLaw.map (fun w => fun j => w (j - k))).map
        uibhbotCodeWordRel).map F := by
      rw [Measure.map_map measurable_uibhbotCodeWordRel hs,
        Measure.map_map hF (measurable_uibhbotCodeWordRel.comp hs)]
      rfl
    _ = (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map F := by
      have ht := uibhbotWordFamilyLaw_map_shift (-k)
      change uibhbotWordFamilyLaw.map (fun w => fun j => w (j - k)) = _ at ht
      rw [ht]
      rfl
    _ = iidCodeMeasure := uibhbotCodeLawRel_map_forward

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureCode_map (k : ℤ) {β : Type*} [MeasurableSpace β]
    {f : (ℕ → Fin 3) → β} (hf : Measurable f) :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map (fun W => f (uibhbotFutureCode k W)) =
      iidCodeMeasure.map f := by
  change (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map (f ∘ uibhbotFutureCode k) = _
  rw [← Measure.map_map hf (measurable_uibhbotFutureCode k), uibhbotFutureCode_law]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureCode_stream (k : ℤ) (W : ℤ → Fin 3) :
    (fun i : ℕ => uibhbotFutureCode k W (i + 1)) =
      lemma38StartStream W (uibhbotBoundaryHitTime k W) := by
  funext i
  simp only [uibhbotFutureCode_succ, lemma38StartStream, add_comm]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
@[expose] noncomputable def uibhbotFutureVertex (k : ℤ) (W : ℤ → Fin 3) :
    ℕ → WholePlaneVertex W := lemma38StartVertexι W (uibhbotBoundaryHitTime k W)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
@[expose] noncomputable def uibhbotFutureEdge (k : ℤ) (W : ℤ → Fin 3) :
    ℕ → WholePlaneEdge W := lemma38StartEdgeι W (uibhbotBoundaryHitTime k W)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureVertex_injective (k : ℤ) (W : ℤ → Fin 3) :
    Function.Injective (uibhbotFutureVertex k W) :=
  lemma38StartVertexι_injective W _

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureEdge_injective (k : ℤ) (W : ℤ → Fin 3) :
    Function.Injective (uibhbotFutureEdge k W) := lemma38StartEdgeι_injective W _

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureEdge_west (k : ℤ) (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgeWest W (uibhbotFutureEdge k W e) =
      uibhbotFutureVertex k W (edgeWest (fun i => uibhbotFutureCode k W (i + 1)) e) := by
  rw [uibhbotFutureCode_stream]
  exact lemma38StartEdgeWest W _ e

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureEdge_east (k : ℤ) (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgeEast W (uibhbotFutureEdge k W e) =
      uibhbotFutureVertex k W (edgeEast (fun i => uibhbotFutureCode k W (i + 1)) e) := by
  rw [uibhbotFutureCode_stream]
  exact lemma38StartEdgeEast W _ e

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureEdge_present (k : ℤ) (W : ℤ → Fin 3) (e : ℕ)
    (he : EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) e) :
    wholePlaneEdgePresent W (uibhbotFutureEdge k W e) := by
  rw [uibhbotFutureCode_stream] at he
  let t := uibhbotBoundaryHitTime k W
  change wholePlaneEdgePresent W (lemma38StartEdgeι W t e)
  change EdgePresent (lemma38StartStream W t) e at he
  by_cases ht : t ≤ 0
  · rw [lemma38StartEdgeι, ite_eq_left ht]
    apply wholePlaneRun_present_colimit
    rwa [lemma38StartStream_eq_shifted W t ht] at he
  · have ht' : 0 ≤ t := by omega
    have hs : (fun i => shiftedStream W 0 (t.toNat + i)) =
        lemma38StartStream W t := by
      funext i
      simp only [shiftedStream, lemma38StartStream, Nat.cast_add,
        Int.toNat_of_nonneg ht']
      congr 1
      omega
    rw [lemma38StartEdgeι, ite_eq_right ht]
    apply wholePlaneRun_present_colimit
    rw [← hs] at he
    obtain ⟨m, hb, hp⟩ := he
    have hr := kmswWindowPatchData_rel (shiftedStream W 0) t.toNat m
    refine ⟨t.toNat + m, ?_, ?_⟩
    · rw [kmswWindowEdgeMapInf_eq_stage _ _ _ e hb]
      exact hr.edge_bound e hb
    · rw [kmswWindowEdgeMapInf_eq_stage _ _ _ e hb]
      exact hr.present e hb hp

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
 
@[expose] def UIBHBOTFutureBoundaryAlignment (k : ℤ) (W : ℤ → Fin 3) : Prop :=
  ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
    ∀ ℓ : ℤ, ℓ ≤ k →
      uibhbotFutureVertex k W
        (boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h (ℓ - k)) =
          uibhbotFutureVertex ℓ W 0

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
 
@[expose] def UIBHBOTFutureBoundaryAlignmentAlmostSure : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∀ k : ℤ, UIBHBOTFutureBoundaryAlignment k W

end DirectedDistances.RandomWalk
