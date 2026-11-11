module

public import DirectedDistances.RandomWalk.UIBHBOTEncodingWalk
public import DirectedDistances.RandomWalk.RConditionedWalk
public import DirectedDistances.RandomWalk.ExcursionWordSupport
public import DirectedDistances.RandomWalk.ConditionedVectorFactorization
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Independence.InfinitePi

/-! # UIBHBOT negative-time law identification -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The final step of a stopped excursion is the first-coordinate step `(-1, 0)`.
This gives the deterministic first step after reversing the block -/
private theorem stoppedExcursionWord_lastCode {v : List (Fin 3)}
    (hv : IsStoppedExcursionWord v) (hne : v ≠ []) : v.getLast hne = 0 := by
  rcases hv with ⟨hlen, hend, hbefore⟩
  have htake : v.take (v.length - 1) = v.dropLast := by
    exact List.take_eq_dropLast (by omega)
  have hi : v.length - 1 < v.length := by omega
  have hprev : -1 < ((v.dropLast.map lazyTwoDimensionalStep).sum).1 := by
    have h := hbefore (v.length - 1) hi
    rw [htake] at h
    exact h
  have htotal : ((v.map lazyTwoDimensionalStep).sum).1 =
      ((v.dropLast.map lazyTwoDimensionalStep).sum).1 +
        (lazyTwoDimensionalStep (v.getLast hne)).1 := by
    have hdecomp : v.dropLast ++ [v.getLast hne] = v := List.dropLast_concat_getLast hne
    calc
      _ = ((v.dropLast ++ [v.getLast hne]).map lazyTwoDimensionalStep).sum.1 :=
        congrArg (fun xs : List (Fin 3) => ((xs.map lazyTwoDimensionalStep).sum).1)
          hdecomp.symm
      _ = _ := by simp
  have hstep : -1 ≤ (lazyTwoDimensionalStep (v.getLast hne)).1 := by
    change -1 ≤ (v.getLast hne : ℤ) - 1
    omega
  have hlast : (lazyTwoDimensionalStep (v.getLast hne)).1 = -1 := by
    rw [htotal] at hend
    omega
  have hcode : v.getLast hne = 0 := by
    change (v.getLast hne : ℤ) - 1 = -1 at hlast
    have hcInt : ((v.getLast hne).val : ℤ) = 0 := by omega
    have hcNat : (v.getLast hne).val = 0 := by exact_mod_cast hcInt
    exact Fin.ext hcNat
  exact hcode

/-- A stopped block read backward has deterministic first increment `(1, 0)` -/
private theorem uibhbotConcatWalk_neg_one_of_stopped (w : ℤ → List (Fin 3))
    (hv : IsStoppedExcursionWord (w (-1))) : uibhbotConcatWalk w (-1) = (1, 0) := by
  have hne : w (-1) ≠ [] := by
    intro h
    have hlen := hv.1
    simp [h] at hlen
  have hrevStep : (((w (-1)).map lazyTwoDimensionalStep).reverse.take 1) =
      [lazyTwoDimensionalStep ((w (-1)).getLast hne)] := by
    rw [List.take_one]
    simp [List.head?_reverse, List.getLast?_eq_some_getLast hne]
  simp only [uibhbotConcatWalk,
    ite_eq_right (by norm_num : ¬ (0 : ℤ) ≤ -1)]
  norm_num
  change -(((w (-1)).map lazyTwoDimensionalStep).reverse.take 1).sum = (1, 0)
  rw [hrevStep]
  simp [stoppedExcursionWord_lastCode hv hne, lazyTwoDimensionalStep]

/-- Almost every iid stopped block is a stopped excursion word. -/
private theorem ae_stoppedExcursionWord_at (k : ℤ) :
    ∀ᵐ w ∂uibhbotWordFamilyLaw, IsStoppedExcursionWord (w k) := by
  have hm : Measurable (fun w : ℤ → List (Fin 3) => w k) := measurable_pi_apply k
  have hmap : ∀ᵐ v ∂uibhbotWordFamilyLaw.map (fun w => w k),
      IsStoppedExcursionWord v := by
    rw [uibhbotWordFamilyLaw_map_eval k]
    exact ae_isStoppedExcursionWord_excursionWordLaw
  exact (ae_map_iff hm.aemeasurable (MeasurableSet.of_discrete)).mp hmap

/-- The first negative-time prefix, at times `0` and `-1`, agrees with the
shifted, coordinate-swapped R-conditioned path prefix -/
theorem uibhbot_negative_prefix_one :
    uibhbotWordFamilyLaw.map
        (fun w => fun j : Fin 2 => uibhbotConcatWalk w (-(j.val : ℤ))) =
      (rConditionedPathLaw 0 0).map
        (fun q => fun j : Fin 2 =>
          if j.val = 0 then (0, 0) else (q (j.val - 1)).swap + (1, 0)) := by
  let p : Fin 2 → ℤ × ℤ := fun j => if j.val = 0 then (0, 0) else (1, 0)
  have hleft : ∀ᵐ w ∂uibhbotWordFamilyLaw,
      (fun j : Fin 2 => uibhbotConcatWalk w (-(j.val : ℤ))) = p := by
    filter_upwards [ae_stoppedExcursionWord_at (-1)] with w hw
    funext j
    fin_cases j
    · simp only [p, ↓reduceIte]
      change uibhbotConcatWalk w 0 = 0
      exact uibhbotConcatWalk_zero w
    · simp [p, uibhbotConcatWalk_neg_one_of_stopped w hw]
  have hstartTrajectory : ∀ᵐ r ∂conditionedVectorTrajectory 0 0,
      r 0 = (0, 0) := by
    change ∀ᵐ r ∂DirectedDistances.Probability.markovTrajectory conditionedVectorKernel
      (0, 0), r 0 = (0, 0)
    exact DirectedDistances.Probability.markovTrajectory_ae_start _ _
  have hstartVector : ∀ᵐ q ∂conditionedVectorPathLaw 0 0, q 0 = (0, 0) := by
    rw [conditionedVectorPathLaw]
    have hm : Measurable
        (fun r : ℕ → ℕ × ℤ => fun n => (((r n).1 : ℤ), (r n).2)) :=
      Measurable.of_eval fun n => by fun_prop
    apply (ae_map_iff hm.aemeasurable (by measurability)).2
    filter_upwards [hstartTrajectory] with r hr
    simpa using congrArg (fun z : ℕ × ℤ => ((z.1 : ℤ), z.2)) hr
  have hstartR : ∀ᵐ q ∂rConditionedPathLaw 0 0, q 0 = (0, 0) := by
    rw [rConditionedPathLaw]
    have hm : Measurable
        (fun p : ℕ → ℤ × ℤ => fun n => stepRotateInv (p n)) :=
      Measurable.of_eval fun n => (measurable_of_countable stepRotateInv).comp
        (measurable_pi_apply n)
    apply (ae_map_iff hm.aemeasurable (by measurability)).2
    filter_upwards [hstartVector] with q hq
    simp [hq, stepRotateInv]
  have hright : ∀ᵐ q ∂rConditionedPathLaw 0 0,
      (fun j : Fin 2 => if j.val = 0 then (0, 0)
        else (q (j.val - 1)).swap + (1, 0)) = p := by
    filter_upwards [hstartR] with q hq
    funext j
    fin_cases j <;> simp [p, hq]
  rw [Measure.map_congr hleft, Measure.map_const, Measure.map_congr hright,
    Measure.map_const]
  simp [p, rConditionedPathLaw]

/-- Helper toward Definition 5.8: a finite tuple of preceding words, read nearest
first and backward within each word, integrated with the negative-time sign. -/
@[expose] def uibhbotBackwardWordPrefix (N : ℕ)
    (v : Fin N → List (Fin 3)) : Fin (N + 1) → ℤ × ℤ :=
  fun j => -(((((List.ofFn fun i => (v i).reverse).flatten).take j.val).map
    lazyTwoDimensionalStep).sum)

private theorem length_le_flatMap_of_nonempty {α β : Type*} (xs : List α)
    (f : α → List β) (hf : ∀ x ∈ xs, 1 ≤ (f x).length) :
    xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hf x (by simp)
      have ht := ih (fun y hy => hf y (by simp [hy]))
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega

private theorem backward_take_stable (w : ℤ → List (Fin 3)) (N d : ℕ)
    (hd : d ≤ N) (hw : ∀ k : ℤ, 1 ≤ (w k).length) :
    ((List.range N).flatMap (fun k : ℕ => (w (-(k : ℤ) - 1)).reverse)).take d =
      ((List.range d).flatMap (fun k : ℕ => (w (-(k : ℤ) - 1)).reverse)).take d := by
  have hlen : d ≤ ((List.range d).flatMap
      (fun k : ℕ => (w (-(k : ℤ) - 1)).reverse)).length := by
    simpa using length_le_flatMap_of_nonempty (List.range d)
      (fun k : ℕ => (w (-(k : ℤ) - 1)).reverse)
      (fun k _ => by simpa using hw (-(k : ℤ) - 1))
  have hN : N = d + (N - d) := by omega
  conv_lhs => rw [hN, List.range_add, List.flatMap_append]
  exact List.take_append_of_le_length hlen

private theorem backward_prefix_eq (N : ℕ) (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, 1 ≤ (w k).length) :
    (fun j : Fin (N + 1) => uibhbotConcatWalk w (-(j.val : ℤ))) =
      uibhbotBackwardWordPrefix N (fun i => w (-(i.val : ℤ) - 1)) := by
  have hwords : (List.ofFn fun i : Fin N => (w (-(i.val : ℤ) - 1)).reverse) =
      (List.range N).map (fun k : ℕ => (w (-(k : ℤ) - 1)).reverse) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  funext j
  have hj : j.val ≤ N := by omega
  by_cases hz : j.val = 0
  · simp [hz, uibhbotConcatWalk_zero, uibhbotBackwardWordPrefix]
  · have hpos : ¬ 0 ≤ -(j.val : ℤ) := by omega
    simp only [uibhbotConcatWalk, hpos, ↓reduceIte, neg_neg,
      Int.toNat_natCast, uibhbotBackwardWordPrefix, hwords, ← List.flatMap_def]
    simp only [bind_pure_comp]
    change -(((List.range j.val).map (fun k : ℕ => (k : ℤ))).flatMap
        (fun k : ℤ => (w (-k - 1)).reverse) |>.take j.val |>.map
        lazyTwoDimensionalStep).sum = _
    rw [List.flatMap_map]
    change -(((List.range j.val).flatMap
        (fun k : ℕ => (w (-(k : ℤ) - 1)).reverse)).take j.val |>.map
        lazyTwoDimensionalStep).sum = _
    rw [backward_take_stable w N j.val hj hw]

/-- Helper toward Definition 5.8: every finite negative prefix is the image of
exactly `N` iid stopped words. This is an all-horizon reduction, with no
time-reversal or conditioned-law premise. -/
theorem uibhbot_negative_prefix_eq_word_product (N : ℕ) :
    uibhbotWordFamilyLaw.map
        (fun w => fun j : Fin (N + 1) => uibhbotConcatWalk w (-(j.val : ℤ))) =
      (Measure.pi fun _ : Fin N => excursionWordLaw).map (uibhbotBackwardWordPrefix N) := by
  let coords : (ℤ → List (Fin 3)) → Fin N → List (Fin 3) :=
    fun w i => w (-(i.val : ℤ) - 1)
  have hm : Measurable coords := Measurable.of_eval fun _ => measurable_pi_apply _
  have hc : uibhbotWordFamilyLaw.map coords =
      Measure.pi (fun _ : Fin N => excursionWordLaw) := by
    rw [uibhbotWordFamilyLaw, Measure.map_infinitePi_infinitePi_of_inj
      (show Function.Injective (fun i : Fin N => -(i.val : ℤ) - 1) from by
        intro i j hij
        change -(i.val : ℤ) - 1 = -(j.val : ℤ) - 1 at hij
        have he : (i.val : ℤ) = (j.val : ℤ) := by omega
        apply Fin.ext
        exact_mod_cast he), Measure.infinitePi_eq_pi]
  have hw : ∀ᵐ w ∂uibhbotWordFamilyLaw, ∀ k : ℤ, 1 ≤ (w k).length := by
    rw [ae_all_iff]
    intro k
    filter_upwards [ae_stoppedExcursionWord_at k] with w hw
    exact hw.1
  rw [← hc, Measure.map_map (measurable_of_countable _) hm]
  apply Measure.map_congr
  filter_upwards [hw] with w hw
  exact backward_prefix_eq N w hw

open Classical in
private theorem stopped_word_atom (v : List (Fin 3)) :
    excursionWordLaw {v} =
      if IsStoppedExcursionWord v then (1 / 3 : ℝ≥0∞) ^ v.length else 0 := by
  classical
  by_cases hv : IsStoppedExcursionWord v
  · simp only [hv, ↓reduceIte, excursionWordLaw_singleton v hv]
  · rw [ite_eq_right hv]
    apply measure_mono_null _ (ae_iff.mp ae_isStoppedExcursionWord_excursionWordLaw)
    simpa only [Set.singleton_subset_iff, Set.mem_ofPred_eq] using hv

open Classical in
/-- Helper toward Definition 5.8: the exact finite-horizon renewal sum for
every negative-time cylinder. All factors are proved stopped-word atoms;
the sum does not assume a transition, independence, or density identity. -/
theorem uibhbot_negative_prefix_cylinder_sum (N : ℕ)
    (q : Fin (N + 1) → ℤ × ℤ) :
    (uibhbotWordFamilyLaw.map
      (fun w => fun j : Fin (N + 1) => uibhbotConcatWalk w (-(j.val : ℤ)))) {q} =
      ∑' v : Fin N → List (Fin 3),
        (if uibhbotBackwardWordPrefix N v = q then (1 : ℝ≥0∞) else 0) *
          ∏ i : Fin N, (if IsStoppedExcursionWord (v i) then
            (1 / 3 : ℝ≥0∞) ^ (v i).length else 0) := by
  classical
  rw [uibhbot_negative_prefix_eq_word_product,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← lintegral_indicator_one (MeasurableSet.of_discrete), lintegral_countable']
  apply tsum_congr
  intro v
  rw [Measure.pi_singleton]
  simp only [stopped_word_atom]
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply]

/-- Helper toward Definition 5.8: insert the deterministic first step, swap
coordinates, and shift a conditioned finite prefix. -/
@[expose] def uibhbotShiftedConditionedPrefix (n : ℕ)
    (p : Fin (n + 1) → ℤ × ℤ) : Fin (n + 2) → ℤ × ℤ :=
  Fin.cons (0, 0) (fun j => (p j).swap + (1, 0))

private theorem shiftedConditionedPrefix_injective (n : ℕ) :
    Function.Injective (uibhbotShiftedConditionedPrefix n) := by
  intro p q h
  funext j
  have hj := congrFun h j.succ
  change (p j).swap + (1, 0) = (q j).swap + (1, 0) at hj
  have he := add_right_cancel hj
  exact congrArg Prod.swap he

private theorem shiftedConditionedPrefix_map (n : ℕ) :
    (rConditionedPathLaw 0 0).map
        (fun p => uibhbotShiftedConditionedPrefix n (fun j => p j.val)) =
      ((rConditionedPathLaw 0 0).map
        (fun p => fun j : Fin (n + 1) => p j.val)).map
          (uibhbotShiftedConditionedPrefix n) := by
  rw [Measure.map_map (measurable_of_countable _) (by fun_prop)]
  rfl

open Classical in
/-- Helper toward Definition 5.8: the exact atom on the conditioned side of
the proposed renewal identity. The source word, every positivity constraint,
the deterministic first step, both coordinates, and the terminal height are
retained, at every finite horizon. -/
theorem uibhbot_shifted_conditioned_prefix_atom (n : ℕ)
    (q : Fin (n + 2) → ℤ × ℤ) :
    ((rConditionedPathLaw 0 0).map
      (fun p => uibhbotShiftedConditionedPrefix n (fun j => p j.val))) {q} =
      if (∃ a : Fin n → Fin 3,
          uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) = q) ∧
          (∀ j : Fin (n + 1), 1 ≤ (q j.succ).1) then
        ENNReal.ofReal ((q (Fin.last (n + 1))).1 : ℝ) * ((3 : ℝ≥0∞) ^ n)⁻¹
      else 0 := by
  classical
  rw [shiftedConditionedPrefix_map, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  by_cases hr : ∃ a : Fin n → Fin 3,
      uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) = q
  · obtain ⟨a, rfl⟩ := hr
    have hfiber : uibhbotShiftedConditionedPrefix n ⁻¹'
        {uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a)} =
          {lazyTwoDimensionalPrefix 0 0 a} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        (shiftedConditionedPrefix_injective n).eq_iff]
    rw [hfiber, rConditionedPathLaw_map_prefix]
    simp only [Nat.cast_zero]
    rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
      lazyTwoDimensionalPrefix_atom]
    have hm : ∃ b : Fin n → Fin 3,
        uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 b) =
          uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) := ⟨a, rfl⟩
    have hp : (∀ j : Fin (n + 1), 1 ≤
        (uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) j.succ).1) ↔
        (∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 a j).2) := by
      constructor <;> intro h j
      · have hj := h j
        change 1 ≤ (lazyTwoDimensionalPrefix 0 0 a j).2 + 1 at hj
        omega
      · change 1 ≤ (lazyTwoDimensionalPrefix 0 0 a j).2 + 1
        have hj := h j
        omega
    have hend : (uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a)
        (Fin.last (n + 1))).1 = (lazyTwoDimensionalPrefix 0 0 a (Fin.last n)).2 + 1 := rfl
    simp only [hm, true_and, hp, hend, Int.cast_add, Int.cast_one,
      zero_add, div_one]
    split_ifs <;> simp
  · rw [ite_eq_right (fun h => hr h.1), rConditionedPathLaw_map_prefix]
    simp only [Nat.cast_zero]
    apply withDensity_absolutelyContinuous _ _
    rw [Measure.map_apply (measurable_of_countable _) (MeasurableSet.of_discrete)]
    have he : lazyTwoDimensionalPrefix 0 0 ⁻¹'
        (uibhbotShiftedConditionedPrefix n ⁻¹' {q}) = ∅ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      exact fun ha => hr ⟨a, ha⟩
    rw [he, measure_empty]

private theorem shiftedConditionedPrefix_apply (n : ℕ) (p : ℕ → ℤ × ℤ) :
    uibhbotShiftedConditionedPrefix n (fun j => p j.val) =
      (fun j : Fin (n + 2) => if j.val = 0 then (0, 0)
        else (p (j.val - 1)).swap + (1, 0)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [uibhbotShiftedConditionedPrefix]
  · simp [uibhbotShiftedConditionedPrefix]

open Classical in
/-- Helper toward Definition 5.8: the proposed law identity at any positive
horizon is equivalent to this explicit renewal sum. The equivalence is a
reduction only: it does not assert that the sum has been evaluated. -/
theorem uibhbot_negative_prefix_law_iff_renewal_sum (n : ℕ) :
    (uibhbotWordFamilyLaw.map
        (fun w => fun j : Fin (n + 2) => uibhbotConcatWalk w (-(j.val : ℤ))) =
      (rConditionedPathLaw 0 0).map
        (fun p => fun j : Fin (n + 2) => if j.val = 0 then (0, 0)
          else (p (j.val - 1)).swap + (1, 0))) ↔
    ∀ q : Fin (n + 2) → ℤ × ℤ,
      (∑' v : Fin (n + 1) → List (Fin 3),
        (if uibhbotBackwardWordPrefix (n + 1) v = q then (1 : ℝ≥0∞) else 0) *
          ∏ i : Fin (n + 1), (if IsStoppedExcursionWord (v i) then
            (1 / 3 : ℝ≥0∞) ^ (v i).length else 0)) =
      if (∃ a : Fin n → Fin 3,
          uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) = q) ∧
          (∀ j : Fin (n + 1), 1 ≤ (q j.succ).1) then
        ENNReal.ofReal ((q (Fin.last (n + 1))).1 : ℝ) * ((3 : ℝ≥0∞) ^ n)⁻¹
      else 0 := by
  classical
  have hright : (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 2) =>
        if j.val = 0 then (0, 0) else (p (j.val - 1)).swap + (1, 0)) =
      (fun p => uibhbotShiftedConditionedPrefix n (fun j => p j.val)) := by
    funext p
    exact (shiftedConditionedPrefix_apply n p).symm
  rw [hright]
  constructor
  · intro h q
    rw [← uibhbot_negative_prefix_cylinder_sum (n + 1), h,
      uibhbot_shifted_conditioned_prefix_atom]
  · intro h
    apply Measure.ext_of_singleton
    intro q
    rw [uibhbot_negative_prefix_cylinder_sum (n + 1),
      uibhbot_shifted_conditioned_prefix_atom]
    exact h q

private theorem measurable_backward_blocks (xs : List ℕ) :
    Measurable (fun w : ℤ → List (Fin 3) =>
      xs.flatMap (fun k : ℕ => (w (-(k : ℤ) - 1)).reverse)) := by
  induction xs with
  | nil => exact measurable_const
  | cons k xs ih =>
      exact (measurable_of_countable
        (fun p : List (Fin 3) × List (Fin 3) => p.1.reverse ++ p.2)).comp
          ((measurable_pi_apply (-(k : ℤ) - 1)).prodMk ih)

private theorem measurable_negative_path :
    Measurable (fun w : ℤ → List (Fin 3) =>
      fun n : ℕ => uibhbotConcatWalk w (-(n : ℤ))) := by
  apply Measurable.of_eval
  intro n
  by_cases hn : n = 0
  · simpa only [hn, Nat.cast_zero, neg_zero, uibhbotConcatWalk_zero] using
      (measurable_const : Measurable (fun _ : ℤ → List (Fin 3) => (0 : ℤ × ℤ)))
  · have hneg : ¬ 0 ≤ -(n : ℤ) := by omega
    have he : (fun w : ℤ → List (Fin 3) => uibhbotConcatWalk w (-(n : ℤ))) =
        (fun w => -((((List.range n).flatMap
          (fun k : ℕ => (w (-(k : ℤ) - 1)).reverse)).take n).map
            lazyTwoDimensionalStep).sum) := by
      funext w
      simp only [uibhbotConcatWalk, hneg, ↓reduceIte, neg_neg,
        Int.toNat_natCast, bind_pure_comp]
      change -(((((List.range n).map (fun k : ℕ => (k : ℤ))).flatMap
        (fun k : ℤ => (w (-k - 1)).reverse)).take n).map lazyTwoDimensionalStep).sum = _
      rw [List.flatMap_map]
    rw [he]
    exact (measurable_of_countable (fun v : List (Fin 3) =>
      -((v.take n).map lazyTwoDimensionalStep).sum)).comp
        (measurable_backward_blocks (List.range n))

private theorem measurable_shifted_conditioned_path :
    Measurable (fun p : ℕ → ℤ × ℤ => fun n : ℕ =>
      if n = 0 then (0, 0) else (p (n - 1)).swap + (1, 0)) := by
  apply Measurable.of_eval
  intro n
  split_ifs <;> fun_prop

private theorem negative_path_law_iff_positive_prefix :
    (uibhbotWordFamilyLaw.map
        (fun w => fun n : ℕ => uibhbotConcatWalk w (-(n : ℤ))) =
      (rConditionedPathLaw 0 0).map
        (fun p => fun n : ℕ => if n = 0 then (0, 0)
          else (p (n - 1)).swap + (1, 0))) ↔
    ∀ n : ℕ,
      uibhbotWordFamilyLaw.map
          (fun w => fun j : Fin (n + 2) => uibhbotConcatWalk w (-(j.val : ℤ))) =
        (rConditionedPathLaw 0 0).map
          (fun p => fun j : Fin (n + 2) => if j.val = 0 then (0, 0)
            else (p (j.val - 1)).swap + (1, 0)) := by
  constructor
  · intro h n
    have he := congrArg (fun μ : Measure (ℕ → ℤ × ℤ) =>
      μ.map (fun p => fun j : Fin (n + 2) => p j.val)) h
    rw [Measure.map_map (by fun_prop) measurable_negative_path,
      Measure.map_map (by fun_prop) measurable_shifted_conditioned_path] at he
    exact he
  · intro h
    apply measure_eq_of_fin_prefix_map_eq
    intro n
    have hmleft : Measurable (fun w : ℤ → List (Fin 3) =>
        fun j : Fin (n + 2) => uibhbotConcatWalk w (-(j.val : ℤ))) :=
      (show Measurable (fun p : ℕ → ℤ × ℤ =>
        fun j : Fin (n + 2) => p j.val) by fun_prop).comp measurable_negative_path
    have hmright : Measurable (fun p : ℕ → ℤ × ℤ =>
        fun j : Fin (n + 2) => if j.val = 0 then (0, 0)
          else (p (j.val - 1)).swap + (1, 0)) := by
      fun_prop
    have he := congrArg (fun μ : Measure (Fin (n + 2) → ℤ × ℤ) =>
      μ.map (fun p => fun j : Fin (n + 1) => p j.castSucc)) (h n)
    rw [Measure.map_map (by fun_prop) hmleft,
      Measure.map_map (by fun_prop) hmright] at he
    rw [Measure.map_map (by fun_prop) measurable_negative_path,
      Measure.map_map (by fun_prop) measurable_shifted_conditioned_path]
    exact he

open Classical in
/-- Helper toward Definition 5.8: finite-prefix uniqueness reduces the full
negative path-law identification exactly to the displayed all-horizon renewal
sum. Neither side of this equivalence is asserted as proved here. -/
theorem uibhbot_negative_path_law_iff_renewal_sum :
    (uibhbotWordFamilyLaw.map
        (fun w => fun n : ℕ => uibhbotConcatWalk w (-(n : ℤ))) =
      (rConditionedPathLaw 0 0).map
        (fun p => fun n : ℕ => if n = 0 then (0, 0)
          else (p (n - 1)).swap + (1, 0))) ↔
    ∀ (n : ℕ) (q : Fin (n + 2) → ℤ × ℤ),
      (∑' v : Fin (n + 1) → List (Fin 3),
        (if uibhbotBackwardWordPrefix (n + 1) v = q then (1 : ℝ≥0∞) else 0) *
          ∏ i : Fin (n + 1), (if IsStoppedExcursionWord (v i) then
            (1 / 3 : ℝ≥0∞) ^ (v i).length else 0)) =
      if (∃ a : Fin n → Fin 3,
          uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) = q) ∧
          (∀ j : Fin (n + 1), 1 ≤ (q j.succ).1) then
        ENNReal.ofReal ((q (Fin.last (n + 1))).1 : ℝ) * ((3 : ℝ≥0∞) ^ n)⁻¹
      else 0 := by
  rw [negative_path_law_iff_positive_prefix]
  exact forall_congr' uibhbot_negative_prefix_law_iff_renewal_sum

end DirectedDistances.RandomWalk
end
