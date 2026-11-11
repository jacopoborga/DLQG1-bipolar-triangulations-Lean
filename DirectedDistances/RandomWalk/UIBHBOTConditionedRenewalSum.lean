module

public import DirectedDistances.RandomWalk.UIBHBOTConditionedLaw
public import DirectedDistances.RandomWalk.ExcursionBlockFlatLaw

/- # Stopped-word renewal sum for the UIBHBOT -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

open Classical in
/-- Helper toward Definition 5.8: the stopped-word weights have total mass one.
Almost-sure stopping is supplied by `ExcursionWordSupport`, rather than assumed. -/
theorem uibhbot_stopped_word_weight_sum :
    (∑' v : List (Fin 3),
      if IsStoppedExcursionWord v then (1 / 3 : ℝ≥0∞) ^ v.length else 0) = 1 := by
  simpa [excursionPassage_one_iff] using
    (lintegral_flat (k := 1) (by omega) (fun _ => 1)).symm

/-- Helper toward Definition 5.8: read the last `N` letters of a passage
word backward, negating the integrated displacement. -/
@[expose] def uibhbotPassageBackwardPrefix (N : ℕ) (u : List (Fin 3)) :
    Fin (N + 1) → ℤ × ℤ :=
  fun j => -(((u.reverse.take j.val).map lazyTwoDimensionalStep).sum)

private theorem ofFn_rev {α : Type*} (N : ℕ) (v : Fin N → α) :
    List.ofFn (fun i => v i.rev) = (List.ofFn v).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp
    congr 1
    apply Fin.ext
    simp [Fin.rev]
    omega

private theorem backwardPrefix_eq_passage (N : ℕ) (v : Fin N → List (Fin 3)) :
    uibhbotBackwardWordPrefix N v =
      uibhbotPassageBackwardPrefix N ((List.ofFn (fun i => v i.rev)).flatten) := by
  have he : ((List.ofFn (fun i => v i.rev)).flatten).reverse =
      (List.ofFn (fun i => (v i).reverse)).flatten := by
    rw [ofFn_rev, List.reverse_flatten, List.map_reverse, List.reverse_reverse]
    rw [List.map_ofFn]
    rfl
  funext j
  change -(((((List.ofFn fun i => (v i).reverse).flatten).take j.val).map
    lazyTwoDimensionalStep).sum) = _
  rw [uibhbotPassageBackwardPrefix, he]

private theorem backwardPrefix_lintegral_eq_passage (N : ℕ)
    (f : (Fin (N + 1) → ℤ × ℤ) → ℝ≥0∞) :
    (∫⁻ v, f (uibhbotBackwardWordPrefix N v)
      ∂(Measure.pi fun _ : Fin N => excursionWordLaw)) =
    ∫⁻ v, f (uibhbotPassageBackwardPrefix N (List.ofFn v).flatten)
      ∂(Measure.pi fun _ : Fin N => excursionWordLaw) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin N => List (Fin 3)) Fin.revPerm
  have he (v : Fin N → List (Fin 3)) : e v = fun i => v i.rev := by
    funext i
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin N => List (Fin 3)) Fin.revPerm v i.rev
    simpa [e] using h
  have hp : MeasurePreserving e
      (Measure.pi fun _ : Fin N => excursionWordLaw)
      (Measure.pi fun _ : Fin N => excursionWordLaw) :=
    measurePreserving_piCongrLeft (fun _ : Fin N => excursionWordLaw) Fin.revPerm
  simp_rw [backwardPrefix_eq_passage]
  conv_lhs => arg 2; ext v; rw [← he v]
  exact hp.lintegral_comp (f := fun v =>
    f (uibhbotPassageBackwardPrefix N (List.ofFn v).flatten))
    (measurable_of_countable _)

open Classical in
/-- Helper toward Definition 5.8: the original tuple renewal sum is exactly
one sum over first-passage words. This is a reduction, with no density premise. -/
theorem uibhbot_negative_renewal_sum_eq_passage_sum (n : ℕ)
    (q : Fin (n + 2) → ℤ × ℤ) :
    (∑' v : Fin (n + 1) → List (Fin 3),
      (if uibhbotBackwardWordPrefix (n + 1) v = q then (1 : ℝ≥0∞) else 0) *
        ∏ i : Fin (n + 1), (if IsStoppedExcursionWord (v i) then
          (1 / 3 : ℝ≥0∞) ^ (v i).length else 0)) =
      ∑' u : List (Fin 3),
        (if excursionPassage (n + 1) u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) *
          (if uibhbotPassageBackwardPrefix (n + 1) u = q then 1 else 0) := by
  classical
  rw [← uibhbot_negative_prefix_cylinder_sum (n + 1),
    uibhbot_negative_prefix_eq_word_product,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← lintegral_indicator_one MeasurableSet.of_discrete]
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply]
  change (∫⁻ v, (if uibhbotBackwardWordPrefix (n + 1) v = q
    then (1 : ℝ≥0∞) else 0) ∂(Measure.pi fun _ : Fin (n + 1) => excursionWordLaw)) = _
  rw [backwardPrefix_lintegral_eq_passage (n + 1)
    (fun p => if p = q then 1 else 0)]
  exact lintegral_flat (by omega)
    (fun u => if uibhbotPassageBackwardPrefix (n + 1) u = q then 1 else 0)

open Classical in
/-- Helper toward Definition 5.8: the exact renewal-sum evaluation at the
initial horizon follows from the proved deterministic first-step law. -/
theorem uibhbot_negative_renewal_sum_zero (q : Fin (0 + 2) → ℤ × ℤ) :
    (∑' v : Fin (0 + 1) → List (Fin 3),
      (if uibhbotBackwardWordPrefix (0 + 1) v = q
        then (1 : ℝ≥0∞) else 0) *
        ∏ i : Fin (0 + 1),
          (if IsStoppedExcursionWord (v i) then
            (1 / 3 : ℝ≥0∞) ^ (v i).length else 0)) =
    if (∃ a : Fin 0 → Fin 3,
        uibhbotShiftedConditionedPrefix 0
          (lazyTwoDimensionalPrefix 0 0 a) = q) ∧
        (∀ j : Fin (0 + 1), 1 ≤ (q j.succ).1) then
      ENNReal.ofReal ((q (Fin.last (0 + 1))).1 : ℝ) *
        ((3 : ℝ≥0∞) ^ 0)⁻¹
    else 0 := by
  exact (uibhbot_negative_prefix_law_iff_renewal_sum 0).mp
    uibhbot_negative_prefix_one q

private theorem fst_sum_ge_neg_length (u : List (Fin 3)) :
    -(u.length : ℤ) ≤ ((u.map lazyTwoDimensionalStep).sum).1 := by
  induction u with
  | nil => simp
  | cons c u ih =>
      have hs : -1 ≤ (lazyTwoDimensionalStep c).1 := by
        change -1 ≤ (c : ℤ) - 1
        omega
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
        List.map_cons, List.sum_cons, Prod.fst_add]
      omega

/-- Helper toward Definition 5.8: a passage to `-N` has at least `N`
letters, so the backward prefix never reads past the available word. -/
theorem uibhbot_passage_length_le {N : ℕ} {u : List (Fin 3)}
    (hu : excursionPassage N u) : N ≤ u.length := by
  have h := fst_sum_ge_neg_length u
  rw [hu.2.1] at h
  omega

private theorem fst_reverse_take (u : List (Fin 3)) (i : ℕ) :
    (((u.reverse.take i).map lazyTwoDimensionalStep).sum).1 =
      ((u.map lazyTwoDimensionalStep).sum).1 -
        (((u.take (u.length - i)).map lazyTwoDimensionalStep).sum).1 := by
  have h := congrArg (fun v : List (Fin 3) => ((v.map lazyTwoDimensionalStep).sum).1)
    (List.take_append_drop (u.length - i) u)
  simp only [List.map_append, List.sum_append, Prod.fst_add] at h
  rw [List.take_reverse, List.map_reverse, List.sum_reverse]
  omega

/-- Helper toward Definition 5.8: every nonzero point of a reversed
first-passage prefix has first coordinate at least one. -/
theorem uibhbot_passage_backward_prefix_positive {N : ℕ} {u : List (Fin 3)}
    (hu : excursionPassage N u) (j : Fin N) :
    1 ≤ (uibhbotPassageBackwardPrefix N u j.succ).1 := by
  have hlen := uibhbot_passage_length_le hu
  have hj : u.length - (j.val + 1) < u.length := by omega
  have hb := hu.2.2 (u.length - (j.val + 1)) hj
  change 1 ≤ -((((u.reverse.take (j.val + 1)).map lazyTwoDimensionalStep).sum).1)
  rw [fst_reverse_take, hu.2.1]
  omega

/-- Helper toward Definition 5.8: reverse a word and reflect its first-coordinate steps. -/
@[expose] def uibhbotReflectReverse (u : List (Fin 3)) : List (Fin 3) :=
  u.reverse.map Fin.rev

private theorem uibhbotReflectReverse_involutive (u : List (Fin 3)) :
    uibhbotReflectReverse (uibhbotReflectReverse u) = u := by
  simp [uibhbotReflectReverse, List.map_reverse, List.map_map, Function.comp_def]

private theorem fst_reflect (u : List (Fin 3)) :
    (((u.map Fin.rev).map lazyTwoDimensionalStep).sum).1 =
      -((u.map lazyTwoDimensionalStep).sum).1 := by
  induction u with
  | nil => simp
  | cons c u ih =>
      simp only [List.map_cons, List.sum_cons, Prod.fst_add, ih]
      have hc : (lazyTwoDimensionalStep c.rev).1 = -(lazyTwoDimensionalStep c).1 := by
        fin_cases c <;> norm_num [Fin.rev, lazyTwoDimensionalStep]
      rw [hc]
      omega

private theorem fst_uibhbotReflectReverse (u : List (Fin 3)) :
    (((uibhbotReflectReverse u).map lazyTwoDimensionalStep).sum).1 =
      -((u.map lazyTwoDimensionalStep).sum).1 := by
  rw [uibhbotReflectReverse, fst_reflect, List.map_reverse, List.sum_reverse]

private theorem fst_uibhbotReflectReverse_take (u : List (Fin 3)) (i : ℕ) :
    ((((uibhbotReflectReverse u).take i).map lazyTwoDimensionalStep).sum).1 =
      (((u.take (u.length - i)).map lazyTwoDimensionalStep).sum).1 -
        ((u.map lazyTwoDimensionalStep).sum).1 := by
  rw [uibhbotReflectReverse, ← List.map_take, fst_reflect, fst_reverse_take]
  omega

/-- Helper toward Definition 5.8: reflection and reversal, followed by one
down-step, identify nonnegative meanders with first-passage words. -/
theorem uibhbot_reflect_reverse_passage_iff (h : ℕ) (u : List (Fin 3)) :
    excursionPassage (h + 1) (uibhbotReflectReverse u ++ [0]) ↔
      ((u.map lazyTwoDimensionalStep).sum).1 = (h : ℤ) ∧
        ∀ i ≤ u.length, 0 ≤ (((u.take i).map lazyTwoDimensionalStep).sum).1 := by
  have hlen : (uibhbotReflectReverse u).length = u.length := by simp [uibhbotReflectReverse]
  have htotal : (((uibhbotReflectReverse u ++ [0]).map lazyTwoDimensionalStep).sum).1 =
      -((u.map lazyTwoDimensionalStep).sum).1 - 1 := by
    simp [fst_uibhbotReflectReverse, sub_eq_add_neg]
  constructor
  · intro hu
    have hend := hu.2.1
    rw [htotal] at hend
    have hs : ((u.map lazyTwoDimensionalStep).sum).1 = (h : ℤ) := by omega
    refine ⟨hs, fun i hi => ?_⟩
    have hj : u.length - i < (uibhbotReflectReverse u ++ [0]).length := by simp [hlen]
    have hb := hu.2.2 (u.length - i) hj
    rw [List.take_append_of_le_length (by omega : u.length - i ≤ (uibhbotReflectReverse u).length),
      fst_uibhbotReflectReverse_take, hs] at hb
    have hi' : u.length - (u.length - i) = i := by omega
    rw [hi'] at hb
    omega
  · rintro ⟨hs, hb⟩
    refine ⟨by simp, ?_, ?_⟩
    · rw [htotal, hs]
      omega
    · intro i hi
      have hi' : i ≤ (uibhbotReflectReverse u).length := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      rw [List.take_append_of_le_length hi', fst_uibhbotReflectReverse_take, hs]
      have hnonneg := hb (u.length - i) (Nat.sub_le _ _)
      omega

private theorem passage_last_zero {k : ℕ} {u : List (Fin 3)}
    (hu : excursionPassage k u) (hne : u ≠ []) : u.getLast hne = 0 := by
  have hlen : u.length - 1 < u.length := by simpa using hu.1
  have hb := hu.2.2 (u.length - 1) hlen
  rw [List.take_eq_dropLast (by omega)] at hb
  have he := congrArg (fun v : List (Fin 3) => ((v.map lazyTwoDimensionalStep).sum).1)
    (List.dropLast_concat_getLast hne)
  simp only [List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton, Prod.fst_add] at he
  have hs : -1 ≤ (lazyTwoDimensionalStep (u.getLast hne)).1 := by
    change -1 ≤ (u.getLast hne : ℤ) - 1
    omega
  have ht := hu.2.1
  have hc : (lazyTwoDimensionalStep (u.getLast hne)).1 = -1 := by omega
  change (u.getLast hne : ℤ) - 1 = -1 at hc
  apply Fin.ext
  omega

open Classical in
/-- Helper toward Definition 5.8: the total weight of nonnegative meanders
ending at any prescribed height is `3`. This is the completion mass needed
for a partial reversed stopped block; it follows from passage normalization. -/
theorem uibhbot_nonnegative_meander_weight_sum (h : ℕ) :
    (∑' u : List (Fin 3),
      if ((u.map lazyTwoDimensionalStep).sum).1 = (h : ℤ) ∧
        (∀ i ≤ u.length, 0 ≤ (((u.take i).map lazyTwoDimensionalStep).sum).1) then
        (1 / 3 : ℝ≥0∞) ^ u.length else 0) = 3 := by
  classical
  let S : Set (List (Fin 3)) := {u |
    ((u.map lazyTwoDimensionalStep).sum).1 = (h : ℤ) ∧
      ∀ i ≤ u.length, 0 ≤ (((u.take i).map lazyTwoDimensionalStep).sum).1}
  let T : Set (List (Fin 3)) := {v | excursionPassage (h + 1) v}
  let cat : S → T := fun u => ⟨uibhbotReflectReverse u.val ++ [0],
    (uibhbot_reflect_reverse_passage_iff h u.val).mpr u.property⟩
  have hcat : Function.Bijective cat := by
    constructor
    · intro u v he
      have he' : uibhbotReflectReverse u.val = uibhbotReflectReverse v.val :=
        List.append_cancel_right (congrArg Subtype.val he)
      apply Subtype.ext
      have he'' := congrArg uibhbotReflectReverse he'
      simpa only [uibhbotReflectReverse_involutive] using he''
    · intro v
      have hne : v.val ≠ [] := by
        intro he
        have hp := v.property.1
        simp [he] at hp
      have hv : uibhbotReflectReverse (uibhbotReflectReverse v.val.dropLast) ++ [0] =
          v.val := by
        rw [uibhbotReflectReverse_involutive, ← passage_last_zero v.property hne]
        exact List.dropLast_concat_getLast hne
      have hs : uibhbotReflectReverse v.val.dropLast ∈ S := by
        apply (uibhbot_reflect_reverse_passage_iff h _).mp
        rw [hv]
        exact v.property
      exact ⟨⟨uibhbotReflectReverse v.val.dropLast, hs⟩, Subtype.ext hv⟩
  let F : List (Fin 3) → ℝ≥0∞ := fun u =>
    if u ∈ S then (1 / 3 : ℝ≥0∞) ^ u.length else 0
  let G : List (Fin 3) → ℝ≥0∞ := fun v =>
    if v ∈ T then (1 / 3 : ℝ≥0∞) ^ v.length else 0
  have hF : Function.support F ⊆ S := by
    intro u hu
    by_contra hn
    exact hu (by simp [F, hn])
  have hG : Function.support G ⊆ T := by
    intro v hv
    by_contra hn
    exact hv (by simp [G, hn])
  have hmass : (∑' v : List (Fin 3), G v) = 1 := by
    simpa [G, T] using (lintegral_flat (k := h + 1) (by omega) (fun _ => 1)).symm
  change (∑' u, F u) = 3
  calc
    _ = ∑' u : S, F u := (tsum_subtype_eq_of_support_subset hF).symm
    _ = ∑' u : S, (3 : ℝ≥0∞) * G (cat u) := by
      apply tsum_congr
      intro u
      simp only [F, G, u.property, (cat u).property, ↓reduceIte]
      change (1 / 3 : ℝ≥0∞) ^ u.val.length =
        3 * (1 / 3 : ℝ≥0∞) ^ (uibhbotReflectReverse u.val ++ [0]).length
      simp only [List.length_append, List.length_singleton, uibhbotReflectReverse,
        List.length_map, List.length_reverse, pow_succ]
      calc
        _ = (1 / 3 : ℝ≥0∞) ^ u.val.length * (3 * (1 / 3)) := by
          rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
        _ = _ := by ac_rfl
    _ = 3 * ∑' u : S, G (cat u) := ENNReal.tsum_mul_left
    _ = 3 * ∑' v : T, G v := congrArg (fun x : ℝ≥0∞ => 3 * x)
      (tsum_comp_eq_tsum_of_bijective hcat (fun v : T => G v.val))
    _ = 3 * ∑' v, G v := congrArg (fun x : ℝ≥0∞ => 3 * x)
      (tsum_subtype_eq_of_support_subset hG)
    _ = 3 := by rw [hmass, mul_one]

/-- Helper toward Definition 5.8: a fixed passage suffix is completed to a
stopped word precisely by a nonnegative meander at the required height.
The empty completion is included when `h = 0`. -/
theorem uibhbot_stopped_append_passage_iff (h : ℕ) (s u : List (Fin 3))
    (hs : excursionPassage (h + 1) s) :
    IsStoppedExcursionWord (u ++ s) ↔
      ((u.map lazyTwoDimensionalStep).sum).1 = (h : ℤ) ∧
        ∀ i ≤ u.length, 0 ≤ (((u.take i).map lazyTwoDimensionalStep).sum).1 := by
  have htotal : (((u ++ s).map lazyTwoDimensionalStep).sum).1 =
      ((u.map lazyTwoDimensionalStep).sum).1 +
        ((s.map lazyTwoDimensionalStep).sum).1 := by
    simp only [List.map_append, List.sum_append, Prod.fst_add]
  constructor
  · intro hu
    have he := hu.2.1
    rw [htotal, hs.2.1] at he
    refine ⟨by omega, fun i hi => ?_⟩
    have hil : i < (u ++ s).length := by
      simp only [List.length_append]
      have := hs.1
      omega
    have hb := hu.2.2 i hil
    rw [List.take_append_of_le_length hi] at hb
    omega
  · rintro ⟨he, hb⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append]
      have := hs.1
      omega
    · rw [htotal, he, hs.2.1]
      omega
    · intro i hi
      by_cases hil : i ≤ u.length
      · rw [List.take_append_of_le_length hil]
        have := hb i hil
        omega
      · have hir : i - u.length < s.length := by
          simp only [List.length_append] at hi
          omega
        have hie : i = u.length + (i - u.length) := by omega
        rw [hie, List.take_length_add_append]
        simp only [List.map_append, List.sum_append, Prod.fst_add, he]
        have := hs.2.2 (i - u.length) hir
        omega

/-- Helper toward Definition 5.8: appending a fixed passage suffix gives
a bijection from its nonnegative meander completions to stopped words
with that suffix. -/
theorem uibhbot_stopped_suffix_bijective (h : ℕ) (s : List (Fin 3))
    (hs : excursionPassage (h + 1) s) :
    Function.Bijective (fun u : {u : List (Fin 3) //
        ((u.map lazyTwoDimensionalStep).sum).1 = (h : ℤ) ∧
          ∀ i ≤ u.length, 0 ≤ (((u.take i).map lazyTwoDimensionalStep).sum).1} =>
      (⟨u.val ++ s, (uibhbot_stopped_append_passage_iff h s u.val hs).mpr u.property,
        ⟨u.val, rfl⟩⟩ : {v : List (Fin 3) // IsStoppedExcursionWord v ∧ s <:+ v})) := by
  constructor
  · intro u v he
    apply Subtype.ext
    exact List.append_cancel_right (congrArg Subtype.val he)
  · intro v
    obtain ⟨u, hu⟩ := v.property.2
    have hmeander := (uibhbot_stopped_append_passage_iff h s u hs).mp
      (hu ▸ v.property.1)
    exact ⟨⟨u, hmeander⟩, Subtype.ext hu⟩

open Classical in
/-- Helper toward Definition 5.8: the exact weight of all stopped words
ending in a fixed passage suffix. This includes the empty completion and
does not add a separate endpoint-cut class. -/
theorem uibhbot_stopped_suffix_weight_sum (h : ℕ) (s : List (Fin 3))
    (hs : excursionPassage (h + 1) s) :
    (∑' v : List (Fin 3),
      if IsStoppedExcursionWord v ∧ s <:+ v then
        (1 / 3 : ℝ≥0∞) ^ v.length else 0) =
      (3 : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ s.length := by
  classical
  let S : Set (List (Fin 3)) := {u |
    ((u.map lazyTwoDimensionalStep).sum).1 = (h : ℤ) ∧
      ∀ i ≤ u.length, 0 ≤ (((u.take i).map lazyTwoDimensionalStep).sum).1}
  let T : Set (List (Fin 3)) := {v | IsStoppedExcursionWord v ∧ s <:+ v}
  let cat : S → T := fun u => ⟨u.val ++ s,
    (uibhbot_stopped_append_passage_iff h s u.val hs).mpr u.property, ⟨u.val, rfl⟩⟩
  let F : List (Fin 3) → ℝ≥0∞ := fun u =>
    if u ∈ S then (1 / 3 : ℝ≥0∞) ^ u.length else 0
  let G : List (Fin 3) → ℝ≥0∞ := fun v =>
    if v ∈ T then (1 / 3 : ℝ≥0∞) ^ v.length else 0
  have hF : Function.support F ⊆ S := by
    intro u hu
    by_contra hn
    exact hu (by simp [F, hn])
  have hG : Function.support G ⊆ T := by
    intro v hv
    by_contra hn
    exact hv (by simp [G, hn])
  change (∑' v, G v) = _
  calc
    _ = ∑' v : T, G v := (tsum_subtype_eq_of_support_subset hG).symm
    _ = ∑' u : S, G (cat u) :=
      (tsum_comp_eq_tsum_of_bijective
        (uibhbot_stopped_suffix_bijective h s hs) (fun v : T => G v.val)).symm
    _ = ∑' u : S, F u * (1 / 3 : ℝ≥0∞) ^ s.length := by
      apply tsum_congr
      intro u
      simp only [G, F, (cat u).property, u.property, ↓reduceIte]
      change (1 / 3 : ℝ≥0∞) ^ (u.val ++ s).length = _
      rw [List.length_append, pow_add]
    _ = (∑' u : S, F u) * (1 / 3 : ℝ≥0∞) ^ s.length := ENNReal.tsum_mul_right
    _ = (∑' u, F u) * (1 / 3 : ℝ≥0∞) ^ s.length :=
      congrArg (fun x : ℝ≥0∞ => x * (1 / 3 : ℝ≥0∞) ^ s.length)
        (tsum_subtype_eq_of_support_subset hF)
    _ = 3 * (1 / 3 : ℝ≥0∞) ^ s.length := by
      rw [show (∑' u, F u) = 3 from uibhbot_nonnegative_meander_weight_sum h]

/-- Helper toward Definition 5.8: finite paths with a prescribed endpoint
and a lower bound on all first-coordinate prefix sums. -/
@[expose] def uibhbotFloorMeander (a h : ℕ) (u : List (Fin 3)) : Prop :=
  ((u.map lazyTwoDimensionalStep).sum).1 = (h : ℤ) ∧
    ∀ i ≤ u.length, -(a : ℤ) ≤ (((u.take i).map lazyTwoDimensionalStep).sum).1

private theorem negative_word_split {u : List (Fin 3)}
    (hn : ∃ i ≤ u.length, (((u.take i).map lazyTwoDimensionalStep).sum).1 < 0) :
    ∃ v w, IsStoppedExcursionWord v ∧ v ++ w = u := by
  let n := Nat.find hn
  have hns : n ≤ u.length ∧ (((u.take n).map lazyTwoDimensionalStep).sum).1 < 0 :=
    Nat.find_spec hn
  have hpos : 0 < n := by
    by_contra hh
    have hz : n = 0 := by omega
    simp [hz] at hns
  have hbefore : ∀ j < n,
      0 ≤ (((u.take j).map lazyTwoDimensionalStep).sum).1 := by
    intro j hj
    have := Nat.find_min hn hj
    omega
  have hprev := hbefore (n - 1) (by omega)
  have hstep : -1 ≤ (lazyTwoDimensionalStep u[n - 1]).1 := by
    change -1 ≤ (u[n - 1] : ℤ) - 1
    omega
  have he : (((u.take n).map lazyTwoDimensionalStep).sum).1 =
      (((u.take (n - 1)).map lazyTwoDimensionalStep).sum).1 +
        (lazyTwoDimensionalStep u[n - 1]).1 := by
    have hn' : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn', List.take_succ_eq_append_getElem (by omega)]
    simp only [List.map_append, List.sum_append, Prod.fst_add,
      List.map_singleton, List.sum_singleton]
  refine ⟨u.take n, u.drop n, ?_, List.take_append_drop n u⟩
  refine ⟨?_, by omega, ?_⟩
  · simp only [List.length_take, Nat.min_eq_left hns.1]
    exact hpos
  · intro j hj
    simp only [List.length_take, Nat.min_eq_left hns.1] at hj
    rw [List.take_take, Nat.min_eq_left hj.le]
    have := hbefore j hj
    omega

private theorem stopped_prefix_unique {u v : List (Fin 3)}
    (hu : IsStoppedExcursionWord u) (hv : IsStoppedExcursionWord v)
    (hp : u <+: v) : u = v := by
  have hle := hp.length_le
  by_cases he : u.length = v.length
  · exact hp.eq_of_length he
  · have hb := hv.2.2 u.length (by omega)
    rw [← List.prefix_iff_eq_take.mp hp, hu.2.1] at hb
    omega

private theorem floor_append_iff (a h : ℕ) (v w : List (Fin 3))
    (hv : IsStoppedExcursionWord v) :
    uibhbotFloorMeander (a + 1) h (v ++ w) ↔
      uibhbotFloorMeander a (h + 1) w := by
  have htotal : (((v ++ w).map lazyTwoDimensionalStep).sum).1 =
      -1 + ((w.map lazyTwoDimensionalStep).sum).1 := by
    simp only [List.map_append, List.sum_append, Prod.fst_add, hv.2.1]
  constructor
  · rintro ⟨he, hb⟩
    refine ⟨by rw [htotal] at he; omega, fun i hi => ?_⟩
    have hi' : v.length + i ≤ (v ++ w).length := by
      simp only [List.length_append]
      omega
    have := hb (v.length + i) hi'
    rw [List.take_length_add_append] at this
    simp only [List.map_append, List.sum_append, Prod.fst_add, hv.2.1] at this
    omega
  · rintro ⟨he, hb⟩
    refine ⟨by rw [htotal, he]; omega, fun i hi => ?_⟩
    by_cases hil : i < v.length
    · rw [List.take_append_of_le_length hil.le]
      have := hv.2.2 i hil
      omega
    · have hie : i = v.length + (i - v.length) := by omega
      have hir : i - v.length ≤ w.length := by
        simp only [List.length_append] at hi
        omega
      rw [hie, List.take_length_add_append]
      simp only [List.map_append, List.sum_append, Prod.fst_add, hv.2.1]
      have := hb (i - v.length) hir
      omega

private theorem stopped_append_not_nonnegative (v w : List (Fin 3))
    (hv : IsStoppedExcursionWord v) :
    ¬ (∀ i ≤ (v ++ w).length,
      0 ≤ ((((v ++ w).take i).map lazyTwoDimensionalStep).sum).1) := by
  intro hb
  have hi : v.length ≤ (v ++ w).length := by simp
  have := hb v.length hi
  rw [List.take_left, hv.2.1] at this
  omega

open Classical in
private theorem word_subtype_weight_sum (P : List (Fin 3) → Prop) :
    (∑' u : {u : List (Fin 3) // P u}, (1 / 3 : ℝ≥0∞) ^ u.val.length) =
      ∑' u : List (Fin 3), if P u then (1 / 3 : ℝ≥0∞) ^ u.length else 0 := by
  classical
  let F : List (Fin 3) → ℝ≥0∞ := fun u =>
    if P u then (1 / 3 : ℝ≥0∞) ^ u.length else 0
  have hs : Function.support F ⊆ {u | P u} := by
    intro u hu
    by_contra hn
    change ¬ P u at hn
    exact hu (by simp [F, hn])
  calc
    _ = ∑' u : {u : List (Fin 3) // P u}, F u := by
      apply tsum_congr
      intro u
      simp only [F, u.property, ↓reduceIte]
    _ = _ := tsum_subtype_eq_of_support_subset hs

private theorem floor_negative_bijective (a h : ℕ) :
    Function.Bijective (fun p :
        {v : List (Fin 3) // IsStoppedExcursionWord v} ×
          {w : List (Fin 3) // uibhbotFloorMeander a (h + 1) w} =>
      (⟨p.1.val ++ p.2.val,
        (floor_append_iff a h p.1.val p.2.val p.1.property).mpr p.2.property,
        fun hn => stopped_append_not_nonnegative p.1.val p.2.val p.1.property hn.2⟩ :
        {u : List (Fin 3) // uibhbotFloorMeander (a + 1) h u ∧
          ¬ uibhbotFloorMeander 0 h u})) := by
  constructor
  · intro p q he
    have he' : p.1.val ++ p.2.val = q.1.val ++ q.2.val := congrArg Subtype.val he
    have hp : p.1.val <+: p.1.val ++ p.2.val := ⟨_, rfl⟩
    have hq : q.1.val <+: p.1.val ++ p.2.val := by
      rw [he']
      exact ⟨_, rfl⟩
    have hh : p.1.val = q.1.val := by
      rcases List.prefix_or_prefix_of_prefix hp hq with hh | hh
      · exact stopped_prefix_unique p.1.property q.1.property hh
      · exact (stopped_prefix_unique q.1.property p.1.property hh).symm
    apply Prod.ext
    · exact Subtype.ext hh
    · apply Subtype.ext
      rw [hh] at he'
      exact List.append_cancel_left he'
  · intro u
    have hn : ∃ i ≤ u.val.length,
        (((u.val.take i).map lazyTwoDimensionalStep).sum).1 < 0 := by
      by_contra hn
      apply u.property.2
      refine ⟨u.property.1.1, fun i hi => ?_⟩
      have hni : ¬ (((u.val.take i).map lazyTwoDimensionalStep).sum).1 < 0 := by
        intro hh
        exact hn ⟨i, hi, hh⟩
      simpa only [Nat.cast_zero, neg_zero] using (le_of_not_gt hni)
    obtain ⟨v, w, hv, he⟩ := negative_word_split hn
    have hw : uibhbotFloorMeander a (h + 1) w := by
      apply (floor_append_iff a h v w hv).mp
      rw [he]
      exact u.property.1
    exact ⟨(⟨v, hv⟩, ⟨w, hw⟩), Subtype.ext he⟩

/-- Helper toward Definition 5.8: the complete disjoint decomposition of
a floor-constrained path into either a nonnegative meander or its unique
first stopped block followed by a path with one fewer allowed negative
level. Iteration is the passage-word alternative to cutting the tuple at
last visits; the nonnegative branch includes the empty word. -/
theorem uibhbot_floor_meander_partition (a h : ℕ) :
    ∃ e :
      ({u : List (Fin 3) // uibhbotFloorMeander 0 h u} ⊕
        ({v : List (Fin 3) // IsStoppedExcursionWord v} ×
          {w : List (Fin 3) // uibhbotFloorMeander a (h + 1) w})) ≃
        {u : List (Fin 3) // uibhbotFloorMeander (a + 1) h u},
      (∀ u, (e (Sum.inl u)).val = u.val) ∧
        ∀ p, (e (Sum.inr p)).val = p.1.val ++ p.2.val := by
  classical
  let P := {u : List (Fin 3) // uibhbotFloorMeander 0 h u}
  let R := {v : List (Fin 3) // IsStoppedExcursionWord v} ×
    {w : List (Fin 3) // uibhbotFloorMeander a (h + 1) w}
  let T := {u : List (Fin 3) // uibhbotFloorMeander (a + 1) h u}
  let B := {u : List (Fin 3) // uibhbotFloorMeander (a + 1) h u ∧
    ¬ uibhbotFloorMeander 0 h u}
  let neg : R → B := fun p => ⟨p.1.val ++ p.2.val,
    (floor_append_iff a h p.1.val p.2.val p.1.property).mpr p.2.property,
    fun hn => stopped_append_not_nonnegative p.1.val p.2.val p.1.property hn.2⟩
  let pos : P → T := fun u => ⟨u.val, u.property.1, fun i hi => by
    have hb := u.property.2 i hi
    simp only [Nat.cast_zero, neg_zero] at hb
    omega⟩
  let f : P ⊕ R → T := Sum.elim pos (fun p => ⟨(neg p).val, (neg p).property.1⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      cases x with
      | inl u =>
          cases y with
          | inl v =>
              have he' : u.val = v.val := congrArg (fun z : T => z.val) he
              exact congrArg Sum.inl (Subtype.ext he')
          | inr p =>
              have he' : u.val = (neg p).val := congrArg Subtype.val he
              exact False.elim ((neg p).property.2 (he' ▸ u.property))
      | inr p =>
          cases y with
          | inl u =>
              have he' : (neg p).val = u.val := congrArg Subtype.val he
              exact False.elim ((neg p).property.2 (he'.symm ▸ u.property))
          | inr q =>
              have hn : neg p = neg q := Subtype.ext (congrArg (fun z : T => z.val) he)
              exact congrArg Sum.inr ((floor_negative_bijective a h).injective hn)
    · intro u
      by_cases h0 : uibhbotFloorMeander 0 h u.val
      · exact ⟨Sum.inl ⟨u.val, h0⟩, Subtype.ext rfl⟩
      · obtain ⟨p, hp⟩ := (floor_negative_bijective a h).surjective
          (⟨u.val, u.property, h0⟩ : B)
        exact ⟨Sum.inr p, Subtype.ext (congrArg (fun z : B => z.val) hp)⟩
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl, fun _ => rfl⟩

/-- Helper toward Definition 5.8: a finite path from zero to any
nonnegative height, killed below `-a`, has total word weight `3(a+1)`.
The proof splits at the first negative prefix, rather than assuming a
Markov or ladder-time identity. -/
theorem uibhbot_floor_meander_weight_sum (a h : ℕ) :
    (∑' u : {u : List (Fin 3) // uibhbotFloorMeander a h u},
      (1 / 3 : ℝ≥0∞) ^ u.val.length) = (3 : ℝ≥0∞) * (a + 1) := by
  classical
  induction a generalizing h with
  | zero =>
      rw [word_subtype_weight_sum]
      simpa only [uibhbotFloorMeander, Nat.cast_zero, neg_zero, zero_add, mul_one]
        using uibhbot_nonnegative_meander_weight_sum h
  | succ a ih =>
      let B : Set (List (Fin 3)) := {u | uibhbotFloorMeander (a + 1) h u ∧
        ¬ uibhbotFloorMeander 0 h u}
      have hsplit :
          (∑' u : {u : List (Fin 3) // uibhbotFloorMeander (a + 1) h u},
            (1 / 3 : ℝ≥0∞) ^ u.val.length) =
          (∑' u : {u : List (Fin 3) // uibhbotFloorMeander 0 h u},
            (1 / 3 : ℝ≥0∞) ^ u.val.length) +
          ∑' u : B, (1 / 3 : ℝ≥0∞) ^ u.val.length := by
        rw [word_subtype_weight_sum, word_subtype_weight_sum,
          word_subtype_weight_sum, ← tsum_add]
        apply tsum_congr
        intro u
        have hmono : uibhbotFloorMeander 0 h u → uibhbotFloorMeander (a + 1) h u := by
          rintro ⟨he, hb⟩
          refine ⟨he, fun i hi => ?_⟩
          have := hb i hi
          simp only [Nat.cast_zero, neg_zero] at this
          omega
        by_cases h0 : uibhbotFloorMeander 0 h u
        · simp [B, h0, hmono h0]
        · by_cases ha : uibhbotFloorMeander (a + 1) h u <;> simp [B, h0, ha]
      have hnegative : (∑' u : B, (1 / 3 : ℝ≥0∞) ^ u.val.length) =
          (3 : ℝ≥0∞) * (a + 1) := by
        calc
          _ = ∑' p : {v : List (Fin 3) // IsStoppedExcursionWord v} ×
              {w : List (Fin 3) // uibhbotFloorMeander a (h + 1) w},
              (1 / 3 : ℝ≥0∞) ^ (p.1.val ++ p.2.val).length :=
            (tsum_comp_eq_tsum_of_bijective (floor_negative_bijective a h)
              (fun u : B => (1 / 3 : ℝ≥0∞) ^ u.val.length)).symm
          _ = ∑' v : {v : List (Fin 3) // IsStoppedExcursionWord v},
              ∑' w : {w : List (Fin 3) // uibhbotFloorMeander a (h + 1) w},
                (1 / 3 : ℝ≥0∞) ^ v.val.length *
                  (1 / 3 : ℝ≥0∞) ^ w.val.length := by
            simp only [List.length_append, pow_add, tsum_prod']
          _ = (∑' v : {v : List (Fin 3) // IsStoppedExcursionWord v},
              (1 / 3 : ℝ≥0∞) ^ v.val.length) *
              ∑' w : {w : List (Fin 3) // uibhbotFloorMeander a (h + 1) w},
                (1 / 3 : ℝ≥0∞) ^ w.val.length := by
            simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
          _ = 3 * (a + 1) := by
            rw [word_subtype_weight_sum, uibhbot_stopped_word_weight_sum, one_mul, ih]
      rw [hsplit, hnegative, word_subtype_weight_sum]
      have hz : (∑' u : List (Fin 3),
          if uibhbotFloorMeander 0 h u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) = 3 := by
        simpa only [uibhbotFloorMeander, Nat.cast_zero, neg_zero]
          using uibhbot_nonnegative_meander_weight_sum h
      rw [hz]
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]
      ac_rfl

private theorem passage_append_suffix_iff (N m : ℕ) (s u : List (Fin 3))
    (hs : excursionPassage m s) :
    excursionPassage N (u ++ s) ↔
      ((u.map lazyTwoDimensionalStep).sum).1 = (m : ℤ) - N ∧
        ∀ i ≤ u.length, -(N : ℤ) < (((u.take i).map lazyTwoDimensionalStep).sum).1 := by
  have htotal : (((u ++ s).map lazyTwoDimensionalStep).sum).1 =
      ((u.map lazyTwoDimensionalStep).sum).1 - m := by
    simp only [List.map_append, List.sum_append, Prod.fst_add, hs.2.1, sub_eq_add_neg]
  constructor
  · intro hu
    have he := hu.2.1
    rw [htotal] at he
    refine ⟨by omega, fun i hi => ?_⟩
    have hil : i < (u ++ s).length := by
      simp only [List.length_append]
      have := hs.1
      omega
    have hb := hu.2.2 i hil
    rwa [List.take_append_of_le_length hi] at hb
  · rintro ⟨he, hb⟩
    refine ⟨?_, by rw [htotal, he]; omega, fun i hi => ?_⟩
    · simp only [List.length_append]
      have := hs.1
      omega
    · by_cases hil : i ≤ u.length
      · rw [List.take_append_of_le_length hil]
        exact hb i hil
      · have hir : i - u.length < s.length := by
          simp only [List.length_append] at hi
          omega
        have hie : i = u.length + (i - u.length) := by omega
        rw [hie, List.take_length_add_append]
        simp only [List.map_append, List.sum_append, Prod.fst_add, he]
        have := hs.2.2 (i - u.length) hir
        omega

/-- Helper toward Definition 5.8: reversal and reflection turn the prefix
before a fixed passage suffix into a path killed below `-(m-1)`. -/
theorem uibhbot_passage_suffix_completion_iff (N m : ℕ) (s u : List (Fin 3))
    (hm : 0 < m) (hmN : m ≤ N) (hs : excursionPassage m s) :
    excursionPassage N (u ++ s) ↔
      uibhbotFloorMeander (m - 1) (N - m) (uibhbotReflectReverse u) := by
  rw [passage_append_suffix_iff N m s u hs]
  constructor
  · rintro ⟨he, hb⟩
    refine ⟨?_, fun i hi => ?_⟩
    · rw [fst_uibhbotReflectReverse, he]
      omega
    · rw [fst_uibhbotReflectReverse_take, he]
      have := hb (u.length - i) (Nat.sub_le _ _)
      omega
  · rintro ⟨he, hb⟩
    rw [fst_uibhbotReflectReverse] at he
    have he' : ((u.map lazyTwoDimensionalStep).sum).1 = (m : ℤ) - N := by omega
    refine ⟨he', fun i hi => ?_⟩
    have hlen : (uibhbotReflectReverse u).length = u.length := by
      simp only [uibhbotReflectReverse, List.length_map, List.length_reverse]
    have hb' := hb (u.length - i) (by rw [hlen]; exact Nat.sub_le _ _)
    rw [fst_uibhbotReflectReverse_take, he'] at hb'
    have hi' : u.length - (u.length - i) = i := by omega
    rw [hi'] at hb'
    omega

open Classical in
/-- Helper toward Definition 5.8: the first-passage words ending with a
prescribed passage suffix have exact mass `3m` times the suffix weight.
The first-negative-prefix decomposition in the floor-meander theorem
provides the `m` disjoint contributions without an endpoint-cut duplicate. -/
theorem uibhbot_passage_suffix_weight_sum (N m : ℕ) (s : List (Fin 3))
    (hm : 0 < m) (hmN : m ≤ N) (hs : excursionPassage m s) :
    (∑' v : List (Fin 3),
      if excursionPassage N v ∧ s <:+ v then
        (1 / 3 : ℝ≥0∞) ^ v.length else 0) =
      ((3 : ℝ≥0∞) * m) * (1 / 3 : ℝ≥0∞) ^ s.length := by
  classical
  let S := {u : List (Fin 3) // uibhbotFloorMeander (m - 1) (N - m) u}
  let T := {v : List (Fin 3) // excursionPassage N v ∧ s <:+ v}
  let cat : S → T := fun u => ⟨uibhbotReflectReverse u.val ++ s,
    (uibhbot_passage_suffix_completion_iff N m s (uibhbotReflectReverse u.val)
      hm hmN hs).mpr (by rw [uibhbotReflectReverse_involutive]; exact u.property),
    ⟨uibhbotReflectReverse u.val, rfl⟩⟩
  have hcat : Function.Bijective cat := by
    constructor
    · intro u v he
      have he' := List.append_cancel_right (congrArg Subtype.val he)
      have he'' := congrArg uibhbotReflectReverse he'
      apply Subtype.ext
      simpa only [uibhbotReflectReverse_involutive] using he''
    · intro v
      obtain ⟨u, hu⟩ := v.property.2
      have hp : excursionPassage N (u ++ s) := hu ▸ v.property.1
      have hmeander := (uibhbot_passage_suffix_completion_iff N m s u hm hmN hs).mp hp
      refine ⟨⟨uibhbotReflectReverse u, hmeander⟩, ?_⟩
      apply Subtype.ext
      change uibhbotReflectReverse (uibhbotReflectReverse u) ++ s = v.val
      rw [uibhbotReflectReverse_involutive, hu]
  calc
    _ = ∑' v : T, (1 / 3 : ℝ≥0∞) ^ v.val.length := by
      refine Eq.trans ?_ (word_subtype_weight_sum
        (fun v => excursionPassage N v ∧ s <:+ v)).symm
      apply tsum_congr
      intro v
      by_cases hv : excursionPassage N v ∧ s <:+ v <;> simp only [hv, ↓reduceIte]
    _ = ∑' u : S, (1 / 3 : ℝ≥0∞) ^ (cat u).val.length :=
      (tsum_comp_eq_tsum_of_bijective hcat
        (fun v : T => (1 / 3 : ℝ≥0∞) ^ v.val.length)).symm
    _ = ∑' u : S, (1 / 3 : ℝ≥0∞) ^ u.val.length *
        (1 / 3 : ℝ≥0∞) ^ s.length := by
      apply tsum_congr
      intro u
      change (1 / 3 : ℝ≥0∞) ^ (uibhbotReflectReverse u.val ++ s).length = _
      simp only [List.length_append, uibhbotReflectReverse,
        List.length_map, List.length_reverse, pow_add]
    _ = (∑' u : S, (1 / 3 : ℝ≥0∞) ^ u.val.length) *
        (1 / 3 : ℝ≥0∞) ^ s.length := ENNReal.tsum_mul_right
    _ = _ := by
      rw [uibhbot_floor_meander_weight_sum]
      have he : (m - 1 : ℕ) + 1 = m := by omega
      have he' : ((m - 1 : ℕ) : ℝ≥0∞) + 1 = m := by exact_mod_cast he
      rw [he']

private theorem word_eq_of_fst_prefix_eq (u v : List (Fin 3))
    (hlen : u.length = v.length)
    (hp : ∀ i ≤ u.length,
      (((u.take i).map lazyTwoDimensionalStep).sum).1 =
        (((v.take i).map lazyTwoDimensionalStep).sum).1) : u = v := by
  apply List.ext_getElem hlen
  intro i hi hj
  have h0 := hp i (by omega)
  have h1 := hp (i + 1) (by omega)
  rw [List.take_succ_eq_append_getElem hi, List.take_succ_eq_append_getElem hj] at h1
  simp only [List.map_append, List.sum_append, Prod.fst_add,
    List.map_singleton, List.sum_singleton] at h1
  have he : (lazyTwoDimensionalStep u[i]).1 = (lazyTwoDimensionalStep v[i]).1 := by omega
  change (u[i] : ℤ) - 1 = (v[i] : ℤ) - 1 at he
  apply Fin.ext
  omega

/-- Helper toward Definition 5.8: fixing the integrated backward prefix
is exactly fixing the terminal word of that length. -/
theorem uibhbot_passage_backward_prefix_eq_iff_suffix (N : ℕ)
    (s u : List (Fin 3)) (hslen : s.length = N) (hulen : N ≤ u.length) :
    uibhbotPassageBackwardPrefix N u = uibhbotPassageBackwardPrefix N s ↔ s <:+ u := by
  constructor
  · intro he
    have hword : u.reverse.take N = s.reverse := by
      apply word_eq_of_fst_prefix_eq
      · simp only [List.length_take, List.length_reverse, hslen,
          Nat.min_eq_left hulen]
      · intro i hi
        have hiN : i ≤ N := by
          simp only [List.length_take, List.length_reverse, Nat.min_eq_left hulen] at hi
          exact hi
        have hp := congrArg Prod.fst (congrFun he ⟨i, by omega⟩)
        change -(((u.reverse.take i).map lazyTwoDimensionalStep).sum).1 =
          -(((s.reverse.take i).map lazyTwoDimensionalStep).sum).1 at hp
        rw [List.take_take, Nat.min_eq_left hiN]
        omega
    apply List.reverse_prefix.mp
    rw [List.prefix_iff_eq_take, List.length_reverse, hslen]
    exact hword.symm
  · intro hs
    have hp := List.prefix_iff_eq_take.mp (List.reverse_prefix.mpr hs)
    rw [List.length_reverse, hslen] at hp
    funext j
    change -(((u.reverse.take j.val).map lazyTwoDimensionalStep).sum) =
      -(((s.reverse.take j.val).map lazyTwoDimensionalStep).sum)
    have hj : j.val ≤ N := by omega
    have ht := congrArg (List.take j.val) hp
    rw [List.take_take, Nat.min_eq_left hj] at ht
    rw [ht]

open Classical in
/-- Helper toward Definition 5.8: evaluate the tuple renewal sum at a
backward prefix given by an admissible passage suffix. -/
theorem uibhbot_negative_renewal_sum_at_passage (n m : ℕ) (s : List (Fin 3))
    (hm : 0 < m) (hmN : m ≤ n + 1) (hs : excursionPassage m s)
    (hslen : s.length = n + 1) :
    (∑' v : Fin (n + 1) → List (Fin 3),
      (if uibhbotBackwardWordPrefix (n + 1) v =
          uibhbotPassageBackwardPrefix (n + 1) s then (1 : ℝ≥0∞) else 0) *
        ∏ i : Fin (n + 1), (if IsStoppedExcursionWord (v i) then
          (1 / 3 : ℝ≥0∞) ^ (v i).length else 0)) =
      (m : ℝ≥0∞) * ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  rw [uibhbot_negative_renewal_sum_eq_passage_sum]
  have he : (∑' u : List (Fin 3),
      (if excursionPassage (n + 1) u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) *
        (if uibhbotPassageBackwardPrefix (n + 1) u =
          uibhbotPassageBackwardPrefix (n + 1) s then 1 else 0)) =
      ∑' u : List (Fin 3), if excursionPassage (n + 1) u ∧ s <:+ u then
        (1 / 3 : ℝ≥0∞) ^ u.length else 0 := by
    apply tsum_congr
    intro u
    by_cases hu : excursionPassage (n + 1) u
    · simp only [hu, ↓reduceIte, uibhbot_passage_backward_prefix_eq_iff_suffix
        (n + 1) s u hslen (uibhbot_passage_length_le hu)]
      by_cases hp : s <:+ u <;> simp [hp]
    · simp [hu]
  rw [he, uibhbot_passage_suffix_weight_sum (n + 1) m s hm hmN hs, hslen]
  simp only [one_div, pow_succ]
  calc
    3 * (m : ℝ≥0∞) * (3⁻¹ ^ n * 3⁻¹) =
        ((3 : ℝ≥0∞) * 3⁻¹) * ((m : ℝ≥0∞) * 3⁻¹ ^ n) := by ac_rfl
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      congr 1
      exact ENNReal.inv_pow.symm

private theorem passage_backward_prefix_step (N : ℕ) (u : List (Fin 3))
    (hlen : N ≤ u.length) (i : Fin N) :
    uibhbotPassageBackwardPrefix N u i.succ =
      uibhbotPassageBackwardPrefix N u i.castSucc -
        lazyTwoDimensionalStep (u.reverse[i.val]'(by simp only [List.length_reverse]; omega)) := by
  have hi : i.val < u.reverse.length := by simp only [List.length_reverse]; omega
  change -(((u.reverse.take (i.val + 1)).map lazyTwoDimensionalStep).sum) = _
  rw [List.take_succ_eq_append_getElem hi]
  simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  simp only [uibhbotPassageBackwardPrefix, Fin.val_castSucc]
  abel

/-- Helper toward Definition 5.8: exchange the source codes whose
negative increments become each other after swapping coordinates. -/
@[expose] def uibhbotReverseSwapCode (c : Fin 3) : Fin 3 :=
  if c = 0 then 1 else if c = 1 then 0 else 2

private theorem step_reverseSwapCode (c : Fin 3) :
    lazyTwoDimensionalStep (uibhbotReverseSwapCode c) =
      (-lazyTwoDimensionalStep c).swap := by
  fin_cases c <;> norm_num [uibhbotReverseSwapCode]

/-- Helper toward Definition 5.8: the exact shifted source step-word
prefix is the backward integration of a finite suffix word. -/
theorem uibhbot_shifted_prefix_as_backward_word (n : ℕ) (a : Fin n → Fin 3) :
    ∃ s : List (Fin 3), s.length = n + 1 ∧
      uibhbotPassageBackwardPrefix (n + 1) s =
        uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) := by
  let b : Fin (n + 1) → Fin 3 := Fin.cons 0 (fun i => uibhbotReverseSwapCode (a i))
  let s := (List.ofFn b).reverse
  have hlen : s.length = n + 1 := by simp [s]
  have hqstep (i : Fin (n + 1)) :
      uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) i.succ =
        uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) i.castSucc -
          lazyTwoDimensionalStep (b i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [uibhbotShiftedConditionedPrefix, lazyTwoDimensionalPrefix_zero, b]
    · change (lazyTwoDimensionalPrefix 0 0 a j.succ).swap + (1, 0) =
        (lazyTwoDimensionalPrefix 0 0 a j.castSucc).swap + (1, 0) -
          lazyTwoDimensionalStep (uibhbotReverseSwapCode (a j))
      rw [lazyTwoDimensionalPrefix_succ, step_reverseSwapCode]
      apply Prod.ext <;> simp [add_assoc, add_comm]
  refine ⟨s, hlen, ?_⟩
  funext j
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih =>
      rw [passage_backward_prefix_step (n + 1) s hlen.ge i, ih, hqstep]
      have he : s.reverse[i.val]'(by simp only [List.length_reverse, hlen]; omega) = b i := by
        simp only [s, List.reverse_reverse, List.getElem_ofFn]
      rw [he]

/-- Helper toward Definition 5.8: every backward passage prefix has
the exact source step-word representation used in the target density. -/
theorem uibhbot_passage_backward_prefix_in_shifted_range (n : ℕ)
    (u : List (Fin 3)) (hu : excursionPassage (n + 1) u) :
    ∃ a : Fin n → Fin 3, uibhbotShiftedConditionedPrefix n
      (lazyTwoDimensionalPrefix 0 0 a) = uibhbotPassageBackwardPrefix (n + 1) u := by
  let q := uibhbotPassageBackwardPrefix (n + 1) u
  let p : Fin (n + 1) → ℤ × ℤ := fun j => (q j.succ - (1, 0)).swap
  have hlen := uibhbot_passage_length_le hu
  have hne : u ≠ [] := by
    intro he
    have := hu.1
    simp [he] at this
  have hfirst : q (1 : Fin (n + 2)) = (1, 0) := by
    change -(((u.reverse.take 1).map lazyTwoDimensionalStep).sum) = _
    rw [List.take_one]
    simp [List.head?_reverse, List.getLast?_eq_some_getLast hne,
      passage_last_zero hu hne]
  have hp : p ∈ Set.range (@lazyTwoDimensionalPrefix n 0 0) := by
    apply (mem_range_lazyTwoDimensionalPrefix_iff 0 0 p).mpr
    refine ⟨?_, fun i => ?_⟩
    · change (q (1 : Fin (n + 2)) - (1, 0)).swap = (0, 0)
      rw [hfirst]
      rfl
    · let c := u.reverse[i.val + 1]'(by simp only [List.length_reverse]; omega)
      refine ⟨uibhbotReverseSwapCode c, ?_⟩
      have hs := passage_backward_prefix_step (n + 1) u hlen i.succ
      change q i.succ.succ = q i.succ.castSucc - lazyTwoDimensionalStep c at hs
      change (q i.succ.succ - (1, 0)).swap =
        (q i.castSucc.succ - (1, 0)).swap +
          lazyTwoDimensionalStep (uibhbotReverseSwapCode c)
      rw [hs, step_reverseSwapCode]
      apply Prod.ext <;> simp <;> omega
  obtain ⟨a, ha⟩ := hp
  refine ⟨a, ?_⟩
  funext j
  refine Fin.cases rfl (fun i => ?_) j
  change (lazyTwoDimensionalPrefix 0 0 a i).swap + (1, 0) = q i.succ
  rw [ha]
  change (q i.succ - (1, 0)).swap.swap + (1, 0) = q i.succ
  simp

/-- Helper toward Definition 5.8: positivity of the entire finite backward
prefix is exactly the strict first-passage constraint for its suffix word. -/
theorem uibhbot_passage_of_backward_prefix_positive (N : ℕ) (s : List (Fin 3))
    (hN : 0 < N) (hlen : s.length = N)
    (hp : ∀ j : Fin N, 1 ≤ (uibhbotPassageBackwardPrefix N s j.succ).1) :
    ∃ m : ℕ, 0 < m ∧ m ≤ N ∧ excursionPassage m s ∧
      (uibhbotPassageBackwardPrefix N s (Fin.last N)).1 = (m : ℤ) := by
  have hlast : 1 ≤ (uibhbotPassageBackwardPrefix N s (Fin.last N)).1 := by
    have he : (⟨N - 1, by omega⟩ : Fin N).succ = Fin.last N := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    simpa only [he] using hp ⟨N - 1, by omega⟩
  let m := (uibhbotPassageBackwardPrefix N s (Fin.last N)).1.toNat
  have hme : (m : ℤ) = (uibhbotPassageBackwardPrefix N s (Fin.last N)).1 :=
    Int.toNat_of_nonneg (by omega)
  have hend : ((s.map lazyTwoDimensionalStep).sum).1 = -(m : ℤ) := by
    have ht : s.reverse.take N = s.reverse :=
      List.take_of_length_le (by simpa only [List.length_reverse, hlen] using le_refl N)
    change (m : ℤ) = -(((s.reverse.take N).map lazyTwoDimensionalStep).sum).1 at hme
    rw [ht, List.map_reverse, List.sum_reverse] at hme
    omega
  have hbound := fst_sum_ge_neg_length s
  refine ⟨m, by omega, by omega, ⟨by omega, hend, ?_⟩, hme.symm⟩
  intro i hi
  have hpi := hp ⟨N - i - 1, by omega⟩
  change 1 ≤ -(((s.reverse.take (N - i - 1 + 1)).map lazyTwoDimensionalStep).sum).1 at hpi
  rw [fst_reverse_take, hend] at hpi
  have hi' : s.length - (N - i - 1 + 1) = i := by omega
  rw [hi'] at hpi
  omega

open Classical in
/-- Helper toward Definition 5.8: the exact all-horizon stopped-word
renewal sum, with the complete source step-word and positivity constraints.
The passage-suffix decomposition proves the endpoint multiplicity; no
law identity or independence claim is assumed. -/
theorem uibhbot_negative_renewal_sum
    (n : ℕ) (q : Fin (n + 2) → ℤ × ℤ) :
    (∑' v : Fin (n + 1) → List (Fin 3),
      (if uibhbotBackwardWordPrefix (n + 1) v = q
        then (1 : ℝ≥0∞) else 0) *
        ∏ i : Fin (n + 1),
          (if IsStoppedExcursionWord (v i) then
            (1 / 3 : ℝ≥0∞) ^ (v i).length else 0)) =
    if (∃ a : Fin n → Fin 3,
        uibhbotShiftedConditionedPrefix n
          (lazyTwoDimensionalPrefix 0 0 a) = q) ∧
        (∀ j : Fin (n + 1), 1 ≤ (q j.succ).1) then
      ENNReal.ofReal ((q (Fin.last (n + 1))).1 : ℝ) *
        ((3 : ℝ≥0∞) ^ n)⁻¹
    else 0 := by
  classical
  by_cases had : (∃ a : Fin n → Fin 3,
      uibhbotShiftedConditionedPrefix n (lazyTwoDimensionalPrefix 0 0 a) = q) ∧
      ∀ j : Fin (n + 1), 1 ≤ (q j.succ).1
  · obtain ⟨⟨a, ha⟩, hp⟩ := had
    obtain ⟨s, hslen, hsq⟩ := uibhbot_shifted_prefix_as_backward_word n a
    have heq : uibhbotPassageBackwardPrefix (n + 1) s = q := hsq.trans ha
    have hpos : ∀ j : Fin (n + 1),
        1 ≤ (uibhbotPassageBackwardPrefix (n + 1) s j.succ).1 := by
      rwa [heq]
    obtain ⟨m, hm, hmN, hs, hend⟩ :=
      uibhbot_passage_of_backward_prefix_positive (n + 1) s (by omega) hslen hpos
    have heval := uibhbot_negative_renewal_sum_at_passage n m s hm hmN hs hslen
    rw [heq] at heval hend
    rw [ite_eq_left ⟨⟨a, ha⟩, hp⟩, heval, hend]
    simp
  · rw [ite_eq_right had, uibhbot_negative_renewal_sum_eq_passage_sum]
    apply tsum_eq_zero_iff.mpr
    intro u
    by_cases hu : excursionPassage (n + 1) u
    · have hnot : uibhbotPassageBackwardPrefix (n + 1) u ≠ q := by
        intro he
        apply had
        constructor
        · obtain ⟨a, ha⟩ := uibhbot_passage_backward_prefix_in_shifted_range n u hu
          exact ⟨a, ha.trans he⟩
        · intro j
          rw [← he]
          exact uibhbot_passage_backward_prefix_positive hu j
      simp only [hnot, ↓reduceIte, mul_zero]
    · simp only [hu, ↓reduceIte, zero_mul]

/-- Helper toward Definition 5.8: the whole negative-time concatenated
path has the shifted, coordinate-swapped R-conditioned path law. -/
theorem uibhbot_negative_pathLaw_eq_rConditioned :
    uibhbotWordFamilyLaw.map
        (fun w => fun n : ℕ => uibhbotConcatWalk w (-(n : ℤ))) =
      (rConditionedPathLaw 0 0).map
        (fun p => fun n : ℕ => if n = 0 then (0, 0)
          else (p (n - 1)).swap + (1, 0)) := by
  exact uibhbot_negative_path_law_iff_renewal_sum.mpr uibhbot_negative_renewal_sum

end DirectedDistances.RandomWalk
end
