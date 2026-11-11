/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConeProbLower
public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefixRange

/-! # Finite word counts for the cone endpoint event

Finite-word reformulation of the event `E_n` in `lem-cone-prob-lower` -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- The literal translated cone endpoint event `E_n` of `lem-cone-prob-lower` -/
@[expose] def coneEvent (l y : ℤ) (n : ℕ) : Set (ℕ → Fin 3) :=
  {ω : ℕ → Fin 3 |
    (∀ j ≤ n, 0 ≤ ((l, y) + codeWalk ω j).1 ∧
      0 ≤ ((l, y) + codeWalk ω j).2) ∧
    (l, y) + codeWalk ω n = (0, 0)}

/-- The finite-word cone endpoint predicate from a natural-number start for -/
@[expose] def coneWordGood {n : ℕ} (x y : ℕ) (w : Fin n → Fin 3) : Prop :=
  (∀ j : Fin (n + 1),
    0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ) w j).1 ∧
      0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ) w j).2) ∧
  lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ) w (Fin.last n) = (0, 0)

/-- The number of length-`n` source words whose translated path stays in the
closed quadrant at every prefix and ends at the origin. This is the finite
word count reformulation of `E_n` in `lem-cone-prob-lower` -/
@[expose] noncomputable def coneWordCount (n x y : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.univ : Finset (Fin n → Fin 3)).filter (coneWordGood x y)).card

private theorem uniform_map_tailWord (N : ℕ) :
    iidCodeMeasure.map (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1)) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3)) := by
  classical
  have hf : (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1)) =
      (fun q : Fin (N + 1) → Fin 3 => fun i : Fin N => q i.succ) ∘
        (fun ω : ℕ → Fin 3 => fun j : Fin (N + 1) => ω j.val) := by
    funext ω i
    rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), iidCodeMeasure_map_prefix]
  have hmp := measurePreserving_piFinSuccAbove
    (fun j : Fin (N + 1) =>
      if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure) 0
  have hsnd : (fun q : Fin (N + 1) → Fin 3 => fun i : Fin N => q i.succ) =
      Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (N + 1) => Fin 3) 0) := by
    funext q i
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [hsnd, ← Measure.map_map measurable_snd (MeasurableEquiv.measurable _),
    hmp.map_eq, Measure.map_snd_prod]
  simp only [Fin.val_zero, ite_true, measure_univ, one_smul, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Fin.succAbove_zero]
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton, Measure.uniformOfFinset_apply_singleton]
  simp [uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton, ENNReal.inv_pow]

private theorem cone_prefix_word_eq (n : ℕ) (x y : ℤ) (ω : ℕ → Fin 3)
    (j : Fin (n + 1)) :
    (x, y) + codeWalk ω j.val =
      lazyTwoDimensionalPrefix x y (fun i : Fin n => ω (i.val + 1)) j := by
  have hsum (f : Fin 3 → ℤ) :
      ∑ i ∈ Finset.range j.val, f (ω (i + 1)) =
        ∑ i : Fin n with i.val < j.val, f (ω (i.val + 1)) := by
    have hset : Finset.range j.val = (Finset.range n).filter (fun i => i < j.val) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    rw [hset, Finset.sum_filter, Finset.sum_filter,
      Fin.sum_univ_eq_sum_range (fun i => if i < j.val then f (ω (i + 1)) else 0) n]
  unfold codeWalk lazyTwoDimensionalPrefix
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.fst_sum]
    exact congrArg (fun z : ℤ => x + z) (hsum fun c => (lazyTwoDimensionalStep c).1)
  · simp only [Prod.snd_add, Prod.snd_sum]
    exact congrArg (fun z : ℤ => y + z) (hsum fun c => (lazyTwoDimensionalStep c).2)

/-- The probability of the source cone endpoint event is its finite word count
divided by the number `3^n` of equally likely code words. -/
theorem iidCodeMeasure_real_coneEvent (n x y : ℕ) :
    iidCodeMeasure.real (coneEvent (x : ℤ) (y : ℤ) n) =
      (coneWordCount n x y : ℝ) / 3 ^ n := by
  classical
  have hpre :
      (fun ω : ℕ → Fin 3 => fun i : Fin n => ω (i.val + 1)) ⁻¹'
          {w : Fin n → Fin 3 | coneWordGood x y w} = coneEvent (x : ℤ) (y : ℤ) n := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, coneEvent, coneWordGood]
    constructor
    · rintro ⟨hpath, hend⟩
      refine ⟨?_, ?_⟩
      · intro j hj
        let k : Fin (n + 1) := ⟨j, by omega⟩
        have h := hpath k
        rw [← cone_prefix_word_eq n (x : ℤ) (y : ℤ) ω k] at h
        simpa [k] using h
      · have h := hend
        rw [← cone_prefix_word_eq n (x : ℤ) (y : ℤ) ω (Fin.last n)] at h
        simpa using h
    · rintro ⟨hpath, hend⟩
      refine ⟨?_, ?_⟩
      · intro j
        have h := hpath j.val (by omega)
        rw [cone_prefix_word_eq n (x : ℤ) (y : ℤ) ω j] at h
        simpa using h
      · have h := hend
        have heq := cone_prefix_word_eq n (x : ℤ) (y : ℤ) ω (Fin.last n)
        have heq' : ((x : ℤ), (y : ℤ)) + codeWalk ω n =
            lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ)
              (fun i : Fin n => ω (i.val + 1)) (Fin.last n) := by
          simpa using heq
        rw [heq'] at h
        simpa using h
  have hmeas : Measurable (fun ω : ℕ → Fin 3 => fun i : Fin n => ω (i.val + 1)) := by
    fun_prop
  calc
    iidCodeMeasure.real (coneEvent (x : ℤ) (y : ℤ) n) =
        iidCodeMeasure.real (Set.preimage
          (fun ω : ℕ → Fin 3 => fun i : Fin n => ω (i.val + 1))
          {w : Fin n → Fin 3 | coneWordGood x y w}) := by rw [hpre]
    _ = (iidCodeMeasure.map
          (fun ω : ℕ → Fin 3 => fun i : Fin n => ω (i.val + 1))).real
          {w : Fin n → Fin 3 | coneWordGood x y w} :=
            (map_measureReal_apply hmeas (Set.to_countable _).measurableSet).symm
    _ = (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).real
          {w : Fin n → Fin 3 | coneWordGood x y w} := by rw [uniform_map_tailWord]
    _ = (coneWordCount n x y : ℝ) / 3 ^ n := by
      rw [Measure.real, Measure.uniformOfFinset_apply, ENNReal.toReal_div]
      simp only [Set.mem_ofPred_eq,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
        Nat.cast_ofNat, ENNReal.toReal_natCast, ENNReal.toReal_pow]
      have hcount :
          ((Finset.univ : Finset (Fin n → Fin 3)).filter
            (fun w => coneWordGood x y w)).card = coneWordCount n x y := by
        rfl
      rw [hcount, ENNReal.toReal_ofNat]

/-- The original `(l, 0)` event is the zero second-coordinate specialization
of the generalized finite word probability formula -/
theorem iidCodeMeasure_real_coneEvent_zero_snd (n x : ℕ) :
    iidCodeMeasure.real (coneEvent (x : ℤ) 0 n) =
      (coneWordCount n x 0 : ℝ) / 3 ^ n :=
  iidCodeMeasure_real_coneEvent n x 0

private theorem cone_prefix_cons {n : ℕ} (x y : ℤ) (c : Fin 3)
    (w : Fin n → Fin 3) (j : Fin (n + 1)) :
    lazyTwoDimensionalPrefix x y (Fin.cons c w) j.succ =
      (x, y) + lazyTwoDimensionalStep c + lazyTwoDimensionalPrefix 0 0 w j := by
  unfold lazyTwoDimensionalPrefix
  apply Prod.ext
  · simp only [Prod.fst_add, Finset.sum_filter,
      Fin.sum_univ_succ, Fin.val_succ, Fin.val_zero,
      Nat.zero_lt_succ, Fin.cons_zero, ite_true, Fin.cons_succ,
      Nat.add_lt_add_iff_right]
    ring
  · simp only [Prod.snd_add, Finset.sum_filter,
      Fin.sum_univ_succ, Fin.val_succ, Fin.val_zero,
      Nat.zero_lt_succ, Fin.cons_zero, ite_true, Fin.cons_succ,
      Nat.add_lt_add_iff_right]
    ring

private theorem cone_prefix_cons_zero_nat {n : ℕ} (x y : ℕ)
    (w : Fin n → Fin 3) (j : Fin (n + 1)) :
    lazyTwoDimensionalPrefix ((x + 1 : ℕ) : ℤ) (y : ℤ) (Fin.cons 0 w) j.succ =
      lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ) w j := by
  rw [cone_prefix_cons, lazyTwoDimensionalStep_zero]
  apply Prod.ext
  · simp only [lazyTwoDimensionalPrefix, Prod.fst_add]
    push_cast
    omega
  · simp only [lazyTwoDimensionalPrefix, Prod.snd_add]
    omega

private theorem cone_prefix_cons_one_nat {n : ℕ} (x y : ℕ)
    (w : Fin n → Fin 3) (j : Fin (n + 1)) :
    lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ) (Fin.cons 1 w) j.succ =
      lazyTwoDimensionalPrefix (x : ℤ) ((y + 1 : ℕ) : ℤ) w j := by
  rw [cone_prefix_cons, lazyTwoDimensionalStep_one]
  apply Prod.ext
  · simp only [lazyTwoDimensionalPrefix, Prod.fst_add]
    omega
  · simp only [lazyTwoDimensionalPrefix, Prod.snd_add]
    push_cast
    omega

private theorem cone_prefix_cons_two_nat {n : ℕ} (x y : ℕ)
    (w : Fin n → Fin 3) (j : Fin (n + 1)) :
    lazyTwoDimensionalPrefix (x : ℤ) ((y + 1 : ℕ) : ℤ) (Fin.cons 2 w) j.succ =
      lazyTwoDimensionalPrefix ((x + 1 : ℕ) : ℤ) (y : ℤ) w j := by
  rw [cone_prefix_cons, lazyTwoDimensionalStep_two]
  apply Prod.ext
  · simp only [lazyTwoDimensionalPrefix, Prod.fst_add]
    push_cast
    omega
  · simp only [lazyTwoDimensionalPrefix, Prod.snd_add]
    push_cast
    omega

private theorem coneWordGood_cons_of_prefix {n : ℕ} (x y x' y' : ℕ)
    (c : Fin 3) (w : Fin n → Fin 3)
    (hp : ∀ j : Fin (n + 1),
      lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ) (Fin.cons c w) j.succ =
        lazyTwoDimensionalPrefix (x' : ℤ) (y' : ℤ) w j) :
    coneWordGood x y (Fin.cons c w) ↔ coneWordGood x' y' w := by
  unfold coneWordGood
  constructor
  · rintro ⟨hpath, hend⟩
    refine ⟨?_, ?_⟩
    · intro j
      have h := hpath j.succ
      rw [hp j] at h
      exact h
    · have h := hend
      rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl, hp (Fin.last n)] at h
      exact h
  · rintro ⟨hpath, hend⟩
    refine ⟨?_, ?_⟩
    · intro j
      refine Fin.cases ?_ ?_ j
      · simp only [lazyTwoDimensionalPrefix_zero]
        exact ⟨by positivity, by positivity⟩
      · intro i
        have h := hpath i
        rw [hp i]
        exact h
    · rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl, hp (Fin.last n)]
      exact hend

private theorem coneWordGood_cons_zero (n x y : ℕ) (w : Fin n → Fin 3) :
    coneWordGood x y (Fin.cons 0 w) ↔
      0 < x ∧ coneWordGood (x - 1) y w := by
  by_cases hx : x = 0
  · subst x
    constructor
    · intro h
      let j : Fin (n + 1) := 0
      have hfirst := (h.1 j.succ).1
      rw [cone_prefix_cons, lazyTwoDimensionalStep_zero,
        lazyTwoDimensionalPrefix_zero] at hfirst
      norm_num at hfirst
    · rintro ⟨hx, _⟩
      omega
  · have hxpos : 0 < x := by omega
    have hxEq : (x : ℤ) = ((x - 1) + 1 : ℕ) := by exact_mod_cast (show x = (x - 1) + 1 by omega)
    have hp (j : Fin (n + 1)) :
        lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ) (Fin.cons 0 w) j.succ =
          lazyTwoDimensionalPrefix ((x - 1 : ℕ) : ℤ) (y : ℤ) w j := by
      rw [hxEq]
      exact cone_prefix_cons_zero_nat (x - 1) y w j
    have hg := coneWordGood_cons_of_prefix x y (x - 1) y 0 w hp
    exact ⟨fun h => ⟨hxpos, hg.mp h⟩, fun h => hg.mpr h.2⟩

private theorem coneWordGood_cons_one (n x y : ℕ) (w : Fin n → Fin 3) :
    coneWordGood x y (Fin.cons 1 w) ↔ coneWordGood x (y + 1) w := by
  apply coneWordGood_cons_of_prefix x y x (y + 1) 1 w
  intro j
  exact cone_prefix_cons_one_nat x y w j

private theorem coneWordGood_cons_two (n x y : ℕ) (w : Fin n → Fin 3) :
    coneWordGood x y (Fin.cons 2 w) ↔
      0 < y ∧ coneWordGood (x + 1) (y - 1) w := by
  by_cases hy : y = 0
  · subst y
    constructor
    · intro h
      let j : Fin (n + 1) := 0
      have hfirst := (h.1 j.succ).2
      rw [cone_prefix_cons, lazyTwoDimensionalStep_two,
        lazyTwoDimensionalPrefix_zero] at hfirst
      norm_num at hfirst
    · rintro ⟨hy, _⟩
      omega
  · have hypos : 0 < y := by omega
    have hyEq : (y : ℤ) = ((y - 1) + 1 : ℕ) := by exact_mod_cast (show y = (y - 1) + 1 by omega)
    have hp (j : Fin (n + 1)) :
        lazyTwoDimensionalPrefix (x : ℤ) (y : ℤ) (Fin.cons 2 w) j.succ =
          lazyTwoDimensionalPrefix ((x + 1 : ℕ) : ℤ) ((y - 1 : ℕ) : ℤ) w j := by
      rw [hyEq]
      exact cone_prefix_cons_two_nat x (y - 1) w j
    have hg := coneWordGood_cons_of_prefix x y (x + 1) (y - 1) 2 w hp
    exact ⟨fun h => ⟨hypos, hg.mp h⟩, fun h => hg.mpr h.2⟩

private theorem coneWordCount_eq_sum (n x y : ℕ) :
    coneWordCount n x y =
      ∑ w : Fin n → Fin 3, if coneWordGood x y w then 1 else 0 := by
  classical
  unfold coneWordCount
  exact (Finset.sum_boole (coneWordGood x y) Finset.univ).symm

private theorem coneWordGood_cons_zero_sum (n x y : ℕ) :
    (∑ w : Fin n → Fin 3,
      if coneWordGood x y (Fin.cons 0 w) then 1 else 0) =
        if 0 < x then coneWordCount n (x - 1) y else 0 := by
  classical
  simp_rw [coneWordGood_cons_zero]
  rw [coneWordCount_eq_sum n (x - 1) y]
  by_cases hx : 0 < x <;> simp [hx]

private theorem coneWordGood_cons_one_sum (n x y : ℕ) :
    (∑ w : Fin n → Fin 3,
      if coneWordGood x y (Fin.cons 1 w) then 1 else 0) =
        coneWordCount n x (y + 1) := by
  classical
  simp_rw [coneWordGood_cons_one]
  rw [coneWordCount_eq_sum n x (y + 1)]

private theorem coneWordGood_cons_two_sum (n x y : ℕ) :
    (∑ w : Fin n → Fin 3,
      if coneWordGood x y (Fin.cons 2 w) then 1 else 0) =
        if 0 < y then coneWordCount n (x + 1) (y - 1) else 0 := by
  classical
  simp_rw [coneWordGood_cons_two]
  rw [coneWordCount_eq_sum n (x + 1) (y - 1)]
  by_cases hy : 0 < y <;> simp [hy]

/-- At horizon zero the only successful word is the empty word from the origin. -/
theorem coneWordCount_zero (x y : ℕ) :
    coneWordCount 0 x y = if x = 0 ∧ y = 0 then 1 else 0 := by
  classical
  unfold coneWordCount coneWordGood
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [lazyTwoDimensionalPrefix_zero, hx, hy]

/-- First-step decomposition of the finite cone endpoint word count, with
the literal source-step order `(-1,0)`, `(0,1)`, `(1,-1)`. -/
theorem coneWordCount_succ (n x y : ℕ) :
    coneWordCount (n + 1) x y =
      (if 0 < x then coneWordCount n (x - 1) y else 0) +
        coneWordCount n x (y + 1) +
        (if 0 < y then coneWordCount n (x + 1) (y - 1) else 0) := by
  classical
  rw [coneWordCount_eq_sum (n + 1) x y]
  have he := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3))
    (fun p : Fin 3 × (Fin n → Fin 3) =>
      if coneWordGood x y (Fin.cons p.1 p.2) then 1 else 0)
    (fun w => if coneWordGood x y w then 1 else 0) (fun _ => rfl)
  rw [← he, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [coneWordGood_cons_zero_sum, coneWordGood_cons_one_sum,
    coneWordGood_cons_two_sum]
  exact (add_assoc _ _ _).symm
end DirectedDistances.RandomWalk
