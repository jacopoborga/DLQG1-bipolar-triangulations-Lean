/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ShiftedWindowRNBound
public import DirectedDistances.RandomWalk.ShiftedConditionedWindowAfterHit
public import DirectedDistances.PaperProofs.Section7.BoltzmannLDPLowerSegment
public import DirectedDistances.PaperProofs.Section7.BoltzmannLDPLowerAssembly
-- Proof-only access to the assembly proposition and event bodies.
import all DirectedDistances.PaperProofs.Section7.BoltzmannLDPLowerAssembly
import DirectedDistances.RandomWalk.BoltzmannLowerInput
import DirectedDistances.Paper.Section1.CellLDP
import DirectedDistances.RandomWalk.IIDWalkMaximalTailBound
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Corrected shifted-window estimates toward Lemma 7.11

Helpers toward Lemma 7.11 (`lem-boltzmann-ldp-lower`,
`(L_N + ℓ + 1)/(ℓ + 1)`, as required by translating the uncentered RN law.
The printed centered density omits `+ℓ`; see the proof-local finding

The second moment is proved locally: the concurrent moment module had no -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Filter DirectedDistances.RandomWalk
open DirectedDistances.KMSW DirectedDistances.PlanarMap Quiver
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open scoped ENNReal BigOperators

private noncomputable def lazyEndpointSquareSum (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin 3, (lazyWordValues w (Fin.last n) : ℝ) ^ 2


private theorem lazyEndpointSquareSum_succ (n : ℕ) :
    lazyEndpointSquareSum (n + 1) =
      3 * lazyEndpointSquareSum n + 2 * (3 : ℝ) ^ n := by
  classical
  unfold lazyEndpointSquareSum
  have hlast (a : Fin 3) (w : Fin n → Fin 3) :
      lazyWordValues (Fin.cons a w) (Fin.last (n + 1)) =
        ((a : ℤ) - 1) + lazyWordValues w (Fin.last n) := by
    simpa only [show Fin.last (n + 1) = (Fin.last n).succ from rfl] using
      lazyWordValues_cons a w (Fin.last n)
  have he := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3))
    (fun p : Fin 3 × (Fin n → Fin 3) =>
      (lazyWordValues (Fin.cons p.1 p.2) (Fin.last (n + 1)) : ℝ) ^ 2)
    (fun w => (lazyWordValues w (Fin.last (n + 1)) : ℝ) ^ 2) (fun _ => rfl)
  rw [← he, Fintype.sum_prod_type]
  simp_rw [hlast, Int.cast_add, Int.cast_sub, Int.cast_one]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Int.cast_ofNat, Int.cast_neg, Int.cast_one, sub_neg_eq_add]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [zero_add]
  simp_rw [show ∀ x : ℝ, (-1 + x) ^ 2 + (x ^ 2 + (1 + x) ^ 2) =
    3 * x ^ 2 + 2 by intro x; ring]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const]
  simp only [nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat]
  ring


private theorem lazyEndpointSquareAverage (n : ℕ) :
    (1 / 3 : ℝ) ^ n * lazyEndpointSquareSum n = (2 / 3 : ℝ) * n := by
  induction n with
  | zero => simp [lazyEndpointSquareSum, lazyWordValues_zero]
  | succ n ih =>
      rw [show n + 1 = (n + 1) from rfl, lazyEndpointSquareSum_succ]
      simp only [pow_succ]
      have hp : (1 / 3 : ℝ) ^ n * (3 : ℝ) ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (1 / 3 : ℝ) ^ n * (1 / 3 : ℝ) *
            (3 * lazyEndpointSquareSum n + 2 * (3 : ℝ) ^ n) =
            (1 / 3 : ℝ) ^ n * lazyEndpointSquareSum n +
              (2 / 3 : ℝ) * ((1 / 3 : ℝ) ^ n * (3 : ℝ) ^ n) := by ring
        _ = (2 / 3 : ℝ) * n + 2 / 3 := by rw [ih, hp]; ring
        _ = (2 / 3 : ℝ) * ((n + 1 : ℕ) : ℝ) := by push_cast; ring

private theorem uniform_lazy_word_isProbability (N : ℕ) :
    IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))) := by
  refine ⟨?_⟩
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_self (by positivity) (by norm_num)


private theorem integral_uniform_lazyEndpoint_square (n : ℕ) :
    (∫ w, (lazyWordValues w (Fin.last n) : ℝ) ^ 2 ∂
      Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))) =
      (2 / 3 : ℝ) * n := by
  classical
  let := uniform_lazy_word_isProbability n
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real, Measure.uniformOfFinset_apply_singleton,
    Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, ENNReal.toReal_inv, ENNReal.toReal_pow,
    Nat.cast_ofNat, ENNReal.toReal_ofNat, smul_eq_mul]
  rw [← Finset.mul_sum]
  simpa only [lazyEndpointSquareSum, one_div, inv_pow] using
    lazyEndpointSquareAverage n


private theorem lazyPrefixLaw_isProbability (N : ℕ) :
    IsProbabilityMeasure (lazyPrefixLaw N) := by
  let : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))) := by
    refine ⟨?_⟩
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_self (by positivity) (by norm_num)
  change IsProbabilityMeasure
    ((Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))).map
      (lazyTwoDimensionalPrefix 0 0))
  refine ⟨?_⟩
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  exact measure_univ


/-- Helper toward Lemma 7.11; not a paper result. The lazy prefix endpoint
has second moment `2N/3`; the corrected-density finding is recorded in -/
theorem ldpLower_lazyPrefix_secondMoment (N : ℕ) :
    ∫ q, (shiftedWindowL q) ^ 2 ∂lazyPrefixLaw N = (2 / 3 : ℝ) * N := by
  rw [lazyPrefixLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simpa only [shiftedWindowL, lazyTwoDimensionalPrefix_fst,
    Int.cast_zero, zero_add] using integral_uniform_lazyEndpoint_square N

private theorem integral_uniform_affineSquare_le (ℓ N : ℕ) :
    (∫ w, (1 + (lazyWordValues w (Fin.last N) : ℝ) /
      ((ℓ : ℝ) + 1)) ^ 2 ∂
      Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))) ≤
      2 + 2 * ((2 / 3 : ℝ) * N) / ((ℓ : ℝ) + 1) ^ 2 := by
  let := uniform_lazy_word_isProbability N
  let d : ℝ := (ℓ : ℝ) + 1
  have hd : d ≠ 0 := by dsimp [d]; positivity
  calc
    _ ≤ ∫ w, (2 + (2 / d ^ 2) *
        (lazyWordValues w (Fin.last N) : ℝ) ^ 2) ∂
        Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3)) := by
      apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
      intro w
      change (1 + (lazyWordValues w (Fin.last N) : ℝ) / d) ^ 2 ≤ _
      have he : (2 / d ^ 2) * (lazyWordValues w (Fin.last N) : ℝ) ^ 2 =
          2 * ((lazyWordValues w (Fin.last N) : ℝ) / d) ^ 2 := by
        field_simp
      dsimp only
      rw [he]
      nlinarith only [sq_nonneg (1 - (lazyWordValues w (Fin.last N) : ℝ) / d)]
    _ = _ := by
      rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
        integral_const_mul, integral_uniform_lazyEndpoint_square]
      simp only [integral_const, measureReal_def, measure_univ,
        ENNReal.toReal_one, one_smul]
      dsimp [d]
      ring

private theorem lintegral_affineSquare_le (ℓ N : ℕ) :
    ∫⁻ q, ENNReal.ofReal
        (1 + shiftedWindowL q / ((ℓ : ℝ) + 1)) ^ 2 ∂lazyPrefixLaw N ≤
      ENNReal.ofReal (2 + 2 * ((2 / 3 : ℝ) * N) / ((ℓ : ℝ) + 1) ^ 2) := by
  let := uniform_lazy_word_isProbability N
  rw [lazyPrefixLaw, lintegral_map (measurable_of_countable _)
    (measurable_of_countable _)]
  calc
    _ ≤ ∫⁻ w, ENNReal.ofReal ((1 + shiftedWindowL
        (lazyTwoDimensionalPrefix 0 0 w) / ((ℓ : ℝ) + 1)) ^ 2) ∂
        Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3)) := by
      apply lintegral_mono
      intro w
      let a : ℝ := 1 + shiftedWindowL (lazyTwoDimensionalPrefix 0 0 w) / ((ℓ : ℝ) + 1)
      change ENNReal.ofReal a ^ 2 ≤ ENNReal.ofReal (a ^ 2)
      by_cases ha : 0 ≤ a
      · rw [ENNReal.ofReal_pow ha]
      · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge ha), zero_pow (by omega : 2 ≠ 0)]
        exact bot_le
    _ = ENNReal.ofReal (∫ w, (1 + shiftedWindowL
        (lazyTwoDimensionalPrefix 0 0 w) / ((ℓ : ℝ) + 1)) ^ 2 ∂
        Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite)
        (Eventually.of_forall fun _ => sq_nonneg _)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [shiftedWindowL, lazyTwoDimensionalPrefix_fst, Int.cast_zero,
        zero_add] using integral_uniform_affineSquare_le ℓ N

/-- Helper toward Lemma 7.11; not a paper result. Cauchy–Schwarz for the
corrected shifted RN weight, with a locally proved second-moment bound.
The `+ℓ` correction is the proof-local density finding recorded in -/
theorem ldpLower_shiftedWeight_event_le (ℓ N : ℕ)
    (B : Set (Fin (N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    (∫⁻ q, shiftedWindowWeight ℓ q * B.indicator (fun _ => (1 : ℝ≥0∞)) q
        ∂lazyPrefixLaw N) ≤
      (ENNReal.ofReal (2 + 2 * ((2 / 3 : ℝ) * N) / ((ℓ : ℝ) + 1) ^ 2)) ^
        (1 / 2 : ℝ) * (lazyPrefixLaw N B) ^ (1 / 2 : ℝ) := by
  classical
  let μ := lazyPrefixLaw N
  let F : (Fin (N + 1) → ℤ × ℤ) → ℝ≥0∞ :=
    B.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hB
  have hweight : Measurable
      (fun q : Fin (N + 1) → ℤ × ℤ => shiftedWindowWeight ℓ q) :=
    measurable_of_countable _
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    hweight.aemeasurable hF.aemeasurable
  have hFtwo : ∫⁻ q, F q ^ (2 : ℝ) ∂μ = μ B := by
    rw [show (fun q => F q ^ (2 : ℝ)) = B.indicator (fun _ => (1 : ℝ≥0∞)) by
      funext q
      by_cases hq : q ∈ B <;> simp [F, hq]]
    rw [lintegral_indicator_const hB]
    simp only [one_mul]
  have hweightPoint (q : Fin (N + 1) → ℤ × ℤ) :
      shiftedWindowWeight ℓ q ^ (2 : ℝ) ≤
        ENNReal.ofReal (1 + shiftedWindowL q / ((ℓ : ℝ) + 1)) ^ 2 := by
    rw [ENNReal.rpow_two]
    by_cases hq : ∀ j, -(ℓ : ℤ) ≤ (q j).1
    · have hreal :
          (((ℓ : ℝ) + shiftedWindowL q + 1) / ((ℓ : ℝ) + 1)) =
            1 + shiftedWindowL q / ((ℓ : ℝ) + 1) := by
        have hd : (ℓ : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hd]
        ring
      simp only [shiftedWindowWeight, ite_eq_left hq, hreal, le_refl]
    · simp only [shiftedWindowWeight, ite_eq_right hq, zero_pow (by omega : 2 ≠ 0)]
      exact bot_le
  have hweightSq :
      (∫⁻ q, shiftedWindowWeight ℓ q ^ (2 : ℝ) ∂μ) ≤
        ENNReal.ofReal (2 + 2 * ((2 / 3 : ℝ) * N) / ((ℓ : ℝ) + 1) ^ 2) :=
    (lintegral_mono hweightPoint).trans (lintegral_affineSquare_le ℓ N)
  calc
    _ ≤ (∫⁻ q, shiftedWindowWeight ℓ q ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ q, F q ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
      simpa only [F, μ, Pi.mul_apply] using hholder
    _ ≤ _ := by
      rw [hFtwo]
      exact mul_le_mul_of_nonneg_right
        (ENNReal.rpow_le_rpow hweightSq (by norm_num)) (by positivity)

/-- Helper toward Lemma 7.11; not a paper result. The bad-window probability
on one first-hit height slice is bounded by its slice mass times the
corrected-density Cauchy–Schwarz factor. This uses exactly the conditioned
vector-path law, with no conditional-probability existence premise. -/
theorem ldpLower_postFirstHit_slice_le (x : ℕ) (y : ℤ) (k ℓ N : ℕ)
    (B : Set (Fin (N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    (((conditionedVectorPathLaw x y).restrict
      {p | conditionedSecondCoordinateFirstHit k p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit k p).toNat).1 = (ℓ : ℤ)}).map
      (fun p => fun j : Fin (N + 1) =>
        p ((conditionedSecondCoordinateFirstHit k p).toNat + j.val) -
          p (conditionedSecondCoordinateFirstHit k p).toNat)) B ≤
    (conditionedVectorPathLaw x y
      {p | conditionedSecondCoordinateFirstHit k p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit k p).toNat).1 = (ℓ : ℤ)}) *
      ((ENNReal.ofReal (2 + 2 * ((2 / 3 : ℝ) * N) / ((ℓ : ℝ) + 1) ^ 2)) ^
        (1 / 2 : ℝ) * (lazyPrefixLaw N B) ^ (1 / 2 : ℝ)) := by
  rw [conditionedVectorPathLaw_postFirstHit_window_law, Measure.smul_apply,
    smul_eq_mul]
  change _ * (lazyPrefixLaw N).withDensity (shiftedWindowWeight ℓ) B ≤ _
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [withDensity_apply _ hB]
  have heq : (fun q => shiftedWindowWeight ℓ q * B.indicator
      (fun _ => (1 : ℝ≥0∞)) q) = B.indicator (shiftedWindowWeight ℓ) := by
    funext q
    by_cases hq : q ∈ B <;> simp [hq]
  have h := ldpLower_shiftedWeight_event_le ℓ N B hB
  rw [heq, lintegral_indicator hB] at h
  exact h

private theorem shifted_moment_factor_le (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (r ℓ N : ℕ) (hℓ : c * (r : ℝ) ≤ (ℓ : ℝ))
    (hN : (N : ℝ) ≤ (r : ℝ) ^ 2 / C) :
    2 + 2 * ((2 / 3 : ℝ) * N) / ((ℓ : ℝ) + 1) ^ 2 ≤
      2 + 4 / (3 * C * c ^ 2) := by
  have hd : 0 < (ℓ : ℝ) + 1 := by positivity
  have hsq : (c * (r : ℝ)) ^ 2 ≤ ((ℓ : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hℓ]) 2
  have hNC : (N : ℝ) * C ≤ (r : ℝ) ^ 2 := (le_div_iff₀ hC).mp hN
  have hfrac : (N : ℝ) / ((ℓ : ℝ) + 1) ^ 2 ≤ 1 / (C * c ^ 2) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) (mul_pos hC (sq_pos_of_pos hc))).mpr
    have hx := mul_le_mul_of_nonneg_right hNC (sq_nonneg c)
    nlinarith only [hx, hsq]
  calc
    _ = 2 + (4 / 3 : ℝ) * ((N : ℝ) / ((ℓ : ℝ) + 1) ^ 2) := by ring
    _ ≤ 2 + (4 / 3 : ℝ) * (1 / (C * c ^ 2)) := by linarith only [hfrac]
    _ = _ := by field_simp

/-- Helper toward Lemma 7.11; not a paper result. Uniform Cauchy–Schwarz
control on a fixed first-hit height `ℓ ≥ c r`, under the exact conditioned
path law used by the stopped Boltzmann carriers. The bad window may be
any measurable finite-prefix event. The corrected density includes `+ℓ`, -/
theorem ldpLower_postHalfHit_slice_le_of_height (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C) (r ℓ N : ℕ)
    (hℓ : c * (r : ℝ) ≤ (ℓ : ℝ))
    (hN : (N : ℝ) ≤ (r : ℝ) ^ 2 / C)
    (B : Set (Fin (N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    (((conditionedVectorPathLaw 0 0).restrict
      {p | conditionedSecondCoordinateFirstHit (r / 2) p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat).1 = (ℓ : ℤ)}).map
      (fun p => fun j : Fin (N + 1) =>
        p ((conditionedSecondCoordinateFirstHit (r / 2) p).toNat + j.val) -
          p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat)) B ≤
    (conditionedVectorPathLaw 0 0
      {p | conditionedSecondCoordinateFirstHit (r / 2) p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat).1 = (ℓ : ℤ)}) *
      ((ENNReal.ofReal (2 + 4 / (3 * C * c ^ 2))) ^ (1 / 2 : ℝ) *
        (lazyPrefixLaw N B) ^ (1 / 2 : ℝ)) := by
  refine (ldpLower_postFirstHit_slice_le 0 0 (r / 2) ℓ N B hB).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
    (shifted_moment_factor_le c C hc hC r ℓ N hℓ hN)) (by norm_num)

private theorem measurable_hitWindow (k N : ℕ) :
    Measurable (fun p : ℕ → ℤ × ℤ => fun j : Fin (N + 1) =>
      p ((conditionedSecondCoordinateFirstHit k p).toNat + j.val) -
        p (conditionedSecondCoordinateFirstHit k p).toNat) := by
  have ht : Measurable (fun p : ℕ → ℤ × ℤ =>
      (conditionedSecondCoordinateFirstHit k p).toNat) := by
    apply (measurable_of_countable ENat.toNat).comp
    apply ENat.measurable_iff.mpr
    intro n
    obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp
      (measurableSet_conditionedVectorPast_firstHit_eq k n)
    change MeasurableSet {p | conditionedSecondCoordinateFirstHit k p = (n : ℕ∞)}
    rw [← hpre]
    exact hS.preimage (measurable_conditionedVectorPrefix n)
  have he (n : ℕ) : Measurable (fun p : ℕ → ℤ × ℤ =>
      p ((conditionedSecondCoordinateFirstHit k p).toNat + n)) := by
    have heval : Measurable (fun z : (ℕ → ℤ × ℤ) × ℕ => z.1 (z.2 + n)) :=
      measurable_from_prod_countable_left fun m => measurable_pi_apply (m + n)
    exact heval.comp (measurable_id.prodMk ht)
  exact .of_eval fun j => (he j.val).sub (by simpa only [Nat.add_zero] using he 0)

/-- Helper toward Lemma 7.11; not a paper result. The preceding height-slice
bound written as an event in the original conditioned path space, suitable
for summing the disjoint height slices. Uses the corrected `+ℓ` density; -/
theorem ldpLower_postHalfHit_badWindow_le (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C) (r ℓ N : ℕ)
    (hℓ : c * (r : ℝ) ≤ (ℓ : ℝ))
    (hN : (N : ℝ) ≤ (r : ℝ) ^ 2 / C)
    (B : Set (Fin (N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    conditionedVectorPathLaw 0 0
      {p | conditionedSecondCoordinateFirstHit (r / 2) p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat).1 = (ℓ : ℤ) ∧
        (fun j : Fin (N + 1) =>
          p ((conditionedSecondCoordinateFirstHit (r / 2) p).toNat + j.val) -
            p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat) ∈ B} ≤
    (conditionedVectorPathLaw 0 0
      {p | conditionedSecondCoordinateFirstHit (r / 2) p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat).1 = (ℓ : ℤ)}) *
      ((ENNReal.ofReal (2 + 4 / (3 * C * c ^ 2))) ^ (1 / 2 : ℝ) *
        (lazyPrefixLaw N B) ^ (1 / 2 : ℝ)) := by
  have h := ldpLower_postHalfHit_slice_le_of_height c C hc hC r ℓ N hℓ hN B hB
  rw [Measure.map_apply (measurable_hitWindow (r / 2) N) hB,
    Measure.restrict_apply (hB.preimage (measurable_hitWindow (r / 2) N))] at h
  convert h using 1
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  tauto

/-- Helper toward Lemma 7.11; not a paper result. The chance of hitting
`-⌈r/2⌉` at or before `⌊r²/C⌋` is bounded uniformly in the positive integer
radius, including when the floored time horizon is zero. Supports the
corrected-density argument recorded in -/
theorem ldpLower_cell_earlyHit_inclusive_probability (r : ℕ) (hr : 1 ≤ r)
    (C : ℝ) (hC : 0 < C) :
    iidCodeMeasure.real {ω | ∃ k : ℕ, k ≤ ⌊(r : ℝ) ^ 2 / C⌋₊ ∧
      (codeWalk ω k).2 = -(((r + 1) / 2 : ℕ) : ℤ)} ≤
      4 * Real.exp (-C / 8) := by
  let n : ℕ := ⌊(r : ℝ) ^ 2 / C⌋₊
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hround : (r : ℝ) / 2 ≤ (((r + 1) / 2 : ℕ) : ℝ) := by
    have h : r ≤ 2 * ((r + 1) / 2) := by omega
    have h' : (r : ℝ) ≤ 2 * (((r + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h
    linarith only [h']
  let E : Set (ℕ → Fin 3) := {ω | ∃ k : ℕ, k ≤ ⌊(r : ℝ) ^ 2 / C⌋₊ ∧
    (codeWalk ω k).2 = -(((r + 1) / 2 : ℕ) : ℤ)}
  by_cases hn : n = 0
  · have he : E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨k, hk, he⟩
      have hkn : k ≤ n := hk
      have hk0 : k = 0 := by omega
      rw [hk0, codeWalk_zero] at he
      have hceil : 1 ≤ (r + 1) / 2 := by omega
      dsimp only at he
      omega
    change iidCodeMeasure.real E ≤ _
    rw [he, measureReal_empty]
    positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have htail := iidCodeWalk_blockMax_tail 0 n hnpos ((r : ℝ) / 2) (by positivity)
  simp only [Nat.zero_add, codeWalk_zero, Prod.fst_sub, Prod.snd_sub,
    sub_zero] at htail
  have hsub : E ⊆ {ω | ∃ k ≤ n, (r : ℝ) / 2 ≤ |((codeWalk ω k).1 : ℝ)| ∨
      (r : ℝ) / 2 ≤ |((codeWalk ω k).2 : ℝ)|} := by
    rintro ω ⟨k, hk, he⟩
    refine ⟨k, hk, Or.inr ?_⟩
    rw [he]
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg]
    exact hround.trans (le_abs_self _)
  have hnc : (n : ℝ) * C ≤ (r : ℝ) ^ 2 :=
    (le_div_iff₀ hC).mp (Nat.floor_le (by positivity))
  have hexp : -((r : ℝ) / 2) ^ 2 / (2 * (n : ℝ)) ≤ -C / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith only [hnc]
  exact (measureReal_mono hsub).trans
    (htail.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)))

private theorem ldpLower_shifted_floor_scale (r : ℕ) (C : ℝ) (hC : 1 < C) :
    (r : ℝ) ^ (3 / 2 : ℝ) ≤
      2 * C * ((max 1 ⌊(r : ℝ) ^ 2 / C⌋₊ : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
  let n : ℕ := ⌊(r : ℝ) ^ 2 / C⌋₊
  have hfloor := Nat.lt_floor_add_one ((r : ℝ) ^ 2 / C)
  have hn : (1 : ℝ) ≤ ((max 1 n : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left 1 n)
  have hnm : (n : ℝ) ≤ ((max 1 n : ℕ) : ℝ) := by
    exact_mod_cast (le_max_right 1 n)
  have hsq : (r : ℝ) ^ 2 ≤ (2 * C) * ((max 1 n : ℕ) : ℝ) := by
    have hx : (r : ℝ) ^ 2 / C ≤ 2 * ((max 1 n : ℕ) : ℝ) := by
      dsimp only [n] at hnm
      linarith only [hfloor, hn, hnm]
    have h := (div_le_iff₀ (by linarith : 0 < C)).mp hx
    nlinarith only [h]
  have hp := Real.rpow_le_rpow (sq_nonneg (r : ℝ)) hsq (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hid : ((r : ℝ) ^ 2) ^ (3 / 4 : ℝ) = (r : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg r)]
    norm_num
  rw [hid, Real.mul_rpow (by positivity) (by positivity)] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_self_of_one_le (by linarith : 1 ≤ 2 * C) (by norm_num))
    (Real.rpow_nonneg (by positivity) _))

/-- Helper toward Lemma 7.11, `eqn-boltzmann-ldp-lower-cell`; not a paper
result. One pair of constants works for every positive integer radius. The
first clause excludes hits of `-⌈r/2⌉` through `⌊r²/C⌋`,
including its endpoint. This strengthens the late-hit event for the strict
stopped-stage convention. It also includes paths that never hit. The
corrected shifted density is recorded in
edge, so no lower cutoff on the radius is needed. -/
theorem ldpLower_cell_inclusive_event (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C A : ℝ, 1 < C ∧ 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - ε ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
        (∀ k : ℕ, k ≤ ⌊(r : ℝ) ^ 2 / C⌋₊ →
          (codeWalk ω k).2 ≠ -(((r + 1) / 2 : ℕ) : ℤ)) ∧
        (∃ a b : StagePresentVertex (fun i => ω (i + 1)) ⌊(r : ℝ) ^ 2 / C⌋₊,
          ∃ p : Path a b, A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (p.length : ℝ))} := by
  obtain ⟨A₀, hA₀, hcell⟩ :=
    DirectedDistances.Paper.Section1.thm_cell_ldp (ε / 2) (by positivity) (by linarith)
  let C : ℝ := 64 / ε + 2
  let A : ℝ := 2 * C * A₀
  have hC : 1 < C := by
    have h : 0 < 64 / ε := by positivity
    dsimp only [C]
    linarith only [h]
  have hCpos : 0 < C := by linarith only [hC]
  have hA₀pos : 0 < A₀ := by linarith only [hA₀]
  have hA : 1 < A := by dsimp [A]; nlinarith only [hC, hA₀]
  have hApos : 0 < A := by linarith only [hA]
  refine ⟨C, A, hC, hA, ?_⟩
  intro r hr
  let n : ℕ := ⌊(r : ℝ) ^ 2 / C⌋₊
  let D : Set (ℕ → Fin 3) := {ω | ∃ a b : StagePresentVertex
    (fun i => ω (i + 1)) n, ∃ p : Path a b,
      A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (p.length : ℝ)}
  let H : Set (ℕ → Fin 3) := {ω | ∃ k : ℕ, k ≤ ⌊(r : ℝ) ^ 2 / C⌋₊ ∧
    (codeWalk ω k).2 = -(((r + 1) / 2 : ℕ) : ℤ)}
  let G : Set (ℕ → Fin 3) := {ω |
    (∀ k : ℕ, k ≤ ⌊(r : ℝ) ^ 2 / C⌋₊ →
      (codeWalk ω k).2 ≠ -(((r + 1) / 2 : ℕ) : ℤ)) ∧ ω ∈ D}
  have hD : 1 - ε / 2 ≤ iidCodeMeasure.real D := by
    by_cases hn : n = 0
    · have hscale := ldpLower_shifted_floor_scale r C hC
      change (r : ℝ) ^ (3 / 2 : ℝ) ≤
        2 * C * ((max 1 n : ℕ) : ℝ) ^ (3 / 4 : ℝ) at hscale
      rw [hn] at hscale
      norm_num only [max_eq_left (by omega : (0 : ℕ) ≤ 1), Nat.cast_one,
        Real.one_rpow, mul_one] at hscale
      have hroot : A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ 1 := by
        apply (inv_mul_le_iff₀ hApos).mpr
        dsimp only [A]
        nlinarith only [hscale, hC, hA₀]
      have huniv : Set.univ ⊆ D := by
        intro ω _
        refine ⟨⟨0⟩, ⟨1⟩, Hom.toPath (initialEdgeArrow (fun i => ω (i + 1)) n), ?_⟩
        simpa only [Path.length_toPath, Nat.cast_one] using hroot
      have hm := measureReal_mono (μ := iidCodeMeasure) huniv
      rw [probReal_univ] at hm
      linarith only [hm, hε]
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hscale := ldpLower_shifted_floor_scale r C hC
      change (r : ℝ) ^ (3 / 2 : ℝ) ≤
        2 * C * ((max 1 n : ℕ) : ℝ) ^ (3 / 4 : ℝ) at hscale
      rw [max_eq_right hnpos] at hscale
      refine (hcell n hnpos).trans (measureReal_mono ?_)
      intro ω hω
      obtain ⟨a, b, p, hp⟩ := hω.1
      refine ⟨a, b, p, (inv_mul_le_iff₀ hApos).mpr ?_⟩
      have hp' := (inv_mul_le_iff₀ hA₀pos).mp hp
      calc
        (r : ℝ) ^ (3 / 2 : ℝ) ≤ 2 * C * (n : ℝ) ^ (3 / 4 : ℝ) := hscale
        _ ≤ 2 * C * (A₀ * (p.length : ℝ)) :=
          mul_le_mul_of_nonneg_left hp' (by positivity)
        _ = A * (p.length : ℝ) := by dsimp only [A]; ring
  have htail : 4 * Real.exp (-C / 8) ≤ ε / 2 := by
    have hexp := Real.add_one_le_exp (C / 8)
    have hprod : (ε / 2) * (C / 8 + 1) ≥ 4 := by
      dsimp only [C]
      field_simp
      nlinarith only [hε]
    have hbound : 4 ≤ (ε / 2) * Real.exp (C / 8) :=
      hprod.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    have hdiv := (div_le_iff₀ (Real.exp_pos (C / 8))).mpr hbound
    rw [show -C / 8 = -(C / 8) by ring, Real.exp_neg]
    simpa only [div_eq_mul_inv] using hdiv
  have hH : iidCodeMeasure.real H ≤ ε / 2 :=
    (ldpLower_cell_earlyHit_inclusive_probability r hr C hCpos).trans htail
  have hsub : D ⊆ G ∪ H := by
    intro ω hω
    by_cases hh : ω ∈ H
    · exact Or.inr hh
    · refine Or.inl ⟨?_, hω⟩
      intro k hk he
      exact hh ⟨k, hk, he⟩
  have hm := measureReal_mono (μ := iidCodeMeasure) hsub
  have hu := measureReal_union_le (μ := iidCodeMeasure) G H
  change 1 - ε ≤ iidCodeMeasure.real G
  linarith only [hm, hu, hD, hH]


/-- First-hit measurability for the height-slice sum. Helper toward Lemma 7.11; see -/
private theorem measurable_firstHit (k : ℕ) :
    Measurable (conditionedSecondCoordinateFirstHit k) := by
  apply ENat.measurable_iff.mpr
  intro n
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp
    (measurableSet_conditionedVectorPast_firstHit_eq k n)
  change MeasurableSet {p | conditionedSecondCoordinateFirstHit k p = (n : ℕ∞)}
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix n)

/-- Measurability of the first-hit height used in the disjoint slice sum. Helper toward Lemma 7.11; see -/
private theorem measurable_hitHeight (k : ℕ) :
    Measurable (fun p : ℕ → ℤ × ℤ =>
      (p (conditionedSecondCoordinateFirstHit k p).toNat).1) := by
  have ht := (measurable_of_countable ENat.toNat).comp (measurable_firstHit k)
  have he : Measurable (fun z : (ℕ → ℤ × ℤ) × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact (he.comp (measurable_id.prodMk ht)).fst

/-- Helper toward Lemma 7.11: summing the disjoint first-hit height slices
above the height cutoff. The factor uses the corrected density recorded in -/
theorem ldpLower_postHalfHit_high_badWindow_le (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C) (r N : ℕ)
    (hN : (N : ℝ) ≤ (r : ℝ) ^ 2 / C)
    (B : Set (Fin (N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    conditionedVectorPathLaw 0 0
      {p | conditionedSecondCoordinateFirstHit (r / 2) p < ⊤ ∧
        c * (r : ℝ) ≤ ((p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat).1 : ℝ) ∧
        (fun j : Fin (N + 1) =>
          p ((conditionedSecondCoordinateFirstHit (r / 2) p).toNat + j.val) -
            p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat) ∈ B} ≤
      (ENNReal.ofReal (2 + 4 / (3 * C * c ^ 2))) ^ (1 / 2 : ℝ) *
        (lazyPrefixLaw N B) ^ (1 / 2 : ℝ) := by
  classical
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit (r / 2)
  let H (ℓ : ℕ) : Set (ℕ → ℤ × ℤ) :=
    {p | τ p < ⊤ ∧ (p (τ p).toNat).1 = (ℓ : ℤ)}
  let D (ℓ : ℕ) : Set (ℕ → ℤ × ℤ) :=
    {p | p ∈ H ℓ ∧ c * (r : ℝ) ≤ (ℓ : ℝ) ∧
      (fun j : Fin (N + 1) => p ((τ p).toNat + j.val) - p (τ p).toNat) ∈ B}
  let K := (ENNReal.ofReal (2 + 4 / (3 * C * c ^ 2))) ^ (1 / 2 : ℝ) *
    (lazyPrefixLaw N B) ^ (1 / 2 : ℝ)
  have hfinite : MeasurableSet {p | τ p < ⊤} := by
    have he : {p | τ p < ⊤} = ⋃ n : ℕ, {p | τ p = (n : ℕ∞)} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun h => by obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h.ne; exact ⟨n, hn.symm⟩,
        fun ⟨n, hn⟩ => by rw [hn]; exact ENat.natCast_lt_top n⟩
    rw [he]
    exact MeasurableSet.iUnion fun n =>
      (measurable_firstHit (r / 2)) (measurableSet_singleton _)
  have hHm : ∀ ℓ, MeasurableSet (H ℓ) := fun ℓ =>
    hfinite.inter (measurableSet_eq_fun (measurable_hitHeight (r / 2)) measurable_const)
  have hHd : Pairwise (fun i j => Disjoint (H i) (H j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    apply hij
    have hh : (i : ℤ) = (j : ℤ) := hi.2.symm.trans hj.2
    exact_mod_cast hh
  have hsub : {p | τ p < ⊤ ∧
      c * (r : ℝ) ≤ ((p (τ p).toNat).1 : ℝ) ∧
      (fun j : Fin (N + 1) => p ((τ p).toNat + j.val) - p (τ p).toNat) ∈ B} ⊆
      ⋃ ℓ, D ℓ := by
    rintro p ⟨hfin, hheight, hbad⟩
    have hz : 0 ≤ (p (τ p).toNat).1 := by
      have hh : (0 : ℝ) ≤ ((p (τ p).toNat).1 : ℝ) :=
        (mul_nonneg hc.le (Nat.cast_nonneg r)).trans hheight
      exact_mod_cast hh
    refine Set.mem_iUnion.mpr ⟨(p (τ p).toNat).1.toNat, ?_⟩
    have he := Int.toNat_of_nonneg hz
    have heR : (((p (τ p).toNat).1.toNat : ℕ) : ℝ) =
        ((p (τ p).toNat).1 : ℝ) := by exact_mod_cast he
    exact ⟨⟨hfin, he.symm⟩, by rwa [heR], hbad⟩
  have hD : ∀ ℓ, μ (D ℓ) ≤ μ (H ℓ) * K := by
    intro ℓ
    by_cases hℓ : c * (r : ℝ) ≤ (ℓ : ℝ)
    · have he : D ℓ = {p | τ p < ⊤ ∧ (p (τ p).toNat).1 = (ℓ : ℤ) ∧
          (fun j : Fin (N + 1) => p ((τ p).toNat + j.val) - p (τ p).toNat) ∈ B} := by
        ext p
        simp only [D, H, Set.mem_ofPred_eq, hℓ]
        tauto
      rw [he]
      exact ldpLower_postHalfHit_badWindow_le c C hc hC r ℓ N hℓ hN B hB
    · have he : D ℓ = ∅ := by ext p; simp [D, hℓ]
      rw [he, measure_empty]
      exact bot_le
  calc
    _ ≤ μ (⋃ ℓ, D ℓ) := measure_mono hsub
    _ ≤ ∑' ℓ, μ (D ℓ) := measure_iUnion_le _
    _ ≤ ∑' ℓ, μ (H ℓ) * K := tsum_le_tsum hD
    _ = μ (⋃ ℓ, H ℓ) * K := by
      rw [ENNReal.tsum_mul_right, measure_iUnion hHd hHm]
    _ ≤ 1 * K := mul_le_mul_of_nonneg_right prob_le_one (by positivity)
    _ = K := one_mul K

/-- The literal finite walk prefix on the iid code carrier. Helper toward Lemma 7.11; see -/
private def shiftedIIDPrefix (k : ℕ) (ω : ℕ → Fin 3) :
    Fin (k + 1) → ℤ × ℤ := fun j => codeWalk ω j.val

/-- The finite source word, excluding the deterministic dummy coordinate. Helper toward Lemma 7.11; see -/
private def shiftedIIDWord (k : ℕ) (ω : ℕ → Fin 3) : Fin k → Fin 3 :=
  fun i => ω (i.val + 1)

/-- Identification of the iid finite walk prefix with the integrated finite word. Helper toward Lemma 7.11; see -/
private theorem shiftedIIDPrefix_eq_lazyPrefix (k : ℕ) (ω : ℕ → Fin 3) :
    shiftedIIDPrefix k ω =
      lazyTwoDimensionalPrefix 0 0 (shiftedIIDWord k ω) := by
  funext j
  have hsum (f : Fin 3 → ℤ) :
      ∑ i ∈ Finset.range j.val, f (ω (i + 1)) =
        ∑ i : Fin k with i.val < j.val, f (ω (i.val + 1)) := by
    have hs : Finset.range j.val = (Finset.range k).filter (fun i => i < j.val) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    rw [hs, Finset.sum_filter, Finset.sum_filter,
      Fin.sum_univ_eq_sum_range (fun i => if i < j.val then f (ω (i + 1)) else 0) k]
  unfold shiftedIIDPrefix shiftedIIDWord codeWalk lazyTwoDimensionalPrefix
  apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, zero_add] <;>
    first | exact hsum (fun c => (lazyTwoDimensionalStep c).1)
          | exact hsum (fun c => (lazyTwoDimensionalStep c).2)

/-- Uniform law of the finite iid source word. Helper toward Lemma 7.11; see -/
private theorem shifted_iidCodeMeasure_map_IIDWord (k : ℕ) :
    iidCodeMeasure.map (shiftedIIDWord k) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3)) := by
  classical
  have hf : shiftedIIDWord k =
      (fun q : Fin (k + 1) → Fin 3 => fun i : Fin k => q i.succ) ∘
        (fun ω : ℕ → Fin 3 => fun j : Fin (k + 1) => ω j.val) := by
    funext ω i
    rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    iidCodeMeasure_map_prefix]
  have hmp := measurePreserving_piFinSuccAbove
    (fun j : Fin (k + 1) => if j.val = 0 then
      Measure.dirac (0 : Fin 3) else uniformCodeMeasure) 0
  have hsnd : (fun q : Fin (k + 1) → Fin 3 => fun i : Fin k => q i.succ) =
      Prod.snd ∘ MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (k + 1) => Fin 3) 0 := by
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

/-- Identification of the iid prefix law with the finite lazy-prefix carrier. Helper toward Lemma 7.11; see -/
private theorem shifted_iidCodeMeasure_map_IIDPrefix (k : ℕ) :
    iidCodeMeasure.map (shiftedIIDPrefix k) =
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0) := by
  have hw : Measurable (shiftedIIDWord k) :=
    Measurable.of_eval fun i => measurable_pi_apply (i.val + 1)
  rw [show shiftedIIDPrefix k =
      (lazyTwoDimensionalPrefix 0 0) ∘ shiftedIIDWord k from by
        funext ω
        exact shiftedIIDPrefix_eq_lazyPrefix k ω]
  rw [← Measure.map_map (measurable_of_countable _) hw,
    shifted_iidCodeMeasure_map_IIDWord]


/-- Constant extension of a finite window, used only through its original horizon. Helper toward Lemma 7.11; see -/
private def extendWindow {N : ℕ} (q : Fin (N + 1) → ℤ × ℤ) (n : ℕ) : ℤ × ℤ :=
  q ⟨min n N, by omega⟩

/-- The window extension preserves every coordinate through its original horizon. Helper toward Lemma 7.11; see -/
private theorem extendWindow_prefix (N : ℕ) (p : ℕ → ℤ × ℤ) (n : ℕ) (hn : n ≤ N) :
    extendWindow (fun j : Fin (N + 1) => p j.val) n = p n := by
  simp only [extendWindow, min_eq_left hn]

/-- The decoded window and the original path give the same finite KMSW stage. Helper toward Lemma 7.11; see -/
private theorem windowStage_eq (N : ℕ) (p : ℕ → ℤ × ℤ) :
    kmswStage (boltzmannKMSWStream (pathCode
      (extendWindow (fun j : Fin (N + 1) => p j.val)))) N =
    kmswStage (boltzmannKMSWStream (pathCode p)) N := by
  apply kmswStage_congr
  intro i hi
  change pathCode (extendWindow (fun j : Fin (N + 1) => p j.val)) (i + 1) =
    pathCode p (i + 1)
  simp only [pathCode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    extendWindow_prefix N p (i + 1) (by omega),
    extendWindow_prefix N p (i + 1 - 1) (by omega)]

/-- Equal stages preserve present directed paths and their lengths. Helper toward Lemma 7.11; see -/
private theorem stage_hasLongPath_congr {w w' : ℕ → Fin 3} {N : ℕ}
    (h : kmswStage w N = kmswStage w' N) (b : ℝ) :
    (∃ a z : StagePresentVertex w N, ∃ p : Path a z, b ≤ (p.length : ℝ)) ↔
    (∃ a z : StagePresentVertex w' N, ∃ p : Path a z, b ≤ (p.length : ℝ)) := by
  have transfer {u v : ℕ → Fin 3} (he : kmswStage u N = kmswStage v N)
      (hh : ∃ a z : StagePresentVertex u N, ∃ p : Path a z, b ≤ (p.length : ℝ)) :
      ∃ a z : StagePresentVertex v N, ∃ p : Path a z, b ≤ (p.length : ℝ) := by
    obtain ⟨a, z, p, hp⟩ := hh
    let F : Prefunctor (StagePresentVertex u N) (StagePresentVertex v N) := {
      obj := fun a => ⟨a.id⟩
      map := fun e => ⟨e.val, by simpa only [he] using e.property⟩ }
    have hlen : (F.mapPath p).length = p.length := by
      clear hp
      induction p with
      | nil => rfl
      | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
    exact ⟨F.obj a, F.obj z, F.mapPath p, by simpa only [hlen] using hp⟩
  exact ⟨transfer h, transfer h.symm⟩

/-- The strengthened cell event on the finite-prefix carrier, including the terminal time. Helper toward Lemma 7.11; see -/
private def inclusiveWindowEvent (r N : ℕ) (A : ℝ) :
    Set (Fin (N + 1) → ℤ × ℤ) := {q |
      (∀ j, (q j).2 ≠ -(((r + 1) / 2 : ℕ) : ℤ)) ∧
      ∃ a b : StagePresentVertex (boltzmannKMSWStream (pathCode (extendWindow q))) N,
        ∃ p : Path a b, A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (p.length : ℝ)}

/-- Identification of the finite-prefix strengthened event on the iid code carrier. Helper toward Lemma 7.11; see -/
private theorem inclusiveWindowEvent_codeWalk (r N : ℕ) (A : ℝ) (ω : ℕ → Fin 3) :
    (fun j : Fin (N + 1) => codeWalk ω j.val) ∈ inclusiveWindowEvent r N A ↔
      (∀ k : ℕ, k ≤ N → (codeWalk ω k).2 ≠ -(((r + 1) / 2 : ℕ) : ℤ)) ∧
      (∃ a b : StagePresentVertex (fun i => ω (i + 1)) N,
        ∃ p : Path a b, A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (p.length : ℝ)) := by
  have hstream : boltzmannKMSWStream (pathCode (codeWalk ω)) = fun i => ω (i + 1) := by
    funext i
    exact pathCode_codeWalk ω (i + 1) (by omega)
  have hs := windowStage_eq N (codeWalk ω)
  rw [hstream] at hs
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr
  · exact ⟨fun h k hk => h ⟨k, by omega⟩, fun h j => h j.val (by omega)⟩
  · exact stage_hasLongPath_congr hs _

/-- The strengthened cell estimate transferred to the finite lazy-prefix carrier. Helper toward Lemma 7.11; see -/
private theorem lazyPrefixLaw_bad_inclusiveWindow_le (ε C A : ℝ)
    (r : ℕ) (hcell : 1 - ε ≤ iidCodeMeasure.real
      {ω : ℕ → Fin 3 |
        (∀ k : ℕ, k ≤ ⌊(r : ℝ) ^ 2 / C⌋₊ →
          (codeWalk ω k).2 ≠ -(((r + 1) / 2 : ℕ) : ℤ)) ∧
        (∃ a b : StagePresentVertex (fun i => ω (i + 1)) ⌊(r : ℝ) ^ 2 / C⌋₊,
          ∃ p : Path a b, A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (p.length : ℝ))}) :
    (lazyPrefixLaw ⌊(r : ℝ) ^ 2 / C⌋₊).real
      (inclusiveWindowEvent r ⌊(r : ℝ) ^ 2 / C⌋₊ A)ᶜ ≤ ε := by
  let N := ⌊(r : ℝ) ^ 2 / C⌋₊
  let := lazyPrefixLaw_isProbability N
  have hm : Measurable (shiftedIIDPrefix N) := by
    exact .of_eval fun j => (measurable_pi_apply j.val).comp measurable_codeWalk
  have he := shifted_iidCodeMeasure_map_IIDPrefix N
  change iidCodeMeasure.map (shiftedIIDPrefix N) = lazyPrefixLaw N at he
  have hgood : 1 - ε ≤ (lazyPrefixLaw N).real (inclusiveWindowEvent r N A) := by
    rw [← he, map_measureReal_apply hm ((Set.to_countable _).measurableSet)]
    convert hcell using 1
    congr 1
    ext ω
    exact inclusiveWindowEvent_codeWalk r N A ω
  have ht := measureReal_add_measureReal_compl (μ := lazyPrefixLaw N)
    ((Set.to_countable (inclusiveWindowEvent r N A)).measurableSet)
  rw [probReal_univ] at ht
  linarith only [ht, hgood]


/-- Identification of a first-hit witness with the extended-natural first-hit time. Helper toward Lemma 7.11; see -/
private theorem firstHit_eq_of_first (k n : ℕ) (p : ℕ → ℤ × ℤ)
    (hn : (p n).2 = -(k : ℤ)) (hbefore : ∀ j < n, (p j).2 ≠ -(k : ℤ)) :
    conditionedSecondCoordinateFirstHit k p = (n : ℕ∞) := by
  classical
  have hh : ∃ j, (p j).2 = -(k : ℤ) := ⟨n, hn⟩
  simp only [conditionedSecondCoordinateFirstHit, dite_eq_left hh]
  exact congrArg (fun n : ℕ => (n : ℕ∞)) ((Nat.find_eq_iff hh).mpr ⟨hn, hbefore⟩)

/-- A finite extended-natural hit supplies an actual hitting-time witness. Helper toward Lemma 7.11; see -/
private theorem hit_exists_of_finite (k : ℕ) (p : ℕ → ℤ × ℤ)
    (hf : conditionedSecondCoordinateFirstHit k p < ⊤) :
    ∃ n, (p n).2 = -(k : ℤ) := by
  classical
  by_contra hh
  simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hh, lt_self_iff_false] at hf

/-- Unit downward steps cannot skip an intervening integer level. Helper toward Lemma 7.11; see -/
private theorem lower_hit_before (q : ℕ → ℤ) (hq : q 0 = 0)
    (hs : ∀ n, q n - 1 ≤ q (n + 1)) (r n : ℕ) (hn : q n ≤ -(r : ℤ)) :
    ∃ k ≤ n, q k = -(r : ℤ) := by
  induction n with
  | zero => exact ⟨0, le_rfl, by rw [hq] at hn ⊢; omega⟩
  | succ n ih =>
    by_cases h : q n ≤ -(r : ℤ)
    · obtain ⟨k, hk, he⟩ := ih h
      exact ⟨k, by omega, he⟩
    · exact ⟨n + 1, le_rfl, by have := hs n; omega⟩

/-- The inclusive no-hit clause places the shifted stage strictly before the stopping time. Helper toward Lemma 7.11; see -/
private theorem inclusiveWindow_stopped_segment (r N : ℕ) (A : ℝ)
    (p : ℕ → ℤ × ℤ)
    (hlegal : p 0 = (0, 0) ∧ ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (hfr : conditionedSecondCoordinateFirstHit r p < ⊤)
    (hfh : conditionedSecondCoordinateFirstHit (r / 2) p < ⊤)
    (hg : (fun j : Fin (N + 1) =>
      p ((conditionedSecondCoordinateFirstHit (r / 2) p).toNat + j.val) -
        p (conditionedSecondCoordinateFirstHit (r / 2) p).toNat) ∈
          inclusiveWindowEvent r N A) :
    boltzmannTau (r / 2) (pathCode p) + N < boltzmannTau r (pathCode p) ∧
      (∃ a b : StagePresentVertex
        (fun i => boltzmannKMSWStream (pathCode p)
          (boltzmannTau (r / 2) (pathCode p) + i)) N,
        ∃ s : Path a b, A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (s.length : ℝ)) := by
  classical
  have hw : codeWalk (pathCode p) = p := by
    funext n
    rw [codeWalk_pathCode p hlegal.2 n, hlegal.1]
    exact sub_zero _
  have hhr := hit_exists_of_finite r p hfr
  have hhh := hit_exists_of_finite (r / 2) p hfh
  let T := Nat.find hhh
  let U := Nat.find hhr
  have hT : boltzmannTau (r / 2) (pathCode p) = T := by
    simp only [boltzmannTau, hw, dite_eq_left hhh]; rfl
  have hU : boltzmannTau r (pathCode p) = U := by
    simp only [boltzmannTau, hw, dite_eq_left hhr]; rfl
  have ht : (conditionedSecondCoordinateFirstHit (r / 2) p).toNat = T := by
    simp only [conditionedSecondCoordinateFirstHit, dite_eq_left hhh, ENat.toNat_natCast]; rfl
  have hlevT : (p T).2 = -((r / 2 : ℕ) : ℤ) := Nat.find_spec hhh
  have hlevU : (p U).2 = -(r : ℤ) := Nat.find_spec hhr
  have hsteps : ∀ n, (p n).2 - 1 ≤ (p (n + 1)).2 := by
    intro n
    obtain ⟨c, hc⟩ := hlegal.2 n
    have hh := congrArg Prod.snd hc
    fin_cases c <;> norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hh ⊢ <;> omega
  have hTU : T ≤ U := by
    obtain ⟨k, hk, he⟩ := lower_hit_before (fun n => (p n).2)
      (congrArg Prod.snd hlegal.1) hsteps (r / 2) U (by rw [hlevU]; omega)
    exact (Nat.find_min' hhh he).trans hk
  rw [ht] at hg
  have hTN : T + N < U := by
    by_contra h
    have hk : U - T ≤ N := by omega
    have hno := hg.1 ⟨U - T, by omega⟩
    apply hno
    change (p (T + (U - T)) - p T).2 = _
    rw [Nat.add_sub_of_le hTU, Prod.snd_sub, hlevU, hlevT]
    omega
  have hs := windowStage_eq N (fun n => p (T + n) - p T)
  have hp := (stage_hasLongPath_congr hs (A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ))).mp hg.2
  rw [ldpLower_centeredSegment_stream] at hp
  rw [hT, hU]
  exact ⟨hTN, hp⟩

/-- Full large-radius step-2 estimate toward Lemma 7.11
strict stopping before `τ_r`. Constants are chosen using `C > 1` to bound
the corrected RN factor independently of `C`, as recorded in -/
theorem ldpLower_postHalfHit_segment_probability (δ : ℝ) (hδ : 0 < δ) :
    ∃ A C : ℝ, 1 < A ∧ 1 < C ∧ ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      1 - δ ≤ (conditionedVectorPathLaw 0 0).real
        {p | boltzmannTau (r / 2) (pathCode p) + ⌊(r : ℝ) ^ 2 / C⌋₊ <
            boltzmannTau r (pathCode p) ∧
          (∃ a b : StagePresentVertex
            (fun i => boltzmannKMSWStream (pathCode p)
              (boltzmannTau (r / 2) (pathCode p) + i)) ⌊(r : ℝ) ^ 2 / C⌋₊,
            ∃ s : Path a b, A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (s.length : ℝ))} := by
  classical
  obtain ⟨c, hc, r₀, hheight⟩ := conditionedVectorPathLaw_first_hit_height_lower δ hδ
  let M : ℝ := 2 + 4 / (3 * c ^ 2)
  have hM : 0 < M := by dsimp [M]; positivity
  let t : ℝ := min (δ / (2 * (M + 1))) (1 / 2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let ε : ℝ := t ^ 2
  have hε : 0 < ε := sq_pos_of_pos ht
  have hε1 : ε < 1 := by dsimp [ε]; nlinarith only [ht, ht1]
  obtain ⟨C, A, hC, hA, hcell⟩ := ldpLower_cell_inclusive_event ε hε hε1
  have hCpos : 0 < C := by linarith only [hC]
  refine ⟨A, C, hA, hC, max r₀ 1, ?_⟩
  intro r hr
  have hr₀ : r₀ ≤ r := (le_max_left _ _).trans hr
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  let N := ⌊(r : ℝ) ^ 2 / C⌋₊
  let μ := conditionedVectorPathLaw 0 0
  let := lazyPrefixLaw_isProbability N
  let τ := conditionedSecondCoordinateFirstHit (r / 2)
  let B := (inclusiveWindowEvent r N A)ᶜ
  let D : Set (ℕ → ℤ × ℤ) := {p | τ p < ⊤ ∧
    c * (r : ℝ) ≤ ((p (τ p).toNat).1 : ℝ) ∧
      (fun j : Fin (N + 1) => p ((τ p).toNat + j.val) - p (τ p).toNat) ∈ B}
  let E : Set (ℕ → ℤ × ℤ) := {p | ∃ n : ℕ,
    (p n).2 = -((r / 2 : ℕ) : ℤ) ∧
      (∀ k < n, (p k).2 ≠ -((r / 2 : ℕ) : ℤ)) ∧ c * (r : ℝ) ≤ ((p n).1 : ℝ)}
  let G : Set (ℕ → ℤ × ℤ) := {p |
    boltzmannTau (r / 2) (pathCode p) + N < boltzmannTau r (pathCode p) ∧
      ∃ a b : StagePresentVertex
        (fun i => boltzmannKMSWStream (pathCode p)
          (boltzmannTau (r / 2) (pathCode p) + i)) N,
        ∃ s : Path a b, A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (s.length : ℝ)}
  have hB : (lazyPrefixLaw N).real B ≤ ε :=
    lazyPrefixLaw_bad_inclusiveWindow_le ε C A r (hcell r hr1)
  have hraw := ldpLower_postHalfHit_high_badWindow_le c C hc hCpos r N
    (Nat.floor_le (by positivity)) B ((Set.to_countable B).measurableSet)
  have hMC : 2 + 4 / (3 * C * c ^ 2) ≤ M := by
    dsimp only [M]
    have hd : 0 < 3 * c ^ 2 := by positivity
    have hh : 3 * c ^ 2 ≤ 3 * C * c ^ 2 := by nlinarith only [hC, sq_pos_of_pos hc]
    exact add_le_add (show (2 : ℝ) ≤ 2 from le_rfl)
      (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 4 by norm_num) hd hh)
  have hbad : μ.real D ≤ δ / 2 := by
    have hf : ENNReal.ofReal (2 + 4 / (3 * C * c ^ 2)) ^ (1 / 2 : ℝ) *
        lazyPrefixLaw N B ^ (1 / 2 : ℝ) ≠ ⊤ := by finiteness
    have hh := ENNReal.toReal_mono hf hraw
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (by positivity)] at hh
    change μ.real D ≤ _ at hh
    have hroot : Real.sqrt M ≤ M + 1 := by
      have hsq := Real.sq_sqrt hM.le
      have hnonneg := Real.sqrt_nonneg M
      nlinarith only [hsq, hnonneg, hM]
    have heps : Real.sqrt ε = t := by dsimp [ε]; exact Real.sqrt_sq ht.le
    have htδ : (M + 1) * t ≤ δ / 2 := by
      have hh := min_le_left (δ / (2 * (M + 1))) (1 / 2 : ℝ)
      change t ≤ _ at hh
      have hd := (le_div_iff₀ (by positivity : 0 < 2 * (M + 1))).mp hh
      linarith only [hd]
    calc
      μ.real D ≤ Real.sqrt (2 + 4 / (3 * C * c ^ 2)) *
          Real.sqrt ((lazyPrefixLaw N).real B) := by
        simpa only [Real.sqrt_eq_rpow, Measure.real] using hh
      _ ≤ Real.sqrt M * Real.sqrt ε :=
        mul_le_mul (Real.sqrt_le_sqrt hMC) (Real.sqrt_le_sqrt hB)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ (M + 1) * t := by rw [heps]; exact mul_le_mul_of_nonneg_right hroot ht.le
      _ ≤ δ / 2 := htδ
  have hsub : E ≤ᵐ[μ] G ∪ D := by
    filter_upwards [conditionedVectorPathLaw_ae_legal, firstHitPastMap_finite_hit_ae r hr1]
      with p hlegal hfr
    rintro ⟨n, hn, hbefore, hlevel⟩
    have hτ := firstHit_eq_of_first (r / 2) n p hn hbefore
    have hfh : τ p < ⊤ := by change conditionedSecondCoordinateFirstHit (r / 2) p < ⊤; rw [hτ]; exact ENat.natCast_lt_top n
    by_cases hbad : (fun j : Fin (N + 1) => p ((τ p).toNat + j.val) - p (τ p).toNat) ∈ B
    · right
      refine ⟨hfh, ?_, hbad⟩
      simpa only [τ, hτ, ENat.toNat_natCast] using hlevel
    · left
      apply inclusiveWindow_stopped_segment r N A p hlegal hfr hfh
      simpa only [B, Set.mem_compl_iff, not_not] using hbad
  have hm : μ.real E ≤ μ.real (G ∪ D) :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := μ) G D
  have hE : 1 - δ / 2 ≤ μ.real E := hheight r hr₀
  change 1 - δ ≤ μ.real G
  linarith only [hE, hm, hu, hbad]

/-- The exact step-2 proposition consumed by the conditional assembly of
Lemma 7.11. The corrected density and the inclusive endpoint convention are -/
theorem ldpLower_lemma711Step2 : lemma711Step2 := by
  intro δ hδ
  exact ldpLower_postHalfHit_segment_probability δ hδ

end DirectedDistances.PaperProofs.Section7
