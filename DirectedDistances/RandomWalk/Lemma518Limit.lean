module

public import DirectedDistances.RandomWalk.Lemma518BridgeReduction
public import DirectedDistances.RandomWalk.DecodedChunkWindowLaw
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Real.Sqrt

/-! # Uniform convention-free bridge window limit

Helpers toward corrected Lemma 5.18 (`lem-disk-walk-conv`),
in lines 785–823. These helpers are not counted as paper results.
is convention-free and quantifies over all measurable extensions agreeing
on level-interior bridge outcomes. The cemetery form belongs in a separate file. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- Explicit convention-free comparison toward corrected Lemma 5.18
to every measurable extension agreeing on level-interior bridge outcomes. -/
theorem bridgeWindow_tv_explicit (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ell n : ℕ), (hm : 0 < m) → m ≤ ell →
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ W : (ℕ → Fin 3) × ℕ → (Fin (2 * N + 1) → ℤ × ℤ),
      Measurable W →
      (∀ ω K, ω ∈ coneEvent (ell : ℤ) 0 n → 1 ≤ K → K ≤ ell →
        N ≤ K → K + N ≤ ell → W (ω, K) = bridgeRawWindow N (ω, K)) →
      ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ), MeasurableSet B →
      |((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.Icc 1 ell))).real (W ⁻¹' B) -
        (uibhbotExcursionWindowLaw N).real B| ≤
        2 * δ + 4 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
          Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c +
        2 * (m : ℝ) / ell +
        2 * iidCodeMeasure.real
          {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} +
        4 * (N : ℝ) / m + 2 * (N : ℝ) / ell + 1 / (ell : ℝ) := by
  obtain ⟨c, hc, hred⟩ := bridgeWindow_reduction_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m ell n hm hml N δ hδ hn hlo hhi hln hcong W hW hagree B hB
  have h₁ := hred m ell n hm hml N δ hδ hn hlo hhi hln hcong W hW hagree B hB
  have h₂ := decodedChunkWindow_excursionWindow_bound N m hm B hB
  have ht := abs_sub_le
    (((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
      (Measure.uniformOfFinset (Finset.Icc 1 ell))).real (W ⁻¹' B))
    (((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
      {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
        decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B})
    ((uibhbotExcursionWindowLaw N).real B)
  convert ht.trans (add_le_add h₁ h₂) using 1
  ring

/-- Uniform control of the fixed-block errors on the lower square-root band.
Helper toward corrected `lem-disk-walk-conv`, -/
private theorem bridgeWindow_fixedParameters_eventually
    (A : ℝ) (hA : 1 < A) (m N : ℕ) (hm : 0 < m)
    (δ c η : ℝ) (hδ : 0 < δ) (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ell : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      m ≤ ell ∧
      4 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c ≤ η ∧
      (2 * (m : ℝ) + 2 * (N : ℝ) + 1) / ell ≤ η := by
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  let L : ℕ → ℕ := fun n => ⌈A⁻¹ * Real.sqrt (n : ℝ)⌉₊
  have hlim := conditionedSelectedChunk_bound_tendsto A hA m (m ^ 100) hm δ c hδ hc L
    (Filter.Eventually.of_forall fun n => Nat.le_ceil _)
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlow : Filter.Tendsto (fun n : ℕ => A⁻¹ * Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop := hsqrt.const_mul_atTop (inv_pos.mpr hA0)
  have htail := hlow.const_div_atTop (2 * (m : ℝ) + 2 * (N : ℝ) + 1)
  filter_upwards [hlim.eventually_le_const (show δ < δ + η / 2 by linarith),
    htail.eventually_le_const hη, hlow.eventually_ge_atTop (m : ℝ)] with n he ht hmlo
  intro ell hlo
  have hml : m ≤ ell := by exact_mod_cast hmlo.trans hlo
  have hlpos : 0 < A⁻¹ * Real.sqrt (n : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast hm) hmlo
  refine ⟨hml, ?_, (div_le_div_of_nonneg_left (by positivity) hlpos hlo).trans ht⟩
  have hL : L n ≤ ell := Nat.ceil_le.mpr hlo
  have hd : ((L n / m : ℕ) : ℝ) ≤ ((ell / m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_le_div_right hL : L n / m ≤ ell / m)
  have hexp : Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) ≤
      Real.exp (-2 * δ ^ 2 * (L n / m : ℕ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hd (by nlinarith only [sq_nonneg δ])
  have he' : δ + 2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
      Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c ≤ δ + η / 2 := by
    apply le_trans _ he
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ hc.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
  calc
    _ = 2 * ((δ + 2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c) - δ) := by ring
    _ ≤ 2 * ((δ + η / 2) - δ) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right he' δ) (by norm_num)
    _ = η := by ring

/-- The positive-size lower band forces a positive level. Helper toward
corrected Lemma 5.18 (`lem-disk-walk-conv`,
band; not counted as a paper result. -/
theorem bridgeWindow_one_le_level (A : ℝ) (hA : 1 < A) (n ell : ℕ)
    (hn : 1 ≤ n) (hlo : A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ)) :
    1 ≤ ell := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpos : (0 : ℝ) < ell :=
    (mul_pos (inv_pos.mpr (lt_trans zero_lt_one hA))
      (Real.sqrt_pos.mpr hnpos)).trans_le hlo
  have : 0 < ell := by exact_mod_cast hpos
  exact this

/-- Uniform convention-free window comparison toward corrected Lemma 5.18
successive limits in lines 785–823); not counted as a paper result.
the measurable extension, and the measurable event. No cemetery convention
is selected: all extensions agreeing on level-interior bridge outcomes qualify. -/
theorem bridgeWindow_tv_uniform (A : ℝ) (hA : 1 < A) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ell : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ W : (ℕ → Fin 3) × ℕ → (Fin (2 * N + 1) → ℤ × ℤ), Measurable W →
      (∀ ω K, ω ∈ coneEvent (ell : ℤ) 0 n → 1 ≤ K → K ≤ ell → N ≤ K → K + N ≤ ell →
        W (ω, K) = bridgeRawWindow N (ω, K)) →
      ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ), MeasurableSet B →
      |((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.Icc 1 ell))).real (W ⁻¹' B) -
        (uibhbotExcursionWindowLaw N).real B| ≤ ε := by
  obtain ⟨c, hc, hexplicit⟩ := bridgeWindow_tv_explicit A hA
  obtain ⟨m₀, hm₀⟩ := exists_fstHit_overflow_eventually_small (ε / 16) (by positivity)
  have hofflim : Filter.Tendsto (fun m : ℕ => 4 * (N : ℝ) / (m : ℝ))
      Filter.atTop (nhds 0) := tendsto_natCast_atTop_atTop.const_div_atTop _
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp
    (hofflim.eventually_le_const (show 0 < ε / 8 by positivity))
  let m : ℕ := max 1 (max m₀ m₁)
  have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hmm₀ : m₀ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmm₁ : m₁ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hov := hm₀ m hmm₀
  have hoff := hm₁ m hmm₁
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
    (bridgeWindow_fixedParameters_eventually A hA m N hm (ε / 8) c (ε / 8)
      (by positivity) hc (by positivity))
  refine ⟨max 1 k, ?_⟩
  intro n hn ell hlo hhi hln hcong W hW hagree B hB
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  obtain ⟨hml, he, ht⟩ := hk n ((le_max_right _ _).trans hn) ell hlo
  have hb := hexplicit m ell n hm hml N (ε / 8) (by positivity)
    hn1 hlo hhi hln hcong W hW hagree B hB
  calc
    _ ≤ 2 * (ε / 8) +
        4 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
          Real.exp (-2 * (ε / 8) ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c +
        2 * iidCodeMeasure.real
          {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} +
        4 * (N : ℝ) / m + (2 * (m : ℝ) + 2 * (N : ℝ) + 1) / ell := by
      convert hb using 1
      ring
    _ ≤ ε := by linarith only [he, ht, hov, hoff, hε]

end DirectedDistances.RandomWalk
