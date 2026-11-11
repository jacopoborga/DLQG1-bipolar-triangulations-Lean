module

public import DirectedDistances.Recursive.LDPFluctuationConditional
public import DirectedDistances.Recursive.RightStationaryBusemann







public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk

private theorem variation_bound (f : ℕ → ℝ) (n : ℕ) :
    ∀ a b : ℕ, a ≤ n → b ≤ n →
      |f a - f b| ≤ ∑ i ∈ Finset.range n, |f (i + 1) - f i| := by
  induction n with
  | zero =>
      intro a b ha hb
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      simp [ha0, hb0]
  | succ n ih =>
      intro a b ha hb
      rw [Finset.sum_range_succ]
      by_cases han : a ≤ n
      · by_cases hbn : b ≤ n
        · exact (ih a b han hbn).trans (le_add_of_nonneg_right (abs_nonneg _))
        · have hbe : b = n + 1 := by omega
          rw [hbe]
          calc
            |f a - f (n + 1)| ≤ |f a - f n| + |f n - f (n + 1)| :=
              abs_sub_le _ _ _
            _ ≤ (∑ i ∈ Finset.range n, |f (i + 1) - f i|) +
                |f (n + 1) - f n| := by
              rw [abs_sub_comm (f n)]
              have hh := ih a n han le_rfl
              linarith only [hh]
      · have hae : a = n + 1 := by omega
        rw [hae]
        by_cases hbn : b ≤ n
        · calc
            |f (n + 1) - f b| ≤ |f (n + 1) - f n| + |f n - f b| :=
              abs_sub_le _ _ _
            _ ≤ (∑ i ∈ Finset.range n, |f (i + 1) - f i|) +
                |f (n + 1) - f n| := by
              have hh := ih n b le_rfl hbn
              linarith only [hh]
        · have hbe : b = n + 1 := by omega
          rw [hbe, sub_self, abs_zero]
          exact add_nonneg (Finset.sum_nonneg fun i hi => abs_nonneg _) (abs_nonneg _)

private theorem busemann_variation_bound (ω : ℕ → Fin 3) (k : ℕ)
    (l : ℤ) (hl : -(k : ℤ) ≤ l) (hl' : l ≤ k) :
    |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
      ∑ i : Fin (2 * k),
        |((ldpIncrement busemannLDPMeasurableVersion
          ((i.val : ℤ) - k + 1) ω : ℤ) : ℝ)| := by
  let f : ℕ → ℝ := fun n => (busemannLDPMeasurableVersion ω ((n : ℤ) - k) : ℝ)
  let j : ℕ := (l + (k : ℤ)).toNat
  have hj : j ≤ 2 * k := by dsimp [j]; omega
  have he : (j : ℤ) - k = l := by dsimp [j]; omega
  have hv := variation_bound f (2 * k) j k hj (by omega)
  have hfj : f j = (busemannLDPMeasurableVersion ω l : ℝ) := by simp [f, he]
  have hfk : f k = 0 := by simp [f, busemannLDPMeasurableVersion_zero]
  rw [hfj, hfk, sub_zero] at hv
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    |((ldpIncrement busemannLDPMeasurableVersion ((i : ℤ) - k + 1) ω : ℤ) : ℝ)|)]
  have hi (i : ℕ) : |f (i + 1) - f i| =
      |((ldpIncrement busemannLDPMeasurableVersion
        ((i : ℤ) - k + 1) ω : ℤ) : ℝ)| := by
    have e₁ : ((i + 1 : ℕ) : ℤ) - k = (i : ℤ) - k + 1 := by omega
    have e₀ : (i : ℤ) - k + 1 - 1 = (i : ℤ) - k := by omega
    simp only [f, ldpIncrement, Int.cast_sub, e₁, e₀]
  simpa only [hi] using hv

/-- using finite-sum tails. The open items are `ind`, stationarity for `k ≤ 0`,
and `sym`; positive-index stationarity is supplied by
`busemannLDPMeasurableVersion_right_stationary`. This is not
`lem-ldp-fluctuation` itself and is not counted as that paper result. F1/F4 apply. -/
theorem ldp_fluctuation_of_items
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0))
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  classical
  obtain ⟨C, hC, htail⟩ := ldp_absolute_increment_tail_bound_of_items hind
    busemannLDPMeasurableVersion_right_stationary hstatL hsym
  refine ⟨8 * C, ?_⟩
  intro k hk A hA
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hApos : 0 < A := lt_trans zero_lt_one hA
  let Z : Fin (2 * k) → (ℕ → Fin 3) → ℝ := fun i ω =>
    |((ldpIncrement busemannLDPMeasurableVersion ((i.val : ℤ) - k + 1) ω : ℤ) : ℝ)|
  have hZm (i : Fin (2 * k)) : Measurable (Z i) := by
    exact (measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp
      ((measurable_busemannLDPMeasurableVersion _).sub
        (measurable_busemannLDPMeasurableVersion _))
  have ht : 0 < A * (k : ℝ) ^ (3 / 2 : ℝ) :=
    mul_pos hApos (Real.rpow_pos_of_pos hkpos _)
  have hb := probability_sum_tail_of_tails iidCodeMeasure Z hZm
    (fun i ω => abs_nonneg _) hC (by norm_num : (0 : ℝ) < 2 / 3)
    (by norm_num : (2 / 3 : ℝ) < 1)
    (fun i t ht => htail _ t ht) _ ht
  have hpower : (A * (k : ℝ) ^ (3 / 2 : ℝ)) ^ (-(2 / 3 : ℝ)) =
      A ^ (-(2 / 3 : ℝ)) * (k : ℝ)⁻¹ := by
    rw [Real.mul_rpow hApos.le (Real.rpow_nonneg hkpos.le _),
      ← Real.rpow_mul hkpos.le]
    norm_num [Real.rpow_neg_one]
  rw [hpower] at hb
  have hcoef : C * (1 + 1 / (1 - (2 / 3 : ℝ))) * ((2 * k : ℕ) : ℝ) *
      (A ^ (-(2 / 3 : ℝ)) * (k : ℝ)⁻¹) =
      (8 * C) * A ^ (-(2 / 3 : ℝ)) := by
    push_cast
    norm_num
    field_simp [ne_of_gt hkpos]
    ring
  rw [hcoef] at hb
  have hsummeas : Measurable (fun ω => ∑ i, Z i ω) := by fun_prop
  have hs : MeasurableSet {ω | A * (k : ℝ) ^ (3 / 2 : ℝ) < ∑ i, Z i ω} :=
    measurableSet_lt measurable_const hsummeas
  have hcomp := probReal_compl_eq_one_sub (μ := iidCodeMeasure) hs
  have hsub : {ω | A * (k : ℝ) ^ (3 / 2 : ℝ) < ∑ i, Z i ω}ᶜ ⊆
      {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
    intro ω hω l hl hl'
    have hsmall : (∑ i, Z i ω) ≤ A * (k : ℝ) ^ (3 / 2 : ℝ) := le_of_not_gt hω
    exact (busemann_variation_bound ω k l hl hl').trans hsmall
  have hmono := measureReal_mono hsub (measure_ne_top iidCodeMeasure _)
  rw [hcomp] at hmono
  linarith only [hb, hmono]

end DirectedDistances.Recursive
