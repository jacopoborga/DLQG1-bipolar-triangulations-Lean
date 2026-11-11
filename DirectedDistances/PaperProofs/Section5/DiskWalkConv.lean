/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.Lemma518Limit
public import DirectedDistances.RandomWalk.Lemma518Cemetery
public import DirectedDistances.RandomWalk.Lemma518Sequence
public import DirectedDistances.RandomWalk.UIBHBOTEncodingWalk

/-! # Provider for corrected Lemma 5.18 (lem-disk-walk-conv)

are described at lines 671–675 and the bi-infinite walk Z^bc at lines 299–302.
C15/C19 ruling. The cemetery value for windows leaving [0,n], its vanishing
probability, and independence of the total extension follow

The first clause is total variation convergence of the cemetery-valued window
to the law of Z^bc restricted to [-N,N]; the target puts no mass on the
cemetery. The second clause gives the vanishing exceptional probability. The
third clause states extension independence for every measurable total
extension agreeing wherever the finite bridge window is valid.

The code letters ω (i + 1) encode iid increments uniformly chosen from
{(1,-1), (-1,0), (0,1)}; coordinate 0 is unused. The event coneEvent ℓ 0 n
requires the walk from (ℓ,0) to stay in the closed quadrant at every time
0,…,n and end at (0,0). Independently, K is uniform on {1,…,ℓ}. T is the
first hit of -K by the first coordinate, and window index j corresponds to
time j-N relative to T. The process Z^bc is the bi-infinite concatenation of
iid stopped excursion words, with time zero at the start of word zero. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory Filter DirectedDistances.RandomWalk

private theorem disk_walk_boundary_error_eventually (A : ℝ) (hA : 1 < A)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      2 * (N : ℝ) / (ℓ : ℝ) ≤ ε / 2 := by
  by_cases hN : N = 0
  · subst N
    refine ⟨0, ?_⟩
    intro n _ ℓ _
    simpa using (le_of_lt (half_pos hε))
  · have hApos : 0 < A := lt_trans zero_lt_one hA
    let c : ℝ := 4 * (N : ℝ) * A / ε
    have hcpos : 0 < c := by
      dsimp [c]
      positivity
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp
      (hsqrt.eventually_ge_atTop c)
    refine ⟨n₁, ?_⟩
    intro n hn ℓ hlo
    have hs : c ≤ Real.sqrt (n : ℝ) := hn₁ n hn
    have hnpos : (0 : ℝ) < n := by
      by_contra h
      have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hnzero : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) hnnonneg
      rw [hnzero] at hs
      have : c ≤ 0 := by simpa using hs
      exact (not_le_of_gt hcpos) this
    have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hlowerpos : 0 < A⁻¹ * Real.sqrt (n : ℝ) :=
      mul_pos (inv_pos.mpr hApos) hspos
    have hscaled : 2 * (N : ℝ) * A ≤ (ε / 2) * Real.sqrt (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ ε / 2)
      calc
        2 * (N : ℝ) * A = (ε / 2) * (4 * (N : ℝ) * A / ε) := by
          field_simp [ne_of_gt hε]
          ; ring
        _ ≤ (ε / 2) * Real.sqrt (n : ℝ) := hmul
    have hquot : 2 * (N : ℝ) / (A⁻¹ * Real.sqrt (n : ℝ)) ≤ ε / 2 := by
      rw [show 2 * (N : ℝ) / (A⁻¹ * Real.sqrt (n : ℝ)) =
          (2 * (N : ℝ) * A) / Real.sqrt (n : ℝ) by
        field_simp [ne_of_gt hApos, ne_of_gt hspos]]
      exact (div_le_iff₀ hspos).2 hscaled
    have hratio : 2 * (N : ℝ) / (ℓ : ℝ) ≤
        2 * (N : ℝ) / (A⁻¹ * Real.sqrt (n : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) hlowerpos hlo
    exact hratio.trans hquot

/-- Corrected Lemma 5.18 (lem-disk-walk-conv), from
domain and with the finite bridge cemetery convention. The single threshold precedes
the level and all measurable sets and extensions. -/
theorem disk_walk_conv_corrected :
    ∀ A : ℝ, 1 < A → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
        A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
        (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
        (∀ S : Set (Option (Fin (2 * N + 1) → ℤ × ℤ)),
          |((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
              (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real (bridgeOptionWindow n N ⁻¹' S) -
            (uibhbotEncodingWindowLaw N).real (some ⁻¹' S)| ≤ ε) ∧
        ((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
            (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            (bridgeOptionWindow n N ⁻¹' {none}) ≤ ε ∧
        (∀ W : (ℕ → Fin 3) × ℕ → (Fin (2 * N + 1) → ℤ × ℤ), Measurable W →
          (∀ p x, bridgeOptionWindow n N p = some x → W p = x) →
          ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ),
            |((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
                (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real (W ⁻¹' B) -
              (uibhbotEncodingWindowLaw N).real B| ≤ ε) := by
  intro A hA N ε hε
  obtain ⟨n₀tv, htv⟩ := bridgeWindow_tv_uniform A hA N (ε / 2) (by linarith)
  obtain ⟨n₁, hboundary⟩ := disk_walk_boundary_error_eventually A hA N ε hε
  refine ⟨max (max n₀tv n₁) 1, ?_⟩
  intro n hn ℓ hlo hhi hℓn hcong
  have hnlarge : max n₀tv n₁ ≤ n := (le_max_left _ _).trans hn
  have hn₀tv : n₀tv ≤ n := (le_max_left _ _).trans hnlarge
  have hn₁ : n₁ ≤ n := (le_max_right _ _).trans hnlarge
  have hnpositive : 1 ≤ n := (le_max_right _ _).trans hn
  have hlevel := bridgeWindow_one_le_level A hA n ℓ hnpositive hlo
  have herr : 2 * (N : ℝ) / (ℓ : ℝ) ≤ ε / 2 := hboundary n hn₁ ℓ hlo
  have hrawMeas : Measurable (bridgeRawWindow N) := measurable_bridgeRawWindow' N
  have hrawAgree : ∀ ω K, ω ∈ coneEvent (ℓ : ℤ) 0 n → 1 ≤ K → K ≤ ℓ →
      N ≤ K → K + N ≤ ℓ → bridgeRawWindow N (ω, K) = bridgeRawWindow N (ω, K) :=
    fun _ _ _ _ _ _ _ => rfl
  have htarget : uibhbotEncodingWindowLaw N = uibhbotExcursionWindowLaw N :=
    uibhbotEncodingWindowLaw_eq_uibhbotExcursionWindowLaw N
  constructor
  · intro S
    have hS : MeasurableSet (some ⁻¹' S : Set (Fin (2 * N + 1) → ℤ × ℤ)) :=
      (Set.to_countable _).measurableSet
    have htransfer := bridgeOptionWindow_transfer (n := n) (ell := ℓ) (N := N)
      hlevel (bridgeRawWindow N) hrawMeas hrawAgree S
    have htransfer' : |((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
        (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real (bridgeOptionWindow n N ⁻¹' S) -
      ((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
        (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
        ((bridgeRawWindow N) ⁻¹' (some ⁻¹' S))| ≤ ε / 2 :=
      htransfer.trans herr
    have htv' := htv n hn₀tv ℓ hlo hhi hℓn hcong (bridgeRawWindow N) hrawMeas
      hrawAgree (some ⁻¹' S) hS
    rw [htarget]
    calc
      |((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            (bridgeOptionWindow n N ⁻¹' S) -
          (uibhbotExcursionWindowLaw N).real (some ⁻¹' S)| ≤
        |((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            (bridgeOptionWindow n N ⁻¹' S) -
          ((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
            (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            ((bridgeRawWindow N) ⁻¹' (some ⁻¹' S))| +
        |((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            ((bridgeRawWindow N) ⁻¹' (some ⁻¹' S)) -
          (uibhbotExcursionWindowLaw N).real (some ⁻¹' S)| := abs_sub_le _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add htransfer' htv'
      _ = ε := by ring
  constructor
  · have hnone := bridgeOptionWindow_none_bound (n := n) (ell := ℓ) (N := N) hlevel
    calc
      _ ≤ 2 * (N : ℝ) / (ℓ : ℝ) := by simpa [bridgeLevelLaw] using hnone
      _ ≤ ε / 2 := herr
      _ ≤ ε := by linarith
  · intro W hW hagree B
    have hB : MeasurableSet B := (Set.to_countable B).measurableSet
    have hrawAgree' := agree_interior_of_agree_valid (n := n) (ell := ℓ) (N := N)
      W hagree
    have htv' := htv n hn₀tv ℓ hlo hhi hℓn hcong W hW
      (by
        intro ω K hω hK hKℓ hNK hKN
        exact hrawAgree' ω K hω hK hKℓ hNK hKN)
      B hB
    rw [htarget]
    exact htv'.trans (by linarith)

/-- Sequential form of corrected Lemma 5.18, with the same source and rulings
as disk_walk_conv_corrected. It follows by intersecting the eventual
square-root band and C15/C19 admissibility conditions. -/
theorem disk_walk_conv_corrected_seq :
    ∀ A : ℝ, 1 < A → ∀ ℓ : ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ n : ℝ) ∧ (ℓ n : ℝ) ≤ A * Real.sqrt (n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, ℓ n ≤ n ∧ ∃ q : ℤ, (n : ℤ) = (ℓ n : ℤ) + 3 * q) →
      ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ∀ S : Set (Option (Fin (2 * N + 1) → ℤ × ℤ)),
          |((ProbabilityTheory.cond iidCodeMeasure (coneEvent (ℓ n : ℤ) 0 n)).prod
              (Measure.uniformOfFinset (Finset.Icc 1 (ℓ n)))).real
              (bridgeOptionWindow n N ⁻¹' S) -
            (uibhbotEncodingWindowLaw N).real (some ⁻¹' S)| ≤ ε := by
  intro A hA ℓ hband hadm N ε hε
  obtain ⟨n₀, hmain⟩ := disk_walk_conv_corrected A hA N ε hε
  have hthreshold : ∀ᶠ n : ℕ in atTop, n₀ ≤ n :=
    Filter.eventually_atTop.2 ⟨n₀, fun _ hn => hn⟩
  filter_upwards [hthreshold, hband, hadm] with n hn hbandn hadmn
  rcases hbandn with ⟨hlo, hhi⟩
  rcases hadmn with ⟨hℓn, hcong⟩
  intro S
  exact (hmain n hn (ℓ n) hlo hhi hℓn hcong).1 S

/-- Nonemptiness of the corrected domain for all sufficiently large n,
from Lemma518Sequence.exists_admissible_level. -/
theorem disk_walk_conv_domain_nonempty (A : ℝ) (hA : 1 < A) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      ∃ ℓ : ℕ, A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) ∧
        (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) ∧ ℓ ≤ n ∧
        ∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q :=
  exists_admissible_level A hA

end DirectedDistances.PaperProofs.Section5
