module

public import DirectedDistances.RandomWalk.Lemma518Limit

/-! # Sequence-level helpers for the corrected bridge window limit

Helpers toward corrected Lemma 5.18 (`lem-disk-walk-conv`),
admissibility restriction. These are not counted as paper results. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter

/-- Measurability of the raw bridge window used in corrected Lemma 5.18
counted as a paper result. -/
theorem measurable_bridgeRawWindow' (N : ℕ) :
    Measurable (bridgeRawWindow N) := by
  have hh (K : ℕ) : Measurable (codeFstFirstHit (-(K : ℤ))) := by
    rw [ENat.measurable_iff]
    intro k
    exact codePast_le k _ (measurableSet_codePast_codeFstFirstHit_eq _ k)
  apply measurable_from_prod_countable_left
  intro K
  have ht : Measurable (fun ω => (codeFstFirstHit (-(K : ℤ)) ω).toNat) :=
    (measurable_of_countable ENat.toNat).comp (hh K)
  apply measurable_pi_iff.mpr
  intro j
  have hw : Measurable (fun z : ℕ × (ℕ → Fin 3) => codeWalk z.2 z.1) :=
    measurable_from_prod_countable_right fun t =>
      (measurable_pi_apply t).comp measurable_codeWalk
  exact (hw.comp (((ht.add_const j.val).sub_const N).prodMk measurable_id)).sub
    (hw.comp (ht.prodMk measurable_id))

/-- Eventually, every square-root band contains a level with the required
modulo-three admissibility. This witnesses that the corrected hypotheses of
are nonvacuous; helper, not counted as a paper result. -/
theorem exists_admissible_level (A : ℝ) (hA : 1 < A) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      ∃ ℓ : ℕ, A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) ∧
        (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) ∧ ℓ ≤ n ∧
        ∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q := by
  have hApos : 0 < A := lt_trans zero_lt_one hA
  have hinv : A⁻¹ < 1 := inv_lt_one_of_one_lt₀ hA
  have hwidthCoeff : 0 < A - A⁻¹ := sub_pos.mpr (lt_trans hinv hA)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hwidth : Tendsto (fun n : ℕ => (A - A⁻¹) * Real.sqrt (n : ℝ))
      atTop atTop := hsqrt.const_mul_atTop hwidthCoeff
  obtain ⟨nw, hnwidth⟩ := Filter.eventually_atTop.mp
    (hwidth.eventually_ge_atTop (3 : ℝ))
  obtain ⟨nr, hnroot⟩ := Filter.eventually_atTop.mp
    (hsqrt.eventually_ge_atTop A)
  refine ⟨max nw nr, ?_⟩
  intro n hn
  have hwidthn : 3 ≤ (A - A⁻¹) * Real.sqrt (n : ℝ) :=
    hnwidth n ((le_max_left _ _).trans hn)
  have hrootn : A ≤ Real.sqrt (n : ℝ) :=
    hnroot n ((le_max_right _ _).trans hn)
  let L : ℕ := ⌈A⁻¹ * Real.sqrt (n : ℝ)⌉₊
  let d : ℕ := (n % 3 + 3 - L % 3) % 3
  let ell : ℕ := L + d
  have hxnonneg : 0 ≤ A⁻¹ * Real.sqrt (n : ℝ) :=
    mul_nonneg (inv_pos.mpr hApos).le (Real.sqrt_nonneg _)
  have hceilLo : A⁻¹ * Real.sqrt (n : ℝ) ≤ (L : ℝ) := by
    exact Nat.le_ceil _
  have hceilHi : (L : ℝ) < A⁻¹ * Real.sqrt (n : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one hxnonneg
  have hdlt : d < 3 := by
    dsimp [d]
    exact Nat.mod_lt _ (by omega)
  have hdle : d ≤ 2 := by omega
  have hellCast : (ell : ℝ) = (L : ℝ) + (d : ℝ) := by
    simp [ell]
  have hlow : A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) := by
    rw [hellCast]
    exact hceilLo.trans (le_add_of_nonneg_right (Nat.cast_nonneg d))
  have hceilPlus : (ell : ℝ) < A⁻¹ * Real.sqrt (n : ℝ) + 3 := by
    rw [hellCast]
    have hdleR : (d : ℝ) ≤ 2 := by exact_mod_cast hdle
    linarith
  have hspan : A⁻¹ * Real.sqrt (n : ℝ) + 3 ≤ A * Real.sqrt (n : ℝ) := by
    nlinarith [hwidthn]
  have hhi : (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) :=
    le_of_lt (lt_of_lt_of_le hceilPlus hspan)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hupperN : A * Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hrootn hsqrt_nonneg
    nlinarith [hsqrt_sq]
  have hell_le_n : ell ≤ n := by
    exact_mod_cast hhi.trans hupperN
  have hmod : ell % 3 = n % 3 := by
    dsimp [ell, d]
    omega
  have hnrep : (n : ℤ) = (n % 3 : ℤ) + 3 * (n / 3 : ℕ) := by
    have h := Nat.mod_add_div n 3
    omega
  have hellrep : (ell : ℤ) = (ell % 3 : ℤ) + 3 * (ell / 3 : ℕ) := by
    have h := Nat.mod_add_div ell 3
    omega
  refine ⟨ell, hlow, hhi, hell_le_n, ?_⟩
  refine ⟨((n / 3 : ℕ) : ℤ) - ((ell / 3 : ℕ) : ℤ), ?_⟩
  have hmodInt : (ell : ℤ) % 3 = (n : ℤ) % 3 := by
    exact_mod_cast hmod
  rw [hnrep, hellrep, hmodInt]
  ring

/-- Transfer the uniform bridge window limit to an eventually admissible
level sequence, toward corrected Lemma 5.18 (`lem-disk-walk-conv`,
result. C15/C19 are expressed by the eventual level congruence. -/
theorem bridgeWindow_tv_seq (A : ℝ) (hA : 1 < A) (ℓ : ℕ → ℕ)
    (hband : ∀ᶠ (n : ℕ) in atTop,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ n : ℝ) ∧
        (ℓ n : ℝ) ≤ A * Real.sqrt (n : ℝ))
    (hadm : ∀ᶠ (n : ℕ) in atTop,
      ℓ n ≤ n ∧ ∃ q : ℤ, (n : ℤ) = (ℓ n : ℤ) + 3 * q)
    (N : ℕ) (W : ℕ → (ℕ → Fin 3) × ℕ → Fin (2 * N + 1) → ℤ × ℤ)
    (hW : ∀ n, Measurable (W n))
    (hagree : ∀ᶠ (n : ℕ) in atTop, ∀ ω K,
      ω ∈ coneEvent (ℓ n : ℤ) 0 n → 1 ≤ K → K ≤ ℓ n →
      N ≤ K → K + N ≤ ℓ n → W n (ω, K) = bridgeRawWindow N (ω, K)) :
    ∀ ε > 0, ∀ᶠ (n : ℕ) in atTop,
      ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ), MeasurableSet B →
        |((cond iidCodeMeasure (coneEvent (ℓ n : ℤ) 0 n)).prod
            (Measure.uniformOfFinset (Finset.Icc 1 (ℓ n)))).real
            (W n ⁻¹' B) - (uibhbotExcursionWindowLaw N).real B| ≤ ε := by
  intro ε hε
  obtain ⟨n₀, huni⟩ := bridgeWindow_tv_uniform A hA N ε hε
  have hthreshold : ∀ᶠ n : ℕ in atTop, n₀ ≤ n :=
    Filter.eventually_atTop.2 ⟨n₀, fun _ hn => hn⟩
  filter_upwards [hthreshold, hband, hadm, hagree] with n hn hbandn hadmn hagreen
  intro B hB
  rcases hbandn with ⟨hlo, hhi⟩
  rcases hadmn with ⟨hln, hcong⟩
  exact huni n hn (ℓ n) hlo hhi hln hcong (W n) (hW n) hagreen B hB

/-- The sequence-level limit for the raw comparison window, toward corrected
helper, not counted as a paper result. -/
theorem bridgeWindow_tv_seq_raw (A : ℝ) (hA : 1 < A) (ℓ : ℕ → ℕ)
    (hband : ∀ᶠ (n : ℕ) in atTop,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ n : ℝ) ∧
        (ℓ n : ℝ) ≤ A * Real.sqrt (n : ℝ))
    (hadm : ∀ᶠ (n : ℕ) in atTop,
      ℓ n ≤ n ∧ ∃ q : ℤ, (n : ℤ) = (ℓ n : ℤ) + 3 * q)
    (N : ℕ) :
    ∀ ε > 0, ∀ᶠ (n : ℕ) in atTop,
      ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ), MeasurableSet B →
        |((cond iidCodeMeasure (coneEvent (ℓ n : ℤ) 0 n)).prod
            (Measure.uniformOfFinset (Finset.Icc 1 (ℓ n)))).real
            ((bridgeRawWindow N) ⁻¹' B) -
          (uibhbotExcursionWindowLaw N).real B| ≤ ε := by
  apply bridgeWindow_tv_seq A hA ℓ hband hadm N
    (fun _ => bridgeRawWindow N)
    (fun _ => measurable_bridgeRawWindow' N)
  filter_upwards [] with n
  intro ω K hω hK₁ hK₂ hK₃ hK₄
  rfl

end DirectedDistances.RandomWalk
