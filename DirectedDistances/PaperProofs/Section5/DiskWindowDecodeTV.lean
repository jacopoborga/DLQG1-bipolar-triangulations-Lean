module

public import DirectedDistances.Paper.Section5.DiskWalkConv

/-! # Decoded disk-window total variation

Helper toward prop-disk-bs-conv / Proposition 5.16
(`Paper.Section5.DiskWalkConv`; S3/C15/C19 domain, finite bridge cemetery).
This is reading-independent: no rooted map, ball, or Definition 3.8 topology is chosen.
It is not the paper result. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk

/-- Helper toward prop-disk-bs-conv / Proposition 5.16
total-variation window convergence (`Paper.Section5.DiskWalkConv`; S3/C15/C19 domain,
finite bridge cemetery) through any measurable finite-window decoder. Reading-independent:
no rooted map, ball, or Definition 3.8 topology is chosen; not the paper result.
The anchor bounds every subset, so no measurability restriction on `C` is needed. -/
theorem diskWindow_decode_tv
    (A : ℝ) (hA : 1 < A) (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    {β : Type*} [MeasurableSpace β]
    (decode : (Fin (2 * N + 1) → ℤ × ℤ) → β)
    (_hdecode : Measurable decode) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      ∀ C : Set (Option β),
        |((cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
            (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            ((fun p => Option.map decode (bridgeOptionWindow n N p)) ⁻¹' C) -
          (uibhbotEncodingWindowLaw N).real ((fun x => some (decode x)) ⁻¹' C)| ≤ ε := by
  obtain ⟨n₀, htv⟩ :=
    DirectedDistances.Paper.Section5.disk_walk_conv_corrected A hA N ε hε
  refine ⟨n₀, ?_⟩
  intro n hn ℓ hlo hhi hℓn hcong C
  exact (htv n hn ℓ hlo hhi hℓn hcong).1 ((Option.map decode) ⁻¹' C)

/-- Helper toward prop-disk-bs-conv / Proposition 5.16
push-forward of corrected Lemma 5.18 (`Paper.Section5.DiskWalkConv`; S3/C15/C19 domain,
finite bridge cemetery). Reading-independent: no rooted map, ball, or Definition 3.8 topology
is chosen; not the paper result. The estimate holds for every subset. -/
theorem diskWindow_id_tv
    (A : ℝ) (hA : 1 < A) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      ∀ C : Set (Option (Fin (2 * N + 1) → ℤ × ℤ)),
        |((cond iidCodeMeasure (coneEvent (ℓ : ℤ) 0 n)).prod
            (Measure.uniformOfFinset (Finset.Icc 1 ℓ))).real
            (bridgeOptionWindow n N ⁻¹' C) -
          (uibhbotEncodingWindowLaw N).real (some ⁻¹' C)| ≤ ε := by
  simpa only [Option.map_id, id] using
    diskWindow_decode_tv A hA N ε hε id measurable_id

end DirectedDistances.PaperProofs.Section5
